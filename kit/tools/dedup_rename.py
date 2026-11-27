#!/usr/bin/env python3
"""P4: rename duplicate theorem/lemma leaf names, using Lean's own reference index (.ilean).

    python3 dedup_rename.py <project> [--apply] [--report kit/dedup/report.json]

Needs a finished build: every module's .ilean (in <project>/.lake/build/lib/lean) lists the
definition range and every usage range of every constant, including `h.mul`-style field
notation, `.mul`, `open … in mul`, `@X.mul`, simp/rw lists, `attribute […]` and `export`.

For each group of declarations (--kinds, default theorem,lemma) sharing a leaf name, the one with the most usages
keeps its name; every other one gets  <ns>.<nsLeafLowerCamel>_<leaf>  (e.g. IsRapid.mul ->
IsRapid.isRapid_mul), so field notation `h.isRapid_mul` keeps working; a root-level declaration gets its module name
as prefix. Lean-generated companions of a renamed def (foo.eq_1, foo.eq_def, …) are renamed
at every usage too. New leaves are made
globally unique against every declaration leaf in the project.

Safety: per constant, ALL its ranges (definition + usages) are checked to end with the old leaf
before anything is edited; one mismatch skips the constant. Also skipped (learned from D's first
apply, 2026-11-27): name-generating attributes (@[ext] -> X.ext_iff, @[simps] -> X_apply,
reassoc, elementwise, mk_iff, to_additive); declarations that have declarations in their own
namespace (renaming def IsNear breaks h.foo for IsNear.foo); leaves with a `.leaf` occurrence in
code that .ilean did not record (e.g. `(.refl ·.2)`); declarations in Main/Statements.
Run it right after a successful build: a usage added after the build is not in the index.
Positions in .ilean are (0-based line, UTF-16 column).
Without --apply only the plan is printed.
"""
import argparse, collections, json, pathlib, re, sys

ap = argparse.ArgumentParser()
ap.add_argument("project", type=pathlib.Path)
ap.add_argument("--apply", action="store_true")
ap.add_argument("--report", type=pathlib.Path)
ap.add_argument("--kinds", default="theorem,lemma",
                help="declaration kinds whose duplicate leaves are renamed, e.g. theorem,lemma,def")
ap.add_argument("--src-dir", default=None, help="defaults to srcDir in lakefile.toml, else '.'")
a = ap.parse_args()

P = a.project.resolve()
src_dir = a.src_dir
if src_dir is None:
    m = re.search(r'^srcDir\s*=\s*"([^"]+)"', (P / "lakefile.toml").read_text(), re.M) \
        if (P / "lakefile.toml").exists() else None
    src_dir = m.group(1) if m else "."
SRC = P / src_dir
ILEAN = P / ".lake" / "build" / "lib" / "lean"

# ---- load sources and indexes ----------------------------------------------------------------
mods = {}
for f in sorted(SRC.rglob("*.lean")):
    if ".lake" in f.relative_to(P).parts:
        continue
    mods[".".join(f.relative_to(SRC).with_suffix("").parts)] = f
stale, missing = [], []
refs = collections.defaultdict(lambda: {"def": None, "uses": []})  # full name -> ranges
for mod, f in mods.items():
    il = ILEAN / pathlib.Path(*mod.split(".")).with_suffix(".ilean")
    if not il.exists():
        missing.append(mod); continue
    if f.stat().st_mtime > il.stat().st_mtime + 1:
        stale.append(mod)   # may only be a touched timestamp (git); ranges are verified below
    for key, v in json.loads(il.read_text())["references"].items():
        k = json.loads(key)
        if "c" not in k:
            continue
        name, defmod = k["c"]["n"], k["c"]["m"]
        if v.get("definition") and defmod == mod:
            refs[name]["def"] = (mod, v["definition"][:4])
            refs[name]["defmod"] = mod
        for u in v.get("usages", []):
            refs[name]["uses"].append((mod, u[:4]))
if missing:
    print(f"missing .ilean for {len(missing)} modules, e.g. {missing[:5]}")
    sys.exit("run a full build first (./kit/run/20_build.sh), then rerun")
if stale:
    print(f"warning: {len(stale)} sources newer than their .ilean (fine if only git touched them; "
          f"every range is verified against the text, mismatching constants are skipped)")

lines = {mod: f.read_text().split("\n") for mod, f in mods.items()}


def blank_comments(text: str) -> str:
    """comments -> spaces, newlines kept, so positions stay valid"""
    out, i, d, n = list(text), 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            d += 1; out[i] = out[i + 1] = " "; i += 2; continue
        if d and text.startswith("-/", i):
            d -= 1; out[i] = out[i + 1] = " "; i += 2; continue
        if d:
            if text[i] != "\n":
                out[i] = " "
            i += 1; continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                out[i] = " "; i += 1
            continue
        i += 1
    return "".join(out)


code_lines = {mod: blank_comments("\n".join(L)).split("\n") for mod, L in lines.items()}


def cp_index(line: str, utf16_col: int) -> int:
    n = 0
    for i, ch in enumerate(line):
        if n >= utf16_col:
            return i
        n += 2 if ord(ch) > 0xFFFF else 1
    return len(line)


def text_at(mod, r):
    l0, c0, l1, c1 = r
    if l0 != l1:
        return None
    L = lines[mod][l0]
    return L[cp_index(L, c0):cp_index(L, c1)]


KIND = re.compile(r"(?:^|\s)(theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque)\s+$")


def decl_kind_and_attrs(mod, r):
    l0, c0 = r[0], r[1]
    L = lines[mod][l0]
    head = L[:cp_index(L, c0)]
    m = KIND.search(head)
    attrs = head
    k = l0 - 1
    while k >= 0 and (lines[mod][k].lstrip().startswith("@[") or lines[mod][k].rstrip().endswith("]")) \
            and k > l0 - 4:
        attrs = lines[mod][k] + "\n" + attrs; k -= 1
    return (m.group(1) if m else None), attrs


def leaf(name):
    return name.split(".")[-1]


def namespace(name):
    parts = name.split(".")
    if parts[0] == "_private":  # _private.<Module>.0.<ns>.<leaf>
        parts = parts[parts.index("0") + 1:]
    return parts[:-1]


# ---- declarations in the project -------------------------------------------------------------
decls = {}            # full name -> (kind, attrs)
all_leaves = collections.Counter()
for name, r in refs.items():
    if r["def"] is None:
        continue
    kind, attrs = decl_kind_and_attrs(*r["def"])
    if kind is None:
        continue  # auto-generated or unusual: not a written declaration
    decls[name] = (kind, attrs)
    all_leaves[leaf(name)] += 1

KINDS = set(a.kinds.split(","))
thm = {n: v for n, v in decls.items() if v[0] in KINDS}
tl = [n for n, v in decls.items() if v[0] in ("theorem", "lemma")]
tld = [n for n, v in decls.items() if v[0] in ("theorem", "lemma", "def")]
groups = collections.defaultdict(list)
for n in thm:
    groups[leaf(n)].append(n)
dups = {l: ns for l, ns in groups.items() if len(ns) > 1}
N = len(thm)
before = 100 * (N - len(groups)) / max(N, 1)

# ---- positions .ilean recorded (any constant): an unrecorded `.leaf` is a usage Lean did not index
covered = collections.defaultdict(list)          # (mod, line) -> [(start_cp, end_cp)]
for name, r in refs.items():
    for m_, rg in ([r["def"]] if r["def"] else []) + r["uses"]:
        if rg[0] == rg[2]:
            L = lines[m_][rg[0]]
            covered[(m_, rg[0])].append((cp_index(L, rg[1]), cp_index(L, rg[3])))
IDC = r"[\w'!?]"


def unindexed_dot_uses(lf):
    rx = re.compile(rf"\.{re.escape(lf)}(?!{IDC})")
    hits = []
    for m_, CL in code_lines.items():
        for k, L in enumerate(CL):
            if lf not in L:
                continue
            for mm in rx.finditer(L):
                s0, e0 = mm.start(), mm.end()
                if not any(a <= s0 + 1 and e0 <= b for a, b in covered.get((m_, k), [])):
                    hits.append(f"{m_}:{k + 1}")
    return hits


GENERATING = re.compile(r"@\[[^\]]*\b(ext|simps!?|reassoc|elementwise|mk_iff|to_additive)\b")
has_children = {n for n in decls if any(o.startswith(n + ".") for o in decls)}
unindexed_cache = {}

# ---- plan --------------------------------------------------------------------------------------
PROTECTED = {"Main", "Statements"}
taken = set(all_leaves)
plan, skipped = {}, []
def blocked(n, lf):
    """reason why n must keep its name, or None"""
    if refs[n]["defmod"] in PROTECTED:
        return "in Main/Statements"
    g = GENERATING.search(thm[n][1])
    if g:   # the attribute derives other names (X.ext_iff, X_apply, X_assoc, …) from this one
        return f"@[{g.group(1)}] generates names from it"
    if n in has_children:   # X.foo lemmas are reached by field notation on terms of type X
        return "has declarations in its namespace (field notation)"
    if lf not in unindexed_cache:
        unindexed_cache[lf] = unindexed_dot_uses(lf)
    if unindexed_cache[lf]:
        return f"`.{lf}` used where .ilean has no record, e.g. {unindexed_cache[lf][0]}"
    return None


for lf, names in sorted(dups.items()):
    why = {n: blocked(n, lf) for n in names}
    # keeper: one that cannot be renamed if any (protected first), else the most used
    names.sort(key=lambda n: (refs[n]["defmod"] not in PROTECTED, why[n] is None, -len(refs[n]["uses"]), n))
    for n in names[1:]:                    # names[0] keeps its name
        if why[n]:
            skipped.append((n, why[n])); continue
        ns = namespace(n) or [refs[n]["defmod"].split(".")[-1]]   # root decl: module name as prefix
        cand = None
        for depth in range(1, len(ns) + 1):
            pre = "_".join(p[:1].lower() + p[1:] for p in ns[-depth:])
            c = f"{pre}_{lf}"
            if c not in taken:
                cand = c; break
        if cand is None:
            k = 2
            while f"{lf}_{k}" in taken:
                k += 1
            cand = f"{lf}_{k}"
        # (module, range, old tail, new tail): the constant itself, plus Lean-generated companions
        # (foo.eq_1, foo.eq_def, foo.induct, ...) whose names derive from it
        ranges = [(m_, r, lf, cand) for m_, r in [refs[n]["def"]] + refs[n]["uses"]]
        for aux, ar in refs.items():
            if aux.startswith(n + ".") and aux not in decls:
                suf = aux[len(n):]
                ranges += [(m_, r, lf + suf, cand + suf) for m_, r in ar["uses"]]
        bad = [(m_, r, o) for m_, r, o, _ in ranges if not (text_at(m_, r) or "").endswith(o)]
        if bad:
            m_, r, o = bad[0]
            skipped.append((n, f"range text {text_at(m_, r)!r} (expected …{o}) at {m_}:{r[0] + 1}")); continue
        taken.add(cand)
        plan[n] = (cand, sorted(set((m_, tuple(r), o, w) for m_, r, o, w in ranges)))

renamed = set(plan)
after_groups = collections.Counter(leaf(n) if n not in plan else plan[n][0] for n in thm)
after = 100 * (N - len(after_groups)) / max(N, 1)
S = lambda d: max(0.0, min(100.0, 50 + (4.22 - d) * (40.0 / (4.22 - 1.14))))
def rate(names, ren=None):
    ls = [(ren[n][0] if ren and n in ren else leaf(n)) for n in names]
    return 100 * (len(ls) - len(set(ls))) / max(len(ls), 1)


print(f"kinds {sorted(KINDS)}: decls {N}; duplicate leaf groups {len(dups)}; dup rate {before:.3f}% "
      f"-> {after:.3f}%  (S_dedup {S(before):.1f} -> {S(after):.1f})")
print(f"renames {len(plan)} ({collections.Counter(thm[n][0] for n in plan)}), "
      f"edits {sum(len(r) for _, r in plan.values())}, skipped {len(skipped)}")
print(f"dup rate theorem+lemma {rate(tl):.3f}% -> {rate(tl, plan):.3f}%   "
      f"theorem+lemma+def {rate(tld):.3f}% -> {rate(tld, plan):.3f}%")
why_count = collections.Counter(w.split(" e.g.")[0].split(" at ")[0] if not w.startswith("`.") else "`.leaf` unindexed use"
                                for _, w in skipped)
for w, c in why_count.most_common():
    print(f"  skipped {c:4d}: {w}")
for n, why in skipped[:15]:
    print(f"  skip {n}: {why}")

report = dict(dup_rate_before=before, dup_rate_after=after, renames={n: (n.rsplit('.', 1)[0] + '.' if '.' in n else '') + c for n, (c, _) in plan.items()},
              skipped=skipped)
if a.report:
    a.report.parent.mkdir(parents=True, exist_ok=True)
    a.report.write_text(json.dumps(report, indent=1, ensure_ascii=False))
if not a.apply:
    print("(dry run; --apply to edit)"); sys.exit(0)

# ---- apply: per file, edits from the end so earlier positions stay valid ----------------------
per_file = collections.defaultdict(list)
for n, (new_leaf, ranges) in plan.items():
    for mod, r, old_tail, new_tail in ranges:
        per_file[mod].append((r, old_tail, new_tail))
for mod, edits in per_file.items():
    L = lines[mod]
    for (l0, c0, l1, c1), old, new in sorted(edits, key=lambda e: (e[0][0], e[0][1]), reverse=True):
        s = L[l0]; i, j = cp_index(s, c0), cp_index(s, c1)
        seg = s[i:j]
        assert seg.endswith(old), (mod, l0, seg, old)
        L[l0] = s[:i] + seg[: len(seg) - len(old)] + new + s[j:]
    mods[mod].write_text("\n".join(L))
print(f"applied to {len(per_file)} files")
