#!/usr/bin/env python3
"""P4: rename duplicate theorem/lemma leaf names, using Lean's own reference index (.ilean).

    python3 dedup_rename.py <project> [--apply] [--report kit/dedup/report.json]

Needs a finished build: every module's .ilean (in <project>/.lake/build/lib/lean) lists the
definition range and every usage range of every constant, including `h.mul`-style field
notation, `.mul`, `open … in mul`, `@X.mul`, simp/rw lists, `attribute […]` and `export`.

For each group of theorem/lemma declarations sharing a leaf name, the one with the most usages
keeps its name; every other one gets  <ns>.<nsLeafLowerCamel>_<leaf>  (e.g. IsRapid.mul ->
IsRapid.isRapid_mul), so field notation `h.isRapid_mul` keeps working. New leaves are made
globally unique against every declaration leaf in the project.

Safety: per constant, ALL its ranges (definition + usages) are checked to end with the old leaf
before anything is edited; one mismatch skips the constant. Skipped too: @[to_additive]
(its generated name derives from the source name) and declarations in Main/Statements.
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

# ---- plan --------------------------------------------------------------------------------------
PROTECTED = {"Main", "Statements"}
taken = set(all_leaves)
plan, skipped = {}, []
for lf, names in sorted(dups.items()):
    # keeper: a declaration in Main/Statements (names checked by the challenge) if any, else most used
    names.sort(key=lambda n: (refs[n]["defmod"] not in PROTECTED, -len(refs[n]["uses"]), n))
    for n in names[1:]:                    # names[0] keeps its name
        if refs[n]["defmod"] in PROTECTED:
            skipped.append((n, "in Main/Statements")); continue
        kind, attrs = thm[n]
        if "to_additive" in attrs:
            skipped.append((n, "to_additive")); continue
        ns = namespace(n)
        if not ns:
            skipped.append((n, "root namespace, no prefix")); continue
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
        ranges = [refs[n]["def"]] + refs[n]["uses"]
        bad = [(m_, r) for m_, r in ranges if not (text_at(m_, r) or "").endswith(lf)]
        if bad:
            m_, r = bad[0]
            skipped.append((n, f"range text {text_at(m_, r)!r} at {m_}:{r[0] + 1}")); continue
        taken.add(cand)
        plan[n] = (cand, sorted(set((m_, tuple(r)) for m_, r in ranges)))

renamed = set(plan)
after_groups = collections.Counter(leaf(n) if n not in plan else plan[n][0] for n in thm)
after = 100 * (N - len(after_groups)) / max(N, 1)
S = lambda d: max(0.0, min(100.0, 50 + (4.22 - d) * (40.0 / (4.22 - 1.14))))
def rate(names, ren=None):
    ls = [(ren[n][0] if ren and n in ren else leaf(n)) for n in names]
    return 100 * (len(ls) - len(set(ls))) / max(len(ls), 1)


print(f"kinds {sorted(KINDS)}: decls {N}; duplicate leaf groups {len(dups)}; dup rate {before:.3f}% "
      f"-> {after:.3f}%  (S_dedup {S(before):.1f} -> {S(after):.1f})")
print(f"renames {len(plan)}, edits {sum(len(r) for _, r in plan.values())}, skipped {len(skipped)}")
print(f"dup rate theorem+lemma {rate(tl):.3f}% -> {rate(tl, plan):.3f}%   "
      f"theorem+lemma+def {rate(tld):.3f}% -> {rate(tld, plan):.3f}%")
for n, why in skipped[:25]:
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
    for mod, r in ranges:
        per_file[mod].append((r, leaf(n), new_leaf))
for mod, edits in per_file.items():
    L = lines[mod]
    for (l0, c0, l1, c1), old, new in sorted(edits, key=lambda e: (e[0][0], e[0][1]), reverse=True):
        s = L[l0]; i, j = cp_index(s, c0), cp_index(s, c1)
        seg = s[i:j]
        assert seg.endswith(old), (mod, l0, seg, old)
        L[l0] = s[:i] + seg[: len(seg) - len(old)] + new + s[j:]
    mods[mod].write_text("\n".join(L))
print(f"applied to {len(per_file)} files")
