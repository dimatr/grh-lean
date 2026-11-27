#!/usr/bin/env python3
"""Phase A restructuring of grh-compact: merge single-importer modules, then re-folder by Louvain.

    python3 restructure.py <baseline-project> <out-project> [--cap 40] [--seeds 20] [--dry-run]

Reads <baseline>/src, writes <out>/src (and copies lakefile/manifest/toolchain/Challenge/scripts
if missing). The baseline is never modified. Writes <out>/RESTRUCTURE_MAP.json (old -> new module).

Merge rule: a module A imported by exactly one module B (A, B not Main/Statements) is absorbed
into B if the merged file stays <= --cap declarations. Repeat to a fixed point.
Merged file = union of imports, then each original file in import-topological order, each
wrapped in `section ... end` with its unclosed `section`/`namespace` scopes closed first, so
`open`, `variable`, `set_option`, local attributes and notations stay scoped as before.

Re-folder rule: module path becomes <Top>/<Cluster>/<Leaf>.lean, where Cluster is the Louvain
community (best modularity of --seeds seeds) on the merged import graph, named after the most
common old level-2 folder in it; Top is Lib or New (majority of the community, by declarations),
because lakefile.toml (fixed) only globs Lib.+ and New.+.
"""
import argparse, collections, json, pathlib, re, shutil, sys
import networkx as nx
from networkx.algorithms.community import louvain_communities, modularity

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from score import strip_comments, DECL  # noqa: E402

IMPORT_LINE = re.compile(r"^import\s+(\S+)\s*$")
SCOPE = re.compile(r"^\s*(noncomputable\s+section|section|namespace|mutual|end)\b[ \t]*([^\s]*)")
PROTECTED = {"Main", "Statements"}


def split_file(text):
    """Return (imports, body). Imports are the `import X` lines of the header (Lean requires them
    first, after comments only). Body is everything else, original comments kept."""
    lines = text.splitlines()
    imports, body = [], []
    in_header = True
    depth = 0  # block-comment depth while scanning the header
    for l in lines:
        if in_header:
            m = IMPORT_LINE.match(l)
            if m and depth == 0:
                imports.append(m.group(1)); continue
            stripped = l.strip()
            depth += l.count("/-") - l.count("-/")
            if depth > 0 or stripped == "" or stripped.startswith("--") or stripped.startswith("/-") \
                    or stripped.endswith("-/"):
                body.append(l); continue
            in_header = False
        body.append(l)
    return imports, "\n".join(body).rstrip() + "\n"


def open_scopes(text):
    """Scopes still open at the end of the file, outermost first, from comment-stripped text."""
    st = []
    for l in strip_comments(text).splitlines():
        m = SCOPE.match(l)
        if not m:
            continue
        kind, name = m.group(1), m.group(2)
        if kind == "end":
            if st:
                st.pop()
            continue
        if kind == "mutual":
            st.append(("mutual", ""))
        elif kind == "namespace":
            st.append(("namespace", name))
        else:  # section / noncomputable section, optional name
            st.append(("section", name if name and not name.startswith("--") else ""))
    return st


def closers(scopes):
    out = []
    for kind, name in reversed(scopes):
        if kind == "mutual":
            raise ValueError("file ends inside a mutual block")
        out.append(f"end {name}".rstrip())
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("baseline", type=pathlib.Path)
    ap.add_argument("out", type=pathlib.Path)
    ap.add_argument("--cap", type=int, default=40, help="max declarations in a merged file")
    ap.add_argument("--seeds", type=int, default=20)
    ap.add_argument("--no-refolder", action="store_true")
    ap.add_argument("--isolate", type=pathlib.Path, default=HERE.parent / "isolate.txt",
                    help="original modules never merged (one per line); grown by isolate_failures.py")
    ap.add_argument("--layout", type=pathlib.Path, default=HERE.parent / "layout.json",
                    help="persisted folder of every original module; created on first run")
    ap.add_argument("--recluster", action="store_true", help="ignore --layout and run Louvain again")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()

    src = a.baseline / "src"
    files = sorted(src.rglob("*.lean"))
    mod = lambda f: ".".join(f.relative_to(src).with_suffix("").parts)
    text = {mod(f): f.read_text() for f in files}
    order = {m: k for k, m in enumerate(text)}
    parsed = {m: split_file(t) for m, t in text.items()}
    proj_imports = {m: [i for i in imp if i in text and i != m] for m, (imp, _) in parsed.items()}
    ext_imports = {m: [i for i in imp if i not in text] for m, (imp, _) in parsed.items()}
    decls = {m: len(DECL.findall(strip_comments(t))) for m, t in text.items()}

    iso = set()
    if a.isolate.exists():
        iso = {l.split("#")[0].strip() for l in a.isolate.read_text().splitlines()} - {""}
        unknown = iso - set(text)
        if unknown:
            print("warning: isolate entries not in baseline:", sorted(unknown))

    # ---- merge to fixed point ------------------------------------------------------------
    owner = {m: m for m in text}                 # original module -> surviving module
    members = {m: [m] for m in text}             # surviving module -> original members
    imp = {m: list(v) for m, v in proj_imports.items()}  # surviving graph
    size = dict(decls)
    while True:
        importers = collections.defaultdict(list)
        for m, v in imp.items():
            for i in v:
                importers[i].append(m)
        cand = [(size[x], order[x], x, ims[0]) for x, ims in importers.items()
                if len(ims) == 1 and x not in PROTECTED and ims[0] not in PROTECTED
                and x not in iso and ims[0] not in iso
                and size[x] + size[ims[0]] <= a.cap]
        if not cand:
            break
        _, _, x, b = min(cand)
        members[b] = members[x] + members[b]
        for o in members.pop(x):
            owner[o] = b
        size[b] += size.pop(x)
        imp[b] = list(dict.fromkeys(i for i in imp[b] + imp.pop(x) if i not in (x, b)))
        for m in imp:
            imp[m] = list(dict.fromkeys(b if i == x else i for i in imp[m] if not (m == b and i == x)))
            imp[m] = [i for i in imp[m] if i != m]

    # ---- re-folder ----------------------------------------------------------------------
    # folder of every ORIGINAL module ("Top.Cluster"), persisted so regeneration is stable
    folder = {}
    if a.layout.exists() and not a.recluster and not a.no_refolder:
        folder = json.loads(a.layout.read_text())
    elif not a.no_refolder:
        G = nx.Graph(); G.add_nodes_from(imp)
        G.add_edges_from((m, i) for m, v in imp.items() for i in v)
        best = max((louvain_communities(G, seed=s) for s in range(a.seeds)), key=lambda c: modularity(G, c))
        used = set()
        for comm in sorted(best, key=lambda c: (-sum(size[m] for m in c), min(c))):
            movable = [m for m in comm if m not in PROTECTED]
            if not movable:
                continue
            w2 = collections.Counter(); wt = collections.Counter()
            for m in movable:
                p = m.split(".")
                w2[p[2] if p[1] == "General" and len(p) > 3 else p[1] if len(p) > 2 else p[-1]] += size[m] + 1
                wt[p[0]] += size[m] + 1
            top = wt.most_common(1)[0][0] if wt.most_common(1)[0][0] in ("Lib", "New") else "Lib"
            base = re.sub(r"[^A-Za-z0-9]", "", w2.most_common(1)[0][0]) or "Misc"
            base = base[0].upper() + base[1:]
            name, k = base, 2
            while (top, name) in used:
                name, k = f"{base}{k}", k + 1
            used.add((top, name))
            for m in movable:
                for o in members[m]:
                    folder[o] = f"{top}.{name}"
        if not a.dry_run:
            a.layout.write_text(json.dumps(dict(sorted(folder.items())), indent=0))
    newname, leaves = {}, collections.defaultdict(set)
    for m in sorted(imp, key=lambda m: order[m]):
        if m in PROTECTED or not folder:
            newname[m] = m; continue
        f = folder.get(m) or ".".join(m.split(".")[:2])   # module unseen in layout: keep its old folder
        leaf, j = m.split(".")[-1], 2
        while leaf in leaves[f]:
            leaf, j = f"{m.split('.')[-1]}{j}", j + 1
        leaves[f].add(leaf)
        newname[m] = f"{f}.{leaf}"
    final = {o: newname[owner[o]] for o in text}

    # ---- emit ----------------------------------------------------------------------------
    out_files = {}
    for surv, mem in members.items():
        mem_set = set(mem)
        # topological order of the original members (Kahn, ties by original order)
        indeg = {m: sum(1 for i in proj_imports[m] if i in mem_set) for m in mem}
        ready = sorted((m for m in mem if indeg[m] == 0), key=order.get)
        topo = []
        while ready:
            m = ready.pop(0); topo.append(m)
            for n in mem:
                if m in proj_imports[n]:
                    indeg[n] -= 1
                    if indeg[n] == 0:
                        ready.append(n); ready.sort(key=order.get)
        if len(topo) != len(mem):
            raise SystemExit(f"cycle inside merged module {surv}")
        me = newname[surv]
        ext = list(dict.fromkeys(i for m in topo for i in ext_imports[m]))
        prj = list(dict.fromkeys(final[i] for m in topo for i in proj_imports[m] if final[i] != me))
        head = "".join(f"import {i}\n" for i in ext + prj)
        if len(topo) == 1:
            body = parsed[topo[0]][1]
            out = head + ("\n" if not body.startswith("\n") else "") + body
        else:
            parts = []
            for m in topo:
                body = parsed[m][1].strip("\n")
                cl = closers(open_scopes(body))
                parts.append(f"-- part: {m}\nsection\n{body}\n" + "".join(c + "\n" for c in cl) + "end\n")
            out = head + "\n" + "\n".join(parts)
        out_files[me] = out

    report = dict(modules_before=len(text), modules_after=len(out_files),
                  merged_groups=sum(1 for v in members.values() if len(v) > 1),
                  largest_group=max(len(v) for v in members.values()),
                  decls_per_file=sum(decls.values()) / len(out_files))
    print(json.dumps(report))
    if a.dry_run:
        return

    a.out.mkdir(parents=True, exist_ok=True)
    for name in ["lakefile.toml", "lake-manifest.json", "lean-toolchain", "Challenge.lean",
                 "comparator.json", "LICENSE", "NOTICE", "ATTRIBUTION.md"]:
        if (a.baseline / name).exists():
            shutil.copy2(a.baseline / name, a.out / name)
    (a.out / "scripts").mkdir(exist_ok=True)
    shutil.copy2(a.baseline / "scripts" / "PrintAxioms.lean", a.out / "scripts" / "PrintAxioms.lean")
    if (a.out / "src").exists():
        shutil.rmtree(a.out / "src")
    for m, t in out_files.items():
        p = a.out / "src" / pathlib.Path(*m.split(".")).with_suffix(".lean")
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(t)
    shutil.copy2(src / "Statements.lean", a.out / "src" / "Statements.lean")  # byte-identical
    (a.out / "RESTRUCTURE_MAP.json").write_text(json.dumps(
        dict(report=report, module_map=final,
             groups={newname[s]: m for s, m in members.items()}), indent=1))


if __name__ == "__main__":
    main()
