#!/usr/bin/env python3
"""Graph-only what-if: merge single-importer modules into their importer, then re-folder.

No Lean is touched. Estimates P2/P3/P5 after Phase A so we know the ceiling before editing.
Usage: python3 simulate_merge.py <project-dir> [--max-dpf 26]
"""
import argparse, collections, math, pathlib, re, sys
import networkx as nx
from networkx.algorithms.community import louvain_communities, modularity
sys.path.insert(0, str(pathlib.Path(__file__).parent))
from score import load, IMPORT, DECL, clamp

ap = argparse.ArgumentParser(); ap.add_argument("project", type=pathlib.Path)
ap.add_argument("--max-dpf", type=float, default=26.0, help="do not grow a file beyond this many decls x factor")
ap.add_argument("--cap", type=int, default=60, help="max decls in one merged file")
a = ap.parse_args()
root, mods, raw, code = load(a.project)
imports = {m: list(dict.fromkeys(i for i in IMPORT.findall(s) if i in mods and i != m)) for m, s in code.items()}
decls = {m: len(DECL.findall(s)) for m, s in code.items()}
protected = {"Statements", "Main"}


def metrics(imports, decls, folder_of):
    indeg = collections.Counter(i for v in imports.values() for i in v)
    imported = [m for m in imports if indeg[m] > 0]
    one = 100 * sum(indeg[m] == 1 for m in imported) / len(imported)
    G = nx.Graph(); G.add_nodes_from(imports)
    G.add_edges_from((m, i) for m, v in imports.items() for i in v)
    groups = collections.defaultdict(set)
    for m in G: groups[folder_of(m)].add(m)
    qf = modularity(G, groups.values()); ql = modularity(G, louvain_communities(G, seed=42))
    dpf = sum(decls.values()) / len(imports)
    S_reuse = clamp(50 + (53.0 - one) * (40 / 24.9))
    S_tax = clamp(50 + (100 * qf / ql - 71.5) * (35 / 13))
    S_gran = 100 * math.exp(-0.5 * (math.log(dpf / 21.3) / 0.55) ** 2)
    return dict(files=len(imports), one_use=one, align=100 * qf / ql, dpf=dpf,
                S_reuse=S_reuse, S_tax=S_tax, S_gran=S_gran), G


l2 = lambda m: ".".join(m.split(".")[:2]) if "." in m else "<root>"
base, _ = metrics(imports, decls, l2)
print("baseline        ", {k: round(v, 2) for k, v in base.items()})

# greedy merge: absorb a single-importer module into its importer while the result stays <= cap decls
imp = {m: list(v) for m, v in imports.items()}; dc = dict(decls)
changed = True
while changed:
    changed = False
    indeg = collections.defaultdict(list)
    for m, v in imp.items():
        for i in v: indeg[i].append(m)
    for a_mod, importers in sorted(indeg.items(), key=lambda kv: dc.get(kv[0], 0)):
        if a_mod in protected or a_mod not in imp or len(importers) != 1:
            continue
        b = importers[0]
        if b not in imp or dc[a_mod] + dc[b] > a.cap:
            continue
        imp[b] = list(dict.fromkeys([i for i in imp[b] if i != a_mod] + [i for i in imp[a_mod] if i != b]))
        dc[b] += dc.pop(a_mod); del imp[a_mod]
        for m in imp: imp[m] = list(dict.fromkeys(b if i == a_mod else i for i in imp[m] if not (m == b and i == a_mod)))
        imp[b] = [i for i in imp[b] if i != b]
        changed = True
        break  # recompute in-degrees after each merge (cheap at this size)
merged, G = metrics(imp, dc, l2)
print("merged, old dirs", {k: round(v, 2) for k, v in merged.items()})

# re-folder: level-2 folder := Louvain community (best of 20 seeds)
best = max((louvain_communities(G, seed=s) for s in range(20)), key=lambda c: modularity(G, c))
comm = {m: f"C{k}" for k, c in enumerate(best) for m in c}
refold, _ = metrics(imp, dc, lambda m: comm[m])
print("merged, Louvain dirs", {k: round(v, 2) for k, v in refold.items()})
S = 0.4 * 50 + 0.2 * refold["S_reuse"] + 0.15 * refold["S_tax"] + 0.15 * 100 + 0.1 * refold["S_gran"]
print(f"projected total with S_tok=50 (no token change) and S_dedup=100: {S:.2f}")
