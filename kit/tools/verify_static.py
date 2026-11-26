#!/usr/bin/env python3
"""Pre-build checks on a project (seconds, no Lean): imports resolve, import graph acyclic,
imports only in the header, scopes balanced per merged part, pinned Statements, forbidden tokens.

    python3 verify_static.py <project>     exit code 1 on any problem
"""
import hashlib, pathlib, re, sys
import networkx as nx
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from score import strip_comments, gate_static, load  # noqa: E402

proj = pathlib.Path(sys.argv[1])
root, mods, raw, code = load(proj)
problems = list(gate_static(proj, root, mods, raw))
G = nx.DiGraph(); G.add_nodes_from(mods)
for m, s in code.items():
    seen_code = False
    for l in s.splitlines():
        mm = re.match(r"^import\s+(\S+)", l)
        if mm:
            if seen_code:
                problems.append(f"{m}: import after code: {l}")
            tgt = mm.group(1)
            if tgt.startswith("Mathlib") or tgt == "Mathlib":
                continue
            if tgt not in mods:
                problems.append(f"{m}: unresolved import {tgt}")
            else:
                G.add_edge(m, tgt)
        elif l.strip():
            seen_code = True
    opened = 0
    for l in s.splitlines():
        k = re.match(r"^\s*(noncomputable\s+section|section|namespace|mutual|end)\b", l)
        if k:
            opened += -1 if k.group(1) == "end" else 1
            if opened < 0:
                problems.append(f"{m}: more `end` than opened scopes"); break
if not nx.is_directed_acyclic_graph(G):
    problems.append("import cycle: " + " -> ".join(nx.find_cycle(G)[0]))
if "Main" in mods and "New.Main" not in mods:
    pass
for p in problems[:50]:
    print("!", p)
print(f"verify_static: {len(mods)} modules, {G.number_of_edges()} project imports, "
      f"{'OK' if not problems else str(len(problems)) + ' problem(s)'}")
sys.exit(1 if problems else 0)
