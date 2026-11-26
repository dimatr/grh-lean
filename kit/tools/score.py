#!/usr/bin/env python3
"""Local replica of the Bohrium "RH Season 2 (grh-compact)" 5-pillar score.

Usage:  python3 score.py <project-dir> [--json] [--seed 42] [--seeds N]
        <project-dir> holds src/ (Statements.lean, Main.lean, Lib/, New/, ...).

Formulas are copied from the challenge page. The counting rules were not published;
the ones below were reverse-engineered against the published baseline telemetry:

  pillar  published baseline        this replica on baseline   rule used
  P1      T0 = 1,620,584 tokens     1,617,931 (-0.16%)          split dotted ids, merge := -> <- etc.
                                                                 S_tok uses T / T_REF (our own baseline
                                                                 count), so the offset cancels
  P2      one_use 53.0%             52.96%                      imported modules (in_deg>0), in_deg==1
  P3      align 71.6%               71.73% (Louvain seed 42)    Q(level-2 folders)/Q(Louvain), undirected
  P4      dup 4.22%                 4.255% (thm+lemma+def)      (N - distinct leaf names)/N
                                    3.795% (thm+lemma only)     -- rule not pinned down, gap <= 0.07 pts
  P5      12.47 dpf, 9905 decls     12.47, 9905                 theorem|lemma|def|instance, not
                                                                 local/scoped; files = all src/*.lean
"""
import argparse, collections, hashlib, json, math, pathlib, re, statistics, sys

T0_OFFICIAL = 1_620_584
T_REF = 1_617_931          # this tokenizer on the pristine grh-compact baseline
STATEMENTS_SHA = "79ef7ca776e42abe1f46caee13ea09bd19f1e2d0b1620d8d5d200258f33b47bf"
FORBIDDEN = ["addDeclUnsafe", "setEnv", "modifyEnv", "sorryAx", "unsafe", "@[extern",
             "@[implemented_by", "implemented_by", "sorry", "axiom "]
BINARY_EXT = {".olean", ".ilean", ".so", ".c", ".o", ".a", ".dylib", ".dll"}

clamp = lambda x: max(0.0, min(100.0, x))


def strip_comments(s: str) -> str:
    out, i, d, n = [], 0, 0, len(s)
    while i < n:
        if s.startswith("/-", i):
            d += 1; i += 2; continue
        if d and s.startswith("-/", i):
            d -= 1; i += 2; continue
        if d:
            i += 1; continue
        if s.startswith("--", i):
            j = s.find("\n", i); i = n if j < 0 else j; continue
        out.append(s[i]); i += 1
    return "".join(out)


ID = r"[^\W\d][\w'!?₀-₉ᵢ-ᵪ]*"
TOKEN = re.compile(rf"{ID}|\d+(?:\.\d+)?|:=|<;>|->|<-|<=|>=|\|\||&&|::|\.\.|=>|\S")
IMPORT = re.compile(r"^import\s+(\S+)", re.M)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                  r"(theorem|lemma|def|instance)\b", re.M)
NAMED = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                   r"(theorem|lemma|def)\s+([^\s:({\[⦃]+)", re.M)


def load(project: pathlib.Path):
    root = project / "src"
    files = sorted(root.rglob("*.lean"))
    mods = {".".join(f.relative_to(root).with_suffix("").parts): f for f in files}
    raw = {m: f.read_text() for m, f in mods.items()}
    return root, mods, raw, {m: strip_comments(s) for m, s in raw.items()}


def gate_static(project, root, mods, raw):
    issues = []
    st = root / "Statements.lean"
    if not st.exists() or hashlib.sha256(st.read_bytes()).hexdigest() != STATEMENTS_SHA:
        issues.append("Statements.lean missing or modified")
    if "Main" not in mods:
        issues.append("src/Main.lean missing")
    for p in project.rglob("*"):
        if p.is_symlink():
            issues.append(f"symlink: {p}")
        elif p.suffix in BINARY_EXT and ".lake" not in p.parts:
            issues.append(f"binary: {p}")
    for m, s in raw.items():
        if m == "Statements":
            continue
        code = strip_comments(s)
        for tok in FORBIDDEN:
            if tok in code:
                issues.append(f"{m}: contains '{tok.strip()}'")
    return issues


def score(project: pathlib.Path, seed=42, seeds=0):
    import networkx as nx
    from networkx.algorithms.community import louvain_communities, modularity

    root, mods, raw, code = load(project)
    tel = {"files": len(mods)}

    # P1 tokens (exclude Statements, comments, whitespace, import lines)
    T = 0
    for m, s in code.items():
        if m == "Statements":
            continue
        body = "\n".join(l for l in s.splitlines() if not re.match(r"\s*import\s", l))
        T += len(TOKEN.findall(body))
    tel["tokens"] = T
    tel["tokens_vs_baseline_pct"] = 100 * (T / T_REF - 1)
    S_tok = clamp(50 + 50 * (1 - T / T_REF))

    # import graph
    # keep source order: Louvain depends on edge insertion order (sorted order shifts align by ~0.3%)
    edges = {m: list(dict.fromkeys(i for i in IMPORT.findall(s) if i in mods and i != m))
             for m, s in code.items()}
    indeg = collections.Counter(i for v in edges.values() for i in v)

    # P2 one-use
    imported = [m for m in mods if indeg[m] > 0]
    one_use = 100 * sum(indeg[m] == 1 for m in imported) / max(len(imported), 1)
    tel["one_use_pct"] = one_use
    S_reuse = 0.0 if len(mods) <= 5 else clamp(50 + (53.0 - one_use) * (40.0 / (53.0 - 28.1)))

    # P3 taxonomy
    G = nx.Graph(); G.add_nodes_from(mods)
    G.add_edges_from((m, i) for m, v in edges.items() for i in v)
    groups = collections.defaultdict(set)
    for m in G:
        groups[".".join(m.split(".")[:2]) if "." in m else "<root>"].add(m)
    q_folder = modularity(G, groups.values()) if G.number_of_edges() else 0.0
    q_louv = modularity(G, louvain_communities(G, seed=seed)) if G.number_of_edges() else 0.0
    align = 100 * q_folder / max(q_louv, 1e-6)
    tel.update(q_folder=q_folder, q_louvain=q_louv, taxonomy_align_pct=align, folders_l2=len(groups))
    S_tax = 0.0 if (len(mods) <= 5 or q_louv < 0.05) else clamp(50 + (align - 71.5) * (35.0 / (84.5 - 71.5)))
    if seeds:
        qs = [modularity(G, louvain_communities(G, seed=s)) for s in range(seeds)]
        tel["align_range_pct"] = (100 * q_folder / max(qs), 100 * q_folder / statistics.median(qs),
                                  100 * q_folder / min(qs))

    # P4 duplicate leaf names
    def dup_rate(kinds):
        leaves = [n.split(".")[-1] for m, s in code.items() if m != "Statements"
                  for k, n in NAMED.findall(s) if k in kinds]
        return 100 * (len(leaves) - len(set(leaves))) / max(len(leaves), 1)
    dup = dup_rate({"theorem", "lemma", "def"})
    tel["dup_thm_pct"] = dup
    tel["dup_thm_pct_alt_thm_lemma_only"] = dup_rate({"theorem", "lemma"})
    S_dedup = clamp(50 + (4.22 - dup) * (40.0 / (4.22 - 1.14)))

    # P5 granularity
    decls = sum(len(DECL.findall(s)) for s in code.values())
    dpf = decls / max(len(mods), 1)
    tel.update(decls=decls, decls_per_file=dpf)
    S_gran = 100 * math.exp(-0.5 * (math.log(max(dpf, 0.1) / 21.3) / 0.55) ** 2)

    pillars = dict(S_tok=S_tok, S_reuse=S_reuse, S_tax=S_tax, S_dedup=S_dedup, S_gran=S_gran)
    total = 0.40 * S_tok + 0.20 * S_reuse + 0.15 * S_tax + 0.15 * S_dedup + 0.10 * S_gran
    return total, pillars, tel, gate_static(project, root, mods, raw)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("project", type=pathlib.Path)
    ap.add_argument("--seed", type=int, default=42)
    ap.add_argument("--seeds", type=int, default=0, help="also report align over N Louvain seeds")
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args()
    total, p, tel, issues = score(a.project, a.seed, a.seeds)
    if a.json:
        print(json.dumps(dict(score=total, pillars=p, telemetry=tel, static_issues=issues), indent=1))
        return
    print(f"SCORE {total:6.2f}   (static gate: {'OK' if not issues else 'FAIL'}; kernel/axiom gate needs lake build)")
    for k, v in p.items():
        print(f"  {k:8} {v:6.2f}")
    for k, v in tel.items():
        print(f"  {k:32} {v if not isinstance(v, float) else round(v, 4)}")
    for i in issues[:20]:
        print("  !", i)


if __name__ == "__main__":
    main()
