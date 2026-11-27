# grh-compact kit — RH Season 2 (Bohrium), Phase A

Everything needed to restructure, build, check, score and package an entry for
"Riemann Hypothesis — Season 2: 76k Compact Proof Compression (grh-compact)".
Linux or WSL2 (clone inside the Linux filesystem, not under /mnt/c).

    git clone https://github.com/dimatr/grh-lean && cd grh-lean && git checkout kit/phase-a

## Layout (fork dimatr/grh-lean)
    grh-compact/      the working project, tracked: restructure writes src/ here, git diff shows it
    kit/tools/        score.py (local score replica), restructure.py, verify_static.py,
                      extract_errors.py, simulate_merge.py
    kit/run/          numbered scripts (run from the repo root or anywhere)
    kit/baseline/     pristine grh-compact extracted from upstream 72fead1 (tag upstream-72fead1),
                      git-ignored, recreated automatically
    kit/logs/         build logs, errors-latest.txt, axioms-latest.txt, score-latest.txt (ignored)

Workflow: one branch per phase (kit/phase-a, kit/dedup, ...), PRs into the fork's main.
Upstream does not accept contributions; nothing is sent to lsernau/grh-lean.

## Run
    ./kit/run/00_setup.sh        once: networkx, elan + Lean v4.35.0, Mathlib cache (several GB)
    ./kit/run/10_restructure.sh  regenerate grh-compact/src (seconds); args pass through, e.g. --cap 50
    ./kit/run/20_build.sh        lake build Main; JOBS=N to set workers (LEAN_NUM_THREADS)
    ./kit/run/25_fix_loop.sh     build; un-merge original modules whose part fails; regenerate;
                                 rebuild; repeat (MAX_ROUNDS=6). Commits each round locally.
    ./kit/run/30_check.sh        static guard + all 5 theorems use only propext/Classical.choice/Quot.sound
    ./kit/run/40_score.sh        local 5-pillar score, baseline vs grh-compact
    ./kit/run/50_package.sh      submission/proof/src/** + tarball; prints the submit command
    ./kit/run/all.sh             all of the above in order

`./kit/run/20_build.sh baseline` builds the untouched project once, for a reference time.
Optional, not needed for Phase A.

## Build resources
Challenge reference: 17.6 min on 32 cores, ~8.8 GiB peak per Lean process, 37.7 GiB in total.
README of the repo: 1–2 h on 12 cores with 24 GB. Workers = `LEAN_NUM_THREADS` (Lake v4.35 has no -j);
`env.sh` defaults it to min(cores, RAM_GB/3); override with `JOBS=N ./kit/run/20_build.sh`.
Lean does not use the GPU.

## When the build fails
Send back `logs/errors-latest.txt` (condensed: message + source lines per error).
`logs/build-latest.log` is the full log, if asked.

## What Phase A does (tools/restructure.py)
1. Merges every module imported by exactly one other module into that importer, while the merged
   file stays <= 40 declarations (--cap). Main and Statements are never merged.
   Each original file becomes one `section ... end` block, in import order, with the scopes it
   left open closed first, so `open`/`variable`/`set_option`/local attributes stay scoped.
2. Re-folders modules as Lib|New/<Cluster>/<Leaf>.lean, Cluster = Louvain community of the merged
   import graph (keeps the fixed lakefile's Lib.+ / New.+ globs valid).
   The folder of every original module is persisted in kit/layout.json (committed), so
   regeneration is identical on every machine and only touches files that really change.
   Use --recluster to recompute it.
3. kit/isolate.txt lists original modules kept out of merging: merging changes the context a
   part elaborates in (union of imports, sibling lemmas), and a few simp/grind/aesop proofs break.
   Each merged file marks its parts with `-- part: <OriginalModule>` comments for this mapping.
4. Statements.lean is copied byte-identical. RESTRUCTURE_MAP.json records old -> new modules.

Local score replica: baseline 51.27, after Phase A 72.41
(P2 reuse, P3 taxonomy, P5 granularity at ~100; P1 tokens and P4 duplicate names unchanged).

## Not yet in the kit
- P4 (duplicate leaf names, +7.5 max): renaming dot-notation lemmas (`IsRapid.mul` …) needs
  call-site fixes through compile errors.
- P1 (tokens, 40% weight): real proof shortening.
- Independent kernel replay (Comparator + nanoda, see the repo README) — optional before submitting.

## Scorer calibration (rules inferred; formulas from the challenge page)
| pillar | published baseline | replica |
|---|---|---|
| tokens | 1,620,584 | 1,617,931 (S_tok uses the ratio to this count) |
| one-use modules | 53.0% | 52.96% |
| taxonomy align | 71.6% | 71.73% (Louvain seed 42; seed spread 70.1–73.1%) |
| duplicate names | 4.22% | 4.26% |
| decls / file | 12.47 | 12.47 (9905 decls) |
