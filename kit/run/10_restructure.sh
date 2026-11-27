#!/usr/bin/env bash
# Regenerate grh-compact/src (tracked) from the pristine baseline (merge single-use modules + re-folder by Louvain).
# Extra args go to tools/restructure.py, e.g.  ./run/10_restructure.sh --cap 50
# Keeps grh-compact/.lake (Mathlib and build cache) intact.
source "$(dirname "$0")/env.sh"
say "Restructure baseline -> work"
"$PY" "$KIT/tools/restructure.py" "$BASE" "$WORK" "$@"
say "Static checks"
"$PY" "$KIT/tools/verify_static.py" "$WORK"
say "Local score (formula replica)"
"$PY" "$KIT/tools/score.py" "$WORK" | head -7
