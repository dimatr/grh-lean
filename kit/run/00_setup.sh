#!/usr/bin/env bash
# One-time setup: Python deps, elan + Lean v4.35.0, generated work/ project, Mathlib cache.
source "$(dirname "$0")/env.sh"

say "Python"
"$PY" -c 'import networkx' 2>/dev/null || "$PY" -m pip install --user networkx \
  || "$PY" -m pip install --user --break-system-packages networkx
"$PY" -c 'import networkx; print("networkx", networkx.__version__)'

say "elan / Lean"
if ! command -v elan >/dev/null; then
  echo "elan not found - installing to ~/.elan (official installer)"
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
  export PATH="$HOME/.elan/bin:$PATH"
fi
cat "$BASE/lean-toolchain"

say "Generate work/ (restructure)"
[ -f "$WORK/RESTRUCTURE_MAP.json" ] || "$KIT/run/10_restructure.sh"

say "Mathlib cache (pinned 56a00585, several GB, once)"
cd "$WORK"
lake --version
lake exe cache get
echo
echo "Machine: $CORES cores, ${MEM_GB} GB RAM -> default build jobs: $JOBS"
echo "Setup done. Next: ./run/20_build.sh"
