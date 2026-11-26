# Common settings, sourced by every run script.
set -euo pipefail
KIT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
REPO="$(cd "$KIT/.." && pwd)"
BASE_REV="${BASE_REV:-upstream-72fead1}"   # pristine upstream commit (lsernau/grh-lean 72fead1)
BASE="$KIT/baseline"          # pristine grh-compact, extracted from BASE_REV; git-ignored
WORK="$REPO/grh-compact"      # tracked working project: what gets built, committed, submitted
LOGS="$KIT/logs"; mkdir -p "$LOGS"
PY="${PYTHON:-python3}"
export PATH="$HOME/.elan/bin:$PATH"

# (Re)create the pristine baseline from git when missing.
if [ ! -f "$BASE/src/Statements.lean" ]; then
  git -C "$REPO" rev-parse -q --verify "$BASE_REV^{commit}" >/dev/null 2>&1 \
    || git -C "$REPO" fetch -q --depth 1 https://github.com/lsernau/grh-lean 72fead102f663d5c7a407964a13dc0cf9d977207
  REV="$(git -C "$REPO" rev-parse -q --verify "$BASE_REV^{commit}" 2>/dev/null || echo 72fead102f663d5c7a407964a13dc0cf9d977207)"
  rm -rf "$BASE"; mkdir -p "$BASE"
  git -C "$REPO" archive "$REV" grh-compact | tar -x -C "$BASE" --strip-components=1
fi

# Build workers (exported as LEAN_NUM_THREADS by 20_build.sh): limited by cores and by RAM
# (~3 GB per Lean process on average, peaks ~9 GB). Override with JOBS=N ./kit/run/20_build.sh
CORES=$(nproc 2>/dev/null || sysctl -n hw.ncpu)
MEM_GB=$(awk '/MemTotal/ {printf "%d", $2/1048576}' /proc/meminfo 2>/dev/null || echo 32)
AUTO_JOBS=$(( MEM_GB / 3 )); [ "$AUTO_JOBS" -lt 1 ] && AUTO_JOBS=1
[ "$AUTO_JOBS" -gt "$CORES" ] && AUTO_JOBS=$CORES
JOBS="${JOBS:-$AUTO_JOBS}"

ts() { date +%Y%m%d-%H%M%S; }
say() { printf '\n\033[1m== %s\033[0m\n' "$*"; }
