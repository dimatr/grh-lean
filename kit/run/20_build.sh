#!/usr/bin/env bash
# Build Main (what the challenge gate builds). Incremental: only changed modules rebuild.
#   ./run/20_build.sh            work/ project
#   ./run/20_build.sh baseline   pristine project (reference timing; optional)
#   JOBS=8 ./run/20_build.sh     override parallelism
source "$(dirname "$0")/env.sh"
P="$WORK"; [ "${1:-}" = "baseline" ] && P="$BASE"
cd "$P"
[ -d .lake/packages/mathlib ] || lake exe cache get
ulimit -s unlimited 2>/dev/null || ulimit -s 1048576 || true

# Lake v4.35 has no -j flag. Build jobs run on the runtime's shared worker pool, sized by
# LEAN_NUM_THREADS (default: all hardware threads). The value is inherited by each lean child,
# where it also caps per-file parallel proof checking.
export LEAN_NUM_THREADS="$JOBS"
echo "workers: LEAN_NUM_THREADS=$JOBS (cores $CORES, RAM ${MEM_GB} GB)"

LOG="$LOGS/build-$(basename "$P")-$(ts).log"
say "lake build Main  ->  $LOG"
START=$(date +%s)
set +e
lake build Main 2>&1 | tee "$LOG"
RC=${PIPESTATUS[0]}
set -e
echo "wall time: $(( ($(date +%s) - START) / 60 )) min, exit $RC"
"$PY" "$KIT/tools/extract_errors.py" "$LOG" "$P" > "$LOGS/errors-latest.txt"
cp "$LOG" "$LOGS/build-latest.log"
head -15 "$LOGS/errors-latest.txt"
if [ "$RC" -ne 0 ]; then
  echo; echo "BUILD FAILED. Send logs/errors-latest.txt back to Claude."
  exit "$RC"
fi
echo "BUILD OK. Next: ./run/30_check.sh"
