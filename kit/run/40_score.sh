#!/usr/bin/env bash
# Local replica of the 5-pillar score (seconds). Baseline replica = 51.27 (published 51.28).
source "$(dirname "$0")/env.sh"
say "baseline"; "$PY" "$KIT/tools/score.py" "$BASE" | head -6
say "grh-compact (work)";     "$PY" "$KIT/tools/score.py" "$WORK" "$@" | tee "$LOGS/score-latest.txt"
