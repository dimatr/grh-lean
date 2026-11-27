#!/usr/bin/env bash
# Full pipeline: setup -> restructure -> build/fix loop -> check -> score -> package. Stops at first failure.
source "$(dirname "$0")/env.sh"
R="$KIT/run"
"$R/00_setup.sh"
"$R/10_restructure.sh" "$@"
"$R/25_fix_loop.sh"
"$R/30_check.sh"
"$R/40_score.sh"
"$R/50_package.sh"
