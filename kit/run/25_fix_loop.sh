#!/usr/bin/env bash
# Build; if parts of merged files fail, un-merge exactly those original modules, regenerate,
# rebuild (incremental: only changed files and their dependents). Repeat up to MAX_ROUNDS.
# Each round is committed locally (not pushed) so the history shows what was isolated and why.
#   ./kit/run/25_fix_loop.sh            MAX_ROUNDS=6 by default
# Stops when: build OK | an error is not in a merged part (needs a human) | nothing new to isolate.
source "$(dirname "$0")/env.sh"
MAX_ROUNDS="${MAX_ROUNDS:-6}"
for round in $(seq 1 "$MAX_ROUNDS"); do
  say "Round $round/$MAX_ROUNDS: build"
  if "$KIT/run/20_build.sh"; then
    say "BUILD OK after $round round(s)"; exit 0
  fi
  say "Round $round: isolate failing parts"
  set +e
  "$PY" "$KIT/tools/isolate_failures.py" "$LOGS/build-latest.log" "$WORK" --isolate "$KIT/isolate.txt"
  RC=$?
  set -e
  if [ "$RC" -ne 0 ]; then
    echo; echo "Stopped: errors not fixable by un-merging (exit $RC)."
    echo "Send kit/logs/errors-latest.txt to Claude."; exit 1
  fi
  "$KIT/run/10_restructure.sh" | grep -E 'modules_after|verify_static|SCORE' || true
  git -C "$REPO" add -A "$WORK" "$KIT/isolate.txt"
  NEWLINES=$(git -C "$REPO" diff --cached -U0 -- "$KIT/isolate.txt" | grep '^+[^+]' | sed 's/^+/- /')
  git -C "$REPO" commit -q -m "fix loop round $round: un-merge modules failing inside merged files

$NEWLINES" || true
done
echo "Reached MAX_ROUNDS=$MAX_ROUNDS without a clean build. Send kit/logs/errors-latest.txt to Claude."
exit 1
