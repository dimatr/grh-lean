#!/usr/bin/env bash
# Gate checks after a successful build: static guard + exact axiom set of the 5 theorems.
# (The official gate also replays the environment through the kernel; the restructure only
#  moves declarations, so a passing build + axiom check makes a replay failure very unlikely.
#  Optional independent replay: Comparator with nanoda, see README.)
source "$(dirname "$0")/env.sh"
cd "$WORK"
say "Static guard"
"$PY" "$KIT/tools/verify_static.py" "$WORK"
say "Axioms of the five theorems"
OUT="$LOGS/axioms-latest.txt"
ulimit -s unlimited 2>/dev/null || true
lake env lean scripts/PrintAxioms.lean 2>&1 | tee "$OUT"
N=$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]" "$OUT" || true)
BAD=$(grep -E "depends on axioms|sorryAx|does not depend" "$OUT" | grep -vc "\[propext, Classical.choice, Quot.sound\]" || true)
for t in riemannHypothesis riemannZeta_eq_zero_re LFunction_ne_zero_of_half_lt_re \
         LFunction_eq_zero_re LFunction_eq_zero_re_of_isPrimitive; do
  grep -q "'$t' depends on axioms" "$OUT" || { echo "MISSING: $t"; BAD=$((BAD+1)); }
done
if [ "$N" -eq 5 ] && [ "$BAD" -eq 0 ]; then echo "AXIOMS OK (5/5)"; else echo "AXIOM CHECK FAILED"; exit 1; fi
