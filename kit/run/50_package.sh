#!/usr/bin/env bash
# Assemble the submission folder: submission/proof/src/** (.lean only, no binaries, no symlinks).
# Does NOT submit. Submitting is your step:  playground submit --challenge-id <ID> --outputs submission
source "$(dirname "$0")/env.sh"
OUTD="$KIT/submission"
rm -rf "$OUTD"; mkdir -p "$OUTD/proof"
( cd "$WORK" && find src -name '*.lean' -print0 | xargs -0 -I{} cp --parents {} "$OUTD/proof/" )
"$PY" - "$OUTD/proof" <<'EOF'
import hashlib, pathlib, sys
p = pathlib.Path(sys.argv[1])
st = p / "src" / "Statements.lean"
assert hashlib.sha256(st.read_bytes()).hexdigest().startswith("79ef7ca7"), "Statements.lean changed"
bad = [x for x in p.rglob("*") if x.is_symlink() or (x.is_file() and x.suffix != ".lean")]
assert not bad, bad
print(sum(1 for _ in p.rglob("*.lean")), ".lean files packaged; Statements.lean identical")
EOF
tar -czf "$KIT/submission-$(ts).tar.gz" -C "$OUTD" proof
echo "Packaged: $OUTD  (+ tarball in $KIT)"
echo "Submit (needs your Playground login):"
echo "  playground submit --challenge-id <CHALLENGE_ID> --outputs $OUTD"
