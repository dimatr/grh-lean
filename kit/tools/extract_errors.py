#!/usr/bin/env python3
"""Condense a `lake build` log into errors.txt: each error with its message and 4 lines of source.

    python3 extract_errors.py <build.log> <project> > errors.txt
Send errors.txt back to Claude; it is small even when the log is huge.
"""
import collections, pathlib, re, sys

log = pathlib.Path(sys.argv[1]).read_text(errors="replace").splitlines()
proj = pathlib.Path(sys.argv[2])
HEAD = re.compile(r"^(?:error|✖.*?error):?\s*(?:\./)*(src/[^:]+\.lean):(\d+):(\d+):\s*(.*)$")
blocks, cur = [], None
for l in log:
    m = HEAD.match(l.strip())
    if m:
        cur = dict(file=m.group(1), line=int(m.group(2)), col=int(m.group(3)), msg=[m.group(4)])
        blocks.append(cur); continue
    if cur is not None:
        if re.match(r"^(warning|error|info|✖|⚠|✔|Build|Some required)", l.strip()) or not l.strip():
            cur = None
        elif len(cur["msg"]) < 12:
            cur["msg"].append(l.rstrip())
other = [l for l in log if re.match(r"^error:", l.strip()) and not HEAD.match(l.strip())]
byfile = collections.Counter(b["file"] for b in blocks)
print(f"# {len(blocks)} located errors in {len(byfile)} files; {len(other)} other error lines")
for f, n in byfile.most_common():
    print(f"#   {n:3d}  {f}")
for b in blocks[:150]:
    print(f"\n== {b['file']}:{b['line']}:{b['col']}")
    print("\n".join(b["msg"]))
    p = proj / b["file"]
    if p.exists():
        src = p.read_text().splitlines()
        for k in range(max(0, b["line"] - 3), min(len(src), b["line"] + 1)):
            print(f"   {k + 1:5d}| {src[k]}")
if other:
    print("\n# other errors")
    print("\n".join(dict.fromkeys(other)))
