#!/usr/bin/env python3
"""Map located build errors back to ORIGINAL modules and add them to kit/isolate.txt.

    python3 isolate_failures.py <build.log> <project> [--isolate kit/isolate.txt]

An error at src/X.lean:L belongs to the original module whose `-- part: <Module>` marker is the
last one above line L; a file without markers is a single original module (RESTRUCTURE_MAP.json).
Only errors inside MERGED files are isolated: an error in a file that was not merged is not caused
by merging, so it is reported and the script exits 2 (needs a human / Claude).
Exit 0: new modules isolated. Exit 1: nothing new to isolate. Exit 2: non-merge errors present.
"""
import argparse, json, pathlib, re, sys

ap = argparse.ArgumentParser()
ap.add_argument("log", type=pathlib.Path)
ap.add_argument("project", type=pathlib.Path)
ap.add_argument("--isolate", type=pathlib.Path,
                default=pathlib.Path(__file__).resolve().parent.parent / "isolate.txt")
a = ap.parse_args()

HEAD = re.compile(r"error:?\s*(?:\./)*(src/[^:\s]+\.lean):(\d+):(\d+):")
groups = json.loads((a.project / "RESTRUCTURE_MAP.json").read_text())["groups"]
hits = {(m.group(1), int(m.group(2))) for l in a.log.read_text(errors="replace").splitlines()
        for m in [HEAD.search(l)] if m}
if not hits:
    print("no located errors in log"); sys.exit(1)

have = set()
if a.isolate.exists():
    have = {l.split("#")[0].strip() for l in a.isolate.read_text().splitlines()} - {""}
new, foreign = {}, []
for f, line in sorted(hits):
    mod = ".".join(pathlib.Path(f).relative_to("src").with_suffix("").parts)
    members = groups.get(mod, [mod])
    if len(members) == 1:
        foreign.append(f"{f}:{line} (not a merged file: {members[0]})"); continue
    src = (a.project / f).read_text().splitlines()
    owner = None
    for k in range(min(line, len(src)) - 1, -1, -1):
        mm = re.match(r"^-- part: (\S+)$", src[k])
        if mm:
            owner = mm.group(1); break
    if owner is None:
        foreign.append(f"{f}:{line} (in merged file header, before any part)"); continue
    if owner not in have:
        new.setdefault(owner, f"{f}:{line}")

if new:
    with a.isolate.open("a") as fh:
        for m, where in new.items():
            fh.write(f"{m}  # {where}\n")
    print(f"isolated {len(new)} module(s):", *new, sep="\n  ")
for x in foreign:
    print("  ! not fixable by un-merging:", x)
sys.exit(2 if foreign and not new else 0 if new else 1)
