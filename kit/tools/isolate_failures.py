#!/usr/bin/env python3
"""Map located build errors back to ORIGINAL modules and add them to kit/isolate.txt.

    python3 isolate_failures.py <build.log> <project> [--isolate kit/isolate.txt]

An error at src/X.lean:L belongs to the original module whose `-- part: <Module>` marker is the
last one above line L; a file without markers is a single original module (RESTRUCTURE_MAP.json).
An error in an UNMERGED file can still be caused by merging: a definition in some merged part may
elaborate differently there (e.g. untyped binders inferred with more instances in scope) and break
its callers. For those, the constants named in the error message ("in the application ...",
"type mismatch ...") are looked up; if one is defined inside a merged part, that part is isolated.
Otherwise the error is reported and the script exits 2 (needs a human / Claude).
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
hits, msgs, cur = set(), {}, None
for l in a.log.read_text(errors="replace").splitlines():
    m = HEAD.search(l)
    if m:
        cur = (m.group(1), int(m.group(2))); hits.add(cur); msgs.setdefault(cur, []).append(l); continue
    if cur and re.match(r"^\s*(error|warning|info|✖|⚠|✔|ℹ|Build|Some required)", l):
        cur = None
    elif cur:
        msgs[cur].append(l)

# index: constant leaf name -> (file, line) of its declaration in merged files
DECL_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                     r"(?:def|abbrev|structure|class|instance|theorem|lemma|inductive|opaque)\s+([^\s:({\[⦃]+)")
decl_at = {}
for f in (a.project / "src").rglob("*.lean"):
    mod = ".".join(f.relative_to(a.project / "src").with_suffix("").parts)
    if len(groups.get(mod, [mod])) < 2:
        continue
    for k, l in enumerate(f.read_text().splitlines(), 1):
        d = DECL_RE.match(l)
        if d:
            decl_at.setdefault(d.group(1).split(".")[-1], []).append((f, k))


def part_at(path, line):
    src = path.read_text().splitlines()
    for k in range(min(line, len(src)) - 1, -1, -1):
        mm = re.match(r"^-- part: (\S+)$", src[k])
        if mm:
            return mm.group(1)
    return None


def culprits(msg_lines):
    """merged parts defining constants named in an error message"""
    out = []
    text = "\n".join(msg_lines)
    names = set(re.findall(r"in the application\s+@?([A-Za-z_][\w.'?!]*)", text))
    names |= set(re.findall(r"@([A-Z][\w.'?!]*)", text))
    for n in names:
        for f, k in decl_at.get(n.split(".")[-1], []):
            p = part_at(f, k)
            if p:
                out.append((p, n))
    return out
if not hits:
    print("no located errors in log"); sys.exit(1)

have = set()
if a.isolate.exists():
    have = {l.split("#")[0].strip() for l in a.isolate.read_text().splitlines()} - {""}
new, foreign = {}, []
# pass 1: files where some error names a constant defined in another merged part
explained = set()
for f, line in hits:
    mod = ".".join(pathlib.Path(f).relative_to("src").with_suffix("").parts)
    own = part_at(a.project / f, line) if len(groups.get(mod, [mod])) > 1 else None
    if any(p != own for p, _ in culprits(msgs.get((f, line), []))):
        explained.add(f)
for f, line in sorted(hits):
    mod = ".".join(pathlib.Path(f).relative_to("src").with_suffix("").parts)
    members = groups.get(mod, [mod])
    own = part_at(a.project / f, line) if len(members) > 1 else None
    # 1) a constant named in the message that is defined in ANOTHER merged part: blame its definition
    found = [(p, n) for p, n in culprits(msgs.get((f, line), [])) if p != own and p not in have]
    if found:
        for p, n in found:
            new.setdefault(p, f"{f}:{line} via {n}")
        continue
    if f in explained:   # follow-on error of a definition already blamed in this file
        continue
    # 2) error inside a merged part: blame that part
    if own:
        if own not in have:
            new.setdefault(own, f"{f}:{line}")
        continue
    # 3) unmerged file, no merged definition involved: not a merge problem
    foreign.append(f"{f}:{line} ({'merged-file header' if len(members) > 1 else 'not a merged file: ' + members[0]})")

if new:
    with a.isolate.open("a") as fh:
        for m, where in new.items():
            fh.write(f"{m}  # {where}\n")
    print(f"isolated {len(new)} module(s):", *new, sep="\n  ")
for x in foreign:
    print("  ! not fixable by un-merging:", x)
sys.exit(2 if foreign and not new else 0 if new else 1)
