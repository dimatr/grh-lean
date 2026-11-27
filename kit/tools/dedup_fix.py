#!/usr/bin/env python3
"""P4 repair: undo the renames that a failed build points at.

    python3 dedup_fix.py <build.log> <project> [--report kit/dedup/report.json]
                         [--reverted kit/dedup/reverted.txt] [--revert OLD.NAME ...]

Every new name chosen by dedup_rename.py is unique in the project, so undoing a rename is a
whole-identifier text replacement new leaf -> old leaf over src/ (companions like
new.eq_1 follow automatically). Which renames to undo is read from the error messages:
  - a constant/field named in "Unknown constant", "Unknown identifier", "does not contain",
    "Invalid field", "overloaded" messages: renames whose OLD leaf equals that name's leaf
    (also with a generated suffix _iff/_apply/_assoc/_def removed), e.g. `Hall.ext_iff` -> Hall.ext;
    `Exists.refl` (expected type guessed) -> every renamed `…refl`;
  - any NEW leaf that appears in such a message, e.g. `S.filling_IsNear γ` -> undo filling_IsNear.
Over-undoing is harmless (one duplicate name more); under-undoing costs another round.
Exit 0: undid something. Exit 1: nothing new to undo (send the errors to Claude).
"""
import argparse, json, pathlib, re, sys

ap = argparse.ArgumentParser()
ap.add_argument("log", type=pathlib.Path)
ap.add_argument("project", type=pathlib.Path)
here = pathlib.Path(__file__).resolve().parent.parent
ap.add_argument("--report", type=pathlib.Path, default=here / "dedup" / "report.json")
ap.add_argument("--reverted", type=pathlib.Path, default=here / "dedup" / "reverted.txt")
ap.add_argument("--revert", nargs="*", default=[], help="old full names to undo explicitly")
a = ap.parse_args()

renames = json.loads(a.report.read_text())["renames"]          # old full -> new full
done = set()
if a.reverted.exists():
    done = {l.split("#")[0].strip() for l in a.reverted.read_text().splitlines()} - {""}
live = {o: n for o, n in renames.items() if o not in done}
leaf = lambda s: s.split(".")[-1]
by_old_leaf = {}
for o in live:
    by_old_leaf.setdefault(leaf(o), []).append(o)
IDC = r"[\w'!?]"

# ---- error messages ----------------------------------------------------------------------------
HEAD = re.compile(r"error:?\s*(?:\./)*([^:\s]+\.lean):(\d+):(\d+):(.*)$")
msgs, cur = [], None
for l in a.log.read_text(errors="replace").splitlines():
    m = HEAD.search(l)
    if m:
        cur = [m.group(4)]; msgs.append((m.group(1), int(m.group(2)), cur)); continue
    if cur is not None and re.match(r"^\s*(error|warning|info|✖|⚠|✔|ℹ|Build|Some required)", l):
        cur = None
    elif cur is not None:
        cur.append(l)
RELEVANT = re.compile(r"Unknown constant|Unknown identifier|does not contain|Invalid field|overloaded")

pick = {}
for f, line, body in msgs:
    text = "\n".join(body)
    if not RELEVANT.search(text):
        continue
    names = set(re.findall(r"`([^`\s]+)`", text)) | set(re.findall(r"Unknown constant `?([\w.'!?]+)", text))
    for t in names:
        lf = leaf(t)
        for cand in {lf, re.sub(r"_(iff|apply|assoc|def|symm_apply)$", "", lf)}:
            for o in by_old_leaf.get(cand, []):
                pick.setdefault(o, f"{f}:{line} `{t}`")
    for o, n in live.items():
        if re.search(rf"(?<!{IDC}){re.escape(leaf(n))}(?!{IDC})", text):
            pick.setdefault(o, f"{f}:{line} new name `{leaf(n)}` in message")
for o in a.revert:
    if o in live:
        pick.setdefault(o, "explicit")

if not pick:
    print("nothing to undo from these errors"); sys.exit(1)

# ---- undo: whole-identifier replacement new leaf -> old leaf ----------------------------------
m = re.search(r'^srcDir\s*=\s*"([^"]+)"', (a.project / "lakefile.toml").read_text(), re.M) \
    if (a.project / "lakefile.toml").exists() else None
src = a.project / (m.group(1) if m else ".")
pats = [(re.compile(rf"(?<!{IDC}){re.escape(leaf(live[o]))}(?!{IDC})"), leaf(o)) for o in pick]
changed = 0
for p in src.rglob("*.lean"):
    if ".lake" in p.relative_to(a.project).parts:
        continue
    t = p.read_text(); u = t
    for rx, old in pats:
        u = rx.sub(old, u)
    if u != t:
        p.write_text(u); changed += 1
a.reverted.parent.mkdir(parents=True, exist_ok=True)
with a.reverted.open("a") as fh:
    for o, why in pick.items():
        fh.write(f"{o}  # {live[o]} ; {why}\n")
print(f"undid {len(pick)} rename(s) in {changed} files:")
for o, why in pick.items():
    print(f"  {live[o]} -> {o}   ({why})")
