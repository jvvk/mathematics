"""Parse the two 2048-leaf trees printed in Bordewich et al. (arXiv:2005.07357, Appendix A) and compute
their MAST with the verified sparse DP of mast.py.  Expected: both balanced of height 11, MAST 32."""
import re, sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from mast import mast

t = open(__file__.rsplit("/", 1)[0] + "/refs/blossw_raw.txt").read()   # pdftotext refs/blossw.pdf
body = t[t.index("Example on 2048"):]
body = "\n".join(l for l in body.split("\n") if "(" in l or not (re.fullmatch(r"\s*\d+\s*", l) or "\x0c" in l))
body = body.replace("\x0c", "")

def grab(name: str) -> str:
    s = body[body.index(name + " =") + len(name) + 2:]; out = []; depth = 0
    for ch in s:
        if ch in "()0123456789,":
            out.append(ch)
            if ch == "(": depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0: break
    return "".join(out)

def leaves(nw: str):
    depth = 0; seq = []; depths = set(); num = ""
    for ch in nw:
        if ch.isdigit(): num += ch; continue
        if num: seq.append(int(num)); depths.add(depth); num = ""
        if ch == "(": depth += 1
        elif ch == ")": depth -= 1
    return seq, depths

S, dS = leaves(grab("S")); T, dT = leaves(grab("T"))
assert sorted(S) == sorted(T) == list(range(1, 2049)) and dS == dT == {11}
print("published pair: balanced, height 11, mast =", mast(S, T))
