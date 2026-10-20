"""Extensions (MO 515996): (1) constructions survive every deletion; (2) j = k-2 examples of length 2k+8."""
from __future__ import annotations
import itertools, math
from neck import periodic, pair_construction
from odd import odd_construction

def all_deletions_symmetric(w: str) -> bool:
    cols = sorted(set(w))
    for r in range(1, len(cols)):
        for J in itertools.combinations(cols, r):
            u = "".join(ch for ch in w if ch not in J)
            if not periodic(u): return False
    return True

def j_precarious(w: str, j: int) -> bool:
    cols = sorted(set(w))
    if periodic(w): return False
    return all(periodic("".join(ch for ch in w if ch not in J)) for J in itertools.combinations(cols, j))

# (1)
for m in (1, 2, 3):
    print(f"even k={2*m}: every deletion symmetric:", all_deletions_symmetric(pair_construction(m)))
for m in (1, 2):
    print(f"odd  k={2*m+1}: every deletion symmetric:", all_deletions_symmetric(odd_construction(m)))
# (2) insert D's (and further 2-bead colours next to them) into the k=3 word
W = "AABBACABBAABCB"
def ext(k: int) -> str:
    extra = "DEFGH"[: k - 3]
    w = W[0] + extra + W[1:8] + extra + W[8:]
    return w
for k in range(3, 8):
    w = ext(k)
    print(f"k={k}: length {len(w)} (2k+8={2*k+8}), every 2-colour projection symmetric & not symmetric:", j_precarious(w, k - 2))
