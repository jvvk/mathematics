"""Precarious necklaces (MO 515996): checker, pair/prime construction, exhaustive a(3)."""
from __future__ import annotations
import itertools, sys

def periodic(w: str) -> bool:
    # cyclic word has a nontrivial rotational symmetry <=> w occurs in (w+w)[1:-1]
    return len(w) > 1 and w in (w + w)[1:-1]

def precarious(w: str) -> bool:
    cols = set(w)
    return len(cols) >= 2 and not periodic(w) and all(periodic(w.replace(c, "")) for c in cols)

PRIMES = [2, 3, 5, 7, 11, 13]

def pair_construction(m: int) -> str:
    """Pairs (A_i, B_i); in block j, pair i is A_iB_i if j % p_i == 0 else B_iA_i. Blocks = prod p_i."""
    ps = PRIMES[:m]
    nb = 1
    for p in ps: nb *= p
    letters = [(chr(65 + 2 * i), chr(66 + 2 * i)) for i in range(m)]
    return "".join("".join(a + b if j % p == 0 else b + a for (a, b), p in zip(letters, ps)) for j in range(nb))

def exhaustive(k: int, L: int) -> list[str]:
    """All precarious words of length L on k colours using every colour, first letter 'A' (rotation)."""
    al = "ABCDEFGH"[:k]
    out = []
    for t in itertools.product(al, repeat=L - 1):
        w = "A" + "".join(t)
        if len(set(w)) == k and precarious(w): out.append(w)
    return out

if __name__ == "__main__":
    ex = {2: "AABB", 3: "ABCCBBCACBBCCB", 4: "ABCDBACDABDCBACDABCDBADC"}
    for k, w in ex.items(): print("OP example k=%d len %d precarious:" % (k, len(w)), precarious(w))
    for m in range(1, 5):
        w = pair_construction(m)
        print(f"construction k={2*m}: length {len(w)} precarious={precarious(w)}")
    # mutation sanity: a periodic word and a word failing one deletion must be rejected
    assert not precarious("ABAB") and not precarious("AABBC")
    if len(sys.argv) > 1:
        k = int(sys.argv[1])
        for L in range(k, int(sys.argv[2]) + 1):
            r = exhaustive(k, L)
            print(f"k={k} L={L}: {len(r)} precarious", r[:2]); sys.stdout.flush()
            if r: break
