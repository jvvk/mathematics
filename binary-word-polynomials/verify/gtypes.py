"""Kinds of block-reversal edge in the census. For each edge (u, v) not explained by complement-reversal:
  I  interleaving: u = W a1 W ... ar W and v (or its reversal) = W ar ... a1 W (the existing MO answer);
  R  some accepted move has a G with equal diagonal entries (Theorem R; the extra row al - ga = 0);
  N  neither: every accepted move needs a G outside both shapes.
Usage: python3 gtypes.py nmin nmax -> counts per n and examples of N."""
import sys
import classify as C
from exact import classes

def interleave(u, v):
    n = len(u)
    for k in range(1, n):
        if (n - k) % (k + 1): continue
        r = (n - k) // (k + 1); W = u[:k]
        if r < 2 or any(u[i * (k + 1):i * (k + 1) + k] != W for i in range(r + 1)): continue
        seps = [u[i * (k + 1) + k] for i in range(r)]
        w2 = W + "".join(s + W for s in seps[::-1])
        if v in (w2, w2[::-1]): return True
    return False

EQ = (1, 0, C.PR - 1)


def kinds(n: int, eq=EQ):
    """Counts of edge kinds I, R, N (and pairs with no move) for length n, with examples of N."""
    cnt = {"I": 0, "R": 0, "N": 0, "none": 0}; ex = []
    for g in classes(n):
        for i in range(len(g)):
            for j in range(i + 1, len(g)):
                u, v = g[i], g[j]
                if v in (C.comp(u), C.comp(u)[::-1]): continue
                if interleave(u, v) or interleave(v, u): cnt["I"] += 1; continue
                any_mv = r_mv = None
                for vv in {v, v[::-1]}:
                    Ms = [(C.mats(u, tt), C.mats(vv, tt)) for tt in C.PTS]
                    for mv in C.moves(u, vv):
                        if all(C.ok_at(Mu, Mv, n, *mv, tt) for (Mu, Mv), tt in zip(Ms, C.PTS)):
                            any_mv = any_mv or (vv, mv)
                            if all(C.ok_at(Mu, Mv, n, *mv, tt, extra=[eq]) for (Mu, Mv), tt in zip(Ms, C.PTS)):
                                r_mv = (vv, mv); break
                    if r_mv: break
                if r_mv: cnt["R"] += 1
                elif any_mv:
                    cnt["N"] += 1
                    vv, (a, b, la, cuts) = any_mv
                    ex.append(f"{u[:a]}|{' '.join(u[a + cuts[k]:a + cuts[k + 1]] for k in range(len(cuts) - 1))}|{u[n - b:]} -> {vv}")
                else: cnt["none"] += 1
    return cnt, ex


if __name__ == "__main__":
    for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        cnt, ex = kinds(n)
        print(n, cnt, ex[:3], flush=True)
