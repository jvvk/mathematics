"""Exact confirmation of every block-reversal edge found by classify.py: for the first move accepted mod p, solve the
linear conditions on G = [[al, be], [be, ga]] over Q(t) with sympy, and check det G != 0, the two parallel conditions
and lam mu = 1 symbolically. Usage: python3 exactcheck.py nmin nmax  -> per n: edges, confirmed, failures."""
import sys
import sympy as sp
import classify as C
from exact import classes

t = sp.symbols("t"); al, be, ga = sp.symbols("al be ga")
G = sp.Matrix([[al, be], [be, ga]])

def M(w):
    m = sp.eye(2)
    for ch in w: m = m * sp.Matrix([[t - int(ch), -1], [1, 0]])
    return m.applyfunc(sp.expand)

def confirm(u, v, a, b, la, cuts):
    n = len(u); L = n - a - b
    eqs = []
    for i in range(len(cuts) - 1):
        Z = M(u[a + cuts[i]:a + cuts[i + 1]]) * G; eqs.append(Z[0, 1] - Z[1, 0])
    xA, yB = M(u[:a])[0, :].T, M(u[n - b:])[:, 0]
    xA2, yB2 = M(v[:la])[0, :].T, M(v[la + L:])[:, 0]
    par = lambda x, y: (G * x)[0] * y[1] - (G * x)[1] * y[0]
    eqs += [par(xA, yB2), par(xA2, yB)]
    A, _ = sp.linear_eq_to_matrix([sp.expand(e) for e in eqs], [al, be, ga])
    for vec in A.nullspace(simplify=True):
        Gs = G.subs(dict(zip((al, be, ga), vec))).applyfunc(sp.cancel)
        if sp.cancel(Gs.det()) == 0: continue
        Gx, Gx2 = Gs * xA, Gs * xA2
        k = 0 if yB2[0] != 0 else 1; lam = sp.cancel(Gx[k] / yB2[k])
        k = 0 if yB[0] != 0 else 1; mu = sp.cancel(yB[k] / Gx2[k])
        ok = (sp.cancel(Gx - lam * yB2) == sp.zeros(2, 1) and sp.cancel(Gx2 * mu - yB) == sp.zeros(2, 1)
              and sp.cancel(lam * mu - 1) == 0)
        if ok: return True
    return False

def edges(n: int):
    """Return (block edges found, confirmed exactly, failures) for the classes of length n."""
    found_n = conf = 0; bad = []
    for g in classes(n):
        for i in range(len(g)):
            for j in range(i + 1, len(g)):
                u, v = g[i], g[j]
                if v in (C.comp(u), C.comp(u)[::-1]): continue
                found = None
                for vv in {v, v[::-1]}:
                    Ms = [(C.mats(u, tt), C.mats(vv, tt)) for tt in C.PTS]
                    for mv in C.moves(u, vv):
                        if all(C.ok_at(Mu, Mv, n, *mv, tt) for (Mu, Mv), tt in zip(Ms, C.PTS)):
                            found = (vv, mv); break
                    if found: break
                if not found: continue
                found_n += 1
                if confirm(u, found[0], *found[1]): conf += 1
                else: bad.append((u, v, found))
    return found_n, conf, bad


if __name__ == "__main__":
    for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        e, c, bad = edges(n)
        print(n, "block edges", e, "confirmed exactly", c, "failed", bad[:3], flush=True)
