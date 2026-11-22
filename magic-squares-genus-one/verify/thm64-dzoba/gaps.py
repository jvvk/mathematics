"""Close the remaining steps.

(D') the c = infinity member: G factors into three concurrent lines (my chart check only looked at l0 = 1).
(D'') every chart of the singular-member elimination yields a nonzero polynomial in c (or no singular point).
(W) the web degenerates (Q(x, l) = 0 for every line l through x) only at finitely many points: the 8 triple points.
"""
import sympy as S

from curves import F, G, c, ell, l0, l1, l2, q

e, u, v, m0, m1, m2 = S.symbols("e u v m0 m1 m2")


def main():
    print("(D') G =", S.factor(G))
    H = F - c * G
    eqs = [S.diff(H, z) for z in ell]
    for chart in range(3):
        sub = {ell[chart]: 1, **{ell[pv]: 0 for pv in range(chart)}}
        sys_ = [z for z in (S.expand(z.subs(sub)) for z in eqs) if z != 0]
        vars_ = [ell[i] for i in range(chart + 1, 3)] + [c]
        Gb = S.groebner(sys_, *vars_, order="lex")
        cp = [S.factor(g) for g in Gb if g.free_symbols <= {c}]
        print(f"(D'') chart {chart}: ", "no singular points" if list(Gb) == [1] else f"c-polys {cp}")
        assert list(Gb) == [1] or cp
    x = S.Matrix([e, u, v]); m = S.Matrix([m0, m1, m2])
    Qxm = S.expand(x.dot(q.subs(dict(zip(ell, x.cross(m))))))
    coeffs = S.Poly(Qxm, m0, m1, m2).coeffs()
    pts = []
    for chart, sub in enumerate(({e: 1}, {e: 0, u: 1}, {e: 0, u: 0, v: 1})):
        cs = [z for z in (S.expand(cc.subs(sub)) for cc in coeffs) if z != 0]
        vars_ = [z for z in (u, v) if z not in sub]
        if not vars_:
            if not cs:
                pts.append(tuple(sub.get(z, 0) for z in (e, u, v)))
            continue
        Gb = S.groebner(cs, *vars_, order="lex")
        if list(Gb) == [1]:
            continue
        assert Gb.is_zero_dimensional
        for sol in S.solve(list(Gb), vars_, dict=True):
            pts.append(tuple(sub.get(z, sol.get(z)) for z in (e, u, v)))
    print("(W) web-degeneracy points:", len(pts), pts)


if __name__ == "__main__":
    main()
