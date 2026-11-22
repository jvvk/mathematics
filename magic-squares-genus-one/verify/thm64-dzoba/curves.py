"""Independent checks (B)-(E) for dzoba E1 Theorem 6.4.

(B) integral lines of eta = singular points of the dual foliation q = gradF x gradG (l x q(l) = 0).
(C) q is tangent to every member of the pencil F - cG (so F/G is a first integral).
(D) the singular members of the pencil, and the dual curves of their non-line components.
(E) geometric genus of every component of the Kummer cover over each candidate curve.
"""
from __future__ import annotations

import itertools

import sympy as S

e, u, v, s, t, c = S.symbols("e u v s t c")
l0, l1, l2 = S.symbols("l0 l1 l2")
ell = S.Matrix([l0, l1, l2])
F = l1**3 - l0**2 * l1
G = l2**3 - l0**2 * l2
gF = S.Matrix([S.diff(F, z) for z in ell])
gG = S.Matrix([S.diff(G, z) for z in ell])
q = gF.cross(gG)
CELLS = [(a, b) for a in (-1, 0, 1) for b in (-1, 0, 1)]


def foliation_singular_points():
    eqs = list(ell.cross(q))
    pts = set()
    for chart in range(3):
        sub = {ell[chart]: 1}
        sys_ = [S.expand(z.subs(sub)) for z in eqs]
        for prev in range(chart):
            sys_.append(ell[prev])  # earlier coordinates zero
        sys_ = [z.subs({ell[pv]: 0 for pv in range(chart)}) for z in sys_]
        vars_ = [ell[i] for i in range(3) if i > chart]
        sys_ = [z for z in sys_ if z != 0]
        if not vars_:
            if all(S.simplify(z) == 0 for z in sys_):
                pts.add(tuple(1 if i == chart else 0 for i in range(3)))
            continue
        Gb = S.groebner(sys_, *vars_, order="lex")
        if list(Gb) == [1]:
            continue
        assert Gb.is_zero_dimensional, "foliation has a curve of singular points"
        for sol in S.solve(list(Gb), vars_, dict=True):
            pt = [0] * 3
            pt[chart] = 1
            for i in range(chart + 1, 3):
                pt[i] = S.nsimplify(sol[ell[i]])
            pts.add(tuple(pt))
    return sorted(pts, key=str)


def check_tangency():
    H = F - c * G
    gH = S.Matrix([S.diff(H, z) for z in ell])
    # q is orthogonal to gradH, and l is orthogonal to gradH on H = 0 (Euler): q lies in the tangent line.
    assert S.expand(q.dot(gH)) == 0
    assert S.expand(ell.dot(gH) - 3 * H) == 0


def singular_members():
    out = []
    # finite c
    H = F - c * G
    eqs = [S.diff(H, z) for z in ell]
    for chart in range(3):
        sub = {ell[chart]: 1}
        for pv in range(chart):
            sub[ell[pv]] = 0
        sys_ = [S.expand(z.subs(sub)) for z in eqs]
        vars_ = [ell[i] for i in range(chart + 1, 3)] + [c]
        Gb = S.groebner([z for z in sys_ if z != 0], *vars_, order="lex")
        if list(Gb) == [1]:
            continue
        cpoly = [g for g in Gb if g.free_symbols <= {c}]
        out += [S.factor(g) for g in cpoly]
    # c = infinity is G itself: singular iff G has a singular point
    Gb = S.groebner([S.diff(G, z).subs(l0, 1) for z in ell], l1, l2)
    out.append(("c=oo singular", list(Gb) != [1]))
    return out


def dual_conic(Qform):
    """Dual of a smooth conic l^T A l = 0 in the l-plane: x^T adj(A) x = 0 in the x-plane."""
    A = S.hessian(Qform, ell) / 2
    x = S.Matrix([e, u, v])
    return S.factor(S.expand((x.T * A.adjugate() * x)[0]))


# ---------------- genus of Kummer components ----------------

def binary_roots(form):
    """All roots of a binary form in (s,t) with multiplicities, over an algebraic closure (exact)."""
    form = S.expand(form)
    if form == 0:
        return None
    roots = {}
    deg = S.Poly(form, s, t).total_degree()
    # roots at t = 0 (the point s:t = 1:0)
    m_inf = 0
    P = S.Poly(form, s, t)
    while all(mon[1] >= 1 for mon in P.monoms()) and not P.is_zero:
        P = S.Poly(S.expand(P.as_expr() / t), s, t); m_inf += 1
    if m_inf:
        roots["inf"] = m_inf
    aff = S.Poly(P.as_expr().subs(t, 1), s)
    for r, m in S.roots(aff, multiple=False).items():
        roots[S.nsimplify(S.simplify(r))] = roots.get(S.nsimplify(S.simplify(r)), 0) + m
    assert sum(roots.values()) == deg, (form, roots)
    return roots


def kummer_genus(param, skip=None):
    """param: (e,u,v) as binary forms of equal degree in s,t parametrising a curve birationally.
    skip: index of a cell line containing the curve (its root is identically zero there).
    Returns (number of components, genus of each)."""
    forms = []
    for k, (a, b) in enumerate(CELLS):
        if k == skip:
            continue
        f = S.expand(param[0] + a * param[1] + b * param[2])
        assert f != 0, "curve lies in a cell line not declared"
        forms.append(binary_roots(f))
    pts = sorted({r for d in forms for r in d}, key=str)
    # vectors over F2 of f_i / f_0
    rows = []
    for d in forms[1:]:
        rows.append([(d.get(P_, 0) - forms[0].get(P_, 0)) % 2 for P_ in pts])
    M = S.Matrix(rows) if rows else S.zeros(0, len(pts))
    r = gf2_rank([list(rw) for rw in rows])
    B = sum(1 for j in range(len(pts)) if any(rw[j] for rw in rows))
    total = 2 ** (len(forms) - 1)  # 256 for a non-cell curve, 128 inside a cell line
    g = 1 - 2**r + S.Rational(B * 2**r, 4)
    return total // 2**r, g, r, B


def gf2_rank(rows):
    rows = [int("".join(map(str, rw)), 2) for rw in rows if any(rw)]
    rank = 0
    while rows:
        piv = max(rows)
        rows.remove(piv)
        if piv == 0:
            continue
        rank += 1
        top = piv.bit_length() - 1
        rows = [rw ^ piv if (rw >> top) & 1 else rw for rw in rows]
        rows = [rw for rw in rows if rw]
    return rank


def line_param(lv):
    """Parametrise the line lv.(e,u,v) = 0 by two points on it."""
    a0, a1, a2 = lv
    basis = S.Matrix([[a0, a1, a2]]).nullspace()
    P1, P2 = basis
    return tuple(S.expand(s * P1[i] + t * P2[i]) for i in range(3))


def conic_param(conic, point):
    """Rational parametrisation of the conic through a known point (lines through the point)."""
    x0 = S.Matrix(point)
    d = S.Matrix([0, s, t]) if x0[0] != 0 else S.Matrix([s, t, 0])
    lam = S.symbols("lam")
    xx = x0 * lam + d
    expr = S.expand(conic.subs(dict(zip((e, u, v), xx))))
    # expr = lam * (linear in s,t) + quadratic(s,t), since x0 is on the conic
    Pl = S.Poly(expr, lam)
    assert Pl.degree() == 1
    a1, a0 = Pl.all_coeffs()
    # lam = -a0/a1; homogenise
    pt = x0 * (-a0) + d * a1
    return tuple(S.expand(z) for z in pt)


def main():
    pts = foliation_singular_points()
    print("(B) foliation singular points (= eta-integral lines):", len(pts))
    for P_ in pts:
        print("    ", P_, " line:", S.expand(P_[0] * e + P_[1] * u + P_[2] * v))
    # each is integral: Q(x, l0) = x . q(l0) vanishes on the line l0
    check_tangency()
    print("(C) q tangent to every pencil member: OK")
    print("(D) singular members:", singular_members())
    for sign in (1, -1):
        H = S.factor(F - sign * G)
        print(f"    F - ({sign})G =", H)
    results = []
    # cell lines
    for k, (a, b) in enumerate(CELLS):
        n, g, r, B = kummer_genus(line_param((1, a, b)), skip=k)
        results.append((f"cell e+{a}u+{b}v", n, g))
    # non-cell integral lines
    cellset = {(1, a, b) for a, b in CELLS}
    for P_ in pts:
        norm = tuple(S.nsimplify(z / P_[0]) for z in P_) if P_[0] != 0 else P_
        if norm in cellset:
            continue
        n, g, r, B = kummer_genus(line_param(P_))
        results.append((f"line {P_}", n, g))
    # conic components of the reducible members, dualised
    for sign in (1, -1):
        H = S.factor_list(S.expand(F - sign * G))[1]
        for fac, m in H:
            if S.Poly(fac, l0, l1, l2).total_degree() == 2:
                Cx = dual_conic(fac)
                # find a point on the dual conic: intersect with v = 0 (solve for u)
                sol = S.solve(Cx.subs({v: 0, e: 1}), u)
                pt = (1, sol[0], 0)
                par = conic_param(Cx, pt)
                assert S.simplify(Cx.subs(dict(zip((e, u, v), par)))) == 0
                n, g, r, B = kummer_genus(par)
                results.append((f"dual conic {Cx} = 0", n, g))
    print("(E) components over each candidate curve:")
    for name, n, g in results:
        print(f"    {name:45s} components {n:4d}  genus {g}")


if __name__ == "__main__":
    main()
