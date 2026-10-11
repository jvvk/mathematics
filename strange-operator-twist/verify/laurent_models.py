"""Exact elementary checks for linear Laurent models of Bogner's period.

All computations are in the isolated Astra research directory.
"""
import itertools
from collections import defaultdict
from fractions import Fraction as Q
import sympy as s


def multiply(f, g):
    ans = defaultdict(Q)
    for u, a in f.items():
        for v, b in g.items():
            ans[tuple(x + y for x, y in zip(u, v))] += a * b
    return {u: a for u, a in ans.items() if a}


def g_coefficients():
    # G = h(z) * (4(1+uv+u/v)h(y) + (y^-1-y)/(2u)).
    coeffs = defaultdict(Q)
    for uv in [(0, 0), (1, 1), (1, -1)]:
        for y, cy in [(-1, 1), (0, 2), (1, 1)]:
            for z, cz in [(-1, 1), (0, 2), (1, 1)]:
                coeffs[(*uv, y, z)] += 4 * cy * cz
    for y, cy in [(-1, Q(1, 2)), (1, Q(-1, 2))]:
        for z, cz in [(-1, 1), (0, 2), (1, 1)]:
            coeffs[(-1, 0, y, z)] += cy * cz
    return dict(coeffs)


def period_check(N=6):
    g = g_coefficients()
    gn = {(0, 0, 0, 0): Q(1)}
    result = []
    from math import factorial as fac, comb
    for n in range(N + 1):
        expected = comb(2*n, n) * sum(
            Q((-1)**m * 4**(n-3*m) * fac(2*n-2*m),
              fac(m)**3 * fac(n-m) * fac(n-4*m))
            for m in range(n//4+1))
        observed = gn.get((0, 0, 0, 0), 0)
        assert observed == expected, (n, observed, expected)
        result.append(observed)
        if n < N:
            gn = multiply(gn, g)
    return result


def exact_identity():
    a, b, y, u, v, z, t = s.symbols("a b y u v z t")
    hz = z + 2 + 1/z
    # CT_y 1/(1-t*(c + a*y+b/y)) is
    # ((1-t*c)^2 - 4*t^2*a*b)^(-1/2).
    c = 8*(1+a+b)*hz
    a1 = hz
    b1 = hz*(16*(1+a+b)**2-1/(4*a*b))
    discriminant = (1-t*c)**2-4*t*t*a1*b1
    assert s.simplify(discriminant-(1-16*t*hz*(1+a+b)+t*t*hz*hz/(a*b))) == 0
    S = 1+u*v+u/v
    c = 8*S*hz
    a1 = hz*(4*S-1/(2*u))
    b1 = hz*(4*S+1/(2*u))
    assert s.simplify((1-t*c)**2-4*t*t*a1*b1-(1-16*t*hz*S+t*t*hz*hz/u**2)) == 0
    return True


def polytope_check():
    # Delta = T x [-1,1]^2, T=conv{(-1,0),(1,-1),(1,1)}.
    # Exact primitive facet equations ell(x)<=1.
    normals = [(1,0,0,0),(-1,2,0,0),(-1,-2,0,0),
               (0,0,1,0),(0,0,-1,0),(0,0,0,1),(0,0,0,-1)]
    vertices = [(*v, y, z) for v in [(-1,0),(1,-1),(1,1)]
                for y in [-1,1] for z in [-1,1]]
    support = g_coefficients()
    for vertex in vertices:
        assert vertex in support
    for v in support:
        assert all(sum(a*b for a,b in zip(v,n)) <= 1 for n in normals)
    lattice = [v for v in itertools.product(range(-1,2), repeat=4)
               if all(sum(a*b for a,b in zip(v,n)) <= 1 for n in normals)]
    interior = [v for v in lattice
                if all(sum(a*b for a,b in zip(v,n)) < 1 for n in normals)]
    assert interior == [(0,0,0,0)]
    return {"vertices": vertices, "facet_normals": normals,
            "lattice_points":len(lattice), "interior_points":interior}


if __name__ == "__main__":
    print("Discriminant identities:", exact_identity())
    print("Periods:", period_check())
    print("Reflexive polytope:", polytope_check())
