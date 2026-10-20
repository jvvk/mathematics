"""Exact test of the PROOF.md recipe (Steps 2-6) for q/816017.

For each case, build the Laurent matrix F(z) = sum_j z^{n_j} N_j of a product trajectory with orthogonal
frequency components (degenerate and resonant spectra, one and two frequency generators). Then, from F alone:
factor F = alpha beta^T with alpha primitive, check A(z,w) has no z-dependence, read off the orthogonal
components x_mu, and confirm the local generators reproduce F. A mutation (non-orthogonal components, i.e.
non-unitary dynamics) must break Step 4/5, showing orthogonality is load-bearing.
"""

from __future__ import annotations

import random
from functools import reduce

import sympy as sp

random.seed(816017)
Z = sp.symbols("z1 z2")
W = sp.symbols("w1 w2")
I = sp.I


def gauss_rational() -> sp.Expr:
    return sp.Rational(random.randint(-4, 4)) + I * sp.Rational(random.randint(-4, 4))


def orthogonal_set(dim: int, count: int) -> list[sp.Matrix]:
    """Exact pairwise-orthogonal nonzero vectors (Gram-Schmidt without normalising)."""
    out: list[sp.Matrix] = []
    while len(out) < count:
        v = sp.Matrix([gauss_rational() for _ in range(dim)])
        for u in out:
            v = v - (u.H * v)[0] / (u.H * u)[0] * u
        v = sp.simplify(v)
        if any(c != 0 for c in v):
            out.append(v)
    return out


def curve(vectors: list[sp.Matrix], exps: list[tuple[int, int]], k: int) -> sp.Matrix:
    terms = [
        v * sp.Mul(*[Z[i] ** e[i] for i in range(k)]) for v, e in zip(vectors, exps)
    ]
    return reduce(lambda a, b: a + b, terms)


def star(p: sp.Expr, k: int) -> sp.Expr:
    """p*(z): conjugate coefficients, z -> 1/z (equals conj(p) on the torus)."""
    p = sp.expand(p)
    return sp.expand(
        sp.conjugate(p).subs({sp.conjugate(Z[i]): 1 / Z[i] for i in range(k)})
    )


def primitive_factor(F: sp.Matrix, k: int) -> tuple[sp.Matrix, sp.Matrix]:
    """Step 2: F = alpha beta^T with alpha primitive in the Laurent ring."""
    gens = Z[:k]
    col = next(j for j in range(F.shape[1]) if any(sp.expand(e) != 0 for e in F[:, j]))
    entries = [sp.together(sp.expand(e)) for e in F[:, col]]
    nums = [sp.numer(e) for e in entries if e != 0]
    g = reduce(lambda a, b: sp.gcd(a, b, *gens), nums)
    alpha = sp.Matrix([sp.cancel(e / g) for e in entries])
    beta = sp.Matrix(
        [
            sp.cancel(F[0, j] / alpha[0]) if alpha[0] != 0 else None
            for j in range(F.shape[1])
        ]
    )
    if alpha[0] == 0:
        r = next(i for i in range(len(alpha)) if alpha[i] != 0)
        beta = sp.Matrix([sp.cancel(F[r, j] / alpha[r]) for j in range(F.shape[1])])
    for j in range(F.shape[1]):  # beta must be Laurent: denominators are monomials only
        d = sp.Poly(sp.denom(sp.together(beta[j])), *gens)
        assert len(d.terms()) == 1, f"beta entry not Laurent: {beta[j]}"
    assert sp.simplify(alpha * beta.T - F) == sp.zeros(*F.shape), "F != alpha beta^T"
    return alpha, beta


def overlap(alpha: sp.Matrix, k: int) -> sp.Expr:
    """A(z,w) = sum_i alpha_i*(z) alpha_i(zw)."""
    sub = {Z[i]: Z[i] * W[i] for i in range(k)}
    return sp.expand(
        sum(star(a, k) * sp.expand(a.subs(sub, simultaneous=True)) for a in alpha)
    )


def components(alpha: sp.Matrix, k: int) -> dict[tuple[int, ...], sp.Matrix]:
    """x_mu: coefficient vectors of alpha by Laurent exponent mu."""
    shift = 50  # clear negative exponents
    mono = sp.Mul(*[Z[i] ** shift for i in range(k)])
    comp: dict[tuple[int, ...], list] = {}
    for idx, a in enumerate(alpha):
        p = sp.Poly(sp.expand(sp.cancel(a * mono)), *Z[:k])
        for exps, c in p.terms():
            mu = tuple(e - shift for e in exps)
            comp.setdefault(mu, [0] * len(alpha))[idx] = c
    return {mu: sp.Matrix(v) for mu, v in comp.items()}


def check_recipe(F: sp.Matrix, k: int) -> str:
    alpha, beta = primitive_factor(F, k)
    for name, vec in (("A", alpha), ("B", beta)):
        A = overlap(vec, k)
        if any(sp.diff(A, Z[i]) != 0 for i in range(k)):
            return f"FAIL: {name}(z,w) depends on z"
        xs = components(vec, k)
        mus = list(xs)
        for a in range(len(mus)):
            for b in range(a + 1, len(mus)):
                if sp.simplify((xs[mus[a]].H * xs[mus[b]])[0]) != 0:
                    return f"FAIL: x_mu not orthogonal in {name}"
    return "PASS"


def build_case(m: int, n: int, exps_a: list, exps_b: list, k: int) -> sp.Matrix:
    xa = orthogonal_set(m, len(exps_a))
    xb = orthogonal_set(n, len(exps_b))
    return sp.expand(curve(xa, exps_a, k) * curve(xb, exps_b, k).T)


def frobenius_orthogonal(F: sp.Matrix, k: int) -> bool:
    """Grouped components N_j of F (by exponent) pairwise Frobenius-orthogonal: the unitarity hypothesis."""
    shift = 50
    mono = sp.Mul(*[Z[i] ** shift for i in range(k)])
    comps: dict[tuple, sp.Matrix] = {}
    for r in range(F.shape[0]):
        for c in range(F.shape[1]):
            p = sp.Poly(sp.expand(F[r, c] * mono), *Z[:k])
            for exps, coef in p.terms():
                comps.setdefault(exps, sp.zeros(*F.shape))[r, c] = coef
    keys = list(comps)
    return all(
        sp.simplify(
            sum(
                (sp.conjugate(comps[keys[a]][i]) * comps[keys[b]][i])
                for i in range(F.shape[0] * F.shape[1])
            )
        )
        == 0
        for a in range(len(keys))
        for b in range(a + 1, len(keys))
    )


CASES = [
    # (label, m, n, alpha exponents, beta exponents, k)
    (
        "2x2 resonant 0,1 x 0,1 (lambda=1 degenerate)",
        2,
        2,
        [(0,), (1,)],
        [(0,), (1,)],
        1,
    ),
    (
        "3x3 equally spaced 0,1,2 x 0,1,2 (heavy resonance)",
        3,
        3,
        [(0,), (1,), (2,)],
        [(0,), (1,), (2,)],
        1,
    ),
    ("3x2 gaps 0,1,3 x -1,2", 3, 2, [(0,), (1,), (3,)], [(-1,), (2,)], 1),
    (
        "2x3 two generators (1, sqrt2)",
        2,
        3,
        [(0, 0), (1, 1)],
        [(0, 0), (1, 0), (0, 1)],
        2,
    ),
    (
        "3x3 two generators, resonant",
        3,
        3,
        [(0, 0), (1, 0), (0, 1)],
        [(0, 0), (1, 0), (0, 1)],
        2,
    ),
]


def main() -> None:
    for label, m, n, ea, eb, k in CASES:
        F = build_case(m, n, ea, eb, k)
        assert frobenius_orthogonal(F, k), (
            "construction should satisfy unitarity hypothesis"
        )
        print(f"{check_recipe(F, k):4}  {label}")
    # Mutation: non-orthogonal components (dynamics not unitary). Hypothesis fails, and the recipe must detect it.
    u, v = sp.Matrix([1, 1]), sp.Matrix([1, 0])  # <u,v> != 0
    p, q = sp.Matrix([1, I]), sp.Matrix([2, 1])
    Fm = sp.expand((u + Z[0] * v) * (p + Z[0] * q).T)
    print(
        f"mutation non-orthogonal: hypothesis holds = {frobenius_orthogonal(Fm, 1)}, recipe = {check_recipe(Fm, 1)}"
    )


if __name__ == "__main__":
    main()
