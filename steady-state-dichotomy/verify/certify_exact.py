#!/usr/bin/env python3
"""Certify isolated zeros of a three-species quadratic zero-one system over QQ.

Usage: python3 certify_exact.py record.json [--output certificate.json]
Input: {"net": [[[reactant species], [product species]], ...], "kappa": [...]}
       or {"rows": [[c_1, c_x, c_y, c_z, c_xy, c_xz, c_yz], ...]}.
Species indices are 0, 1, 2. JSON decimals and fraction strings are read exactly.

Requires SymPy. Every decision uses rational arithmetic: Groebner bases, Sturm
root isolation, polynomial gcds, and rational interval evaluation. Numerical
approximations printed to the terminal are for display only. Unsupported shape
position or a nonsquarefree eliminant raises an error, never a root-count claim.
"""
import argparse
import hashlib
import json
from pathlib import Path

import sympy as sp

X, Y, Z, LAM = sp.symbols("x y z lambda")
VARIABLES = (X, Y, Z)
MONOMIALS = (1, X, Y, Z, X * Y, X * Z, Y * Z)
MON_KEYS = ((), (0,), (1,), (2,), (0, 1), (0, 2), (1, 2))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_system(record):
    """Read exact coefficients, checking the advertised reaction/sign class."""
    network_info = None
    if "net" in record:
        net = [(tuple(sorted(a)), tuple(sorted(b))) for a, b in record["net"]]
        rates = [sp.Rational(k) for k in record["kappa"]]
        require(len(net) == len(rates), "Reaction and rate counts differ")
        require(len(set(net)) == len(net), "Duplicate reactions")
        require(any(len(a) == 2 for a, _ in net), "Expected a bimolecular reactant")
        rows = [[sp.S.Zero for _ in MONOMIALS] for _ in VARIABLES]
        for (a, b), k in zip(net, rates):
            require(a in MON_KEYS, "Reactants must be quadratic and zero-one")
            require(len(set(b)) == len(b) and set(b) <= {0, 1, 2}, "Invalid product")
            require(a != b and k > 0, "Reactions must change a complex and have positive rates")
            for i in range(3):
                rows[i][MON_KEYS.index(a)] += (int(i in b) - int(i in a)) * k
        stoichiometry = sp.Matrix([[int(i in b) - int(i in a) for a, b in net]
                                   for i in range(3)])
        require(stoichiometry.rank() == 3, "Network is not full-dimensional")
        network_info = {"reactions": len(net), "rank": 3, "rates": [str(k) for k in rates]}
    else:
        raw = record.get("rows", record.get("C"))
        require(raw is not None and len(raw) == 3 and all(len(r) == 7 for r in raw),
                "Expected three rows with seven coefficients")
        rows = [[sp.Rational(c) for c in r] for r in raw]
    for i, row in enumerate(rows):
        for mon, c in zip(MON_KEYS, row):
            require(c == 0 or ((c < 0) == (i in mon)), "Wrong coefficient sign pattern")
    return [sp.expand(sum(c * m for c, m in zip(row, MONOMIALS))) for row in rows], network_info


def polynomial_interval(poly, lo, hi):
    """Horner enclosure over a closed rational interval, without rounding."""
    low = high = sp.S.Zero
    for coefficient in poly.all_coeffs():
        products = (low * lo, low * hi, high * lo, high * hi)
        low, high = min(products) + coefficient, max(products) + coefficient
    return low, high


def signs_at_root(expressions, eliminant, lo, hi):
    """Signs of polynomials at one isolated real root, with exact enclosures.

    Modulo reduction preserves values at that root. A gcd detects exact zeros;
    interval refinement resolves every remaining sign or explicitly fails.
    """
    reduced = {name: sp.Poly(expr, Z, domain=sp.QQ).rem(eliminant)
               for name, expr in expressions.items()}
    zero = set()
    for name, poly in reduced.items():
        common = sp.gcd(poly, eliminant)
        if common.degree() > 0:
            root_in_common = common.eval(lo) == 0 if lo == hi else common.count_roots(lo, hi) == 1
            if root_in_common:
                zero.add(name)
    for _ in range(100):
        enclosures = {name: (sp.S.Zero, sp.S.Zero) if name in zero
                      else polynomial_interval(poly, lo, hi)
                      for name, poly in reduced.items()}
        if all(name in zero or low > 0 or high < 0 for name, (low, high) in enclosures.items()):
            signs = {name: 0 if name in zero else (1 if low > 0 else -1)
                     for name, (low, high) in enclosures.items()}
            return lo, hi, signs, enclosures
        require(lo < hi, "Could not resolve a sign at a rational root")
        lo, hi = eliminant.refine_root(lo, hi, eps=(hi - lo) / 16)
    raise ValueError("Interval refinement did not resolve all signs")


def certify(equations):
    basis = sp.groebner(equations, *VARIABLES, order="lex", domain=sp.QQ)
    require(len(basis.polys) == 3, "Expected a three-element shape basis")
    univariate = [p.as_expr() for p in basis.polys if p.as_expr().free_symbols == {Z}]
    require(len(univariate) == 1, "Expected exactly one univariate eliminant in z")
    eliminant = sp.Poly(univariate[0], Z, domain=sp.QQ).monic()
    require(eliminant.degree() > 0 and sp.gcd(eliminant, eliminant.diff()).degree() == 0,
            "Eliminant must have positive degree and be squarefree")
    coordinates = {}
    for variable in (X, Y):
        candidates = [p.as_expr() for p in basis.polys
                      if p.as_expr().free_symbols <= {variable, Z}
                      and sp.diff(p.as_expr(), variable) == 1]
        require(len(candidates) == 1, "Expected x-p(z), y-q(z) shape position")
        coordinates[variable] = sp.expand(variable - candidates[0])
    require(all(sp.Poly(f.subs(coordinates), Z, domain=sp.QQ).rem(eliminant).is_zero
                for f in equations), "Back-substitution identity failed")
    jacobian = sp.Matrix(equations).jacobian(VARIABLES)
    _, b1, b2, b3 = jacobian.charpoly(LAM).all_coeffs()
    expressions = {"x": coordinates[X], "y": coordinates[Y], "z": Z,
                   "detJ": -b3, "b1": b1, "b2": b2, "b3": b3, "H2": b1 * b2 - b3}
    expressions = {name: sp.expand(expr.subs(coordinates)) for name, expr in expressions.items()}
    roots = []
    for (lo, hi), multiplicity in eliminant.intervals(eps=sp.Rational(1, 10**30)):
        require(multiplicity == 1, "Unexpected multiple root")
        lo, hi, signs, bounds = signs_at_root(expressions, eliminant, lo, hi)
        positive = all(signs[c] > 0 for c in ("x", "y", "z"))
        if positive:
            require(signs["detJ"] != 0, "Degenerate positive steady state")
        if not positive:
            stability = "not a positive steady state"
        elif all(signs[c] > 0 for c in ("b1", "b2", "b3", "H2")):
            stability = "asymptotically stable (strict Routh-Hurwitz)"
        elif signs["detJ"] > 0:
            stability = "unstable (positive real eigenvalue)"
        elif any(signs[c] < 0 for c in ("b1", "b2", "b3", "H2")):
            stability = "unstable (strict Routh-Hurwitz failure)"
        else:
            stability = "not Hurwitz; boundary stability not classified"
        roots.append({"z_interval": [str(lo), str(hi)], "positive": positive,
                      "signs": signs, "bounds": {name: [str(a), str(b)] for name, (a, b) in bounds.items()},
                      "stability": stability})
    return {"equations": [str(f) for f in equations], "groebner_basis": [str(p.as_expr()) for p in basis.polys],
            "eliminant": str(eliminant.as_expr()), "degree": eliminant.degree(), "squarefree": True,
            "coordinates": {str(v): str(expr) for v, expr in coordinates.items()}, "real_roots": roots,
            "positive_states": sum(r["positive"] for r in roots),
            "nondegenerate_positive_states": sum(r["positive"] and r["signs"]["detJ"] != 0 for r in roots),
            "stable_positive_states": sum(r["positive"] and r["stability"].startswith("asymptotically stable") for r in roots)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("record", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    raw = args.record.read_bytes()
    record = json.loads(raw, parse_float=sp.Rational)
    equations, network = read_system(record)
    result = certify(equations)
    result.update({"source_sha256": hashlib.sha256(raw).hexdigest(), "sympy_version": sp.__version__,
                   "network": network, "decision_arithmetic": "exact rational"})
    print(f"Eliminant degree {result['degree']}; real roots {len(result['real_roots'])}; "
          f"positive states {result['positive_states']}; stable {result['stable_positive_states']}")
    for root in result["real_roots"]:
        lo, hi = map(sp.Rational, root["z_interval"])
        midpoint = (lo + hi) / 2
        point = [sp.N(sp.sympify(result["coordinates"][str(v)], locals={"z": Z}).subs(Z, midpoint), 10)
                 for v in (X, Y)] + [sp.N(midpoint, 10)]
        print(f"  display approximation {point}; positive={root['positive']}; "
              f"det sign={root['signs']['detJ']}; {root['stability']}")
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
