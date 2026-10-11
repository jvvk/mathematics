"""Riemann scheme of Bogner's operator P and of its third-order factor L (P = I * L)."""
import sympy as sp

x, s, T = sp.symbols("x s T")
y = sp.Function("y")


def theta_poly_to_ode(polys):
    """polys[k](T): P = sum_k x^k polys[k](theta). Return coefficients p_j(x) of D^j."""
    # theta^m in terms of x^j D^j: theta^m = sum_j S(m,j) x^j D^j (Stirling 2nd kind)
    order = max(sp.degree(p, T) for p in polys)
    coeffs = [sp.Integer(0)] * (order + 1)
    for k, p in enumerate(polys):
        pp = sp.Poly(p, T)
        for (m,), c in pp.terms():
            for j in range(m + 1):
                coeffs[j] += c * x**k * sp.functions.combinatorial.numbers.stirling(m, j) * x**j
    return [sp.expand(c) for c in coeffs]


def exponents(polys, name):
    p = theta_poly_to_ode(polys)
    n = len(p) - 1
    lead = sp.factor(p[n])
    print(f"\n{name}: order {n}, leading coefficient {lead}")
    for x0 in sp.solve(sp.Poly(p[n], x).as_expr() / x**n, x):
        # simple zero of p_n at x0: exponents 0..n-2 and (n-1) - p_{n-1}(x0)/p_n'(x0)
        last = sp.nsimplify(sp.simplify((n - 1) - p[n - 1].subs(x, x0) / sp.diff(p[n], x).subs(x, x0)))
        print(f"  x0 = {sp.nsimplify(x0)}  (|x0| = {sp.N(sp.Abs(x0), 6)}): exponents 0..{n-2} and {last}")
    # infinity: roots of the top theta-polynomial at theta = -alpha, scaled by 1/(number of x-steps)
    top = polys[-1]
    k = len(polys) - 1
    print(f"  infinity (local t = 1/x): exponents {[sp.nsimplify(-r / 1) for r in sp.roots(sp.Poly(top, T)).keys()]} (theta-roots negated; multiplicities from factor {sp.factor(top)})")


P = [T**4, -8 * (2*T + 1)**2 * (5*T**2 + 5*T + 2), 192 * (2*T + 1) * (3*T + 2) * (3*T + 4) * (2*T + 3)]
L = [T**3, -4 * (2*T + 1) * (5*T**2 + 5*T + 2), 48 * (3*T + 2) * (3*T + 4) * (T + 1)]
exponents(P, "P = Bogner operator")
exponents(L, "L = third-order factor")
