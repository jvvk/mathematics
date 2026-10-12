"""Computer-assisted proof for MSE q/5150160: |zeta(z(u))| is strictly increasing on [0, pi], z(u) = 1 - 5 e^{iu}.

F(u) = log|zeta(z(u))|, R(u) = F'(u) = Re(z'(u) L(z)), L = zeta'/zeta. All bounds use Arb ball arithmetic (python-flint);
an enclosure of an interval of u gives an enclosure of every quantity over that whole interval.

Region A, u in (0, D1]: zeta(z) = (z+4) h(z), h(z) = int_0^1 zeta'(-4 + t(z+4)) dt. For z in a convex box B containing -4,
  h(B) lies in the box zeta'(B) and h'(B) in the box zeta''(B)/2 (averages of values in a convex set).
  R = (1/2) cot(u/2) + Re(z' h'/h), and |z'| = 5, so R > 0 when (1/2) cot(D1/2) > 5 max|h'/h|.
Region B, u in [D1, PI - D2]: adaptive bisection until the enclosure of R is positive.
Region C, u in [PI - D2, PI]: R(pi) = 0 (z = 6, z' = 5i, L(6) real). Show R' < 0 there, so R(u) = -int_u^pi R' > 0.
  R' = Re(z'' L + z'^2 (2 c2/c0 - L^2)), with zeta(z+x) = c0 + c1 x + c2 x^2 + ...

Hence R > 0 on (0, pi), so |zeta(z(u))| is strictly increasing on [0, pi] (zero at u = 0).
Run: python prove.py  (prints PROVED and the number of boxes). Set MUTANT=1 to check a false claim is rejected.
"""

from __future__ import annotations

import os
import sys

from flint import acb, acb_series, arb, ctx

ctx.prec = 64
PI = arb.pi()
MUTANT = os.environ.get("MUTANT") == "1"


def path(u: arb) -> tuple[acb, acb, acb]:
    e = acb(0, u).exp()
    return 1 - 5 * e, -5 * acb(0, 1) * e, 5 * e


def coeffs(z: acb, n: int = 3) -> list[acb]:
    s = acb_series([z, 1], prec=n).zeta()
    return [s[k] for k in range(n)]


def interval(a: arb, b: arb) -> arb:
    return arb((a + b) / 2, ((b - a) / 2).upper())


def hull(z1: acb, z2: acb) -> acb:
    """Box containing both boxes."""
    re = interval(
        min(z1.real.lower(), z2.real.lower()), max(z1.real.upper(), z2.real.upper())
    )
    im = interval(
        min(z1.imag.lower(), z2.imag.lower()), max(z1.imag.upper(), z2.imag.upper())
    )
    return acb(re, im)


def region_a(d1: arb) -> bool:
    z, _, _ = path(interval(arb(0), d1))
    box = hull(z, acb(-4))  # convex box containing -4 and every z(u), u in [0, d1]
    # one wide ball gives crude zeta bounds, so cover the box by n x n sub-boxes and take the hull of their enclosures
    n = 64
    re_lo, re_hi = box.real.lower(), box.real.upper()
    im_lo, im_hi = box.imag.lower(), box.imag.upper()
    h = hp = None
    for i in range(n):
        for j in range(n):
            sub = acb(
                interval(
                    re_lo + (re_hi - re_lo) * i / n,
                    re_lo + (re_hi - re_lo) * (i + 1) / n,
                ),
                interval(
                    im_lo + (im_hi - im_lo) * j / n,
                    im_lo + (im_hi - im_lo) * (j + 1) / n,
                ),
            )
            c = coeffs(sub)
            h = c[1] if h is None else hull(h, c[1])
            hp = c[2] if hp is None else hull(hp, c[2])
    # h, hp now enclose h(B) and h'(B)
    if h.abs_lower() <= 0:
        return False
    ratio = hp.abs_upper() / h.abs_lower()
    lhs = (d1 / 2).cos() / (2 * (d1 / 2).sin())  # (1/2) cot(d1/2), decreasing in u
    return bool(lhs > 5 * ratio)


def R_enclosure(u: arb) -> arb:
    z, zp, _ = path(u)
    c = coeffs(z, 2)
    return (zp * c[1] / c[0]).real


def Rp_enclosure(u: arb) -> arb:
    z, zp, zpp = path(u)
    c = coeffs(z, 3)
    L = c[1] / c[0]
    return (zpp * L + zp * zp * (2 * c[2] / c[0] - L * L)).real


def cover(a: arb, b: arb, test, depth: int = 0) -> int:
    """Number of boxes needed; raises if depth exceeds 40."""
    if depth > 40:
        raise RuntimeError(f"cannot certify near u = {a}")
    if test(interval(a, b)):
        return 1
    m = (a + b) / 2
    return cover(a, m, test, depth + 1) + cover(m, b, test, depth + 1)


def main() -> None:
    d1, d2 = arb("0.05"), arb("0.3")
    assert region_a(d1), "region A failed"
    upper = PI + (
        1 if MUTANT else 0
    )  # mutant: claim monotonicity past pi, where it fails by symmetry
    nb = cover(d1, upper - d2, lambda u: R_enclosure(u) > 0)
    nc = cover(upper - d2, upper, lambda u: Rp_enclosure(u) < 0)
    z_end, zp_end, _ = path(upper)
    c = coeffs(z_end, 2)
    print(
        f"region A ok; region B {nb} boxes; region C {nc} boxes; R(pi) encloses {(zp_end * c[1] / c[0]).real}"
    )
    print("PROVED")


if __name__ == "__main__":
    try:
        main()
    except (AssertionError, RuntimeError) as e:
        print("NOT PROVED:", e)
        sys.exit(1)
