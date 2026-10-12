"""The semicircles z(u) = 1 - r e^{iu}, 0 <= u <= pi, through the trivial zero 1 - r of zeta (r odd).

For r = 3 and r = 5, |zeta(z(u))| is strictly increasing on [0, pi] (certified as in prove.py, with the radius as a
parameter). For r = 7, 9, ..., 41 it is not: R(u) = d/du log|zeta(z(u))| is certified negative on a small interval.

All bounds use Arb ball arithmetic (python-flint). Run: python semicircles.py. MUTANT=1 claims monotonicity for r = 7
(the certificate must fail); MUTANT=2 looks for a decrease for r = 3 (none can be certified).
"""

from __future__ import annotations

import os
import sys

from flint import acb, acb_series, arb, ctx

ctx.prec = 64
PI = arb.pi()
MUTANT = os.environ.get("MUTANT", "0")


def interval(a: arb, b: arb) -> arb:
    return arb((a + b) / 2, ((b - a) / 2).upper())


def hull(z1: acb, z2: acb) -> acb:
    re = interval(
        min(z1.real.lower(), z2.real.lower()), max(z1.real.upper(), z2.real.upper())
    )
    im = interval(
        min(z1.imag.lower(), z2.imag.lower()), max(z1.imag.upper(), z2.imag.upper())
    )
    return acb(re, im)


def coeffs(z: acb, n: int = 3) -> list[acb]:
    s = acb_series([z, 1], prec=n).zeta()
    return [s[k] for k in range(n)]


def path(r: int, u: arb) -> tuple[acb, acb, acb]:
    e = acb(0, u).exp()
    return 1 - r * e, -r * acb(0, 1) * e, r * e


def R_enc(r: int, u: arb) -> arb:
    z, zp, _ = path(r, u)
    c = coeffs(z, 2)
    return (zp * c[1] / c[0]).real


def Rp_enc(r: int, u: arb) -> arb:
    z, zp, zpp = path(r, u)
    c = coeffs(z, 3)
    L = c[1] / c[0]
    return (zpp * L + zp * zp * (2 * c[2] / c[0] - L * L)).real


def region_a(r: int, d1: arb) -> bool:
    """zeta(z) = (z - z0) h(z), z0 = 1 - r; R = (1/2) cot(u/2) + Re(z' h'/h) and |z'| = r."""
    z, _, _ = path(r, interval(arb(0), d1))
    box = hull(z, acb(1 - r))
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
    if h.abs_lower() <= 0:
        return False
    return bool(
        (d1 / 2).cos() / (2 * (d1 / 2).sin()) > r * hp.abs_upper() / h.abs_lower()
    )


def cover(a: arb, b: arb, test, depth: int = 0) -> int:
    if depth > 40:
        raise RuntimeError(f"cannot certify near u = {a}")
    if test(interval(a, b)):
        return 1
    m = (a + b) / 2
    return cover(a, m, test, depth + 1) + cover(m, b, test, depth + 1)


def monotone(r: int, d1: str = "0.05", d2: str = "0.3") -> str:
    a, b = arb(d1), arb(d2)
    if not region_a(r, a):
        raise RuntimeError("region A")
    nb = cover(a, PI - b, lambda u: R_enc(r, u) > 0)
    nc = cover(PI - b, PI, lambda u: Rp_enc(r, u) < 0)
    return f"increasing: region A ok, {nb} boxes with R > 0, {nc} boxes with R' < 0 up to R(pi) = 0"


def decrease(r: int) -> str | None:
    """Find a u-interval of width pi/4000 on which R < 0 is certified."""
    N = 4000
    for k in range(1, N):
        u = interval(PI * k / N, PI * (k + 1) / N)
        if R_enc(r, u) < 0:
            return f"decreasing on [{k}pi/{N}, {k + 1}pi/{N}] (R < 0 certified)"
    return None


def main() -> None:
    ok = True
    for r in (3, 5):
        try:
            msg = monotone(r) if MUTANT != "2" or r != 3 else None
            if MUTANT == "2" and r == 3:
                d = decrease(3)
                ok &= d is not None
                msg = d or "no decrease found"
        except RuntimeError as e:
            msg, ok = f"NOT certified ({e})", False
        print(f"r = {r}: {msg}")
    for r in range(7, 43, 2):
        if MUTANT == "1" and r == 7:
            try:
                print(f"r = 7: {monotone(7)}")
            except RuntimeError as e:
                print(f"r = 7: NOT certified ({e})")
                ok = False
            continue
        d = decrease(r)
        print(f"r = {r}: {d or 'NO DECREASE FOUND'}")
        ok &= d is not None
    print("PROVED" if ok else "NOT PROVED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
