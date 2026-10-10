"""Exact reach of a circular arc in Polya's orchard, in 60-digit arithmetic (independent of orchard.py).

The counterclockwise arc of radius a leaving O in direction theta lies on the circle with centre
c = a(-sin theta, cos theta); its point at polar angle psi from c (measured from the direction c -> O) is
reached after turning psi, at distance 2a sin(psi/2) from O. The open disc of radius r at a lattice point q meets
the circle iff |(|q - c|) - a| < r, and then exactly in the angular window phi_q +- delta_q, with
cos delta_q = (a^2 + d^2 - r^2)/(2 a d). The reach is 2a sin(psi*/2) for the first window entry psi* (capped at
pi). Every lattice point with |q| <= reach + r is examined.

    python3 certify.py    -> checks certificates.json (reach >= stated value) and two mutants
"""
import json
import pathlib
import sys

import mpmath as mp

mp.mp.dps = 60
HERE = pathlib.Path(__file__).resolve().parent


def reach(a, theta, r, dmax):
    a, theta, r = mp.mpf(a), mp.mpf(theta), mp.mpf(r)
    cx, cy = -a * mp.sin(theta), a * mp.cos(theta)
    start = mp.atan2(-cy, -cx)                     # direction from c to O
    best = mp.pi
    R = int(mp.ceil(dmax)) + 1
    for i in range(-R, R + 1):
        for j in range(-R, R + 1):
            if (i, j) == (0, 0) or i * i + j * j > (dmax + 1) ** 2:
                continue
            dx, dy = i - cx, j - cy
            d = mp.sqrt(dx * dx + dy * dy)
            if abs(d - a) >= r:
                continue
            phi = (mp.atan2(dy, dx) - start) % (2 * mp.pi)   # counterclockwise turn from O to q's direction
            delta = mp.acos((a * a + d * d - r * r) / (2 * a * d))
            # the window cannot contain the turn 0 (the origin), since |q| >= 1 > r
            assert delta <= phi <= 2 * mp.pi - delta, (i, j)
            best = min(best, phi - delta)
    return 2 * a * mp.sin(best / 2)


def main():
    certs = json.loads((HERE / "certificates.json").read_text())
    ok = True
    for c in certs:
        r = mp.mpf(1) / c["inv_r"]
        got = reach(c["a"], c["theta"], r, c["reach"] + 2)
        good = got >= mp.mpf(c["reach"]) - mp.mpf("1e-9")
        ok &= bool(good)
        print(f"1/r={c['inv_r']:5.0f}  stated {c['reach']:.6f}  exact {mp.nstr(got, 12)}  {'ok' if good else 'FAIL'}")
    # mutants: discs 1% larger, and the arc radius perturbed by 1e-6, must lose reach on most certificates
    lost_r = sum(reach(c["a"], c["theta"], mp.mpf(1.01) / c["inv_r"], c["reach"] + 2) < c["reach"] - 1e-6 for c in certs)
    lost_a = sum(reach(c["a"] * (1 + 1e-6), c["theta"], mp.mpf(1) / c["inv_r"], c["reach"] + 2) < c["reach"] - 1e-6
                 for c in certs)
    print(f"mutants: r + 1% loses reach on {lost_r}/{len(certs)}; a(1 + 1e-6) on {lost_a}/{len(certs)}")
    ok &= lost_r == len(certs) and lost_a >= len(certs) // 2
    print("ALL PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
