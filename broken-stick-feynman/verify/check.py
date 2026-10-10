"""Every number stated in the note, asserted at fast settings (about two minutes on one core).

  triangle   : the hinge coordinates give the triangle probability 1/4                 (marked.py control)
  hinge      : p_3 by the hinge quadrature, inner 24 / outer 16, = 0.0125749944167 within 1e-12
  sectors    : p_3 by sector decomposition of the simplex form, order 32, within 2e-12
  identity   : Theorem 1 by Monte Carlo on both sides for n = 2, 3, 4                  (general_n.py)
  qmc        : the C program: marked mode = p_3, unordered = 0.0652818, no-merge mutant = 30 p_3
  montecarlo : plain Monte Carlo of the Cayley-Menger condition agrees with p_3 and excludes 1/79

Usage: python3 check.py [name ...]
"""
from __future__ import annotations

import math
import pathlib
import re
import subprocess
import sys

import numpy as np

import feynman_hp
import general_n
import marked

HERE = pathlib.Path(__file__).resolve().parent
P3 = 0.0125749944167
PU = 0.0652818


def triangle() -> None:
    v = marked.triangle_control(16)
    assert abs(v - 0.25) < 1e-10, v
    print(f"triangle: {v:.14f}")


def hinge() -> None:
    v = marked.p_marked_cyl(24, 16)
    assert abs(v - P3) < 1e-12, v
    print(f"hinge: p_3 = {v:.15f}")


def sectors() -> None:
    v = 8 * 6 * feynman_hp.sector(0, 32) / math.pi
    assert abs(v - P3) < 2e-12, v
    print(f"sectors: p_3 = {v:.15f}")


def identity() -> None:
    rng = np.random.default_rng(142983)
    assert abs(general_n.C(2) - 1 / math.sqrt(math.pi)) < 1e-15 and abs(general_n.C(3) - 4 / math.pi) < 1e-15
    for n in (2, 3, 4):
        a, sa = general_n.direct(n, 2 * 10**6, rng)
        b, sb = general_n.parametric(n, 2 * 10**6, rng)
        z = abs(a - b) / math.hypot(sa, sb)
        assert z < 4, (n, a, b, z)
        print(f"identity: n={n}: direct {a:.6g} parametric {b:.6g} ({z:.1f} se)")
    b3, s3 = general_n.parametric(3, 2 * 10**6, rng)
    assert abs(b3 - P3) < 4 * s3, (b3, s3)


def _run(binary: pathlib.Path, *args: str) -> tuple[float, float]:
    out = subprocess.run([str(binary), *args], capture_output=True, text=True, timeout=600, check=True).stdout
    m = re.search(r"^\S+ map=\d+ N=\S+ reps=\d+ mean=([\d.]+) se=([\d.e+-]+)", out, re.M)
    return float(m.group(1)), float(m.group(2))


def qmc(binary: pathlib.Path | None = None) -> None:
    if binary is None:
        binary = HERE / "unmarked"
        subprocess.run(["cc", "-O2", "-o", str(binary), str(HERE / "unmarked.c"), "-lm"], check=True)
    m, sm = _run(binary, "marked", "20", "16", "7")
    assert abs(m - P3) < 4 * sm, (m, sm)
    u, su = _run(binary, "unmarked", "22", "16", "7")
    assert abs(u - PU) < 4 * math.hypot(su, 4e-7), (u, su)
    x, sx = _run(binary, "nomerge", "18", "8", "7")
    assert abs(x - 30 * P3) < 4 * sx, (x, sx)
    print(f"qmc: marked {m:.9f}, unordered {u:.7f} +- {su:.1e}, no merging {x:.5f} = 30 p_3")


def montecarlo() -> None:
    p, se = marked.monte_carlo(2 * 10**8, seed=3)  # se about 7.9e-6; 1/79 - p_3 = 8.3e-5
    assert abs(p - P3) < 4 * se and abs(p - 1 / 79) > 4 * se, (p, se)
    print(f"montecarlo: {p:.6f} +- {se:.6f} (1/79 = {1/79:.6f})")


CHECKS = dict(triangle=triangle, hinge=hinge, sectors=sectors, identity=identity, qmc=qmc, montecarlo=montecarlo)

if __name__ == "__main__":
    for name in sys.argv[1:] or list(CHECKS):
        CHECKS[name]()
    print("ALL CHECKS PASS")
