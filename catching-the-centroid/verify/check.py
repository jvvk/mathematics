"""Controls for core.py and exact.py, and numerical checks of Propositions 1 and 2 and formula (3) of note.tex."""

from __future__ import annotations

import numpy as np

from core import half_plane_b, mc, prob, regular

rng = np.random.default_rng(7)
TRI = 1 / 3 + np.log(3) / 6

# controls: the asker's exact values, and Monte Carlo
assert abs(prob(regular(3)) - TRI) < 1e-6, prob(regular(3))
assert abs(prob(regular(4)) - 0.5) < 1e-9
assert abs(prob(regular(6)) - 0.5) < 1e-9
for n in (3, 5, 7):
    p, q = prob(regular(n)), mc(regular(n), 2_000_000, rng)
    assert abs(p - q) < 5 * np.sqrt(0.25 / 2_000_000), (n, p, q)
    print(f"regular {n}: quadrature {p:.6f}  MC {q:.6f}")
V = np.array([[0, 0], [3, 0], [3.5, 1], [1, 2.2], [-0.4, 1.0]])
p, q = prob(V), mc(V, 2_000_000, rng)
assert abs(p - q) < 5 * np.sqrt(0.25 / 2_000_000), (p, q)
print(f"irregular pentagon: quadrature {p:.6f}  MC {q:.6f}")

# Proposition 1 and formula (3): P - 1/2 = int rho_o b, rho_o(t) = b'(t + pi/2)/2; and the Fourier form
M = 8192
for W in (regular(3), V, regular(7)):
    t, rho, b = half_plane_b(W, M)
    P = prob(W, M)
    ro = (rho - np.roll(rho, M // 2)) / 2
    assert abs((ro * b).sum() - (P - 0.5)) < 1e-9
    db = (np.roll(b, -1) - np.roll(b, 1)) / (2 * 2 * np.pi / M)  # b' on the grid
    dens_o = ro / (2 * np.pi / M)
    err = np.max(np.abs(dens_o - np.roll(db, -M // 4) / 2))
    assert err < 1e-2 * np.max(np.abs(dens_o)), err
    beta = np.fft.fft(b) / M
    n = np.fft.fftfreq(M, 1 / M)
    four = (
        2
        * np.pi
        * sum(k * (-1) ** ((k + 1) // 2) * abs(beta[k]) ** 2 for k in range(1, 400, 2))
    )
    assert abs(four - (P - 0.5)) < 1e-5, (four, P - 0.5)
    # ingredients of Theorem 1: Grunbaum |b| <= 1/18, and |P - 1/2| <= 1/54
    assert np.max(np.abs(b)) <= 1 / 18 + 1e-6, np.max(np.abs(b)) - 1 / 18
    assert abs(P - 0.5) <= 1 / 54
print("Proposition 1, formula (3), Fourier form and Theorem 1 ingredients OK")

# the exact evaluators (exact.py): asker's values, Monte Carlo on thin shapes, and the symmetral of a triangle
import exact  # noqa: E402

TRI = 1 / 3 + np.log(3) / 6
assert abs(exact.prob(regular(3)) - TRI) < 1e-12
assert abs(exact.prob(regular(4)) - 0.5) < 1e-12 and abs(exact.prob(regular(6)) - 0.5) < 1e-12
assert abs(exact.prob(V) - prob(V, 1 << 16)) < 1e-6
for deg in (0.5, 30.0, 178.0):  # thin, ordinary and flat isosceles triangles
    a_ = np.radians(deg)
    T = np.array([[0, 0], [np.cos(a_ / 2), -np.sin(a_ / 2)], [np.cos(a_ / 2), np.sin(a_ / 2)]])
    p, q = exact.prob(T), mc(T, 2_000_000, rng)
    assert abs(p - q) < 5 * np.sqrt(0.25 / 2_000_000), (deg, p, q)
    assert abs(exact.phi(T) - 2 / 3) < 1e-12
    print(f"isosceles {deg:5.1f} deg: exact {p:.6f}  MC {q:.6f}  s = {exact.phi(T):.6f}")
assert abs(exact.phi(regular(4)) - 1) < 1e-12
W = V - V.mean(0)
ts = np.linspace(0, 2 * np.pi, 13)
one = np.array([exact._halfplane_area(W, np.array([np.cos(t), np.sin(t)])) for t in ts])
assert np.max(np.abs(exact.halfplane_areas(W, ts) - one)) < 1e-12
print("exact evaluators OK")
