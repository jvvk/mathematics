"""Finite audits of the hand proof; these are not a proof of global injectivity.

Run each mutation in a fresh foreground process through run_checks.py.
"""
import argparse
from functools import lru_cache
import numpy as np

parser = argparse.ArgumentParser()
parser.add_argument("--mutant", default="none")
MUTANT = parser.parse_args().mutant
checks = 0


def check(claim, message):
    global checks
    checks += 1
    assert bool(claim), message


def close(a, b, message, tol=2e-8):
    check(np.allclose(a, b, rtol=tol, atol=tol), message)


@lru_cache(None)
def rule(n):
    x, w = np.polynomial.legendre.leggauss(n)
    return (x + 1) / 2, w / 2


def gaussian(x):
    return np.exp(-np.sum(np.asarray(x) ** 2, axis=-1) / 2)


def triangle(A, B, C, n=64, uniform=False):
    u, w = rule(n)
    U, V = np.meshgrid(u, u, indexing="ij")
    X = A + U[..., None] * (B - A) + ((1 - U) * V)[..., None] * (C - A)
    D = abs(np.linalg.det(np.array([B - A, C - A])))
    W = np.outer(w, w) * (1 - U) * D
    W *= 1 if uniform else gaussian(X)
    mass = W.sum()
    moment = np.sum(X * W[..., None], axis=(0, 1))
    return mass, moment / mass


def boundary(A, B, C, n=64):
    t, w = rule(n)
    moment = np.zeros(2)
    for P, Q, R in [(A, B, C), (B, C, A), (C, A, B)]:
        v = Q - P
        normal = np.array([v[1], -v[0]], dtype=float)
        if normal @ (R - P) > 0:
            normal *= -1
        X = P + t[:, None] * v
        moment -= normal * np.dot(w, gaussian(X))
    if MUTANT == "boundary_sign":
        moment *= -1
    return moment


def edge_jacobian(A, B, C, n=64, uniform=False):
    mass, e = triangle(A, B, C, n, uniform)
    t, w = rule(n)
    J = np.zeros((2, 2))
    ab = []
    for P, Q in [(A, B), (B, A)]:
        v = C - P
        L = np.linalg.norm(v)
        normal = np.array([v[1], -v[0]]) / L
        if normal @ (Q - P) > 0:
            normal *= -1
        X = P + t[:, None] * v
        g = np.ones(n) if uniform else gaussian(X)
        velocity = np.ones(n) if MUTANT == "edge_velocity" else t
        a = np.sum((X - e) * (velocity * g * w * L)[:, None], axis=0)
        J += np.outer(a, normal) / mass
        ab.append((np.dot(t * g, w), np.dot(t * (1 - t) * g, w)))
    lam = np.linalg.solve(np.column_stack([C - A, C - B]), C - e)
    (alphaA, betaA), (alphaB, betaB) = ab
    D = abs(np.linalg.det(np.array([B - A, C - A])))
    sign = -1 if MUTANT == "determinant_sign" else 1
    reduced = sign * D**2 / mass**2 * (
        alphaA * betaB * lam[0] + alphaB * betaA * lam[1] - betaA * betaB
    )
    if MUTANT == "orientation":
        reduced *= np.sign(np.linalg.det(np.array([B - A, C - A])))
    return J, reduced


def F(s, a, b, D, n=64):
    s = np.asarray(s)
    t, w = rule(n)
    x = D + s[..., None] * (-a + (a + b) * t)
    jac = np.ones_like(s) if MUTANT == "section_scale" else s
    return (a + b) * jac * np.sum(np.exp(-x**2 / 2) * w, axis=-1)


def slope(s, a, b, D):
    if MUTANT == "drop_logconcavity":
        # Increasing F(s)=s*exp(50*s*s), but log F is not concave.
        return 1 / s + 100 * s
    den = F(s, a, b, D)
    return (b * np.exp(-(D + b * s)**2 / 2)
            + a * np.exp(-(D - a * s)**2 / 2)) / den


def slice_moment(a, b, D, y0, h, n=64):
    t, w = rule(n)
    y = h * t
    s = 1 - t
    q = F(s, a, b, D, n) * np.exp(-(y0 + y)**2 / 2)
    mass = h * np.dot(w, q)
    return mass, y0 + np.dot(w, y * q) / np.dot(w, q)


def tetrahedron(vertices, n=28):
    t, w = rule(n)
    u, v, z = np.meshgrid(t, t, t, indexing="ij")
    a, b, c, d = vertices
    X = (a + u[..., None] * (b - a)
         + ((1-u)*v)[..., None] * (c-a)
         + ((1-u)*(1-v)*z)[..., None] * (d-a))
    D = abs(np.linalg.det(np.array([b-a, c-a, d-a])))
    W = w[:, None, None] * w[None, :, None] * w[None, None, :]
    W = W * D * (1-u)**2 * (1-v) * gaussian(X)
    return W.sum(), np.sum(X * W[..., None], axis=(0, 1, 2)) / W.sum()


triangles = [
    ([-1, -.5], [1, -.5], [.3, 1]),
    ([.2, 1], [2, -.2], [-.7, .3]),
    ([-2, -1], [.5, -1], [1.2, 2]),
]
for coords in triangles:
    A, B, C = map(lambda x: np.array(x, dtype=float), coords)
    mass, e = triangle(A, B, C)
    mass96, e96 = triangle(A, B, C, 96)
    close([mass, *e], [mass96, *e96], "independent quadrature order")
    close(boundary(A, B, C), mass * e, "Gaussian divergence theorem")
    J, reduced = edge_jacobian(A, B, C)
    eps = 2e-5
    fd = np.column_stack([
        (triangle(A, B, C + eps * v)[1] - triangle(A, B, C - eps * v)[1]) / (2*eps)
        for v in np.eye(2)
    ])
    close(J, fd, "shape derivative against volume finite difference")
    close(np.linalg.det(J), reduced, "edge determinant reduction")
    Js, reduced_s = edge_jacobian(B, A, C)
    close(J, Js, "centroid Jacobian invariant under base swap")
    close(np.linalg.det(Js), reduced_s, "orientation must not alter determinant")
    _, eu = triangle(A, B, C, uniform=True)
    close(eu, (A+B+C)/3, "exact uniform centroid")
    Ju, du = edge_jacobian(A, B, C, uniform=True)
    close(Ju, np.eye(2)/3, "exact uniform Jacobian")
    close(du, 1/9, "exact uniform determinant")

configs = [
    (1., 2., 0., -.7), (.2, 1.3, 2., .4),
    (2., .4, -1.7, -1.2), (0., 1.2, .3, -.5),
    (1.7, 0., -.4, .6), (.1, .15, 3., -.3),
]
for a, b, D, y0 in configs:
    values = np.linspace(.05, 1., 20)
    fv = F(values, a, b, D)
    check(np.all(np.diff(fv) > 0), "homothetic section masses increase")
    gs = slope(values, a, b, D)
    check(np.all(np.diff(gs) < 1e-9), "logarithmic section derivative decreases")
    for h1, h2 in [(.4, .8), (.8, 1.6), (1.6, 3.2)]:
        heights = np.linspace(.03*h1, .97*h1, 19)
        s1, s2 = 1-heights/h1, 1-heights/h2
        der = slope(s1, a, b, D)/h1 - slope(s2, a, b, D)/h2
        if MUTANT == "likelihood_sign":
            der *= -1
        for x in der:
            check(x > 0, "likelihood ratio increases with height")
        ratio = F(s2, a, b, D)/F(s1, a, b, D)
        if MUTANT == "ratio_reversal":
            ratio = 1/ratio
        check(np.all(np.diff(ratio) > 0), "direct likelihood-ratio order")
        means = []
        for h in (h1, h2):
            m1, y1 = slice_moment(a, b, D, y0, h)
            A, B, C = np.array([D-a, y0]), np.array([D+b, y0]), np.array([D, y0+h])
            m2, e = triangle(A, B, C)
            close([m1, y1], [m2, e[1]], "slice formula against triangle quadrature")
            means.append(y1)
        check(means[1] > means[0], "normal centroid strictly increases")
        # Reverse the side of the base; the signed centroids must separate.
        A, B, Cm = np.array([D-a, y0]), np.array([D+b, y0]), np.array([D, y0-h1])
        check(triangle(A, B, Cm)[1][1] < y0 < means[0], "opposite half-spaces")

# All-dimensional extension: compare a tetrahedron directly with its 2D sections.
base = np.array([[-1., -.4], [1.3, -.2], [.1, 1.2]])
foot = .2 * base[0] + .3 * base[1] + .5 * base[2]
last = None
for h in [.5, 1., 2.]:
    t, w = rule(28)
    q = []
    for y in h*t:
        section = foot + (1-y/h)*(base-foot)
        section_mass, _ = triangle(*section, n=28)
        q.append(section_mass*np.exp(-(y-.3)**2/2))
    q = np.array(q)
    slice_mass = h*np.dot(w, q)
    slice_height = np.dot(w, h*t*q)/np.dot(w, q)
    verts = np.column_stack([base, np.full(3, -.3)])
    verts = np.vstack([verts, [*foot, h-.3]])
    direct_mass, direct_mean = tetrahedron(verts)
    close([slice_mass, slice_height-.3], [direct_mass, direct_mean[2]], "tetrahedron section identity")
    if last is not None:
        check(slice_height > last, "tetrahedron centroid order")
    last = slice_height

# Hypothesis controls: arbitrary apex projections do not satisfy the new theorem.
A, B = np.array([10., 0.]), np.array([11., 0.])
y10 = triangle(A, B, np.array([0., 10.]), 96)[1][1]
y20 = triangle(A, B, np.array([0., 20.]), 96)[1][1]
check(y20 < y10-.5, "projection outside the base can reverse centroid height")
if MUTANT == "drop_foot_condition":
    check(y20 > y10, "invalid unrestricted normal-height claim")

print(f"PASS: {checks} assertions; mutant={MUTANT}")
