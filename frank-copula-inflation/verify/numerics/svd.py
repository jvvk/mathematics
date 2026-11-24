"""Exact N x N equiprobable discretisation of the Frank copula; top nontrivial singular value vs Spearman rho."""
import numpy as np
from scipy import integrate

def C(u, v, t):
    return -np.log1p(np.expm1(-t*u)*np.expm1(-t*v)/np.expm1(-t))/t

def rho_s(t):
    val, _ = integrate.dblquad(lambda v, u: C(u, v, t), 0, 1, 0, 1, epsabs=1e-13, epsrel=1e-13)
    return 12*val - 3

def table(N, t):
    g = np.linspace(0, 1, N+1)
    U, V = np.meshgrid(g, g, indexing="ij")
    Cg = C(U, V, t); Cg[0, :] = 0; Cg[:, 0] = 0; Cg[-1, :] = g; Cg[:, -1] = g
    return np.diff(np.diff(Cg, axis=0), axis=1)

for t in [1.0, 3.0, 5.0, 10.0, 20.0]:
    rs = rho_s(t)
    for N in [20, 100, 400]:
        P = table(N, t); r = P.sum(1); c = P.sum(0)
        A = P/np.sqrt(np.outer(r, c))
        Uu, s, Vt = np.linalg.svd(A)
        f = Uu[:, 1]/np.sqrt(r); f *= np.sign(f[-1]-f[0])
        mono = np.all(np.diff(f) > 0)
        # identity scores (cell midpoints) correlation for this table
        x = (np.arange(N)+0.5)/N
        ex = x@r; vx = (x**2)@r-ex**2; cid = (x@P@x-ex*ex)/vx
        print(f"theta={t:5.1f} N={N:4d} rho_S={rs:.6f} sigma1={s[1]:.6f} diff={s[1]-rs:+.2e} idcorr={cid:.6f} monotone={mono}")
