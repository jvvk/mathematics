"""Integer scores 1..m: X = 1 + #{k: U > a_k}, Y = 1 + #{l: V > b_l}. Maximise corr over cut-points; compare rho_S."""
import numpy as np
from scipy import optimize, integrate

def C(u, v, t):
    return -np.log1p(np.expm1(-t*u)*np.expm1(-t*v)/np.expm1(-t))/t

def rho_s(t):
    return 12*integrate.dblquad(lambda v, u: C(u, v, t), 0, 1, 0, 1, epsabs=1e-14, epsrel=1e-14)[0] - 3

def corr(a, b, t):
    a = np.sort(a); b = np.sort(b)
    A, B = np.meshgrid(a, b, indexing="ij")
    cov = np.sum(C(A, B, t) - A*B)            # cov of indicators 1{U>a},1{V>b} = C(a,b)-ab
    va = np.sum(np.minimum.outer(a, a) - np.outer(a, a))
    vb = np.sum(np.minimum.outer(b, b) - np.outer(b, b))
    return cov/np.sqrt(va*vb)

def best(m, t, tries=6, rng=np.random.default_rng(1)):
    k = m-1; top = -1
    for i in range(tries):
        x0 = np.sort(rng.uniform(0.02, 0.98, 2*k)) if i else np.r_[np.linspace(0, 1, m+1)[1:-1]]*np.ones(1)
        if i == 0: x0 = np.r_[x0, x0]
        z0 = np.log(x0/(1-x0))
        f = lambda z: -corr(1/(1+np.exp(-z[:k])), 1/(1+np.exp(-z[k:])), t)
        r = optimize.minimize(f, z0, method="BFGS", options={"gtol": 1e-12})
        if -r.fun > top: top, z = -r.fun, r.x
    return top, np.sort(1/(1+np.exp(-z[:k]))), np.sort(1/(1+np.exp(-z[k:])))

if __name__ == "__main__":
    for t in [3, 5, 8, 10, 15, 20, 30]:
      rs = rho_s(t); row = []
      for m in [2, 3, 4, 5, 6, 8, 11, 15, 20, 30]:
          c, a, b = best(m, t)
          row.append(f"m={m}:{c-rs:+.1e}")
      print(f"theta={t:3d} rho_S={rs:.5f} ", " ".join(row), flush=True)
