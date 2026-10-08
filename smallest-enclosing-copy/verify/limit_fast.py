"""Fast exact limit model, triangle (p=3) and square (p=4). Side k: Poisson points (sigma in [-1,1], D >= 0), scale-free.
M_k(T) = max_i (T sigma_i - D_i) (convex, piecewise linear; only the lower convex hull of the points in (sigma, D) matters).
p=3: rho*(T) = (M1+M2+M3)/3.  p=4: rho*(T) = max((M1+M3)/2, (M2+M4)/2).
Event (Q inside K)  <=>  M_k(T*) <= -|T*| for every side k  (the event E of Section 2 of the paper).
Usage: limit_fast.py p trials seed"""
import os, sys, signal, math, numpy as np
def _stop(*_): raise TimeoutError
signal.signal(signal.SIGALRM, _stop); signal.alarm(int(os.environ.get("TIME_LIMIT", "0")))

def lower_hull(sig, D):
    pts = sorted(zip(sig, D)); h = []
    for p in pts:
        while len(h) >= 2 and (h[-1][0]-h[-2][0])*(p[1]-h[-2][1]) - (h[-1][1]-h[-2][1])*(p[0]-h[-2][0]) <= 0: h.pop()
        h.append(p)
    return np.array(h)

def side(rng, Dmax=12.0):
    m = rng.poisson(2 * Dmax); return lower_hull(rng.uniform(-1, 1, m), rng.uniform(0, Dmax, m))

M = lambda H, T: (T * H[:, 0] - H[:, 1]).max()

def trial(p, rng):
    Hs = [side(rng) for _ in range(p)]
    if p == 3: f = lambda T: sum(M(H, T) for H in Hs)
    else: f = lambda T: max(M(Hs[0], T) + M(Hs[2], T), M(Hs[1], T) + M(Hs[3], T))
    # breakpoints: hull edge slopes, plus (p=4) crossings of the two pair sums, found by bisection on a bracket
    bps = sorted(set(float((b[1]-a[1])/(b[0]-a[0])) for H in Hs for a, b in zip(H[:-1], H[1:])))
    bps = [-1e6] + bps + [1e6]
    vals = [f(t) for t in bps]; i = int(np.argmin(vals))
    a, b = bps[max(i-1, 0)], bps[min(i+1, len(bps)-1)]
    for _ in range(80):   # ternary search on the convex function inside the bracket
        m1, m2 = a + (b-a)/3, b - (b-a)/3
        if f(m1) <= f(m2): b = m2
        else: a = m1
    T = (a + b) / 2
    return all(M(H, T) <= -abs(T) + 1e-9 for H in Hs)

if __name__ == "__main__":
    p, n, seed = map(int, sys.argv[1:4]); rng = np.random.default_rng(seed); r = []
    try:
        for _ in range(n): r.append(trial(p, rng))
    except Exception as e: print("stopped:", type(e).__name__)
    k, m = len(r), sum(r); print(f"p={p} trials={k} P={m/k:.4f} +- {math.sqrt(m/k*(1-m/k)/k):.4f}")
