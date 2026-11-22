"""Sanity check of Proposition 3.1 at finite size: Monte Carlo loop counts in random n x n boxes
(n even) against the exact expectation sum_L P(L) (n+1-w)(n+1-h), computed from the Dyck-path weights.
For even n every count n+1-w is even, so the four parity classes of positions are equally frequent and
the symmetrised weight is exact.  Asserts |z| < 4.
"""
import random
import statistics as st

n, T = 200, 300


def mc_loops(p, rng):
    eps = [0 if rng.random() < p else 1 for _ in range(n + 1)]
    eta = [0 if rng.random() < p else 1 for _ in range(n + 1)]
    W = n + 1
    par, deg = list(range(W * W)), [0] * (W * W)

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x

    def add(a, b):
        deg[a] += 1
        deg[b] += 1
        ra, rb = f(a), f(b)
        if ra != rb:
            par[ra] = rb

    for i in range(W):
        for j in range(n):
            if j % 2 == eps[i]:
                add(i * W + j, i * W + j + 1)
    for j in range(W):
        for i in range(n):
            if i % 2 == eta[j]:
                add(i * W + j, (i + 1) * W + j)
    used, open_ = set(), set()
    for x in range(W * W):
        if deg[x]:
            r = f(x)
            used.add(r)
            if deg[x] != 2:
                open_.add(r)
    return len(used - open_)


def exact(p):
    q = 1 - p
    u, v = p * p, q * q
    amax = (n - 1) // 2
    byk = {}
    for s, t, pre in ((v, u, u), (u, v, v)):
        dp = {(0, 0): 1.0}
        byk.setdefault(0, {})
        byk[0][0] = byk[0].get(0, 0) + pre
        for step in range(2 * amax):
            nd = {}
            for (h, mx), w in dp.items():
                if h > 0:
                    nd[(h - 1, mx)] = nd.get((h - 1, mx), 0) + w
                if 2 * amax - step - 1 >= h + 1:
                    key = (h + 1, max(mx, h + 1))
                    nd[key] = nd.get(key, 0) + w * (s if h % 2 == 0 else t)
            dp = nd
            if step % 2 == 1:
                a = (step + 1) // 2
                for (h, mx), w in dp.items():
                    if h == 0:
                        byk.setdefault(mx, {})
                        byk[mx][a] = byk[mx].get(a, 0) + pre * w
    return sum(sum(w * (n - 2 * a) for a, w in d.items()) ** 2 for d in byk.values()) / 4


rng = random.Random(20261020)
for p in (0.3, 0.15):
    xs = [mc_loops(p, rng) for _ in range(T)]
    m, se, e = st.mean(xs), st.stdev(xs) / T**0.5, exact(p)
    z = (m - e) / se
    assert abs(z) < 4, (p, m, e, z)
    print(f"p = {p}: Monte Carlo {m / n**2:.5f} +- {se / n**2:.5f}, exact {e / n**2:.5f}, z = {z:+.2f}")
