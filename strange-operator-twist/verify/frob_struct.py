"""Direct computation of a Beukers-Vlasenko Frobenius structure at a prime p, lift t -> t^p.
Relation (coefficient of t^{N+pε} in A(Y(t^p,ε)) = α(pε) Y(t,pε)):
   sum_{r ≡ N (p), 0<=r<=N} sum_i A_{i,r} (N-r+pε)^i A_{(N-r)/p}(ε) = α(pε) A_N(pε)   (mod ε^n)
The r = N term is sum_i A_{i,N} (pε)^i, so A_{j,N} is determined recursively, affine in α_1..α_{n-1}.
Then find α ∈ Z_p^{n-1} (digit by digit) making every A_{j,N} p-integral, and report α_1 mod p^s."""
import sys
from fractions import Fraction as F
import cyk
from hadamard_frob import frob_P

T = cyk.T


def vp(x, p):
    if x == 0:
        return 10**9
    x = F(x); v = 0
    n, d = x.numerator, x.denominator
    while n % p == 0: n //= p; v += 1
    while d % p == 0: d //= p; v -= 1
    return v


def structure(coef, p, R, n):
    """coef[N] = list of ε-coefficients (length n). Returns A[j][N] as affine vectors [c, d1..d_{n-1}]."""
    nv = n                                        # vector: const + α_1..α_{n-1}
    zero = lambda: [F(0)] * nv
    A = [[None] * (R + 1) for _ in range(n)]
    for N in range(R + 1):
        # RHS: α(pε) A_N(pε) = sum_j ε^j sum_{a+b=j} α_a p^a * coef[N][b] p^b ; α_0 = 1
        rhs = []
        for j in range(n):
            v = zero()
            for a_ in range(j + 1):
                b = j - a_
                val = coef[N][b] * p**j
                if a_ == 0: v[0] += val
                else: v[a_] += val
            rhs.append(v)
        # subtract known terms r < N
        for r in range(N % p, N, p):
            m = (N - r) // p
            for i in range(n):
                # (N-r+pε)^i * A_m(ε) : ε^j coefficient
                poly = [F(0)] * n
                for k in range(i + 1):
                    if k < n:
                        from math import comb
                        poly[k] += comb(i, k) * F(N - r) ** (i - k) * p**k
                for j in range(n):
                    cj = sum(poly[k] * coef[m][j - k] for k in range(j + 1))
                    if cj:
                        rhs[j] = [rhs[j][t] - cj * A[i][r][t] for t in range(nv)]
        # r = N term: sum_i A_{i,N} (pε)^i A_0(ε), A_0 = 1 exactly
        for j in range(n):
            A[j][N] = [x / p**j for x in rhs[j]]
    return A


def solve_alpha(A, p, n, smax):
    conds = [vec for row in A for vec in row]
    cands = [tuple([0] * (n - 1))]
    for s in range(smax + 1):
        new = []
        from itertools import product
        for base in cands:
            for dig in (product(range(p), repeat=n - 1) if s > 0 else [tuple([0] * (n - 1))]):
                al = [base[k] + (dig[k] * p**(s - 1) if s > 0 else 0) for k in range(n - 1)]
                ok = True
                for vec in conds:
                    dmin = min((vp(vec[k + 1], p) for k in range(n - 1)), default=10**9)
                    if dmin + s < 0:          # not yet determined at this precision
                        continue
                    val = vec[0] + sum(vec[k + 1] * al[k] for k in range(n - 1))
                    if vp(val, p) < 0:
                        ok = False; break
                if ok: new.append(tuple(al))
        cands = list(set(new)) if s > 0 else cands
        if not cands: return s, []
        if len(cands) > 5000: return s, cands[:5]
    return smax, cands


def plog(x, p, prec):
    """p-adic log of x ≡ 1 mod p, as a rational approximation correct mod p^prec."""
    y = F(x) - 1; tot = F(0); k = 1; pw = y
    while vp(pw, p) - vp(k, p) < prec + 5:
        tot += (-1) ** (k + 1) * pw / k; k += 1; pw *= y
    return tot


def modp(x, p, s):
    x = F(x); m = p**s
    return (x.numerator * pow(x.denominator, -1, m)) % m


if __name__ == "__main__":
    which, p, R, smax = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    from sympy import legendre_symbol
    if which == "P":
        cyk.E = 4; n = 4
        Lq = [T**3, -4*(2*T+1)*(5*T**2+5*T+2), 48*(T+1)*(3*T+2)*(3*T+4)]
        a = frob_P(Lq, R)
    else:
        cyk.E = 3; n = 3
        a = cyk.frob([T**3, -4*(2*T+1)*(5*T**2+5*T+2), 48*(T+1)*(3*T+2)*(3*T+4)], R)
    coef = [[a[N][j] for j in range(n)] for N in range(R + 1)]
    A = structure(coef, p, R, n)
    s, cands = solve_alpha(A, p, n, smax)
    cp = legendre_symbol(2, p) * 2 ** ((p - 1) // 2)
    pred = plog(cp, p, smax + 2) / p
    print(f"{which} p={p} R={R}: integral Frobenius structure solutions at precision p^{s}: {len(cands)}")
    for c in cands[:5]:
        print(f"   α mod p^{s}: {c};  predicted α1 = log_p(c_p)/p mod p^{s}: {modp(pred, p, s)}")
