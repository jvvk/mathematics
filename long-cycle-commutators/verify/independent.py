"""Claude's independent check (shares no code with Codex's check.py) of the signed route:
 (3) 2^(n+1) BiL(I,I) = n 4^l sum_{r_j,s_j odd, a+b=n+1} (a-1)!(b-1)! prod_j C(i_j-1,r_j-1)C(i_j-1,s_j-1)/(r_j s_j)
     with BiL(I,I) = (prod m_i!)^2 Bi(lam,lam), Bi by brute-force factorisations c = alpha beta;
 O_n by brute force from its definition; W_m by brute force from its definition; then
 O_n = 2^(n+1)(n-1)!|F|, O_n = 4 n! W_(n-1), (n+1) W_(n-1) = 2^n n!, with |F| = sum_lam z_lam Bi(lam,lam)."""
import itertools, sys
from fractions import Fraction
from math import factorial, comb
from collections import Counter
def cycles(p):
    n = len(p); seen = [0] * n; out = []
    for i in range(n):
        if not seen[i]:
            c = []; j = i
            while not seen[j]: seen[j] = 1; c.append(j); j = p[j]
            out.append(c)
    return out
def ctype(p): return tuple(sorted((len(c) for c in cycles(p)), reverse=True))
def z(lam):
    r = 1
    for k, m in Counter(lam).items(): r *= k ** m * factorial(m)
    return r
def bi_table(n):
    c = [(i + 1) % n for i in range(n)]
    T = Counter()
    for alpha in itertools.permutations(range(n)):
        ainv = [0] * n
        for i, x in enumerate(alpha): ainv[x] = i
        beta = [ainv[c[i]] for i in range(n)]            # alpha beta = c  (beta = alpha^-1 c)
        T[(ctype(alpha), ctype(beta))] += 1
    return T
def compositions(n):
    if n == 0: yield (); return
    for f in range(1, n + 1):
        for rest in compositions(n - f): yield (f,) + rest
def rhs3(I, n):
    l = len(I); tot = Fraction(0)
    odd = [[r for r in range(1, i + 1, 2)] for i in I]
    for rs in itertools.product(*odd):
        for ss in itertools.product(*odd):
            a, b = sum(rs), sum(ss)
            if a + b != n + 1: continue
            t = Fraction(factorial(a - 1) * factorial(b - 1))
            for i, r, s in zip(I, rs, ss): t *= Fraction(comb(i - 1, r - 1) * comb(i - 1, s - 1), r * s)
            tot += t
    return n * 4 ** l * tot
def O_brute(n):
    tot = 0
    for pi in itertools.permutations(range(n)):
        cs = cycles(pi)
        for a in range(1, n + 1):
            b = n + 1 - a
            if not 1 <= b <= n: continue
            for A in itertools.combinations(range(n), a):
                As = set(A)
                if any(len(As.intersection(c)) % 2 == 0 for c in cs): continue
                for B in itertools.combinations(range(n), b):
                    Bs = set(B)
                    if any(len(Bs.intersection(c)) % 2 == 0 for c in cs): continue
                    tot += 4 ** len(cs) * factorial(a - 1) * factorial(b - 1)
    return tot
def W_brute(m):
    tot = 0
    for marks in itertools.product(((0, 0), (1, 0), (0, 1), (1, 1)), repeat=m):
        if sum(x + y for x, y in marks) != m: continue
        a = sum(x for x, _ in marks); b = sum(y for _, y in marks)
        for k in range(m + 1):
            right = sum(x + y for x, y in marks[k:])
            tot += (-1) ** right * factorial(a) * factorial(b)
    return tot
if __debug__ is False:
    raise SystemExit("refusing to run with -O: the checks are assert statements")
for n in [int(x) for x in sys.argv[1:]] or [1, 3, 5, 7]:
    T = bi_table(n)
    F = sum(z(lam) * T[(lam, lam)] for lam in {k[0] for k in T})
    ok3 = True
    for I in compositions(n):
        lam = tuple(sorted(I, reverse=True))
        BiL = 1
        for k, m in Counter(lam).items(): BiL *= factorial(m) ** 2
        BiL *= T[(lam, lam)]
        if 2 ** (n + 1) * BiL != rhs3(I, n): ok3 = False; print("   (3) FAILS for I =", I)
    W = W_brute(n - 1)
    O = O_brute(n) if n <= 7 else None
    assert F == 2 * n * factorial(n) // (n + 1) and (n + 1) * F == 2 * n * factorial(n), ("|F|", n, F)
    assert ok3, ("Proposition 2 (I = J)", n)
    assert (n + 1) * W == 2 ** n * factorial(n), ("(n+1) W", n, W)
    if O is not None:
        assert O == 2 ** (n + 1) * factorial(n - 1) * F, ("O_n bridge", n, O)
        assert O == 4 * factorial(n) * W, ("O_n = 4 n! W", n, O)
    print(f"n={n}: |F|={F} (2n n!/(n+1)={2*n*factorial(n)//(n+1)})  (3) for all compositions: {ok3}  W_(n-1)={W}  "
          f"(n+1)W={(n+1)*W} vs 2^n n!={2**n*factorial(n)}  O_n={O}  2^(n+1)(n-1)!|F|={2**(n+1)*factorial(n-1)*F}  4n!W={4*factorial(n)*W}", flush=True)

print("ALL INDEPENDENT CHECKS PASSED")
