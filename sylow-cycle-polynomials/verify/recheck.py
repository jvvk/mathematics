"""Independent recheck for MO 489315 (Stanley's Sylow polynomials). Shares no code with Codex's verify.py.

From the definitions only:

1. f_n(q) is the cycle polynomial of a Sylow 2-subgroup of S_{2^n}: brute force over the
   automorphism group of the binary tree for n <= 4.
2. Normalisation: f_n = a_n * (T^(n-1) o Q), a_n = 2^(2^(n-1)-1), T(x) = x(x+1)/2, Q(x) = x^2+x.
3. The factorisation f_n + a_n = A_n B_n (grinberg) and A_n, B_n = a_{n-2}^2 h_{-/+} o T^(n-3) o Q.
4. A_n, B_n irreducible mod 5 for n = 3..8 (SymPy factorisation over GF(5)).
5. The composition lemma over F_5, both directions, on random irreducible G of even degree:
   G o V is irreducible iff G(v)/lc(G) is a nonsquare (v the critical value of V).
6. The critical orbit table: T(3) = 1, T(1) = 1, h_-(3), h_+(3), h_-(1), h_+(1) nonsquares.
7. Controls: mod 3 and mod 7 the factors are reducible for some n (5 is not arbitrary);
   a wrong critical value (3 -> 2) breaks the table.
8. Addendum: f_{n,p} = p^((p^n-1)/(p-1)) * Phi^n(q), Phi(x) = (x^p + (p-1)x)/p, and the target
   f_{n,p}^(p-1) + (p-1)p^(p^n-1) = p^(p^n-1) * H(Phi^n(q)), H(x) = x^(p-1) + p - 1;
   factor counts for small p, n.

Run: python recheck.py [--quick]
"""

from __future__ import annotations

import itertools
import random
import sys

import sympy as sp

QUICK = "--quick" in sys.argv
q, x = sp.symbols("q x")
FAIL: list[str] = []


def check(name: str, ok: bool, detail: str = "") -> None:
    print(f"{'PASS' if ok else 'FAIL'}  {name}  {detail}", flush=True)
    if not ok:
        FAIL.append(name)


def a(n: int) -> int:
    return 2 ** (2 ** (n - 1) - 1)


def f(n: int) -> sp.Expr:
    g = q**2 + q
    for k in range(1, n):
        g = sp.expand(g * (g + a(k)))
    return g


# ------------------------------------------------------------------ 1. Sylow cycle polynomial
def tree_automorphisms(n: int) -> list[tuple[int, ...]]:
    """All automorphisms of the complete binary tree of depth n, as permutations of 2^n leaves.

    An automorphism is a choice of swap/no-swap at each internal vertex; leaf i (bits b_1..b_n,
    most significant first) goes to the leaf whose k-th bit is b_k XOR (swap at the vertex
    reached by the first k-1 output bits... ) -- we use the input prefix, which gives the same
    group."""
    internal = [(k, pre) for k in range(n) for pre in range(2**k)]
    perms = []
    for flips in itertools.product((0, 1), repeat=len(internal)):
        s = dict(zip(internal, flips))
        perm = []
        for leaf in range(2**n):
            bits = [(leaf >> (n - 1 - k)) & 1 for k in range(n)]
            out = 0
            for k in range(n):
                pre = 0
                for j in range(k):
                    pre = 2 * pre + bits[j]
                out = 2 * out + (bits[k] ^ s[(k, pre)])
            perm.append(out)
        perms.append(tuple(perm))
    return perms


def cycles(perm: tuple[int, ...]) -> int:
    seen, c = [False] * len(perm), 0
    for i in range(len(perm)):
        if not seen[i]:
            c += 1
            j = i
            while not seen[j]:
                seen[j] = True
                j = perm[j]
    return c


def sylow(n: int) -> sp.Expr:
    """Wreath-product recurrence P_{n+1} = P_n (P_n + |G_{2^n}|), |G_{2^n}| = 2^(2^n - 1)."""
    g = q**2 + q
    for k in range(1, n):
        g = sp.expand(g * (g + 2 ** (2**k - 1)))
    return g


for n in range(1, 4 if QUICK else 5):
    G = tree_automorphisms(n)
    poly = sp.expand(sum(q ** cycles(g) for g in G))
    check(f"Sylow cycle polynomial n={n} (|G|={len(G)}) = wreath recurrence P_n",
          sp.expand(poly - sylow(n)) == 0)
    check("  |G| = 2^(2^n - 1)", len(G) == 2 ** (2**n - 1) and len(set(G)) == len(G))
    if n >= 2:
        check(f"  the question's f_{n} is NOT the Sylow polynomial (index slip)",
              sp.expand(poly - f(n)) != 0, f"f_{n}(1) = {f(n).subs(q, 1)} vs |G| = {len(G)}")

# ------------------------------------------------------------------ 2-3. normalisation, factors
T = lambda e: e * (e + 1) / 2
Q = lambda e: e**2 + e
hm = lambda e: e**2 - e + 2
hp = lambda e: e**2 + 3 * e + 4

N_MAX = 7 if QUICK else 8
u = Q(q)
us = {1: sp.expand(u)}
for n in range(2, N_MAX + 1):
    u = sp.expand(T(u))
    us[n] = u
for n in range(1, N_MAX + 1):
    check(f"f_{n} = a_{n} * T^{n - 1}(Q)", sp.expand(f(n) - a(n) * us[n]) == 0)

factors = {}
for n in range(3, N_MAX + 1):
    A = sp.expand(f(n - 1) - 2 * a(n - 2) * f(n - 2) + a(n - 1))
    B = sp.expand(f(n - 1) + 2 * a(n - 2) * f(n - 2) + 2 * a(n - 1))
    inner = us[n - 2]
    ok = (
        sp.expand(A * B - f(n) - a(n)) == 0
        and sp.expand(A - a(n - 2) ** 2 * hm(inner)) == 0
        and sp.expand(B - a(n - 2) ** 2 * hp(inner)) == 0
        and sp.Poly(A, q).degree() == 2 ** (n - 1)
        and sp.Poly(A, q).LC() == 1
        and sp.Poly(B, q).LC() == 1
    )
    top = 2 ** (n - 2)
    ca, cb = sp.Poly(A, q).all_coeffs(), sp.Poly(B, q).all_coeffs()
    check(
        f"n={n}: f_n + a_n = A_n B_n, A_n/B_n = a^2 h(T^(n-3) Q), monic deg 2^(n-1)", ok
    )
    check(
        f"  top {top} coefficients of A_n and B_n agree",
        ca[:top] == cb[:top] and ca[top] != cb[top],
    )
    factors[n] = (A, B)

# ------------------------------------------------------------------ 4. irreducible mod 5
for n, (A, B) in factors.items():
    for name, P in (("A", A), ("B", B)):
        fl = sp.factor_list(sp.Poly(P, q, modulus=5))
        check(
            f"{name}_{n} irreducible over F_5 (deg {2 ** (n - 1)})",
            len(fl[1]) == 1 and fl[1][0][1] == 1,
        )

# ------------------------------------------------------------------ 4b. the true Sylow family
tq = q
Tk = {0: q}
for k in range(1, N_MAX):
    tq = sp.expand(T(tq))
    Tk[k] = tq
for n in range(2, N_MAX + 1):
    target = sp.expand(sylow(n) + 2 ** (2**n - 1))
    z = Tk[n - 2]
    Am, Bp = sp.expand(hm(z)), sp.expand(hp(z))
    c = sp.Integer(2) ** (2**n - 1) / 8
    ok = sp.expand(target - c * Am * Bp) == 0
    check(f"Sylow n={n}: P_n + |G| = (|G|/8) h_-(T^(n-2) q) h_+(T^(n-2) q)", ok)
    if n <= (6 if QUICK else 7):
        for name, P in (("h_-", Am), ("h_+", Bp)):
            scale = sp.Integer(2) ** (2 ** (n - 1) - 1)  # clears the powers of 2 in T^(n-2)
            Pz = sp.Poly(sp.expand(P * scale), q)
            ok_int = all(cf.is_integer for cf in Pz.all_coeffs())
            fl = sp.factor_list(sp.Poly(Pz.as_expr(), q, modulus=5))
            check(f"  {name}(T^{n-2} q), deg {2 ** (n - 1)}, integral after scaling, irreducible mod 5",
                  ok_int and len(fl[1]) == 1 and fl[1][0][1] == 1)

# ------------------------------------------------------------------ 5. composition lemma
rng = random.Random(489315)
F5 = lambda c: sp.Poly(c, x, modulus=5)
nonsq = {2, 3}
agree = 0
trials = 150 if QUICK else 400
for _ in range(trials):
    d = rng.choice([2, 4, 6])
    while True:
        G = sp.Poly(
            [rng.randrange(1, 5)] + [rng.randrange(5) for _ in range(d)], x, modulus=5
        )
        if G.is_irreducible:
            break
    lc = int(G.LC()) % 5
    if lc not in (1, 4):  # the lemma assumes a square leading coefficient
        G = sp.Poly(G.as_expr() * pow(lc, -1, 5), x, modulus=5)
    va, vb, vc = rng.randrange(1, 5), rng.randrange(5), rng.randrange(5)
    V = va * x**2 + vb * x + vc
    crit = (vc - vb * vb * pow(4 * va, -1, 5)) % 5
    Gv = int(G.eval(crit)) % 5
    lem = (Gv * pow(int(G.LC()) % 5, -1, 5)) % 5 in nonsq
    comp = sp.Poly(sp.expand(G.as_expr().subs(x, V)), x, modulus=5)
    agree += lem == comp.is_irreducible
check(
    f"composition lemma (iff) on {trials} random cases",
    agree == trials,
    f"{agree}/{trials}",
)

# ------------------------------------------------------------------ 6. critical orbit table
Tm = lambda e: (e * (e + 1) * pow(2, -1, 5)) % 5
crit_T = (-pow(8, -1, 5)) % 5
crit_Q = (-pow(4, -1, 5)) % 5
table = [
    crit_T == 3,
    crit_Q == 1,
    Tm(3) == 1,
    Tm(1) == 1,
    hm(3) % 5 == 3,
    hp(3) % 5 == 2,
    hm(1) % 5 == 2,
    hp(1) % 5 == 3,
]
check("critical values 3 (T), 1 (Q); orbit 3 -> 1 -> 1; h values nonsquare", all(table))
check("  discriminants of h_-, h_+ are -7 = 3, a nonsquare", (-7) % 5 == 3)
check(
    "  mutant: critical value 2 gives a square somewhere",
    any(v % 5 in (0, 1, 4) for v in (hm(2), hp(2), hm(Tm(2)), hp(Tm(2)))),
)

# ------------------------------------------------------------------ 7. other primes as controls
for ell in (3, 7):
    red = []
    for n, (A, B) in factors.items():
        if n > 6:
            break
        for P in (A, B):
            red.append(not sp.Poly(P, q, modulus=ell).is_irreducible)
    check(f"control: mod {ell} some factor is reducible (5 is special)", any(red))

# ------------------------------------------------------------------ 8. the addendum
for p in (2, 3, 5, 7):
    Phi = lambda e, p=p: (e**p + (p - 1) * e) / sp.Integer(p)
    fp, up = q**p + (p - 1) * q, Phi(q)
    nmax = {2: 4, 3: 3, 5: 3, 7: 2}[p]
    for n in range(1, nmax + 1):
        s = sp.Integer(p) ** ((p**n - 1) // (p - 1))
        target = sp.expand(fp ** (p - 1) + (p - 1) * sp.Integer(p) ** (p**n - 1))
        ok = (
            sp.expand(fp - s * up) == 0
            and sp.expand(
                target - sp.Integer(p) ** (p**n - 1) * (up ** (p - 1) + p - 1)
            )
            == 0
        )
        check(f"addendum p={p} n={n}: f = p^e Phi^n, target = p^(p^n-1) H(Phi^n)", ok)
        if n <= (2 if p > 5 else 3) and not QUICK or n == 1:
            fl = sp.factor_list(sp.Poly(target, q))
            degs = sorted(int(sp.Poly(fac, q).degree()) for fac, _ in fl[1])
            D = (p - 1) * p**n
            want = [D // 2, D // 2] if p == 5 or (p == 2 and n >= 2) else [D]
            check(f"  factor degrees over Q: {degs}", degs == want and
                  all(e == 1 for _, e in fl[1]), f"expected {want}")
        fp = sp.expand(fp * (fp ** (p - 1) + (p - 1) * sp.Integer(p) ** (p**n - 1)))
        up = sp.expand(Phi(up))

print()
print("ALL PASS" if not FAIL else f"FAILURES: {FAIL}")
sys.exit(1 if FAIL else 0)
