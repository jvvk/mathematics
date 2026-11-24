"""Verify the finite certificate and all numerical bases of the proof.

Uses only Python's standard library. No external solver or imported research code.
Run: python3 verify_proof.py (from verify/)
"""
from pathlib import Path
import json
from math import comb, gcd


def W(n):
    return 1 + n * (n + 1) // 2


def ceildiv(a, b):
    return -((-a) // b)


def feasible(n, a, b, previous):
    """Exact recurrence of Section 6 of the paper, justified by the padding lemma (Lemma 2.1)."""
    half = 1 << (n - 1)
    p = W(n - 1)
    for u in range(a + 1):
        if u >= len(previous) or a - u >= len(previous):
            continue
        lo = max(0, u + b - previous[a - u],
                 ceildiv(p * a + (n - p) * u + n * b - half, n - 1))
        hi = min(b, previous[u] - a + u,
                 (half - (p - n) * u - n * a - b) // (n - 1))
        if lo <= hi:
            return True
    return False


def verify():
    tables = json.loads(Path(__file__).with_name('base_frontiers.json').read_text())
    assert tables[:2] == [[1, 0], [1, 0]]
    checks = 0
    for n in range(2, 16):
        previous, row = tables[n - 1], tables[n]
        for a, b in enumerate(row):
            assert 0 <= b and W(n) * a + (n + 1) * b <= 1 << n
            assert feasible(n, a, b, previous), ('lower bound', n, a, b)
            assert not feasible(n, a, b + 1, previous), ('upper bound', n, a, b)
            checks += 2
        # Monotonicity makes this certify every further a as impossible.
        assert not feasible(n, len(row), 0, previous), ('maximum a', n)
        checks += 1
        # The exact even-frontier inequality needed at small depths.
        for a in range((len(row) - 1) // 2 + 1):
            assert a < len(previous)
            assert row[2 * a] // 2 <= previous[a] - a, ('halving', n, a)
        print(f'n={n:2d}: max a={len(row)-1:3d}; frontier and halving verified')
    assert tables[1][0] // 2 <= tables[0][0]
    # Base of the large-penny lemma: all states with b>=a, c>=66, V_12<=4096.
    n = 12
    C = comb(n, 2)
    base_cases = 0
    for a in range(((1 << n) - C) // (W(n) + n + 1) + 1):
        bmax = ((1 << n) - W(n) * a - C) // (n + 1)
        assert a <= bmax <= tables[n][a]
        base_cases += 1
    print(f'Large-penny base: {base_cases} boundary cases verified at n=12')
    # The infinite extensions are the polynomial inequalities of Lemmas 3.1 and 4.1 (formalised in lean/).
    assert (1 << 13) >= (13**4 + 13**2 - 2 * 13 + 16) // 4
    assert (1 << 13) >= 2 * 13**3
    m = 15
    A = W(m) + m + 1
    assert (1 << m) >= A * m * m + (m + 2) * comb(m, 2)
    print(f'Certificate: {sum(map(len, tables))} integers; {checks} recurrence checks')
    print('ALL FINITE PROOF CHECKS PASSED')


if __name__ == '__main__':
    verify()
