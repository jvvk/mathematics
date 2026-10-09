#!/usr/bin/env python3
"""Independent finite checks; the all-n proof is in ANSWER.md.

Build the factors from the original integer recurrence, not the normalized
composition. Test their reductions with the Frobenius/gcd irreducibility
criterion, using elementary polynomial arithmetic. SymPy is used separately
to check the exact normalization identities.
"""
import json
from pathlib import Path
import sympy as s

P = 5


def trim(a):
    a = [v % P for v in a]
    while len(a) > 1 and not a[-1]:
        a.pop()
    return a


def sub(a, b):
    return trim([(a[i] if i < len(a) else 0) -
                 (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))])


def mul(a, b):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] += x * y
    return trim(c)


def rem(a, b):
    a, b = trim(a), trim(b)
    assert b != [0]
    inv = pow(b[-1], -1, P)
    while a != [0] and len(a) >= len(b):
        d = len(a) - len(b)
        t = a[-1] * inv % P
        for i, v in enumerate(b):
            a[d + i] = (a[d + i] - t * v) % P
        a = trim(a)
    return a


def gcd(a, b):
    while b != [0]:
        a, b = b, rem(a, b)
    inv = pow(a[-1], -1, P)
    return trim([v * inv for v in a])


def powmod(a, n, modulus):
    out = [1]
    while n:
        if n & 1:
            out = rem(mul(out, a), modulus)
        n //= 2
        if n:
            a = rem(mul(a, a), modulus)
    return out


def irreducible_power_two_degree(f):
    f = trim(f)
    degree = len(f) - 1
    assert degree >= 2 and degree & (degree - 1) == 0
    x = [0, 1]
    z = x
    middle_gcd = None
    for j in range(1, degree + 1):
        z = powmod(z, P, f)
        if j == degree // 2:
            middle_gcd = gcd(sub(z, x), f)
    return z == x and middle_gcd == [1]


def coefficients(poly):
    return trim([int(v) for v in reversed(poly.all_coeffs())])


def main():
    # Known positive/negative controls, including a repeated irreducible.
    controls = [
        ([2, 4, 1], True),
        ([4, 3, 1], True),
        ([1, 0, 1], False),
        (mul([2, 4, 1], [2, 4, 1]), False),
        (mul([2, 4, 1], [4, 3, 1]), False),
    ]
    for f, expected in controls:
        assert irreducible_power_two_degree(f) == expected

    q = s.Symbol('q')
    f = {1: s.Poly(q*q + q, q, domain=s.ZZ)}
    a = {j: 2 ** (2 ** (j - 1) - 1) for j in range(1, 9)}
    for j in range(1, 8):
        f[j + 1] = f[j] * (f[j] + s.Poly(a[j], q))

    u = s.Poly(q*q + q, q, domain=s.QQ)
    rows = []
    for n in range(3, 9):
        A = f[n-1] - 2*a[n-2]*f[n-2] + s.Poly(a[n-1], q)
        B = f[n-1] + 2*a[n-2]*f[n-2] + s.Poly(2*a[n-1], q)
        assert A * B == f[n] + s.Poly(a[n], q)
        assert A.LC() == B.LC() == 1
        assert A.degree() == B.degree() == 2**(n-1)
        assert s.Poly(a[n-2]**2*(u*u - u + s.Poly(2, q)), q, domain=s.ZZ) == A
        assert s.Poly(a[n-2]**2*(u*u + 3*u + s.Poly(4, q)), q, domain=s.ZZ) == B
        # The first degree/2 leading coefficients agree; the next does not.
        half = A.degree() // 2
        assert A.all_coeffs()[:half] == B.all_coeffs()[:half]
        assert A.all_coeffs()[half] != B.all_coeffs()[half]
        results = [irreducible_power_two_degree(coefficients(t)) for t in (A, B)]
        assert all(results)
        # Cross-check with a separate library implementation.
        assert all(s.Poly(t.as_expr(), q, modulus=P).is_irreducible for t in (A, B))
        rows.append({'n': n, 'degree_each': A.degree(),
                     'factorization_identity': True,
                     'normalization_identity': True,
                     'irreducible_mod_5_each': results})
        u = (u*u + u).mul_ground(s.Rational(1, 2))

    # Audit the complete five-element orbit/evaluation table in the proof.
    T = lambda x: 3*x*(x+1) % P
    minus = lambda x: (x*x-x+2) % P
    plus = lambda x: (x*x+3*x+4) % P
    assert T(3) == T(1) == 1
    assert (minus(3), plus(3), minus(1), plus(1)) == (3, 2, 2, 3)
    assert (-pow(8, -1, P)) % P == 3
    assert (-pow(4, -1, P)) % P == 1
    assert {x*x % P for x in range(1, P)} == {1, 4}

    report = {'all_n_proof': 'ANSWER.md', 'finite_checks_are_not_the_proof': True,
              'method': 'original integer recurrence; independent Frobenius/gcd test; SymPy cross-check',
              'controls_passed': len(controls), 'checks': rows,
              'critical_orbit_and_nonsquare_table': 'passed'}
    (Path(__file__).parent / 'verification.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
