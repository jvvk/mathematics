"""Exact obstruction to a BV-strong Frobenius operator at p=3.

Standalone rational calculation from P itself; no third-party dependencies.
The coefficients are affine vectors (constant, alpha1, alpha2, alpha3).
"""
from fractions import Fraction as F
from math import comb

ORDER = 4


def mul(a, b):
    return [sum(a[j] * b[k-j] for j in range(k+1))
            for k in range(ORDER)]


def linear(c, d=1):
    return [F(c), F(d), F(0), F(0)]


def product(*factors):
    out = linear(1, 0)
    for factor in factors:
        out = mul(out, factor)
    return out


def periods(R):
    a = [linear(1, 0)]
    for N in range(1, R+1):
        t = N-1
        q1 = product(linear(-8, 0), linear(2*t+1, 2),
                     linear(2*t+1, 2),
                     [F(5*t*t+5*t+2), F(10*t+5), F(5), F(0)])
        rhs = [-x for x in mul(q1, a[N-1])]
        if N >= 2:
            t = N-2
            q2 = product(linear(192, 0), linear(2*t+1, 2),
                         linear(3*t+2, 3), linear(3*t+4, 3),
                         linear(2*t+3, 2))
            rhs = [x-y for x, y in zip(rhs, mul(q2, a[N-2]))]
        inverse = [F((-1)**k * comb(k+3, 3), N**(k+4))
                   for k in range(ORDER)]
        a.append(mul(rhs, inverse))
    return a


def frobenius(a, p, lift_constant=1):
    R = len(a)-1
    A = [[None]*(R+1) for _ in range(ORDER)]
    # u=p*epsilon makes the unknown coefficient A_i,N the u^i coefficient.
    for N in range(R+1):
        rhs = [[a[N][j-k] if k <= j else F(0)
                for k in range(ORDER)] for j in range(ORDER)]
        for r in range(N % p, N, p):
            m = (N-r)//p
            source = [lift_constant**m*a[m][j]/p**j for j in range(ORDER)]
            for i in range(ORDER):
                power = [F(comb(i, k)*(N-r)**(i-k)) if k <= i else F(0)
                         for k in range(ORDER)]
                coeff = mul(power, source)
                for j in range(ORDER):
                    rhs[j] = [rhs[j][k]-coeff[j]*A[i][r][k]
                              for k in range(ORDER)]
        for i in range(ORDER):
            A[i][N] = rhs[i]
    return A


def residue(x, modulus):
    return x.numerator * pow(x.denominator, -1, modulus) % modulus


if __name__ == '__main__':
    a = periods(9)
    assert [x[0] for x in a[:5]] == [1, 16, 576, 25600, 1220800]
    A = frobenius(a, 3)
    expected = {(3, 3): [4, 1, 0, 0], (2, 9): [7, 7, 0, 0]}
    for key, target in expected.items():
        i, N = key
        vec = A[i][N]
        reduced = [residue(9*x, 9) for x in vec]
        assert reduced == target
        print(f'A_{i},{N} =', ', '.join(map(str, vec)))
        print('9 times this affine vector, modulo 9:', reduced)
    print('Integrality requires alpha1=5 mod9 and alpha1=8 mod9: impossible.')
