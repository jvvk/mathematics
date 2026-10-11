"""All-degree finite-sum formula for P's first three logarithmic jets,
and an exact inhomogeneous correction for the fourth jet.
"""
from math import factorial, comb
from fractions import Fraction as F
from frob_struct import cyk, frob_P


def rising(c0, c1, length):
    result = [F(1)] + [F(0)] * (cyk.E-1)
    for j in range(length):
        result = cyk.smul(result, [F(c0)+j, F(c1)] + [F(0)]*(cyk.E-2))
    return result


def closed_L(N):
    answer = [F(0)] * cyk.E
    for m in range(N//4+1):
        num = rising(F(1,2), F(3,4), N-m)
        den = rising(1, F(1,4), m)
        den = cyk.smul(cyk.smul(den, den), den)
        term = cyk.smul(num, cyk.sinv(den))
        scalar = F((-1)**m * 16**(N-2*m), factorial(N-4*m))
        answer = [answer[i]+scalar*term[i] for i in range(cyk.E)]
    return answer


def correction(M):
    u = [F(0)]*(M+1)
    for N in range(1, M+1):
        rhs = -4**N*(comb(2*N,N)-comb(2*N-2,N-1))
        rhs += 4*(2*N-1)*(5*(N-1)**2+5*(N-1)+2)*u[N-1]
        if N>=2:
            rhs -= 48*(N-1)*(3*N-4)*(3*N-2)*u[N-2]
        u[N] = rhs / F(N**3)
    return u


def verify(M=40):
    T = cyk.T
    L = [T**3, -4*(2*T+1)*(5*T**2+5*T+2), 48*(T+1)*(3*T+2)*(3*T+4)]
    cyk.E=4
    direct = cyk.frob(L,M)
    u = correction(M)
    for N in range(M+1):
        candidate = closed_L(N)
        assert candidate[:3] == direct[N][:3], N
        candidate[3] += u[N]
        assert candidate == direct[N], N
    print(f'All four L jets agree through degree {M}, including the inhomogeneous correction.')
    b = [F(1),F(0),F(0),F(0)]
    Pdirect = frob_P(L,M)
    for N in range(M+1):
        if N:
            b = cyk.smul(b, cyk.smul([F(4*N-2),F(4),F(0),F(0)],
                                   cyk.sinv([F(N),F(1),F(0),F(0)])))
        candidate = closed_L(N)
        candidate[3] += u[N]
        assert cyk.smul(b,candidate)==Pdirect[N], N
    print(f'All four P jets agree through degree {M}.')


if __name__ == '__main__':
    verify()
