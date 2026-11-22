"""Proved centre-only filters; see CENTRE_SEXTICS.md.

Default: read m{4,5,6}_distinct_survivors.json, write
m{4,5,6}_centre_sextic_survivors.json and exclusion certificates.
No floating-point computation, off-centre triples, or external CAS is used.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path
import sympy as S
from sympy.matrices.normalforms import smith_normal_decomp
from centre_distinct import reason as distinct_reason

HERE = Path(__file__).resolve().parent
H = [(1, 0), (0, 1), (1, 1), (1, -1)]
x = S.symbols('x')


def rows_of(cfg):
    return [tuple(c[j + 1] for c in cfg) for j in range(4)]


def degree(row):
    assert sum(row) == 0
    return sum(max(t, 0) for t in row)


def monomial_divisor(v, rows):
    return [sum(v[j] * rows[j][p] for j in range(4))
            for p in range(len(rows[0]))]


def all_forced(cfg):
    """(i,j,sign) -> (point, minimum fibre multiplicity, value squared).

    The monomial is phi_i * phi_j**sign; its coefficient at i is +1.
    Fractions are exact. Duplicate consequences at the same point agree.
    """
    out = defaultdict(dict)
    for i, j in combinations(range(4), 2):
        for p, col in enumerate(cfg):
            e = col[1:]
            M = abs(e[i])
            if not M or abs(e[j]) != M:
                continue
            for c in sorted(set(range(4)) - {i, j}):
                if abs(e[c]) >= M:
                    continue
                # On h_c=0 use (U,V) perpendicular to its coefficient vector.
                u, v = H[c][1], -H[c][0]
                ai = H[i][0] * u + H[i][1] * v
                aj = H[j][0] * u + H[j][1] * v
                assert ai and aj
                value = Fraction(aj, ai) ** (1 if e[i] > 0 else -1)
                sign = -1 if e[i] == e[j] else 1
                item = (p, 2 * (M - abs(e[c])), value)
                old = out[i, j, sign].get(p)
                assert old is None or old == item
                out[i, j, sign][p] = item
    return {k: list(v.values()) for k, v in out.items()}


def forced_value(v, p, forced):
    for (i, j, sign), lst in forced.items():
        u = [0] * 4
        u[i], u[j] = 1, sign
        for q, r, value in lst:
            if q != p:
                continue
            z = S.Rational(value.numerator, value.denominator)
            if list(v) == u:
                return z
            if list(v) == [-a for a in u]:
                return 1 / z
    return None


def forced_coincidence(full_rows):
    """Return an explicit INTEGER relation forcing P_j=P_k, if found.

    D=U*M*V is Smith decomposition; no search in elliptic torsion is needed.
    Every returned coefficient list is independently checked by multiplication.
    """
    n = len(full_rows[0])
    M = S.Matrix([r[1:] for r in full_rows])
    D, U, V = smith_normal_decomp(M, domain=S.ZZ)
    rank = sum(D[j, j] != 0 for j in range(min(D.shape)))
    for j, k in combinations(range(n), 2):
        target = [int(p == j) - int(p == k) for p in range(n)]
        z = S.Matrix([target[1:]]) * V
        if any(z[l] for l in range(rank, n - 1)):
            continue
        if any(z[l] % D[l, l] for l in range(rank)):
            continue
        a = S.zeros(1, M.rows)
        for l in range(rank):
            a[l] = z[l] / D[l, l]
        coeffs = [int(t) for t in a * U]
        assert all(t.q == 1 for t in a * U)
        assert [sum(c * r[p] for c, r in zip(coeffs, full_rows))
                for p in range(n)] == target
        return dict(points=[j, k], coefficients=coeffs,
                    relation_rows=full_rows)
    return None


def ramification_filter(cfg):
    rows = rows_of(cfg)
    forced = all_forced(cfg)
    extra = []
    for (i, j, sign), lst in forced.items():
        div = [a + sign * b for a, b in zip(rows[i], rows[j])]
        delta = degree(div)
        if delta == 0:
            if len({z for p, r, z in lst}) > 1:
                return 'constant forced values', dict(monomial=[i, j, sign]), []
            continue
        if any(r > delta for p, r, z in lst):
            return 'fibre multiplicity', dict(monomial=[i, j, sign],
                                               divisor=div), []
        ram = sum(abs(t) - 1 for t in div if t) + sum(r - 1 for p, r, z in lst)
        if ram > 2 * delta:
            return 'all-pair RH', dict(monomial=[i, j, sign], divisor=div,
                                      ramification=ram, bound=2 * delta), []
        for z in {z for p, r, z in lst}:
            if sum(r for p, r, zz in lst if zz == z) > 2 * delta:
                return 'two fibres', dict(monomial=[i, j, sign]), []
        for p, r, z in lst:
            if r == delta:
                relation = [max(t, 0) for t in div]
                relation[p] -= delta
                assert sum(relation) == 0
                extra.append(relation)
    full_rows = [list(r) for r in rows] + extra
    coincidence = forced_coincidence(full_rows)
    if coincidence:
        return 'forced coincidence', coincidence, extra
    return None, None, extra


def square_obstruction(R):
    """An exact odd-multiplicity factor certificate; constants are squares over C."""
    n, d = S.fraction(S.cancel(R))
    for where, pol in [('numerator', n), ('denominator', d)]:
        for factor, multiplicity in S.factor_list(pol, x)[1]:
            if multiplicity % 2:
                assert S.gcd(factor, S.diff(factor, x)) == 1
                return dict(where=where, factor=str(factor),
                            multiplicity=multiplicity)
    return None


def pencil_filter(cfg):
    rows, forced = rows_of(cfg), all_forced(cfg)
    for C in range(4):
        if degree(rows[C]) != 3:
            continue
        for A, B in combinations(sorted(set(range(4)) - {C}), 2):
            for sc, sa, sb in product([-1, 1], repeat=3):
                v, z = [0] * 4, [0] * 4
                v[A], v[C] = sa, -sc
                z[B], z[C] = sb, -sc
                d, e = monomial_divisor(v, rows), monomial_divisor(z, rows)
                if sorted(t for t in d if t) != [-2, 2]:
                    continue
                if sorted(t for t in e if t) != [-2, 2]:
                    continue
                pole, p, q = d.index(-2), d.index(2), e.index(2)
                if pole != e.index(-2) or p == q:
                    continue
                F = forced_value(v, q, forced)
                G = forced_value(z, p, forced)
                value_certificate = dict(F_direct=str(F), G_direct=str(G))
                if F is None or G is None:
                    for t in range(len(cfg)):
                        if t in [pole, p, q]:
                            continue
                        ft = forced_value(v, t, forced)
                        gt = forced_value(z, t, forced)
                        if ft is None or gt is None:
                            continue
                        if F is None and G is not None and gt == G:
                            F = ft / 4
                            value_certificate['F_recovered_at'] = t
                        if G is None and F is not None and ft == F:
                            G = gt / 4
                            value_certificate['G_recovered_at'] = t
                if F is None or G is None:
                    continue
                det = lambda i, j: H[i][0] * H[j][1] - H[i][1] * H[j][0]
                a, b, c = det(B, C), det(C, A), det(A, B)
                denominator = a * F * x**2 + b * G * (x - 1)**2 + c
                if S.expand(denominator) == 0:
                    continue
                R = S.factor(-(a / (F*x**2) + b / (G*(x-1)**2) + c)
                             / denominator)
                odd = square_obstruction(R)
                if odd:
                    return dict(A=A, B=B, C=C, signs=[sa, sb, sc],
                                f_exponents=v, g_exponents=z,
                                pole=pole, fzero=p, gzero=q,
                                F=str(F), G=str(G), coefficients=[a, b, c],
                                R=str(R), odd_factor=odd,
                                values=value_certificate)
    return None


def three_affines_filter(cfg):
    """Lemma 4: use phi_1 (index zero) as the base function."""
    rows = rows_of(cfg)
    if any(degree(r) != 3 for r in rows):
        return None
    for signs in product([-1, 1], repeat=4):
        ds = []
        for j in range(1, 4):
            ds.append([signs[j] * b - signs[0] * a
                       for a, b in zip(rows[0], rows[j])])
        if not all(sorted(t for t in d if t) == [-2, 2] for d in ds):
            continue
        poles = [d.index(-2) for d in ds]
        zeros = [d.index(2) for d in ds]
        if len(set(poles)) == 1 and len(set(zeros)) == 3:
            return dict(signs=signs, pole=poles[0], zeros=zeros, divisors=ds)
    return None


def monomial_filter(cfg):
    """Lemma 5: psi1*psi4=c*psi2*psi3, with degree-two f,g,t."""
    rows = rows_of(cfg)
    for signs in product([-1, 1], repeat=4):
        s0, s1, s2, s3 = signs
        relation = [s0, -s1, -s2, s3]
        if any(monomial_divisor(relation, rows)):
            continue
        vs = [[s0, -s1, 0, 0], [s0, 0, -s2, 0], [s0, 0, 0, s3]]
        if all(degree(monomial_divisor(v, rows)) == 2 for v in vs):
            return dict(signs=signs, relation=relation,
                        f_g_t_divisors=[monomial_divisor(v, rows) for v in vs])
    return None


def exclude(cfg):
    old = distinct_reason(cfg)
    if old != 'survives':
        return old, {}
    why, cert, extra = ramification_filter(cfg)
    if why:
        return why, cert
    cert = pencil_filter(cfg)
    if cert:
        return 'degree-two pencil square obstruction', cert
    cert = three_affines_filter(cfg)
    if cert:
        return 'three affine functions', cert
    cert = monomial_filter(cfg)
    if cert:
        return 'four-function monomial relation', cert
    return 'survives', {}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('degrees', nargs='*', type=int, default=[4, 5, 6])
    parser.add_argument('--source', default='distinct_survivors',
                        help='input suffix, e.g. configs or survivors')
    parser.add_argument('--tag', default='centre_sextic')
    args = parser.parse_args()
    for m in args.degrees:
        data = json.loads((HERE / f'm{m}_{args.source}.json').read_text())
        counts, survivors, certificates = Counter(), [], []
        for index, item in enumerate(data):
            why, cert = exclude(item['cfg'])
            counts[why] += 1
            if why == 'survives':
                survivors.append(item)
            else:
                certificates.append(dict(index=index, reason=why, certificate=cert))
        (HERE / f'm{m}_{args.tag}_survivors.json').write_text(
            json.dumps(survivors, indent=2) + '\n')
        (HERE / f'm{m}_{args.tag}_certificates.json').write_text(
            json.dumps(dict(source=f'm{m}_{args.source}.json',
                            counts=dict(counts), exclusions=certificates), indent=2) + '\n')
        print(f'm={m}: input={len(data)}; {dict(counts)}; output={len(survivors)}')


if __name__ == '__main__':
    main()
