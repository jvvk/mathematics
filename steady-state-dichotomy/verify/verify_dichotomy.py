#!/usr/bin/env python3
"""Exact evidence checks for the determinant-dichotomy manuscript.

Run: python3 verify_dichotomy.py [--output evidence.json]
Requires SymPy and the sibling certify_exact.py. No floating-point decisions.
This verifies examples and the algebra/barrier inequalities used in the proof;
it is not a formal proof checker for Brouwer degree or the general theorem.
"""
import argparse
import hashlib
import json
from pathlib import Path

import sympy as s
from certify_exact import X, Y, Z, MONOMIALS, read_system, certify

HERE = Path(__file__).resolve().parent
VARS = (X, Y, Z)


def need(condition, message):
    if not condition:
        raise ValueError(message)


def barrier_certificate(rows, v=None):
    rows = [[s.Rational(c) for c in row] for row in rows]
    F, _ = read_system({'rows': rows})
    B = s.Matrix(rows)[:, [6, 5, 4]]
    delta = B.det()
    need(delta != 0, 'Singular quadratic matrix')
    strict = all(c != 0 for row in rows for c in row)
    if delta > 0:
        v = B.inv() * s.ones(3, 1)
        direction = 'outward'
    else:
        need(strict, 'Inward certificate requires the strict class here')
        v = s.ones(3, 1) if v is None else s.Matrix(v)
        direction = 'inward'
    need(all(c > 0 for c in v), 'Need a strictly positive rational vector')
    Bv = B * v
    need(all(c > 0 for c in Bv) if delta > 0 else all(c < 0 for c in Bv),
         'Candidate vector does not certify the matrix inequality')
    w = [1/c for c in v]
    Q = [sum(row[k]*MONOMIALS[k] for k in [4, 5, 6]) for row in rows]
    reciprocal = X*Y*Z*B*s.Matrix([1/X, 1/Y, 1/Z])
    need(all(s.expand(q-r) == 0 for q, r in zip(Q, reciprocal)), 'Reciprocal identity')
    Qw = [s.expand(q).subs(dict(zip(VARS, w))) for q in Q]
    ai = [s.Poly(f, *VARS).coeff_monomial(1) for f in F]
    bi = [-s.Poly(f, *VARS).coeff_monomial(VARS[i]) for i, f in enumerate(F)]
    details = {'detB': str(delta), 'B': [[str(c) for c in B.row(i)] for i in range(3)],
               'direction': direction, 'v': list(map(str, v)), 'Bv': list(map(str, Bv)),
               'w': list(map(str, w)), 'Qw': list(map(str, Qw))}
    if delta > 0:
        gamma = min(Qw[i]/w[i] for i in range(3))
        need(gamma > 0, 'Outward speed')
        for i, f in enumerate(F):
            j, k = [t for t in range(3) if t != i]
            p = s.Poly(f, *VARS)
            U = -p.coeff_monomial(VARS[i]*VARS[j])*w[i]*w[j]
            V = -p.coeff_monomial(VARS[i]*VARS[k])*w[i]*w[k]
            W = p.coeff_monomial(VARS[j]*VARS[k])*w[j]*w[k]
            need(W > U+V and U >= 0 and V >= 0, 'Upper-orthant face monotonicity')
        threshold = 2*max(bi)/gamma
        details.update({'gamma': str(gamma), 'r_threshold_strict': str(threshold),
                        'escape_time_bound': '2/(gamma*r_initial)'})
    else:
        deltas, linear_thresholds = [], []
        for i, f in enumerate(F):
            j, k = [t for t in range(3) if t != i]
            p = s.Poly(f, *VARS)
            U = -p.coeff_monomial(VARS[i]*VARS[j])*w[i]*w[j]
            V = -p.coeff_monomial(VARS[i]*VARS[k])*w[i]*w[k]
            W = p.coeff_monomial(VARS[j]*VARS[k])*w[j]*w[k]
            d = min(U, V, (U+V-W)/2)
            need(d > 0, 'Inward quadratic gap')
            for u in [0, 1]:
                for v0 in [0, 1]:
                    need(-U*u-V*v0+W*u*v0+d*(u+v0) <= 0, 'Bilinear corner inequality')
            deltas.append(d)
            linear_thresholds.append(max(p.coeff_monomial(VARS[j])*w[j],
                                         p.coeff_monomial(VARS[k])*w[k])/d)
        R1 = max(linear_thresholds)
        A0, b0 = max(ai[i]/w[i] for i in range(3)), min(bi)
        need(b0 > 0, 'Strict diagonal loss')
        R = s.ceiling(max(R1, 2*A0/b0))+1
        for i, f in enumerate(F):
            j, k = [t for t in range(3) if t != i]
            for u in [0, 1]:
                for v0 in [0, 1]:
                    value = f.subs({VARS[i]: R*w[i], VARS[j]: R*w[j]*u, VARS[k]: R*w[k]*v0})
                    need(value < 0, 'Inward face of the claimed absorbing box')
        details.update({'delta_i': list(map(str, deltas)), 'R1': str(R1), 'A0': str(A0),
                        'b0': str(b0), 'absorbing_box_scale': str(R),
                        'absorbing_box_upper': [str(R*wi) for wi in w]})
    return details


def seven_reaction_check():
    x, y, z = VARS
    rows = [[0, 0, 0, 1, -8, -1, 1], [1, 0, 0, 0, -8, 1, 0], [0, 3, 0, -1, 1, 0, 0]]
    F, _ = read_system({'rows': rows})
    xx, yy = (8*z-1)/(z+24), (z*z+3)/(8*z-1)
    P = z**4-96*z**3+218*z*z-145*z+24
    D = (z+24)*(8*z-1)
    need(s.factor(F[0].subs({x: xx, y: yy})-P/D) == 0, 'Quartic substitution')
    need(all(s.factor(f.subs({x: xx, y: yy})) == 0 for f in F[1:]), 'Other two substitutions')
    J = s.Matrix(F).jacobian(VARS)
    identity = J.det().subs({x: xx, y: yy})-s.diff(P,z)/(z+24)+P*s.diff(D,z)/((z+24)*D)
    need(s.factor(identity) == 0, 'Determinant identity modulo P')
    points = [s.Rational(1,8), s.Rational(1,2), s.Integer(1), s.Integer(2), s.Integer(96)]
    values = [P.subs(z,t) for t in points]
    need([s.sign(t) for t in values] == [1,-1,1,-1,1], 'Four simple positive roots')
    b = barrier_certificate(rows)
    need(b['v'] == ['18','9','1'] and b['gamma'] == '1/162' and b['r_threshold_strict'] == '324',
         'Explicit escape constants')
    exact = certify(F)
    need(exact['positive_states'] == 4 and exact['stable_positive_states'] == 2, 'Seven-reaction count and stability')
    for index, boxes in [(0, {'b1':(26,27), 'b2':(6,7), 'b3':(2,3), 'H2':(179,180)}),
                         (2, {'b1':(9,10), 'b2':(13,14), 'b3':(1,2), 'H2':(125,126)})]:
        for name, (lower, upper) in boxes.items():
            lo, hi = map(s.Rational, exact['real_roots'][index]['bounds'][name])
            need(lower < lo <= hi < upper, 'Stated rational Hurwitz enclosure')
    return {'polynomial': str(P), 'test_points': list(map(str, points)), 'values': list(map(str, values)),
            'barrier': b, 'exact_root_certificate': exact}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    evidence = {'seven_reaction': seven_reaction_check(), 'strict_examples': {}}
    for n, word in enumerate(['zero','one','two','three','four']):
        path = HERE/f'strict_{word}.json'
        raw = path.read_bytes()
        record = json.loads(raw, parse_float=s.Rational)
        equations, _ = read_system(record)
        exact = certify(equations)
        saved = json.loads((HERE/f'certificate_{word}.json').read_text())
        need(saved['source_sha256'] == hashlib.sha256(raw).hexdigest(), 'Input hash mismatch')
        need(all(saved[k] == value for k, value in exact.items()), 'Saved certificate differs from fresh calculation')
        need(exact['positive_states'] == exact['nondegenerate_positive_states'] == n, 'Root count')
        barrier = barrier_certificate(record['rows'])
        degree = sum(r['signs']['detJ'] for r in exact['real_roots'] if r['positive'])
        predicted_degree = 0 if s.Rational(barrier['detB']) > 0 else -1
        need(degree == predicted_degree, 'Degree sum')
        need(exact['stable_positive_states'] == (n-degree)//2, 'Stability count')
        evidence['strict_examples'][word] = {'positive_states': n,
            'stable_states': exact['stable_positive_states'], 'degree_sum': degree,
            'barrier': barrier, 'input_sha256': hashlib.sha256(raw).hexdigest()}
        print(f'PASS: {n} positive states, degree {degree}, {barrier["direction"]} barrier, detB={barrier["detB"]}')
    print('PASS: elementary seven-reaction proof; explicit escape region and time bound; all five exact root certificates')
    if args.output:
        args.output.write_text(json.dumps(evidence, indent=2)+'\n')


if __name__ == '__main__':
    main()
