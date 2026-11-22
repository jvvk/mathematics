"""Exact residue obstruction for simple centre divisors with at most one full column.

Default: m7_offcentre_targets.json -> m7_residue_survivors.json, plus certificates.
Proof, scope and explicit conventions: OFFCENTRE_RESIDUES.md.
No floating point, modular exclusion, or inference of existence from survival.
"""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import combinations_with_replacement, product
import hashlib
import json
from pathlib import Path
import sympy as S
from sympy.polys.matrices import DomainMatrix
from sympy.polys.matrices.ddm import DDM

HERE = Path(__file__).resolve().parent
F = S.QQ.algebraic_field(S.I, S.sqrt(2))
assert S.expand(F.ext.as_expr() - S.sqrt(2) - S.I) == 0
ZERO, ONE = F.zero, F.one
II, SQRT2 = F.from_sympy(S.I), F.from_sympy(S.sqrt(2))
ROOT = {0: ZERO, 1: ONE, -1: II, 2: SQRT2, -2: II * SQRT2}
H = [(1, 0), (0, 1), (1, 1), (1, -1)]
FORMS = [(-1, -1, 1, 0), (-1, 1, 0, 1)]


def encode(v):
    """Four rational coefficients in the basis 1,i,sqrt(2),i*sqrt(2)."""
    co = [S.Rational(c) for c in v.to_list()]
    c0, c1, c2, c3 = (list(reversed(co)) + [S.Rational(0)] * 4)[:4]
    return [str(a) for a in (c0 + c2, c1 + 5*c3, c1 - c3, 2*c2)]


def geometry(cfg):
    low = [p for p, c in enumerate(cfg) if 0 in c[1:]]
    full = [p for p in range(len(cfg)) if p not in low]
    roots, active = [], []
    for p in low:
        c = cfg[p][1:].index(0)
        a, b = H[c]
        kap = [-h*b + k*a for h, k in H]
        roots.append([ROOT[v] for v in kap])
        active.append([i for i in range(4) if i != c])
    return low, full, roots, active


def sign_branches(active):
    """Representatives; global row signs and individual column scales are immaterial.

    The checker independently verifies that their row-sign orbits cover ALL 4^l
    locally normalized sign patterns, rather than relying on this reduction.
    """
    seen = set()
    options = []
    for inds in active:
        masks = []
        for m in range(4):
            ss = [1, 1-2*(m & 1), 1-2*((m >> 1) & 1)]
            if all(ss[j] == 1 for j, i in enumerate(inds) if i not in seen):
                masks.append(m)
        options.append(masks)
        seen.update(inds)
    for ms in product(*options):
        yield sum(m << (2*j) for j, m in enumerate(ms))


def linear_system(cfg, low, full, roots, active, mask):
    vec = []
    for j, (rs, inds) in enumerate(zip(roots, active)):
        m = (mask >> (2*j)) & 3
        ss = [1, 1-2*(m & 1), 1-2*((m >> 1) & 1)]
        v = rs[:]
        for k, i in enumerate(inds):
            v[i] *= ss[k]
        vec.append(v)
    if not full:
        A = [[ZERO for _ in low] for _ in range(8)]
        for j, p in enumerate(low):
            for i in active[j]:
                A[2*i + int(cfg[p][i+1] > 0)][j] = vec[j][i]
        return A, []
    assert len(full) == 1
    f = full[0]
    A = [[ZERO for _ in low] for _ in range(4)]
    B = [[ZERO for _ in low] for _ in range(4)]
    for j, p in enumerate(low):
        for i in active[j]:
            if cfg[p][i+1] == cfg[f][i+1]:
                B[i][j] = -vec[j][i]
            else:
                A[i][j] = vec[j][i]
    # Ax=0; the four full-column entries are Bx.
    return A, B


def kernel(A):
    D = DomainMatrix.from_rep(DDM(A, (len(A), len(A[0])), F))
    rref, piv = D.rref()
    a = rref.to_list()
    free = [j for j in range(len(A[0])) if j not in piv]
    ans = []
    for j in free:
        v = [ZERO] * len(A[0]); v[j] = ONE
        for k, p in enumerate(piv):
            v[p] = -a[k][j]
        ans.append(v)
    return ans


def quadratic(weights, columns):
    x, y = columns
    return [sum((w*a*a for w, a in zip(weights, x)), ZERO),
            sum((2*w*a*b for w, a, b in zip(weights, x, y)), ZERO),
            sum((w*b*b for w, b in zip(weights, y)), ZERO)]


def resultant(q, r):
    a, b, c = q; d, e, f = r
    return (a*f-c*d)**2 - (a*e-b*d)*(b*f-c*e)


def product_witness(q, r, cov):
    """Find an exact identity lambda*q+mu*r=L_i*L_j."""
    dets = [(j, k, q[j]*r[k]-q[k]*r[j])
            for j, k in ((0, 1), (0, 2), (1, 2))]
    pivot = next(((j, k, d) for j, k, d in dets if d), None)
    for i, j in combinations_with_replacement(range(len(cov)), 2):
        a, b = cov[i]; c, d = cov[j]
        pol = [a*c, a*d+b*c, b*d]
        if pivot:
            h, k, den = pivot
            lam = (pol[h]*r[k]-pol[k]*r[h]) / den
            mu = (q[h]*pol[k]-q[k]*pol[h]) / den
        elif any(q):
            h = next(k for k in range(3) if q[k])
            lam, mu = pol[h]/q[h], ZERO
        elif any(r):
            h = next(k for k in range(3) if r[k])
            lam, mu = ZERO, pol[h]/r[h]
        else:
            return None
        if all(lam*q[k]+mu*r[k] == pol[k] for k in range(3)):
            return dict(kind='coordinate product', coordinates=[i, j],
                        multipliers=[encode(lam), encode(mu)])
    return None


def branch_certificate(A, B):
    K = kernel(A)
    if not K:
        return dict(kind='zero kernel')
    cov = [tuple(v[j] for v in K) for j in range(len(A[0]))]
    cov += [tuple(sum((b*a for b, a in zip(row, v)), ZERO) for v in K)
            for row in B]
    for j, v in enumerate(cov):
        if not any(v):
            return dict(kind='zero coordinate', coordinate=j)
    if not B or len(K) > 2:
        return None
    if len(K) == 1:
        values = [sum((w*cov[len(A[0])+j][0]**2 for j, w in enumerate(ws)), ZERO)
                  for ws in FORMS]
        for j, v in enumerate(values):
            if v:
                return dict(kind='nonzero unary quadratic', form=j, coefficient=encode(v))
        return None
    fullcols = [[cov[len(A[0])+j][k] for j in range(4)] for k in range(2)]
    q, r = [quadratic(ws, fullcols) for ws in FORMS]
    res = resultant(q, r)
    if res:
        return dict(kind='nonzero binary resultant', value=encode(res))
    return product_witness(q, r, cov)


def exclude(cfg):
    if any(c[0] != 1 for c in cfg):
        return None, 'non-simple centre divisor'
    if any(sum(v == 0 for v in c[1:]) > 1 or any(v not in (-1, 0, 1) for v in c[1:])
           for c in cfg):
        return None, 'outside local hypotheses'
    low, full, roots, active = geometry(cfg)
    if len(full) > 1:
        return None, 'more than one full column'
    if not low:
        return None, 'no low column'
    branches = []
    for mask in sign_branches(active):
        A, B = linear_system(cfg, low, full, roots, active, mask)
        cert = branch_certificate(A, B)
        if cert is None:
            return None, 'residue system retained'
        branches.append(dict(mask=mask, **cert))
    return dict(low_points=low, full_points=full, branches=branches), 'residue obstruction'


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('degrees', type=int, nargs='*', default=[7])
    ap.add_argument('--source', default=None)
    ap.add_argument('--tag', default='residue')
    args = ap.parse_args()
    for m in args.degrees:
        src = HERE / f'm{m}_{args.source or ("offcentre_targets" if m == 7 else "configs")}.json'
        items = json.loads(src.read_text())
        counts, detail, survivors, certs = Counter(), Counter(), [], []
        for index, item in enumerate(items):
            cert, why = exclude(item['cfg'])
            detail[why] += 1
            if cert is None:
                counts['survives'] += 1; survivors.append(item)
            else:
                counts['residue obstruction'] += 1
                certs.append(dict(index=index, reason=why, certificate=cert))
        payload = dict(source=src.name, source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),
                       field='Q(i,sqrt(2)); basis=(1,i,sqrt(2),i*sqrt(2))',
                       counts=dict(counts), detail=dict(detail), exclusions=certs)
        (HERE / f'm{m}_{args.tag}_survivors.json').write_text(json.dumps(survivors, indent=2)+'\n')
        (HERE / f'm{m}_{args.tag}_certificates.json').write_text(json.dumps(payload, indent=2)+'\n')
        kinds = Counter(b['kind'] for e in certs for b in e['certificate']['branches'])
        print(f'm={m}: input={len(items)}; {dict(counts)}; output={len(survivors)}', flush=True)
        print(f'  detail={dict(detail)}; branch certificates={dict(kinds)}', flush=True)


if __name__ == '__main__':
    main()
