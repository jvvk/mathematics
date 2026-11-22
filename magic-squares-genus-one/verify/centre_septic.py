"""Proved residual-fibre, two-fibre packing, and tame-reciprocity filters.

Proof and scope: CENTRE_SEPTICS.md. All arithmetic is exact.
Default reads m7_survivors.json, writes m7_fibre_reciprocity_survivors.json
and m7_fibre_reciprocity_certificates.json. Does not claim to finish degree 7.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path
import sympy as S
from sympy.matrices.normalforms import smith_normal_decomp
from audit_sextic import rows_of, mono_div, deg, forced, kappa

HERE = Path(__file__).resolve().parent
PAIRS = list(combinations(range(4), 2))


def pair_data(cfg):
    rows = rows_of(cfg)
    out = []
    for i, j in PAIRS:
        for sign in (-1, 1):
            u = [int(k == i) + sign * int(k == j) for k in range(4)]
            d = mono_div(u, rows)
            out.append((u, d, forced(u, cfg)))
    return out


def relation_rows(cfg, data):
    rows = rows_of(cfg)
    extra = []
    for u, d, fv in data:
        delta = deg(d)
        for p, (_, r) in fv.items():
            if delta > 0 and r == delta:
                rel = [max(a, 0) for a in d]
                rel[p] -= delta
                if rel not in rows and rel not in extra:
                    extra.append(rel)
    return rows + extra


class PrincipalLattice:
    """Integer membership with an independently checkable multiplication certificate."""
    def __init__(self, rows):
        self.rows = rows
        M = S.Matrix([r[1:] for r in rows])
        self.D, self.U, self.V = smith_normal_decomp(M, domain=S.ZZ)
        self.rank = sum(self.D[k, k] != 0 for k in range(min(self.D.shape)))

    def certificate(self, target):
        z = S.Matrix([target[1:]]) * self.V
        if any(z[k] for k in range(self.rank, len(target) - 1)):
            return None
        if any(z[k] % self.D[k, k] for k in range(self.rank)):
            return None
        a = S.zeros(1, len(self.rows))
        for k in range(self.rank):
            a[k] = z[k] / self.D[k, k]
        coeffs = [int(v) for v in a * self.U]
        assert [sum(c * r[p] for c, r in zip(coeffs, self.rows))
                for p in range(len(target))] == target
        return coeffs


def residual_filter(cfg, data):
    R = relation_rows(cfg, data)
    L = PrincipalLattice(R)
    for u, d, fv in data:
        if deg(d) != 3:
            continue
        for p, (z, r) in fv.items():
            if r < 2:
                continue
            for q in range(len(cfg)):
                bad = ("zero or pole" if d[q] else
                       "another ramification point" if q != p and q in fv and fv[q][1] >= 2
                       else None)
                if bad is None:
                    continue
                target = [max(a, 0) for a in d]
                target[p] -= 2
                target[q] -= 1
                coeffs = L.certificate(target)
                if coeffs is not None:
                    return dict(monomial=u, divisor=d, double_point=p,
                                residual_point=q, contradiction=bad,
                                relation_rows=R, coefficients=coeffs,
                                target=target)
    return None


def can_pack_two(weights, capacity):
    total = sum(weights)
    return any(total - capacity <= sum(weights[k] for k in range(len(weights)) if mask >> k & 1) <= capacity
               for mask in range(1 << len(weights)))


def packing_filter(cfg, data):
    for u, d, fv in data:
        delta = deg(d)
        if delta == 0:
            continue
        groups = defaultdict(list)
        for p, (z, r) in fv.items():
            groups[z].append((p, r))
        for z, points in groups.items():
            if not can_pack_two([r for p, r in points], delta):
                return dict(monomial=u, divisor=d, degree=delta,
                            value_squared=str(z), points=points)
    return None


def reciprocity_filter(cfg):
    constraints, local = [], []
    for col in cfg:
        mu, e = col[0], col[1:]
        W = S.Matrix([[int(k == i) * e[j] - int(k == j) * e[i]
                       for i, j in PAIRS] for k in range(4)])
        low = [k for k in range(4) if abs(e[k]) < mu]
        assert len(low) <= 1
        constraints += [list(W.row(k)) for k in (low if low else range(4))]
        local.append((e, W, kappa(e, mu)))
    M = S.Matrix(constraints)
    D, U, V = smith_normal_decomp(M, domain=S.ZZ)
    rank = sum(D[k, k] != 0 for k in range(min(D.shape)))
    # Columns of this unimodular V form a saturated integer kernel basis.
    for b in range(rank, 6):
        t = V.col(b)
        assert M * t == S.zeros(M.rows, 1)
        total = Fraction(1)
        locals_ = []
        for e, W, kc in local:
            w = [int(v) for v in W * t]
            value = Fraction(1)
            if kc is None:
                assert not any(w)
            else:
                kap, c = kc
                assert w[c] == 0
                assert sum((1 if e[k] > 0 else -1) * w[k]
                           for k in range(4) if k != c) == 0
                for k in range(4):
                    if k != c:
                        s = 1 if e[k] > 0 else -1
                        value *= kap[k] ** (-s * w[k])
            total *= value
            locals_.append(dict(exponents=w, factor=str(value)))
        if total != 1:
            return dict(pair_order=PAIRS, skew_coefficients=[int(a) for a in t],
                        local=locals_, product=str(total))
    return None


def exclude(cfg):
    data = pair_data(cfg)
    cert = residual_filter(cfg, data)
    if cert is not None:
        return 'residual fibre', cert
    cert = packing_filter(cfg, data)
    if cert is not None:
        return 'two-fibre packing', cert
    cert = reciprocity_filter(cfg)
    if cert is not None:
        return 'tame reciprocity', cert
    return 'survives', {}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('degrees', nargs='*', type=int, default=[7])
    parser.add_argument('--source', default='survivors')
    parser.add_argument('--tag', default='fibre_reciprocity')
    args = parser.parse_args()
    for m in args.degrees:
        src = HERE / f'm{m}_{args.source}.json'
        items = json.loads(src.read_text())
        counts, out, certs = Counter(), [], []
        for index, item in enumerate(items):
            reason, certificate = exclude(item['cfg'])
            counts[reason] += 1
            if reason == 'survives':
                out.append(item)
            else:
                certs.append(dict(index=index, reason=reason, certificate=certificate))
        (HERE / f'm{m}_{args.tag}_survivors.json').write_text(json.dumps(out, indent=2) + '\n')
        import hashlib
        payload = dict(source=src.name, source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),
                       counts=dict(counts), exclusions=certs)
        (HERE / f'm{m}_{args.tag}_certificates.json').write_text(json.dumps(payload, indent=2) + '\n')
        print(f'm={m}: input={len(items)}; {dict(counts)}; output={len(out)}')


if __name__ == '__main__':
    main()
