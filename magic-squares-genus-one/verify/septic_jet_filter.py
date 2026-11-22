"""A certified order-three propagation filter. See SEPTIC_JETS.md.

Only simple centre divisors are processed. No numerical or modular exclusions.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import hashlib
import json
import sys

from centre_septic import PrincipalLattice
from centre_sextic import forced_coincidence

HERE = Path(__file__).resolve().parent
H = ((1, 0), (0, 1), (1, 1), (1, -1))


def pair_data(cfg):
    rows = [[c[i+1] for c in cfg] for i in range(4)]
    data = []
    for i, j in combinations(range(4), 2):
        for s in (-1, 1):
            v = [int(k == i) + s*int(k == j) for k in range(4)]
            d = [sum(v[k]*r[p] for k, r in enumerate(rows))
                 for p in range(len(cfg))]
            forced = {}
            for p, col in enumerate(cfg):
                e = col[1:]
                if 0 not in e or not e[i] or not e[j] or e[i]+s*e[j]:
                    continue
                c = e.index(0)
                x, y = H[c][1], -H[c][0]
                a = H[i][0]*x + H[i][1]*y
                b = H[j][0]*x + H[j][1]*y
                z = Fraction(b, a)**e[i]
                forced[p] = str(z)
            data.append(dict(v=v, d=d, degree=sum(max(t, 0) for t in d),
                             forced=forced))
    return rows, data


def fibre_row(d, p, degree):
    return [max(t, 0)-degree*int(q == p) for q, t in enumerate(d)]


def exclude(cfg):
    if not all(c[0] == 1 and c[1:].count(0) <= 1 for c in cfg):
        return None, 'outside simple scope'
    rows, data = pair_data(cfg)
    initial = list(rows)
    full = []
    for f in data:
        if f['degree'] == 2:
            for p in f['forced']:
                r = fibre_row(f['d'], p, 2)
                if r not in initial:
                    initial.append(r)
                    full.append(dict(v=f['v'], point=p))
    lattice = PrincipalLattice(initial)
    for f in data:
        if f['degree'] != 3:
            continue
        for p in f['forced']:
            target = fibre_row(f['d'], p, 3)
            coeff = lattice.certificate(target)
            if coeff is None:
                continue
            # The residual-fibre lemma upgrades this seed to order three.
            # The local jet lemma then upgrades every unit pair at p.
            added, monomials = [], []
            for g in data:
                if p not in g['forced']:
                    continue
                if g['degree'] < 3:
                    return dict(point=p, seed=f['v'], full_fibres=full,
                                seed_coefficients=coeff,
                                contradiction='multiplicity', short=g['v']), 'excluded'
                if g['degree'] == 3:
                    r = fibre_row(g['d'], p, 3)
                    if r not in initial and r not in added:
                        added.append(r)
                        monomials.append(g['v'])
            collision = forced_coincidence(initial + added)
            if collision is not None:
                return dict(point=p, seed=f['v'], full_fibres=full,
                            seed_coefficients=coeff, added_monomials=monomials,
                            contradiction='coincidence',
                            points=collision['points'],
                            collision_coefficients=collision['coefficients']), 'excluded'
    return None, 'survives'


def main():
    sources = sys.argv[1:] or ['m7_open134.json']
    for name in sources:
        src = HERE / name
        items = json.loads(src.read_text())
        counts, certs, survivors = Counter(), [], []
        for index, item in enumerate(items):
            cert, reason = exclude(item['cfg'])
            counts[reason] += 1
            if cert is None:
                survivors.append(item)
            else:
                certs.append(dict(index=index, **cert))
        stem = src.stem + '_jets'
        payload = dict(source=name, sha256=hashlib.sha256(src.read_bytes()).hexdigest(),
                       counts=dict(counts), exclusions=certs)
        (HERE / (stem+'_certificates.json')).write_text(json.dumps(payload, indent=2)+'\n')
        (HERE / (stem+'_survivors.json')).write_text(json.dumps(survivors, indent=2)+'\n')
        print(f'{name}: input={len(items)}; {dict(counts)}; remaining={len(survivors)}')
        print('  excluded indices:', [c['index'] for c in certs])


if __name__ == '__main__':
    main()
