"""Check jet-filter certificates without importing the filter or using Smith form."""
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import hashlib
import json
import sys
import sympy as S

HERE = Path(__file__).resolve().parent
H = ((1, 0), (0, 1), (1, 1), (1, -1))


def sum_rows(coeff, rows):
    assert len(coeff) == len(rows)
    assert all(type(t) is int for t in coeff)
    return [sum(a*r[p] for a, r in zip(coeff, rows))
            for p in range(len(rows[0]))]


def mono(cfg, v):
    assert len(v) == 4 and all(type(t) is int for t in v)
    nz = [i for i in range(4) if v[i]]
    assert len(nz) == 2 and all(abs(v[i]) == 1 for i in nz)
    i, j = nz
    assert v[i] == 1
    d = [sum(v[k]*col[k+1] for k in range(4)) for col in cfg]
    assert sum(d) == 0
    degree = sum(t for t in d if t > 0)
    return i, j, d, degree


def forced(cfg, v, p):
    i, j, d, degree = mono(cfg, v)
    e = cfg[p][1:]
    assert e.count(0) == 1
    c = e.index(0)
    assert i != c and j != c and d[p] == 0
    # Solve H_j = lambda H_i + mu H_c by determinants.
    det = lambda a, b: a[0]*b[1]-a[1]*b[0]
    lam = Fraction(det(H[j], H[c]), det(H[i], H[c]))
    mu = Fraction(det(H[i], H[j]), det(H[i], H[c]))
    assert lam and mu
    assert [lam*H[i][k]+mu*H[c][k] for k in range(2)] == list(H[j])
    return c


def row(d, p, degree):
    ans = [max(t, 0) for t in d]
    ans[p] -= degree
    return ans


def check_source(name):
    src = HERE / name
    items = json.loads(src.read_text())
    certfile = HERE / (src.stem+'_jets_certificates.json')
    payload = json.loads(certfile.read_text())
    assert payload['source'] == name
    assert payload['sha256'] == hashlib.sha256(src.read_bytes()).hexdigest()
    seen = set()
    for cert in payload['exclusions']:
        index = cert['index']
        assert index not in seen
        seen.add(index)
        cfg = items[index]['cfg']
        assert all(c[0] == 1 and c[1:].count(0) <= 1 for c in cfg)
        assert all(t in (-1, 0, 1) for c in cfg for t in c[1:])
        initial = [[c[k+1] for c in cfg] for k in range(4)]
        for full in cert['full_fibres']:
            v, p = full['v'], full['point']
            _, _, d, degree = mono(cfg, v)
            assert degree == 2
            forced(cfg, v, p)
            initial.append(row(d, p, 2))
        p, v = cert['point'], cert['seed']
        c = forced(cfg, v, p)
        _, _, d, degree = mono(cfg, v)
        assert degree == 3
        assert sum_rows(cert['seed_coefficients'], initial) == row(d, p, 3)
        if cert['contradiction'] == 'multiplicity':
            _, _, dd, delta = mono(cfg, cert['short'])
            assert forced(cfg, cert['short'], p) == c
            assert delta < 3
        else:
            assert cert['contradiction'] == 'coincidence'
            allrows = list(initial)
            for w in cert['added_monomials']:
                assert forced(cfg, w, p) == c
                _, _, dd, delta = mono(cfg, w)
                assert delta == 3
                allrows.append(row(dd, p, 3))
            a, b = cert['points']
            assert 0 <= a < len(cfg) and 0 <= b < len(cfg) and a != b
            assert sum_rows(cert['collision_coefficients'], allrows) == [
                int(q == a)-int(q == b) for q in range(len(cfg))]
    survivors = json.loads((HERE / (src.stem+'_jets_survivors.json')).read_text())
    assert survivors == [d for i, d in enumerate(items) if i not in seen]
    assert payload['counts'].get('excluded', 0) == len(seen)
    print(f'{name}: {len(seen)} exclusions independently checked; {len(survivors)} retained')


def local_controls():
    z = S.symbols('z')
    count = 0
    for c in range(4):
        b = next(i for i in range(4) if i != c)
        for k in (0, 1, 2):
            mat = S.Matrix([H[c], H[b]])
            uv = mat.inv()*S.Matrix([z**k, z**-2])
            hs = [(S.Matrix([h])*uv)[0] for h in H]
            dominant = {}
            for i in range(4):
                if i == c:
                    continue
                # Larger root of R^2-h_i R+1=0, through order four.
                dominant[i] = S.series(hs[i] - 1/hs[i], z, 0, 5).removeO()
            for i, j in combinations(dominant, 2):
                ratio = S.series(dominant[j]/dominant[i], z, 0, 5).removeO().expand()
                diff = (ratio-ratio.coeff(z, 0)).expand()
                assert diff.coeff(z, 1) == 0
                if k == 0:
                    assert diff.coeff(z, 2) != 0
                else:
                    assert diff.coeff(z, 2) == 0
                    if k == 1:
                        assert diff.coeff(z, 3) != 0
                    else:
                        assert diff.coeff(z, 3) == 0
                count += 1
    # E:y^2=x^3+1 is smooth, and y-1=x^3/(y+1) has a triple zero at (0,1).
    x, y = S.symbols('x y')
    assert S.expand((y-1)*(y+1)-x**3) == y**2-x**3-1
    print(f'controls: {count} local jet cases checked; elliptic triple-fibre identity checked')


if __name__ == '__main__':
    local_controls()
    for name in sys.argv[1:] or ['m7_open134.json', 'm4_configs.json',
                                'm5_configs.json', 'm6_configs.json']:
        check_source(name)
