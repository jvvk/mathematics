"""Independent multiplication/rank audit of offcentre_residue.py certificates.

Does not import the filter. Rebuilds local vectors, uses its own Gauss-Jordan
elimination, checks literal quadratic identities, and checks sign-orbit coverage.
"""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import product
import hashlib
import json
from pathlib import Path
import sympy as S

HERE = Path(__file__).resolve().parent
F = S.QQ.algebraic_field(S.I, S.sqrt(2))
Z, U = F.zero, F.one
I, T = F.from_sympy(S.I), F.from_sympy(S.sqrt(2))
BASIS = [U, I, T, I*T]
LOCAL = [[Z,U,U,I], [I,Z,I,I], [I,U,Z,I*T], [U,U,T,Z]]


def read_number(v):
    assert len(v) == 4
    return sum((F.convert(S.Rational(c))*b for c, b in zip(v, BASIS)), Z)


def nullspace(A):
    A = [r[:] for r in A]
    piv, k = [], 0
    for j in range(len(A[0])):
        p = next((p for p in range(k, len(A)) if A[p][j]), None)
        if p is None:
            continue
        A[k], A[p] = A[p], A[k]
        scale = A[k][j]
        A[k] = [a/scale for a in A[k]]
        for p in range(len(A)):
            if p == k or not A[p][j]:
                continue
            scale = A[p][j]
            A[p] = [a-scale*b for a, b in zip(A[p], A[k])]
        piv.append(j); k += 1
        if k == len(A):
            break
    K = []
    for j in range(len(A[0])):
        if j in piv:
            continue
        v = [Z] * len(A[0]); v[j] = U
        for p, c in enumerate(piv):
            v[c] = -A[p][j]
        K.append(v)
    return K


def det(A):
    A = [r[:] for r in A]; ans = U
    for j in range(len(A)):
        p = next((p for p in range(j, len(A)) if A[p][j]), None)
        if p is None:
            return Z
        if p != j:
            A[p], A[j] = A[j], A[p]; ans = -ans
        pivot = A[j][j]; ans *= pivot
        for p in range(j+1, len(A)):
            scale = A[p][j]/pivot
            for c in range(j+1, len(A)):
                A[p][c] -= scale*A[j][c]
    return ans


def reconstruct(cfg, low, full, mask):
    vectors = []
    active = []
    for k, p in enumerate(low):
        c = cfg[p][1:].index(0)
        inds = [i for i in range(4) if i != c]
        v = LOCAL[c][:]
        for j, i in enumerate(inds[1:]):
            if mask & (1 << (2*k+j)):
                v[i] = -v[i]
        active.append(inds); vectors.append(v)
    n = len(low)
    if full:
        f, = full
        A = [[Z]*n for _ in range(4)]
        B = [[Z]*n for _ in range(4)]
        for i in range(4):
            for k, p in enumerate(low):
                if cfg[p][i+1] == 0:
                    continue
                if cfg[p][i+1] == cfg[f][i+1]:
                    B[i][k] = -vectors[k][i]
                else:
                    A[i][k] = vectors[k][i]
    else:
        B = []
        A = [[Z]*n for _ in range(8)]
        for i in range(4):
            for k, p in enumerate(low):
                if cfg[p][i+1]:
                    A[2*i + int(cfg[p][i+1] == 1)][k] = vectors[k][i]
    K = nullspace(A)
    for v in K:
        assert all(sum((a*b for a,b in zip(row,v)),Z) == Z for row in A)
    cov = [tuple(v[j] for v in K) for j in range(n)]
    cov.extend(tuple(sum((a*b for a,b in zip(row,v)),Z) for v in K) for row in B)
    return K, cov


def check_branch(cfg, low, full, cert):
    K, cov = reconstruct(cfg, low, full, cert['mask'])
    kind = cert['kind']
    if kind == 'zero kernel':
        assert len(K) == 0
        return
    if kind == 'zero coordinate':
        assert not any(cov[cert['coordinate']])
        return
    assert full and len(K) in (1,2)
    forms = [(-1,-1,1,0), (-1,1,0,1)]
    n = len(low)
    if len(K) == 1:
        assert kind == 'nonzero unary quadratic'
        a = sum((w*cov[n+i][0]**2 for i,w in enumerate(forms[cert['form']])),Z)
        assert a and a == read_number(cert['coefficient'])
        return
    polys = []
    for ws in forms:
        xx = sum((w*cov[n+i][0]**2 for i,w in enumerate(ws)),Z)
        xy = sum((2*w*cov[n+i][0]*cov[n+i][1] for i,w in enumerate(ws)),Z)
        yy = sum((w*cov[n+i][1]**2 for i,w in enumerate(ws)),Z)
        polys.append([xx,xy,yy])
    q,r = polys
    if kind == 'nonzero binary resultant':
        a,b,c = q; d,e,f = r
        result = det([[a,b,c,Z],[Z,a,b,c],[d,e,f,Z],[Z,d,e,f]])
        assert result and result == read_number(cert['value'])
    else:
        assert kind == 'coordinate product'
        i,j = cert['coordinates']
        a,b = cov[i]; c,d = cov[j]
        assert (a or b) and (c or d)
        lam,mu = map(read_number,cert['multipliers'])
        assert [lam*v+mu*w for v,w in zip(q,r)] == [a*c,a*d+b*c,b*d]


def check_orbits(cfg, low, masks):
    assert len(masks) == len(set(masks))
    actions = set()
    for flips in product((0,1),repeat=4):
        mask = 0
        for k,p in enumerate(low):
            active = [i for i in range(4) if cfg[p][i+1]]
            for j,i in enumerate(active[1:]):
                mask |= (flips[i]^flips[active[0]]) << (2*k+j)
        actions.add(mask)
    covered = {m^a for m in masks for a in actions}
    assert covered == set(range(4**len(low)))


def elliptic_control():
    # E: y^2=x^3-x, omega=dx/(2y), M=y(x-2)(x-3), theta seven simple points.
    # The seven sections form the complete degree-seven space H^0(O(7O)).
    x,y = S.symbols('x y')
    sections = [S.Integer(1),x,y,x*x,x*y,x**3,x*x*y]
    sums = []
    for s in sections:
        ans = S.Integer(0)
        for r in (-1,0,1):
            ans += s.subs({x:r,y:0})/((3*r*r-1)*(r-2)*(r-3))
        for a,c in ((2,3),(3,2)):
            yy = S.sqrt(a**3-a)
            for sy in (yy,-yy):
                ans += s.subs({x:a,y:sy})/(2*(a**3-a)*(a-c))
        sums.append(S.simplify(ans))
    assert sums == [0]*7
    print('elliptic seven-pole positive control: residue sums',sums,flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('degrees',nargs='*',type=int,default=[7])
    ap.add_argument('--tag',default='residue')
    args = ap.parse_args()
    elliptic_control()
    for m in args.degrees:
        payload = json.loads((HERE/f'm{m}_{args.tag}_certificates.json').read_text())
        src = HERE/payload['source']
        assert hashlib.sha256(src.read_bytes()).hexdigest() == payload['source_sha256']
        items = json.loads(src.read_text())
        exclusions = payload['exclusions']; seen = set(); counts = Counter(); branches = 0
        for e in exclusions:
            index = e['index']; assert index not in seen; seen.add(index)
            cfg = items[index]['cfg']
            assert all(c[0] == 1 and all(v in (-1,0,1) for v in c[1:]) and c[1:].count(0)<=1 for c in cfg)
            low = [p for p,c in enumerate(cfg) if 0 in c[1:]]
            full = [p for p in range(len(cfg)) if p not in low]
            assert len(full)<=1 and low
            c = e['certificate']; assert c['low_points']==low and c['full_points']==full
            check_orbits(cfg,low,[b['mask'] for b in c['branches']])
            for b in c['branches']:
                check_branch(cfg,low,full,b); counts[b['kind']]+=1; branches+=1
        survivors = json.loads((HERE/f'm{m}_{args.tag}_survivors.json').read_text())
        assert survivors == [item for j,item in enumerate(items) if j not in seen]
        assert payload['counts'].get('residue obstruction',0)==len(seen)
        assert payload['counts'].get('survives',0)==len(survivors)
        print(f'm={m}: {len(exclusions)} exclusions, {branches} branch certificates, sign coverage verified; {len(survivors)} survivors',flush=True)
        print(' ',dict(counts),flush=True)


if __name__=='__main__':
    main()
