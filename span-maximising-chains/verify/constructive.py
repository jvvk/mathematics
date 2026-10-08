"""Construct exact strict-optimum witnesses for the recursive family.

This implements the realization theorem, not the unproved exclusion claim.
Only the standard library is used. The finite perturbation size is chosen
by exact certification, rather than by trusting floating-point tolerances.

Example: python3 constructive.py --n 7 --index 0 --output constructed.json
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from itertools import islice
import json
from math import lcm
from pathlib import Path

from certificate import certify
from solver import conjectured_patterns
from sweep import integer_directions, maximize_exact


@dataclass
class Witness:
    lengths: tuple
    tangents: tuple
    p: tuple
    q: tuple
    margin: F | None = None


def mul(z,w):
    return z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0]


def conj(z):
    return z[0],-z[1]


def rotation(t):
    return (1-t*t)/(1+t*t),2*t/(1+t*t)


def integer_input(lengths,tangents):
    scale = lcm(*(v.denominator for v in lengths))
    denominator = lcm(*(v.denominator for v in tangents)) if tangents else 1
    return [int(v*scale) for v in lengths],[int(v*denominator) for v in tangents],denominator,scale


def core_geometry(core):
    ls,ts,d,scale = integer_input(core.lengths,core.tangents)
    common,rs,ss = integer_directions(ts,d,core.q)
    w = (F(sum(ls[j]*r for j,r in zip(core.p,rs)),common*scale),
         F(sum(ls[j]*s for j,s in zip(core.p,ss)),common*scale))
    total_rotation = F(rs[-1],common),F(ss[-1],common)
    return w,total_rotation


def first_order_b(core,left,right,ratio,reverse=False):
    w,total = core_geometry(core)
    if reverse:
        w = mul(total,conj(w))
    v = mul(rotation(left),w)
    all_rotation = mul(mul(rotation(left),total),rotation(right))
    outside = 1+ratio*all_rotation[0],ratio*all_rotation[1]
    return v[0]*outside[0]+v[1]*outside[1]


def normalize_lengths(core):
    return Witness(tuple(x/core.lengths[-1] for x in core.lengths),
                   core.tangents,core.p,core.q)


def certify_perturbation(lengths,tangents,p,q,bound):
    if not 2*sum(tangents) < bound:
        raise ArithmeticError('Conservative total-turn bound failed.')
    ls,ts,d,scale = integer_input(lengths,tangents)
    _,fp,fq = maximize_exact(ls,ts,d)
    if (fp,fq) != (p,q):
        return None
    try:
        cp,cq,margin = certify(ls,ts,d)
    except ValueError:
        return None
    if (cp,cq) != (p,q):
        return None
    return Witness(tuple(lengths),tuple(tangents),p,q,margin/scale**2)


def realize(p,q,bound=F(1,2)):
    """Return an exact witness with total turn < bound (0 < bound <= 1/2).

    For each recursive operation, the existence of a sufficiently small
    perturbation is proved in paper.tex. The search here certifies a concrete
    perturbation. It is not a claim of a polynomial-time construction.
    """
    p,q = tuple(p),tuple(q)
    n = len(p)
    if not 0 < bound <= F(1,2):
        raise ValueError('Use a rational bound in (0,1/2].')
    if n == 1 and (p,q) == ((0,),()):
        return Witness((F(1),),(),p,q)
    if n == 2 and (p,q) == ((0,1),(0,)):
        return Witness((F(1),F(2)),(bound/8,),p,q)
    if n == 3 and (p,q) == ((0,2,1),(1,0)):
        lengths,tangents = (F(1),F(2),F(3)),(bound/20,bound/10)
        result = certify_perturbation(lengths,tangents,p,q,bound)
        if result is None:
            raise ArithmeticError('Base-case certificate failed.')
        return result
    if n < 4 or sorted(p) != list(range(n)) or sorted(q) != list(range(n-1)):
        raise ValueError('Pair is not in the defined recursive family.')
    mu = bound/8
    if q[0] == n-2:
        k = p[1]
        if not 2 <= k <= n-1:
            raise ValueError('Invalid type-A first rank.')
        r,m = k-1,n-k+1
        parent_p = tuple(v-r for v in reversed(p[1:m+1]))
        parent_q = tuple(reversed(q[1:m]))
        expected_p = (0,)+tuple(v+r for v in reversed(parent_p))+tuple(range(r-1,0,-1))
        expected_q = (n-2,)+tuple(reversed(parent_q))+tuple(range(m-1,n-2))
        if (p,q) != (expected_p,expected_q):
            raise ValueError('Pair fails the type-A recursion.')
        if r == 1:
            small_tangents = ()
            parent_bound = bound/8
        else:
            b = bound/(100*r**4)
            small_tangents = tuple(j*b for j in range(1,r))
            parent_bound = b/4
        core = normalize_lengths(realize(parent_p,parent_q,parent_bound))
        tangents = core.tangents+small_tangents+(mu,)
        weights = tuple(F(j+1) for j in range(r))
    elif q[0] == n-3 and q[-1] == n-2:
        parent_p = tuple(v-2 for v in p[1:-1])
        parent_q = q[1:-1]
        expected_p = (0,)+tuple(v+2 for v in parent_p)+(1,)
        expected_q = (n-3,)+parent_q+(n-2,)
        if (p,q) != (expected_p,expected_q):
            raise ValueError('Pair fails the type-B recursion.')
        core = normalize_lengths(realize(parent_p,parent_q,bound/8))
        factor = F(1,10)
        for _ in range(300):
            nu,ratio = mu*(1+factor),1+factor
            target = first_order_b(core,mu,nu,ratio)
            other = [first_order_b(core,mu,nu,ratio,True),
                     first_order_b(core,nu,mu,ratio),
                     first_order_b(core,nu,mu,ratio,True)]
            if all(target > x for x in other):
                break
            factor /= 10
        else:
            raise RuntimeError('Increase the type-B precision search limit.')
        tangents = core.tangents+(mu,nu)
        weights = (F(1),ratio)
    else:
        raise ValueError('Pair is not in the defined recursive family.')
    epsilon = core.lengths[0]/(10*(max(weights)+1))
    for _ in range(300):
        lengths = tuple(epsilon*w for w in weights)+core.lengths
        result = certify_perturbation(lengths,tangents,p,q,bound)
        if result is not None:
            return result
        epsilon /= 10
    raise RuntimeError('Increase the perturbation search limit.')


def record(witness):
    ls,ts,d,scale = integer_input(witness.lengths,witness.tangents)
    return dict(lengths=ls,tangent_numerators=ts,tangent_denominator=d,
                p=witness.p,q=witness.q,
                squared_distance_margin=str(witness.margin*scale**2) if witness.margin is not None else None,
                rational_total_turn_upper_bound=str(2*sum(witness.tangents)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--n',type=int,required=True)
    parser.add_argument('--index',type=int,default=0)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    if args.n < 1 or args.index < 0:
        parser.error('n must be positive and index nonnegative.')
    pair = next(islice(conjectured_patterns(args.n),args.index,args.index+1),None)
    if pair is None:
        parser.error('Index exceeds the recursive family size.')
    witness = realize(*pair)
    args.output.write_text(json.dumps(record(witness),indent=2)+'\n')
    print('Constructed and exactly certified:',witness.p,witness.q,flush=True)


if __name__ == '__main__':
    main()
