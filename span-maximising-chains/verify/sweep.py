"""Projection sweep combined with valley-shaped turns.

The projection sweep follows MvG's 2012 Mathematics Stack Exchange answer:
https://math.stackexchange.com/questions/221764/
The valley restriction and its proof are in the accompanying manuscript.

Both solvers enumerate 2**(n-3) angle orders for n >= 3 and O(n**2)
projection events per order. Exact mode takes integer lengths and positive
rational half-angle tangents t_j / denominator. It uses no floating point.
"""
from fractions import Fraction
from functools import cmp_to_key
from math import cos, sin, pi, isfinite, prod


def valley_representatives(n):
    """One turn order per reversal class, with the largest turn first."""
    if n < 1:
        raise ValueError('Need at least one segment.')
    if n <= 2:
        yield tuple(range(n-1))
        return
    for mask in range(1 << (n-3)):
        left = tuple(j for j in range(n-3, 0, -1) if mask >> (j-1) & 1)
        right = tuple(j for j in range(1, n-2) if not mask >> (j-1) & 1)
        yield (n-2,) + left + (0,) + right


def _floating_geometry(angles, q):
    theta = [0.]
    for j in q:
        theta.append(theta[-1]+angles[j])
    rs, ss = [cos(t) for t in theta], [sin(t) for t in theta]
    events = sorted(((theta[i]+theta[j])/2, i, j)
                    for i in range(len(theta)) for j in range(i+1, len(theta)))
    return rs, ss, events


def _canonical(p, q):
    """Normalize the shortest length to the left endpoint after optimization."""
    if p[-1] == 0:
        return tuple(reversed(p)), tuple(reversed(q))
    return tuple(p), tuple(q)


def maximize_sweep(lengths, angles):
    """Return (distance, p, q), using ordinary floating point.

    The mathematical algorithm is exact in real arithmetic. Very close event
    times or nearly tied objective values can require exact mode in practice.
    """
    n = len(lengths)
    if n < 1 or len(angles) != n-1:
        raise ValueError('Need n lengths and n-1 turns.')
    if any(not isfinite(x) or x <= 0 for x in (*lengths, *angles)):
        raise ValueError('All input values must be positive and finite.')
    if any(a >= b for a,b in zip(lengths,lengths[1:])) or any(a >= b for a,b in zip(angles,angles[1:])):
        raise ValueError('Each input list must be strictly increasing.')
    if sum(angles) >= pi:
        raise ValueError('Need total turn < pi.')
    best = None
    for q in valley_representatives(n):
        rs, ss, events = _floating_geometry(angles, q)
        p = list(range(n-1, -1, -1))
        x = sum(lengths[j]*r for j,r in zip(p,rs))
        y = sum(lengths[j]*s for j,s in zip(p,ss))
        v = x*x+y*y
        if best is None or v > best[0]:
            best = v, q, 0
        for step, (_,i,j) in enumerate(events,1):
            delta = lengths[p[j]]-lengths[p[i]]
            x += delta*(rs[i]-rs[j])
            y += delta*(ss[i]-ss[j])
            p[i],p[j] = p[j],p[i]
            v = x*x+y*y
            if v > best[0]:
                best = v, q, step
    _,q,steps = best
    _,_,events = _floating_geometry(angles,q)
    p = list(range(n-1,-1,-1))
    for _,i,j in events[:steps]:
        p[i],p[j] = p[j],p[i]
    p,q = _canonical(p,q)
    # Recompute the returned distance without accumulated sweep updates.
    rs,ss,_ = _floating_geometry(angles,q)
    x = sum(lengths[j]*r for j,r in zip(p,rs))
    y = sum(lengths[j]*s for j,s in zip(p,ss))
    return (x*x+y*y)**.5,p,q


def integer_directions(tangents, denominator, q):
    hs = [denominator**2+t*t for t in tangents]
    common = prod(hs)
    re,im = common,0
    rs,ss = [re],[im]
    for j in q:
        c,s,h = denominator**2-tangents[j]**2,2*denominator*tangents[j],hs[j]
        nr,ni = re*c-im*s,re*s+im*c
        if nr % h or ni % h:
            raise ArithmeticError('Nonintegral scaled rotation.')
        re,im = nr//h,ni//h
        rs.append(re)
        ss.append(im)
    return common,rs,ss


def _half(event):
    x,y = event[:2]
    return 0 if y > 0 or (y == 0 and x >= 0) else 1


def _event_compare(a,b):
    ha,hb = _half(a),_half(b)
    if ha != hb:
        return -1 if ha < hb else 1
    cross = a[0]*b[1]-a[1]*b[0]
    if cross:
        return -1 if cross > 0 else 1
    # Simultaneous events involve disjoint pairs; any deterministic order
    # gives the assignments on the adjacent open intervals, plus legal
    # intermediate assignments. All of them may safely be evaluated.
    return (a[2:] > b[2:])-(a[2:] < b[2:])


def _integer_events(rs,ss):
    events = [(rs[i]*rs[j]-ss[i]*ss[j],rs[i]*ss[j]+ss[i]*rs[j],i,j)
              for i in range(len(rs)) for j in range(i+1,len(rs))]
    return sorted(events,key=cmp_to_key(_event_compare))


def maximize_exact(lengths,tangents,denominator):
    """Return (exact squared distance as Fraction, p, q).

    alpha_j = 2*atan(tangents[j]/denominator), total turn < pi.
    Lengths, tangent numerators, and denominator must be positive integers;
    the two lists must be strictly increasing.
    """
    n = len(lengths)
    if n < 1 or len(tangents) != n-1:
        raise ValueError('Need n lengths and n-1 tangent numerators.')
    if any(type(x) is not int or x <= 0 for x in (*lengths,*tangents,denominator)):
        raise ValueError('Need positive integer input.')
    if any(a >= b for a,b in zip(lengths,lengths[1:])) or any(a >= b for a,b in zip(tangents,tangents[1:])):
        raise ValueError('Each input list must be strictly increasing.')
    common,_,prefix_sines = integer_directions(tangents,denominator,tuple(range(n-1)))
    # Each individual turn lies in (0,pi). Starting below pi, a prefix can
    # cross pi only by entering [pi,2pi), where its sine is nonpositive.
    if any(s <= 0 for s in prefix_sines[1:]):
        raise ValueError('Need total turn < pi.')
    best = None
    for q in valley_representatives(n):
        _,rs,ss = integer_directions(tangents,denominator,q)
        events = _integer_events(rs,ss)
        p = list(range(n-1,-1,-1))
        x = sum(lengths[j]*r for j,r in zip(p,rs))
        y = sum(lengths[j]*s for j,s in zip(p,ss))
        v = x*x+y*y
        if best is None or v > best[0]:
            best = v,q,0
        for step,(_,_,i,j) in enumerate(events,1):
            delta = lengths[p[j]]-lengths[p[i]]
            x += delta*(rs[i]-rs[j])
            y += delta*(ss[i]-ss[j])
            p[i],p[j] = p[j],p[i]
            v = x*x+y*y
            if v > best[0]:
                best = v,q,step
    v,q,steps = best
    _,rs,ss = integer_directions(tangents,denominator,q)
    events = _integer_events(rs,ss)
    p = list(range(n-1,-1,-1))
    for _,_,i,j in events[:steps]:
        p[i],p[j] = p[j],p[i]
    p,q = _canonical(p,q)
    return Fraction(v,common**2),p,q
