"""Exact integer certificates; every turn is alpha=2*atan(t/denominator)."""
from fractions import Fraction
from itertools import permutations
from math import prod, tan
from pathlib import Path
import json

from solver import patterns


def validate_data(lengths, tangents, denominator):
    if len(lengths) < 3 or len(tangents) != len(lengths)-1:
        raise ValueError('Certificates require n >= 3 lengths and n-1 turns.')
    if any(type(x) is not int or x <= 0 for x in (*lengths, *tangents, denominator)):
        raise ValueError('Certificate data must be positive integers.')
    if any(a >= b for a,b in zip(lengths,lengths[1:])) or any(a >= b for a,b in zip(tangents,tangents[1:])):
        raise ValueError('Lengths and tangent numerators must be strictly increasing.')


def score(lengths, tangents, denominator, p, q):
    hs = [denominator**2 + t*t for t in tangents]
    common = prod(hs)
    re, im = common, 0
    x, y = lengths[p[0]]*re, 0
    for i, j in enumerate(q, 1):
        c, s, h = denominator**2 - tangents[j]**2, 2*denominator*tangents[j], hs[j]
        nr, ni = re*c-im*s, re*s+im*c
        if nr % h or ni % h:
            raise ArithmeticError('Nonintegral scaled rotation.')
        re, im = nr//h, ni//h
        x += lengths[p[i]]*re
        y += lengths[p[i]]*im
    return x*x + y*y, common, re, im


def certify(lengths, tangents, denominator):
    validate_data(lengths, tangents, denominator)
    # 0 < total angle < 3 < pi; positive cosine then gives total < pi/2.
    if 2*sum(tangents) >= 3*denominator:
        raise ValueError('This certificate checker requires 2*sum(t) < 3*d.')
    values = []
    for p, q in patterns(len(lengths)):
        v, common, re, im = score(lengths, tangents, denominator, p, q)
        if re <= 0 or im <= 0:
            raise ValueError('Certificate total turn must be strictly below pi/2.')
        values.append((v, p, q))
    values.sort(reverse=True)
    margin = Fraction(values[0][0] - values[1][0], common**2)
    if margin <= 0:
        raise ValueError('The data do not have a unique structured optimum.')
    return values[0][1], values[0][2], margin


def certify_saved(n):
    root = Path(__file__).parent
    witnesses = json.loads((root/f'witnesses-{n}.json').read_text())
    result = []
    for w in witnesses:
        for exponent in range(3, 10):
            denominator = 10**exponent
            lengths = [round(x*denominator) for x in w['lengths']]
            tangents = [round(tan(x/2)*denominator) for x in w['angles']]
            if any(a >= b for a, b in zip(lengths, lengths[1:])) or any(a >= b for a, b in zip(tangents, tangents[1:])):
                continue
            p, q, margin = certify(lengths, tangents, denominator)
            if list(p) == w['p'] and list(q) == w['q']:
                result.append(dict(p=p, q=q, lengths=lengths, tangent_numerators=tangents, tangent_denominator=denominator, squared_distance_margin=str(margin)))
                break
        else:
            raise RuntimeError('Could not rationalize witness.')
    (root/f'exact-witnesses-{n}.json').write_text(json.dumps(result, indent=2))
    print(f'Certified {len(result)} distinct optimal patterns for n={n}.')
    return result


def certify_all_permutations(lengths, tangents, denominator):
    """Independent exact check, using no structural theorem; omit reversals."""
    validate_data(lengths, tangents, denominator)
    n = len(lengths)
    hs = [denominator**2+t*t for t in tangents]
    common = prod(hs)
    orders = [(p, [lengths[j] for j in p]) for p in permutations(range(n)) if p[0] < p[-1]]
    best = second = None
    count = 0
    for q in permutations(range(n-1)):
        re, im = common, 0
        rs, ss = [re], [im]
        for j in q:
            c, s, h = denominator**2-tangents[j]**2, 2*denominator*tangents[j], hs[j]
            nr,ni = re*c-im*s,re*s+im*c
            if nr % h or ni % h:
                raise ArithmeticError('Nonintegral scaled rotation.')
            re,im = nr//h,ni//h
            rs.append(re)
            ss.append(im)
        for p, ls in orders:
            x = sum(l*r for l, r in zip(ls, rs))
            y = sum(l*s for l, s in zip(ls, ss))
            v = x*x+y*y
            count += 1
            if best is None or v > best[0]:
                second, best = best, (v, p, q)
            elif second is None or v > second[0]:
                second = (v, p, q)
    if best[0] <= second[0]:
        raise ValueError('The data do not have a unique unrestricted optimum.')
    return best[1], best[2], Fraction(best[0]-second[0], common**2), count


if __name__ == '__main__':
    import sys
    certify_saved(int(sys.argv[1]) if len(sys.argv) > 1 else 7)
