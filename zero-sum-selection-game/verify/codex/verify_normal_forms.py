#!/usr/bin/env python3
"""Check the twelve normal forms against the entire exact component list."""
from collections import Counter
from fractions import Fraction
from itertools import permutations, product
from pathlib import Path
import json
import sympy

from templates import rref


def shape(number, a=0, b=0, c=0):
    table = (
        ((0,0,0), (0,0,a), (0,b,c)),
        ((a,0,0), (0,0,b), (0,-a,c)),
        ((a,b,0), (0,0,c), (0,-b,-a)),
        ((a,a,a), (0,-a,b), (0,-a,c)),
        ((2*a,a,a), (0,-a,b), (0,-a,-2*a)),
        ((a,b,b), (0,-b,-a), (0,-b,-a)),
        ((2*a,a,a), (0,-a,-2*a), (0,-a,b)),
        ((a+b,a,a), (0,-a,-a-b), (0,-a,-b)),
        ((0,a,a), (0,-a,b), (0,-a,-b)),
        ((3*a,2*a,a), (0,-a,-3*a), (0,-a,-2*a)),
        ((a+b,a,b), (0,-b,-a), (0,-b,-a)),
        ((3*a,2*a,a), (0,-a,-2*a), (0,-a,-3*a)),
    )
    return tuple(x for row in table[number-1] for x in row)


def run():
    root = Path(__file__).resolve().parent
    saved = json.loads((root/'components-order-3.json').read_text())
    expected = {tuple(tuple(Fraction(x) for x in row) for row in item['equations'])
                for item in saved}
    all_spaces = set()
    orbit_sizes = []
    perms = tuple(permutations(range(3)))
    for number in range(1, 13):
        param_count = 3 if number <= 4 else 1 if number in (10,12) else 2
        generators = [shape(number, **{('a','b','c')[i]: 1}) for i in range(param_count)]
        generators += [(-1,-1,-1,1,1,1,0,0,0), (-1,-1,-1,0,0,0,1,1,1)]
        coefficients = sympy.Matrix(generators)
        assert coefficients.rank() == param_count+2
        equations = [tuple(Fraction(x) for x in vector) for vector in coefficients.nullspace()]
        orbit = set()
        for p, q, t in product(perms, repeat=3):
            order = p+tuple(3+j for j in q)+tuple(6+j for j in t)
            orbit.add(rref(tuple(tuple(row[j] for j in order) for row in equations), 9))
        assert all_spaces.isdisjoint(orbit)
        all_spaces.update(orbit)
        orbit_sizes.append(len(orbit))
    assert all_spaces == expected
    return {'passed': True, 'normal_forms': 12, 'components': len(all_spaces),
            'component_dimension_counts': dict(Counter(9-len(w) for w in all_spaces)),
            'orbit_sizes_by_type': orbit_sizes}


if __name__ == '__main__':
    print(json.dumps(run(), indent=2, sort_keys=True))
