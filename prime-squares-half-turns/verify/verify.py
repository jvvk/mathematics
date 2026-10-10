"""Finite exact audits of the hand proof; not an all-prime computational proof."""
import sympy as s

x, y = s.symbols('x y')


def normal(points):
    a = min(i for i, j in points)
    b = min(j for i, j in points)
    return frozenset((i-a, j-b) for i, j in points)


def poly(points):
    return s.Add(*(x**i*y**j for i, j in points))


def image(points, kind):
    maps = {
        'half': lambda i, j: (-i, -j),
        'horizontal': lambda i, j: (i, -j),
        'vertical': lambda i, j: (-i, j),
        'diagonal': lambda i, j: (j, i),
        'antidiagonal': lambda i, j: (-j, -i),
        'quarter': lambda i, j: (-j, i),
    }
    return frozenset(maps[kind](i, j) for i, j in points)


def substitute(f, kind):
    maps = {
        'half': {x: 1/x, y: 1/y},
        'horizontal': {x: x, y: 1/y},
        'vertical': {x: 1/x, y: y},
        'diagonal': {x: y, y: x},
        'antidiagonal': {x: 1/y, y: 1/x},
        'quarter': {x: y, y: 1/x},
    }
    return s.expand(f.subs(maps[kind], simultaneous=True))


def animals(n):
    shapes = {frozenset({(0, 0)})}
    for _ in range(n-1):
        shapes = {
            normal(shape | {(i+di, j+dj)})
            for shape in shapes for i, j in shape
            for di, dj in [(1, 0), (-1, 0), (0, 1), (0, -1)]
            if (i+di, j+dj) not in shape
        }
    return sorted(shapes, key=lambda p: sorted(p))


def bar(shape):
    return (len({i for i, j in shape}) == 1 or
            len({j for i, j in shape}) == 1)


def q(n, z):
    return sum(z**i for i in range(n))


def check(mutant=None):
    count = 0

    def require(condition, message):
        nonlocal count
        assert condition, message
        count += 1

    # Independent coefficient geometry checks catch incorrect reciprocity.
    fixture = frozenset({(0, 0), (1, 0), (0, 1)})
    kinds = ['half', 'horizontal', 'vertical', 'diagonal', 'antidiagonal']
    if mutant == 'quarter_as_involution':
        kinds.append('quarter')
    for kind in kinds:
        actual_kind = 'horizontal' if mutant == 'half_turn' and kind == 'half' else kind
        f = poly(fixture)
        require(s.expand(substitute(f, actual_kind)-poly(image(fixture, kind))) == 0,
                'polynomial transform differs from geometric cell image')
        require(s.expand(substitute(substitute(f, kind), kind)-f) == 0,
                'the proposed orientation operation is not an involution')

    # Oddness is indispensable to the arithmetic implication.
    for p in [2, 3, 5, 7, 11, 13, 17, 101]:
        for u in range(p+1):
            valid = (p % 2 == 1 and (2*u) % p == 0)
            if mutant == 'drop_oddness':
                valid = (2*u) % p == 0
            require(not valid or u in (0, p), 'orientation-count implication fails')

    # Prime and composite cyclotomic controls.
    for n in [2, 3, 4, 5, 6, 7, 9, 11, 13]:
        expected = n in [2, 3, 5, 7, 11, 13]
        claimed = True if mutant == 'drop_primality' else s.Poly(q(n, x), x).is_irreducible
        require(claimed == expected, 'Q_n irreducibility needs primality')

    # Exact connected sets through five cells; no larger-N search.
    expected_fixed = {2: 2, 3: 6, 5: 63}
    for p in [2, 3, 5]:
        shapes = animals(p)
        require(len(shapes) == expected_fixed[p], 'independent fixed-animal count')
        r = s.Poly(q(p, x)*q(p, y), x, y, domain=s.ZZ)
        for shape in shapes:
            f = s.Poly(poly(shape), x, y, domain=s.ZZ)
            require(f.eval({x: 1, y: 1}) == p, 'cell count')
            for kind in kinds:
                g = s.Poly(poly(normal(image(shape, kind))), x, y, domain=s.ZZ)
                d = s.gcd(f, g)
                require(d.LC() == 1, 'the gcd is normalised')
                divides_board = r.rem(d).is_zero
                require(d.total_degree() == 0 or not divides_board or bar(shape),
                        'common factor of tile orientations and board must force a bar')
                if bar(shape):
                    require(r.rem(f).is_zero, 'bars divide the prime-square polynomial')

    # A non-bar need not have coprime orientation polynomials absent a tiling.
    cross = frozenset({(1, 0), (0, 1), (1, 1), (2, 1), (1, 2)})
    f = s.Poly(poly(cross), x, y, domain=s.ZZ)
    g = s.Poly(poly(normal(image(cross, 'half'))), x, y, domain=s.ZZ)
    d = s.Poly(1, x, y, domain=s.ZZ) if mutant == 'unconditional_coprime' else s.gcd(f, g)
    require(d == f, 'centrally symmetric cross is not coprime to its half-turn')
    require(not s.Poly(q(5, x)*q(5, y), x, y).rem(d).is_zero,
            'cross common factor obstructs a tiling')

    # Sparse pattern: reflect every cell independently of the polynomial encoding.
    for p in [3, 5, 7]:
        m = (p-1)//2
        r = poly([(i, j) for i in range(-m, m+1) for j in range(-m, m+1)])
        for kind in kinds:
            require(s.expand(substitute(r, kind)-r) == 0, 'board invariance')
            f = poly(fixture)
            u = x**(-m)*y**(-m) + x**(m-1)*y**(m-1)
            v = x**m*y**m
            pattern = s.expand(f*u+substitute(f, kind)*v)
            reflected = s.expand(substitute(f, kind)*substitute(u, kind)+f*substitute(v, kind))
            require(s.expand(substitute(pattern, kind)-reflected) == 0,
                    'turning or reflecting the whole pattern swaps orientations')
            difference = u+substitute(v, kind) if mutant == 'orientation_sign' else u-substitute(v, kind)
            require(difference.subs({x: 1, y: 1}) == 1,
                    'orientation difference is 2-1, not 2+1')

    # Primitive integer division: integral quotients, including negative coefficients.
    for f in [1+x+y, 1+x+x*y, 1+x+y+x*y+x**2]:
        for h in [1, 1-x+y, 2*x**2-3*x*y+5*y**2, x**3-y**3]:
            numerator = s.Poly(s.expand(f*h), x, y, domain=s.ZZ)
            quotient, remainder = s.div(numerator, s.Poly(f, x, y, domain=s.ZZ))
            require(remainder.is_zero, 'exact division')
            require(quotient.as_expr() == h, 'the integer quotient is correct')
            require(all(c.is_Integer for c in quotient.coeffs()), 'integer coefficient quotient')

    # Concrete counterexample to extending the conclusion to composite side lengths.
    block = frozenset({(0, 0), (1, 0), (0, 1), (1, 1)})
    placements = [(0, 0), (2, 0), (0, 2), (2, 2)]
    cells = [(i+a, j+b) for a, b in placements for i, j in block]
    require(len(cells) == len(set(cells)) == 16, 'four blocks cover 4 by 4 without overlap')
    require(set(cells) == {(i, j) for i in range(4) for j in range(4)}, 'composite board coverage')
    require(not bar(block), 'the composite control is not a bar')
    require(s.expand(poly(block)*poly(placements)-q(4, x)*q(4, y)) == 0,
            'composite tiling polynomial identity')
    return count


if __name__ == '__main__':
    print(f'{check()} exact audit assertions passed')
