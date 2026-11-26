#!/usr/bin/env python3
"""Exact checks for the signed, coefficient-free counting argument.

Run: python3 signed_route/check.py
No third-party dependencies. All arithmetic is integral. The commutator
enumerator is independent of the signed counts. Local maps are checked on
every possible marking, and the word identities on every marking through n=9.
"""
if __debug__ is False:
    raise SystemExit("refusing to run with -O: the checks are assert statements")
from collections import Counter, defaultdict
from itertools import permutations, product
from math import comb, factorial


def cycles(p):
    seen = set()
    out = []
    for i in range(len(p)):
        if i not in seen:
            c = []
            j = i
            while j not in seen:
                seen.add(j)
                c.append(j)
                j = p[j]
            out.append(tuple(c))
    return out


def conjugators(v, w):
    """Yield all u satisfying u v u^-1 = w, without scanning all u."""
    src, dst = defaultdict(list), defaultdict(list)
    for c in cycles(v):
        src[len(c)].append(c)
    for c in cycles(w):
        dst[len(c)].append(c)
    if {k: len(cs) for k, cs in src.items()} != {
        k: len(cs) for k, cs in dst.items()
    }:
        return
    sizes = sorted(src)
    choices = []
    for k in sizes:
        choices.append([
            (match, shifts)
            for match in permutations(range(len(src[k])))
            for shifts in product(range(k), repeat=len(src[k]))
        ])
    for data in product(*choices):
        u = [None] * len(v)
        for k, (match, shifts) in zip(sizes, data):
            for j, target in enumerate(match):
                a, b = src[k][j], dst[k][target]
                for t, x in enumerate(a):
                    u[x] = b[(t + shifts[j]) % k]
        yield tuple(u)


def commutator_count(n):
    total = half = 0
    for v in permutations(range(n)):
        cv = tuple((x + 1) % n for x in v)
        for u in conjugators(v, cv):
            # Check the equation itself, independently of cycle matching.
            assert all(u[v[x]] == (v[u[x]] + 1) % n for x in range(n))
            total += 1
            w = tuple((x - 1) % n for x in u)
            half += w[v[0]] >= v[0]
    return total, half


def partitions(n, low=1):
    if n == 0:
        yield ()
    for k in range(low, n + 1):
        for tail in partitions(n - k, k):
            yield (k,) + tail


def odd_cycle_objects(n):
    """Count O_n by cycle types and a two-variable finite convolution.

    This is dynamic programming over finite choices of subsets, not a
    formal-series identity. Each cycle has odd A and odd B and four colors.
    """
    total = 0
    for lam in partitions(n):
        z = 1
        for k, mult in Counter(lam).items():
            z *= k ** mult * factorial(mult)
        states = {(0, 0): 1}
        for k in lam:
            nxt = defaultdict(int)
            for (a, b), value in states.items():
                for r in range(1, k + 1, 2):
                    for s in range(1, k + 1, 2):
                        if a + b + r + s <= n + 1:
                            nxt[a + r, b + s] += (
                                value * 4 * comb(k, r) * comb(k, s)
                            )
            states = nxt
        for (a, b), value in states.items():
            if a + b == n + 1:
                total += (factorial(n) // z) * value * factorial(a - 1) * factorial(b - 1)
    return total


def marks(n, total):
    by_size = defaultdict(list)
    for mask in range(1 << n):
        by_size[mask.bit_count()].append(mask)
    for a, aa in by_size.items():
        for A in aa:
            for B in by_size.get(total - a, []):
                yield A, B


def sign(k):
    return -1 if k % 2 else 1


def word_count(m):
    """W_m: every pair of mark sets, every cut, factorial order weights."""
    total = 0
    for A, B in marks(m, m):
        weight = factorial(A.bit_count()) * factorial(B.bit_count())
        for k in range(m + 1):
            total += sign((A >> k).bit_count() + (B >> k).bit_count()) * weight
    return total


def telescope_check(n):
    """Check both involutions on every marked word with n total marks.

    Actual orders of A and B tokens are carried unchanged by telescope
    pairing. Their exact multiplicity is factorial(a)*factorial(b).
    """
    endpoint = 0
    residual = 0
    for A, B in marks(n, n):
        weight = factorial(A.bit_count()) * factorial(B.bit_count())
        endpoint += (1 - sign(n)) * weight
        for j in range(n):
            h = ((A >> j) & 1) + ((B >> j) & 1)
            after = (A >> (j + 1)).bit_count() + (B >> (j + 1)).bit_count()
            s = sign(after)
            r = -sign(after + h)
            if h % 2 == 0:
                assert s == -r
            else:
                assert s == r
                residual += (s + r) * weight
            if j + 1 < n:
                # S at j is paired with R at j+1, same cut, same orders.
                next_after = (A >> (j + 2)).bit_count() + (B >> (j + 2)).bit_count()
                next_h = ((A >> (j + 1)) & 1) + ((B >> (j + 1)) & 1)
                assert s == sign(next_after + next_h)
    assert residual == endpoint
    if n % 2:
        assert residual == 2 * (n + 1) * word_count(n - 1)
        assert endpoint == 2 * (2 ** n) * factorial(n)
    return residual


def local_maps_check(mutant=None):
    # PQ -> SR: A stays put; exchange B membership at the two points.
    for ap, bp, aq, bq in product((0, 1), repeat=4):
        before = sign(bp + aq)
        new_bp, new_bq = (bp, bq) if mutant == 'omit_blue_swap' else (bq, bp)
        after = sign(aq + new_bq)
        assert before == after, 'PQ->SR failed to preserve sign'
        assert bp + bq == new_bp + new_bq
        # Applying the swap again recovers the original marking.
        assert (new_bq, new_bp) == (bp, bq)
    # S+R-P-Q at one point cancels unless both marked.
    for a, b in product((0, 1), repeat=2):
        signs = [1, sign(a + b), -sign(b), -sign(a)]
        if mutant == 'wrong_R_sign':
            signs[1] *= -1
        assert sum(signs) == (4 if a == b == 1 else 0), 'single point cancellation failed'


def negative_cycle_involution_check(max_n=6):
    # On a fixed negative-color point set, compose with the transposition
    # of its two smallest points. Test involution and cycle parity exactly.
    checked = 0
    for n in range(2, max_n + 1):
        for p in permutations(range(n)):
            q = list(p)
            q[0], q[1] = q[1], q[0]
            r = list(q)
            r[0], r[1] = r[1], r[0]
            assert tuple(r) == p
            assert (len(cycles(p)) - len(cycles(q))) % 2 == 1
            checked += 1
    return checked


def permutation_word_check(max_n=7):
    """Check the exact permutation-to-word bijection used for S and R."""
    checked = 0
    for n in range(max_n + 1):
        words = set()
        for p in permutations(range(n)):
            blocks = []
            for c in cycles(p):
                j = c.index(max(c))
                blocks.append(c[j:] + c[:j])
            blocks.sort(key=lambda c: c[0])
            word = tuple(x for c in blocks for x in c)
            assert word not in words
            words.add(word)
            rebuilt = list(range(n))
            starts = [j for j, x in enumerate(word) if j == 0 or x > max(word[:j])]
            for lo, hi in zip(starts, starts[1:] + [n]):
                block = word[lo:hi]
                for x, y in zip(block, block[1:] + block[:1]):
                    rebuilt[x] = y
            assert tuple(rebuilt) == p
            checked += 1
        assert len(words) == factorial(n)
    return checked


def direct_odd_objects(n):
    """Independent direct check of O_n for small n (no cycle-type DP)."""
    total = 0
    for p in permutations(range(n)):
        cs = cycles(p)
        masks = [sum(1 << x for x in c) for c in cs]
        for A, B in marks(n, n + 1):
            if all((A & C).bit_count() % 2 and (B & C).bit_count() % 2 for C in masks):
                total += 4 ** len(cs) * factorial(A.bit_count() - 1) * factorial(B.bit_count() - 1)
    return total


def K_involution_check(max_n=6):
    def move(obj):
        U, V, s, r = obj
        if s is not None:
            return ((s,) + U, V, None, r)
        if U:
            return (U[1:], V, U[0], r)
        if r is not None:
            return (U, (r,) + V, None, None)
        assert V
        return (U, V[1:], None, V[0])

    checked = 0
    for n in range(1, max_n + 1):
        for has_s, has_r in product((0, 1), repeat=2):
            if has_s + has_r > n:
                continue
            for labels in permutations(range(n)):
                offset = has_s + has_r
                s = labels[0] if has_s else None
                r = labels[has_s] if has_r else None
                rest = labels[offset:]
                for cut in range(len(rest) + 1):
                    obj = (rest[:cut], rest[cut:], s, r)
                    nxt = move(obj)
                    assert move(nxt) == obj
                    assert (has_s + has_r + (nxt[2] is not None) + (nxt[3] is not None)) % 2 == 1
                    # No point changes between its S and R types.
                    assert set(obj[0]) | ({s} if has_s else set()) == set(nxt[0]) | ({nxt[2]} if nxt[2] is not None else set())
                    checked += 1
    return checked


def mutations():
    killed = []
    for mutant in ('omit_blue_swap', 'wrong_R_sign'):
        try:
            local_maps_check(mutant)
        except AssertionError:
            killed.append(mutant)
        else:
            raise AssertionError('mutation survived: ' + mutant)
    # Dropping the last insertion slot changes (a+1)+(b+1) to a+b.
    n = 3
    assert (n - 1) * word_count(n - 1) != (2 ** n) * factorial(n)
    killed.append('omit_last_insertion_slots')
    # Replacing the four surviving colors by two breaks the bridge.
    O = odd_cycle_objects(3)
    assert O != 2 * factorial(3) * word_count(2)
    killed.append('only_two_surviving_colors')
    return killed


def main():
    local_maps_check()
    pairs = negative_cycle_involution_check()
    print('Local marking maps: exhaustive PASS (16 PQ cases, 4 singleton cases)')
    print(f'Negative-cycle involution: {pairs} permutations PASS')
    print(f'Permutation/word bijection: {permutation_word_check()} permutations PASS')
    print(f'K involution: {K_involution_check()} labeled objects PASS')
    for n in (1, 3, 5):
        assert direct_odd_objects(n) == odd_cycle_objects(n)
    print('Direct odd-cycle objects: n=1,3,5 PASS')
    print('n  |F|  |H|  O_n  W_(n-1)  (n+1)W  2^n*n!')
    for n in (1, 3, 5, 7, 9):
        F, H = commutator_count(n)
        O = odd_cycle_objects(n)
        W = word_count(n - 1)
        telescope_check(n)
        assert O == (2 ** (n + 1)) * factorial(n - 1) * F
        assert O == 4 * factorial(n) * W
        assert (n + 1) * W == (2 ** n) * factorial(n)
        assert (n + 1) * F == 2 * n * factorial(n)
        assert H == factorial(n)
        print(n, F, H, O, W, (n + 1) * W, (2 ** n) * factorial(n), flush=True)
    print('Mutations rejected:', ', '.join(mutations()))
    print('ALL CHECKS PASS')


if __name__ == '__main__':
    main()
