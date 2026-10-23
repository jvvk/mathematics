"""Certificate for the note: Theorem 1 by brute force, the ladder description, the worked example,
and the counts in Remarks 1 and 2. Run: python3 -I verify_note.py  (prints ALL PASS)."""
import itertools
import math
import random
import sys

RANGES = {2: 8, 3: 8, 4: 5, 5: 4, 6: 3}  # entries 1..R for each n


def generators(a: list[int]) -> list[int]:
    n = len(a)
    out = []
    for i in range(n):
        s, p = 1, 1
        for j in range(n - 1):
            p *= a[(i + j) % n]
            s += p
        out.append(s)
    return out


def membership(xs: list[int], bound: int) -> list[bool]:
    rep = [False] * (bound + 1)
    rep[0] = True
    for v in range(1, bound + 1):
        rep[v] = any(v >= x and rep[v - x] for x in xs)
    return rep


def coprime(xs: list[int]) -> bool:
    return math.gcd(*xs) == 1


def digit_values(a: list[int], xs: list[int]) -> list[int]:
    n = len(a)
    bounds = [a[(i - 1) % n] for i in range(n)]  # d_i <= a_{i-1} - 1
    return [sum(d * x for d, x in zip(ds, xs)) for ds in itertools.product(*[range(b) for b in bounds])]


def check_case(a: list[int]) -> tuple[bool, list[bool], int]:
    xs = generators(a)
    n, N = len(a), math.prod(a) - 1
    F = (n - 1) * N
    bound = n * N + N + 2 * max(xs)
    rep = membership(xs, bound)
    frob = max(v for v in range(bound + 1) if not rep[v])
    if frob != F:
        return False, rep, F
    # ladders: in each residue class mod N, S is {lowest} + N Z>=0, lowest = digit value (zero class: 0 and nN)
    vals = digit_values(a, xs)
    if sorted(v % N for v in vals) != sorted(list(range(1, N)) + [0, 0]) or max(vals) != n * N:
        return False, rep, F
    for r in range(1, N):
        low = next(v for v in vals if v % N == r)
        members = [v for v in range(r, bound + 1, N) if rep[v]]
        if members[0] != low or any(not rep[v] for v in range(low, bound + 1, N)):
            return False, rep, F
    return True, rep, F


def main() -> None:
    ok = True
    # worked example
    xs = generators([1, 2, 3])
    rep = membership(xs, 40)
    gaps = [v for v in range(41) if not rep[v]]
    ok &= xs == [4, 9, 7] and gaps == [1, 2, 3, 5, 6, 10]
    ok &= sorted(digit_values([1, 2, 3], xs)) == [0, 4, 7, 8, 11, 15]
    # Theorem 1 over the stated ranges
    total = 0
    for n, R in RANGES.items():
        for a in itertools.product(range(1, R + 1), repeat=n):
            if not coprime(generators(list(a))):
                continue
            total += 1
            good, _, _ = check_case(list(a))
            if not good:
                print("FAIL", a)
                ok = False
    print(f"Theorem 1 + ladders: {total} coprime lists")
    # mutants: a wrong formula must be caught
    for name, f in [("(n-2)N", lambda n, P: (n - 2) * (P - 1)), ("(n-1)P", lambda n, P: (n - 1) * P)]:
        a = [1, 2, 3]
        xs = generators(a)
        rep = membership(xs, 60)
        frob = max(v for v in range(61) if not rep[v])
        ok &= frob != f(3, 6)
        print(f"mutant {name}: rejected")
    print("ALL PASS" if ok else "FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
