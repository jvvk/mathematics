"""Assert the numbers stated in "Sixteen words cover all 15-bit strings" that are not the cover itself (that is
verify15.py) or the symmetric optimum (recheck/recheck_sym.py): the earlier rates, the new rate, the lower bound,
the orbit structure of the cover and the problem sizes. Mutants follow.

    python3 check.py
"""
from __future__ import annotations

import sys

S16 = ("0000000000 0000000011 0000111110 0011001100 0011111111 0110000110 0110101001 0111110000 "
       "1000001111 1001010110 1001111001 1100000000 1100110011 1111000001 1111111100 1111111111").split()


def orbit(w: str) -> frozenset[str]:
    c = w.translate(str.maketrans("01", "10"))
    return frozenset({w, c, w[::-1], c[::-1]})


def run(rates=((2, 3, 1.260), (6, 9, 1.220), (10, 12, 1.212), (17, 15, 1.208)), new=(16, 15), lower=1.058,
        orbit_sizes=(2, 2, 2, 2, 4, 4)) -> int:
    n = 0
    for c, L, shown in rates:
        assert abs(c ** (1 / L) - shown) < 5e-4, (c, L, c ** (1 / L), shown)
        n += 1
    assert 1.2030 < new[0] ** (1 / new[1]) < 1.2031 and 17 ** (1 / 15) > 1.2078
    assert all(new[0] ** (1 / new[1]) < c ** (1 / L) for c, L, _ in rates)
    assert abs(2 ** (5 / 3) / 3 - lower) < 5e-4
    orbs = {orbit(w) for w in S16}
    assert sorted(len(o) for o in orbs) == list(orbit_sizes) and set().union(*orbs) == set(S16)
    assert all(len(w) == 10 for w in S16) and len(set(S16)) == 16
    sizes = sorted(len(orbit(format(y, "010b"))) for y in range(1 << 10))
    assert set(sizes) == {2, 4} and 2 ** 10 == 1024 and 2 ** 15 == 32768
    return n + 5


if __name__ == "__main__":
    print(f"positive: {run()} checks passed", flush=True)
    muts = {"Meyerowitz rate 1.221": dict(rates=((2, 3, 1.260), (6, 9, 1.220), (10, 12, 1.221), (17, 15, 1.208))),
            "cover of size 17 claimed as the improvement": dict(new=(17, 15)),
            "lower bound 1.068": dict(lower=1.068),
            "five orbits": dict(orbit_sizes=(4, 4, 4, 2, 2))}
    for name, kw in muts.items():
        try:
            run(**kw)
        except AssertionError as e:
            print(f"rejected mutant: {name} ({str(e)[:60]})", flush=True)
        else:
            sys.exit(f"UNDETECTED MUTANT: {name}")
    print(f"all {len(muts)} mutants rejected")
