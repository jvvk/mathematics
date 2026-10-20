"""Three unrooted binary trees on 13 leaves (labels 0..12) with no common quartet split: h(3) >= 14.
Found by sat_h3.py --n 13 (CaDiCaL 1.5.3 via PySAT), 2026-10-16; checked here by quartets.py alone."""
import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from quartets import common_quartets, leaves

T1 = (0, ((((6, 5), (1, (8, 10))), ((2, 9), (12, (11, 7)))), (4, 3)))
T2 = (0, ((12, (((6, 9), (4, (7, 10))), ((2, 5), (3, (1, 11))))), 8))
T3 = (0, (((5, 9), ((12, (1, 4)), ((6, 2), ((3, 7), 8)))), (10, 11)))

if __name__ == "__main__":
    for T in (T1, T2, T3):
        assert leaves(T) == frozenset(range(13))
    c = common_quartets([T1, T2, T3])
    assert not c, c
    print("13-leaf witness verified: 715 quartets, none common to all three trees, so h(3) >= 14")
