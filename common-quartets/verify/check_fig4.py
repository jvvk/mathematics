"""Snir-Yuster 2602.23096 Figure 4, read off the rendered page: three 10-leaf trees, claimed no common quartet."""
import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])
from quartets import common_quartets

T1 = (((1, 2), (3, 4)), (9, 10), ((5, 6), (7, 8)))
T2 = (((1, 5), (4, 9)), (10, (3, 8)), (7, (2, 6)))
T3 = (((1, 6), (8, 9)), (10, (4, 7)), (3, (2, 5)))
c = common_quartets([T1, T2, T3])
print("common quartets:", len(c), [sorted(map(sorted, x)) for x in c][:5])
assert not c
print("Figure 4 verified: no common quartet on [10], so h(3) >= 11")
