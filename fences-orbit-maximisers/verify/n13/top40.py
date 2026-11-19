"""Keep the 40 lines with the largest f = e/#Aut from `orbits` output (n e aut digraph6) on stdin."""
import heapq
import sys
from fractions import Fraction

heap = []
for line in sys.stdin:
    n, e, a, g6 = line.split()
    item = (Fraction(int(e), int(a)), g6, n, e, a)
    if len(heap) < 40:
        heapq.heappush(heap, item)
    elif item[0] > heap[0][0]:
        heapq.heapreplace(heap, item)
for f, g6, n, e, a in sorted(heap, reverse=True):
    print(n, e, a, g6)
