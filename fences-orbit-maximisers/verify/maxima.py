"""Read `orbits` output lines (n, e(P), #Aut(P), digraph6) on stdin; print g(n) = max e/#Aut and the
maximisers' digraph6 lines. Usage: genposetg N q | ./orbits | python3 maxima.py"""
import sys
from fractions import Fraction

best, arg, count, n = Fraction(-1), [], 0, None
for line in sys.stdin:
    parts = line.split()
    if len(parts) < 4:
        continue
    n, e, aut, g6 = int(parts[0]), int(parts[1]), int(parts[2]), parts[3]
    count += 1
    assert e % aut == 0, line  # Aut(P) acts freely on linear extensions
    f = Fraction(e, aut)
    if f > best:
        best, arg = f, [g6]
    elif f == best:
        arg.append(g6)
assert count > 0, "no posets read"
print(n, count, best, len(arg), " ".join(arg))
