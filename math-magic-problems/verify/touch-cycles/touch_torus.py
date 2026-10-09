"""Touch cycles on an N x N torus (no edges): SAT means a periodic configuration of the whole plane."""
import sys, z3
a, b, c, N = map(int, sys.argv[1:5])
T = {(x, y): z3.Int(f"t{x}_{y}") for x in range(N) for y in range(N)}
s = z3.Solver(); s.set("timeout", 100000)
for (x, y), t in T.items():
    s.add(t >= 0, t <= 3)
    nb = [((x + dx) % N, (y + dy) % N) for dx in (-1, 0, 1) for dy in (-1, 0, 1) if dx or dy]
    cnt = lambda k: z3.Sum([z3.If(T[q] == k, 1, 0) for q in nb])
    s.add(z3.Implies(t == 1, cnt(2) == a), z3.Implies(t == 2, cnt(3) == b), z3.Implies(t == 3, cnt(1) == c))
for k in (1, 2, 3): s.add(z3.Or([t == k for t in T.values()]))
print(a, b, c, "torus", N, s.check())
