"""Independent check of the extreme-king reduction for touch cycles (written without reading Codex's code).

Normal n = (nx, ny). Put an extreme occupied cell at the origin: every occupied cell p has
n.p < 0, or n.p == 0 and x <= 0 (so the origin maximises (n.p, x)). Window [-r, r]^2 intersected with that
half-plane; cells outside it are empty. Counting rule imposed only where max(|x|,|y|) < r.
UNSAT => no finite arrangement exists. Usage: touch_extreme.py a b c nx ny r"""
import sys, z3
a, b, c, nx, ny, r = map(int, sys.argv[1:7])
inside = lambda x, y: nx * x + ny * y < 0 or (nx * x + ny * y == 0 and x <= 0)  # noqa: E731
T = {}
for x in range(-r - 1, r + 2):
    for y in range(-r - 1, r + 2):
        T[(x, y)] = z3.Int(f"t{x}_{y}")
s = z3.Solver()
for (x, y), t in T.items():
    s.add(t >= 0, t <= 3)
    if not inside(x, y) or max(abs(x), abs(y)) > r:
        if not inside(x, y):
            s.add(t == 0)
        continue
    if max(abs(x), abs(y)) < r:
        nb = [(x + dx, y + dy) for dx in (-1, 0, 1) for dy in (-1, 0, 1) if dx or dy]
        cnt = lambda k: z3.Sum([z3.If(T[q] == k, 1, 0) for q in nb])  # noqa: E731
        s.add(z3.Implies(t == 1, cnt(2) == a), z3.Implies(t == 2, cnt(3) == b), z3.Implies(t == 3, cnt(1) == c))
s.add(T[(0, 0)] > 0)
print(a, b, c, "n =", (nx, ny), "r =", r, s.check(), flush=True)
