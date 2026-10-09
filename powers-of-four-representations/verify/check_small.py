"""Independent check of Proposition 1 (direct count of ordered triples, no generating functions).

A = N_0 minus {16, 64, 256, ...}. For every N <= LIMIT: R_{A,3}(N) - R_{A,3}(N-1) > 0 and
>= N + 1 - 3 m(N) - m(N)^2, where m(N) = #{4^(j+2) <= N}. Also checks h = 4, 5 strict increase. `--mutant` deletes {4n+2} instead and must fail.
"""
import sys

MUTANT = "--mutant" in sys.argv  # delete the progression 4n+2 instead: the check must fail
args = [a for a in sys.argv[1:] if a != "--mutant"]
LIMIT = int(args[0]) if args else 600
E = {4 * j + 2 for j in range(LIMIT)} if MUTANT else {4 ** (j + 2) for j in range(20)}
inA = [n not in E for n in range(LIMIT + 1)]


def conv(f, g):
    out = [0] * (LIMIT + 1)
    for i, a in enumerate(f):
        if a:
            for j in range(LIMIT + 1 - i):
                out[i + j] += a * g[j]
    return out


one = [1 if x else 0 for x in inA]
R2 = conv(one, one)
R3 = conv(R2, one)
R4 = conv(R3, one)
R5 = conv(R4, one)
# direct triple count at a few N, independent of conv
for N in (0, 1, 15, 16, 17, 64, 65, 100):
    direct = sum(1 for a in range(N + 1) for b in range(N + 1 - a) if inA[a] and inA[b] and inA[N - a - b])
    assert direct == R3[N], (N, direct, R3[N])
worst = None
for N in range(1, LIMIT + 1):
    m = sum(1 for e in E if e <= N)
    d = R3[N] - R3[N - 1]
    lb = N + 1 - 3 * m - m * m
    assert d >= lb > 0, (N, d, lb)
    assert R4[N] > R4[N - 1] and R5[N] > R5[N - 1], N
    if worst is None or d - lb < worst[1]:
        worst = (N, d - lb)
print(f"N <= {LIMIT}: h = 3, 4, 5 strictly increasing; R3 difference >= bound > 0; tightest slack {worst}")
