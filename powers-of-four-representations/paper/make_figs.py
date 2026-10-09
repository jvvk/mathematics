"""Data for the note's figure: R_{A,3}(N) - R_{A,3}(N-1) for two sets A, by direct convolution.

  powers.dat:   A = N_0 minus {16, 64, 256, ...}; columns N, difference, lower bound N+1-3m-m^2.
  periodic.dat: A = {n : n mod 4 != 2} (density 3/4); columns N, difference.
"""
from pathlib import Path

OUT = Path(__file__).resolve().parent / "figs"


def r3(member: list[int]) -> list[int]:
    n = len(member)
    r2 = [sum(member[i] * member[k - i] for i in range(k + 1)) for k in range(n)]
    return [sum(r2[i] * member[k - i] for i in range(k + 1)) for k in range(n)]


def main() -> None:
    L = 300
    E = {4 ** (j + 2) for j in range(6)}
    a = [int(k not in E) for k in range(L + 1)]
    R = r3(a)
    rows = []
    for N in range(1, L + 1):
        m = sum(e <= N for e in E)
        d, lb = R[N] - R[N - 1], N + 1 - 3 * m - m * m
        assert d >= lb > 0
        rows.append(f"{N} {d} {lb}")
    (OUT / "powers.dat").write_text("N d lb\n" + "\n".join(rows) + "\n")
    L2 = 40
    b = [int(k % 4 != 2) for k in range(L2 + 1)]
    R2 = r3(b)
    drops = [N for N in range(1, L2 + 1) if R2[N] < R2[N - 1]]
    (OUT / "periodic.dat").write_text("N d\n" + "\n".join(f"{N} {R2[N] - R2[N - 1]}" for N in range(1, L2 + 1)) + "\n")
    print("powers: d >= bound > 0 for N <= 300; first values R3 =", R[:20])
    print("periodic 4n+2 removed: R3 =", R2[:12], "decreases at N =", drops[:10])


if __name__ == "__main__":
    main()
