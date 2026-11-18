"""Compute each step of proof.md (Finch Conjecture 23) on every k <= KMAX with a capture point and assert
it. Independent of capture.c: plain simulation, run detection, pre-period from the definition. The set of
capturing k <= 60 is asserted exactly (Codex's independent full-orbit check confirms that the remaining k
never capture, so the step cutoff hides nothing)."""

KMAX, STEPS = 60, 200_000
CAPTURING = [2, 3, 6, 7, 10, 11, 14, 15, 19, 22, 26, 27, 30, 31, 34, 38, 39, 43, 46, 47, 54, 58, 59]


def seq(k, N):
    x = [None] + [0] * (k - 1) + [1]
    while len(x) <= N:
        n = len(x)
        x.append((x[n - 1] + (1 if x[n - k] else 0)) % 3)
    return x


def capture(k, x):
    G = -(-(k - 1) // 4)
    zeros = [n for n in range(k + 1, len(x)) if x[n] == 0]
    for i in range(len(zeros) - G):
        if all(zeros[i + j + 1] - zeros[i + j] == 4 for j in range(G)):
            return zeros[i + G], G
    return None, G


def preperiod(x, upto):
    mis = [n for n in range(5, upto + 1) if x[n] != x[n - 4]]
    return max(mis) - 4 if mis else 0


def check(k):
    x = seq(k, STEPS)
    z, G = capture(k, x)
    if z is None:
        return None
    b = [None] + [1 if v else 0 for v in x[1:]]
    s = z - 4 * G
    mu = preperiod(x, z + 8 * k)
    assert all(x[n] == x[n - 4] for n in range(z + 1, z + 8 * k)), "capture criterion"
    if k == 2:
        assert (z, mu) == (9, 0), ("k=2 exception", z, mu)
        return z - mu
    if k == 3:
        assert z - mu == 6
        return z - mu
    t = (k - 2) // 4 if k % 4 == 2 else (k - 3) // 4
    assert G == t + 1 and z == s + 4 * t + 4
    # Step 1: forced values of b before the run
    if k % 4 == 2:
        assert all(b[p] == 1 for p in range(s - k + 4, s + 3, 4)), "k=2 mod 4, d_{m+4}"
        assert all(b[p] == 1 for p in range(s - k + 1, s, 4)), "k=2 mod 4, d_{m+1}"
        assert all(b[p] + b[p + 1] == 1 for p in range(s - k + 2, s + 1, 4)), "k=2 mod 4, pairs"
    else:
        assert all(b[p] == 1 for p in range(s - k + 4, s + 2, 4)), "k=3 mod 4, d_{m+4}"
        assert all(b[p] == 1 for p in range(s - k + 1, s - 1, 4)), "k=3 mod 4, d_{m+1}"
        assert all(b[p] + b[p + 1] == 1 for p in range(s - k + 2, s, 4)), "k=3 mod 4, pairs"
    # Step 2
    assert s >= 2 * k - 1, ("Step 1 of the note: s >= 2k - 1", k, s)
    # Step 3
    assert x[z - 2] == (1 if k % 4 == 2 else 2), "Step 3"
    # Step 4
    if k % 4 == 2:
        assert b[s - 4] == 1 and x[z - 6] == 2, "Step 4 (k=2 mod 4)"
    else:
        assert b[s - 4] == 1 and b[s - 5] == 0 and x[z - 6] == 1, "Step 4 (k=3 mod 4)"
    assert z - mu == 6, ("Theorem", k, z, mu)
    return z - mu


def main():
    done = {}
    for k in range(2, KMAX + 1):
        if k % 4 in (2, 3):
            r = check(k)
            if r is not None:
                done[k] = r
    assert done[2] == 9 and all(v == 6 for k, v in done.items() if k >= 3)
    assert sorted(done) == CAPTURING, sorted(done)
    print("ALL CHECKS PASS: z - mu = 6 for", sorted(k for k in done if k >= 3), "; k = 2 gives", done[2])


if __name__ == "__main__":
    main()
