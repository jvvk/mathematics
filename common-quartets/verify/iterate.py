"""The iterated cell-lemma argument (PROOF.md) as an algorithm: from k trees on n >= 2*3^(k-1)+1 leaves, return a
quartet ab|cd displayed by all. Run on random trees; any failure (step fails, or quartet not common) is an assert."""
import random
import sys
from math import ceil

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from quartets import quartet_map, splits  # noqa: E402

STEP = 3  # mutate to 2 to check the harness notices


def rand_tree(labels: list[int], rng: random.Random):
    t = (labels[0], (labels[1], labels[2]))
    for v in labels[3:]:
        paths = []
        def walk(s, p=()):
            paths.append(p)
            if not isinstance(s, int):
                for i, c in enumerate(s):
                    walk(c, p + (i,))
        walk(t[1])
        p = rng.choice(paths)
        def ins(s, p):
            if not p:
                return (s, v)
            l = list(s); l[p[0]] = ins(s[p[0]], p[1:]); return tuple(l)
        t = (t[0], ins(t[1], p))
    return t


def restricted_splits(t, U: set[int]) -> list[tuple[set[int], set[int]]]:
    out = []
    for S in splits(t):
        A = set(S) & U
        if A and A != U:
            out.append((A, U - A))
    return out


def run(trees, n: int) -> tuple:
    # two-tree start: L1 on T1, then the step
    sp = [(A, B) for A, B in restricted_splits(trees[0], set(range(n))) if len(A) >= n / 3 and len(B) >= n / 3]
    A, B = sp[0]
    X, Y = A, B
    for i, T in enumerate(trees[1:], start=1):
        m = min(len(X), len(Y))
        if i > 1:  # the two-tree start uses T1's split of all of [n] untrimmed (cells >= n/6)
            X, Y = set(sorted(X)[:m]), set(sorted(Y)[:m])
        U = X | Y
        C, D = next((C, D) for C, D in restricted_splits(T, U) if len(C) >= len(U) / 3 and len(D) >= len(U) / 3)
        need = ceil(m / STEP) if i > 1 else ceil(n / 6)
        for P, Q in ((X & C, Y & D), (X & D, Y & C)):
            if len(P) >= need and len(Q) >= need:
                X, Y = P, Q
                break
        else:
            raise AssertionError(f"step {i}: no opposite cells of size {need}")
    a, b = sorted(X)[:2]
    c, d = sorted(Y)[:2]
    Q = frozenset([a, b, c, d])
    want = frozenset([frozenset([a, b]), frozenset([c, d])])
    assert all(quartet_map(T)[Q] == want for T in trees), "not common"
    return (a, b, c, d)


if __name__ == "__main__":
    rng = random.Random(2026)
    for k, trials in ((2, 300), (3, 200), (4, 40)):
        n = 2 * 3 ** (k - 1) + 1
        for _ in range(trials):
            trees = []
            for _ in range(k):
                lab = list(range(n)); rng.shuffle(lab)
                trees.append(rand_tree(lab, rng))
            run(trees, n)
        print(f"k={k}, n={n}: {trials} random families, argument produced a common quartet every time")
