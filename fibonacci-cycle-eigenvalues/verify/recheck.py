"""Independent recheck (shares no code with certify.py / scan.py / spec.py): works directly with Laplacian matrices.
1. Numerically (numpy eigvalsh): deficit d(n) for weights (1,2), n <= 700, equals F_k at n = 4F_k, 1 at n = 33, 53, 106,
   and 0 otherwise; same for weights (3, 7/5) with no sporadic n.
2. Numerically: at n = 4F_k the double eigenvalues equal the spectrum of the F_k-cycle twisted by i (Theorem 1.1).
3. Exactly (rank of L_n - I over Q, python-flint fmpq_mat): 1 is a double eigenvalue of L_n, weights (1,2), for
   n < 610 exactly when n in {20, 33, 53, 106} (Theorem 1.2, finite part).
Numerical gaps: genuine doubles agree to < 1e-11, and the closest distinct pair (n = 241, gap 8e-8 near 0.00084)
is > 1e-9; any gap in [1e-11, 1e-9] fails the run. Exits nonzero on any failure."""
import numpy as np, flint
from fractions import Fraction

def fib_letters(n):                      # Fibonacci word via the Sturmian formula, not by substitution
    phi = (1 + 5 ** 0.5) / 2
    return ["B" if int((i + 2) / phi ** 2) - int((i + 1) / phi ** 2) == 1 else "A" for i in range(n)]

def weights(n, a, b): return [a if c == "A" else b for c in fib_letters(n)]

def laplacian(ws, twist=1.0):
    n = len(ws); L = np.zeros((n, n), dtype=complex)
    for i, w in enumerate(ws):
        j = (i + 1) % n; z = twist if j == 0 else 1.0
        L[i, i] += w; L[j, j] += w; L[i, j] -= w * z; L[j, i] -= w * np.conj(z)
    return L

LO, HI = 1e-11, 1e-9                      # gaps < LO count as doubles, > HI as distinct; none may fall between
def deficit(ev):
    g = np.diff(np.sort(ev))
    assert not np.any((g >= LO) & (g <= HI)), ("ambiguous gap", g[(g >= LO) & (g <= HI)])
    return int(np.sum(g < LO))

assert "".join(fib_letters(12)) == "ABAABABAABAA"
F = [1, 1]
while F[-1] < 1000: F.append(F[-1] + F[-2])
four = {4 * f: f for f in F[3:]}
for (a, b, spor) in [(1.0, 2.0, {33, 53, 106}), (3.0, 1.4, set())]:
    for n in range(3, 701):
        d = deficit(np.linalg.eigvalsh(laplacian(weights(n, a, b))))
        want = four.get(n, 1 if n in spor else 0)
        assert d == want, (a, b, n, d, want)
    print(f"1. deficits for weights ({a},{b}), n<=700: OK")
for n, f in four.items():
    if n > 700: continue
    for (a, b) in [(1.0, 2.0), (3.0, 1.4)]:
        ev = np.sort(np.linalg.eigvalsh(laplacian(weights(n, a, b))))
        dbl = np.array([ev[i] for i in range(n - 1) if ev[i + 1] - ev[i] < LO])
        tw = np.sort(np.linalg.eigvalsh(laplacian(weights(f, a, b), twist=1j)))
        assert len(dbl) == f and np.allclose(dbl, tw, atol=1e-6), (n, a, b)
print("2. doubles at n=4F_k (<=700) = spectrum of the i-twisted F_k-cycle: OK")
hits = []
for n in range(3, 610):
    ws = weights(n, 1, 2); M = flint.fmpq_mat(n, n)
    for i, w in enumerate(ws):
        j = (i + 1) % n
        M[i, i] += w; M[j, j] += w; M[i, j] -= w; M[j, i] -= w
    for i in range(n): M[i, i] -= 1
    if n - M.rank() == 2: hits.append(n)
    assert n - M.rank() <= 2
assert hits == [20, 33, 53, 106], hits
print("3. exact: 1 is double for L_n (n<610) iff n in", hits, ": OK")
