"""Integer low-rank factorisations V = A B of the witness Latin squares, for the Lean file Witness.lean.

A's columns are a Z-basis of the lattice spanned by V's columns (Hermite normal form), B the integer
coordinates. Prints Lean definitions (symbols 0..n-1, V = symbol + 1)."""
import sympy as sp
from sympy.matrices.normalforms import hermite_normal_form

W = {
    4: ["1234", "2143", "3412", "4321"],
    6: ["162534", "615243", "253416", "524361", "346152", "431625"],
    8: [[1 + (i ^ j) for j in range(8)] for i in range(8)],   # the XOR square of the question
}


def lean_mat(M, name, typ):
    rows = ", ".join("![" + ", ".join(str(x) for x in row) + "]" for row in M.tolist())
    return f"def {name} : Matrix (Fin {M.rows}) (Fin {M.cols}) {typ} := !![{'; '.join(', '.join(str(x) for x in row) for row in M.tolist())}]"


for n, rows in W.items():
    V = sp.Matrix([[int(c) for c in r] for r in rows]) if isinstance(rows[0], str) else sp.Matrix(rows)
    r = V.rank()
    H = hermite_normal_form(V)            # columns span the same lattice as V's columns
    A = H[:, [k for k in range(H.cols) if any(H[:, k])]]
    assert A.cols == r, (n, A.cols, r)
    B = (A.T * A).inv() * A.T * V          # exact coordinates
    assert all(x.is_integer for x in B), n
    assert A * B == V
    L = V - sp.ones(n, n)
    print(f"-- n = {n}, rank {r}")
    print(f"def L{n} : Matrix (Fin {n}) (Fin {n}) (Fin {n}) := !![" + "; ".join(", ".join(str(x) for x in row) for row in L.tolist()) + "]")
    print(lean_mat(A, f"A{n}", "ℤ"))
    print(lean_mat(B, f"B{n}", "ℤ"))


def xor_factor(k):
    """V = 1 + XOR on 2^k: columns in span(1, b_0, ..., b_{k-1}) (the question's construction)."""
    n = 2 ** k
    A = sp.Matrix([[1] + [(i >> r) & 1 for r in range(k)] for i in range(n)])
    B = sp.Matrix([[1 + j] + [2 ** r * (1 - 2 * ((j >> r) & 1)) for j in [j]] for j in range(n)])
    B = sp.Matrix([[1 + sum(2 ** r * ((j >> r) & 1) for r in range(k)) for j in range(n)]] +
                  [[2 ** r * (1 - 2 * ((j >> r) & 1)) for j in range(n)] for r in range(k)])
    V = sp.Matrix([[1 + (i ^ j) for j in range(n)] for i in range(n)])
    assert A * B == V
    print(f"-- XOR, n = {n}")
    print(lean_mat(A, f"X{n}", "ℤ"))
    print(lean_mat(B, f"Y{n}", "ℤ"))


for k in (2, 3):
    xor_factor(k)
