"""Exact feasibility of every coefficient condition in a finite Frobenius truncation.

Unlike a fixed digit search, this keeps the full affine Z_p lattice of solutions.
Every row is imposed, including rows requiring more digits than the requested
reporting precision.  A nonempty lattice certifies a finite truncation only.
"""
from math import gcd
from functools import reduce
from sympy import Matrix
from sympy.matrices.normalforms import hermite_normal_form
from frob_struct import F, vp, modp, structure, cyk, frob_P, plog


def lattice(A, p, n=4):
    base = [F(0)] * (n - 1)
    basis = Matrix.eye(n - 1)
    imposed = 0
    for row in A:
        for vec in row:
            const = vec[0] + sum(vec[j + 1] * base[j] for j in range(n - 1))
            coeff = [sum(vec[j + 1] * int(basis[j, k]) for j in range(n - 1))
                     for k in range(n - 1)]
            pivot = min(range(n - 1), key=lambda k: vp(coeff[k], p))
            v = vp(coeff[pivot], p)
            if v >= 0:
                if vp(const, p) < 0:
                    return None
                continue
            if vp(const, p) < v:
                return None
            s = -v
            modulus = p ** s
            rhs = modp(-const / coeff[pivot], p, s)
            old = basis[:, pivot]
            base = [base[j] + int(old[j]) * rhs for j in range(n - 1)]
            for k in range(n - 1):
                if k != pivot:
                    ratio = modp(coeff[k] / coeff[pivot], p, s)
                    basis[:, k] -= old * ratio
            basis[:, pivot] = old * modulus
            basis = hermite_normal_form(basis)
            # Keep an integer representative in the fundamental parallelepiped.
            coordinates = basis.inv() * Matrix(base)
            shifts = Matrix([int(c // 1) for c in coordinates])
            reduced = Matrix(base) - basis * shifts
            base = [F(int(c.p), int(c.q)) for c in reduced]
            imposed += 1
    # Independent direct verification of the entire affine lattice.
    for row in A:
        for vec in row:
            assert vp(vec[0] + sum(vec[j + 1] * base[j] for j in range(n - 1)), p) >= 0
            for k in range(n - 1):
                assert vp(sum(vec[j + 1] * int(basis[j, k]) for j in range(n - 1)), p) >= 0
    return base, basis, imposed


def run(p, R):
    from sympy import legendre_symbol
    cyk.E = 4
    T = cyk.T
    Lq = [T**3, -4*(2*T+1)*(5*T**2+5*T+2), 48*(T+1)*(3*T+2)*(3*T+4)]
    a = frob_P(Lq, R)
    coef = [[a[N][j] for j in range(4)] for N in range(R + 1)]
    A = structure(coef, p, R, 4)
    result = lattice(A, p)
    if result is None:
        return {"p": p, "R": R, "feasible": False}
    base, basis, imposed = result
    first_step = reduce(gcd, (int(basis[0, k]) for k in range(3)))
    s = vp(first_step, p)
    cp = int(legendre_symbol(2, p)) * 2 ** ((p - 1) // 2)
    predicted = modp(plog(cp, p, s + 3) / p, p, s)
    return {"p": p, "R": R, "feasible": True, "alpha1_precision": s,
            "alpha1_residue": modp(base[0], p, s), "predicted": predicted,
            "base": [str(v) for v in base], "basis": [list(map(int, basis.row(i))) for i in range(3)],
            "imposed_rows": imposed}


if __name__ == "__main__":
    import sys, json
    if len(sys.argv) == 3:
        print(json.dumps(run(int(sys.argv[1]), int(sys.argv[2])), indent=2))
    else:
        print(json.dumps([run(p, R) for p, R in [(5, 30), (7, 40), (11, 60), (13, 70), (17, 80)]], indent=2))
