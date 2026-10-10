"""Independent recheck of the symmetric claims of "Sixteen words cover all 15-bit strings", sharing no code with
cover.py (CP-SAT) or verify15.py.

Words of length 10 are grouped into orbits under complement and reversal (sizes 2 or 4). A symmetric set is a union
of orbits. It covers {0,1}^15 when every 15-bit string has a subsequence in it. We build the CNF ourselves (one
clause per 15-bit string, over the orbits with a member that is a subsequence of it), add a sequential-counter
encoding of "total size <= K" (each orbit counts size/2 half-units), and solve with Glucose 4 through PySAT.

Expected: K = 16 satisfiable (and the model is replayed as a cover), K = 15 unsatisfiable. With --proof, the K = 15
run writes a DRAT proof for an external checker.

    timeout 900 nice -n 15 ~/.venvs/main/bin/python recheck_sym.py [--proof out.drat]
"""
from __future__ import annotations

import argparse
import sys

from pysat.solvers import Solver

N, M = 15, 10
SOLVER = "glucose4"


def subseq_mask(y: int, m: int, n: int, contiguous: bool = False) -> list[int]:
    """All n-bit x (as ints, bit i = position i) containing the m-bit y as a subsequence: greedy matching."""
    yb = [(y >> i) & 1 for i in range(m)]
    out = []
    if contiguous:  # mutant: substring instead of subsequence
        return [x for x in range(1 << n) if any(all(((x >> (s + i)) & 1) == yb[i] for i in range(m))
                                                for s in range(n - m + 1))]
    for x in range(1 << n):
        j = 0
        for i in range(n):
            if j < m and ((x >> i) & 1) == yb[j]:
                j += 1
        if j == m:
            out.append(x)
    return out


def orbits(m: int) -> list[list[int]]:
    full = (1 << m) - 1
    rev = lambda y: int(format(y, f"0{m}b")[::-1], 2)
    seen, out = set(), []
    for y in range(1 << m):
        if y in seen:
            continue
        orb = sorted({y, y ^ full, rev(y), rev(y) ^ full})
        seen.update(orb)
        out.append(orb)
    return out


def build(K: int, n: int = N, m: int = M, extra: int = 0, contiguous: bool = False):
    orbs = orbits(m)
    covers_x: list[list[int]] = [[] for _ in range(1 << n)]
    for o, orb in enumerate(orbs):
        hit = set()
        for y in orb:
            hit.update(subseq_mask(y, m, n, contiguous))
        for x in hit:
            covers_x[x].append(o + 1)
    clauses = [c for c in covers_x]
    assert all(clauses), "some string is covered by no word at all"
    clauses = [list(c) for c in clauses]
    # weights in half-units: orbit of size s counts s/2; bound K words -> floor(K/2) half-units
    inputs = []
    for o, orb in enumerate(orbs):
        inputs += [o + 1] * (len(orb) // 2)
    cap = K // 2 + extra
    nv = len(orbs)
    # sequential counter (Sinz): s[i][j] = "at least j+1 of the first i+1 inputs are true", j < cap
    s = []
    for i, lit in enumerate(inputs):
        row = []
        for j in range(cap):
            nv += 1
            row.append(nv)
        s.append(row)
        clauses.append([-lit, row[0]])
        if i > 0:
            for j in range(cap):
                clauses.append([-s[i - 1][j], row[j]])
            for j in range(1, cap):
                clauses.append([-lit, -s[i - 1][j - 1], row[j]])
            clauses.append([-lit, -s[i - 1][cap - 1]])
    return orbs, clauses


def solve(K: int, proof: str | None = None, **kw):
    orbs, clauses = build(K, **kw)
    with Solver(name=SOLVER, bootstrap_with=clauses, with_proof=bool(proof)) as sv:
        sat = sv.solve()
        model = sv.get_model() if sat else None
        if proof and not sat:
            with open(proof, "w") as f:
                f.write("\n".join(sv.get_proof()) + "\n")
    chosen = [orbs[v - 1] for v in (model or []) if 0 < v <= len(orbs)]
    return sat, [y for orb in chosen for y in orb], clauses


def is_cover(words: list[int]) -> bool:
    cov = set()
    for y in words:
        cov.update(subseq_mask(y, M, N))
    return len(cov) == 1 << N


S16 = ("0000000000 0000000011 0000111110 0011001100 0011111111 0110000110 0110101001 0111110000 "
       "1000001111 1001010110 1001111001 1100000000 1100110011 1111000001 1111111100 1111111111").split()


def run(proof: str | None = None, **kw) -> None:
    # the published cover: words written left to right; bit i of the int is position i
    published = [sum(int(c) << i for i, c in enumerate(w)) for w in S16]
    assert len(set(published)) == 16 and is_cover(published), "published set is not a cover"
    full = (1 << M) - 1
    rev = lambda y: int(format(y, f"0{M}b")[::-1], 2)
    assert set(published) == {y ^ full for y in published} == {rev(y) for y in published}, "not symmetric"
    for i in range(16):
        assert not is_cover(published[:i] + published[i + 1:]), f"word {i} redundant"
    print("published 16-word set: a cover, closed under complement and reversal, minimal", flush=True)
    sat16, words, _ = solve(16, **kw)
    assert sat16 and len(words) <= 16 and is_cover(words), (sat16, len(words))
    print(f"K=16: satisfiable; a symmetric cover of size {len(words)} found and replayed", flush=True)
    sat15, _, cl = solve(15, proof, **kw)
    assert not sat15, "K=15 satisfiable"
    print(f"K=15: unsatisfiable ({len(cl)} clauses); no symmetric cover of size 15", flush=True)
    if proof:
        with open(proof.replace(".drat", ".cnf"), "w") as f:
            nv = max(abs(l) for c in cl for l in c)
            f.write(f"p cnf {nv} {len(cl)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in cl))
        print("wrote CNF and DRAT proof", flush=True)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--proof")
    ap.add_argument("--no-mutants", action="store_true")
    args = ap.parse_args()
    run(args.proof)
    if not args.no_mutants:
        for name, kw in {"counter allows one more half-unit": dict(extra=1),
                         "substring instead of subsequence": dict(contiguous=True)}.items():
            try:
                run(**kw)
            except AssertionError as e:
                print(f"rejected mutant: {name} ({e})", flush=True)
            else:
                sys.exit(f"UNDETECTED MUTANT: {name}")
        print("all 2 mutants rejected")
