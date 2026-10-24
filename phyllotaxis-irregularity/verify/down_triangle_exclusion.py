"""Theorem B: no triangle on a down vector in the first transition (Lemma 6.1 and Section 6).

Runs the first transition from F(beta, eps) on a grid of beta, eps (both signs) and c < 0 and checks, at every
step of the (2,2) phase where a triangle on a down vector is valid:
  words 1/3 (the next vector is up): the triangle on that up vector is valid and no higher (Lemma 6.1);
  words 2/4 (the next vector is down): the rhombus is valid and lower by at least 0.45 b|c| (the bound b|c|/2
  up to higher-order terms);
and that every run reaches (3,2) with two triangles on up vectors and no pentagon. Two planted claims that are
false (a words 2/4 bound of 0.55 b|c|, a words 1/3 margin of 0.01|c|) must be rejected. Exits nonzero on any
failure. Uses the simulator helpers of transition_scaling.py and seed_convention.py.
Run: python3 down_triangle_exclusion.py   (about two minutes)
"""
from __future__ import annotations
import math, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from transition_scaling import tangent_up, parastichy
from seed_convention import consistent_front

Disk = tuple[float, float, float]


def candidates(F: list[Disk], b0: float, c: float) -> list[tuple[Disk, int, int, bool, bool]]:
    """(apex, first parent, gap, valid, on a down vector) for gaps 0 (triangle), 1 (rhombus), 2 (pentagon)."""
    N, out = len(F), []
    for i in range(N):
        for g in range(min(3, N - 1)):
            j = (i + g + 1) % N
            A = F[i]
            C = F[j] if j > i else (F[j][0] + 1.0, F[j][1], F[j][2])
            Q = tangent_up(A, C, b0, c)
            if Q is None:
                continue
            ok = all(math.hypot(P[0] + s - Q[0], P[1] - Q[1]) >= (P[2] + Q[2]) / 2 - 1e-11
                     for k, P in enumerate(F) if k not in (i, j) for s in (-1.0, 0.0, 1.0))
            out.append((Q, i, g, ok, g == 0 and C[1] < A[1]))
    return out


def first_transition(beta: float, eps: float, c: float):
    """Yields per-run results: list of (kind, value) comparisons and the outcome."""
    pts, b0 = consistent_front(beta, eps, c)
    F = sorted([(p[0] % 1.0, p[1], p[2]) for p in pts])
    comps: list[tuple[str, float, bool]] = []
    triangles_on_down = 0
    for _ in range(int(40 / abs(c))):
        cs = candidates(F, b0, c)
        best = min((x for x in cs if x[3]), key=lambda x: x[0][1])
        if best[4]:
            triangles_on_down += 1
        N = len(F)
        if parastichy(F) == (2, 2):
            for T in cs:
                if not (T[4] and T[3]):
                    continue
                i = T[1]
                nxt_down = F[(i + 2) % N][1] < F[(i + 1) % N][1] if (i + 2) % N != (i + 1) % N else False
                if nxt_down:   # words 2/4: rhombus on (B, E)
                    R = next(x for x in cs if x[1] == (i + 1) % N and x[2] == 1)
                    comps.append(("w24", (T[0][1] - R[0][1]) / (F[i][2] * abs(c)), R[3]))
                else:          # words 1/3: up triangle on (B, E)
                    P = next(x for x in cs if x[1] == (i + 1) % N and x[2] == 0)
                    comps.append(("w13", (T[0][1] - P[0][1]) / abs(c), P[3]))
        Q, i, g = best[0], best[1], best[2]
        removed = {(i + t + 1) % N for t in range(g)}
        F = sorted([F[k] for k in range(N) if k not in removed] + [(Q[0] % 1.0, Q[1], Q[2])], key=lambda p: p[0])
        if g >= 2:
            return comps, triangles_on_down, "pentagon"
        if parastichy(F) == (3, 2):
            return comps, triangles_on_down, "reached (3,2)"
    return comps, triangles_on_down, "did not finish"


def main() -> int:
    fails, w24, w13, runs = 0, [], [], 0
    for beta in (0.36, 0.42, 0.48, 0.523):
        for eps in (-0.01, -0.005, 0.0, 0.002, 0.005, 0.01):
            for c in (-0.0025, -0.00125, -0.0005):
                comps, down, outcome = first_transition(beta, eps, c)
                runs += 1
                if outcome != "reached (3,2)" or down:
                    print(f"FAIL beta={beta} eps={eps} c={c}: {outcome}, {down} triangles on down vectors")
                    fails += 1
                for kind, v, competitor_valid in comps:
                    (w24 if kind == "w24" else w13).append(v)
                    if not competitor_valid:
                        print(f"FAIL beta={beta} eps={eps} c={c}: {kind} competitor invalid while the down triangle is valid")
                        fails += 1
    print(f"{runs} runs; words 2/4: {len(w24)} valid down triangles, min (T-R)/(b|c|) = {min(w24):.4f}; "
          f"words 1/3: {len(w13)}, min (T-P)/|c| = {min(w13):.4f}")
    checks = [("words 2/4 gap >= 0.45 b|c|", min(w24) >= 0.45, True),
              ("words 1/3: down triangle never lower", min(w13) >= 0.0, True),
              ("planted: words 2/4 gap >= 0.55 b|c|", min(w24) >= 0.55, False),
              ("planted: words 1/3 margin >= 0.01|c|", min(w13) >= 0.01, False)]
    for name, holds, expected in checks:
        ok = holds == expected
        print(("PASS " if ok else "FAIL ") + name + ("" if expected else " (must be rejected)"))
        fails += not ok
    print("ALL CHECKS PASSED" if not fails else f"{fails} FAILURES")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
