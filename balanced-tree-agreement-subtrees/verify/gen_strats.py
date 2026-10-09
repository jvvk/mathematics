"""Emit the (2,1) lookahead strategies as Lean `Strat` terms, by the recursion of strategies.py,
and check that their flattened forms are exactly the 42 strategies the certifier uses.

A Lean `Strat` at the pair (u, v) is one of
  stop                      use the pair (u, v)                         (not at the root)
  both false s0 s1          (u0, v0) by s0 and (u1, v1) by s1
  both true  s0 s1          (u0, v1) by s0 and (u1, v0) by s1
  sideT b s                 (u, vb) by s
  sideS b s                 (ub, v) by s
"""
from __future__ import annotations

from functools import lru_cache

from strategies import build

DS, DT = 2, 1


@lru_cache(None)
def strat(u: tuple, v: tuple, root: bool = False) -> tuple:
    """All strategies at (u, v) as (lean_term, flattened_terms), in strategies.py's order."""
    out = [] if root else [("Strat.stop", ((len(u) + len(v), u, v),))]
    su, sv = len(u) < DS, len(v) < DT
    if su and sv:
        for cross, (p, q) in ((False, ((0, 0), (1, 1))), (True, ((0, 1), (1, 0)))):
            A = strat(u + (p[0],), v + (p[1],))
            B = strat(u + (q[0],), v + (q[1],))
            out += [(f"(Strat.both {str(cross).lower()} {ta} {tb})", fa + fb) for ta, fa in A for tb, fb in B]
    if sv:
        for b in (0, 1):
            out += [(f"(Strat.sideT {str(bool(b)).lower()} {t})", f) for t, f in strat(u, v + (b,))]
    if su:
        for b in (0, 1):
            out += [(f"(Strat.sideS {str(bool(b)).lower()} {t})", f) for t, f in strat(u + (b,), v)]
    seen: dict = {}
    for t, f in out:
        seen.setdefault(tuple(sorted(f)), t)
    return tuple((t, k) for k, t in seen.items())


ours = strat((), (), True)
ref = build(DS, DT)
assert [k for _, k in ours] == list(ref), "flattened strategies differ from strategies.py"
print(f"{len(ours)} strategies, identical to strategies.py (same order)")
with open("strats21.lean.txt", "w") as fh:
    fh.write("/-- The 42 strategies of the (2,1) lookahead, in the certifier's order. -/\n")
    fh.write("def strategies21 : List Strat :=\n  [" + ",\n   ".join(t for t, _ in ours) + "]\n")
