"""Mutation test for slab_search.py: allow k x i x j boxes (any i, j) instead of k x ik x jk slabs.
The mutant must find tilings of cubes that slab_search.py proves impossible, so the negative answers
are not vacuous. Usage: python3 slab_mutant.py"""
import pathlib

src = (pathlib.Path(__file__).parent / "slab_search.py").read_text()
mut = src.replace("for p in permutations((k, i * k, j * k))", "for p in permutations((k, i, j))")
mut = mut.replace("max(dims) // k + 1", "max(dims) + 1")
assert mut != src
ns = {"__name__": "mutant"}
exec(compile(mut, "slab_search_mutant", "exec"), ns)
for n, s in ((4, 5), (4, 6)):
    t = ns["tile"](n, (s, s, s))
    assert t, f"mutant should tile the {s}-cube for n = {n}"
    print(f"mutant tiles the {s}-cube with n = {n} (the real search says impossible): caught")
