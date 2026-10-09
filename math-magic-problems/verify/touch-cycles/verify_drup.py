"""Small independent DRUP verifier using only the Python standard library.

Every addition must follow by reverse unit propagation. Deletions can safely
be ignored: retaining already justified clauses only strengthens the database.
"""
from pathlib import Path
import json
import sys
import time

if not __debug__:
    raise RuntimeError("Verification requires assertions; run Python without -O.")


def conflict_by_unit_propagation(clauses, assumptions):
    assignment = {}
    for literal in assumptions:
        variable, value = abs(literal), literal > 0
        if variable in assignment and assignment[variable] != value:
            return True
        assignment[variable] = value
    while True:
        changed = False
        for clause in clauses:
            remaining = []
            satisfied = False
            for literal in clause:
                value = assignment.get(abs(literal))
                if value is None:
                    remaining.append(literal)
                elif value == (literal > 0):
                    satisfied = True
                    break
            if satisfied:
                continue
            if not remaining:
                return True
            if len(remaining) == 1:
                literal = remaining[0]
                assignment[abs(literal)] = literal > 0
                changed = True
        if not changed:
            return False


def verify(stem):
    header = None
    clauses = []
    for line in stem.with_suffix(".cnf").read_text().splitlines():
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            _, kind, variables, count = line.split()
            assert kind == "cnf"
            header = (int(variables), int(count))
        else:
            literals = list(map(int, line.split()))
            assert literals[-1] == 0 and 0 not in literals[:-1]
            clauses.append(literals[:-1])
    assert header is not None and header[1] == len(clauses)
    assert all(abs(v) <= header[0] for c in clauses for v in c)
    # Check that the input is exactly the documented geometrical model rather
    # than an arbitrary unsatisfiable formula. certify.build has no dependency
    # on a solver: it merely lists direct cardinality clauses.
    from certify import build
    metadata = json.loads(stem.with_suffix(".json").read_text())
    points, variables, expected = build(metadata["triple"], metadata["radius"], metadata["normal"])
    assert header[0] == len(variables) and clauses == expected
    assert metadata["points"] == len(points)
    original_count = len(clauses)
    additions = 0
    empty_verified = False
    for number, line in enumerate(stem.with_suffix(".drup").read_text().splitlines(), 1):
        if not line or line.startswith("d"):
            continue
        literals = list(map(int, line.split()))
        assert literals[-1] == 0 and 0 not in literals[:-1]
        clause = literals[:-1]
        assert conflict_by_unit_propagation(clauses, [-v for v in clause]), (stem, number)
        clauses.append(clause)
        additions += 1
        if not clause:
            empty_verified = True
            break
    assert empty_verified, "No verified empty clause"
    return dict(original_clauses=original_count, verified_additions=additions)


if __name__ == "__main__":
    # The checker must reject an unjustified contradiction and accept a simple
    # unit contradiction, including contradiction among assumptions.
    assert not conflict_by_unit_propagation([[1, 2]], [])
    assert conflict_by_unit_propagation([[1], [-1]], [])
    assert conflict_by_unit_propagation([[1, 2], [-1]], [-2])
    assert conflict_by_unit_propagation([], [1, -1])
    paths = [Path(p) for p in sys.argv[1:]] or sorted(Path("certificates").glob("*.cnf"))
    for path in paths:
        start = time.monotonic()
        result = verify(path)
        print(path.stem, result, "seconds=%.3f" % (time.monotonic() - start), flush=True)
