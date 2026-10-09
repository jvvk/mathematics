"""Produce CNF and DRUP certificates for extremal neighbourhood obstructions.

Cardinality clauses use direct combinations (no auxiliary variables).
Run verify_drup.py separately to check the certificates without a SAT solver.
"""
import itertools
import json
from pathlib import Path


def build(triple, radius, normal=(0, 1)):
    nx, ny = normal
    points = [(x, y) for y in range(-radius, radius + 1)
              for x in range(-radius, radius + 1)
              if nx * x + ny * y < 0 or (nx * x + ny * y == 0 and x <= 0)]
    variables = {(x, y, c): 3 * i + c + 1 for i, (x, y) in enumerate(points)
                 for c in range(3)}
    clauses = []
    for x, y in points:
        for c, d in itertools.combinations(range(3), 2):
            clauses.append([-variables[x, y, c], -variables[x, y, d]])
        if abs(x) == radius or abs(y) == radius:
            continue
        for c, degree in enumerate(triple):
            center = variables[x, y, c]
            ns = [variables[xx, yy, (c + 1) % 3]
                  for xx in range(x - 1, x + 2) for yy in range(y - 1, y + 2)
                  if (xx, yy) != (x, y) and (xx, yy, (c + 1) % 3) in variables]
            if len(ns) < degree:
                clauses.append([-center])
                continue
            for subset in itertools.combinations(ns, degree + 1):
                clauses.append([-center] + [-v for v in subset])
            for subset in itertools.combinations(ns, len(ns) - degree + 1):
                clauses.append([-center] + list(subset))
    clauses.append([variables[0, 0, c] for c in range(3)])
    return points, variables, clauses


if __name__ == "__main__":
    from pysat.solvers import Glucose3
    out = Path("certificates")
    out.mkdir(exist_ok=True)
    for triple, radius, normal in [((1, 3, 6), 6, (0, 1)), ((1, 4, 5), 4, (0, 1)),
                                   ((1, 6, 3), 6, (0, 1)), ((2, 3, 4), 8, (1, 1))]:
        points, variables, clauses = build(triple, radius, normal)
        stem = "-".join(map(str, triple))
        solver = Glucose3(with_proof=True)
        solver.append_formula(clauses)
        assert solver.solve() is False
        proof = solver.get_proof()
        # Keep additions through the first empty clause. Deletions are optional
        # for this proof system and our checker deliberately retains clauses.
        trimmed = []
        for line in proof:
            if line.startswith("d"):
                continue
            trimmed.append(line)
            if line == "0":
                break
        proof = trimmed
        # Some solvers omit the final empty line when contradiction is found
        # during clause loading. The independent checker still verifies it.
        if not proof or proof[-1] != "0":
            proof.append("0")
        (out / (stem + ".cnf")).write_text("p cnf %d %d\n" % (len(variables), len(clauses)) +
                                           "\n".join(" ".join(map(str, c)) + " 0" for c in clauses) + "\n")
        (out / (stem + ".drup")).write_text("\n".join(proof) + "\n")
        (out / (stem + ".json")).write_text(json.dumps(dict(triple=triple, radius=radius, normal=normal,
                                                        points=len(points), variables=len(variables),
                                                        clauses=len(clauses), proof_lines=len(proof)), indent=2) + "\n")
        print(stem, len(points), len(clauses), len(proof), flush=True)
