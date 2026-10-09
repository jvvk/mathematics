"""Independent integer-colour formulation. Outside the patch remains free.

The only known empty sites are beyond an extremal supporting line. Constraints
on the outer square boundary are omitted, so UNSAT is a global obstruction.
"""
import json
import time
from pathlib import Path
import z3


def model(triple, radius, normal=(0, 1)):
    nx, ny = normal
    def allowed(x, y):
        dot = nx * x + ny * y
        return dot < 0 or (dot == 0 and x <= 0)
    points = [(x, y) for x in range(-radius, radius + 1)
              for y in range(-radius, radius + 1) if allowed(x, y)]
    cells = {p: z3.Int("v_%s_%s" % p) for p in points}
    s = z3.Solver()
    s.set(timeout=10000)
    for (x, y), value in cells.items():
        s.add(value >= 0, value <= 3)
        if abs(x) == radius or abs(y) == radius:
            continue
        for color, required in enumerate(triple, 1):
            terms = []
            for xx in range(x - 1, x + 2):
                for yy in range(y - 1, y + 2):
                    if (xx, yy) != (x, y) and (xx, yy) in cells:
                        terms.append(z3.If(cells[xx, yy] == color % 3 + 1, 1, 0))
            s.add(z3.Implies(value == color, z3.Sum(terms) == required))
    s.add(cells[0, 0] != 0)
    return s, cells


if __name__ == "__main__":
    for triple, radius, normal in [((1, 1, 2), 4, (0, 1)), ((1, 3, 6), 6, (0, 1)),
                                  ((1, 4, 5), 4, (0, 1)), ((1, 6, 3), 6, (0, 1)),
                                  ((2, 3, 4), 8, (1, 1))]:
            s, cells = model(triple, radius, normal)
            start = time.monotonic()
            result = str(s.check())
            record = dict(triple=triple, radius=radius, normal=normal, result=result,
                          seconds=time.monotonic() - start)
            if result == "sat":
                m = s.model()
                record["patch"] = [(x, y, "ABC"[m.eval(v).as_long() - 1])
                                   for (x, y), v in cells.items() if m.eval(v).as_long()]
            else:
                path = Path("smt")
                path.mkdir(exist_ok=True)
                (path / ("patch-%s-%s-%s.smt2" % ("-".join(map(str, triple)), *normal))).write_text(s.to_smt2())
            with open("independent.jsonl", "a") as f:
                f.write(json.dumps(record) + "\n")
            print(json.dumps({k: v for k, v in record.items() if k != "patch"}), flush=True)
