"""Two proved necessary conditions for a genus-one curve with t_00 != 0.

1. Every centre-pair function is nonconstant (constant-offset Kummer covers).
2. Their four principal divisors are distinct up to sign (genus-five obstruction).

See CENTRE_DISTINCT.md for the proofs, valid in every degree. This script only
compares integer vectors; it invokes no numerical or algebraic solver.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path

HERE = Path(__file__).parent


def reason(cfg):
    rows = [tuple(c[i + 1] for c in cfg) for i in range(4)]
    if any(not any(r) for r in rows):
        return "constant centre-pair function"
    unoriented = [min(r, tuple(-x for x in r)) for r in rows]
    if len(set(unoriented)) != 4:
        return "repeated divisor up to sign"
    return "survives"


def line_root_counts():
    """Enumerate all collision parameters for the two line-pencil types.

    Each finite branch root is a rational affine function a*c+b. All possible
    changes of cardinality occur at pairwise equalities, so this is exhaustive.
    """
    from fractions import Fraction as Q

    pencils = {
        "axial": [(Q(a), Q(b)) for a, b in
                  [(0, 1), (0, -1), (1, 1), (1, -1), (-1, 1), (-1, -1)]],
        "diagonal": [(Q(a), Q(b)) for a, b in
                     [(0, 1), (0, -1), (1, 1), (1, -1)]]
                    + [(Q(1, 2), Q(1, 2)), (Q(1, 2), Q(-1, 2))],
    }
    for name, roots in pencils.items():
        special = set()
        for a, b in roots:
            for aa, bb in roots:
                if a != aa:
                    special.add((bb - b) / (a - aa))
        values = {str(c): len({a * c + b for a, b in roots})
                  for c in sorted(special)}
        assert 3 not in values.values()
        print(name, "special root counts:", values, "generic:", len(roots))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("degrees", nargs="*", type=int, default=[4, 5, 6])
    args = parser.parse_args()
    line_root_counts()
    for m in args.degrees:
        source = HERE / f"m{m}_survivors.json"
        data = json.loads(source.read_text())
        counts = Counter(reason(d["cfg"]) for d in data)
        out = [d for d in data if reason(d["cfg"]) == "survives"]
        target = HERE / f"m{m}_distinct_survivors.json"
        target.write_text(json.dumps(out, indent=2) + "\n")
        print(f"m={m}: input={len(data)}; {dict(sorted(counts.items()))}; output={len(out)}")
        print("  remaining group-law types:", dict(sorted(Counter(
            d["aug"].split(" N")[0] for d in out).items())))


if __name__ == "__main__":
    main()
