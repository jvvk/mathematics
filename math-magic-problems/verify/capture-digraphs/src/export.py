"""Write out/graphs.json (labelled arc lists of the five unsolved diagrams) and out/witness_u.json
(a vertex-labelled position realizing diagram u exactly, not merely up to isomorphism).

Vertex labels follow Friedman's hexagon drawings: 0 top-left, 1 top-right, 2 right, 3 bottom-right,
4 bottom-left, 5 left. Squares use chess notation with a1 at the lower-left corner of the box.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

from digraphs import UNSOLVED, all_classes, canon, is_2_regular
from realize import decide

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verify"))
from check import capture_graph  # noqa: E402

STATUS = {
    "f": "published none (DeVincentis); confirmed not realizable",
    "u": "published none (Thompson); REALIZABLE, witness in witness_u.json",
    "q": "open (?); not realizable",
    "r": "open (?); not realizable",
    "s": "open (?); not realizable",
}
LABELS = ["top-left", "top-right", "right", "bottom-right", "bottom-left", "left"]


def main() -> None:
    classes = all_classes(6)
    graphs = {}
    for k in "fqrsu":
        arcs = sorted(UNSOLVED[k])
        assert is_2_regular(arcs, 6)
        graphs[k] = {
            "figure": f"https://erich-friedman.github.io/mathmagic/1013/a6-2-{k}.gif",
            "class_index": classes.index(canon(arcs, 6)),
            "arcs": arcs,
            "status": STATUS[k],
        }
    (ROOT / "out/graphs.json").write_text(
        json.dumps({"vertex_labels": LABELS, "graphs": graphs}, indent=1) + "\n"
    )

    arcs = set(UNSOLVED["u"])
    verdict, types, pos, _ = decide(sorted(arcs), 6)
    assert verdict == "REALIZABLE"
    x0 = min(p[0] for p in pos)
    y0 = min(p[1] for p in pos)
    pos = [(x - x0, y - y0) for x, y in pos]
    assert capture_graph(types, pos) == arcs, "witness must realize u exactly, vertex for vertex"
    w = max(p[0] for p in pos) + 1
    h = max(p[1] for p in pos) + 1
    rows = []
    for y in reversed(range(h)):
        rows.append(" ".join(next((f"{types[i]}{i}" for i, p in enumerate(pos) if p == (x, y)), "..") for x in range(w)))
    witness = {
        "diagram": "u",
        "board": f"{w}x{h}",
        "vertices": [
            {"vertex": i, "label": LABELS[i], "piece": types[i], "square": "abcdefgh"[x] + str(y + 1)}
            for i, (x, y) in enumerate(pos)
        ],
        "diagram_rows_top_to_bottom": rows,
        "attacks": {str(a): sorted(b for (c, b) in arcs if c == a) for a in range(6)},
    }
    (ROOT / "out/witness_u.json").write_text(json.dumps(witness, indent=1) + "\n")
    print("\n".join(rows))


if __name__ == "__main__":
    main()
