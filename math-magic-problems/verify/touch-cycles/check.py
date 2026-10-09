"""Independent checker for Friedman #24; no solver imports."""
from collections import Counter


def check(cells, triple):
    points = {}
    for x, y, color in cells:
        assert color in "ABC", (x, y, color)
        assert (x, y) not in points, (x, y)
        points[x, y] = color
    populations = Counter(points.values())
    assert all(populations[c] for c in "ABC"), populations
    violations = []
    for (x, y), color in points.items():
        next_color = "BCA"["ABC".index(color)]
        count = sum(points.get((x + dx, y + dy)) == next_color
                    for dx in (-1, 0, 1) for dy in (-1, 0, 1)
                    if dx or dy)
        required = triple["ABC".index(color)]
        if count != required:
            violations.append((x, y, color, count, required))
    assert not violations, violations
    return dict(populations)


if __name__ == "__main__":
    import json
    import sys
    data = json.load(open(sys.argv[1]))
    print(check(data["cells"], data["triple"]))
