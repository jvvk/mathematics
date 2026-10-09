"""Draw the 14-square tiling of 697 x 611 as TikZ, after checking cell by cell that it tiles the rectangle.

Run from this directory: python3 make_fig.py   (standard library only)
"""

from pathlib import Path

W, H = 697, 611
SQUARES = [
    (0, 0, 371),
    (371, 0, 326),
    (371, 326, 41),
    (412, 326, 285),
    (371, 367, 4),
    (375, 367, 37),
    (0, 371, 240),
    (240, 371, 68),
    (308, 371, 34),
    (342, 371, 33),
    (342, 404, 35),
    (377, 404, 35),
    (308, 405, 34),
    (240, 439, 172),
]


def check() -> None:
    covered = bytearray(W * H)
    for x, y, s in SQUARES:
        assert 0 <= x and x + s <= W and 0 <= y and y + s <= H
        for yy in range(y, y + s):
            row = yy * W
            for xx in range(x, x + s):
                assert not covered[row + xx], "overlap"
                covered[row + xx] = 1
    assert all(covered), "gap"


def tikz() -> str:
    k = 10.0 / W
    out = [r"\begin{tikzpicture}"]
    for x, y, s in SQUARES:
        out.append(
            rf"\filldraw[fill=black!6,draw=black,line width=0.5pt] ({x * k:.4f},{y * k:.4f}) rectangle ({(x + s) * k:.4f},{(y + s) * k:.4f});"
        )
        if s >= 30:
            size = r"\small" if s >= 100 else r"\tiny"
            out.append(
                rf"\node[font={size}] at ({(x + s / 2) * k:.4f},{(y + s / 2) * k:.4f}) {{{s}}};"
            )
    out.append(rf"\draw[line width=1.2pt] (0,0) rectangle ({W * k:.4f},{H * k:.4f});")
    out.append(r"\end{tikzpicture}")
    return "\n".join(out)


if __name__ == "__main__":
    check()
    (Path(__file__).resolve().parent / "fig_tiling.tex").write_text(tikz() + "\n")
    print("checked 697 x 611 cell by cell; wrote fig_tiling.tex")
