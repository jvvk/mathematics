"""Write fig_blocks.tex: three block reversals, each as two rows of cells (1 dark, 0 light) with every block framed
in its own colour, so the reversal of the blocks is visible. Asserts that each pair has the same polynomial."""

import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent / "verify"))
from exact import charpoly

EXAMPLES = [  # (label, A, blocks, B)
    ("interleaving, $n=8$", "10", ["110", "010"], ""),
    ("Theorem R, $n=12$", "101", ["001", "100"], "000"),
    ("neither, $n=13$", "1", ["10101", "1000"], "101"),
]
COLS = ["rust", "inkblue", "sage"]


def row(word_parts, y, out):
    """word_parts: list of (string, colour or None). Draw cells from x = 0 at height y."""
    x = 0
    for s, col in word_parts:
        x0 = x
        for ch in s:
            fill = "ink" if ch == "1" else "paper"
            out.append(f"  \\fill[{fill}] ({x},{y}) rectangle ++(1,1);")
            out.append(f"  \\draw[gray!60] ({x},{y}) rectangle ++(1,1);")
            x += 1
        if col and s:
            out.append(
                f"  \\draw[{col},line width=1.6pt] ({x0}+0.06,{y}+0.06) rectangle ({x}-0.06,{y}+0.94);"
            )
    return x


def main():
    out = ["\\begin{tikzpicture}[x=0.36cm,y=0.36cm]"]
    y = 0
    for label, A, Ys, B in EXAMPLES:
        u = A + "".join(Ys) + B
        v = A + "".join(Ys[::-1]) + B
        assert charpoly(u) == charpoly(v) and v not in (u, u[::-1]), (u, v)
        cols = COLS[: len(Ys)]
        row([(A, None)] + list(zip(Ys, cols)) + [(B, None)], y, out)
        row([(A, None)] + list(zip(Ys[::-1], cols[::-1])) + [(B, None)], y - 1.3, out)
        out.append(
            f"  \\node[right,font=\\small] at ({len(u) + 0.6},{y - 0.15}) {{{label}}};"
        )
        out.append(
            f"  \\node[left,font=\\scriptsize\\ttfamily] at (-0.3,{y + 0.5}) {{{u}}};"
        )
        out.append(
            f"  \\node[left,font=\\scriptsize\\ttfamily] at (-0.3,{y - 0.8}) {{{v}}};"
        )
        y -= 3.6
    out.append("\\end{tikzpicture}")
    pathlib.Path(__file__).with_name("fig_blocks.tex").write_text("\n".join(out) + "\n")


if __name__ == "__main__":
    main()
