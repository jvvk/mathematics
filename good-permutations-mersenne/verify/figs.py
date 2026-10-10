"""TikZ fragments for the note (written to ../note/figs/).

fig_pairs.tex   the asker's permutation for n = 31 as bars, the middle bar and one linked pair;
fig_blocks.tex  every block (start, length) of the asker's permutation for n = 15 and n = 31,
                with the blocks of integer average filled: only prefixes of length 3 and 5 (n = 15).
"""
from pathlib import Path

from check import bad_blocks, construction

_ROOT = Path(__file__).resolve().parent.parent
OUT = _ROOT / ("paper" if (_ROOT / "paper").exists() else "note") / "figs"


def pairs() -> str:
    n, q = 31, 16
    a = construction(n)
    sx, sy, bw = 0.42, 0.11, 0.3
    out = [f"\\draw[book/thin] (0.1,0) -- ({(n + 1) * sx:.2f},0);"]
    for t in range(1, n + 1):
        col = "black!85" if t == q else ("copper" if t < q else "steel")
        x = t * sx
        out.append(f"\\fill[{col}] ({x - bw / 2:.3f},0) rectangle ({x + bw / 2:.3f},{a[t - 1] * sy:.3f});")
    for t in (2, 2 + q, q):
        out.append(f"\\node[above, font=\\scriptsize] at ({t * sx:.3f},{a[t - 1] * sy:.3f}) {{{a[t - 1]}}};")
    x1, x2 = 2 * sx, (2 + q) * sx
    out.append(f"\\draw[inkmuted] ({x1:.3f},-0.12) .. controls ({x1:.3f},-0.9) and ({x2:.3f},-0.9) .. ({x2:.3f},-0.12);")
    for t in (1, 16, 31):
        out.append(f"\\node[below, font=\\scriptsize] at ({t * sx:.3f},-0.02) {{{t}}};")
    return "\n".join(out) + "\n"


def blocks(n: int, cell: float) -> str:
    a = construction(n)
    bad = bad_blocks(a)
    out = []
    for L in range(2, n):
        for s in range(1, n - L + 2):
            x, y = (s - 1) * cell, (L - 2) * cell
            style = "fill=copper" if (s, L) in bad else "fill=black!8"
            out.append(f"\\path[{style}] ({x:.3f},{y:.3f}) rectangle +({cell * 0.9:.3f},{cell * 0.9:.3f});")
    return "\n".join(out) + "\n"


if __name__ == "__main__":
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "pairs31.tex").write_text(pairs())
    assert bad_blocks(construction(15)) == {(1, 3), (1, 5)}
    assert not bad_blocks(construction(31))
    (OUT / "blocks15.tex").write_text(blocks(15, 0.36))
    (OUT / "blocks31.tex").write_text(blocks(31, 0.18))
    print("figures written")
