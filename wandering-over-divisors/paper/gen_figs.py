"""Generate the TikZ figures of the note from the solver tables in ../data/sqN.txt.

fig_moves.tex   the board for 10^2 with the three moves
fig_maps.tex    losing squares for the 7x7, 9x9 and 10x10 boards (exceptions marked)
fig_strategy.tex  the second player's route in Theorem 4 (bottom row, N opening), n = 7, a = 4
"""

from pathlib import Path

HERE = Path(__file__).resolve().parent
DATA = HERE.parent / "verify" / "data"


def load(n: int) -> dict[tuple[int, int], str]:
    rows = (DATA / f"sq{n}.txt").read_text().split()
    return {(x, y): rows[n - 1 - y][x] for y in range(n) for x in range(n)}


def board_map(n: int, xshift: float, cell: float, title: str) -> str:
    b = load(n)
    out = [f"\\begin{{scope}}[xshift={xshift}cm]"]
    for (x, y), v in sorted(b.items()):
        if v != "L":
            continue
        ee = x % 2 == 0 and y % 2 == 0
        colour = "inkblue" if (ee or n % 2 == 0) else "rust"
        out.append(
            f"\\fill[{colour}] ({x * cell:.3f},{y * cell:.3f}) rectangle ++({cell:.3f},{cell:.3f});"
        )
    out.append(
        f"\\draw[gray!60, step={cell}] (0,0) grid ({n * cell:.3f},{n * cell:.3f});"
    )
    out.append(f"\\node[below] at ({n * cell / 2:.3f},-0.05) {{\\small {title}}};")
    out.append("\\end{scope}")
    return "\n".join(out)


def fig_maps() -> str:
    cell = 0.32
    parts = ["\\begin{tikzpicture}"]
    parts.append(board_map(7, 0.0, cell, "$7\\times 7$ ($n=6$)"))
    parts.append(board_map(9, 3.0, cell, "$9\\times 9$ ($n=8$)"))
    parts.append(board_map(10, 6.6, cell, "$10\\times 10$ ($n=9$)"))
    parts.append("\\end{tikzpicture}")
    return "\n".join(parts)


def fig_moves() -> str:
    c = 1.35
    lines = ["\\begin{tikzpicture}[>={Stealth[length=2.2mm]}]"]
    for x in range(3):
        for y in range(3):
            d = 2**x * 5**y
            lines.append(f"\\draw[gray!70] ({x * c},{y * c}) rectangle ++({c},{c});")
            lines.append(f"\\node at ({x * c + c / 2},{y * c + c / 2}) {{${d}$}};")
    cx, cy = 1 * c + c / 2, 1 * c + c / 2
    lines.append(
        f"\\draw[->, very thick, rust] ({cx + 0.28},{cy}) -- ({cx + c - 0.3},{cy}) node[midway, above] {{\\scriptsize $E$}};"
    )
    lines.append(
        f"\\draw[->, very thick, rust] ({cx},{cy + 0.25}) -- ({cx},{cy + c - 0.3}) node[midway, left] {{\\scriptsize $N$}};"
    )
    lines.append(
        f"\\draw[->, very thick, rust] ({cx - 0.25},{cy - 0.22}) -- ({cx - c + 0.32},{cy - c + 0.3}) node[midway, above left] {{\\scriptsize $D$}};"
    )
    lines.append(
        f"\\node[below] at ({1.5 * c},-0.1) {{\\small $\\times 2$ is $E$, $\\times 5$ is $N$, $\\div 10$ is $D$}};"
    )
    lines.append("\\end{tikzpicture}")
    return "\n".join(lines)


def fig_strategy() -> str:
    n, a, c = 7, 4, 0.42
    L = ["\\begin{tikzpicture}[>={Stealth[length=1.8mm]}]"]
    L.append(f"\\draw[gray!55, step={c}] (0,0) grid ({(n + 1) * c},{(n + 1) * c});")

    def ctr(x: int, y: int) -> tuple[float, float]:
        return (x * c + c / 2, y * c + c / 2)

    def path(pts: list[tuple[int, int]], style: str) -> str:
        coords = " -- ".join(f"({ctr(x, y)[0]:.3f},{ctr(x, y)[1]:.3f})" for x, y in pts)
        return f"\\draw[{style}] {coords};"

    # phase 1: bottom row west, Alice's N squares on row 1
    sweep = []
    for b in range(a, 0, -1):
        sweep += [(b, 0), (b, 1), (b - 1, 0)]
    sweep += [(0, 1), (0, 2)]
    L.append(path(sweep, "->, thick, inkblue"))
    # phase 2: climb along x - y = -2 (Alice's side square drawn above-left)
    climb = [(0, 2)]
    for i in range(n - 2):
        climb += [(i, i + 3), (i + 1, i + 3)]
    climb += [(n - 1, n), (n, n)]
    L.append(path(climb, "->, thick, rust"))
    # phase 3: right-edge sweep
    down = [(n, n)]
    for y in range(n, 0, -1):
        down += [(n - 1, y - 1), (n, y - 1)]
    L.append(path(down, "->, thick, inkblue!60"))
    sx, sy = ctr(a, 0)
    L.append(f"\\fill[black] ({sx:.3f},{sy:.3f}) circle (2.4pt);")
    L.append(f"\\node[below] at ({sx:.3f},-0.02) {{\\scriptsize start}};")
    L.append("\\end{tikzpicture}")
    return "\n".join(L)


if __name__ == "__main__":
    (HERE / "fig_maps.tex").write_text(fig_maps() + "\n")
    (HERE / "fig_moves.tex").write_text(fig_moves() + "\n")
    (HERE / "fig_strategy.tex").write_text(fig_strategy() + "\n")
    print("wrote fig_maps.tex, fig_moves.tex, fig_strategy.tex")
