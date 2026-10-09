"""Write the TikZ figures of note.tex (fig_*.tex) from the words and paths themselves."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "verify"))
import involution as I  # noqa: E402

OUT = Path(__file__).resolve().parent


def dyck_path(steps: str, x0: float, y0: float, s: float = 0.32, valleys: bool = True) -> str:
    """A Dyck path from 'U'/'D' letters, with valley down steps marked."""
    pts = [(x0, y0)]
    for c in steps:
        x, y = pts[-1]
        pts.append((x + s, y + (s if c == "U" else -s)))
    lines = [rf"\draw[gray!25] ({x0},{y0}) -- ({x0 + s * len(steps)},{y0});"]
    lines.append(r"\draw[thick,inkblue] " + " -- ".join(f"({x:.3f},{y:.3f})" for x, y in pts) + ";")
    if valleys:
        for i in range(len(steps) - 1):
            if steps[i] == "D" and steps[i + 1] == "U":
                x, y = pts[i + 1]
                lines.append(rf"\fill[rust] ({x:.3f},{y:.3f}) circle (1.6pt);")
    return "\n".join(lines)


STEP = {"u": (1, 1), "d": (1, -1), "a": (1, 0), "b": (1, 0), "c": (1, 0)}
STYLE = {"u": "thick,inkblue", "d": "thick,inkblue", "a": "thick,gray!60", "b": "ultra thick,rust",
         "c": "ultra thick,inkblue,dashed"}


def word_path(w: str, x0: float, y0: float, s: float = 0.5, labels: bool = True, mark=(), ground=None) -> str:
    """A two-coloured Motzkin word: u, d diagonal; a grey level; b thick rust level; c dashed level."""
    g = y0 if ground is None else ground
    out = [rf"\draw[gray!25] ({x0},{g}) -- ({x0 + s * len(w)},{g});"]
    x, y = x0, y0
    for i, c in enumerate(w):
        dx, dy = STEP[c]
        nx, ny = x + s * dx, y + s * dy
        st = STYLE[c] + (",line width=2.2pt,draw=rust!70" if i in mark else "")
        out.append(rf"\draw[{st}] ({x:.3f},{y:.3f}) -- ({nx:.3f},{ny:.3f});")
        if labels:
            out.append(rf"\node[font=\scriptsize,gray] at ({(x + nx) / 2:.3f},{min(y, ny) - 0.22:.3f}) {{${c}$}};")
        x, y = nx, ny
    for (xx, yy) in [(x0, y0), (x, y)]:
        out.append(rf"\fill ({xx:.3f},{yy:.3f}) circle (1pt);")
    return "\n".join(out)


def fig_three() -> str:
    """The five Dyck paths of semilength 3."""
    rows = []
    paths = ["UUUDDD", "UUDUDD", "UUDDUD", "UDUUDD", "UDUDUD"]
    for j, P in enumerate(paths):
        steps = tuple(1 if c == "U" else -1 for c in P)
        m = sum(i + 1 for i in range(5) if P[i] == "D" and P[i + 1] == "U")
        k = sum(1 for i in range(5) if P[i] == "D" and P[i + 1] == "U")
        x0 = 2.9 * j
        rows.append(dyck_path(P, x0, 0))
        cx = x0 + 0.96
        sign = "+" if m % 2 == 0 else "-"
        rows.append(rf"\node[font=\small] at ({cx},-0.42) {{\texttt{{{P}}}}};")
        rows.append(rf"\node[font=\footnotesize] at ({cx},-0.85) {{$k={k}$, $\maj={m}$}};")
        rows.append(rf"\node[font=\footnotesize] at ({cx},-1.25) {{sign ${sign}$}};")
        if I.is_symmetric(steps):
            rows.append(rf"\node[font=\footnotesize,rust] at ({cx},-1.65) {{symmetric}};")
    return "\\begin{tikzpicture}[line join=round]\n" + "\n".join(rows) + "\n\\end{tikzpicture}\n"


def fig_encode() -> str:
    P = "UUDUUDDDUD"
    out = [dyck_path(P, 0, 0, s=0.45)]
    # valley labels (u_j, d_j)
    pts, x, y = [], 0.0, 0.0
    for c in P:
        pts.append((x, y))
        x += 0.45; y += 0.45 if c == "U" else -0.45
    pts.append((x, y))
    ups = downs = 0
    for i in range(len(P) - 1):
        ups += P[i] == "U"; downs += P[i] == "D"
        if P[i] == "D" and P[i + 1] == "U":
            vx, vy = pts[i + 1]
            out.append(rf"\node[font=\small,rust,below] at ({vx:.3f},{vy - 0.05:.3f}) {{$({ups},{downs})$}};")
    out.append(r"\node[font=\small] at (2.25,-0.95) {\texttt{UUDUUDDDUD}, valleys at positions 3 and 8};")
    out.append(r"\draw[->,gray] (4.9,0.5) -- (6.1,0.5);")
    out.append(word_path("udab", 6.6, 0.25, s=0.75))
    out.append(r"\node[font=\small] at (8.1,-0.95) {$U=\{2,4\}$, $D=\{1,4\}$};")
    return "\\begin{tikzpicture}[line join=round]\n" + "\n".join(out) + "\n\\end{tikzpicture}\n"


def fig_partners() -> str:
    S = 0.55
    out = [r"\node[font=\small,anchor=west] at (-0.2,0.95) {partners};"]
    rows = [("ua", "au", "", 0), ("ud", "ba", "", 0), ("du", "ab", "height $\\ge 1$", 1)]
    for r, (p, q, note, h) in enumerate(rows):
        y = -1.45 * r
        out.append(word_path(p, 0, y + h * S, s=S, ground=y))
        out.append(rf"\draw[<->,gray] (1.35,{y + 0.3}) -- (1.95,{y + 0.3});")
        out.append(word_path(q, 2.2, y + h * S, s=S, ground=y))
        if note:
            out.append(rf"\node[font=\footnotesize,anchor=west] at (3.45,{y + 0.55}) {{{note}}};")
    out.append(r"\node[font=\small,anchor=west] at (6.0,0.95) {no partner};")
    for j, p in enumerate(["uu", "dd"]):
        x = 6.2 + 1.7 * j
        out.append(word_path(p, x, -0.6 + (2 * S if p == "dd" else 0), s=S, ground=-0.6))
    for j, p in enumerate(["aa", "bb"]):
        out.append(word_path(p, 6.2 + 1.7 * j, -1.75, s=S))
    out.append(word_path("ab", 6.2, -2.9, s=S))
    out.append(r"\node[font=\footnotesize,anchor=west] at (7.4,-2.85) {at height $0$};")
    return "\\begin{tikzpicture}[line join=round]\n" + "\n".join(out) + "\n\\end{tikzpicture}\n"


def fig_halve() -> str:
    w = "abuuddab"
    assert I.iota(w) == w
    s = I.to_symmetric(w)
    assert s == "uudududd", s
    rows = [(w, 0.4, (), "a fixed word: pairs \\texttt{ab}, \\texttt{uu}, \\texttt{dd}, \\texttt{ab}"),
            ("cudc", 0.8, (), "halved: one letter per pair, \\texttt{ab} becomes $c$"),
            ("uudu", 0.8, (0, 3), "$c$ becomes $u$: the last departures from levels $0$ and $1$"),
            (s, 0.4, (0, 3), "followed by its mirror image")]
    out, y = [], 0.0
    tops = {w: 2, "cudc": 1, "uudu": 2, s: 2}
    for i, (word, sc, mark, label) in enumerate(rows):
        if i:
            y -= 0.85 + tops[word] * sc
        out.append(word_path(word, 0, y, s=sc, mark=mark))
        out.append(rf"\node[font=\small,anchor=west] at (3.7,{y + 0.25}) {{{label}}};")
    out.append(r"\draw[gray,dashed] (1.6,%.2f) -- (1.6,%.2f);" % (y - 0.3, y + 1.0))
    return "\\begin{tikzpicture}[line join=round]\n" + "\n".join(out) + "\n\\end{tikzpicture}\n"


if __name__ == "__main__":
    for name, f in [("three", fig_three), ("encode", fig_encode), ("partners", fig_partners), ("halve", fig_halve)]:
        (OUT / f"fig_{name}.tex").write_text(f())
    print("figures written")
