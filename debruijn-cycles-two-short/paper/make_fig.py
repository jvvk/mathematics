"""Writes fig_b3.tex: the de Bruijn graph B(3) with the two balanced deletions highlighted.

Cycles of length 14 in B(4) are Eulerian circuits of B(3) with two edges removed: either the two loops
(at 000 and 111) or the 2-cycle 010 <-> 101. Run: python3 make_fig.py > fig_b3.tex
"""
POS = {"000": (0, 0), "001": (1.6, 1.25), "100": (1.6, -1.25), "010": (3.2, 0.62),
       "101": (3.2, -0.62), "011": (4.8, 1.25), "110": (4.8, -1.25), "111": (6.4, 0)}
LOOPS = {"000": "left", "111": "right"}
CYCLE = {("010", "101"), ("101", "010")}
BEND = {("010", "101"): "bend left=28", ("101", "010"): "bend left=28", ("100", "001"): "bend left=18",
        ("001", "100"): "bend left=18"}


def edges():
    for u in POS:
        for b in "01":
            v = u[1:] + b
            yield u, v


def b3_fig() -> str:
  out = [r"\begin{tikzpicture}[>=stealth, scale=1.25, every node/.style={font=\small},",
         r"  vtx/.style={draw=inkblue, fill=softblue, rounded corners=2pt, inner sep=2.5pt, font=\ttfamily\small}]"]
  for name, (x, y) in POS.items():
      out.append(rf"\node[vtx] ({name}) at ({x},{y}) {{{name}}};")
  for u, v in edges():
      if u == v:
          side = LOOPS[u]
          ang = 180 if side == "left" else 0
          out.append(rf"\draw[->, rust, very thick, dashed] ({u}) to[out={ang + 35}, in={ang - 35}, looseness=6] ({u});")
      elif (u, v) in CYCLE:
          out.append(rf"\draw[->, rust, very thick] ({u}) to[{BEND[(u, v)]}] ({v});")
      else:
          opt = BEND.get((u, v), "")
          out.append(rf"\draw[->, inkblue!70] ({u}) to[{opt}] ({v});")
  out.append(r"\end{tikzpicture}")
  return "\n".join(out)


if __name__ == "__main__" and len(__import__("sys").argv) == 1:
    print(b3_fig())


def shift_fig(m: int = 4) -> str:
    """fig_shift.tex: p = 0101... shifted k places keeps p[k:] and appends k random bits;
    the kept part starts like p for even k and like q for odd k."""
    p = "".join("01"[i % 2] for i in range(m))
    rows = [r"\begin{tikzpicture}[x=0.62cm, y=0.62cm, every node/.style={font=\small}]"]
    for k in range(m):
        y = -k
        rows.append(rf"\node[anchor=east] at (-0.4,{y}) {{$k={k}$}};")
        for i in range(m):
            x = i
            if i < m - k:
                rows.append(rf"\draw[fill=softblue, draw=inkblue] ({x},{y - 0.4}) rectangle ({x + 0.9},{y + 0.4});")
                rows.append(rf"\node[font=\ttfamily\small] at ({x + 0.45},{y}) {{{p[k + i]}}};")
            else:
                rows.append(rf"\draw[fill=black!8, draw=black!40] ({x},{y - 0.4}) rectangle ({x + 0.9},{y + 0.4});")
                rows.append(rf"\node[text=black!55] at ({x + 0.45},{y}) {{$\ast$}};")
        target = "p" if k % 2 == 0 else "q"
        colour = "inkblue" if k % 2 == 0 else "rust"
        rows.append(rf"\node[anchor=west, text={colour}] at ({m + 0.3},{y}) {{can be ${target}$: probability $2^{{-{k}}}$}};")
    rows.append(r"\end{tikzpicture}")
    return "\n".join(rows)


if __name__ == "__main__" and len(__import__("sys").argv) > 1 and __import__("sys").argv[1] == "shift":
    print(shift_fig())
