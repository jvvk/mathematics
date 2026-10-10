"""Figure data for the note (written to ../paper/figs or ../note/figs).

pairs101.tex: (a) the points (a, abar) for p = 101 and the hyperbola xy = 2000, the points with
a >= 2 under it in copper; (b) the two staircases of four columns that squeeze the region xy <= 2000.
Asserts the counts quoted in the caption: R(2000) = 50 inverse pairs, against Tc(2000)/p = 50.9.
"""
from pathlib import Path

_ROOT = Path(__file__).resolve().parent.parent
OUT = _ROOT / ("paper" if (_ROOT / "paper").exists() else "note") / "figs"

p, X, L = 101, 2000, 4
S = 4.0 / p  # square side 4 cm
inv = {a: pow(a, -1, p) for a in range(1, p)}
R = sum(1 for a in range(2, p) if a * inv[a] <= X)
T = sum(min(p - 1, X // a) for a in range(1, p))
assert R == 50 and round(T / p, 1) == 50.9, (R, T / p)

hyp = [(x, X / x) for x in [X / p + (p - X / p) * i / 120 for i in range(121)]]


def panel(dx: float, body: list[str]) -> list[str]:
    return [rf"\begin{{scope}}[shift={{({dx},0)}}]",
            rf"\draw[inkmuted] (0,0) rectangle ({p * S:.3f},{p * S:.3f});"] + body + [r"\end{scope}"]


curve = r"\draw[thick] " + " -- ".join(f"({x * S:.3f},{y * S:.3f})" for x, y in hyp) + ";"
shade = (r"\fill[copper!12] (0,0) -- (0," + f"{p * S:.3f}" + ") -- "
         + " -- ".join(f"({x * S:.3f},{y * S:.3f})" for x, y in hyp) + f" -- ({p * S:.3f},0) -- cycle;")
A = [shade, curve]
for a in range(1, p):
    col = "copper" if a * inv[a] <= X and a > 1 else "black"
    A.append(rf"\fill[{col}] ({a * S:.3f},{inv[a] * S:.3f}) circle (0.75pt);")
A.append(r"\node[below, font=\small] at (2,-0.1) {(a)};")
B = [shade, curve]
edges = [1 + round(i * (p - 2) / L) for i in range(L + 1)]
for l in range(L):
    al, be = edges[l], edges[l + 1]
    lo, hi = min(p - 1, X / be), min(p - 1, X / al)
    B.append(rf"\draw[fill=inkmuted!25] ({al * S:.3f},0) rectangle ({be * S:.3f},{lo * S:.3f});")
    B.append(rf"\draw[copper, thick] ({al * S:.3f},{lo * S:.3f}) -- ({al * S:.3f},{hi * S:.3f}) -- "
             rf"({be * S:.3f},{hi * S:.3f}) -- ({be * S:.3f},{lo * S:.3f});")
B.append(r"\node[below, font=\small] at (2,-0.1) {(b)};")

OUT.mkdir(parents=True, exist_ok=True)
(OUT / "pairs101.tex").write_text("\n".join(panel(0, A) + panel(4.8, B)) + "\n")
print(f"wrote {OUT / 'pairs101.tex'}: R(2000) = {R}, Tc(2000)/p = {T / p:.1f}")
