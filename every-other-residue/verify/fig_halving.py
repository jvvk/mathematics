"""Write figs/halving.tex: one step of the proof of Theorem 1 on the worked example (k = 3, p = 1).
Upper-half elements (>= 8) in copper. Data recomputed from the recursive construction in strong_check.py."""
from pathlib import Path
from strong_check import pair, parity

n, M = 8, 16
e = [0, 1, 1, 0, 0, 1, 0, 0]; f = [1, 0, 0, 1, 1, 1, 0, 0]
A = [r + n * e[r] for r in range(n)]; B = [r + n * f[r] for r in range(n)]
assert parity(A, B, 3) == 1
A0 = sorted(a for a in A if a % 2 == 0); A1 = sorted(a for a in A if a % 2)
B0 = sorted(b for b in B if b % 2 == 0); B1 = sorted(b for b in B if b % 2)
X0 = [a // 2 for a in A0]; X1 = [(a - 1) // 2 for a in A1]; Y0 = [b // 2 for b in B0]; Y1 = [(b - 1) // 2 for b in B1]
q1, q2 = parity(X0, Y1, 2), parity(X1, Y0, 2)
s1 = sorted((x + y) % 8 for x, y in pair(X0, Y1, 2)); s2 = sorted((x + y) % 8 for x, y in pair(X1, Y0, 2))
t1 = sorted(2 * t + 1 for t in s1); t2 = sorted(2 * t + 1 for t in s2)
assert sorted(t1 + t2) == list(range(1, 16, 2))
def fmt(xs, half):
    return "\\{" + ",".join(rf"\textcolor{{copper}}{{{x}}}" if x >= half else str(x) for x in xs) + "\\}"
out = [r"\tikzset{bx/.style={draw=inkmuted, rounded corners=2pt, inner sep=3pt, font=\scriptsize}}"]
out += [rf"\node[bx] (a0) at (0,0) {{$A_0={fmt(A0,8)}$}};", rf"\node[bx] (a1) at (0,-0.7) {{$A_1={fmt(A1,8)}$}};",
        rf"\node[bx] (b0) at (5.2,0) {{$B_0={fmt(B0,8)}$}};", rf"\node[bx] (b1) at (5.2,-0.7) {{$B_1={fmt(B1,8)}$}};",
        r"\draw[copper, thick] (a0.east) -- (b1.west); \draw[copper, thick] (a1.east) -- (b0.west);",
        r"\node[font=\scriptsize, fill=white] at (2.6,-0.35) {$p=1$: cross};",
        rf"\node[bx] (h1) at (0.9,-2.0) {{$X_0,Y_1$ in $\mathbb Z/8$, parity ${q1}$: sums ${fmt(s1,99)}$}};",
        rf"\node[bx] (h2) at (4.3,-2.9) {{$X_1,Y_0$ in $\mathbb Z/8$, parity ${q2}$: sums ${fmt(s2,99)}$}};",
        r"\draw[->, inkmuted] (1.4,-1.05) -- (h1.north); \draw[->, inkmuted] (4.0,-1.05) -- (h2.north);",
        rf"\node[bx, draw=copper] (fin) at (2.6,-4.0) {{$2t+1$: ${fmt(t1,99)}\cup{fmt(t2,99)}$ = all odd residues mod $16$}};",
        r"\draw[->, inkmuted] (h1.south) -- (fin.north west); \draw[->, inkmuted] (h2.south) -- (fin.north east);"]
HERE = Path(__file__).resolve().parent
path = ((HERE.parent / "paper" / "figs") if (HERE.parent / "paper").exists() else (HERE.parent / "note" / "figs")) / "halving.tex"
path.write_text("\n".join(out) + "\n")
print("wrote", path, q1, q2, s1, s2, t1, t2)
