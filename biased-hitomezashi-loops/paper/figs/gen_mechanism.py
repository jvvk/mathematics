"""Generate figs/mechanism.tex: one loop of width 5 and height 3 with its vertical word and the labels it forces
(Lemma 2.3 / lem:zeros). Searches labellings of a 7 x 5 window for a loop with bounding box [1,6] x [1,4]."""
import itertools
n, m = 7, 5
def loops(eps, eta):
    adj, segs = {}, []
    def add(a, b):
        adj.setdefault(a, []).append(b); adj.setdefault(b, []).append(a); segs.append((a, b))
    for i in range(n + 1):
        for j in range(m):
            if j % 2 == eps[i]: add((i, j), (i, j + 1))
    for j in range(m + 1):
        for i in range(n):
            if i % 2 == eta[j]: add((i, j), (i + 1, j))
    seen, cyc_all = set(), []
    for s in adj:
        if s in seen: continue
        cyc, prev, cur, ok = [s], None, s, True
        while True:
            if len(adj[cur]) != 2: ok = False; break
            nxt = adj[cur][0] if prev is None else next(v for v in adj[cur] if v != prev)
            prev, cur = cur, nxt
            if cur == s: break
            cyc.append(cur)
        seen.update(cyc)
        if ok: cyc_all.append(cyc)
    return segs, cyc_all
def ccw(c):
    a = sum(c[k][0]*c[(k+1)%len(c)][1] - c[(k+1)%len(c)][0]*c[k][1] for k in range(len(c)))
    return c if a > 0 else c[::-1]
for eps in itertools.product((0, 1), repeat=n + 1):
    for eta in itertools.product((0, 1), repeat=m + 1):
        segs, cs = loops(eps, eta)
        for c in cs:
            xs = [x for x, _ in c]; ys = [y for _, y in c]
            if (min(xs), max(xs), min(ys), max(ys)) == (1, 6, 1, 4):
                c = ccw(c)
                word = {}
                for k in range(len(c)):
                    (x1, y1), (x2, y2) = c[k], c[(k+1) % len(c)]
                    if x1 == x2: word[x1] = 'U' if y2 < y1 else 'D'   # south = U (paper's convention)
                V = ''.join(word[x] for x in range(1, 7))
                labels = [eps[x] for x in range(1, 7)]
                P = V[1:-1]; h = 0; ev = od = 0
                for s in P:
                    if s == 'U': ev += h % 2 == 0; od += h % 2 == 1; h += 1
                    else: h -= 1
                A, B = 1 + od, ev
                assert labels.count(0) in (2*A, 2*B), (V, labels)
                out = [r"\begin{tikzpicture}[scale=0.6]"]
                out.append(r"\fill[loopfill] " + " -- ".join(f"({x},{y})" for x, y in c) + " -- cycle;")
                out.append(rf"\draw[gridline] (0,0) grid ({n},{m});")
                for (a, b) in segs:
                    out.append(rf"\draw[stitch,gray!60] ({a[0]},{a[1]}) -- ({b[0]},{b[1]});")
                for k in range(len(c)):
                    a, b = c[k], c[(k+1) % len(c)]
                    out.append(rf"\draw[stitch,->,>=stealth] ({a[0]},{a[1]}) -- ({(a[0]+b[0])/2},{(a[1]+b[1])/2});")
                    out.append(rf"\draw[stitch] ({a[0]},{a[1]}) -- ({b[0]},{b[1]});")
                for x in range(1, 7):
                    out.append(rf"\node[font=\footnotesize] at ({x},{m+0.55}) {{$\mathsf{{{word[x]}}}$}};")
                    out.append(rf"\node[font=\footnotesize] at ({x},-0.55) {{${eps[x]}$}};")
                out.append(rf"\node[font=\footnotesize,anchor=east] at (0.4,{m+0.55}) {{$V(L)$}};")
                out.append(r"\node[font=\footnotesize,anchor=east] at (0.4,-0.55) {$\varepsilon_i$};")
                out.append(r"\end{tikzpicture}")
                open("mechanism.tex", "w").write("\n".join(out) + "\n")
                print("V =", V, "P =", P, "A,B =", A, B, "vertical labels", labels, "zeros", labels.count(0),
                      "eta", [eta[y] for y in range(1, 5)])
                raise SystemExit
