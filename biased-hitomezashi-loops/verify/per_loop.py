"""Per-loop check of Lemmas 2.1-2.3 and Pete's reading, exhaustively on N x N boxes.

For every labelling of an N x N box and every loop in it, orient the loop counterclockwise and read
the vertical word (U where its stitches run south) and the horizontal word (U where they run east).
Assert: both words are U P D with P a Dyck path, the two Dyck paths have the same height, and the
numbers of 0-labels on the lines the loop uses are {2A, 2B} with A = 1 + #(up-steps of P from odd
heights) and B = #(up-steps of P from even heights).  Shares no code with the Lean files.
"""
import itertools
import sys

N = int(sys.argv[1]) if len(sys.argv) > 1 else 7


def stitches(eps, eta):
    adj = {}

    def add(a, b):
        adj.setdefault(a, []).append(b)
        adj.setdefault(b, []).append(a)

    for i in range(N + 1):
        for j in range(N):
            if j % 2 == eps[i]:
                add((i, j), (i, j + 1))
    for j in range(N + 1):
        for i in range(N):
            if i % 2 == eta[j]:
                add((i, j), (i + 1, j))
    return adj


def loops(adj):
    seen, out = set(), []
    for s in adj:
        if s in seen:
            continue
        cyc, prev, cur, closed = [s], None, s, True
        while True:
            if len(adj[cur]) != 2:
                closed = False
                break
            nxt = adj[cur][0] if prev is None else next(v for v in adj[cur] if v != prev)
            prev, cur = cur, nxt
            if cur == s:
                break
            cyc.append(cur)
        seen.update(cyc)
        if closed:
            out.append(cyc)
    return out


def dyck_stats(w):
    h, top, ev, od = 0, 0, 0, 0
    for x in w:
        if x == "U":
            ev, od = (ev + 1, od) if h % 2 == 0 else (ev, od + 1)
        h += 1 if x == "U" else -1
        if h < 0:
            return None
        top = max(top, h)
    return (top, ev, od) if h == 0 else None


checked = 0
for eps in itertools.product([0, 1], repeat=N + 1):
    for eta in itertools.product([0, 1], repeat=N + 1):
        for c in loops(stitches(eps, eta)):
            a2 = sum(c[i][0] * c[(i + 1) % len(c)][1] - c[(i + 1) % len(c)][0] * c[i][1] for i in range(len(c)))
            if a2 < 0:
                c = c[::-1]
            xs, ys = [p[0] for p in c], [p[1] for p in c]
            x0, x1, y0, y1 = min(xs), max(xs), min(ys), max(ys)
            dv, dh = {}, {}
            for k in range(len(c)):
                a, b = c[k], c[(k + 1) % len(c)]
                if a[0] == b[0]:
                    dv.setdefault(a[0], set()).add("S" if b[1] < a[1] else "N")
                else:
                    dh.setdefault(a[1], set()).add("E" if b[0] > a[0] else "W")
            assert all(len(v) == 1 for v in list(dv.values()) + list(dh.values())), "direction not constant"
            wv = "".join("U" if dv[x] == {"S"} else "D" for x in range(x0, x1 + 1))
            wh = "".join("U" if dh[y] == {"E"} else "D" for y in range(y0, y1 + 1))
            assert wv[0] == "U" and wv[-1] == "D" and wh[0] == "U" and wh[-1] == "D"
            sv, sh = dyck_stats(wv[1:-1]), dyck_stats(wh[1:-1])
            assert sv is not None and sh is not None and sv[0] == sh[0], "not Dyck / heights differ"
            for (top, ev, od), labels in ((sv, eps[x0:x1 + 1]), (sh, eta[y0:y1 + 1])):
                A, B = 1 + od, ev
                z = labels.count(0)
                assert {z, len(labels) - z} == {2 * A, 2 * B}, (labels, A, B)
            checked += 1
print(f"N = {N}: {checked} loop occurrences checked, all pass")
