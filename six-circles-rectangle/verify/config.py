"""MO 515498 (six circles in a rectangle). Solve the configuration to 50 digits and list which tangencies hold.
Rectangle centre O=(0,0), half-height h=1, half-width w. Top row: A=(-(w-a),1-a) [corner], B=(x,1-b) [touches top,
passes through O], C=(w-c,1-c) [corner]; bottom row is the point reflection. Imposed: AB=a+b, BC=b+c, CA'=a+c,
BA'=a+b, OB=b. Claim to test: |AA'| = 2h, i.e. OA = 1."""
import itertools
import mpmath as mp

mp.mp.dps = 50


def sol():
    def F(a, b, c, w, x):
        A, B, C = (-(w - a), 1 - a), (x, 1 - b), (w - c, 1 - c)
        Ap = (-A[0], -A[1])
        d = lambda P, Q: mp.sqrt((P[0] - Q[0]) ** 2 + (P[1] - Q[1]) ** 2)
        return [d(A, B) - (a + b), d(B, C) - (b + c), d(C, Ap) - (a + c), d(B, Ap) - (a + b), d(B, (0, 0)) - b]
    return mp.findroot(F, (0.6066, 0.5210, 0.4037, 1.5259, 0.2050))


if __name__ == "__main__":
    a, b, c, w, x = sol()
    print("a b c w x =", [mp.nstr(v, 20) for v in (a, b, c, w, x)])
    P = {"A": ((-(w - a), 1 - a), a), "B": ((x, 1 - b), b), "C": ((w - c, 1 - c), c)}
    for k in "ABC":
        (px, py), r = P[k]
        P[k + "'"] = ((-px, -py), r)
    d = lambda p, q: mp.sqrt((p[0] - q[0]) ** 2 + (p[1] - q[1]) ** 2)
    print("OA =", mp.nstr(d(P["A"][0], (0, 0)), 30))
    for u, v in itertools.combinations(P, 2):
        gap = d(P[u][0], P[v][0]) - P[u][1] - P[v][1]
        if abs(gap) < mp.mpf(10) ** -30:
            print("tangent:", u, v)
