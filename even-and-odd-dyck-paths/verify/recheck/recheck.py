#!/usr/bin/env python3
"""Independent recheck for "Even and odd Dyck paths" (shares no code with involution.py).

Checks, from the definitions in the note:
  1. Theorem 1, E - O = S, for n <= N, with Dyck paths generated from the positions of their up steps.
  2. Both sides against the q-Narayana number of Fürlinger and Hofbauer at q = -1, built by exact
     polynomial arithmetic (q-binomials by the q-Pascal rule, exact division by [k+1]).
  3. The identity (1) itself, coefficient by coefficient, for n <= 8.
  4. maj P* = 2nk - maj P, and maj P = nk for symmetric P.
  5. Every worked example in the text (Figures 1 to 4 and Sections 3 to 5).
  6. Lemmas 1 to 4 on all words for n <= 10, with the encoding written from valley coordinates.
  7. Mutants: a wrong partner rule and a wrong halving must fail.
Usage: python3 recheck.py [N]   (default N = 10)
"""
from itertools import combinations
import sys

FAIL = []


def check(cond: bool, what: str) -> None:
    if not cond:
        FAIL.append(what)


# ---------- paths from the definitions ----------

def paths(n: int):
    for ups in combinations(range(2 * n), n):
        s = ["D"] * (2 * n)
        for i in ups:
            s[i] = "U"
        h = 0
        ok = True
        for c in s:
            h += 1 if c == "U" else -1
            if h < 0:
                ok = False
                break
        if ok:
            yield "".join(s)


def valleys(P: str) -> list[int]:
    return [i + 1 for i in range(len(P) - 1) if P[i] == "D" and P[i + 1] == "U"]


def maj(P: str) -> int:
    return sum(valleys(P))


def mirror_path(P: str) -> str:
    return "".join("U" if c == "D" else "D" for c in reversed(P))


# ---------- exact polynomials in q (lists of integer coefficients) ----------

def padd(a, b):
    m = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(m)]


def pmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def shift(a, k):
    return [0] * k + a


def pdiv_exact(a, b):
    a = a[:]
    while a and a[-1] == 0:
        a.pop()
    q = [0] * max(1, len(a) - len(b) + 1)
    for i in range(len(a) - len(b), -1, -1):
        c, r = divmod(a[i + len(b) - 1], b[-1])
        assert r == 0
        q[i] = c
        for j, y in enumerate(b):
            a[i + j] -= c * y
    assert all(x == 0 for x in a), "division not exact"
    return q


def qbinom(n: int, k: int):
    """q-Pascal: [n,k] = [n-1,k-1] + q^k [n-1,k]."""
    if k < 0 or k > n:
        return [0]
    if k == 0 or k == n:
        return [1]
    return padd(qbinom(n - 1, k - 1), shift(qbinom(n - 1, k), k))


def qnarayana(n: int, k: int):
    """q^{k(k+1)} [n,k][n-1,k] / [k+1]."""
    num = pmul(qbinom(n, k), qbinom(n - 1, k))
    return shift(pdiv_exact(num, [1] * (k + 1)), k * (k + 1))


def at(p, q):
    return sum(c * q ** i for i, c in enumerate(p))


# ---------- words from valley coordinates (Section 3) ----------

def coords(P: str):
    out, ups, downs = [], 0, 0
    for i, c in enumerate(P):
        if c == "U":
            ups += 1
        else:
            downs += 1
            if i + 1 < len(P) and P[i + 1] == "U":
                out.append((ups, downs))
    return out


def word(P: str) -> str:
    n = len(P) // 2
    U = {u for u, _ in coords(P)}
    D = {d for _, d in coords(P)}
    return "".join({(False, True): "u", (True, False): "d", (False, False): "a", (True, True): "b"}[(x in U, x in D)]
                   for x in range(1, n))


def heights(w: str) -> list[int]:
    h, out = 0, [0]
    for c in w:
        h += {"u": 1, "d": -1}.get(c, 0)
        out.append(h)
    return out


def sign_word(w: str) -> int:
    return (-1) ** sum(x for x, c in enumerate(w, 1) if c in "ud")


def mirror_word(w: str) -> str:
    return "".join({"u": "d", "d": "u"}.get(c, c) for c in reversed(w))


# ---------- the rule (Section 4), written from the bullet list ----------

LEVEL = set("ab")


def partner(pair: str, h: int, high_ok=lambda h: h >= 1):
    x, y = pair
    if (x in LEVEL) != (y in LEVEL):
        return y + x
    if pair == "ud":
        return "ba"
    if pair == "ba":
        return "ud"
    if pair == "du" and high_ok(h):
        return "ab"
    if pair == "ab" and high_ok(h):
        return "du"
    return None


def rule(w: str, high_ok=lambda h: h >= 1) -> str:
    hs = heights(w)
    for i in range(0, len(w) - 1, 2):
        p = partner(w[i:i + 2], hs[i], high_ok)
        if p is not None:
            return w[:i] + p + w[i + 2:]
    return w


# ---------- the halving map (Section 5) ----------

def halve(w: str, ab_to="c") -> str:
    m = {"uu": "u", "dd": "d", "aa": "a", "bb": "b", "ab": ab_to}
    h = "".join(m[w[i:i + 2]] for i in range(0, len(w) - 1, 2))
    h = h.replace("c", "u")
    mid = w[-1] if len(w) % 2 else ""
    return h + mid + mirror_word(h)


def run(N: int) -> None:
    # 1-4
    for n in range(1, N + 1):
        P_all = list(paths(n))
        for k in range(n):
            group = [P for P in P_all if len(valleys(P)) == k]
            E = sum(1 for P in group if maj(P) % 2 == 0)
            O = len(group) - E
            S = sum(1 for P in group if mirror_path(P) == P)
            check(E - O == S, f"Theorem 1 n={n} k={k}: {E}-{O} != {S}")
            check(at(qnarayana(n, k), -1) == S, f"q-Narayana at -1, n={n} k={k}")
            if n <= 8:
                gf = [0] * (n * n + 1)
                for P in group:
                    gf[maj(P)] += 1
                qn = qnarayana(n, k)
                check(padd(gf, [0]) [:len(qn)] == qn and all(c == 0 for c in gf[len(qn):]),
                      f"identity (1) n={n} k={k}")
            for P in group:
                check(maj(mirror_path(P)) == 2 * n * k - maj(P), f"mirror maj {P}")
                if mirror_path(P) == P:
                    check(maj(P) == n * k, f"symmetric maj {P}")
    # 5: the worked examples
    three = {"UUUDDD": (0, 0, True, "aa"), "UUDUDD": (1, 3, True, "ud"), "UUDDUD": (1, 4, False, "ab"),
             "UDUUDD": (1, 2, False, "ba"), "UDUDUD": (2, 6, True, "bb")}
    check(set(paths(3)) == set(three), "five paths of semilength 3")
    for P, (k, m, sym, w) in three.items():
        check((len(valleys(P)), maj(P), mirror_path(P) == P, word(P)) == (k, m, sym, w), f"Figure 1 {P}")
    check([sign_word(three[P][3]) for P in three] == [1, -1, 1, 1, 1], "signs of the n = 3 words")
    P = "UUDUUDDDUD"
    check(valleys(P) == [3, 8] and coords(P) == [(2, 1), (4, 4)] and word(P) == "udab" and maj(P) == 11,
          "Figure 2")
    check(rule("udab") == "baab" and maj("UDUUUDDDUD") == 10 and word("UDUUUDDDUD") == "baab", "Section 4 example")
    check(rule("ud") == "ba" and rule("ab") == "ab" and rule("aa") == "aa" and rule("bb") == "bb", "n = 3 rule")
    check(rule("abuuddab") == "abuuddab", "Figure 4 word is fixed")
    check(halve("abuuddab") == "uudududd" and mirror_word("uudu") == "dudd", "Figure 4 halving")
    sym_path = [Q for Q in paths(9) if word(Q) == "uudududd"]
    check(len(sym_path) == 1 and mirror_path(sym_path[0]) == sym_path[0], "Figure 4 image is a symmetric path")
    check(halve("ab") == "ud" and word("UUDUDD") == "ud", "n = 3 halving")
    # 6: lemmas on all words
    for n in range(1, N + 1):
        P_all = list(paths(n))
        W = {word(P): P for P in P_all}
        check(len(W) == len(P_all), f"Lemma 1/2 injective n={n}")
        legal = [w for w in W]
        for w, P in W.items():
            hs = heights(w)
            check(min(hs) >= 0 and hs[-1] == 0, f"Lemma 2 word legal {w}")
            check(w.count("u") + w.count("b") == len(valleys(P)), f"Lemma 2 count {w}")
            check(sign_word(w) == (-1) ** maj(P), f"equation (3) {w}")
            check((mirror_path(P) == P) == (mirror_word(w) == w), f"Lemma 2 mirror {w}")
            v = rule(w)
            check(v in W, f"Lemma 3 legal {w}->{v}")
            check(rule(v) == w, f"Lemma 3 involution {w}")
            check(v.count("u") + v.count("b") == w.count("u") + w.count("b"), f"Lemma 3 count {w}")
            if v != w:
                check(sign_word(v) == -sign_word(w), f"Lemma 3 sign {w}")
            else:
                check(sign_word(w) == 1, f"Lemma 3 fixed sign {w}")
        fixed = [w for w in W if rule(w) == w]
        images = [halve(w) for w in fixed]
        symm = {w for w in W if mirror_word(w) == w}
        check(len(set(images)) == len(images) and set(images) == symm, f"Lemma 4 bijection n={n}")
        for w in fixed:
            z = halve(w)
            check(z.count("u") + z.count("b") == w.count("u") + w.count("b"), f"Lemma 4 count {w}")


def mutants(N: int) -> int:
    """Each wrong variant must produce a failure; returns the number that did."""
    killed = 0
    n_range = range(2, min(N, 7) + 1)
    # du <-> ab allowed at height 0
    bad = False
    for n in n_range:
        W = {word(P) for P in paths(n)}
        for w in W:
            v = rule(w, high_ok=lambda h: True)
            if v not in W:
                bad = True
    killed += bad
    # halving sends ab to a instead of c
    bad = False
    for n in n_range:
        W = {word(P) for P in paths(n)}
        fixed = [w for w in W if rule(w) == w]
        imgs = [halve(w, ab_to="a") for w in fixed]
        if len(set(imgs)) != len(imgs) or set(imgs) != {w for w in W if mirror_word(w) == w}:
            bad = True
    killed += bad
    # sign that counts a b letter once instead of twice
    bad = any((-1) ** sum(x for x, c in enumerate(word(P), 1) if c in "udb") != (-1) ** maj(P)
              for n in n_range for P in paths(n))
    killed += bad
    return killed


if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    run(N)
    k = mutants(N)
    print(f"mutants rejected: {k}/3")
    if FAIL or k != 3:
        print("FAIL", FAIL[:10])
        sys.exit(1)
    print(f"ALL PASS (n <= {N})")
