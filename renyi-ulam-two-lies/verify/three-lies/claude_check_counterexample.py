"""Claude's independent check of Codex's e = 3 counterexample (route-e3, 2026-11-24).
Shares no code with checks/codex-route-e3/explore/verify_counterexample.py; written from the game's definitions.

Claim: x = (2a, 52, 120, 0), a = (2^105 - 153920) / 198592, is 106-winnable, while its halving child
h = (a, a+26, 86, 60) is not 105-winnable. So the even first question is not optimal.

Part A (h loses in 105): necessary conditions only, enumerated over every (w, t, lam) with no simplification
  taken from PROOF.md: the first question's last-two coordinates (w, t) and the YES-slack lam; the residue
  conditions are recomputed from the transition rule, and the coefficients of u, v are checked to vanish.
Part B (x wins in 106): replay every certificate row with my own transition and volume code; a row
  (n, A, B, C, D, q) asserts (A, B, C, D) is n-winnable via first question q. A child is accepted if it has
  <= 1 candidate, or its core (first three coordinates) was accepted at depth n-1 and its volume fits
  (padding lemma: core winnable + volume <= 2^n  =>  winnable; Guzicki 1990 Lemma 3.11, proof in PROOF.md s.1).
  Monotonicity in depth is NOT assumed: the child core must be certified at exactly n-1, or have <= 1 candidate.
"""

import json
import sys
from math import comb
from pathlib import Path

E = 3


def binom(n: int, k: int) -> int:
    return comb(n, k) if 0 <= k <= n else 0


def cap(n: int, i: int) -> int:
    """Leaves used by one candidate with i lies already used, n questions left."""
    return sum(binom(n, j) for j in range(E - i + 1))


def vol(s: tuple[int, ...], n: int) -> int:
    return sum(s[i] * cap(n, i) for i in range(E + 1))


def answer(s: tuple[int, ...], q: tuple[int, ...]) -> tuple[int, ...]:
    """Child after the answer 'in q': class-i members of q stay, non-members move up a class."""
    return tuple(q[i] + (s[i - 1] - q[i - 1] if i > 0 else 0) for i in range(E + 1))


def both(s, q):
    return answer(s, q), answer(s, tuple(si - qi for si, qi in zip(s, q)))


def part_a() -> None:
    num = 2**105 - 153920
    assert num % 198592 == 0
    a = num // 198592
    assert a == 204262101229170061472237061
    h = (a, a + 26, 86, 60)
    x = (2 * a, 52, 120, 0)
    assert both(x, tuple(z // 2 for z in x)) == (h, h)
    slack = 2**105 - vol(h, 105)
    assert slack == 28, slack
    n = 105
    # YES volume at depth n-1 of question (u,v,w,t) = base + c0 u + c1 v + c2 w + c3 t, read off answer():
    zero = (0, 0, 0, 0)
    base = vol(answer(h, zero), n - 1)
    coef = [
        vol(answer(h, tuple(int(i == j) for j in range(4))), n - 1) - base
        for i in range(4)
    ]
    assert coef == [binom(n - 1, 3), binom(n - 1, 2), n - 1, 1], coef
    M = coef[1]
    assert coef[0] % M == 0  # u and v move T only by multiples of M
    survivors = []
    for w in range(h[2] + 1):
        for t in range(h[3] + 1):
            for lam in range(slack + 1):
                T = (
                    2 ** (n - 1) - lam
                )  # YES child volume; NO child then has slack slack - lam
                if (T - base - coef[2] * w - coef[3] * t) % M:
                    continue  # no (u, v) reaches this T
                survivors.append((w, t, lam))
    assert survivors, "no first question even passes the volume test"
    # Next level: at a child c (depth n-1 = 104), any first question shifts its YES volume at depth 103 by
    # multiples of p = 103 except for the last coordinate, so  (2^103 - Kc) mod p <= sigma_c + c_3.
    m = n - 1
    p = m - 1
    assert binom(m - 1, 3) % p == 0 and binom(m - 1, 2) % p == 0 and (m - 1) % p == 0
    killed = 0
    for w, t, lam in survivors:
        # residues of the children's K mod p do not depend on u, v: check the coefficients vanish mod p
        def K(c):
            return vol(answer(c, (0, 0, 0, 0)), m - 1)

        def kids(u, v):
            return both(h, (u, v, w, t))

        y0, z0 = kids(0, 0)
        for du, dv in ((1, 0), (0, 1)):
            y1, z1 = kids(du, dv)
            assert (K(y1) - K(y0)) % p == 0 and (K(z1) - K(z0)) % p == 0
            # the slack and last class do not depend on u, v either
            assert y1[3] == y0[3] and z1[3] == z0[3]
        sig_y = lam
        sig_z = slack - lam
        ok_y = (2 ** (m - 1) - K(y0)) % p <= sig_y + y0[3]
        ok_z = (2 ** (m - 1) - K(z0)) % p <= sig_z + z0[3]
        assert not (ok_y and ok_z), ("survives", w, t, lam)
        killed += 1
    ws = sorted({w for w, _, _ in survivors})
    print(
        f"A: h={h} slack {slack}; first-level survivors {len(survivors)} (w in {ws}); all {killed} killed at the second level"
    )


def part_b(cert: Path) -> None:
    d = json.loads(cert.read_text())
    a = 204262101229170061472237061
    x = (2 * a, 52, 120, 0)
    assert tuple(d["parent"]) == x and d["depth"] == 106
    rows = sorted((tuple(r) for r in d["records"]), key=lambda r: r[0])
    ok: set[tuple[int, int, int, int]] = set()
    seen = set()
    checks = 0

    def child_ok(c, n):
        if min(c) < 0:
            return False
        if sum(c) <= 1:
            return True
        if vol(c, n) > 2**n:
            return False
        # padding: a core with <= 1 candidate is winnable at every depth
        return c[0] + c[1] + c[2] <= 1 or (n, c[0], c[1], c[2]) in ok

    for r in rows:
        n, s, q = r[0], r[1:5], r[5:9]
        assert len(r) == 9 and (n, *s[:3]) not in seen
        seen.add((n, *s[:3]))
        assert n >= 1 and min(s) >= 0 and all(0 <= qi <= si for qi, si in zip(q, s))
        assert vol(s, n) <= 2**n
        Y, N = both(s, q)
        assert vol(Y, n - 1) + vol(N, n - 1) == vol(s, n)
        for c in (Y, N):
            assert child_ok(c, n - 1), (r, c)
            checks += 1
        ok.add((n, *s[:3]))
    assert (106, *x[:3]) in ok and vol(x, 106) <= 2**106
    assert vol(x, 105) > 2**105
    root = [r for r in rows if r[0] == 106 and tuple(r[1:4]) == x[:3]][0]
    print(
        f"B: {len(rows)} rows, {checks} child checks; parent {x} 106-winnable via first question {root[5:9]}; 105 ruled out by volume"
    )


def paper_literals() -> None:
    """Every number Section 7 of the paper states, recomputed from the definitions."""
    from math import gcd
    a = (2**105 - 153920) // 198592
    assert 198592 * a == 2**105 - 153920 and a == 204262101229170061472237061
    h = (a, a + 26, 86, 60)
    assert vol(h, 105) == 198592 * a + 153892 == 2**105 - 28
    K = sum(h[i] * cap(104, i + 1) for i in range(3))
    assert K == 5566 * a + 2816
    assert binom(104, 3) == 182104 == 34 * 5356 and binom(104, 2) == 5356
    assert (2**104 - K) % 5356 == 1838 and 1838 + 5356 == 7194 and 104 * 86 + 88 == 9032
    assert gcd(gcd(182104, 5356), 104) == 52
    assert (2**103 - 2 * a - 26) % 103 == 35 and (2**103 - 2 * a - 9) % 103 == 52
    for u, v, w, t in [(0, 0, 17, 0), (5, 9, 69, 3), (a, a + 26, 40, 60), (123, 456, 0, 0)]:
        Y, N = both(h, (u, v, w, t))
        KY = sum(Y[i] * cap(103, i + 1) for i in range(3))
        KN = sum(N[i] * cap(103, i + 1) for i in range(3))
        assert (KY - (2 * a + 26 + w)) % 103 == 0 and (KN - (2 * a + 9 - w)) % 103 == 0
    assert (35 - 69) % 103 == 69 and (52 + 17) % 103 == 69
    assert 86 - 69 + 18 == 35 and 28 + 60 - 70 + 17 == 35
    x = (2 * a, 52, 120, 0)
    assert both(x, (a, 25, 112, 0)) == ((a, a + 25, 139, 8), (a, a + 27, 33, 112))
    assert binom(105, 2) == 105 * 52
    assert vol((a, a + 25, 139, 8), 105) == vol((a, a + 27, 33, 112), 105) == 2**105 - 28
    print("paper literals: all match")


if __name__ == "__main__":
    paper_literals()
    part_a()
    part_b(Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).with_name("counter_certificate.json"))
    print("COUNTEREXAMPLE CONFIRMED (Claude independent check)")
