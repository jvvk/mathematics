"""Generate a Lean 4 proof that a*3^k + b is not in B/B for every k >= k0.

The carry set for each parity of k is the fitted union of chains and sporadic carries (hyps.json).
The generator only decides *which* constructor and index each move lands on, and how many digits to
peel in each zero-digit argument; Lean re-checks every such claim with omega, so a wrong guess makes
the file fail rather than prove something false.  Small k below the symbolic threshold are closed by
concrete certificates (exact carry lists) checked by `decide`.

usage: python3 gen_lean.py a b k0 [K]   ->  writes BalancedTernary/Fam_<a>_<b>.lean
"""

import json
import os
import sys
from fractions import Fraction as Fr

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "verify"))
from reach import explore

HERE = os.path.dirname(os.path.abspath(__file__))
OUTDIR = os.path.join(HERE, "..", "BalancedTernary")
H = json.load(open(f"{HERE}/hyps.json"))
H2 = json.load(open(f"{HERE}/hyps2.json")) if __import__("os").path.exists(f"{HERE}/hyps2.json") else {}
J = 10  # powers 3^k, 3^(k-1), ..., 3^(k-J) are omega atoms


def btdig(x: int) -> list[int]:
    d = []
    while x:
        c = x % 3
        c = -1 if c == 2 else c
        d.append(c)
        x = (x - c) // 3
    return d


def first_zero(x: int) -> int:
    """Position of the first zero balanced digit of x (a position past the top counts)."""
    d = btdig(x)
    return next((p for p, c in enumerate(d) if c == 0), len(d))


def lit(x) -> str:
    x = int(x)
    return f"({x})" if x < 0 else str(x)


def kpow(m: int) -> str:
    return "3 ^ k" if m == 0 else f"3 ^ (k - {m})"


def hcon(hi: int, v: str = "i") -> str:
    """Upper index constraint v <= k - hi (hi may be negative)."""
    return f"{v} + {hi} ≤ k" if hi >= 0 else f"{v} ≤ k + {-hi}"


def kx(j: int) -> str:
    return "k" if j == 0 else f"(k - {j})"


def ix(j: int) -> str:
    return "i" if j == 0 else f"(i - {j})"


def ipow(j: int, base: str = "i") -> str:
    return f"3 ^ {base}" if j == 0 else f"3 ^ ({base} - {j})"


class Fam:
    def __init__(self, a: int, b: int, par: int, M: int = 2):
        self.a, self.b, self.par, self.M = a, b, par, M
        bs = f"{'m' if b < 0 else 'p'}{abs(b)}"
        self.name = (f"F{a}_{bs}_{'e' if par == 0 else 'o'}" if M == 2 and f"{a},{b},{par}" in H
                     else f"F{a}_{bs}_{M}r{par}")
        src = H[f"{a},{b},{par}"] if M == 2 and f"{a},{b},{par}" in H else H2[f"{a},{b},{M},{par}"]
        self.ctors = [("z",)]
        for cl in src:
            g = Fr(*cl["g"])
            beta = Fr(*cl["beta"])
            sg = cl["sg"]
            assert beta.denominator == 1
            for s in cl["spor"]:
                s = Fr(*s)
                assert s.denominator == 1
                m = 0
                while (g * 3**m).denominator != 1:
                    m += 1
                self.ctors.append(("s", sg, int(g * 3**m), m, int(s)))
            for c in cl["chains"]:
                assert g.denominator == 1
                self.ctors.append(
                    (
                        "c",
                        sg,
                        int(g),
                        int(beta),
                        c["t"],
                        c["st"],
                        c["res"],
                        c["lo"],
                        c["hi"],
                    )
                )

    # ---------- numeric model ----------
    def value(self, n: int, k: int, i=None) -> int:
        c = self.ctors[n]
        if c[0] == "z":
            return 0
        if c[0] == "s":
            _, sg, P, m, s = c
            return sg * (P * 3 ** (k - m) + s)
        _, sg, g, beta, t, st, res, lo, hi = c
        return sg * (g * 3**k + beta - t * 3**i)

    def indices(self, n: int, k: int):
        c = self.ctors[n]
        if c[0] != "c":
            return [None]
        _, sg, g, beta, t, st, res, lo, hi = c
        return [i for i in range(lo, k - hi + 1) if st == 1 or i % st == res % st]

    def elements(self, k: int) -> dict:
        E = {}
        for n in range(len(self.ctors)):
            for i in self.indices(n, k):
                v = self.value(n, k, i)
                assert v not in E, "duplicate carry"
                E[v] = (n, i)
        return E

    def target(self, k: int, r: int, d: int, c: int):
        """Target (ctor, index) of the move, or None if (d, c) is impossible."""
        v = r + (self.a * 3**k + self.b) * d
        if (v - c) % 3:
            return None
        return self.E[k][(v - c) // 3]

    # ---------- Lean text ----------
    def val(self, n: int, idx: str) -> str:
        """Lean value of constructor n at index expression idx ('i', '(i - 1)', '5', '(k - 2)')."""
        c = self.ctors[n]
        if c[0] == "z":
            return "0"
        if c[0] == "s":
            _, sg, P, m, s = c
            inner = f"{lit(P)} * {kpow(m)} + {lit(s)}"
        else:
            _, sg, g, beta, t, st, res, lo, hi = c
            inner = f"{lit(g)} * 3 ^ k + {lit(beta)} - {lit(t)} * 3 ^ {idx}"
        return inner if sg == 1 else f"-({inner})"

    def cname(self, n: int) -> str:
        return {"z": "z", "s": f"s{n}", "c": f"c{n}"}[self.ctors[n][0]]

    def inductive(self) -> str:
        L = [
            f"/-- Carry set for k ≡ {self.par} (mod {self.M}). -/",
            f"inductive {self.name} (k : Nat) : Int → Prop",
            f"  | z : {self.name} k 0",
        ]
        for n, c in enumerate(self.ctors):
            if c[0] == "s":
                L.append(
                    f"  | s{n} (r : Int) (hr : r = {self.val(n, '')}) : {self.name} k r"
                )
            elif c[0] == "c":
                _, sg, g, beta, t, st, res, lo, hi = c
                h3 = f" (h3 : i % {st} = {res})" if st != 1 else ""
                L.append(
                    f"  | c{n} (i : Nat) (r : Int) (h1 : {lo} ≤ i) (h2 : {hcon(hi)}){h3}"
                    f" (hr : r = {self.val(n, 'i')}) : {self.name} k r"
                )
        return "\n".join(L)

    def mk_target(self, tn: int, idx: str) -> str:
        c = self.ctors[tn]
        if c[0] == "z":
            return "(by have : r' = 0 := by omega\n              rw [this]; exact .z)"
        if c[0] == "s":
            return f"(.s{tn} r' (by omega))"
        st = c[5]
        h3 = " (by omega)" if st != 1 else ""
        return f"(.c{tn} {idx} r' (by omega) (by omega){h3} (by omega))"

    def idx_repr(self, ti, k: int) -> str:
        if ti is None:
            return ""
        return str(ti) if ti <= 12 else (kx(k - ti) if ti <= k else f"(k + {ti - k})")

    def four_cases(self, k: int, r_of_k, idx_of, indent: str) -> list[str]:
        """Bullets for (d, c) in (1,1), (1,-1), (-1,1), (-1,-1)."""
        out = []
        for d in (1, -1):
            for c in (1, -1):
                ts = [self.target(kk, r_of_k(kk), d, c) for kk in (k, k + self.M)]
                if ts[0] is None:
                    assert ts[1] is None
                    out.append(f"{indent}· omega")
                    continue
                (tn, ti), (tn2, ti2) = ts
                assert tn == tn2
                idx = idx_of(ti, k)
                assert idx == idx_of(ti2, k + self.M), (idx, idx_of(ti2, k + self.M))
                out.append(f"{indent}· exact {self.mk_target(tn, idx)}")
        return out

    def katoms(self, indent: str) -> list[str]:
        L = [f"{indent}have := p3 k (k - 1) (by omega)"]
        top = max([-c[8] for c in self.ctors if c[0] == "c"] + [0])
        L += [f"{indent}have := p3 (k + {m}) {'k' if m == 1 else f'(k + {m - 1})'} (by omega)" for m in range(1, top + 1)]
        L += [
            f"{indent}have := p3 (k - {m}) (k - {m + 1}) (by omega)"
            for m in range(1, J)
        ]
        L.append(f"{indent}have := pow3_pos (k - {J})")
        return L

    def iatoms(self, D: int, indent: str, base: str = "i") -> list[str]:
        L = [f"{indent}have := p3 {base} ({base} - 1) (by omega)"]
        L += [
            f"{indent}have := p3 ({base} - {m}) ({base} - {m + 1}) (by omega)"
            for m in range(1, D)
        ]
        L.append(f"{indent}have := pow3_pos ({base} - {D})")
        return L

    def numpow(self, v: int, indent: str) -> str:
        return f"{indent}have : (3 : Int) ^ {v} = {3**v} := by decide"

    # ----- closure -----
    def step_lemma(self, n: int, K0: int) -> str:
        c = self.ctors[n]
        name = self.name
        head = (
            f"theorem {name}.step_{self.cname(n)} {{k : Nat}} (hk : KMIN ≤ k) (hpar : k % {self.M} = {self.par})"
            f" {{r r' d c : Int}}"
        )
        tail = (
            f"    (hd : d = 1 ∨ d = -1) (hc : c = 1 ∨ c = -1)\n"
            f"    (hv : r + ({self.a} * 3 ^ k + {lit(self.b)}) * d = 3 * r' + c) : {name} k r' := by"
        )
        body = self.katoms("  ")
        if c[0] == "z":
            args = "(hr : r = 0)"
            body += [
                "  subst hr",
                "  rcases hd with rfl | rfl <;> rcases hc with rfl | rfl",
            ]
            body += self.four_cases(
                K0, lambda kk: 0, lambda ti, kk: self.idx_repr(ti, kk), "  "
            )
        elif c[0] == "s":
            args = f"(hr : r = {self.val(n, '')})"
            body += ["  rcases hd with rfl | rfl <;> rcases hc with rfl | rfl"]
            body += self.four_cases(
                K0,
                lambda kk: self.value(n, kk),
                lambda ti, kk: self.idx_repr(ti, kk),
                "  ",
            )
        else:
            _, sg, g, beta, t, st, res, lo, hi = c
            h3 = f" (h3 : i % {st} = {res})" if st != 1 else ""
            args = f"{{i : Nat}} (h1 : {lo} ≤ i) (h2 : {hcon(hi)}){h3} (hr : r = {self.val(n, 'i')})"
            # generic pattern from a middle index, then the exceptional bottom indices
            mids = [i for i in self.indices(n, K0) if K0 // 3 <= i <= K0 // 2]

            def pat(kk, i):
                r = self.value(n, kk, i)
                res_ = []
                for d in (1, -1):
                    for cc in (1, -1):
                        tg = self.target(kk, r, d, cc)
                        res_.append(
                            None
                            if tg is None
                            else (tg[0], i - tg[1] if tg[1] is not None else None)
                        )
                return res_

            Q = 4 if any(c_[0] == "c" and c_[5] == 4 for c_ in self.ctors) else 2
            # generic pattern per residue of i mod Q (a step-1 chain may feed two step-2 chains)
            Pr = {}
            for i in mids:
                Pr.setdefault(i % Q, pat(K0, i))
                assert pat(K0, i) == Pr[i % Q], "generic pattern not periodic"
            split = len(set(map(str, Pr.values()))) > 1
            exc = [i for i in self.indices(n, K0) if i < K0 // 3 and pat(K0, i) != Pr[i % Q]]
            assert all(pat(K0, i) == Pr[i % Q] for i in self.indices(n, K0) if i >= K0 // 3), "top exception"
            tlo = [self.ctors[x[0]][7] for P in Pr.values() for x in P if x and self.ctors[x[0]][0] == "c"]
            B0 = max([1] + [i + 1 for i in exc] + [l + 1 for l in tlo])
            small = [i for i in self.indices(n, K0) if i < B0]
            alts = " ∨ ".join([f"i = {i}" for i in small] + [f"{B0} ≤ i"])
            pats = " | ".join(["rfl"] * len(small) + ["hi"])
            body += [f"  rcases (show {alts} by omega) with {pats}"]
            for i in small:
                body += ["  · " + self.numpow(i, "").strip()]
                body += ["    rcases hd with rfl | rfl <;> rcases hc with rfl | rfl"]
                body += self.four_cases(K0, (lambda kk, i=i: self.value(n, kk, i)),
                                        lambda ti, kk: self.idx_repr(ti, kk), "    ")
            body += ["  · have := p3 i (i - 1) (by omega)"]
            groups = [(None, next(iter(Pr.values())))] if not split else [(q, Pr.get(q)) for q in range(Q)]
            ind = "    "
            if split and Q == 2:
                body += ["    rcases Nat.mod_two_eq_zero_or_one i with hip | hip"]
                ind = "      "
            elif split:
                body += [f"    rcases (show {' ∨ '.join(f'i % {Q} = {q}' for q in range(Q))} by omega) with "
                         + " | ".join(["hip"] * Q)]
                ind = "      "
            for rsd, P in groups:
                if split:
                    body += [f"    · -- i % {Q} = {rsd}"]
                if P is None:
                    body += [f"{ind}omega"]
                    continue
                body += [f"{ind}rcases hd with rfl | rfl <;> rcases hc with rfl | rfl"]
                for x in P:
                    if x is None:
                        body.append(f"{ind}· omega")
                    else:
                        tn, off = x
                        assert off == 1 and self.ctors[tn][0] == "c"
                        body.append(f"{ind}· exact {self.mk_target(tn, '(i - 1)')}")
        return "\n".join([head, "    " + args, tail] + body)

    # ----- bound and no positive zero-free carry -----
    def bound_nzf(self, n: int) -> str:
        c = self.ctors[n]
        name = self.name
        cn = self.cname(n)
        L = []
        n_expr = f"({self.a} * 3 ^ k + {lit(self.b)})"
        if c[0] == "z":
            return ""
        if c[0] == "s":
            _, sg, P, m, s = c
            args = f"{{r : Int}} (hr : r = {self.val(n, '')})"
            L.append(
                f"theorem {name}.bd_{cn} {{k : Nat}} (hk : KMIN ≤ k) {args} : 2 - {n_expr} ≤ r := by"
            )
            L += self.katoms("  ") + ["  omega"]
            L.append(
                f"theorem {name}.nz_{cn} {{k : Nat}} (hk : KMIN ≤ k) {args} (hpos : 0 < r) : ¬ ZF r := by"
            )
            L += self.katoms("  ")
            if sg == -1:
                L.append("  omega")
            else:
                L += ["  intro h0", "  subst hr"] + self.peel_const(P, m, s, "  ")
            return "\n".join(L)
        _, sg, g, beta, t, st, res, lo, hi = c
        h3 = f" (h3 : i % {st} = {res})" if st != 1 else ""
        args = f"{{i : Nat}} (h1 : {lo} ≤ i) (h2 : {hcon(hi)}){h3} {{r : Int}} (hr : r = {self.val(n, 'i')})"
        mono = (f"  have := pow3_mono i {kx(hi)} (by omega)" if hi >= 0 else
                f"  have := pow3_le_shift i k {-hi} {3**(-hi)} (by decide) (by omega)")
        L.append(
            f"theorem {name}.bd_{cn} {{k : Nat}} (hk : KMIN ≤ k) {args} : 2 - {n_expr} ≤ r := by"
        )
        L += self.katoms("  ") + [mono, "  have := pow3_pos i", "  omega"]
        L.append(
            f"theorem {name}.nz_{cn} {{k : Nat}} (hk : KMIN ≤ k) {args} (hpos : 0 < r) : ¬ ZF r := by"
        )
        L += self.katoms("  ") + [mono, "  have := pow3_pos i"]
        if sg == -1:
            L.append("  omega")
            return "\n".join(L)
        p = first_zero(beta)
        Bz = max(lo, p + 3)
        small = [i for i in range(lo, Bz) if st == 1 or i % st == res % st]
        alts = " ∨ ".join([f"i = {i}" for i in small] + [f"{Bz} ≤ i"])
        pats = " | ".join(["rfl"] * len(small) + ["hi"])
        L += [
            "  intro h0",
            "  subst hr",
            f"  rcases (show {alts} by omega) with {pats}",
        ]
        for i in small:
            L.append("  · " + self.numpow(i, "").strip())
            L += self.peel_const(
                g, 0, beta - t * 3**i, "    ", extra=f" - {lit(t)} * 3 ^ {i}"
            )
        # generic: peel the digits of beta; the t*3^i term is divisible by 3^(p+1)
        L += ["  · skip"] + self.iatoms(p + 1, "    ")
        L += [
            (f"    have := pow3_le_mul (i - {j}) (k - {j}) {hi} {3**hi} (by decide) (by omega)" if hi >= 0 else
             f"    have := pow3_le_shift {ix(j)} {kx(j)} {-hi} {3**(-hi)} (by decide) (by omega)")
            for j in range(p + 1)
        ]
        L += [
            f"    have := pow3_le_mul 0 (i - {j}) {Bz - j} {3 ** (Bz - j)} (by decide) (by omega)"
            for j in range(p + 1)
        ]
        L += self.peel_generic(g, beta, t, p, "    ")
        return "\n".join(L)

    def peel_const(
        self, P: int, m: int, R: int, indent: str, extra: str = ""
    ) -> list[str]:
        """h0 : ZF (P*3^(k-m) + R [+ extra]).  Peel the low digits of R to its first zero digit."""
        L = []
        hyp = "h0"
        cur = R
        p = first_zero(R)
        assert m + p + 1 <= J, "not enough k-atoms"
        for j in range(p):
            dgt = btdig(cur)[0]
            nxt = (cur - dgt) // 3
            e = f"{lit(P)} * {kpow(m + j + 1)} + {lit(nxt)}"
            L.append(
                f"{indent}have h{j + 1} := ZF.down ({e}) {lit(dgt)} {hyp} (by omega) "
                f"({'.inl rfl' if dgt == 1 else '.inr rfl'}) (by omega)"
            )
            hyp = f"h{j + 1}"
            cur = nxt
        L.append(f"{indent}exact {hyp}.mod3 (by omega)")
        return L

    def peel_generic(self, g: int, beta: int, t: int, p: int, indent: str) -> list[str]:
        L = []
        hyp = "h0"
        cur = beta
        for j in range(p):
            dgt = btdig(cur)[0]
            nxt = (cur - dgt) // 3
            e = f"{lit(g)} * {kpow(j + 1)} + {lit(nxt)} - {lit(t)} * {ipow(j + 1)}"
            L.append(
                f"{indent}have h{j + 1} := ZF.down ({e}) {lit(dgt)} {hyp} (by omega) "
                f"({'.inl rfl' if dgt == 1 else '.inr rfl'}) (by omega)"
            )
            hyp = f"h{j + 1}"
            cur = nxt
        L.append(f"{indent}exact {hyp}.mod3 (by omega)")
        return L

    def generate(self, K0: int) -> str:
        self.E = {kk: self.elements(kk) for kk in (K0, K0 + self.M)}
        parts = [self.inductive()]
        for n in range(len(self.ctors)):
            parts.append(self.step_lemma(n, K0))
            bn = self.bound_nzf(n)
            if bn:
                parts.append(bn)
        # assemble the invariant lemmas
        nm = self.name
        cases_step, cases_bd, cases_nz = [], [], []
        for n, c in enumerate(self.ctors):
            cn = self.cname(n)
            if c[0] == "z":
                cases_step.append(f"  | z => exact {nm}.step_z hk hpar rfl hd hc hv")
                cases_bd.append("  | z => have := pow3_ge k 1 3 (by decide) (by omega); omega")
                cases_nz.append("  | z => omega")
            elif c[0] == "s":
                cases_step.append(
                    f"  | s{n} r hr => exact {nm}.step_{cn} hk hpar hr hd hc hv"
                )
                cases_bd.append(f"  | s{n} r hr => exact {nm}.bd_{cn} hk hr")
                cases_nz.append(f"  | s{n} r hr => exact {nm}.nz_{cn} hk hr hpos")
            else:
                h3 = " h3" if c[5] != 1 else ""
                cases_step.append(
                    f"  | c{n} i r h1 h2{h3} hr => exact {nm}.step_{cn} hk hpar h1 h2{h3} hr hd hc hv"
                )
                cases_bd.append(
                    f"  | c{n} i r h1 h2{h3} hr => exact {nm}.bd_{cn} hk h1 h2{h3} hr"
                )
                cases_nz.append(
                    f"  | c{n} i r h1 h2{h3} hr => exact {nm}.nz_{cn} hk h1 h2{h3} hr hpos"
                )
        n_expr = f"({self.a} * 3 ^ k + {lit(self.b)})"
        parts.append(
            "\n".join(
                [
                    f"theorem {nm}.step {{k : Nat}} (hk : KMIN ≤ k) (hpar : k % {self.M} = {self.par}) {{r r' d c : Int}}",
                    f"    (hr : {nm} k r) (hd : d = 1 ∨ d = -1) (hc : c = 1 ∨ c = -1)",
                    f"    (hv : r + {n_expr} * d = 3 * r' + c) : {nm} k r' := by",
                    "  cases hr with",
                ]
                + cases_step
            )
        )
        parts.append(
            "\n".join(
                [
                    f"theorem {nm}.bound {{k : Nat}} (hk : KMIN ≤ k) {{r : Int}} (hr : {nm} k r) : 2 - {n_expr} ≤ r := by",
                    "  cases hr with",
                ]
                + cases_bd
            )
        )
        parts.append(
            "\n".join(
                [
                    f"theorem {nm}.nz {{k : Nat}} (hk : KMIN ≤ k) {{r : Int}} (hr : {nm} k r) (hpos : 0 < r) : ¬ ZF r := by",
                    "  cases hr with",
                ]
                + cases_nz
            )
        )
        parts.append(
            "\n".join(
                [
                    f"theorem {nm}.main (k : Nat) (hk : KMIN ≤ k) (hpar : k % {self.M} = {self.par}) :",
                    f"    ¬ ∃ m N : Int, 0 < m ∧ ZF m ∧ 0 < N ∧ ZF N ∧ N = {n_expr} * m :=",
                    f"  not_BB_of_inv _ ({nm} k) .z",
                    f"    (fun _ _ _ _ hr hd hc hv => {nm}.step hk hpar hr hd hc hv)",
                    f"    (fun _ hr => {nm}.bound hk hr)",
                    f"    (fun _ _ _ hr hc hv hpos => {nm}.nz hk ({nm}.step hk hpar hr (.inl rfl) hc (by omega)) hpos)",
                ]
            )
        )
        return "\n\n".join(parts)


def main_class(a: int, b: int, k0: int, KMIN: int, M: int, r: int) -> None:
    """Prove a*3^k + b not in B/B for every k >= k0 with k % M = r."""
    f = Fam(a, b, r, M)
    bs = f"{'m' if b < 0 else 'p'}{abs(b)}"
    thm = f"not_BB_{a}_{bs}_{M}r{r}"
    K0 = next(k for k in range(26, 26 + M) if k % M == r)
    out = [f"/-\n  {a}·3^k {'-' if b < 0 else '+'} {abs(b)} is not in B/B for every k ≥ {k0} with k ≡ {r} (mod {M}).",
           "  Generated by guy-f31-bt/lean_gen/gen_lean.py; every step is re-checked by Lean (omega, decide).\n-/",
           "import BalancedTernary.TernCore", "", "namespace Tern", "",
           "set_option maxHeartbeats 4000000\nset_option linter.unusedVariables false\nset_option maxRecDepth 100000", "",
           f.generate(K0).replace("KMIN", str(KMIN)), ""]
    small = [k for k in range(k0, KMIN) if k % M == r]
    for k in small:
        n = a * 3**k + b
        acc, S = explore(n)
        assert not acc, f"k={k} is a member"
        out.append(f"theorem {thm}_k{k} : ¬ ∃ m N : Int, 0 < m ∧ ZF m ∧ 0 < N ∧ ZF N ∧ N = ({a} * 3 ^ {k} + {lit(b)}) * m :=")
        out.append(f"  not_BB_of_cert _ {sorted(S)} (by decide)")
        out.append("")
    alts = " ∨ ".join([f"k = {k}" for k in small] + [f"{KMIN} ≤ k"])
    pats = " | ".join(["rfl"] * len(small) + ["hk"])
    out += [f"/-- **Theorem.** {a}·3^k {'-' if b < 0 else '+'} {abs(b)} ∉ B/B for every k ≥ {k0} with k ≡ {r} (mod {M}). -/",
            f"theorem {thm} (k : Nat) (hk0 : {k0} ≤ k) (hkr : k % {M} = {r}) :",
            f"    ¬ ∃ m N : Int, 0 < m ∧ ZF m ∧ 0 < N ∧ ZF N ∧ N = ({a} * 3 ^ k + {lit(b)}) * m := by",
            f"  rcases (show {alts} by omega) with {pats}"]
    for k in small:
        out.append(f"  · exact {thm}_k{k}")
    out += [f"  · exact {f.name}.main k hk hkr", "", "end Tern", ""]
    path = f"{OUTDIR}/Fam_{a}_{bs}_{M}r{r}.lean"
    open(path, "w").write("\n".join(out))
    print("wrote", path)


def main():
    a, b, k0 = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    KMIN = int(sys.argv[4]) if len(sys.argv) > 4 else 14
    fams = [Fam(a, b, 0), Fam(a, b, 1)]
    bs = f"{'m' if b < 0 else 'p'}{abs(b)}"
    thm = f"not_BB_{a}_{bs}"
    out = [
        f"/-\n  {a}·3^k {'-' if b < 0 else '+'} {abs(b)} is not in B/B for every k ≥ {k0}.",
        "  Generated by guy-f31-bt/lean_gen/gen_lean.py; every step is re-checked by Lean (omega, decide).\n-/",
        "import BalancedTernary.TernCore",
        "",
        "namespace Tern",
        "",
        "set_option maxHeartbeats 4000000\nset_option linter.unusedVariables false",
        "",
    ]
    for f in fams:
        out.append(f.generate(26 + f.par).replace("KMIN", str(KMIN)))
        out.append("")
    # small k by concrete certificates
    small = list(range(k0, KMIN))
    for k in small:
        n = a * 3**k + b
        acc, S = explore(n)
        assert not acc, f"k={k} is a member"
        out.append(
            f"theorem {thm}_k{k} : ¬ ∃ m N : Int, 0 < m ∧ ZF m ∧ 0 < N ∧ ZF N ∧ N = ({a} * 3 ^ {k} + {lit(b)}) * m :="
        )
        out.append(f"  not_BB_of_cert _ {sorted(S)} (by decide)")
        out.append("")
    alts = " ∨ ".join([f"k = {k}" for k in small] + [f"{KMIN} ≤ k"])
    pats = " | ".join(["rfl"] * len(small) + ["hk"])
    out += [
        f"/-- **Theorem.** {a}·3^k {'-' if b < 0 else '+'} {abs(b)} ∉ B/B for every k ≥ {k0}. -/",
        f"theorem {thm} (k : Nat) (hk0 : {k0} ≤ k) :",
        f"    ¬ ∃ m N : Int, 0 < m ∧ ZF m ∧ 0 < N ∧ ZF N ∧ N = ({a} * 3 ^ k + {lit(b)}) * m := by",
        f"  rcases (show {alts} by omega) with {pats}",
    ]
    for k in small:
        out.append(f"  · exact {thm}_k{k}")
    out += [
        "  · rcases Nat.mod_two_eq_zero_or_one k with h | h",
        f"    · exact {fams[0].name}.main k hk h",
        f"    · exact {fams[1].name}.main k hk h",
        "",
        "end Tern",
        "",
    ]
    path = f"{OUTDIR}/Fam_{a}_{bs}.lean"
    open(path, "w").write("\n".join(out))
    print("wrote", path)


if __name__ == "__main__":
    if len(sys.argv) > 6:
        main_class(*map(int, sys.argv[1:7]))
    else:
        main()
