#!/usr/bin/env python3
"""Mutation tests for LeanProofs/BalancedMast (agreement subtrees of balanced trees): every wrong
variant must FAIL to check.

Each mutant copies one file to BalancedMast/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, background QoS). Unmutated copies must pass (baseline).
"""
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "BalancedMast"
MUT = D / "Mut.lean"

MUTANTS = [
    ("triples: c outside the cluster -> inside", "Basic.lean",
     "∃ s ∈ S.subtrees, a ∈ s.L ∧ b ∈ s.L ∧ c ∉ s.L", "∃ s ∈ S.subtrees, a ∈ s.L ∧ b ∈ s.L ∧ c ∈ s.L"),
    ("restriction drops a nonempty half", "Restrict.lean",
     "    | some l', none => some l'", "    | some l', none => none"),
    ("substitution: product -> sum", "Subst.lean",
     "    mast (S.bind A) (T.bind B) ≤ mast S T * K := by", "    mast (S.bind A) (T.bind B) ≤ mast S T + K := by"),
    ("submultiplicativity -> subadditivity", "Balanced.lean",
     "theorem M_add_le (h k : ℕ) : M (h + k) ≤ M h * M k := by",
     "theorem M_add_le (h k : ℕ) : M (h + k) ≤ M h + M k := by"),
    ("grid lemma without the factor 2", "Grid.lean",
     "    Y.card ≤ 2 * max (2 ^ dS) (2 ^ dT) := by", "    Y.card ≤ max (2 ^ dS) (2 ^ dT) := by"),
    ("caterpillar 0 with two ranks swapped", "Example.lean",
     "[[0, 1, 2, 7, 11, 20, 38, 86]", "[[0, 1, 7, 2, 11, 20, 38, 86]"),
    ("cells not reversed in T", "Example.lean",
     "def fT (j w : ℕ) : ℕ := 128 * (cat w).1 + pos j (7 - (cat w).2)",
     "def fT (j w : ℕ) : ℕ := 128 * (cat w).1 + pos j (cat w).2"),
    ("M(2^11) <= 2^4", "Example.lean", "theorem M_eleven : M 11 ≤ 2 ^ 5 :=", "theorem M_eleven : M 11 ≤ 2 ^ 4 :="),
    ("Phi diagonal weight 4^c -> 8^c", "Lower.lean",
     "(4 : ℝ) ^ c * (x₁ ^ a + x₄ ^ a)", "(8 : ℝ) ^ c * (x₁ ^ a + x₄ ^ a)"),
    ("inflated lower bound for 2^c", "CertOne.lean", "def certQ2 : ℕ := 17764576", "def certQ2 : ℕ := 17764676"),
    ("root certificate with r^4", "CertOne.lean",
     "decide (r ^ 5 * certN ^ 2 ≤ S ^ 2 * 2 ^ (5 * certK))", "decide (r ^ 4 * certN ^ 2 ≤ S ^ 2 * 2 ^ (5 * certK))"),
    ("exponent 0.235 -> 0.24", "CertOne.lean",
     "(2 : ℝ) ^ ((m : ℝ) * (47 / 200)) ≤ M m", "(2 : ℝ) ^ ((m : ℝ) * (48 / 200)) ≤ M m"),
    ("a strategy that stops at the root", "TwoLevel.lean",
     "  [(Strat.both false Strat.stop Strat.stop),", "  [(Strat.stop),"),
    ("exponent 0.243 -> 0.244", "TwoLevel.lean",
     "(2 : ℝ) ^ ((m : ℝ) * (243 / 1000)) ≤ M m", "(2 : ℝ) ^ ((m : ℝ) * (244 / 1000)) ≤ M m"),
]


def check(text: str) -> bool:
    MUT.write_text(text)
    p = subprocess.Popen(["taskpolicy", "-c", "background", "lake", "env", "lean", str(MUT)], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                         start_new_session=True)
    try:
        out, _ = p.communicate(timeout=1200)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)  # lake's lean child too
        p.communicate()
        print("  (timed out: counted as not compiling)", flush=True)
        return False
    return p.returncode == 0 and "error" not in out


def main() -> int:
    bad = 0
    sel = [m for m in MUTANTS if not sys.argv[1:] or any(a in m[1] for a in sys.argv[1:])]
    try:
        for f in sorted({m[1] for m in sel}):
            ok = check((D / f).read_text())
            print(f"baseline {'ok' if ok else 'FAILS'}: {f}", flush=True)
            bad += not ok
        for name, f, old, new in sel:
            src = (D / f).read_text()
            if src.count(old) != 1:
                print(f"MUTATION DID NOT APPLY: {name}", flush=True)
                bad += 1
                continue
            if check(src.replace(old, new)):
                print(f"MUTANT SURVIVED: {name}", flush=True)
                bad += 1
            else:
                print(f"rejected: {name}", flush=True)
    finally:
        MUT.unlink(missing_ok=True)
    print(f"{len(sel)} mutants, {bad} problems")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
