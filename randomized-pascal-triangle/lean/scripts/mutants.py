#!/usr/bin/env python3
"""Mutation tests for LeanProofs/RandPascal (MO 479618): every wrong variant must FAIL to check.

Each mutant copies one file to RandPascal/Mut.lean with a single textual change and compiles it
with `lake env lean` (single process, nice 15). Unmutated copies must pass (baseline).
"""
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
D = ROOT / "LeanProofs" / "RandPascal"
MUT = D / "Mut.lean"

MUTANTS = [
    ("step: parent j-1 -> j-2", "Basic.lean",
     "cell (c ⟨j, h⟩) (x (j - 1)) (x j)", "cell (c ⟨j, h⟩) (x (j - 2)) (x j)"),
    ("coins K n = n + 8 -> n + 4", "Sums.lean",
     "  have h3 : j + 3 < K n := by unfold K; omega", "  have h3 : j + 3 < n + 4 := by unfold K; omega"),
    ("marginal: drop the third weight", "Sums.lean",
     "∑ b₁ : Bool, ∑ b₂ : Bool, ∑ b₃ : Bool, w p b₁ * w p b₂ * w p b₃ * φ b₁ b₂ b₃ := by",
     "∑ b₁ : Bool, ∑ b₂ : Bool, ∑ b₃ : Bool, w p b₁ * w p b₂ * φ b₁ b₂ b₃ := by"),
    ("shift: drop the lower vanishing hypothesis", "Sums.lean",
     "(hlo : ∀ j, j < k → g j = 0) (hhi", "(hlo : ∀ j, j < 0 → g j = 0) (hhi"),
    ("(1): tails term |a-b| -> |a+b|", "TheoremA.lean",
     "E3 p (fun A _ _ => A) a b c d = p * (a + b) + (1 - p) * |a - b| := by",
     "E3 p (fun A _ _ => A) a b c d = p * (a + b) + (1 - p) * |a + b| := by"),
    ("(2): mixed-outcome factor p(1-p) -> 2p(1-p)", "TheoremA.lean",
     "    p * (1 - p) * ((a + b - |a - b|) + (b + c - |b - c|)) ≤",
     "    2 * p * (1 - p) * ((a + b - |a - b|) + (b + c - |b - c|)) ≤"),
    ("(1): 2p -> p", "TheoremA.lean",
     "P p n (S (n + 5)) x = 2 * p * S (n + 4) x", "P p n (S (n + 5)) x = p * S (n + 4) x"),
    ("lambda: 4p(1-p) -> 4p", "TheoremA.lean",
     "p ^ 2 + Real.sqrt (p ^ 4 + 4 * p * (1 - p))", "p ^ 2 + Real.sqrt (p ^ 4 + 4 * p)"),
    ("Theorem A: growth lambda^(n+1)", "TheoremA.lean",
     "    lamA p ^ n ≤ Exp p n (S (n + 4)) := by", "    lamA p ^ (n + 1) ≤ Exp p n (S (n + 4)) := by"),
    ("threshold: 2p^2-4p+1 < 0 -> < 1/10", "TheoremA.lean",
     "(h : 2 * p ^ 2 - 4 * p + 1 < 0) :", "(h : 2 * p ^ 2 - 4 * p + 1 < 1 / 10) :"),
    ("input window /4 -> /3", "TheoremB.lean",
     "  (a + b + c + d) / 4 + C.t", "  (a + b + c + d) / 3 + C.t"),
    ("output correction A+D-2B -> A+D-B", "TheoremB.lean",
     "    - C.al * (A + D - 2 * B)", "    - C.al * (A + D - B)"),
    ("W <= V2 -> W <= V", "TheoremB.lean",
     "lemma W_le_V2 (M : ℕ) (x : ℕ → ℝ) : W M x ≤ V2 M x :=",
     "lemma W_le_V2 (M : ℕ) (x : ℕ → ℝ) : W M x ≤ V M x :="),
    ("Theorem B: 5001/5000 -> 5002/5000", "TheoremB.lean",
     "(n : ℕ) : (5001 / 5000 : ℝ) ^ n ≤", "(n : ℕ) : (5002 / 5000 : ℝ) ^ n ≤"),
    ("quarter: 51/50 -> 52/50", "TheoremB.lean",
     "(n : ℕ) : (51 / 50 : ℝ) ^ n ≤", "(n : ℕ) : (52 / 50 : ℝ) ^ n ≤"),
    ("mean: last term lambda^(N-1) -> lambda^N", "Mean.lean",
     "    _ = lam ^ M := by field_simp; ring", "    _ = lam ^ (M + 1) := by field_simp; ring"),
    ("bridge value off by one", "Bridge.lean",
     "= 6757339 / 18750000 := by", "= 6757340 / 18750000 := by"),
]


def check(text: str) -> bool:
    MUT.write_text(text)
    r = subprocess.run(["nice", "-n", "15", "lake", "env", "lean", str(MUT)], cwd=ROOT,
                       capture_output=True, text=True, timeout=600)
    return r.returncode == 0 and "error" not in r.stdout


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
