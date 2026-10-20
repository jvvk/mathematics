"""Mutation harness for LeanProofs/Precarious/{Basic,Bound,Construct,Framework,Extensions,Closed,ClosedConstruct,Rotation}.lean: every mutant statement must be rejected."""
import os, subprocess, sys, tempfile

MUTANTS = [
    ("LeanProofs/Precarious/Basic.lean", "at most one colour", "((w.toFinset).filter (fun c => q ∣ r c)).card ≤ 2 := by", "((w.toFinset).filter (fun c => q ∣ r c)).card ≤ 1 := by"),
    ("LeanProofs/Precarious/Basic.lean", "counting off by one", "    r ∣ w.count x := by", "    r ∣ w.count x + 1 := by"),
    ("LeanProofs/Precarious/Basic.lean", "wrong power", "(hpairs : ∀ x ∈ w, ∀ y ∈ w, x ≠ y → IsPow (pair x y w) q) : IsPow w q := by", "(hpairs : ∀ x ∈ w, ∀ y ∈ w, x ≠ y → IsPow (pair x y w) q) : IsPow w (q + 1) := by"),
    ("LeanProofs/Precarious/Basic.lean", "shift doubled", "      = (((replicate q v).flatten).take j).count z + v.count z := by", "      = (((replicate q v).flatten).take j).count z + 2 * v.count z := by"),
    ("LeanProofs/Precarious/Basic.lean", "chain value", "    ∀ z ∈ A, (w.take (∑ z ∈ A, p z)).count z = p z := by", "    ∀ z ∈ A, (w.take (∑ z ∈ A, p z)).count z = p z + 1 := by"),
    ("LeanProofs/Precarious/Basic.lean", "period block", "    w = (replicate q (w.take B)).flatten := by", "    w = (replicate q (w.take (B + 1))).flatten := by"),
    ("LeanProofs/Precarious/Bound.lean", "bound plus one", "theorem lower_bound (w : List α) (hw : IsPrecarious w) : a w.toFinset.card ≤ w.length := by", "theorem lower_bound (w : List α) (hw : IsPrecarious w) : a w.toFinset.card + 1 ≤ w.length := by"),
    ("LeanProofs/Precarious/Bound.lean", "a(5) value", "a 5 = 126", "a 5 = 125"),
    ("LeanProofs/Precarious/Bound.lean", "arith strict", "    a k ≤ (k - S) * pr t + S * pr (t - 1) := by", "    a k + 1 ≤ (k - S) * pr t + S * pr (t - 1) := by"),
    ("LeanProofs/Precarious/Bound.lean", "primes product", "pr T.card ≤ ∏ p ∈ T, p := by", "pr (T.card + 1) ≤ ∏ p ∈ T, p := by"),
    ("LeanProofs/Precarious/Bound.lean", "odd formula", "((k - 1) * Nat.nth Nat.Prime (k / 2) + 1)", "(k * Nat.nth Nat.Prime (k / 2) + 1)"),
    ("LeanProofs/Precarious/Bound.lean", "fibre size", "  have hfib : ∀ p, (C.filter (fun c => q c = p)).card ≤ 2 := by", "  have hfib : ∀ p, (C.filter (fun c => q c = p)).card ≤ 1 := by"),
    ("LeanProofs/Precarious/Construct.lean", "even length", "      (evenWord m).length = 2 * m * pr m := by", "      (evenWord m).length = 2 * m * pr m + 1 := by"),
    ("LeanProofs/Precarious/Construct.lean", "odd colours", "    IsPrecarious (oddWord m) ∧ (oddWord m).toFinset.card = 2 * m + 1 ∧", "    IsPrecarious (oddWord m) ∧ (oddWord m).toFinset.card = 2 * m ∧"),
    ("LeanProofs/Precarious/Construct.lean", "no-power strength", "    p ∣ N / p := by", "    p * p ∣ N / p := by"),
    ("LeanProofs/Precarious/Construct.lean", "shift hypothesis", "(hD : ∀ l : Fin m, l ≠ i → pp l ∣ D)", "(hD : ∀ l : Fin m, l = i → pp l ∣ D)"),
    ("LeanProofs/Precarious/Construct.lean", "block period", "lemma block_shift_pr (m j : ℕ) : block m (j + pr m) = block m j := by", "lemma block_shift_pr (m j : ℕ) : block m (j + pr m + 1) = block m j := by"),
    ("LeanProofs/Precarious/Construct.lean", "attained length", "      IsPrecarious w ∧ w.toFinset.card = k ∧ w.length = a k := by", "      IsPrecarious w ∧ w.toFinset.card = k ∧ w.length = a k + 1 := by"),
    ("LeanProofs/Precarious/Construct.lean", "pair never flips", "if p ∣ j then [x, y] else [y, x]", "if p ∣ j then [x, y] else [x, y]"),
    ("LeanProofs/Precarious/Framework.lean", "six-k bound", "    (hsk : s ≤ w.toFinset.card) : 6 * w.toFinset.card ≤ w.length := by", "    (hsk : s ≤ w.toFinset.card) : 7 * w.toFinset.card ≤ w.length := by"),
    ("LeanProofs/Precarious/Framework.lean", "two-keep bound", "    2 * w.toFinset.card + 8 ≤ w.length := by", "    2 * w.toFinset.card + 9 ≤ w.length := by"),
    ("LeanProofs/Precarious/Framework.lean", "two primes six", "    (d1 : p₁ ∣ n) (d2 : p₂ ∣ n) : 6 ≤ n := by", "    (d1 : p₁ ∣ n) (d2 : p₂ ∣ n) : 7 ≤ n := by"),
    ("LeanProofs/Precarious/Framework.lean", "keep size", "theorem keep_three_bound (s : ℕ) (hs : 3 ≤ s)", "theorem keep_three_bound (s : ℕ) (hs : 2 ≤ s)"),
    ("LeanProofs/Precarious/Extensions.lean", "2k+8 attained", "      KeepPrec 2 w ∧ w.toFinset.card = k ∧ w.length = 2 * k + 8 := by", "      KeepPrec 2 w ∧ w.toFinset.card = k ∧ w.length = 2 * k + 7 := by"),
    ("LeanProofs/Precarious/Extensions.lean", "6k attained", "      KeepPrec 3 w ∧ w.toFinset.card = k ∧ w.length = 6 * k := by", "      KeepPrec 3 w ∧ w.toFinset.card = k ∧ w.length = 6 * k + 1 := by"),
    ("LeanProofs/Precarious/Extensions.lean", "keep below 2m", "(hm : 1 ≤ m) (hs : s < 2 * m) : KeepPrec s (extWord m n)", "(hm : 1 ≤ m) (hs : s ≤ 2 * m) : KeepPrec s (extWord m n)"),
    ("LeanProofs/Precarious/Extensions.lean", "base word", "def WR : List (Fin 3) := [1, 0, 0, 1, 2, 1]", "def WR : List (Fin 3) := [1, 0, 1, 0, 2, 1]"),
    ("LeanProofs/Precarious/Extensions.lean", "keep instead of delete", "    Symm ((evenWord m).filter (fun z => z ∉ J)) := by", "    Symm ((evenWord m).filter (fun z => z ∈ J)) := by"),
    ("LeanProofs/Precarious/Closed.lean", "formula exponent", "noncomputable def closedForm (k s : ℕ) : ℕ := s * pr (s / 2 + 1) + (k - s) * pr ((s + 1) / 2)", "noncomputable def closedForm (k s : ℕ) : ℕ := s * pr (s / 2 + 2) + (k - s) * pr ((s + 1) / 2)"),
    ("LeanProofs/Precarious/Closed.lean", "general bound plus one", "    (hsk : s < w.toFinset.card) : closedForm w.toFinset.card s ≤ w.length := by", "    (hsk : s < w.toFinset.card) : closedForm w.toFinset.card s + 1 ≤ w.length := by"),
    ("LeanProofs/Precarious/Closed.lean", "pairs disjoint without distinct primes", "      have hdisj : ∀ q ∈ Px x, ∀ q' ∈ Px x, q ≠ q' → Disjoint (e q) (e q') := by", "      have hdisj : ∀ q ∈ Px x, ∀ q' ∈ Px x, Disjoint (e q) (e q') := by"),
    ("LeanProofs/Precarious/ClosedConstruct.lean", "cluster keeps one more", "theorem clusterWord_keepPrec (h n : ℕ) (hh : 1 ≤ h) (hn : 1 ≤ n) : KeepPrec (2 * h) (clusterWord h n) := by", "theorem clusterWord_keepPrec (h n : ℕ) (hh : 1 ≤ h) (hn : 1 ≤ n) : KeepPrec (2 * h + 1) (clusterWord h n) := by"),
    ("LeanProofs/Precarious/ClosedConstruct.lean", "cluster length", "(clusterWord h n).length = 2 * h * pr (h + 1) + n * pr h := by", "(clusterWord h n).length = 2 * h * pr (h + 1) + n * pr (h + 1) := by"),
    ("LeanProofs/Precarious/ClosedConstruct.lean", "top case", "lemma closedForm_top (k : ℕ) (hk : 2 ≤ k) : closedForm k (k - 1) = a k := by", "lemma closedForm_top (k : ℕ) (hk : 2 ≤ k) : closedForm k (k - 1) = a k + 1 := by"),
    ("LeanProofs/Precarious/ClosedConstruct.lean", "exact attained", "      KeepPrec s w ∧ w.toFinset.card = k ∧ w.length = closedForm k s := by", "      KeepPrec s w ∧ w.toFinset.card = k ∧ w.length = closedForm k s + 1 := by"),
    ("LeanProofs/Precarious/Rotation.lean", "rotation bound", "    Symm w ↔ ∃ s, 0 < s ∧ s < w.length ∧ w.rotate s = w := by", "    Symm w ↔ ∃ s, 0 < s ∧ s ≤ w.length ∧ w.rotate s = w := by"),
    ("LeanProofs/Precarious/Rotation.lean", "filter not rotated", "    ∃ t', (w.rotate t).filter p = (w.filter p).rotate t' := by", "    ∃ t', (w.rotate t).filter p = (w.filter p).rotate t' ∧ t' = 0 := by"),
    ("LeanProofs/Precarious/Rotation.lean", "rotation flips symmetry", "theorem symm_rotate (w : List α) (t : ℕ) : Symm (w.rotate t) ↔ Symm w := by", "theorem symm_rotate (w : List α) (t : ℕ) : Symm (w.rotate t) ↔ ¬ Symm w := by"),
    ("LeanProofs/Precarious/ClosedConstruct.lean", "wrong kept size", "    IsPrecarious w ↔ KeepPrec (w.toFinset.card - 1) w := by", "    IsPrecarious w ↔ KeepPrec (w.toFinset.card - 2) w := by"),
]


tmpdir = tempfile.mkdtemp(dir=os.environ.get("TMPDIR"))
killed = 0
ONLY = sys.argv[1] if len(sys.argv) > 1 else ""
MUTANTS = [m for m in MUTANTS if ONLY in m[0]]
for SRC, name, old, new in MUTANTS:
    src = open(SRC).read()
    assert src.count(old) == 1, f"pattern not unique: {name}"
    path = os.path.join(tmpdir, "Mutant.lean")
    open(path, "w").write(src.replace(old, new))
    r = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True, timeout=900)
    ok = r.returncode != 0 or "error" in r.stdout
    killed += ok
    print(("killed  " if ok else "SURVIVED"), name, flush=True)
os.remove(os.path.join(tmpdir, "Mutant.lean")); os.rmdir(tmpdir)
print(f"{killed}/{len(MUTANTS)} mutants killed")
sys.exit(0 if killed == len(MUTANTS) else 1)
