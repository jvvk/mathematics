import LeanProofs.Lemniscates.TheoremA

/-!
# Corollaries: Cassini ovals and the pairs `(2,2)`, `(2,3)`

* `oval_le_six` (Corollary 2): two distinct Cassini ovals `|(z - a)(z - b)| = ρ` meet in at most six
  points. As in the paper: the coprime case and the case `R ≠ 0` need no finiteness; if `R = 0` then
  `f₁² = f₂²`, so `f₁ = f₂`, and two ovals with the same foci and a common point coincide.
* `bernoulli_six`: the Bernoulli lemniscates with foci `±1` and `0, 2` meet in six points.
* `M_eq_iff` (Corollary 3, second part): `M(n₁, n₂) = n₁ n₂ + n₂ + d e` equals `2 n₁ n₂ - 2`, for
  `2 ≤ n₁ ≤ n₂`, only for `(2, 2)` and `(2, 3)`.
-/

open Polynomial ComplexConjugate

namespace Lemniscates

open CaseI CaseII

/-- The Cassini oval with foci `a, b` and level `ρ`. -/
def oval (a b : ℂ) (ρ : ℝ) : Set ℂ := {z | ‖(z - a) * (z - b)‖ = ρ}

lemma oval_poly_eval (a b z : ℂ) : ((X - C a) * (X - C b)).eval z = (z - a) * (z - b) := by
  simp

lemma oval_poly_monic (a b : ℂ) : ((X - C a) * (X - C b)).Monic :=
  (monic_X_sub_C a).mul (monic_X_sub_C b)

lemma oval_poly_natDegree (a b : ℂ) : ((X - C a) * (X - C b)).natDegree = 2 := by
  rw [(monic_X_sub_C a).natDegree_mul (monic_X_sub_C b), natDegree_X_sub_C, natDegree_X_sub_C]

/-- Monic quadratics with equal squares are equal. -/
lemma eq_of_sq_eq {f g : ℂ[X]} (hf : f.Monic) (hg : g.Monic) (hfd : f.natDegree = 2)
    (hgd : g.natDegree = 2) (h : f ^ 2 = g ^ 2) : f = g := by
  have hsum : f + g ≠ 0 := by
    intro h0
    have := congrArg (fun p => p.coeff 2) h0
    simp only [coeff_add, coeff_zero] at this
    have h1 : f.coeff 2 = 1 := by rw [← hfd]; exact hf.coeff_natDegree
    have h2 : g.coeff 2 = 1 := by rw [← hgd]; exact hg.coeff_natDegree
    rw [h1, h2] at this
    norm_num at this
  have : (f - g) * (f + g) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' hsum

/-- **Corollary 2.** Two distinct Cassini ovals meet in at most six points. -/
theorem oval_le_six {a b c d : ℂ} {ρ₁ ρ₂ : ℝ} (h₁ : 0 < ρ₁) (h₂ : 0 < ρ₂)
    (hne : oval a b ρ₁ ≠ oval c d ρ₂)
    (F : Finset ℂ) (hF : ∀ z ∈ F, z ∈ oval a b ρ₁ ∧ z ∈ oval c d ρ₂) : F.card ≤ 6 := by
  classical
  set f₁ := (X - C a) * (X - C b)
  set f₂ := (X - C c) * (X - C d)
  have hf₁ := oval_poly_monic a b
  have hf₂ := oval_poly_monic c d
  have hd₁ := oval_poly_natDegree a b
  have hd₂ := oval_poly_natDegree c d
  have hmem : ∀ (p q : ℂ) (ρ : ℝ) (z : ℂ), 0 < ρ →
      (z ∈ oval p q ρ ↔ ‖((X - C p) * (X - C q)).eval z‖ ^ 2 = ρ ^ 2) := by
    intro p q ρ z hρ
    rw [oval_poly_eval]
    exact (pow_left_inj₀ (norm_nonneg _) hρ.le two_ne_zero).symm
  have hF' : ∀ z ∈ F, ‖f₁.eval z‖ ^ 2 = ρ₁ ^ 2 ∧ ‖f₂.eval z‖ ^ 2 = ρ₂ ^ 2 := fun z hz =>
    ⟨(hmem a b ρ₁ z h₁).mp (hF z hz).1, (hmem c d ρ₂ z h₂).mp (hF z hz).2⟩
  have h6 : 2 * f₁.natDegree * f₂.natDegree - 2 = 6 := by rw [hd₁, hd₂]
  by_cases hcop : IsCoprime f₁ f₂
  · have := caseI hf₁ hf₂ hd₁.ge hd₂.ge hcop (by positivity) F hF'
    rwa [h6] at this
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ] at hcop
  push Not at hcop
  obtain ⟨ζ, hζ₁, hζ₂⟩ := hcop
  rw [coe_aeval_eq_eval] at hζ₁ hζ₂
  by_cases hR : R f₁ f₂ (conjP f₁) (conjP f₂) ((ρ₁ ^ 2 : ℝ) : ℂ) ((ρ₂ ^ 2 : ℝ) : ℂ) = 0
  · -- `f₁² = f₂²`, so `f₁ = f₂`; a common point forces equal levels, hence equal ovals
    have hpow := pow_eq hf₁ hf₂ (by omega) (by omega) (by positivity) (by positivity) hR
    rw [hd₁, hd₂] at hpow
    have hfe : f₁ = f₂ := eq_of_sq_eq hf₁ hf₂ hd₁ hd₂ hpow
    rcases F.eq_empty_or_nonempty with hF0 | ⟨z₀, hz₀⟩
    · rw [hF0, Finset.card_empty]; omega
    · exfalso
      obtain ⟨e₁, e₂⟩ := hF' z₀ hz₀
      rw [hfe, e₂] at e₁
      have hρ : ρ₁ = ρ₂ := (pow_left_inj₀ h₁.le h₂.le two_ne_zero).mp e₁.symm
      apply hne
      ext z
      rw [hmem a b ρ₁ z h₁, hmem c d ρ₂ z h₂]
      change ‖f₁.eval z‖ ^ 2 = ρ₁ ^ 2 ↔ ‖f₂.eval z‖ ^ 2 = ρ₂ ^ 2
      rw [hfe, hρ]
  · have := count_of_R_ne_zero hf₁ hf₂ hd₁.ge hd₂.ge hζ₁ hζ₂ hR F hF'
    rwa [h6] at this

/-! ## Six is attained -/

/-- `⟨x, y⟩` lies on `‖z² - 1‖ = 1` when `(x² + y²)² = 2 (x² - y²)`. -/
lemma mem_bernoulli {x y : ℝ} (h : (x ^ 2 + y ^ 2) ^ 2 = 2 * (x ^ 2 - y ^ 2)) :
    (⟨x, y⟩ : ℂ) ∈ oval (-1) 1 1 := by
  show ‖((⟨x, y⟩ : ℂ) - -1) * ((⟨x, y⟩ : ℂ) - 1)‖ = 1
  have hn : Complex.normSq (((⟨x, y⟩ : ℂ) - -1) * ((⟨x, y⟩ : ℂ) - 1)) = 1 := by
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im]
    linear_combination h
  have h2 : ‖((⟨x, y⟩ : ℂ) - -1) * ((⟨x, y⟩ : ℂ) - 1)‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq, hn]
  have h0 := norm_nonneg (((⟨x, y⟩ : ℂ) - -1) * ((⟨x, y⟩ : ℂ) - 1))
  nlinarith

/-- `⟨x, y⟩` lies on `‖z (z - 2)‖ = 1` when `((x - 1)² + y²)² = 2 ((x - 1)² - y²)`. -/
lemma mem_bernoulli' {x y : ℝ} (h : ((x - 1) ^ 2 + y ^ 2) ^ 2 = 2 * ((x - 1) ^ 2 - y ^ 2)) :
    (⟨x, y⟩ : ℂ) ∈ oval 0 2 1 := by
  have := mem_bernoulli h
  have e : ∀ z : ℂ, (z - 0) * (z - 2) = (z - 1 - -1) * (z - 1 - 1) := fun z => by ring
  show ‖((⟨x, y⟩ : ℂ) - 0) * ((⟨x, y⟩ : ℂ) - 2)‖ = 1
  rw [e]
  have hz : (⟨x, y⟩ : ℂ) - 1 = ⟨x - 1, y⟩ := by apply Complex.ext <;> simp
  rw [hz]; exact this

/-- **Six is attained** by the Bernoulli lemniscates with foci `±1` and `0, 2`. -/
theorem bernoulli_six : ∃ F : Finset ℂ, F.card = 6 ∧
    ∀ z ∈ F, z ∈ oval (-1) 1 1 ∧ z ∈ oval 0 2 1 := by
  classical
  set s := Real.sqrt 2 with hs
  have hs2 : s ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs54 : 5 < 4 * s := by nlinarith
  set Y := (4 * s - 5) / 4 with hY
  have hY0 : 0 < Y := by rw [hY]; linarith
  set v := Real.sqrt Y
  have hv2 : v ^ 2 = Y := Real.sq_sqrt hY0.le
  have hv0 : 0 < v := Real.sqrt_pos.mpr hY0
  set t := Real.sqrt (2 / 3)
  have ht2 : t ^ 2 = 2 / 3 := Real.sq_sqrt (by norm_num)
  have ht0 : 0 < t := Real.sqrt_pos.mpr (by norm_num)
  set u := Real.sqrt (1 / 12)
  have hu2 : u ^ 2 = 1 / 12 := Real.sq_sqrt (by norm_num)
  have hu0 : 0 < u := Real.sqrt_pos.mpr (by norm_num)
  let pts : List ℂ := [⟨1 / 2, v⟩, ⟨1 / 2, -v⟩, ⟨1 / 2 + t, u⟩, ⟨1 / 2 + t, -u⟩,
    ⟨1 / 2 - t, u⟩, ⟨1 / 2 - t, -u⟩]
  have hnd : pts.Nodup := by
    simp only [pts, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, Complex.ext_iff, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals first | (intro h₁; linarith) | (rintro ⟨h₁, h₂⟩ <;> linarith)
  refine ⟨pts.toFinset, by rw [List.toFinset_card_of_nodup hnd]; rfl, fun z hz => ?_⟩
  simp only [pts, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
    or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨mem_bernoulli ?_, mem_bernoulli' ?_⟩ <;>
    simp only [neg_sq, hv2, hu2] <;>
    first
    | linear_combination (Y + (4 * s - 5) / 4 + 5 / 2) * hY + hs2
    | linear_combination (t ^ 2 + 2 * t + 1 / 3) * ht2
    | linear_combination (t ^ 2 - 2 * t + 1 / 3) * ht2

/-! ## The pairs where the Orevkov–Pakovich construction meets the bound -/

/-- `M(n₁, n₂) = n₁ n₂ + n₂ + d e` of Orevkov–Pakovich, `d = gcd`, `e = 1` iff `n₁ / d` is even. -/
def M (n₁ n₂ : ℕ) : ℕ :=
  n₁ * n₂ + n₂ + Nat.gcd n₁ n₂ * (if Even (n₁ / Nat.gcd n₁ n₂) then 1 else 0)

/-- **Corollary 3, second part.** -/
theorem M_eq_iff {n₁ n₂ : ℕ} (h₁ : 2 ≤ n₁) (h₁₂ : n₁ ≤ n₂) :
    M n₁ n₂ = 2 * n₁ * n₂ - 2 ↔ (n₁ = 2 ∧ n₂ = 2) ∨ (n₁ = 2 ∧ n₂ = 3) := by
  constructor
  · intro h
    have hd : Nat.gcd n₁ n₂ ≤ n₁ := Nat.gcd_le_left _ (by omega)
    have he : (if Even (n₁ / Nat.gcd n₁ n₂) then 1 else 0) ≤ 1 := by split_ifs <;> omega
    have hde : Nat.gcd n₁ n₂ * (if Even (n₁ / Nat.gcd n₁ n₂) then 1 else 0) ≤ n₁ :=
      le_trans (Nat.mul_le_mul_left _ he) (by rw [mul_one]; exact hd)
    have hmn : 2 * 2 ≤ n₁ * n₂ := Nat.mul_le_mul h₁ (le_trans h₁ h₁₂)
    have key : n₁ * n₂ ≤ n₂ + n₁ + 2 := by
      unfold M at h
      rw [show 2 * n₁ * n₂ = 2 * (n₁ * n₂) by ring] at h
      omega
    have hn₁ : n₁ = 2 := by
      by_contra hne
      have : 3 * n₂ ≤ n₁ * n₂ := Nat.mul_le_mul_right _ (by omega)
      omega
    subst hn₁
    have : n₂ ≤ 4 := by omega
    interval_cases n₂ <;> simp_all [M]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> decide

end Lemniscates
