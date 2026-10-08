import LeanProofs.RandPascal.Basic

/-!
# Randomized Pascal triangle: marginals and window sums

* `marg3`: averaging a function of three distinct coins over all coin vectors is the average over
  those three coins alone (independence, by expanding the product of sums).
* `sum_shift`: shifting the index of a sum does nothing when the summand vanishes at both ends.
* `P_window`: the one-step expectation of a sum of functions of three consecutive new entries is
  the sum, over windows of four consecutive old entries, of a three-coin average.
-/

open Finset

namespace RandPascal

/-- A product over `Fin K` whose factors are `1` off three distinct indices. -/
lemma prod_three {K : ℕ} (f : Fin K → ℝ) {i j k : Fin K} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h1 : ∀ l, l ≠ i → l ≠ j → l ≠ k → f l = 1) : ∏ l, f l = f i * f j * f k := by
  rw [← prod_subset (subset_univ {i, j, k}) (fun l _ hl => by
    simp only [mem_insert, mem_singleton, not_or] at hl; exact h1 l hl.1 hl.2.1 hl.2.2)]
  rw [prod_insert (by simp [hij, hik]), prod_insert (by simp [hjk]), prod_singleton]; ring

/-- Averaging over all coins a function of three distinct coins. -/
lemma marg3 (p : ℝ) {K : ℕ} {i j k : Fin K} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (φ : Bool → Bool → Bool → ℝ) :
    ∑ c : Fin K → Bool, wt p c * φ (c i) (c j) (c k) =
      ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ b₃ : Bool, w p b₁ * w p b₂ * w p b₃ * φ b₁ b₂ b₃ := by
  classical
  -- indicator of the event `c i = b₁, c j = b₂, c k = b₃`, written as a product over coordinates
  let g : Bool → Bool → Bool → Fin K → Bool → ℝ := fun b₁ b₂ b₃ l β =>
    if l = i then (if β = b₁ then 1 else 0) else if l = j then (if β = b₂ then 1 else 0)
    else if l = k then (if β = b₃ then 1 else 0) else 1
  have hind : ∀ (c : Fin K → Bool) b₁ b₂ b₃, ∏ l, g b₁ b₂ b₃ l (c l) =
      (if c i = b₁ then 1 else 0) * (if c j = b₂ then 1 else 0) * (if c k = b₃ then 1 else 0) := by
    intro c b₁ b₂ b₃
    rw [prod_three _ hij hik hjk (fun l h1 h2 h3 => by simp [g, h1, h2, h3])]
    simp [g, hij.symm, hik.symm, hjk.symm]
  have hexp : ∀ (c : Fin K → Bool), φ (c i) (c j) (c k) = ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ b₃ : Bool,
      ((if c i = b₁ then 1 else 0) * (if c j = b₂ then 1 else 0) * (if c k = b₃ then 1 else 0)) *
        φ b₁ b₂ b₃ := by
    intro c
    cases c i <;> cases c j <;> cases c k <;> simp
  have hmass : ∀ b₁ b₂ b₃, ∑ c : Fin K → Bool, wt p c * ∏ l, g b₁ b₂ b₃ l (c l) =
      w p b₁ * w p b₂ * w p b₃ := by
    intro b₁ b₂ b₃
    have : ∀ c : Fin K → Bool, wt p c * ∏ l, g b₁ b₂ b₃ l (c l) =
        ∏ l, (w p (c l) * g b₁ b₂ b₃ l (c l)) := fun c => by rw [wt, ← prod_mul_distrib]
    simp_rw [this]
    rw [← Fintype.prod_sum (fun l β => w p β * g b₁ b₂ b₃ l β)]
    rw [prod_three _ hij hik hjk (fun l h1 h2 h3 => by simp [g, h1, h2, h3, w_add])]
    simp [g, hij.symm, hik.symm, hjk.symm]
  calc ∑ c : Fin K → Bool, wt p c * φ (c i) (c j) (c k)
      = ∑ c : Fin K → Bool, ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ b₃ : Bool,
          wt p c * (∏ l, g b₁ b₂ b₃ l (c l)) * φ b₁ b₂ b₃ := by
        refine sum_congr rfl fun c _ => ?_
        rw [hexp c]; simp only [mul_sum, hind]; ring_nf
    _ = ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ b₃ : Bool,
          (∑ c : Fin K → Bool, wt p c * ∏ l, g b₁ b₂ b₃ l (c l)) * φ b₁ b₂ b₃ := by
        rw [sum_comm]; refine sum_congr rfl fun b₁ _ => ?_
        rw [sum_comm]; refine sum_congr rfl fun b₂ _ => ?_
        rw [sum_comm]; refine sum_congr rfl fun b₃ _ => ?_
        rw [sum_mul]
    _ = _ := by simp only [hmass]

/-- Shifting a sum by `k` when the summand vanishes below `k` and from `N` on. -/
lemma sum_shift (g : ℕ → ℝ) (N k : ℕ) (hlo : ∀ j, j < k → g j = 0) (hhi : ∀ j, N ≤ j → g j = 0) :
    ∑ j ∈ range N, g (j + k) = ∑ j ∈ range N, g j := by
  have h1 := prod_range_add (M := Multiplicative ℝ) g k N
  have h2 := prod_range_add (M := Multiplicative ℝ) g N k
  have e1 : ∑ j ∈ range (k + N), g j = ∑ j ∈ range k, g j + ∑ j ∈ range N, g (k + j) :=
    sum_range_add g k N
  have e2 : ∑ j ∈ range (N + k), g j = ∑ j ∈ range N, g j + ∑ j ∈ range k, g (N + j) :=
    sum_range_add g N k
  have z1 : ∑ j ∈ range k, g j = 0 := sum_eq_zero fun j hj => hlo j (mem_range.1 hj)
  have z2 : ∑ j ∈ range k, g (N + j) = 0 := sum_eq_zero fun j _ => hhi _ (by omega)
  rw [add_comm k N, z1, zero_add] at e1
  rw [z2, add_zero] at e2
  rw [e1] at e2
  simpa [add_comm] using e2

/-- The three-coin average of a function of the three new entries above a window `(a, b, c, d)`. -/
def E3 (p : ℝ) (Φ : ℝ → ℝ → ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  ∑ b₁ : Bool, ∑ b₂ : Bool, ∑ b₃ : Bool,
    w p b₁ * w p b₂ * w p b₃ * Φ (cell b₁ a b) (cell b₂ b c) (cell b₃ c d)

/-- One-step expectation of a window sum over the new row. -/
lemma P_window (p : ℝ) (n : ℕ) (x : ℕ → ℝ) (Φ : ℝ → ℝ → ℝ → ℝ) :
    P p n (fun y => ∑ j ∈ range (n + 5), Φ (y (j + 1)) (y (j + 2)) (y (j + 3))) x =
      ∑ j ∈ range (n + 5), E3 p Φ (x j) (x (j + 1)) (x (j + 2)) (x (j + 3)) := by
  unfold P
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 hj
  have h1 : j + 1 < K n := by unfold K; omega
  have h2 : j + 2 < K n := by unfold K; omega
  have h3 : j + 3 < K n := by unfold K; omega
  have key := marg3 p (i := ⟨j + 1, h1⟩) (j := ⟨j + 2, h2⟩) (k := ⟨j + 3, h3⟩)
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    (fun b₁ b₂ b₃ => Φ (cell b₁ (x j) (x (j + 1))) (cell b₂ (x (j + 1)) (x (j + 2)))
      (cell b₃ (x (j + 2)) (x (j + 3))))
  simp only [step, dif_pos h1, dif_pos h2, dif_pos h3]
  simpa [E3, Nat.add_sub_cancel] using key

end RandPascal
