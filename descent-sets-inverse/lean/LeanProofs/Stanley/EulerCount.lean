/-
  The combinatorial interpretation of the Entringer triangle: its entries count
  down-up permutations with a prescribed first value. In particular E n counts
  permutations whose descent set is altS n.
-/
import LeanProofs.Stanley.Entringer
import Mathlib.GroupTheory.Perm.Fin

namespace Stanley.Alt
open Finset Equiv

/-- Alternation expressed as comparisons of adjacent values. -/
theorem descP_eq_altS_iff {n : ℕ} (w : Perm (Fin n)) :
    descP w = altS n ↔ ∀ (i : ℕ) (h : i + 1 < n),
      (w ⟨i + 1, h⟩ < w ⟨i, by omega⟩ ↔ Even i) := by
  constructor
  · intro hw i hi
    have hmem := Finset.ext_iff.mp hw i
    simpa [descP, altS, show i < n - 1 by omega, hi] using hmem
  · intro hw
    ext i
    by_cases hi : i < n - 1
    · have h := hw i (by omega)
      simpa [descP, altS, hi, show i + 1 < n by omega] using h
    · simp [descP, altS, hi]

/-- Complement all values, reversing every comparison. -/
def complement {n : ℕ} (w : Perm (Fin n)) : Perm (Fin n) := w.trans Fin.revPerm

@[simp] theorem complement_apply {n : ℕ} (w : Perm (Fin n)) (i : Fin n) :
    complement w i = Fin.rev (w i) := rfl

@[simp] theorem complement_complement {n : ℕ} (w : Perm (Fin n)) :
    complement (complement w) = w := by ext i; simp

/-- Delete the first value and complement the standardized tail. -/
noncomputable def firstTail (n : ℕ) :
    Perm (Fin (n + 2)) ≃ Fin (n + 2) × Perm (Fin (n + 1)) :=
  Perm.decomposeFin'.trans (Equiv.prodCongr (Equiv.refl _)
    ({ toFun := complement, invFun := complement,
       left_inv := complement_complement, right_inv := complement_complement } :
         Perm (Fin (n + 1)) ≃ Perm (Fin (n + 1))))

@[simp] theorem firstTail_symm (n : ℕ) (k : Fin (n + 2)) (v : Perm (Fin (n + 1))) :
    (firstTail n).symm (k, v) = Perm.decomposeFin'Symm k (complement v) := rfl

/-- Standardization is increasing; value complementation flips the tail pattern. -/
theorem prepend_alternating_iff (n : ℕ) (k : Fin (n + 2)) (v : Perm (Fin (n + 1))) :
    descP ((firstTail n).symm (k, v)) = altS (n + 2) ↔
      descP v = altS (n + 1) ∧ n - (v 0 : ℕ) < (k : ℕ) := by
  rw [descP_eq_altS_iff, descP_eq_altS_iff]
  have htail (i : ℕ) (hi : i + 1 < n + 1) :
      (((firstTail n).symm (k, v)) ⟨i + 2, by omega⟩ <
        ((firstTail n).symm (k, v)) ⟨i + 1, by omega⟩) ↔
        ¬ (v ⟨i + 1, hi⟩ < v ⟨i, by omega⟩) := by
    change k.succAbove (Fin.rev (v ⟨i + 1, hi⟩)) <
      k.succAbove (Fin.rev (v ⟨i, by omega⟩)) ↔ _
    rw [(Fin.strictMono_succAbove k).lt_iff_lt, Fin.rev_lt_rev]
    have hn : v ⟨i, by omega⟩ ≠ v ⟨i + 1, hi⟩ := by
      intro h; have := v.injective h; have := congrArg Fin.val this; simp at this
    exact lt_iff_not_ge.trans (by constructor <;> intro h <;> order)
  have hzero : ((firstTail n).symm (k, v)) 1 < ((firstTail n).symm (k, v)) 0 ↔
      n - (v 0 : ℕ) < (k : ℕ) := by
    change k.succAbove (Fin.rev (v 0)) < k ↔ _
    rw [Fin.succAbove_lt_iff_castSucc_lt]
    simp [Fin.lt_def, Fin.val_rev]
  constructor
  · intro hw
    refine ⟨?_, ?_⟩
    · intro i hi
      have h := hw (i + 1) (by omega)
      rw [htail i hi] at h
      have hp : Even (i + 1) ↔ ¬ Even i := by rw [Nat.even_add_one, Nat.not_even_iff_odd]
      tauto
    · exact hzero.mp ((hw 0 (by omega)).mpr (by simp))
  · rintro ⟨hv, hk⟩ i hi
    cases i with
    | zero => simpa using hzero.mpr hk
    | succ i =>
      rw [htail i (by omega), hv i (by omega), Nat.even_add_one, Nat.not_even_iff_odd]

/-- Down-up permutations of size n+1 starting with the rank k. -/
def altFirst (n k : ℕ) : ℕ :=
  ((univ : Finset (Perm (Fin (n + 1)))).filter
    (fun w => descP w = altS (n + 1) ∧ (w 0 : ℕ) = k)).card

theorem altFirst_tail (n k : ℕ) (hk : k ≤ n + 1) :
    altFirst (n + 1) k =
      ((univ : Finset (Perm (Fin (n + 1)))).filter
        (fun v => descP v = altS (n + 1) ∧ n - (v 0 : ℕ) < k)).card := by
  classical
  let kf : Fin (n + 2) := ⟨k, by omega⟩
  unfold altFirst
  rw [card_filter, card_filter]
  calc
    _ = ∑ p : Fin (n + 2) × Perm (Fin (n + 1)),
        if descP ((firstTail n).symm p) = altS (n + 2) ∧
          (((firstTail n).symm p) 0 : ℕ) = k then 1 else 0 :=
      ((firstTail n).symm.sum_comp _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type, sum_comm]
      apply sum_congr rfl
      intro v _
      rw [sum_eq_single kf]
      · simp only [prepend_alternating_iff]
        change (if (descP v = altS (n + 1) ∧ n - (v 0 : ℕ) < k) ∧ k = k
          then 1 else 0) = _
        simp only [and_true]
      · intro j _ hj
        have hne : (j : ℕ) ≠ k := fun h => hj (Fin.ext h)
        rw [firstTail_symm]
        simp only [Perm.decomposeFin'Symm_zero, hne, and_false, ite_false]
      · simp

theorem altFirst_succ_zero (n : ℕ) : altFirst (n + 1) 0 = 0 := by
  rw [altFirst_tail n 0 (by omega)]
  simp

/-- The same cumulative recurrence as the reversed Entringer row. -/
theorem altFirst_succ_succ {n k : ℕ} (hk : k ≤ n) :
    altFirst (n + 1) (k + 1) = altFirst (n + 1) k + altFirst n (n - k) := by
  rw [altFirst_tail n (k + 1) (by omega), altFirst_tail n k (by omega), altFirst]
  rw [card_filter, card_filter, card_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  have hv := (v 0).is_lt
  by_cases h : descP v = altS (n + 1)
  · simp only [h, true_and]
    split_ifs <;> omega
  · simp [h]

theorem altFirst_eq_entry (n k : ℕ) (hk : k ≤ n) : altFirst n k = entry n k := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by omega
    subst k
    decide
  | succ n ih =>
    induction k with
    | zero => rw [altFirst_succ_zero, entry_succ_zero]
    | succ k ihk =>
      rw [altFirst_succ_succ (by omega), entry_succ_succ (by omega),
        ihk (by omega), ih (n - k) (by omega)]

/-- The original Euler-number definition counts alternating permutations. -/
theorem E_eq_card_alternating (n : ℕ) :
    E n = ((univ : Finset (Perm (Fin n))).filter
      (fun w => descP w = altS n)).card := by
  cases n with
  | zero => decide
  | succ n =>
    change entry (n + 1) (n + 1) = _
    rw [← altFirst_eq_entry (n + 1) (n + 1) (by omega),
      altFirst_tail n (n + 1) (by omega)]
    congr 1
    ext v
    simp only [mem_filter, mem_univ, true_and]
    have : n - (v 0 : ℕ) < n + 1 := by omega
    simp [this]

end Stanley.Alt
