import Mathlib

/-!
# Every taxicab distance once (MSE 4967838)

`n` lattice points *realise* `N = n(n-1)/2` if the taxicab distances of the pairs `i < j` are
`1, 2, …, N`, each exactly once.

* `odd_tdist_iff`: a distance is odd exactly when the endpoints have different colours (parity of
  `x + y`);
* `card_cross`: the pairs of different colours number `a * b`;
* `card_odd_Icc`: `1, …, N` contains `(N + 1) / 2` odd numbers;
* `parity`: so `(a - b)² = n - 2 (N mod 2)`, and `N` is even iff `n ≡ 0, 1 (mod 4)`; hence
  `square_condition`: `n` is a square when `n ≡ 0, 1 (mod 4)`, and `n - 2` otherwise (the asker's
  condition);
* `eleven`: the eleven points of the note realise `55`, with colour split `7, 4`.
-/

open Finset

namespace TaxicabEleven

/-- Taxicab distance. -/
def tdist (p q : ℤ × ℤ) : ℤ := |p.1 - q.1| + |p.2 - q.2|

/-- The pairs `i < j`. -/
def pairs (n : ℕ) : Finset (Fin n × Fin n) := univ.filter fun ij => ij.1 < ij.2

/-- `P` realises `N`: the distances of the pairs `i < j` are `1, …, N`, each once. -/
def Realises {n : ℕ} (P : Fin n → ℤ × ℤ) (N : ℕ) : Prop :=
  Set.InjOn (fun ij : Fin n × Fin n => tdist (P ij.1) (P ij.2)) (pairs n) ∧
    (pairs n).image (fun ij => tdist (P ij.1) (P ij.2)) = Icc (1 : ℤ) N

/-- The colour of a point: the parity of `x + y`. -/
def colour (p : ℤ × ℤ) : Prop := Odd (p.1 + p.2)

instance (p : ℤ × ℤ) : Decidable (colour p) := by unfold colour; infer_instance

lemma odd_tdist_iff (p q : ℤ × ℤ) : Odd (tdist p q) ↔ ¬ (colour p ↔ colour q) := by
  unfold tdist colour
  rw [← Int.not_even_iff_odd, Int.even_add, even_abs, even_abs, ← Int.not_even_iff_odd,
    ← Int.not_even_iff_odd, Int.even_sub, Int.even_sub, Int.even_add, Int.even_add]
  tauto

/-- Pairs of different colours: `a * b`, where `a` points have one colour and `b` the other. -/
lemma card_cross {n : ℕ} (c : Fin n → Prop) [DecidablePred c] :
    ((pairs n).filter fun ij => ¬ (c ij.1 ↔ c ij.2)).card =
      (univ.filter c).card * (univ.filter fun i => ¬ c i).card := by
  rw [← card_product]
  refine card_nbij' (fun ij => if c ij.1 then ij else (ij.2, ij.1))
    (fun uv => (min uv.1 uv.2, max uv.1 uv.2)) ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ h
    simp only [pairs, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h
    simp only [coe_product, coe_filter, mem_univ, true_and, Set.mem_prod, Set.mem_ofPred_eq]
    by_cases hi : c i <;> simp only [hi, ite_true, ite_false] <;> tauto
  · rintro ⟨u, v⟩ h
    simp only [coe_product, coe_filter, mem_univ, true_and, Set.mem_prod, Set.mem_ofPred_eq] at h
    simp only [pairs, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq]
    have huv : u ≠ v := by rintro rfl; exact h.2 h.1
    rcases lt_or_gt_of_ne huv with hl | hl
    · simp only [min_eq_left hl.le, max_eq_right hl.le]; exact ⟨hl, by tauto⟩
    · simp only [min_eq_right hl.le, max_eq_left hl.le]; exact ⟨hl, by tauto⟩
  · rintro ⟨i, j⟩ h
    simp only [pairs, coe_filter, mem_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h
    by_cases hi : c i
    · simp [hi, min_eq_left h.1.le, max_eq_right h.1.le]
    · simp [hi, min_eq_right h.1.le, max_eq_left h.1.le]
  · rintro ⟨u, v⟩ h
    simp only [coe_product, coe_filter, mem_univ, true_and, Set.mem_prod, Set.mem_ofPred_eq] at h
    have huv : u ≠ v := by rintro rfl; exact h.2 h.1
    rcases lt_or_gt_of_ne huv with hl | hl
    · simp [min_eq_left hl.le, max_eq_right hl.le, h.1]
    · have hv : ¬ c v := h.2
      simp [min_eq_right hl.le, max_eq_left hl.le, hv]

/-- `1, …, N` contains `(N + 1) / 2` odd numbers. -/
lemma card_odd_Icc (N : ℕ) : ((Icc (1 : ℤ) N).filter Odd).card = (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have h : Icc (1 : ℤ) ((N + 1 : ℕ) : ℤ) = insert ((N : ℤ) + 1) (Icc (1 : ℤ) (N : ℤ)) := by
      ext x; simp only [mem_Icc, mem_insert]; push_cast; omega
    rw [h, filter_insert]
    have hn : (N : ℤ) + 1 ∉ Icc (1 : ℤ) N := by simp
    rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩
    · have ho : Odd ((N : ℤ) + 1) := ⟨k, by rw [hk]; push_cast; ring⟩
      simp only [ho, ↓reduceIte]
      rw [card_insert_of_notMem (by simp [hn]), ih]; omega
    · have ho : ¬ Odd ((N : ℤ) + 1) := by
        rw [Int.not_odd_iff_even]; exact ⟨k + 1, by rw [hk]; push_cast; ring⟩
      simp only [ho, ↓reduceIte]; rw [ih]; omega

/-- `N = n(n-1)/2` is even exactly when `n ≡ 0, 1 (mod 4)`. -/
lemma choose_two_even_iff (n : ℕ) : n * (n - 1) / 2 % 2 = 0 ↔ n % 4 = 0 ∨ n % 4 = 1 := by
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 4 ∧ n = 4 * k + r :=
    ⟨n / 4, n % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 4).symm⟩
  have key : ∀ Q e : ℕ, (4 * k + r) * (4 * k + r - 1) = 2 * (2 * Q + e) →
      (n' : ℕ) → n' = 4 * k + r → (n' * (n' - 1) / 2 % 2 = 0 ↔ e % 2 = 0) := by
    intro Q e h n' hn; subst hn; rw [h, Nat.mul_div_cancel_left _ two_pos]; omega
  interval_cases r
  · rcases k with _ | k
    · simp
    · rw [key ((k + 1) * (4 * k + 3)) 0
        (by rw [show 4 * (k + 1) + 0 - 1 = 4 * k + 3 by omega]; ring) _ rfl]; omega
  · rw [key (k * (4 * k + 1)) 0 (by rw [show 4 * k + 1 - 1 = 4 * k by omega]; ring) _ rfl]; omega
  · rw [key (4 * k ^ 2 + 3 * k) 1 (by rw [show 4 * k + 2 - 1 = 4 * k + 1 by omega]; ring) _ rfl]
    omega
  · rw [key (4 * k ^ 2 + 5 * k) 3 (by rw [show 4 * k + 3 - 1 = 4 * k + 2 by omega]; ring) _ rfl]
    omega

/-- The parity count: with `a` points of one colour and `b` of the other,
`(a - b)² = n - 2 (N mod 2)`. -/
theorem parity {n : ℕ} (P : Fin n → ℤ × ℤ) (h : Realises P (n * (n - 1) / 2)) :
    (((univ.filter fun i => colour (P i)).card : ℤ) -
        (univ.filter fun i => ¬ colour (P i)).card) ^ 2 =
      n - 2 * ((n * (n - 1) / 2 % 2 : ℕ) : ℤ) := by
  -- the odd distances are the pairs of different colours, and they are the odd numbers ≤ N
  have hodd : (univ.filter fun i => colour (P i)).card *
      (univ.filter fun i => ¬ colour (P i)).card = (n * (n - 1) / 2 + 1) / 2 := by
    rw [← card_cross (fun i => colour (P i)), ← card_odd_Icc, ← h.2, filter_image,
      card_image_of_injOn (h.1.mono (by intro x hx; exact (mem_filter.mp hx).1))]
    congr 1; ext ij; simp [odd_tdist_iff]
  have hab : (univ.filter fun i => colour (P i)).card +
      (univ.filter fun i => ¬ colour (P i)).card = n := by
    simpa using card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun i => colour (P i))
  set N := n * (n - 1) / 2 with hN
  set a := (univ.filter fun i => colour (P i)).card
  set b := (univ.filter fun i => ¬ colour (P i)).card
  have h2N : 2 * N = n * (n - 1) := by
    rw [hN]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
  have hhalf : 2 * ((N + 1) / 2) = N + N % 2 := by omega
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a, b]
  have h2N' : (2 * N : ℤ) = n * (n - 1) := by
    have := congrArg (fun m : ℕ => (m : ℤ)) h2N; push_cast [Nat.cast_sub hn] at this; linarith
  have hhalf' : (2 * ((N + 1) / 2) : ℤ) = N + (N % 2 : ℕ) := by exact_mod_cast hhalf
  have hodd' : (a * b : ℤ) = ((N + 1) / 2 : ℕ) := by exact_mod_cast hodd
  have hab' : (a + b : ℤ) = n := by exact_mod_cast hab
  push_cast at hhalf' hodd'
  have : ((a : ℤ) - b) ^ 2 = (a + b) ^ 2 - 4 * (a * b) := by ring
  rw [this, hab', hodd']
  push_cast
  linarith

/-- The asker's condition. -/
theorem square_condition {n : ℕ} (P : Fin n → ℤ × ℤ) (h : Realises P (n * (n - 1) / 2)) :
    (n % 4 = 0 ∨ n % 4 = 1 → IsSquare n) ∧ (n % 4 = 2 ∨ n % 4 = 3 → IsSquare (n - 2)) := by
  have hp := parity P h
  set d := ((univ.filter fun i => colour (P i)).card : ℤ) -
    (univ.filter fun i => ¬ colour (P i)).card
  constructor
  · intro h4
    rw [(choose_two_even_iff n).mpr h4] at hp
    refine ⟨d.natAbs, ?_⟩
    have : ((d.natAbs * d.natAbs : ℕ) : ℤ) = n := by
      push_cast; rw [abs_mul_abs_self, ← sq, hp]; simp
    exact_mod_cast this.symm
  · intro h4
    have hodd : n * (n - 1) / 2 % 2 = 1 := by
      have := (choose_two_even_iff n).not.mpr (by omega); omega
    rw [hodd] at hp
    have hn : 2 ≤ n := by omega
    refine ⟨d.natAbs, ?_⟩
    have : ((d.natAbs * d.natAbs : ℕ) : ℤ) = ((n - 2 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hn]; rw [abs_mul_abs_self, ← sq, hp]; push_cast; ring
    exact_mod_cast this.symm

/-- The eleven points of the note, `A, …, K`. -/
def eleven_pts : Fin 11 → ℤ × ℤ :=
  ![(0, 14), (0, 16), (1, 16), (7, 11), (8, 7), (11, 2), (12, 7), (14, 45), (17, 49), (23, 0),
    (23, 26)]

/-- The eleven points realise `55` (a finite check, done by hand in the note's table). -/
theorem eleven : Realises eleven_pts 55 := by
  have himg : (pairs 11).image (fun ij => tdist (eleven_pts ij.1) (eleven_pts ij.2)) =
      Icc (1 : ℤ) ((55 : ℕ) : ℤ) := by decide
  refine ⟨injOn_of_card_image_eq ?_, himg⟩
  rw [himg]; decide

/-- Their colour split is `7, 4`, as `parity` requires: `(7 - 4)² = 11 - 2`. -/
theorem eleven_split :
    (univ.filter fun i => colour (eleven_pts i)).card = 7 ∧
      (univ.filter fun i => ¬ colour (eleven_pts i)).card = 4 := by
  decide

end TaxicabEleven
