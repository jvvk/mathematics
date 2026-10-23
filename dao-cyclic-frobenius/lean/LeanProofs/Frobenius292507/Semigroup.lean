import LeanProofs.Frobenius292507.Digits

/-!
# MO 292507: steps 7 to 9 of the answer

* `w_cong`, `w_le`, `w_max`: step 7, `w(d) = ∑ dᵢ xᵢ ≡ x₀ · v(d) (mod N)`, `w(d) ≤ nN` for a digit
  vector, `w(max) = nN`.
* `InS_add_N`, `InS_add_mul_N`: step 8, `s ∈ S`, `s > 0` give `s + kN ∈ S`
  (trade one `xᵢ` and `N` for `aᵢ` copies of `xᵢ₊₁`). A positive element has only nonzero
  representations, so "nonzero representation" is carried as `0 < s`.
* `carry_down`: step 9, every positive `s ∈ S` is `w(d) + kN` for a digit vector `d` with `w(d) > 0`
  (trade `a_{i-1}` copies of `xᵢ` for one `x_{i-1}`; the value drops by `N`).
-/

namespace Frobenius292507

open Finset

variable {n : ℕ} {a : ℕ → ℕ}

/-- The weight `w(d) = ∑ dᵢ xᵢ`. -/
def w (n : ℕ) (a : ℕ → ℕ) (d : ℕ → ℕ) : ℕ := ∑ i ∈ range n, d i * x n a i

lemma InS_w (d : ℕ → ℕ) : InS n a (w n a d) := ⟨d, rfl⟩

lemma InS_add {s t : ℕ} (hs : InS n a s) (ht : InS n a t) : InS n a (s + t) := by
  obtain ⟨c, rfl⟩ := hs
  obtain ⟨c', rfl⟩ := ht
  exact ⟨c + c', by simp [add_mul, sum_add_distrib]⟩

lemma InS_mul_x (hper : ∀ i, a (i + n) = a i) (hn : 1 ≤ n) (k i : ℕ) : InS n a (k * x n a i) := by
  refine ⟨fun j => if j = i % n then k else 0, ?_⟩
  simp only [ite_mul, zero_mul, sum_ite_eq', mem_range, Nat.mod_lt _ (show 0 < n by omega),
    ite_true, x_mod hper]

lemma exists_pos_coeff {c : ℕ → ℕ} {s : ℕ} (hs : ∑ i ∈ range n, c i * x n a i = s) (h : 0 < s) :
    ∃ i < n, 0 < c i := by
  by_contra hc
  push Not at hc
  have : s = 0 := by
    rw [← hs]; exact sum_eq_zero fun i hi => by rw [Nat.le_zero.1 (hc i (mem_range.1 hi)), zero_mul]
  omega

lemma w_pos_iff (hn : 1 ≤ n) {d : ℕ → ℕ} : 0 < w n a d ↔ ∃ i < n, 0 < d i := by
  constructor
  · intro h; exact exists_pos_coeff rfl h
  · rintro ⟨i, hi, hd⟩
    have := single_le_sum (f := fun j => d j * x n a j) (fun _ _ => Nat.zero_le _) (mem_range.2 hi)
    have := x_pos (a := a) hn i
    unfold w
    nlinarith

/-- **Step 7**: `w(d) ≡ x₀ · ∑ dᵢ πᵢ (mod N)`. -/
lemma w_cong (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i) (d : ℕ → ℕ) :
    (w n a d : ZMod (N n a)) = x n a 0 * v n a d := by
  unfold w v
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  rw [x_cong hper hpos (mem_range.1 hi)]
  ring

/-- **Step 7**: `w(max) = nN`, the sum identity of step 2. -/
lemma w_max (hn : 1 ≤ n) (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i) :
    w n a (fun i => b n a i - 1) = n * N n a := sum_identity hn hper hpos

/-- **Step 7**: `w(d) ≤ nN` for a digit vector. -/
lemma w_le (hn : 1 ≤ n) (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i) {d : ℕ → ℕ}
    (hd : IsDigit n a d) : w n a d ≤ n * N n a := by
  rw [← w_max hn hper hpos]
  exact sum_le_sum fun i hi => Nat.mul_le_mul_right _
    (show d i ≤ b n a i - 1 by have := hd i (mem_range.1 hi); omega)

/-- **Step 8**: if `s ∈ S` and `s > 0` then `s + N ∈ S`. -/
lemma InS_add_N (hn : 1 ≤ n) (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i) {s : ℕ}
    (hs : InS n a s) (h : 0 < s) : InS n a (s + N n a) := by
  obtain ⟨c, hc⟩ := hs
  obtain ⟨i, hi, hci⟩ := exists_pos_coeff hc h
  set c' : ℕ → ℕ := fun j => c j - if j = i then 1 else 0
  have key : ∀ j ∈ range n, c' j * x n a j + (if j = i then x n a j else 0) = c j * x n a j := by
    intro j _
    by_cases hj : j = i
    · subst hj
      simp only [c', ite_true]
      obtain ⟨r, hr⟩ : ∃ r, c j = r + 1 := ⟨c j - 1, by omega⟩
      rw [hr, Nat.add_sub_cancel]; ring
    · simp [c', hj]
  have hsplit : ∑ j ∈ range n, c' j * x n a j + x n a i = s := by
    rw [← hc, ← sum_congr rfl key, sum_add_distrib, sum_ite_eq', ite_eq_left (mem_range.2 hi)]
  have : s + N n a = ∑ j ∈ range n, c' j * x n a j + a i * x n a (i + 1) := by
    rw [carry hper hpos i]; omega
  rw [this]
  exact InS_add ⟨c', rfl⟩ (InS_mul_x hper hn _ _)

/-- **Step 8**, iterated: `s + kN ∈ S`. -/
lemma InS_add_mul_N (hn : 1 ≤ n) (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i) {s : ℕ}
    (hs : InS n a s) (h : 0 < s) (k : ℕ) : InS n a (s + k * N n a) := by
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc]
    exact InS_add_N hn hper hpos ih (by omega)

/-- **Step 9** (carrying down): a positive `s ∈ S` is `w(d) + kN`
for a digit vector `d` with `w(d) > 0`. -/
lemma carry_down (hn : 1 ≤ n) (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i)
    (hN : 1 ≤ N n a) : ∀ s, InS n a s → 0 < s →
      ∃ d k, IsDigit n a d ∧ 0 < w n a d ∧ s = w n a d + k * N n a := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    rintro ⟨c, hc⟩ hs
    by_cases hdig : IsDigit n a c
    · exact ⟨c, 0, hdig, by unfold w; rw [hc]; exact hs, by rw [← hc]; simp [w]⟩
    · simp only [IsDigit, not_forall, not_lt] at hdig
      obtain ⟨i, hi, hbi⟩ := hdig
      set j := (i + n - 1) % n
      have hj : j < n := Nat.mod_lt _ (by omega)
      set c' : ℕ → ℕ := fun k => c k - (if k = i then b n a i else 0) + (if k = j then 1 else 0)
      have key : ∀ k ∈ range n, c' k * x n a k + (if k = i then b n a i * x n a k else 0)
          = c k * x n a k + (if k = j then x n a k else 0) := by
        intro k _
        by_cases hki : k = i
        · rw [hki]
          obtain ⟨r, hr⟩ : ∃ r, c i = b n a i + r := ⟨c i - b n a i, by omega⟩
          simp only [c', ite_true, hr, Nat.add_sub_cancel_left]
          split_ifs <;> ring
        · simp only [c', hki, ite_false, Nat.sub_zero]
          split_ifs <;> ring
      have hsum : ∑ k ∈ range n, c' k * x n a k + b n a i * x n a i = s + x n a j := by
        have := sum_congr rfl key
        rw [sum_add_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq',
          ite_eq_left (mem_range.2 hi), ite_eq_left (mem_range.2 hj), hc] at this
        exact this
      rw [carry_b hn hper hpos i] at hsum
      set s' := ∑ k ∈ range n, c' k * x n a k
      have hsum' : s' + (x n a j + N n a) = s + x n a j := hsum
      have hs' : s = s' + N n a := by omega
      have hpos' : 0 < s' := by
        have h1 := single_le_sum (f := fun k => c' k * x n a k) (fun _ _ => Nat.zero_le _)
          (mem_range.2 hj)
        have h2 : 1 ≤ c' j := by simp only [c', ite_true]; omega
        have h3 := x_pos (a := a) hn j
        change c' j * x n a j ≤ s' at h1
        nlinarith
      obtain ⟨d, k, hd, hwd, hk⟩ := ih s' (by omega) ⟨c', rfl⟩ hpos'
      exact ⟨d, k + 1, hd, hwd, by rw [hs', hk, Nat.succ_mul]; ring⟩

end Frobenius292507
