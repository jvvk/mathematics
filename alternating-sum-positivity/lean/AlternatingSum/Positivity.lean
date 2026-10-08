import AlternatingSum.Corollaries

/-!
  Corollary 2, sharp form: for `n ≤ a + b`, `L(u,a,b,n) > 0` exactly when `a` is even and
  `n ≥ a/2`. The proof gives `z` and `w²` weight `1` each (here `w` weight 1, `z` weight 2):
  every term of `(R-1)^ν` has weight at least `ν`, and `(2z + w²)^ν` supplies every monomial of
  weight exactly `ν`.
-/

namespace Abdesselam

open MvPowerSeries Finset Nat

/-- All coefficients of weight `d 0 + 2 d 1 < 2k` vanish. -/
def Wt (k : ℕ) (F : PS) : Prop := ∀ d : Fin 2 →₀ ℕ, d 0 + 2 * d 1 < 2 * k → coeff d F = 0

theorem Wt_mul {k l : ℕ} {F G : PS} (hF : Wt k F) (hG : Wt l G) : Wt (k + l) (F * G) := by
  classical
  intro d hd; rw [coeff_mul]
  refine sum_eq_zero fun p hp ↦ ?_
  rw [mem_antidiagonal] at hp
  have h0 : p.1 0 + p.2 0 = d 0 := by simpa using congrArg (· 0) hp
  have h1 : p.1 1 + p.2 1 = d 1 := by simpa using congrArg (· 1) hp
  by_cases hk : p.1 0 + 2 * p.1 1 < 2 * k
  · rw [hF _ hk, zero_mul]
  · rw [hG _ (by omega), mul_zero]

theorem Wt_zero (F : PS) : Wt 0 F := fun _ h ↦ absurd h (by omega)

theorem Wt_pow {k : ℕ} {F : PS} (hF : Wt k F) (n : ℕ) : Wt (k * n) (F ^ n) := by
  induction n with
  | zero => rw [mul_zero]; exact Wt_zero _
  | succ n ih => rw [pow_succ, mul_add, mul_one]; exact Wt_mul ih hF

theorem Wt_R_sub_one : Wt 1 (R - 1) := by
  intro d hd
  rw [coeff_R_sub_one]
  split_ifs with h0
  · rfl
  · have h1 : d 1 = 0 := by omega
    have h2 : d 0 = 1 := by
      by_contra h2
      apply h0; ext t; fin_cases t <;> simp <;> omega
    rw [coeff_R]; exact EvenW_R_pow 0 d (by rw [h2]; decide)

/-- A single term of the product bounds its coefficient from below. -/
theorem coeff_mul_ge {F G : PS} (hF : NN F) (hG : NN G) (d₁ d₂ : Fin 2 →₀ ℕ) :
    coeff d₁ F * coeff d₂ G ≤ coeff (d₁ + d₂) (F * G) := by
  classical
  rw [coeff_mul]
  exact single_le_sum (f := fun p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ) ↦ coeff p.1 F * coeff p.2 G)
    (a := (d₁, d₂)) (fun p _ ↦ mul_nonneg (hF _) (hG _)) (by rw [mem_antidiagonal])

theorem pos_pow {F : PS} (hF : NN F) (e : Fin 2 →₀ ℕ) (he : 0 < coeff e F) :
    ∀ k : ℕ, 0 < coeff (k • e) (F ^ k) := by
  classical
  intro k
  induction k with
  | zero => rw [zero_nsmul, pow_zero, coeff_one, ite_eq_left rfl]; norm_num
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact lt_of_lt_of_le (mul_pos ih he) (coeff_mul_ge (NN_pow hF k) hF _ _)

theorem nsmul_mono (k x y : ℕ) : k • mono x y = mono (k * x) (k * y) := by
  ext t; fin_cases t <;> simp

/-- `(R-1)^ν` has a positive coefficient at every monomial `w^(2i) z^(ν-i)`, `i ≤ ν`. -/
theorem pos_R_sub_one_pow (i j : ℕ) : 0 < coeff (mono (2 * i) j) ((R - 1) ^ (i + j)) := by
  have hw : 0 < coeff (mono 2 0) (R - 1) := by
    rw [coeff_R_sub_one, ite_eq_right (by simp [mono]), coeff_R, coeff_R_pow]; norm_num
  have hz : 0 < coeff (mono 0 1) (R - 1) := by
    rw [coeff_R_sub_one, ite_eq_right (by simp [mono]), coeff_R, coeff_R_pow]; norm_num
  have h1 := pos_pow NN_R_sub_one _ hw i
  have h2 := pos_pow NN_R_sub_one _ hz j
  rw [nsmul_mono] at h1 h2
  simp only [mul_zero, mul_one] at h1 h2
  have := coeff_mul_ge (NN_pow NN_R_sub_one i) (NN_pow NN_R_sub_one j) (mono (i * 2) 0) (mono 0 j)
  rw [mono_add, ← pow_add, add_zero, zero_add] at this
  rw [mul_comm 2 i]
  exact lt_of_lt_of_le (mul_pos h1 h2) this

/-- **Corollary 2:** for `n ≤ a + b`, `L > 0` exactly when `a` is even and `a ≤ 2n`. -/
theorem L_pos_iff (u a b n : ℕ) (hn : n ≤ a + b) :
    0 < L u a b n ↔ Even a ∧ a ≤ 2 * n := by
  rw [main u a b n hn]
  have hpref : (0 : ℚ) < ((u + (a + b - n)) ! : ℚ) ^ 2 / ((a + b - n) ! : ℚ) := by positivity
  rw [mul_pos_iff_of_pos_left hpref]
  constructor
  · intro h
    refine ⟨by_contra fun ha ↦ ?_, by_contra fun hlt ↦ ?_⟩
    · rw [EvenW_mul (EvenW_R_pow u) (EvenW_pow EvenW_R_sub_one _) _ (by simpa using ha)] at h
      exact lt_irrefl 0 h
    · have hw := Wt_mul (Wt_zero (R ^ (u + 1))) (Wt_pow Wt_R_sub_one (a + b - n))
      rw [hw (mono a b) (by simp; omega)] at h
      exact lt_irrefl 0 h
  · rintro ⟨⟨r, rfl⟩, h2⟩
    -- split `w^a z^b` as `w^(2(r-i)) z^(b-j) · w^(2i) z^j` with `i + j = ν`
    set ν := r + r + b - n with hν
    set i := ν - min ν b with hi
    set j := min ν b with hj
    have hij : i + j = ν := by omega
    have hpos2 := pos_R_sub_one_pow i j
    rw [hij] at hpos2
    have hpos1 : 0 < coeff (mono (2 * (r - i)) (b - j)) (R ^ (u + 1)) := by
      rw [coeff_R_pow, ite_eq_left (by exact ⟨r - i, by ring⟩)]
      exact mul_pos (by exact_mod_cast Nat.choose_pos (by omega))
        (by exact_mod_cast Nat.choose_pos (by omega))
    have := coeff_mul_ge (NN_R_pow u) (NN_pow NN_R_sub_one ν) (mono (2 * (r - i)) (b - j))
      (mono (2 * i) j)
    rw [mono_add, show 2 * (r - i) + 2 * i = r + r by omega, show b - j + j = b by omega] at this
    exact lt_of_lt_of_le (mul_pos hpos1 hpos2) this

end Abdesselam
