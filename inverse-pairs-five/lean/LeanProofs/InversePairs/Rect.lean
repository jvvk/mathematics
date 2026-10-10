import Mathlib

/-!
# Inverse pairs (MSE 5146740): inverse pairs in a rectangle (Lemma 1)

`ψ` is the standard additive character of `ZMod p`, `K u v = ∑_{x unit} ψ (u x + v x⁻¹)` the
Kloosterman sum, and `WeilBound p` is Weil's bound `‖K u v‖ ≤ 2 √p` for `u, v ≠ 0`, quoted (it is
not in Mathlib) and carried as a hypothesis. `N p I J` counts units `x` with `x ∈ I` and `x⁻¹ ∈ J`.
* `indicator`: `[y ∈ I] = (1/p) ∑_u ∑_{a ∈ I} ψ (u (y - a))`;
* `N_expand`: `N = |I||J|/p + (1/p²) ∑_{u,v ≠ 0} Â u B̂ v (K u v + 1)`;
* `norm_A_le`, `sum_norm_A_le`: `‖Â u‖ ≤ 1/|sin (π u/p)|` and `∑_{u ≠ 0} ‖Â u‖ ≤ p (1 + log p)`;
* `rect`: `|N - |I||J|/p| ≤ 3 √p (1 + log p)²` (Lemma 1).
-/

open Finset Complex

namespace InversePairs

variable (p : ℕ) [hp : Fact p.Prime]

/-- The standard additive character of `ZMod p`. -/
noncomputable abbrev ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar

/-- The Kloosterman sum. -/
noncomputable def K (u v : ZMod p) : ℂ :=
  ∑ x : (ZMod p)ˣ, ψ p (u * x + v * ((x⁻¹ : (ZMod p)ˣ) : ZMod p))

/-- Weil's bound for Kloosterman sums (A. Weil 1948), quoted. -/
def WeilBound : Prop := ∀ u v : ZMod p, u ≠ 0 → v ≠ 0 → ‖K p u v‖ ≤ 2 * Real.sqrt p

/-- The number of units `x` with `x ∈ I` and `x⁻¹ ∈ J` (as residues in `0..p-1`). -/
noncomputable def N (I J : Finset ℕ) : ℕ :=
  #{x : (ZMod p)ˣ | (x : ZMod p).val ∈ I ∧ ((x⁻¹ : (ZMod p)ˣ) : ZMod p).val ∈ J}

/-- The Fourier coefficient `Â u = ∑_{a ∈ I} ψ (-(u a))`. -/
noncomputable def F (I : Finset ℕ) (u : ZMod p) : ℂ := ∑ a ∈ I, ψ p (-(u * a))

lemma prim : (ψ p).IsPrimitive := ZMod.isPrimitive_stdAddChar p

lemma orth (b : ZMod p) : ∑ u : ZMod p, ψ p (u * b) = if b = 0 then (p : ℂ) else 0 := by
  classical
  rw [AddChar.sum_mulShift b (prim p), ZMod.card]
  split_ifs <;> simp

lemma indicator (I : Finset ℕ) (hI : ∀ a ∈ I, a < p) (y : ZMod p) :
    (if y.val ∈ I then (1 : ℂ) else 0) = (1 / p) * ∑ u : ZMod p, ∑ a ∈ I, ψ p (u * (y - a)) := by
  classical
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [sum_comm]
  simp_rw [orth p]
  have key : ∀ a ∈ I, (y - (a : ZMod p) = 0 ↔ a = y.val) := fun a ha => by
    rw [sub_eq_zero]
    constructor
    · rintro rfl; rw [ZMod.val_cast_of_lt (hI a ha)]
    · rintro rfl; simp
  rw [sum_congr rfl fun a ha => if_congr (key a ha) rfl rfl, sum_ite_eq']
  split_ifs <;> simp [hp0]

lemma sum_F (I : Finset ℕ) (hI : ∀ a ∈ I, 1 ≤ a ∧ a < p) : ∑ u : ZMod p, F p I u = 0 := by
  classical
  simp only [F]
  rw [sum_comm]
  refine sum_eq_zero fun a ha => ?_
  have h := orth p (-(a : ZMod p))
  have hne : -(a : ZMod p) ≠ 0 := by
    rw [neg_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
    exact fun hd => by have := Nat.le_of_dvd (hI a ha).1 hd; have := (hI a ha).2; omega
  rw [ite_eq_right hne] at h
  rw [← h]
  exact sum_congr rfl fun u _ => by ring_nf

lemma K_zero_zero : K p 0 0 = p - 1 := by
  simp only [K, zero_mul, add_zero, AddChar.map_zero_eq_one, sum_const, card_univ,
    ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
  rw [nsmul_eq_mul, mul_one, Nat.cast_sub hp.out.one_le]; simp

lemma K_zero_left (v : ZMod p) (hv : v ≠ 0) : K p 0 v = -1 := by
  classical
  have hsum : ∑ y : ZMod p, ψ p (y * v) = 0 := by rw [orth p v, ite_eq_right hv]
  have hsplit : ∑ y : ZMod p, ψ p (y * v) = 1 + ∑ x : (ZMod p)ˣ, ψ p (x * v) := by
    rw [← Finset.sum_add_sum_compl {0}]
    simp only [Finset.sum_singleton, zero_mul, AddChar.map_zero_eq_one]
    congr 1
    refine Finset.sum_bij' (fun y hy => Units.mk0 y (by simpa using hy)) (fun x _ => (x : ZMod p))
      (fun _ _ => mem_univ _) (fun x _ => by simp) (fun _ _ => rfl) (fun x _ => by simp)
      (fun _ _ => rfl)
  have hinv : ∑ x : (ZMod p)ˣ, ψ p (x * v) = K p 0 v := by
    simp only [K, zero_mul, zero_add]
    exact Fintype.sum_equiv (Equiv.inv _) _ _ fun x => by simp [mul_comm]
  rw [hsplit, hinv] at hsum
  linear_combination hsum

lemma K_zero_right (u : ZMod p) (hu : u ≠ 0) : K p u 0 = -1 := by
  classical
  have hsum : ∑ y : ZMod p, ψ p (y * u) = 0 := by rw [orth p u, ite_eq_right hu]
  have hsplit : ∑ y : ZMod p, ψ p (y * u) = 1 + ∑ x : (ZMod p)ˣ, ψ p (x * u) := by
    rw [← Finset.sum_add_sum_compl {0}]
    simp only [Finset.sum_singleton, zero_mul, AddChar.map_zero_eq_one]
    congr 1
    refine Finset.sum_bij' (fun y hy => Units.mk0 y (by simpa using hy)) (fun x _ => (x : ZMod p))
      (fun _ _ => mem_univ _) (fun x _ => by simp) (fun _ _ => rfl) (fun x _ => by simp)
      (fun _ _ => rfl)
  have h2 : ∑ x : (ZMod p)ˣ, ψ p (x * u) = K p u 0 := by
    simp only [K, zero_mul, add_zero]
    exact sum_congr rfl fun x _ => by rw [mul_comm]
  rw [hsplit, h2] at hsum
  linear_combination hsum

lemma N_cast (I J : Finset ℕ) :
    (N p I J : ℂ) = ∑ x : (ZMod p)ˣ, (if (x : ZMod p).val ∈ I then (1 : ℂ) else 0) *
      (if ((x⁻¹ : (ZMod p)ˣ) : ZMod p).val ∈ J then 1 else 0) := by
  classical
  simp only [N, card_filter, Nat.cast_sum]
  refine sum_congr rfl fun x _ => ?_
  by_cases h1 : (x : ZMod p).val ∈ I <;> by_cases h2 : ((x⁻¹ : (ZMod p)ˣ) : ZMod p).val ∈ J
  · rw [ite_eq_left ⟨h1, h2⟩, ite_eq_left h1, ite_eq_left h2]; simp
  · rw [ite_eq_right (fun h => h2 h.2), ite_eq_left h1, ite_eq_right h2]; simp
  · rw [ite_eq_right (fun h => h1 h.1), ite_eq_right h1, ite_eq_left h2]; simp
  · rw [ite_eq_right (fun h => h1 h.1), ite_eq_right h1, ite_eq_right h2]; simp

lemma shift (x u : ZMod p) (I : Finset ℕ) :
    ∑ a ∈ I, ψ p (u * (x - a)) = ψ p (u * x) * F p I u := by
  simp only [F, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [← AddChar.map_add_eq_mul]; ring_nf

/-- The double Fourier expansion `N = (1/p²) ∑_{u,v} Â u B̂ v K u v`. -/
lemma N_expand (I J : Finset ℕ) (hI : ∀ a ∈ I, a < p) (hJ : ∀ b ∈ J, b < p) :
    (N p I J : ℂ) = (1 / (p : ℂ) ^ 2) * ∑ u, ∑ v, F p I u * F p J v * K p u v := by
  rw [N_cast]
  simp_rw [indicator p I hI, indicator p J hJ, shift]
  have e : ∀ x : (ZMod p)ˣ, (1 / (p : ℂ) * ∑ u, ψ p (u * x) * F p I u) *
      (1 / (p : ℂ) * ∑ v, ψ p (v * ((x⁻¹ : (ZMod p)ˣ) : ZMod p)) * F p J v) =
      (1 / (p : ℂ) ^ 2) * ∑ u, ∑ v, F p I u * F p J v *
        ψ p (u * x + v * ((x⁻¹ : (ZMod p)ˣ) : ZMod p)) := fun x => by
    rw [show ∀ A B : ℂ, (1 / (p : ℂ) * A) * (1 / (p : ℂ) * B) = 1 / (p : ℂ) ^ 2 * (A * B) from
      fun A B => by ring, sum_mul_sum]
    congr 1
    exact sum_congr rfl fun u _ => sum_congr rfl fun v _ => by rw [AddChar.map_add_eq_mul]; ring
  rw [sum_congr rfl fun x _ => e x, ← mul_sum]
  congr 1
  simp only [K, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun u _ => by rw [sum_comm]

/-- `N = |I||J|/p + (1/p²) ∑_{u,v ≠ 0} Â u B̂ v (K u v + 1)`. -/
lemma N_main (I J : Finset ℕ) (hI : ∀ a ∈ I, 1 ≤ a ∧ a < p) (hJ : ∀ b ∈ J, 1 ≤ b ∧ b < p) :
    (N p I J : ℂ) = (#I * #J : ℂ) / p + (1 / (p : ℂ) ^ 2) *
      ∑ u, ∑ v, (if u ≠ 0 ∧ v ≠ 0 then F p I u * F p J v * (K p u v + 1) else 0) := by
  classical
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [N_expand p I J (fun a ha => (hI a ha).2) (fun b hb => (hJ b hb).2)]
  have hF0 : ∀ (I : Finset ℕ), F p I 0 = #I := fun I => by simp [F]
  -- termwise: `K u v = K' u v - 1 + p [u = 0][v = 0]` with `K' = K + 1` off the axes
  have hterm : ∀ u v : ZMod p, F p I u * F p J v * K p u v =
      (if u ≠ 0 ∧ v ≠ 0 then F p I u * F p J v * (K p u v + 1) else 0) - F p I u * F p J v +
      (if u = 0 ∧ v = 0 then (p : ℂ) * (F p I 0 * F p J 0) else 0) := fun u v => by
    by_cases hu : u = 0 <;> by_cases hv : v = 0
    · subst hu hv; simp [K_zero_zero]; ring
    · subst hu; simp [hv, K_zero_left p v hv]
    · subst hv; simp [hu, K_zero_right p u hu]
    · simp [hu, hv]; ring
  have hsplit : ∑ u, ∑ v, F p I u * F p J v * K p u v =
      ∑ u, ∑ v, (if u ≠ 0 ∧ v ≠ 0 then F p I u * F p J v * (K p u v + 1) else 0)
        - (∑ u, F p I u) * (∑ v, F p J v) + p * (F p I 0 * F p J 0) := by
    simp_rw [hterm, sum_add_distrib, sum_sub_distrib, sum_mul_sum]
    congr 1
    rw [Finset.sum_eq_single (0 : ZMod p)]
    · simp
    · intro u _ hu; exact sum_eq_zero fun v _ => by simp [hu]
    · simp
  rw [hsplit, sum_F p I hI, sum_F p J hJ, hF0, hF0]
  field_simp
  ring

/-! ### The geometric-series bound -/

lemma psi_neg (u : ZMod p) :
    ψ p (-u) = exp (I * ((-2 * Real.pi * u.val / p : ℝ) : ℂ)) := by
  have : -u = ((-(u.val : ℤ) : ℤ) : ZMod p) := by push_cast; rw [ZMod.natCast_zmod_val]
  rw [this, ZMod.stdAddChar_coe]
  congr 1; push_cast; ring

lemma norm_psi (u : ZMod p) : ‖ψ p (-u)‖ = 1 := by rw [psi_neg]; exact norm_exp_I_mul_ofReal _

lemma norm_psi_sub_one (u : ZMod p) :
    ‖ψ p (-u) - 1‖ = 2 * |Real.sin (Real.pi * u.val / p)| := by
  rw [psi_neg, norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  rw [show -2 * Real.pi * u.val / p / 2 = -(Real.pi * u.val / p) by ring, Real.sin_neg, abs_neg]

/-- `‖Â u‖ ≤ 1/|sin (π u/p)|` for an interval `I` and `u ≠ 0`. -/
lemma norm_F_le (u : ZMod p) (hu : u ≠ 0) (α L : ℕ) :
    ‖F p (Ico α (α + L)) u‖ ≤ 1 / |Real.sin (Real.pi * u.val / p)| := by
  have hz1 : ψ p (-u) ≠ 1 := fun h =>
    hu (neg_eq_zero.1 (ZMod.injective_stdAddChar (by rw [h, AddChar.map_zero_eq_one])))
  have hterm : ∀ a : ℕ, ψ p (-(u * a)) = ψ p (-u) ^ a := fun a => by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]; ring_nf
  simp only [F, hterm]
  rw [Finset.sum_Ico_eq_sum_range, show α + L - α = L by omega]
  simp_rw [pow_add]
  rw [← mul_sum, geom_sum_eq hz1, norm_mul, norm_pow, norm_psi, one_pow, one_mul, norm_div,
    norm_psi_sub_one]
  have hnum : ‖ψ p (-u) ^ L - 1‖ ≤ 2 := by
    calc ‖ψ p (-u) ^ L - 1‖ ≤ ‖ψ p (-u) ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_psi, one_pow, norm_one]; norm_num
  calc ‖ψ p (-u) ^ L - 1‖ / (2 * |Real.sin (Real.pi * u.val / p)|)
      ≤ 2 / (2 * |Real.sin (Real.pi * u.val / p)|) :=
        div_le_div_of_nonneg_right hnum (by positivity)
    _ = 1 / |Real.sin (Real.pi * u.val / p)| := by ring

/-- `1/|sin (π k/p)| ≤ (p/2)(1/k + 1/(p - k))` for `1 ≤ k < p`. -/
lemma inv_sin_le (k : ℕ) (hk1 : 1 ≤ k) (hkp : k < p) :
    1 / |Real.sin (Real.pi * k / p)| ≤ (p / 2) * (1 / (k : ℝ) + 1 / ((p : ℝ) - k)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hpk : (0 : ℝ) < (p : ℝ) - k := by
    have : (k : ℝ) < p := by exact_mod_cast hkp
    linarith
  -- `sin x ≥ 2x/π` on `[0, π/2]`, applied to `m = min(k, p - k)`
  have key : ∀ m : ℝ, 0 < m → 2 * m ≤ p →
      2 * m / p ≤ Real.sin (Real.pi * m / p) := fun m hm h2 => by
    have hx0 : 0 ≤ Real.pi * m / p := by positivity
    have hx1 : Real.pi * m / p ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hp0 two_pos]; nlinarith [Real.pi_pos]
    have := Real.mul_le_sin hx0 hx1
    calc 2 * m / p = 2 / Real.pi * (Real.pi * m / p) := by field_simp
      _ ≤ _ := this
  rcases le_or_gt (2 * k) p with h | h
  · have h2 : 2 * (k : ℝ) ≤ p := by exact_mod_cast h
    have hs := key k hk0 h2
    have hpos : 0 < 2 * (k : ℝ) / p := by positivity
    rw [abs_of_pos (lt_of_lt_of_le hpos hs)]
    calc 1 / Real.sin (Real.pi * k / p) ≤ 1 / (2 * k / p) := one_div_le_one_div_of_le hpos hs
      _ = (p / 2) * (1 / k) := by field_simp
      _ ≤ _ := by gcongr; linarith [one_div_pos.2 hpk]
  · have h2 : 2 * ((p : ℝ) - k) ≤ p := by
      have : (p : ℝ) < 2 * k := by exact_mod_cast h
      linarith
    have hs := key ((p : ℝ) - k) hpk h2
    have hsym : Real.sin (Real.pi * k / p) = Real.sin (Real.pi * ((p : ℝ) - k) / p) := by
      rw [show Real.pi * ((p : ℝ) - k) / p = Real.pi - Real.pi * k / p by field_simp,
        Real.sin_pi_sub]
    have hpos : 0 < 2 * ((p : ℝ) - k) / p := by positivity
    rw [hsym, abs_of_pos (lt_of_lt_of_le hpos hs)]
    calc 1 / Real.sin (Real.pi * ((p : ℝ) - k) / p) ≤ 1 / (2 * ((p : ℝ) - k) / p) :=
          one_div_le_one_div_of_le hpos hs
      _ = (p / 2) * (1 / ((p : ℝ) - k)) := by field_simp
      _ ≤ _ := by gcongr; linarith [one_div_pos.2 hk0]

lemma sum_val (f : ℕ → ℝ) : ∑ u : ZMod p, f u.val = ∑ k ∈ range p, f k := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  refine Finset.sum_nbij' (fun u => u.val) (fun k => (k : ZMod p)) ?_ ?_ ?_ ?_ ?_
  · intro u _; simp [ZMod.val_lt]
  · intro k _; simp
  · intro u _; exact ZMod.natCast_zmod_val u
  · intro k hk
    have hk' : k < p := by simpa using hk
    exact ZMod.val_cast_of_lt hk'
  · intro u _; rfl

lemma sum_inv_le : ∑ k ∈ Ico 1 p, (1 / (k : ℝ)) ≤ 1 + Real.log p := by
  have h1 : ∑ k ∈ Ico 1 p, (1 / (k : ℝ)) = (harmonic (p - 1) : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast
    rw [show Icc 1 (p - 1) = Ico 1 p by ext; simp; omega]; simp [one_div]
  rw [h1]
  have hp2 := hp.out.two_le
  have hlog : Real.log ((p - 1 : ℕ) : ℝ) ≤ Real.log p :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < p - 1)) (by exact_mod_cast (by omega))
  linarith [harmonic_le_one_add_log (p - 1)]

/-- `∑_{u ≠ 0} ‖Â u‖ ≤ p (1 + log p)`. -/
lemma sum_norm_F_le (α L : ℕ) :
    ∑ u : ZMod p, (if u ≠ 0 then ‖F p (Ico α (α + L)) u‖ else 0) ≤ p * (1 + Real.log p) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  set g : ℕ → ℝ := fun k => if k ≠ 0 then (p / 2) * (1 / (k : ℝ) + 1 / ((p : ℝ) - k)) else 0
  have hle : ∀ u : ZMod p, (if u ≠ 0 then ‖F p (Ico α (α + L)) u‖ else 0) ≤ g u.val := fun u => by
    by_cases hu : u = 0
    · subst hu; simp [g]
    · have hv : u.val ≠ 0 := (ZMod.val_ne_zero u).2 hu
      simp only [ne_eq, hu, not_false_eq_true, ite_true, g, hv]
      exact (norm_F_le p u hu α L).trans
        (inv_sin_le p u.val (Nat.one_le_iff_ne_zero.2 hv) (ZMod.val_lt u))
  refine (sum_le_sum fun u _ => hle u).trans ?_
  rw [sum_val p g, Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hp.out.pos]
  simp only [g, ne_eq, not_true_eq_false, ite_false, zero_add]
  rw [sum_congr rfl fun k hk => ite_eq_left (by simp at hk; omega), ← mul_sum, sum_add_distrib]
  have hrefl : ∑ k ∈ Ico 1 p, (1 / ((p : ℝ) - k)) = ∑ k ∈ Ico 1 p, (1 / (k : ℝ)) := by
    refine Finset.sum_nbij' (fun k => p - k) (fun k => p - k) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp at hk ⊢; omega
    · intro k hk; simp at hk ⊢; omega
    · intro k hk; simp at hk; omega
    · intro k hk; simp at hk; omega
    · intro k hk; rw [mem_Ico] at hk; rw [Nat.cast_sub hk.2.le]
  rw [hrefl]
  have := sum_inv_le p
  have hp0 : (0 : ℝ) ≤ p := by positivity
  nlinarith

/-- Lemma 1: inverse pairs in a rectangle, given Weil's bound. -/
theorem rect (hW : WeilBound p) (α L γ M : ℕ) (hα : 1 ≤ α) (hαL : α + L ≤ p) (hγ : 1 ≤ γ)
    (hγM : γ + M ≤ p) :
    |(N p (Ico α (α + L)) (Ico γ (γ + M)) : ℝ) - L * M / p| ≤
      3 * Real.sqrt p * (1 + Real.log p) ^ 2 := by
  set I := Ico α (α + L)
  set J := Ico γ (γ + M)
  have hI : ∀ a ∈ I, 1 ≤ a ∧ a < p := fun a ha => by simp [I] at ha; omega
  have hJ : ∀ b ∈ J, 1 ≤ b ∧ b < p := fun b hb => by simp [J] at hb; omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hsq : 1 ≤ Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hp.out.one_le)
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.out.one_le)
  have hmain := N_main p I J hI hJ
  have hcI : #I = L := by simp [I]
  have hcJ : #J = M := by simp [J]
  set E := ∑ u, ∑ v, (if u ≠ 0 ∧ v ≠ 0 then F p I u * F p J v * (K p u v + 1) else 0)
  have hdiff : ((N p I J : ℝ) - L * M / p : ℝ) = ((1 / (p : ℂ) ^ 2) * E).re := by
    have := congrArg Complex.re hmain
    rw [hcI, hcJ] at this
    simp only [Complex.add_re, Complex.natCast_re] at this
    rw [this]
    have : ((L * M : ℂ) / p).re = L * M / p := by
      rw [show ((L * M : ℂ) / p) = ((L * M / p : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    rw [this]; ring
  have hE : ‖E‖ ≤ (2 * Real.sqrt p + 1) * (p * (1 + Real.log p)) ^ 2 := by
    calc ‖E‖ ≤ ∑ u, ∑ v, ‖(if u ≠ 0 ∧ v ≠ 0 then F p I u * F p J v * (K p u v + 1) else 0)‖ :=
          (norm_sum_le _ _).trans (sum_le_sum fun u _ => norm_sum_le _ _)
      _ ≤ ∑ u, ∑ v, (2 * Real.sqrt p + 1) * ((if u ≠ 0 then ‖F p I u‖ else 0) *
            (if v ≠ 0 then ‖F p J v‖ else 0)) := by
          refine sum_le_sum fun u _ => sum_le_sum fun v _ => ?_
          by_cases hu : u = 0
          · simp [hu]
          · by_cases hv : v = 0
            · simp [hv]
            · simp only [ne_eq, hu, hv, not_false_eq_true, and_self, ite_true, norm_mul]
              have hK : ‖K p u v + 1‖ ≤ 2 * Real.sqrt p + 1 := by
                have h1 := norm_add_le (K p u v) 1
                have h2 := hW u v hu hv
                rw [norm_one] at h1
                linarith
              have h1 := norm_nonneg (F p I u)
              have h2 := norm_nonneg (F p J v)
              nlinarith [mul_nonneg h1 h2]
      _ = (2 * Real.sqrt p + 1) * ((∑ u, (if u ≠ 0 then ‖F p I u‖ else 0)) *
            (∑ v, (if v ≠ 0 then ‖F p J v‖ else 0))) := by
          rw [sum_mul_sum, mul_sum]; exact sum_congr rfl fun u _ => by rw [mul_sum]
      _ ≤ (2 * Real.sqrt p + 1) * ((p * (1 + Real.log p)) * (p * (1 + Real.log p))) := by
          have a1 := sum_norm_F_le p α L
          have a2 := sum_norm_F_le p γ M
          have b1 : 0 ≤ ∑ u, (if u ≠ 0 then ‖F p I u‖ else 0) :=
            sum_nonneg fun u _ => by split_ifs <;> simp
          gcongr
      _ = _ := by ring
  rw [hdiff]
  calc |((1 / (p : ℂ) ^ 2) * E).re| ≤ ‖(1 / (p : ℂ) ^ 2) * E‖ := Complex.abs_re_le_norm _
    _ = ‖E‖ / p ^ 2 := by
        rw [norm_mul, norm_div, norm_one, norm_pow, Complex.norm_natCast]; ring
    _ ≤ (2 * Real.sqrt p + 1) * (p * (1 + Real.log p)) ^ 2 / p ^ 2 :=
        div_le_div_of_nonneg_right hE (by positivity)
    _ = (2 * Real.sqrt p + 1) * (1 + Real.log p) ^ 2 := by field_simp
    _ ≤ 3 * Real.sqrt p * (1 + Real.log p) ^ 2 := by gcongr; linarith

end InversePairs
