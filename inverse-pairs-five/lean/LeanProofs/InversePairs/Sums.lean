import LeanProofs.InversePairs.Stair
import LeanProofs.InversePairs.Div

/-!
# Inverse pairs: finite sums (the layer-cake identity and the full grid)

`w m = 1/√m`.
* `telescope`, `layer`: `∑_i w(nᵢ) = ∑_{m=1}^{N} (w m - w (m+1)) #{i : nᵢ ≤ m} + w(N+1) #s`;
* `Tc_eq`: `Tc X` is the number of pairs `(a, b) ∈ [1, p)²` with `ab ≤ X`;
* `grid_sum`: `∑_{a,b} w(ab) = (∑_a w a)²`, and `C_close`: `|(∑_a w a)²/p - 4| ≤ 8/√p`;
* `dw_nonneg`, `m_dw_le`, `sum_w_le`: `0 ≤ w m - w(m+1)`, `m (w m - w(m+1)) ≤ 1/(2√m)`,
  `∑_{m<Y} w m ≤ 2√Y`.
-/

open Finset Real

namespace InversePairs

/-- `w m = 1/√m`. -/
noncomputable def w (m : ℕ) : ℝ := 1 / Real.sqrt m

lemma telescope (g : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ m ∈ Ico a b, (g m - g (m + 1)) = g a - g b := by
  rw [sum_Ico_eq_sum_range]
  have := sum_range_sub' (fun k => g (a + k)) (b - a)
  simp only [add_zero, show a + (b - a) = b by omega] at this
  rw [← this]
  exact sum_congr rfl fun k _ => by rw [add_assoc]

/-- The discrete layer-cake identity. -/
lemma layer {ι : Type*} (s : Finset ι) (n : ι → ℕ) (N : ℕ) (hn : ∀ i ∈ s, 1 ≤ n i ∧ n i ≤ N)
    (g : ℕ → ℝ) :
    ∑ i ∈ s, g (n i) =
      ∑ m ∈ Icc 1 N, (g m - g (m + 1)) * #{i ∈ s | n i ≤ m} + g (N + 1) * #s := by
  classical
  have h1 : ∀ i ∈ s, g (n i) =
      ∑ m ∈ Icc 1 N, (if n i ≤ m then g m - g (m + 1) else 0) + g (N + 1) := fun i hi => by
    rw [← sum_filter]
    have : (Icc 1 N).filter (fun m => n i ≤ m) = Ico (n i) (N + 1) := by
      ext m; simp only [mem_filter, mem_Icc, mem_Ico]; have := hn i hi; omega
    rw [this, telescope g _ _ (by have := hn i hi; omega)]; ring
  rw [sum_congr rfl h1, sum_add_distrib, sum_comm, sum_const, nsmul_eq_mul]
  congr 1
  · refine sum_congr rfl fun m _ => ?_
    rw [card_filter, Nat.cast_sum, mul_sum]
    exact sum_congr rfl fun i _ => by split_ifs <;> simp
  · ring

variable (p : ℕ) [hp : Fact p.Prime]

omit hp in
lemma Tc_eq (X : ℕ) : Tc p X = #{x ∈ Ico 1 p ×ˢ Ico 1 p | x.1 * x.2 ≤ X} := by
  rw [Tc, card_filter, sum_product]
  refine sum_congr rfl fun a ha => ?_
  simp only [mem_Ico] at ha
  rw [← card_filter]
  have : (Ico 1 p).filter (fun b => a * b ≤ X) = Ico 1 (min p (X / a + 1)) := by
    ext b; simp only [mem_filter, mem_Ico, lt_min_iff, Nat.lt_succ_iff]
    rw [Nat.le_div_iff_mul_le (by omega), mul_comm]; tauto
  rw [this, Nat.card_Ico]
  generalize X / a = q
  omega

omit hp in
lemma w_mul (a b : ℕ) : w (a * b) = w a * w b := by
  simp only [w]; push_cast
  rw [Real.sqrt_mul (Nat.cast_nonneg _), one_div_mul_one_div]

omit hp in
lemma grid_sum : ∑ x ∈ Ico 1 p ×ˢ Ico 1 p, w (x.1 * x.2) = (∑ a ∈ Ico 1 p, w a) ^ 2 := by
  rw [sum_product, sq, sum_mul_sum]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => w_mul a b

/-- `2(√(a+1) - √a) ≤ 1/√a ≤ 2(√a - √(a-1))` for `a ≥ 1`. -/
lemma w_between (a : ℕ) (ha : 1 ≤ a) :
    2 * (Real.sqrt (a + 1) - Real.sqrt a) ≤ w a ∧
      w a ≤ 2 * (Real.sqrt a - Real.sqrt ((a : ℝ) - 1)) := by
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  set s := Real.sqrt a
  set t := Real.sqrt (a + 1)
  set u := Real.sqrt ((a : ℝ) - 1)
  have hs : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a := Real.sq_sqrt (by linarith)
  have ht2 : t ^ 2 = a + 1 := Real.sq_sqrt (by linarith)
  have hu2 : u ^ 2 = a - 1 := Real.sq_sqrt (by linarith)
  have hts : s ≤ t := Real.sqrt_le_sqrt (by linarith)
  have hus : u ≤ s := Real.sqrt_le_sqrt (by linarith)
  simp only [w]
  constructor
  · rw [le_div_iff₀ hs]; nlinarith
  · rw [div_le_iff₀ hs]; nlinarith

omit hp in
lemma sum_w_bounds (hp2 : 2 ≤ p) :
    2 * (Real.sqrt p - 1) ≤ ∑ a ∈ Ico 1 p, w a ∧ ∑ a ∈ Ico 1 p, w a ≤ 2 * Real.sqrt p := by
  constructor
  · have := telescope (fun m => -2 * Real.sqrt m) 1 p (by omega)
    calc 2 * (Real.sqrt p - 1) = ∑ m ∈ Ico 1 p, 2 * (Real.sqrt (m + 1) - Real.sqrt m) := by
          rw [show ∑ m ∈ Ico 1 p, 2 * (Real.sqrt (m + 1) - Real.sqrt m) =
            ∑ m ∈ Ico 1 p, ((fun m : ℕ => -2 * Real.sqrt m) m -
              (fun m : ℕ => -2 * Real.sqrt m) (m + 1))
            from sum_congr rfl fun m _ => by push_cast; ring, this]
          simp; ring
      _ ≤ _ := sum_le_sum fun a ha => (w_between a (by simp at ha; omega)).1
  · have := telescope (fun m => -2 * Real.sqrt ((m : ℝ) - 1)) 1 p (by omega)
    calc ∑ a ∈ Ico 1 p, w a ≤ ∑ m ∈ Ico 1 p, 2 * (Real.sqrt m - Real.sqrt ((m : ℝ) - 1)) :=
          sum_le_sum fun a ha => (w_between a (by simp at ha; omega)).2
      _ = 2 * Real.sqrt ((p : ℝ) - 1) := by
          rw [show ∑ m ∈ Ico 1 p, 2 * (Real.sqrt m - Real.sqrt ((m : ℝ) - 1)) =
            ∑ m ∈ Ico 1 p, ((fun m : ℕ => -2 * Real.sqrt ((m : ℝ) - 1)) m -
              (fun m : ℕ => -2 * Real.sqrt ((m : ℝ) - 1)) (m + 1))
            from sum_congr rfl fun m _ => by push_cast; ring_nf, this]
          simp
      _ ≤ 2 * Real.sqrt p := by gcongr; linarith

omit hp in
/-- The full grid average tends to `4`: `|(∑_{a<p} 1/√a)²/p - 4| ≤ 8/√p`. -/
lemma C_close (hp2 : 2 ≤ p) : |(∑ a ∈ Ico 1 p, w a) ^ 2 / p - 4| ≤ 8 / Real.sqrt p := by
  obtain ⟨h1, h2⟩ := sum_w_bounds p hp2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 hp0
  have hs2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hs1 : 1 ≤ Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ p))
  set h := ∑ a ∈ Ico 1 p, w a
  have hh0 : 0 ≤ h := by linarith
  rw [abs_le]
  constructor
  · rw [le_sub_iff_add_le, le_div_iff₀ hp0]
    have : (2 * (Real.sqrt p - 1)) ^ 2 ≤ h ^ 2 := by
      have : 0 ≤ 2 * (Real.sqrt p - 1) := by linarith
      gcongr
    have e : (-(8 / Real.sqrt p) + 4) * p = 4 * p - 8 * Real.sqrt p := by
      field_simp; nlinarith
    rw [e]; nlinarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hp0]
    have : h ^ 2 ≤ (2 * Real.sqrt p) ^ 2 := by gcongr
    have : 0 ≤ 8 / Real.sqrt p * p := by positivity
    nlinarith

lemma dw_nonneg (m : ℕ) (hm : 1 ≤ m) : 0 ≤ w m - w (m + 1) := by
  simp only [w, sub_nonneg]
  have : (0 : ℝ) < m := by exact_mod_cast hm
  apply one_div_le_one_div_of_le (Real.sqrt_pos.2 this)
  exact Real.sqrt_le_sqrt (by push_cast; linarith)

lemma m_dw_le (m : ℕ) (hm : 1 ≤ m) : (m : ℝ) * (w m - w (m + 1)) ≤ w m / 2 := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set s := Real.sqrt m
  set t := Real.sqrt ((m + 1 : ℕ) : ℝ)
  have hs : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = m := Real.sq_sqrt (by linarith)
  have ht2 : t ^ 2 = m + 1 := by rw [Real.sq_sqrt (by positivity)]; push_cast; ring
  have hts : s ≤ t := Real.sqrt_le_sqrt (by push_cast; linarith)
  have ht : 0 < t := lt_of_lt_of_le hs hts
  simp only [w]
  rw [show (m : ℝ) * (1 / s - 1 / t) = s ^ 2 * (t - s) / (s * t) by rw [hs2]; field_simp]
  rw [div_le_iff₀ (by positivity)]
  have key : (t - s) * (t + s) = 1 := by nlinarith
  field_simp
  nlinarith [mul_pos hs ht]

lemma sum_w_le (Y : ℕ) : ∑ m ∈ Ico 1 Y, w m ≤ 2 * Real.sqrt Y := by
  rcases Nat.lt_or_ge Y 1 with h | h
  · rw [Ico_eq_empty (by omega)]; simp
  · have := telescope (fun m => -2 * Real.sqrt ((m : ℝ) - 1)) 1 Y h
    calc ∑ m ∈ Ico 1 Y, w m ≤ ∑ m ∈ Ico 1 Y, 2 * (Real.sqrt m - Real.sqrt ((m : ℝ) - 1)) :=
          sum_le_sum fun a ha => (w_between a (by simp at ha; omega)).2
      _ = 2 * Real.sqrt ((Y : ℝ) - 1) := by
          rw [show ∑ m ∈ Ico 1 Y, 2 * (Real.sqrt m - Real.sqrt ((m : ℝ) - 1)) =
            ∑ m ∈ Ico 1 Y, ((fun m : ℕ => -2 * Real.sqrt ((m : ℝ) - 1)) m -
              (fun m : ℕ => -2 * Real.sqrt ((m : ℝ) - 1)) (m + 1))
            from sum_congr rfl fun m _ => by push_cast; ring_nf, this]
          simp
      _ ≤ 2 * Real.sqrt Y := by gcongr; linarith

end InversePairs
