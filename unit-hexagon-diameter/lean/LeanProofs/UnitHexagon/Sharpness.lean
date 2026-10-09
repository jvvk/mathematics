import LeanProofs.UnitHexagon.Rays
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Unit hexagons: the sharpness family (Section 5)

For `0 < t < 1/2` put `A = (0,0)`, `B = (1,0)`, `C = (1,1)`,
`D = (2t²/(1+t²), 1 + 2t/(1+t²))`, `E = D + (3/5, -4/5)` and `F = E/2 + k·J E` with `J(x,y) = (-y,x)` and
`k = √(1/|E|² - 1/4)`. We prove:
* all six edges have length one;
* `2 E_y - |E|² = 16 t (1 - 2t) / (5 (1 + t²))`, hence `F_x < 0`, and `0 < F_y < 1`;
* every nonadjacent pair of edges is separated by a line, and every turn is nonzero (five positive, the
  one at `E` negative), so the hexagon is simple;
* as `t → 0` all squared pairwise distances tend to at most `2`: for every `ε > 0` some member has all
  squared distances below `2 + ε`, lies in a box of side `1 + ε`, and lies within squared distance
  `1/2 + ε` of `(1/2, 1/2)`.
-/

open Real Filter Topology

namespace UnitHexagon

noncomputable section

def Dx (t : ℝ) : ℝ := 2 * t ^ 2 / (1 + t ^ 2)
def Dy (t : ℝ) : ℝ := 1 + 2 * t / (1 + t ^ 2)
def Ex (t : ℝ) : ℝ := Dx t + 3 / 5
def Ey (t : ℝ) : ℝ := Dy t - 4 / 5
def r2 (t : ℝ) : ℝ := Ex t ^ 2 + Ey t ^ 2
def kk (t : ℝ) : ℝ := Real.sqrt (1 / r2 t - 1 / 4)
def Fx (t : ℝ) : ℝ := Ex t / 2 - kk t * Ey t
def Fy (t : ℝ) : ℝ := Ey t / 2 + kk t * Ex t

/-- The six vertices `A, B, C, D, E, F`. -/
def V (t : ℝ) : Fin 6 → ℝ × ℝ :=
  ![(0, 0), (1, 0), (1, 1), (Dx t, Dy t), (Ex t, Ey t), (Fx t, Fy t)]

/-- Squared Euclidean distance. -/
def d2 (P Q : ℝ × ℝ) : ℝ := (P.1 - Q.1) ^ 2 + (P.2 - Q.2) ^ 2

lemma q_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

lemma Ex_pos (t : ℝ) : 0 < Ex t := by
  unfold Ex Dx; have := q_pos t; positivity

lemma r2_pos (t : ℝ) : 0 < r2 t := by
  unfold r2; have := Ex_pos t; positivity

/-- Segments separated by a linear functional are disjoint. -/
lemma disjoint_of_sep {P Q R S : ℝ × ℝ} (u v c : ℝ) (hP : u * P.1 + v * P.2 ≤ c)
    (hQ : u * Q.1 + v * Q.2 ≤ c) (hR : c < u * R.1 + v * R.2) (hS : c < u * S.1 + v * S.2) :
    Disjoint (segment ℝ P Q) (segment ℝ R S) := by
  rw [Set.disjoint_left]
  rintro z ⟨a, b, ha, hb, hab, rfl⟩ ⟨c', d, hc, hd, hcd, hz⟩
  have e1 : u * (a • P + b • Q).1 + v * (a • P + b • Q).2 ≤ c := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have h1 := mul_le_mul_of_nonneg_left hP ha
    have h2 := mul_le_mul_of_nonneg_left hQ hb
    have h3 : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    linarith
  have e2 : c < u * (c' • R + d • S).1 + v * (c' • R + d • S).2 := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have h3 : c' * c + d * c = c := by rw [← add_mul, hcd, one_mul]
    rcases eq_or_lt_of_le hc with h0 | h0
    · have hd1 : d = 1 := by linarith
      rw [← h0, hd1]; linarith
    · have h1 := mul_lt_mul_of_pos_left hR h0
      have h2 := mul_le_mul_of_nonneg_left hS.le hd
      linarith
  rw [hz] at e2; linarith

/-- Adjacent edges meet only at their common vertex when the turn is nonzero. -/
lemma adjacent_meet {P Q R : ℝ × ℝ} (h : cross (Q - P) (R - Q) ≠ 0) :
    segment ℝ P Q ∩ segment ℝ Q R = {Q} := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨a, b, ha, hb, hab, rfl⟩, ⟨c, d, hc, hd, hcd, hz⟩⟩
    have hz' : a • P + b • Q - Q = d • (R - Q) := by
      rw [← hz]; rw [show c = 1 - d by linarith]; simp only [sub_smul, one_smul, smul_sub]; abel
    have ha' : a = 1 - b := by linarith
    have key : d * cross (Q - P) (R - Q) = 0 := by
      have e1 := congrArg Prod.fst hz'; have e2 := congrArg Prod.snd hz'
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
        Prod.snd_sub, smul_eq_mul, ha'] at e1 e2
      simp only [cross, Prod.fst_sub, Prod.snd_sub]
      linear_combination (Q.2 - P.2) * e1 - (Q.1 - P.1) * e2
    rcases mul_eq_zero.1 key with hd0 | hc0
    · rw [← hz, show c = 1 by linarith, hd0]; simp
    · exact absurd hc0 h
  · intro hz; rw [hz]; exact ⟨right_mem_segment ℝ P Q, left_mem_segment ℝ Q R⟩

section family
variable {t : ℝ} (ht : 0 < t) (ht' : t < 1 / 2)
include ht ht'

omit ht' in
lemma Dx_pos : 0 < Dx t := by unfold Dx; have := q_pos t; positivity

lemma Dx_lt : Dx t < 2 / 5 := by
  unfold Dx; rw [div_lt_iff₀ (q_pos t)]; nlinarith

omit ht' in
lemma Dy_gt : 1 < Dy t := by
  unfold Dy; have := q_pos t; have : 0 < 2 * t / (1 + t ^ 2) := by positivity
  linarith

lemma Ey_bounds : 0 < Ey t ∧ Ey t < 1 := by
  unfold Ey Dy
  have hq := q_pos t
  have h1 : 0 < 2 * t / (1 + t ^ 2) := by positivity
  have h2 : 2 * t / (1 + t ^ 2) < 4 / 5 := by rw [div_lt_iff₀ hq]; nlinarith
  constructor <;> linarith

lemma Ex_lt_one : Ex t < 1 := by unfold Ex; linarith [Dx_lt ht ht']

lemma r2_lt_two : r2 t < 2 := by
  unfold r2
  have := Ex_pos t; have := Ex_lt_one ht ht'; obtain ⟨a, b⟩ := Ey_bounds ht ht'
  nlinarith

lemma kk_sq : kk t ^ 2 = 1 / r2 t - 1 / 4 := by
  unfold kk
  rw [Real.sq_sqrt]
  have := r2_pos t; have := r2_lt_two ht ht'
  rw [sub_nonneg, le_div_iff₀ (r2_pos t)]; linarith

lemma kk_pos : 0 < kk t := by
  unfold kk; apply Real.sqrt_pos.2
  have := r2_pos t; have := r2_lt_two ht ht'
  rw [sub_pos, lt_div_iff₀ (r2_pos t)]; linarith

omit ht' in
/-- The sign identity of Section 5. -/
lemma sign_identity : 2 * Ey t - r2 t = 16 * t * (1 - 2 * t) / (5 * (1 + t ^ 2)) := by
  unfold r2 Ey Ex Dy Dx
  have := q_pos t
  field_simp
  ring

lemma unit_AF : Fx t ^ 2 + Fy t ^ 2 = 1 := by
  have hk := kk_sq ht ht'
  have hr := r2_pos t
  have : Fx t ^ 2 + Fy t ^ 2 = r2 t * (1 / 4 + kk t ^ 2) := by unfold Fx Fy r2; ring
  rw [this, hk]; field_simp; ring

lemma unit_EF : (Fx t - Ex t) ^ 2 + (Fy t - Ey t) ^ 2 = 1 := by
  have hk := kk_sq ht ht'
  have hr := r2_pos t
  have : (Fx t - Ex t) ^ 2 + (Fy t - Ey t) ^ 2 = r2 t * (1 / 4 + kk t ^ 2) := by
    unfold Fx Fy r2; ring
  rw [this, hk]; field_simp; ring

omit ht' in
lemma unit_CD : (Dx t - 1) ^ 2 + (Dy t - 1) ^ 2 = 1 := by
  unfold Dx Dy; have := q_pos t; field_simp; ring

omit ht ht' in
lemma unit_DE : (Ex t - Dx t) ^ 2 + (Ey t - Dy t) ^ 2 = 1 := by
  unfold Ex Ey; norm_num

/-- `F` lies strictly left of the vertical axis. -/
lemma Fx_neg : Fx t < 0 := by
  have hk := kk_sq ht ht'
  have hkp := kk_pos ht ht'
  have hr := r2_pos t
  obtain ⟨hy, _⟩ := Ey_bounds ht ht'
  have hx := Ex_pos t
  have hs : 0 < 2 * Ey t - r2 t := by
    rw [sign_identity ht]
    have := q_pos t
    have : 0 < 1 - 2 * t := by linarith
    positivity
  -- (k E_y)² - (E_x/2)² = (4 E_y² - r2²) / (4 r2) > 0
  have hsq : (Ex t / 2) ^ 2 < (kk t * Ey t) ^ 2 := by
    have e : (kk t * Ey t) ^ 2 - (Ex t / 2) ^ 2 = (4 * Ey t ^ 2 - r2 t ^ 2) / (4 * r2 t) := by
      rw [mul_pow, hk]; unfold r2; field_simp; ring
    have : 0 < (4 * Ey t ^ 2 - r2 t ^ 2) / (4 * r2 t) := by
      apply div_pos _ (by positivity); nlinarith
    linarith
  have := lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  unfold Fx; linarith

lemma Fy_bounds : 0 < Fy t ∧ Fy t < 1 := by
  have hkp := kk_pos ht ht'
  obtain ⟨hy, _⟩ := Ey_bounds ht ht'
  have hx := Ex_pos t
  have hpos : 0 < Fy t := by unfold Fy; positivity
  refine ⟨hpos, ?_⟩
  have := unit_AF ht ht'
  have := Fx_neg ht ht'
  nlinarith

/-! ### Simplicity -/

/-- The nine nonadjacent edge pairs are disjoint. -/
theorem simple_nonadjacent :
    let A := V t 0; let B := V t 1; let C := V t 2; let D := V t 3; let E := V t 4; let F := V t 5
    Disjoint (segment ℝ A B) (segment ℝ C D) ∧ Disjoint (segment ℝ A B) (segment ℝ D E) ∧
    Disjoint (segment ℝ A B) (segment ℝ E F) ∧ Disjoint (segment ℝ B C) (segment ℝ D E) ∧
    Disjoint (segment ℝ B C) (segment ℝ E F) ∧ Disjoint (segment ℝ B C) (segment ℝ F A) ∧
    Disjoint (segment ℝ C D) (segment ℝ E F) ∧ Disjoint (segment ℝ C D) (segment ℝ F A) ∧
    Disjoint (segment ℝ D E) (segment ℝ F A) := by
  intro A B C D E F
  have dx := Dx_pos ht; have dx' := Dx_lt ht ht'; have dy := Dy_gt ht
  have ex := Ex_pos t; have ex' := Ex_lt_one ht ht'; obtain ⟨ey, ey'⟩ := Ey_bounds ht ht'
  have fx := Fx_neg ht ht'; obtain ⟨fy, fy'⟩ := Fy_bounds ht ht'
  simp only [A, B, C, D, E, F, V, Matrix.cons_val]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact disjoint_of_sep 0 1 0 (by norm_num) (by norm_num) (by norm_num) (by simp; linarith)
  · exact disjoint_of_sep 0 1 0 (by norm_num) (by norm_num) (by simp; linarith) (by simp; linarith)
  · exact disjoint_of_sep 0 1 0 (by norm_num) (by norm_num) (by simp; linarith) (by simp; linarith)
  · exact disjoint_of_sep (-1) 0 (-1) (by norm_num) (by norm_num) (by simp; linarith)
      (by simp; linarith)
  · exact disjoint_of_sep (-1) 0 (-1) (by norm_num) (by norm_num) (by simp; linarith)
      (by simp; linarith)
  · exact disjoint_of_sep (-1) 0 (-1) (by norm_num) (by norm_num) (by simp; linarith)
      (by norm_num)
  · exact disjoint_of_sep 0 (-1) (-1) (by norm_num) (by simp; linarith) (by simp; linarith)
      (by simp; linarith)
  · exact disjoint_of_sep 0 (-1) (-1) (by norm_num) (by simp; linarith) (by simp; linarith)
      (by norm_num)
  · exact (disjoint_of_sep 1 0 0 (by simp; linarith) (by norm_num) (by simp; linarith)
      (by simp; linarith)).symm

/-- Turn cross products: positive at `A, B, C, D, F`, negative at `E`. -/
theorem turns :
    0 < cross (V t 0 - V t 5) (V t 1 - V t 0) ∧ 0 < cross (V t 1 - V t 0) (V t 2 - V t 1) ∧
    0 < cross (V t 2 - V t 1) (V t 3 - V t 2) ∧ 0 < cross (V t 3 - V t 2) (V t 4 - V t 3) ∧
    cross (V t 4 - V t 3) (V t 5 - V t 4) < 0 ∧ 0 < cross (V t 5 - V t 4) (V t 0 - V t 5) := by
  have dx := Dx_pos ht; have dy := Dy_gt ht
  have ex := Ex_pos t; obtain ⟨ey, _⟩ := Ey_bounds ht ht'
  have fx := Fx_neg ht ht'; obtain ⟨fy, fy'⟩ := Fy_bounds ht ht'
  simp only [V, cross, Matrix.cons_val, Prod.fst_sub, Prod.snd_sub]
  refine ⟨by simp; linarith, by norm_num, ?_, ?_, ?_, ?_⟩
  · have h := Dx_lt ht ht'; nlinarith
  · -- equals 2 (1 - 2t)(t + 2) / (5 (1 + t²))
    have e : (Dx t - 1) * (Ey t - Dy t) - (Dy t - 1) * (Ex t - Dx t) =
        2 * (1 - 2 * t) * (t + 2) / (5 * (1 + t ^ 2)) := by
      unfold Ex Ey Dx Dy; have := q_pos t; field_simp; ring
    rw [e]
    have h1 : 0 < 1 - 2 * t := by linarith
    apply div_pos _ (by have := q_pos t; positivity)
    have := mul_pos (mul_pos two_pos h1) (by linarith : (0 : ℝ) < t + 2)
    linarith
  · unfold Ex Ey; ring_nf; nlinarith
  · nlinarith [mul_pos ex fy, mul_pos ey (neg_pos.2 fx)]

end family

/-! ### The limit `t → 0` -/

lemma continuous_Dx : Continuous Dx := by
  unfold Dx; exact (by fun_prop : Continuous fun t : ℝ => 2 * t ^ 2).div (by fun_prop)
    (fun t => (q_pos t).ne')
lemma continuous_Dy : Continuous Dy := by
  unfold Dy; exact continuous_const.add ((by fun_prop : Continuous fun t : ℝ => 2 * t).div (by fun_prop)
    (fun t => (q_pos t).ne'))
lemma continuous_Ex : Continuous Ex := by unfold Ex; exact continuous_Dx.add continuous_const
lemma continuous_Ey : Continuous Ey := by unfold Ey; exact continuous_Dy.sub continuous_const
lemma continuous_r2 : Continuous r2 := by
  unfold r2; exact (continuous_Ex.pow 2).add (continuous_Ey.pow 2)
lemma continuous_kk : Continuous kk := by
  unfold kk
  exact Real.continuous_sqrt.comp ((continuous_const.div continuous_r2 (fun t => (r2_pos t).ne')).sub
    continuous_const)
lemma continuous_Fx : Continuous Fx := by
  unfold Fx; exact (continuous_Ex.div_const 2).sub (continuous_kk.mul continuous_Ey)
lemma continuous_Fy : Continuous Fy := by
  unfold Fy; exact (continuous_Ey.div_const 2).add (continuous_kk.mul continuous_Ex)

lemma continuous_V (i : Fin 6) : Continuous fun t => V t i := by
  fin_cases i <;> simp [V, continuous_Dx, continuous_Dy, continuous_Ex, continuous_Ey, continuous_Fx,
    continuous_Fy, continuous_prodMk, continuous_const]

lemma kk_zero : kk 0 = 3 / 2 := by
  unfold kk r2 Ex Ey Dx Dy
  rw [show (1 : ℝ) / ((2 * 0 ^ 2 / (1 + 0 ^ 2) + 3 / 5) ^ 2 + (1 + 2 * 0 / (1 + 0 ^ 2) - 4 / 5) ^ 2)
      - 1 / 4 = (3 / 2) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

lemma V_zero : V 0 = ![(0, 0), (1, 0), (1, 1), (0, 1), (3 / 5, 1 / 5), (0, 1)] := by
  have k0 := kk_zero
  have hD : Dx 0 = 0 ∧ Dy 0 = 1 := by unfold Dx Dy; norm_num
  have hE : Ex 0 = 3 / 5 ∧ Ey 0 = 1 / 5 := by unfold Ex Ey; rw [hD.1, hD.2]; norm_num
  have hF : Fx 0 = 0 ∧ Fy 0 = 1 := by unfold Fx Fy; rw [k0, hE.1, hE.2]; norm_num
  unfold V; rw [hD.1, hD.2, hE.1, hE.2, hF.1, hF.2]

/-- In the limit every squared distance is at most `2`, every vertex lies in `[0,1]²`, and every vertex
is within squared distance `1/2` of the centre. -/
lemma limit_bounds (i j : Fin 6) :
    d2 (V 0 i) (V 0 j) ≤ 2 ∧ (0 ≤ (V 0 i).1 ∧ (V 0 i).1 ≤ 1 ∧ 0 ≤ (V 0 i).2 ∧ (V 0 i).2 ≤ 1) ∧
      d2 (V 0 i) (1 / 2, 1 / 2) ≤ 1 / 2 := by
  rw [V_zero]
  fin_cases i <;> fin_cases j <;> simp [d2] <;> norm_num

/-- Sharpness and the containment thresholds: for every `ε > 0` some member of the family has all
squared pairwise distances below `2 + ε`, all vertices in `[-ε, 1 + ε]²`, and all vertices within squared
distance `1/2 + ε` of `(1/2, 1/2)`. -/
theorem sharp (ε : ℝ) (hε : 0 < ε) : ∃ t, 0 < t ∧ t < 1 / 2 ∧
    (∀ i j, d2 (V t i) (V t j) < 2 + ε) ∧
    (∀ i, -ε < (V t i).1 ∧ (V t i).1 < 1 + ε ∧ -ε < (V t i).2 ∧ (V t i).2 < 1 + ε) ∧
    (∀ i, d2 (V t i) (1 / 2, 1 / 2) < 1 / 2 + ε) := by
  have cd : ∀ i j, Continuous fun t => d2 (V t i) (V t j) := fun i j => by
    unfold d2
    have hi := continuous_V i; have hj := continuous_V j
    fun_prop
  have cc : ∀ i, Continuous fun t => d2 (V t i) (1 / 2, 1 / 2) := fun i => by
    unfold d2; have hi := continuous_V i; fun_prop
  have e1 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i j, d2 (V t i) (V t j) < 2 + ε := by
    rw [Filter.eventually_all]; intro i; rw [Filter.eventually_all]; intro j
    exact (cd i j).continuousAt.eventually_lt continuousAt_const
      (by linarith [(limit_bounds i j).1])
  have e2 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i,
      -ε < (V t i).1 ∧ (V t i).1 < 1 + ε ∧ -ε < (V t i).2 ∧ (V t i).2 < 1 + ε := by
    rw [Filter.eventually_all]; intro i
    obtain ⟨_, ⟨a, b, c, d⟩, _⟩ := limit_bounds i i
    have c1 := (continuous_fst.comp (continuous_V i)).continuousAt (x := (0 : ℝ))
    have c2 := (continuous_snd.comp (continuous_V i)).continuousAt (x := (0 : ℝ))
    exact (continuousAt_const.eventually_lt c1 (by simp; linarith)).and
      ((c1.eventually_lt continuousAt_const (by simp; linarith)).and
      ((continuousAt_const.eventually_lt c2 (by simp; linarith)).and
      (c2.eventually_lt continuousAt_const (by simp; linarith))))
  have e3 : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, d2 (V t i) (1 / 2, 1 / 2) < 1 / 2 + ε := by
    rw [Filter.eventually_all]; intro i
    exact (cc i).continuousAt.eventually_lt continuousAt_const (by linarith [(limit_bounds i i).2.2])
  have e4 : ∀ᶠ t in 𝓝 (0 : ℝ), t < 1 / 2 := Iio_mem_nhds (by norm_num)
  have all := ((e1.and e2).and (e3.and e4)).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi 0))
  obtain ⟨t, ⟨⟨h1, h2⟩, h3, h4⟩, ht⟩ := (all.and self_mem_nhdsWithin).exists
  exact ⟨t, ht, h4, h1, h2, h3⟩

end

end UnitHexagon
