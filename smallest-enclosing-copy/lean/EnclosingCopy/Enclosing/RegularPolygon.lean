import EnclosingCopy.Enclosing.ConvexPolygon
import EnclosingCopy.Enclosing.RegularGeom

/-!
# The regular `q`-gon of area one, by its vertices

`regVerts q` lists the vertices `R (cos (θⱼ - π/q), sin (θⱼ - π/q))`, `θⱼ = 2πj/q`, of the regular
`q`-gon centred at the origin with circumradius `R = r / cos (π/q)`, where the inradius
`r = (q tan (π/q))^{-1/2}` makes the area one. Then side `j` runs from angle `θⱼ - π/q` to
`θⱼ + π/q`, so (`regSides_u`, `regSides_h`, `regSides_a`, `regSides_b`)

* its outward normal is `uⱼ = (cos θⱼ, sin θⱼ)` (the normals `un q j` of Section 7),
* its support number is `r`, and its end positions are `∓c` with `c = r tan (π/q)`.

The vertices are in strictly convex position (`regVerts_convex`): a vertex `k` off side `j` has
`v_k · uⱼ = R cos ((2d - 1)π/q)` with `d = k - j ∉ {0, 1}`, and `|2d - 1|π/q` lies in
`[3π/q, 2π - 3π/q]`, where the cosine is below `cos (π/q)`.
-/

namespace Enclosing

open Real Finset

variable {q : ℕ}

/-- The inradius of the regular `q`-gon of area one. -/
noncomputable def rIn (q : ℕ) : ℝ := 1 / sqrt (q * tan (π / q))

/-- Half the side length: `c = r tan (π/q)`. -/
noncomputable def cHalf (q : ℕ) : ℝ := rIn q * tan (π / q)

/-- The circumradius `R = r / cos (π/q)`. -/
noncomputable def rOut (q : ℕ) : ℝ := rIn q / cos (π / q)

/-- The angle of the normal of side `j`. -/
noncomputable def thA (q : ℕ) (j : ℕ) : ℝ := 2 * π * j / q

/-- The vertices of the regular `q`-gon of area one. -/
noncomputable def regVerts (q : ℕ) : Fin q → ℝ × ℝ :=
  fun j => (rOut q * cos (thA q j - π / q), rOut q * sin (thA q j - π / q))

lemma regVerts_self (j : Fin q) :
    regVerts q j = (rOut q * cos (thA q j - π / q), rOut q * sin (thA q j - π / q)) := rfl

section Basic

variable [NeZero q] (hq : 3 ≤ q)
include hq

lemma q_pos : (0 : ℝ) < q := by
  have : (3 : ℝ) ≤ q := by exact_mod_cast hq
  linarith

lemma piq_pos : 0 < π / q := div_pos pi_pos (q_pos hq)

lemma piq_lt : π / q < π / 2 := by
  have : (3 : ℝ) ≤ q := by exact_mod_cast hq
  exact div_lt_div_of_pos_left pi_pos (by norm_num) (by linarith)

lemma tanq_pos : 0 < tan (π / q) := tan_pos_of_pos_of_lt_pi_div_two (piq_pos hq) (piq_lt hq)

lemma cosq_pos : 0 < cos (π / q) :=
  cos_pos_of_mem_Ioo ⟨by linarith [piq_pos hq, pi_pos], piq_lt hq⟩

lemma sinq_pos : 0 < sin (π / q) :=
  sin_pos_of_pos_of_lt_pi (piq_pos hq) (by linarith [piq_lt hq, pi_pos])

lemma rIn_pos : 0 < rIn q := by
  have := tanq_pos hq; have := q_pos hq
  unfold rIn; positivity

lemma rIn_sq : rIn q ^ 2 * (q * tan (π / q)) = 1 := by
  have h := mul_pos (q_pos hq) (tanq_pos hq)
  unfold rIn
  rw [div_pow, sq_sqrt h.le]
  have := (tanq_pos hq).ne'
  have := (q_pos hq).ne'
  field_simp

lemma cHalf_pos : 0 < cHalf q := mul_pos (rIn_pos hq) (tanq_pos hq)

lemma rOut_pos : 0 < rOut q := div_pos (rIn_pos hq) (cosq_pos hq)

lemma rOut_sin : rOut q * sin (π / q) = cHalf q := by
  unfold rOut cHalf
  rw [tan_eq_sin_div_cos]
  have := (cosq_pos hq).ne'
  field_simp

lemma rOut_cos : rOut q * cos (π / q) = rIn q := by
  unfold rOut
  have := (cosq_pos hq).ne'
  field_simp

lemma fin_succ_val (j : Fin q) :
    ((j + 1 : Fin q) : ℕ) = if (j : ℕ) + 1 = q then 0 else (j : ℕ) + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 3 := ⟨q - 3, by omega⟩
  have h1 : ((1 : Fin (n + 3)) : ℕ) = 1 := by simp
  rw [Fin.val_add, h1]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · rw [Nat.mod_eq_of_lt (by omega)]

/-- The next vertex sits at angle `θⱼ + π/q`. -/
lemma regVerts_succ (j : Fin q) :
    regVerts q (j + 1) =
      (rOut q * cos (thA q j + π / q), rOut q * sin (thA q j + π / q)) := by
  have hq0 := (q_pos hq).ne'
  simp only [regVerts]
  rw [fin_succ_val hq]
  split_ifs with h
  · have he : thA q j + π / q = (thA q (0 : ℕ) - π / q) + 2 * π := by
      simp only [thA]
      have : ((j : ℕ) : ℝ) = q - 1 := by
        have : ((j : ℕ) : ℝ) + 1 = q := by exact_mod_cast h
        linarith
      rw [this]; field_simp; ring
    rw [he, cos_add_two_pi, sin_add_two_pi]
  · have he : thA q ((j : ℕ) + 1) - π / q = thA q j + π / q := by
      simp only [thA]; push_cast; field_simp; ring
    rw [he]

end Basic

/-! ### The side data -/

section Sides

variable [NeZero q] (hq : 3 ≤ q)
include hq

lemma edge_reg (j : Fin q) : edge (regVerts q) j =
    (2 * cHalf q * -sin (thA q j), 2 * cHalf q * cos (thA q j)) := by
  rw [edge, regVerts_succ hq, regVerts_self, ← rOut_sin hq]
  simp only [Prod.mk_sub_mk, cos_add, cos_sub, sin_add, sin_sub]
  ext <;> simp <;> ring

lemma len_reg (j : Fin q) : len (regVerts q) j = 2 * cHalf q := by
  rw [len, edge_reg hq]
  simp only [dot]
  have h : (2 * cHalf q * -sin (thA q j)) * (2 * cHalf q * -sin (thA q j)) +
      (2 * cHalf q * cos (thA q j)) * (2 * cHalf q * cos (thA q j)) = (2 * cHalf q) ^ 2 := by
    have := sin_sq_add_cos_sq (thA q j)
    linear_combination (2 * cHalf q) ^ 2 * this
  rw [h, sqrt_sq (by have := cHalf_pos hq; positivity)]

lemma tng_reg (j : Fin q) : tng (regVerts q) j = (-sin (thA q j), cos (thA q j)) := by
  have hc := (cHalf_pos hq).ne'
  rw [tng, len_reg hq, edge_reg hq]
  ext <;> simp <;> field_simp

lemma nrm_reg (j : Fin q) : nrm (regVerts q) j = un q j := by
  rw [nrm, tng_reg hq, un]
  simp [thA]

lemma hsup_reg (j : Fin q) : hsup (regVerts q) j = rIn q := by
  rw [hsup, nrm_reg hq, regVerts_self, un, ← rOut_cos hq]
  simp only [dot, thA]
  rw [cos_sub, sin_sub]
  have := sin_sq_add_cos_sq (2 * π * (j : ℝ) / q)
  linear_combination rOut q * cos (π / q) * this

lemma aEnd_reg (j : Fin q) : aEnd (regVerts q) j = -cHalf q := by
  rw [aEnd, tng_reg hq, regVerts_self, ← rOut_sin hq]
  simp only [dot]
  rw [cos_sub, sin_sub]
  have := sin_sq_add_cos_sq (thA q j)
  linear_combination -(rOut q * sin (π / q)) * this

lemma bEnd_reg (j : Fin q) : bEnd (regVerts q) j = cHalf q := by
  rw [bEnd, tng_reg hq, regVerts_succ hq, ← rOut_sin hq]
  simp only [dot]
  rw [cos_add, sin_add]
  have := sin_sq_add_cos_sq (thA q j)
  linear_combination rOut q * sin (π / q) * this

/-- The shoelace area is one. -/
lemma regVerts_area : area (regVerts q) = 1 := by
  have hterm : ∀ j : Fin q, (regVerts q j).1 * (regVerts q (j + 1)).2 -
      (regVerts q j).2 * (regVerts q (j + 1)).1 = 2 * rOut q ^ 2 * sin (π / q) * cos (π / q) := by
    intro j
    rw [regVerts_succ hq, regVerts_self]
    simp only
    rw [show thA q j + π / q = (thA q j - π / q) + 2 * (π / q) by ring, cos_add, sin_add,
      sin_two_mul]
    linear_combination (2 * rOut q ^ 2 * sin (π / q) * cos (π / q)) *
      sin_sq_add_cos_sq (thA q j - π / q)
  rw [area, Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have h1 := rIn_sq hq
  have hc := (cosq_pos hq).ne'
  unfold rOut at *
  rw [tan_eq_sin_div_cos] at h1
  field_simp at h1 ⊢
  linear_combination h1

/-- `cos y < cos (π/q)` on `[3π/q, 2π - 3π/q]`. -/
lemma cos_lt_cosq {y : ℝ} (h1 : 3 * (π / q) ≤ y) (h2 : y ≤ 2 * π - 3 * (π / q)) :
    cos y < cos (π / q) := by
  have hp := piq_pos hq
  rcases le_total y π with hy | hy
  · exact cos_lt_cos_of_nonneg_of_le_pi hp.le hy (by linarith)
  · rw [← cos_two_pi_sub]
    exact cos_lt_cos_of_nonneg_of_le_pi hp.le (by linarith) (by linarith)

/-- **The regular `q`-gon is in strictly convex position.** -/
lemma regVerts_convex : ConvexPos (regVerts q) := by
  intro i k hki hki1
  rw [hsup_reg hq, nrm_reg hq, regVerts_self, un, ← rOut_cos hq]
  simp only [dot]
  rw [show rOut q * cos (thA q k - π / q) * cos (2 * π * (i : ℕ) / q) +
      rOut q * sin (thA q k - π / q) * sin (2 * π * (i : ℕ) / q) =
      rOut q * cos ((thA q k - π / q) - 2 * π * (i : ℕ) / q) by
        rw [cos_sub (thA q k - π / q) (2 * π * (i : ℕ) / q)]; ring]
  apply mul_lt_mul_of_pos_left _ (rOut_pos hq)
  have hq0 := (q_pos hq).ne'
  set d : ℤ := ((k : ℕ) : ℤ) - ((i : ℕ) : ℤ) with hd
  have hang : thA q k - π / q - 2 * π * (i : ℕ) / q = (2 * (d : ℝ) - 1) * (π / q) := by
    simp only [thA, hd]; push_cast; field_simp; ring
  rw [hang]
  have hk := k.isLt
  have hi := i.isLt
  have hd0 : d ≠ 0 := fun h => hki (Fin.ext (by omega))
  have hsv := fin_succ_val hq i
  have hd1 : d ≠ 1 := by
    intro h
    apply hki1
    apply Fin.ext
    rw [hsv, if_neg (by omega)]
    omega
  have hd2 : d ≠ 1 - q := by
    intro h
    apply hki1
    apply Fin.ext
    rw [hsv, if_pos (by omega)]
    omega
  have hpq : (q : ℝ) * (π / q) = π := by field_simp
  have hp := piq_pos hq
  rcases le_or_gt 2 d with h2 | h2
  · have hdq : d ≤ q - 1 := by omega
    have a1 : (2 : ℝ) ≤ d := by exact_mod_cast h2
    have a2 : (d : ℝ) ≤ q - 1 := by exact_mod_cast hdq
    apply cos_lt_cosq hq <;> nlinarith
  · have hdq : 2 - q ≤ d := by omega
    have hdn : d ≤ -1 := by omega
    have a1 : (d : ℝ) ≤ -1 := by exact_mod_cast hdn
    have a2 : (2 : ℝ) - q ≤ d := by exact_mod_cast hdq
    rw [← cos_neg]
    apply cos_lt_cosq hq <;> nlinarith

end Sides

end Enclosing
