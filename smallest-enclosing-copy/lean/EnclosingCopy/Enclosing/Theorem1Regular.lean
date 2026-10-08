import EnclosingCopy.Enclosing.Theorem1
import EnclosingCopy.Enclosing.RegularChord

/-!
# Corollary 3: regular polygons

For `n` independent uniform points in the regular `q`-gon (`q ≥ 3`), the probability that some
smallest similar copy containing them lies inside the polygon tends to

  `p_q = q tan (π/q) E[Vol(T) 1{0 ∈ int T}] + 1{q even} 8/(3q²)`,

where `T` is the tetrahedron spanned by four independent points, each on a uniformly chosen
vertical edge of the prism `P_q × [-1, 1]` at a uniform height (`prismE`). This is
`theorem1_regular`. The proof evaluates the three factors of Theorem 8 for the side data of the
area-one regular `q`-gon, with inradius `r`, half-side `c = r tan (π/q)` and `q tan(π/q) r² = 1`:

* vertex term: `spatial · cone = q tan(π/q) r³/(4c) · 4 r c⁵ q⁴ E = q tan(π/q) (r² q tan(π/q))⁴ E`;
* segment term: for even `q`, `q` ordered pairs, each `(8 r c⁴/3) · (r/c)(r/2 + S/(4 c ...))`
  with `S = 2c cot(π/q) = 2r`, so each is `8 r³ c³ / 3 = 8/(3q³)`; for odd `q` there are none.
-/

namespace Enclosing

open MeasureTheory Set Real ENNReal Filter Topology

variable {q : ℕ} [NeZero q]

/-- The side data of the regular `q`-gon of area one. -/
noncomputable def regSides (hq : 3 ≤ q) : Sides q :=
  sidesOf (regVerts q) hq (regVerts_convex hq) (regVerts_area hq)

lemma regSides_isReg (hq : 3 ≤ q) : IsReg (regSides hq) (rIn q) (cHalf q) :=
  ⟨nrm_reg hq, hsup_reg hq, aEnd_reg hq, bEnd_reg hq⟩

/-- `r⁴ c⁴ q⁴ = (r² q tan(π/q))⁴ = 1`. -/
lemma rc_four (hq : 3 ≤ q) : rIn q ^ 4 * cHalf q ^ 4 * (q : ℝ) ^ 4 = 1 := by
  have h := rIn_sq hq
  rw [cHalf]
  calc rIn q ^ 4 * (rIn q * tan (π / q)) ^ 4 * (q : ℝ) ^ 4 = (rIn q ^ 2 * (q * tan (π / q))) ^ 4 := by
        ring
    _ = 1 := by rw [h, one_pow]

/-- The vertex term of the regular `q`-gon: `q tan(π/q) E`. -/
lemma vertex_term_reg (hq : 3 ≤ q) :
    spatialVertexIntegral (regSides hq) * coneVertexDensity (regSides hq) =
      ENNReal.ofReal (q * tan (π / q)) * prismE q := by
  have hK := regSides_isReg hq
  have hr := rIn_pos hq
  have hc := cHalf_pos hq
  rw [spatial_reg hK hq hr hc, cone_reg hK hr hc, ← mul_assoc,
    ← ENNReal.ofReal_mul (by have := tanq_pos hq; have := q_pos hq; positivity)]
  congr 1; congr 1
  have h4 := rc_four hq
  calc q * tan (π / q) * rIn q ^ 3 / (4 * cHalf q) * (4 * rIn q * cHalf q ^ 5 * (q : ℝ) ^ 4)
      = q * tan (π / q) * (rIn q ^ 4 * cHalf q ^ 4 * (q : ℝ) ^ 4) := by field_simp
    _ = q * tan (π / q) := by rw [h4, mul_one]

/-- `S = 2r` for the regular `2m`-gon of area one. -/
lemma slopeSum_two_r {m : ℕ} (hm : 2 ≤ m) [NeZero (2 * m)] (hq : 3 ≤ 2 * m)
    (k : Fin (2 * m)) : slopeSum (regSides hq) k = 2 * rIn (2 * m) := by
  rw [slopeSum_reg hm (regSides_isReg hq), cHalf, tan_eq_sin_div_cos]
  have hs := sinq_pos hq
  have hc := cosq_pos hq
  push_cast at hs hc ⊢
  field_simp

/-- The segment term of the regular `q`-gon: `8/(3q²)` for even `q`, `0` for odd `q`. -/
lemma segment_term_reg (hq : 3 ≤ q) :
    ∑ p ∈ parPairs (regSides hq), segDensity (regSides hq) p.1 p.2 *
        ∫⁻ w, chordWeightInf (regSides hq) p.1 w =
      if Even q then ENNReal.ofReal (8 / (3 * (q : ℝ) ^ 2)) else 0 := by
  have hK := regSides_isReg hq
  by_cases hev : Even q
  · rw [if_pos hev]
    obtain ⟨m, hm⟩ := hev
    have hq2 : q = 2 * m := by omega
    subst hq2
    have hm2 : 2 ≤ m := by omega
    have hm0 : 0 < m := by omega
    have hr := rIn_pos hq
    have hc := cHalf_pos hq
    rw [parPairs_even hm0 _ hK, Finset.sum_image (fun a _ b _ h => (Prod.mk.inj h).1)]
    have hterm : ∀ a : Fin (2 * m), segDensity (regSides hq) a (a + halfFin m hm0) *
        ∫⁻ w, chordWeightInf (regSides hq) a w =
          ENNReal.ofReal (8 / (3 * ((2 * m : ℕ) : ℝ) ^ 3)) := by
      intro a
      have hP := parPair_reg hm2 hK hr a
      have hS := slopeSum_two_r hm2 hq a
      rw [segDensity_reg hK hr hc, chordInf_reg hK hq hr hc hP (by rw [hS]; positivity), hS,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have hT := rIn_sq hq
      have hqpos := q_pos hq
      have ht := tanq_pos hq
      set r := rIn (2 * m)
      set τ := tan (π / ((2 * m : ℕ) : ℝ))
      set Q : ℝ := ((2 * m : ℕ) : ℝ)
      have e1 : r / 2 + 2 * r * (Q * τ) * r ^ 2 / 4 = r := by
        have : 2 * r * (Q * τ) * r ^ 2 / 4 = r * (r ^ 2 * (Q * τ)) / 2 := by ring
        rw [this, hT]; ring
      rw [e1]
      calc 8 * r * cHalf (2 * m) ^ 4 / 3 * (r / cHalf (2 * m) * r)
          = 8 / 3 * (r ^ 2 * (Q * τ)) ^ 3 / Q ^ 3 := by
            simp only [cHalf]
            field_simp
            rfl
        _ = 8 / (3 * Q ^ 3) := by rw [hT]; field_simp
    rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := q_pos hq
    field_simp
  · rw [if_neg hev, parPairs_odd hK hev, Finset.sum_empty]

/-- **Corollary 3.** For `n` independent uniform points in the regular `q`-gon (`q ≥ 3`), the
probability that some smallest regular `q`-gon containing them (of any orientation) lies inside
the original tends to `q tan (π/q) E[Vol(T) 1{0 ∈ int T}] + 1{q even} 8/(3q²)`, where `T` is
the tetrahedron spanned by four independent points, each on a uniformly chosen vertical edge of
the prism `P_q × [-1, 1]` at a uniform height. -/
theorem theorem1_regular (hq : 3 ≤ q) :
    Tendsto (fun n : ℕ => (Measure.pi fun _ : Fin n =>
        polygonSample (regVerts q) hq (regVerts_convex hq) (regVerts_area hq))
        {x | TrueEv (regSides hq) x}) atTop
      (𝓝 (ENNReal.ofReal (q * tan (π / q)) * prismE q +
        if Even q then ENNReal.ofReal (8 / (3 * (q : ℝ) ^ 2)) else 0)) := by
  have h := theorem1 hq (regVerts_convex hq) (regVerts_area hq)
  dsimp only at h
  rw [← vertex_term_reg hq, ← segment_term_reg hq]
  exact h

end Enclosing
