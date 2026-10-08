import Mathlib.Analysis.Real.Sqrt
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic

/-!
# Six circles in a rectangle: the Gazette note's proof, step by step

The configuration is that of the original coordinate proof (MathOverflow 515498): rectangle
`[-w, w] × [-h, h]`, centre `O = (0, 0)`; top row `A = (-(w-a), h-a)`, `B = (x, h-b)`,
`C = (w-c, h-c)`; bottom row by the half-turn about `O`.

This file follows the route of the note `../paper/note.tex` (8 October 2026).
Each lemma is one argument of the note, stated in coordinates with only the hypotheses that
argument uses:

* reduction: `B` touches `A` and `A'`, so `OA ⊥ OB`; and `B_t` lies right of `U`;
* Step 1: tangent lengths; `OB_t^2 = 2bh`; `A_tC_t = 2·OB_t`; the ratio `UM/MB_t = OU/OB_t`;
  converse of the angle bisector theorem (`OM` makes equal angles with `OU` and `OB_t`);
* Step 2: the contact point `T` (`(a+c)T = cA + aC'`); the homothety at `T` makes `A_t, T, C'_b`
  collinear; `A_tC'_b ∥ OM` puts `T` on the chord from `A_t`; `T` is on circle `A`; the isosceles
  triangle `A A_t T` doubles the angle, so `AT ∥ OB_t`; the line of centres through `T` gives
  `AC' ∥ OB_t`;
* Step 3: `K` on `Ω` and `OB_t`; the tangents at `U` and `K` meet at `M` (`MK ⊥ OK`, `MK = MU`);
  the right angle at `K` gives the angle `ψ` at `M`; `OS_0 = OB_t`, `SS_0 = UM`; the right
  triangles `MKB_t` and `SS_0X` are congruent, so `S_0X = KB_t = OB_t - h`, `X = E' = (-h, 0)`, and
  `A` lies on the line through `E'` parallel to `OB_t`;
* Step 4, in Mathlib's Euclidean plane: `∠E'OA = ∠UOB = 2ψ` and `∠OE'A = π/2 - ψ`; the angle sum
  of triangle `OE'A` gives `∠OAE' = π/2 - ψ`, and the converse of the isosceles triangle theorem
  (`EuclideanGeometry.dist_eq_of_angle_eq_angle_of_angle_ne_pi`) gives `OA = OE' = h`.

The main theorem chains the lemmas: each step's conclusion is the next step's hypothesis.

Write `d = OB_t > 0` and `m = UM = (a - c)/2`; `M = (m, h)`, `B_t = (x, h)`, `U = (0, h)`.
-/

namespace SixCircles

/-! ### Reduction -/

/-- `B` touches the congruent circles `A` and `A'`, so `BA = BA'` and `OA ⊥ OB`
(`A = (-(w-a), h-a)`, `B = (x, h-b)`). -/
theorem reduction {h a b w x : ℝ}
    (hAB : (x + (w - a)) ^ 2 + (a - b) ^ 2 = (a + b) ^ 2)
    (hBA' : (w - a - x) ^ 2 + (2 * h - a - b) ^ 2 = (a + b) ^ 2) :
    -(w - a) * x + (h - a) * (h - b) = 0 := by
  linear_combination (-1 / 4 : ℝ) * hAB + (1 / 4 : ℝ) * hBA'

/-- `B_t` lies strictly right of `U`: otherwise `A` and `B` lie in the closed upper-left quadrant
and `OA · OB > 0`. -/
theorem Bt_right {h a b w x : ℝ} (hah : a < h) (hbh : b < h) (hAtBt : -(w - a) < x)
    (hperp : -(w - a) * x + (h - a) * (h - b) = 0) : 0 < x := by
  by_contra hx
  rw [not_lt] at hx
  have hwa : 0 < w - a := by linarith
  have h1 : 0 < (h - a) * (h - b) := mul_pos (by linarith) (by linarith)
  have h2 : (w - a) * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hwa.le hx
  linarith

/-! ### Step 1: a bisector -/

/-- Tangent length: circles of radii `r = ρ^2`, `s = σ^2` touching each other and a line on the
same side touch it at points `2ρσ` apart (`(r+s)^2 - (r-s)^2 = 4rs`). -/
theorem tangent_length {sep ρ σ : ℝ} (hsep : 0 < sep) (hρ : 0 < ρ) (hσ : 0 < σ)
    (h : sep ^ 2 + (ρ ^ 2 - σ ^ 2) ^ 2 = (ρ ^ 2 + σ ^ 2) ^ 2) : sep = 2 * ρ * σ := by
  have h2 : (sep - 2 * ρ * σ) * (sep + 2 * ρ * σ) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · have := mul_pos hρ hσ; linarith

/-- Circle `B` passes through `O` and touches the top side at `B_t`: `OB_t^2 = 2bh`
(the diameter `2b` times the projection `h` of the leg `OB_t` onto it). -/
theorem OBt_sq {h b x : ℝ} (hBO : x ^ 2 + (h - b) ^ 2 = b ^ 2) : x ^ 2 + h ^ 2 = 2 * b * h := by
  linear_combination hBO

/-- `A_tC_t = 2·OB_t`, from the tangent lengths `√a + √c = √(2h)`, `A_tC_t = 2√b(√a+√c)`
and `OB_t^2 = 2bh`. -/
theorem AtCt_eq {h d α β γ : ℝ} (hβ : 0 < β) (hd : 0 < d) (hα : 0 < α) (hγ : 0 < γ)
    (hleft : (α + γ) ^ 2 = 2 * h) (hOB : d ^ 2 = 2 * β ^ 2 * h) :
    2 * β * (α + γ) = 2 * d := by
  have hsq : d ^ 2 = (β * (α + γ)) ^ 2 := by linear_combination hOB - β ^ 2 * hleft
  have hpos : 0 < β * (α + γ) := by positivity
  have hf : (d - β * (α + γ)) * (d + β * (α + γ)) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp hf with k | k
  · linarith
  · linarith

/-- The ratio in which `M` divides `UB_t`: `UM · OB_t = MB_t · OU`, where
`UM = m = (a-c)/2 = (α^2-γ^2)/2`, `MB_t = x - m = β(α-γ)`, `OB_t = d = β(α+γ)`,
`OU = h = (α+γ)^2/2`. -/
theorem bisector_ratio {h d m x α β γ : ℝ}
    (hm : m = (α ^ 2 - γ ^ 2) / 2) (hMB : x - m = β * (α - γ))
    (hd : d = β * (α + γ)) (hh : h = (α + γ) ^ 2 / 2) :
    m * d = (x - m) * h := by
  subst hm hd hh; rw [hMB]; ring

/-- Converse of the angle bisector theorem in triangle `UOB_t`: if `M` divides `UB_t` in the
ratio `OU : OB_t`, then `OM` makes equal angles with `OU = (0,h)` and `OB_t = (x,h)`:
`(OM·OU)/OU = (OM·OB_t)/OB_t`, i.e. `h·d = m·x + h^2`. -/
theorem bisects {h d m x : ℝ} (hh : 0 < h) (hd : 0 < d) (hpy : x ^ 2 + h ^ 2 = d ^ 2)
    (hratio : m * d = (x - m) * h) : h * d = m * x + h ^ 2 := by
  have hb : m * (h + d) = h * x := by linear_combination hratio
  have key : (h * d - m * x - h ^ 2) * (h + d) = 0 := by
    linear_combination (-x) * hb - h * hpy
  rcases mul_eq_zero.mp key with k | k
  · linarith
  · linarith

/-! ### Step 2: a parallel -/

/-- The contact point `T` of circles `A` and `C'` divides `AC'` in the ratio `a : c`:
`(a + c) T = c A + a C'`. The homothety with centre `T` and ratio `-c/a` takes circle `A` to circle
`C'` and the top point `A_t = A + (0, a)` to the bottom point `C'_b = C' - (0, c)`:
`a (C'_b - T) = c (T - A_t)`, so `A_t, T, C'_b` are collinear. -/
theorem homothety {a c A1 A2 C1 C2 T1 T2 : ℝ}
    (hT1 : (a + c) * T1 = c * A1 + a * C1) (hT2 : (a + c) * T2 = c * A2 + a * C2) :
    a * (C1 - T1) = c * (T1 - A1) ∧ a * ((C2 - c) - T2) = c * (T2 - (A2 + a)) := by
  constructor
  · linear_combination -hT1
  · linear_combination -hT2

/-- From `A_t = (-(w-a), h)` to `C'_b = (-(w-c), -h)` the separations are `-2` times those from
`O` to `M = ((a-c)/2, h)`: `A_t C'_b ∥ OM`. -/
theorem chord_parallel_OM {h a c w : ℝ} :
    (-(w - c)) - (-(w - a)) = -2 * ((a - c) / 2) ∧ ((-(h - c)) - c) - ((h - a) + a) = -2 * h := by
  constructor <;> ring

/-- Collinearity of `A_t, T, C'_b` with `C'_b - A_t = -2 (m, h)` puts `T` on the chord from `A_t`
in the direction `-(m, h)`: `(a + c)(T - A_t) = -2a (m, h)`. -/
theorem T_on_chord {a c m h At1 At2 T1 T2 Cb1 Cb2 : ℝ}
    (hom1 : a * (Cb1 - T1) = c * (T1 - At1)) (hom2 : a * (Cb2 - T2) = c * (T2 - At2))
    (hch1 : Cb1 - At1 = -2 * m) (hch2 : Cb2 - At2 = -2 * h) :
    (a + c) * (T1 - At1) = -2 * a * m ∧ (a + c) * (T2 - At2) = -2 * a * h := by
  constructor
  · linear_combination -hom1 + a * hch1
  · linear_combination -hom2 + a * hch2

/-- `T` lies on circle `A`: `(a + c)(T - A) = a (C' - A)` and the tangency `|C' - A| = a + c`
give `|T - A| = a`. -/
theorem T_on_circle {a c A1 A2 C1 C2 T1 T2 : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hT1 : (a + c) * T1 = c * A1 + a * C1) (hT2 : (a + c) * T2 = c * A2 + a * C2)
    (htan : (C1 - A1) ^ 2 + (C2 - A2) ^ 2 = (a + c) ^ 2) :
    (T1 - A1) ^ 2 + (T2 - A2) ^ 2 = a ^ 2 := by
  have e : (a + c) ^ 2 * ((T1 - A1) ^ 2 + (T2 - A2) ^ 2 - a ^ 2) = 0 := by
    linear_combination ((a + c) * (T1 - A1) + a * (C1 - A1)) * hT1
      + ((a + c) * (T2 - A2) + a * (C2 - A2)) * hT2 + a ^ 2 * htan
  rcases mul_eq_zero.mp e with k | k
  · exact absurd k (by positivity)
  · linarith

/-- The angle `ψ` between `OU` and `OB_t` is twice the angle between `OU` and `OM`
(`tan ψ = 2 tan(ψ/2)/(1 - tan^2(ψ/2))`), in the form `x(h^2 - m^2) = 2mh^2`. -/
theorem double_angle {h d m x : ℝ} (hh : 0 < h) (hd : 0 < d) (hx : 0 < x)
    (hpy : x ^ 2 + h ^ 2 = d ^ 2) (hbis : h * d = m * x + h ^ 2) :
    x * (h ^ 2 - m ^ 2) = 2 * m * h ^ 2 := by
  have hb0 : x * (m * (h + d) - h * x) = 0 := by
    linear_combination (-(h + d)) * hbis - h * hpy
  have hb : m * (h + d) = h * x := by
    rcases mul_eq_zero.mp hb0 with k | k
    · linarith
    · linarith
  have hhd : 0 < h + d := by linarith
  have e : (x * (h ^ 2 - m ^ 2) - 2 * m * h ^ 2) * (h + d) ^ 2 = 0 := by
    linear_combination (-x * (m * (h + d) + h * x) - 2 * h ^ 2 * (h + d)) * hb - x * h ^ 2 * hpy
  rcases mul_eq_zero.mp e with k | k
  · linarith
  · nlinarith

/-- The isosceles triangle `A A_t T` doubles the angle. With `k = a + c`, the chord from the top
point `A_t = A + (0, a)` gives `k (T - A_t) = -2a (m, h)`; `T` is on circle `A`; and the doubled
angle is `x(h^2 - m^2) = 2mh^2`. Then the radius `AT` is parallel to `OB_t = (x, h)`. -/
theorem radius_parallel {a h m x k T1 T2 A1 A2 : ℝ} (ha : 0 < a) (hh : 0 < h) (hk : 0 < k)
    (hc1 : k * (T1 - A1) = -2 * a * m) (hc2 : k * (T2 - (A2 + a)) = -2 * a * h)
    (hcirc : (T1 - A1) ^ 2 + (T2 - A2) ^ 2 = a ^ 2)
    (hdbl : x * (h ^ 2 - m ^ 2) = 2 * m * h ^ 2) :
    (T1 - A1) * h - (T2 - A2) * x = 0 := by
  -- the isosceles triangle A A_t T: its base A_tT has k h = m^2 + h^2
  have e1 : 4 * a ^ 2 * (m ^ 2 + h ^ 2 - k * h) = 0 := by
    linear_combination k ^ 2 * hcirc - (k * (T1 - A1) - 2 * a * m) * hc1
      - (k * (T2 - A2) + k * a - 2 * a * h) * hc2
  have hkh : k * h = m ^ 2 + h ^ 2 := by
    rcases mul_eq_zero.mp e1 with k1 | k1
    · exact absurd k1 (by positivity)
    · linarith
  have e2 : k * h * ((T1 - A1) * h - (T2 - A2) * x) = 0 := by
    linear_combination h ^ 2 * hc1 - h * x * hc2 - a * x * hkh + a * hdbl
  rcases mul_eq_zero.mp e2 with k2 | k2
  · exact absurd k2 (by positivity)
  · exact k2

/-- The line of centres `AC'` passes through `T` (`(a + c)(T - A) = a (C' - A)`), so it is parallel
to `AT`, hence to `OB_t`. -/
theorem line_of_centres_parallel {a c A1 A2 C1 C2 T1 T2 x h : ℝ} (ha : 0 < a)
    (hT1 : (a + c) * T1 = c * A1 + a * C1) (hT2 : (a + c) * T2 = c * A2 + a * C2)
    (hAT : (T1 - A1) * h - (T2 - A2) * x = 0) : (C1 - A1) * h - (C2 - A2) * x = 0 := by
  have e : a * ((C1 - A1) * h - (C2 - A2) * x) = 0 := by
    linear_combination (a + c) * hAT - h * hT1 + x * hT2
  rcases mul_eq_zero.mp e with k | k
  · exact absurd k ha.ne'
  · exact k

/-! ### Step 3: the line of centres passes through `E'` -/

/-- `K = (h/d)(x, h)` lies on `Ω` (`OK = h`). -/
theorem K_on_Omega {h d x : ℝ} (hd : 0 < d) (hpy : x ^ 2 + h ^ 2 = d ^ 2) :
    (h / d * x) ^ 2 + (h / d * h) ^ 2 = h ^ 2 := by
  have hd0 : d ≠ 0 := hd.ne'
  field_simp
  linear_combination h ^ 2 * hpy

/-- The tangents to `Ω` at `U` and at `K` meet at `M`: `MK ⊥ OK` and `MK = MU = m`. -/
theorem tangents_meet_at_M {h d m x : ℝ} (hd : 0 < d) (hpy : x ^ 2 + h ^ 2 = d ^ 2)
    (hbis : h * d = m * x + h ^ 2) :
    (h / d * x - m) * (h / d * x) + (h / d * h - h) * (h / d * h) = 0 ∧
    (h / d * x - m) ^ 2 + (h / d * h - h) ^ 2 = m ^ 2 := by
  have hK : (h / d * x) ^ 2 + (h / d * h) ^ 2 = h ^ 2 := K_on_Omega hd hpy
  have hMK : m * (h / d * x) + h * (h / d * h) = h ^ 2 := by
    calc m * (h / d * x) + h * (h / d * h) = h / d * (m * x + h ^ 2) := by ring
      _ = h / d * (h * d) := by rw [hbis]
      _ = h ^ 2 := by field_simp
  constructor
  · linear_combination hK - hMK
  · linear_combination hK - 2 * hMK

/-- The angle at `M` in the right triangle `MKB_t` (right angle at `K`, from the tangent at `K`):
`KB_t · OU = MK · UB_t`, i.e. `(d - h) h = m x`, because the triangle shares its angle at `B_t`
with the right triangle `OUB_t`. In coordinates the right angle at `K` gives it directly. -/
theorem angle_at_M {h d m x : ℝ} (hh : 0 < h) (hd : 0 < d) (hpy : x ^ 2 + h ^ 2 = d ^ 2)
    (hperp : (h / d * x - m) * (h / d * x) + (h / d * h - h) * (h / d * h) = 0) :
    (d - h) * h = m * x := by
  have hK : (h / d * x) ^ 2 + (h / d * h) ^ 2 = h ^ 2 := K_on_Omega hd hpy
  have hd0 : d ≠ 0 := hd.ne'
  have e : h / d * (m * x + h ^ 2 - h * d) = 0 := by
    have : h / d * (h * d) = h ^ 2 := by field_simp
    linear_combination -hperp + hK + (-1 : ℝ) * this + (0 : ℝ) * hpy
  rcases mul_eq_zero.mp e with k | k
  · exact absurd k (by positivity)
  · linarith

/-- `S`, the midpoint of `AC'`: `OS_0 = OB_t` and `SS_0 = UM`. -/
theorem S_facts {h a c w d : ℝ} (hAtCt : 2 * w - a - c = 2 * d) :
    ((-(w - a)) + (-(w - c))) / 2 = -d ∧ ((h - a) + (-(h - c))) / 2 = -((a - c) / 2) := by
  constructor <;> linarith

/-- The right triangles `MKB_t` and `SS_0X` are congruent (equal legs `m`, equal angles `ψ`
adjacent to them); `X` is reached from `S` by going up `m` along the direction `(x, h)`:
`S_0X = KB_t = d - h`. -/
theorem congruent {h d m x : ℝ} (hh : 0 < h) (hM : (d - h) * h = m * x) :
    m / h * x = d - h := by
  have hh0 : h ≠ 0 := hh.ne'
  field_simp
  linear_combination -hM

/-- `A` lies on the line through `X` parallel to `v`, when `C' - A ∥ v`, `S` is the midpoint of
`AC'` and `X - S ∥ v`. -/
theorem A_on_line {A1 A2 C1 C2 S1 S2 X1 X2 v1 v2 l : ℝ}
    (hpar : (C1 - A1) * v2 - (C2 - A2) * v1 = 0)
    (hS1 : S1 = (A1 + C1) / 2) (hS2 : S2 = (A2 + C2) / 2)
    (hX1 : X1 = S1 + l * v1) (hX2 : X2 = S2 + l * v2) :
    (A1 - X1) * v2 - (A2 - X2) * v1 = 0 := by
  subst hS1 hS2 hX1 hX2
  linear_combination (-1 / 2 : ℝ) * hpar

/-! ### Step 4: the isosceles triangle, in the Euclidean plane -/

open EuclideanGeometry Real

lemma inner2 (a b c d : ℝ) : inner ℝ (!₂[a, b]) (!₂[c, d]) = a * c + b * d := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_two, dotProduct]
  ring

lemma norm2 (a b : ℝ) : ‖(!₂[a, b] : EuclideanSpace ℝ (Fin 2))‖ = √(a ^ 2 + b ^ 2) := by
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_two]

lemma vsub2 (a b c d : ℝ) :
    (!₂[a, b] : EuclideanSpace ℝ (Fin 2)) -ᵥ !₂[c, d] = !₂[a - c, b - d] := by
  ext i; fin_cases i <;> simp

/-- The angle at `q` between `p` and `r`, as an explicit arccos. -/
lemma angle2 (p1 p2 q1 q2 r1 r2 : ℝ) :
    ∠ (!₂[p1, p2] : EuclideanSpace ℝ (Fin 2)) !₂[q1, q2] !₂[r1, r2] =
      arccos (((p1 - q1) * (r1 - q1) + (p2 - q2) * (r2 - q2)) /
        (√((p1 - q1) ^ 2 + (p2 - q2) ^ 2) * √((r1 - q1) ^ 2 + (r2 - q2) ^ 2))) := by
  rw [EuclideanGeometry.angle, vsub2, vsub2, InnerProductGeometry.angle, inner2, norm2, norm2]

lemma sqrt_of_eq_sq {u v : ℝ} (hv : 0 ≤ v) (h : u = v ^ 2) : √u = v := by
  rw [h, Real.sqrt_sq hv]

/-- **Step 4.** `O = (0,0)`, `E' = (-h, 0)`, `U = (0, h)`, `B = (x, h - b)` with `OB_t^2 = 2bh`, and
`A = (p, s)` above the horizontal with `OA ⊥ OB` and `A` on the line through `E'` parallel to
`OB_t = (x, h)`. With `ψ = ∠UOB_t`: `∠E'OA = ∠UOB = 2ψ` (a quarter-turn about `O`, and the
isosceles triangle `OBB_t`), `∠OE'A = π/2 - ψ` (`E'A ∥ OB_t`), so by the angle sum
`∠OAE' = π/2 - ψ` too, and the triangle is isosceles: `OA = OE' = h`. -/
theorem isosceles_by_angles {h d p s x b : ℝ} (hh : 0 < h) (hd : 0 < d) (hx : 0 < x)
    (hs : 0 < s) (hb : 0 < b) (hpy : x ^ 2 + h ^ 2 = d ^ 2) (hBO : x ^ 2 + h ^ 2 = 2 * b * h)
    (hline : (p + h) * h = s * x) (hperp : p * x + s * (h - b) = 0) :
    p ^ 2 + s ^ 2 = h ^ 2 := by
  set O : EuclideanSpace ℝ (Fin 2) := !₂[0, 0]
  set E : EuclideanSpace ℝ (Fin 2) := !₂[-h, 0]
  set A : EuclideanSpace ℝ (Fin 2) := !₂[p, s]
  set U : EuclideanSpace ℝ (Fin 2) := !₂[0, h]
  set B : EuclideanSpace ℝ (Fin 2) := !₂[x, h - b]
  set Bt : EuclideanSpace ℝ (Fin 2) := !₂[x, h]
  set ψ := ∠ U O Bt with hψ
  have hd0 : d ≠ 0 := hd.ne'
  have hx0 : x ≠ 0 := hx.ne'
  have hh0 : h ≠ 0 := hh.ne'
  have hb0 : b ≠ 0 := hb.ne'
  have hdh : h ≤ d := by nlinarith
  have rU : √((0 - 0) ^ 2 + (h - 0) ^ 2) = h := sqrt_of_eq_sq hh.le (by ring)
  have rE : √((-h - 0) ^ 2 + (0 - 0) ^ 2) = h := sqrt_of_eq_sq hh.le (by ring)
  have rE' : √((0 - -h) ^ 2 + (0 - 0) ^ 2) = h := sqrt_of_eq_sq hh.le (by ring)
  have rBt : √((x - 0) ^ 2 + (h - 0) ^ 2) = d := sqrt_of_eq_sq hd.le (by linear_combination hpy)
  -- ψ = arccos (h/d)
  have hψv : ψ = arccos (h / d) := by
    rw [hψ, angle2, rU, rBt]
    congr 1; field_simp; ring
  have hψ0 : 0 ≤ ψ := by rw [hψv]; exact arccos_nonneg _
  have hψ2 : ψ < π / 2 := by rw [hψv]; exact arccos_lt_pi_div_two.mpr (by positivity)
  have hcosψ : cos ψ = h / d := by
    rw [hψv]; exact cos_arccos (by
      have : 0 ≤ h / d := by positivity
      linarith) ((div_le_one hd).mpr hdh)
  -- ∠UOB = 2ψ (the isosceles triangle OBB_t doubles the angle)
  have hBnorm : √((x - 0) ^ 2 + (h - b - 0) ^ 2) = b := sqrt_of_eq_sq hb.le (by linear_combination hBO)
  have hUOB : ∠ U O B = 2 * ψ := by
    rw [angle2, rU, hBnorm]
    have harg : ((0 - 0) * (x - 0) + (h - 0) * (h - b - 0)) / (h * b) = cos (2 * ψ) := by
      rw [cos_two_mul, hcosψ]; field_simp; linear_combination h ^ 2 * hBO - h ^ 2 * hpy
    rw [harg, arccos_cos (by linarith) (by linarith)]
  -- ∠E'OA = ∠UOB: the quarter-turn about O takes U to E' and the ray OB to the ray OA
  have hp : p = -(s / x) * (h - b) := by field_simp; linear_combination hperp
  have hAnorm : √((p - 0) ^ 2 + (s - 0) ^ 2) = s / x * b := by
    apply sqrt_of_eq_sq (by positivity)
    rw [hp]; field_simp; linear_combination s ^ 2 * hBO
  have hEOA : ∠ E O A = ∠ U O B := by
    rw [angle2, angle2, rE, rU, hAnorm, hBnorm]
    congr 1
    rw [hp]; field_simp; ring
  -- ∠OE'A = π/2 - ψ (E'A is parallel to OB_t)
  have hOEA : ∠ O E A = π / 2 - ψ := by
    rw [angle2, rE']
    have hph : p + h = s / h * x := by field_simp; linear_combination hline
    have hn : √((p - -h) ^ 2 + (s - 0) ^ 2) = s / h * d := by
      apply sqrt_of_eq_sq (by positivity)
      have : p - -h = p + h := by ring
      rw [this, hph]; field_simp; linear_combination s ^ 2 * hpy
    rw [hn]
    have hsd : h * (s / h * d) = s * d := by field_simp
    have harg : ((0 - -h) * (p - -h) + (0 - 0) * (s - 0)) / (h * (s / h * d)) = x / d := by
      rw [hsd, div_eq_div_iff (by positivity) hd0]
      linear_combination d * hline
    rw [harg, arccos_eq_pi_div_two_sub_arcsin]
    congr 1
    -- arcsin (x/d) = arccos (h/d) = ψ
    rw [hψv, arccos_eq_arcsin (by positivity)]
    congr 1
    symm; apply sqrt_of_eq_sq (by positivity)
    field_simp; linear_combination -hpy
  -- the angle sum of triangle OE'A gives ∠OAE' = π/2 - ψ
  have hEO : E ≠ O := by
    intro hEq
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hEq
    simp [E, O] at this; exact hh0 this
  have hsum := angle_add_angle_add_angle_eq_pi A hEO
  have hOAE : ∠ O A E = ∠ O E A := by
    rw [angle_comm O A E]
    rw [angle_comm A O E, hEOA, hUOB, hOEA] at hsum
    rw [hOEA]; linarith
  -- converse of the isosceles triangle theorem: OE' = OA
  have hpi : ∠ E O A ≠ π := by rw [hEOA, hUOB]; linarith [pi_pos]
  have hdist := dist_eq_of_angle_eq_angle_of_angle_ne_pi hOAE.symm hpi
  rw [EuclideanSpace.dist_eq, EuclideanSpace.dist_eq] at hdist
  simp [Fin.sum_univ_two, O, E, A] at hdist
  have h2 := (Real.sqrt_inj (by positivity) (by positivity)).mp hdist
  linarith

/-! ### The theorem, by the note's route -/

/-- **MathOverflow 515498, the note's proof.** `|AA'| = 2h`. -/
theorem six_circles_note (h a b c w x : ℝ) (hh : 0 < h) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hah : a < h) (hbh : b < h) (hch : c < h)
    (hAB : (x + (w - a)) ^ 2 + (a - b) ^ 2 = (a + b) ^ 2)
    (hBC : (w - c - x) ^ 2 + (b - c) ^ 2 = (b + c) ^ 2)
    (hCA' : (a - c) ^ 2 + (2 * h - a - c) ^ 2 = (a + c) ^ 2)
    (hBA' : (w - a - x) ^ 2 + (2 * h - a - b) ^ 2 = (a + b) ^ 2)
    (hBO : x ^ 2 + (h - b) ^ 2 = b ^ 2)
    (hAtBt : -(w - a) < x) (hBtCt : x < w - c) :
    (2 * (w - a)) ^ 2 + (2 * (h - a)) ^ 2 = (2 * h) ^ 2 := by
  -- Reduction.
  have hperp := reduction hAB hBA'
  have hx : 0 < x := Bt_right hah hbh hAtBt hperp
  -- Step 1: tangent lengths.
  obtain ⟨α, hα0, rfl⟩ : ∃ α : ℝ, 0 < α ∧ α ^ 2 = a := ⟨√a, Real.sqrt_pos.mpr ha, Real.sq_sqrt ha.le⟩
  obtain ⟨β, hβ0, rfl⟩ : ∃ β : ℝ, 0 < β ∧ β ^ 2 = b := ⟨√b, Real.sqrt_pos.mpr hb, Real.sq_sqrt hb.le⟩
  obtain ⟨γ, hγ0, rfl⟩ : ∃ γ : ℝ, 0 < γ ∧ γ ^ 2 = c := ⟨√c, Real.sqrt_pos.mpr hc, Real.sq_sqrt hc.le⟩
  have e1 : x + (w - α ^ 2) = 2 * α * β :=
    tangent_length (by linarith) hα0 hβ0 (by linear_combination hAB)
  have e2 : w - γ ^ 2 - x = 2 * β * γ :=
    tangent_length (by linarith) hβ0 hγ0 (by linear_combination hBC)
  have e3 : 2 * h - α ^ 2 - γ ^ 2 = 2 * α * γ :=
    tangent_length (by linarith) hα0 hγ0 (by linear_combination hCA')
  have hleft : (α + γ) ^ 2 = 2 * h := by linear_combination -e3
  -- OB_t = d.
  have hOB := OBt_sq hBO
  obtain ⟨d, hd0, hpy⟩ : ∃ d : ℝ, 0 < d ∧ x ^ 2 + h ^ 2 = d ^ 2 :=
    ⟨Real.sqrt (x ^ 2 + h ^ 2), Real.sqrt_pos.mpr (by positivity), (Real.sq_sqrt (by positivity)).symm⟩
  -- A_tC_t = 2 OB_t.
  have hAtCt : 2 * β * (α + γ) = 2 * d :=
    AtCt_eq hβ0 hd0 hα0 hγ0 hleft (by rw [← hpy]; linear_combination hOB)
  have hdβ : d = β * (α + γ) := by linarith
  have hW : 2 * w - α ^ 2 - γ ^ 2 = 2 * d := by linear_combination e1 + e2 + hAtCt
  -- The ratio UM/MB_t = OU/OB_t and the bisector OM.
  have hMB : x - (α ^ 2 - γ ^ 2) / 2 = β * (α - γ) := by linear_combination (e1 - e2) / 2
  have hh2 : h = (α + γ) ^ 2 / 2 := by linear_combination -hleft / 2
  have hratio := bisector_ratio rfl hMB hdβ hh2
  have hbis := bisects hh hd0 hpy hratio
  -- Step 2: the contact point T, the homothety, T on the chord from A_t and on circle A, the
  -- doubled angle, the radius AT ∥ OB_t, and the line of centres AC' ∥ OB_t.
  have ha' : (0 : ℝ) < α ^ 2 := by positivity
  have hc' : (0 : ℝ) < γ ^ 2 := by positivity
  set A1 := -(w - α ^ 2) with hA1
  set A2 := h - α ^ 2 with hA2
  set C1 := -(w - γ ^ 2) with hC1
  set C2 := -(h - γ ^ 2) with hC2
  set T1 := (γ ^ 2 * A1 + α ^ 2 * C1) / (α ^ 2 + γ ^ 2) with hT1d
  set T2 := (γ ^ 2 * A2 + α ^ 2 * C2) / (α ^ 2 + γ ^ 2) with hT2d
  have hk0 : (0 : ℝ) < α ^ 2 + γ ^ 2 := by positivity
  have hT1 : (α ^ 2 + γ ^ 2) * T1 = γ ^ 2 * A1 + α ^ 2 * C1 := by rw [hT1d]; field_simp
  have hT2 : (α ^ 2 + γ ^ 2) * T2 = γ ^ 2 * A2 + α ^ 2 * C2 := by rw [hT2d]; field_simp
  obtain ⟨hom1, hom2⟩ := homothety hT1 hT2
  obtain ⟨hch1, hch2⟩ := chord_parallel_OM (h := h) (a := α ^ 2) (c := γ ^ 2) (w := w)
  obtain ⟨hTc1, hTc2⟩ := T_on_chord (At1 := A1) (At2 := A2 + α ^ 2) (Cb1 := C1) (Cb2 := C2 - γ ^ 2)
    hom1 hom2 hch1 hch2
  have hcirc := T_on_circle ha' hc' hT1 hT2 (by rw [hA1, hA2, hC1, hC2]; linear_combination hCA')
  have hdbl := double_angle hh hd0 hx hpy hbis
  have hrad := radius_parallel ha' hh hk0 hTc1 hTc2 hcirc hdbl
  have hpar := line_of_centres_parallel ha' hT1 hT2 hrad
  -- Step 3: tangents from M give the angle at M; the congruence; X = E'; A on the line through E'.
  obtain ⟨hperpK, _hMK⟩ := tangents_meet_at_M hd0 hpy hbis
  have hM := angle_at_M hh hd0 hpy hperpK
  have hcong := congruent hh hM
  obtain ⟨hS1, hS2⟩ := S_facts (h := h) (a := α ^ 2) (c := γ ^ 2) (w := w) (d := d) hW
  have hon := A_on_line (A1 := A1) (A2 := A2) (C1 := C1) (C2 := C2)
    (S1 := -d) (S2 := -((α ^ 2 - γ ^ 2) / 2)) (X1 := -h) (X2 := 0) (v1 := x) (v2 := h)
    (l := (α ^ 2 - γ ^ 2) / 2 / h) hpar (by rw [hA1, hC1]; linarith) (by rw [hA2, hC2]; linarith)
    (by rw [hcong]; ring) (by field_simp; ring)
  have hline : (-(w - α ^ 2) + h) * h = (h - α ^ 2) * x := by rw [hA1, hA2] at hon; linear_combination hon
  -- Step 4: the isosceles triangle OE'A.
  have hA := isosceles_by_angles (p := -(w - α ^ 2)) (s := h - α ^ 2) (x := x) (b := β ^ 2) hh hd0 hx
    (by linarith) (by positivity) hpy hOB hline (by linear_combination hperp)
  linear_combination 4 * hA

end SixCircles
