import Mathlib

/-!
# Exact limiting tilings of the ratio-law proof

Constants used in `open-questions/sunflower-phyllotaxis/PROOF_ratio_law.md` (items (b), K0, placement).
Unit disk diameters (the `c = 0` limit), cylinder circumference normalised by the front period.

* `threshold_tan`: a lattice front with `m` downs of angle `β` and `n` ups of angle `β + 60°` closes
  (zero total height) iff `tan β = -√3 n / (2m + n)`. Hence `tan β_D = -√3/2` for `(m, n) = (1, 2)` and
  `tan β_D = -√3/4` for `(3, 2)` (the tiling K0).
* Rational model: at modulus `N` the point `(X, Y) ∈ ℚ²` stands for `(X/√N, √3 Y/√N)`. Squared distances
  become `((ΔX)² + 3 (ΔY)²)/N` and rotation by 60° is rational, so every K0 point (`N = 19`) and every point
  of the `(1,2)` threshold tiling (`N = 7`) is rational, and every distance claim is exact arithmetic.
* K0 (front word `U S U S U U D` at the moment of placement): the pentagon apex `Q` is tangent to `P0, P2, P3`
  (the triple degeneracy), the lagging triangle apex `T` and the burst disk `z1` are both at distance `√3`
  from `Q`, and the height gap is `√(3/76)` in both cases.
* Step one: in the `(2,2)` word `Ua D Ub/+ Ub/−` the lowest location (triangle on `(Ub/−, Ua)`) lies
  `√(3/28)` below the rhombus on `(D, Ub/−)`.
-/

namespace Phyllotaxis.Tilings

open Real

/-! ## Threshold lattices -/

theorem threshold_identity (m n β : ℝ) :
    2 * (m * sin β + n * sin (β + π / 3)) = (2 * m + n) * sin β + √3 * n * cos β := by
  rw [sin_add, sin_pi_div_three, cos_pi_div_three]
  ring

/-- **Threshold law.** `m` downs at angle `β` and `n` ups at `β + 60°` (the triangle threshold: hinge
`120°`) have zero total height iff `tan β = -√3 n / (2m + n)`. -/
theorem threshold_tan {m n β : ℝ} (hβ : cos β ≠ 0) (hmn : 2 * m + n ≠ 0) :
    m * sin β + n * sin (β + π / 3) = 0 ↔ tan β = -(√3 * n) / (2 * m + n) := by
  have h := threshold_identity m n β
  rw [tan_eq_sin_div_cos, div_eq_div_iff hβ hmn]
  constructor
  · intro h0
    rw [h0] at h
    linarith
  · intro h1
    linarith

theorem threshold_one_two {β : ℝ} (hβ : cos β ≠ 0) :
    1 * sin β + 2 * sin (β + π / 3) = 0 ↔ tan β = -(√3 / 2) := by
  rw [threshold_tan hβ (by norm_num)]
  constructor <;> intro h <;> rw [h] <;> ring

theorem threshold_three_two {β : ℝ} (hβ : cos β ≠ 0) :
    3 * sin β + 2 * sin (β + π / 3) = 0 ↔ tan β = -(√3 / 4) := by
  rw [threshold_tan hβ (by norm_num)]
  constructor <;> intro h <;> rw [h] <;> ring

/-! ## Rational model of a tiling at modulus `N` -/

/-- `(X, Y)` stands for the plane point `(X/√N, √3 Y/√N)`. -/
noncomputable def emb (N : ℝ) (p : ℚ × ℚ) : ℝ × ℝ := ((p.1 : ℝ) / √N, √3 * (p.2 : ℝ) / √N)

/-- Squared Euclidean distance in the plane. -/
def sqd (a b : ℝ × ℝ) : ℝ := (a.1 - b.1) ^ 2 + (a.2 - b.2) ^ 2

/-- Squared norm of a rational point, times `N`. -/
def nsq (p : ℚ × ℚ) : ℚ := p.1 ^ 2 + 3 * p.2 ^ 2

/-- Rotation by `+60°` in rational coordinates. -/
def rot60 (p : ℚ × ℚ) : ℚ × ℚ := ((p.1 - 3 * p.2) / 2, (p.1 + p.2) / 2)

/-- Rotation by `-60°` in rational coordinates. -/
def rotm60 (p : ℚ × ℚ) : ℚ × ℚ := ((p.1 + 3 * p.2) / 2, (p.2 - p.1) / 2)

theorem sqd_emb {N : ℝ} (hN : 0 < N) (p q : ℚ × ℚ) :
    sqd (emb N p) (emb N q) = (nsq (p - q) : ℝ) / N := by
  have h3 : √3 ^ 2 = 3 := sq_sqrt (by norm_num)
  have hN' : √N ^ 2 = N := sq_sqrt hN.le
  have hs : √N ≠ 0 := (sqrt_pos.2 hN).ne'
  simp only [sqd, emb, nsq, Prod.fst_sub, Prod.snd_sub]
  push_cast
  rw [show ((p.1 : ℝ) / √N - q.1 / √N) ^ 2 + (√3 * p.2 / √N - √3 * q.2 / √N) ^ 2 =
      ((p.1 - q.1) ^ 2 + √3 ^ 2 * (p.2 - q.2) ^ 2) / √N ^ 2 by field_simp, h3, hN']

/-- Height difference in the plane. -/
theorem height_emb (N : ℝ) (p q : ℚ × ℚ) :
    (emb N p).2 - (emb N q).2 = √3 * ((p.2 - q.2 : ℚ) : ℝ) / √N := by
  simp only [emb]
  push_cast
  ring

/-- `rot60` is the plane rotation by `π/3`. -/
theorem emb_rot60 (N : ℝ) (p : ℚ × ℚ) :
    emb N (rot60 p) = ((emb N p).1 * cos (π / 3) - (emb N p).2 * sin (π / 3),
      (emb N p).1 * sin (π / 3) + (emb N p).2 * cos (π / 3)) := by
  have h3 : √3 * √3 = 3 := mul_self_sqrt (by norm_num)
  simp only [emb, rot60, cos_pi_div_three, sin_pi_div_three]
  push_cast
  ext
  · simp only
    rw [show √3 * (p.2 : ℝ) / √N * (√3 / 2) = (√3 * √3) * p.2 / (2 * √N) by ring, h3]
    ring
  · simp only
    ring

/-- `rotm60` is the plane rotation by `-π/3`. -/
theorem emb_rotm60 (N : ℝ) (p : ℚ × ℚ) :
    emb N (rotm60 p) = ((emb N p).1 * cos (π / 3) + (emb N p).2 * sin (π / 3),
      -(emb N p).1 * sin (π / 3) + (emb N p).2 * cos (π / 3)) := by
  have h3 : √3 * √3 = 3 := mul_self_sqrt (by norm_num)
  simp only [emb, rotm60, cos_pi_div_three, sin_pi_div_three]
  push_cast
  ext
  · simp only
    rw [show √3 * (p.2 : ℝ) / √N * (√3 / 2) = (√3 * √3) * p.2 / (2 * √N) by ring, h3]
    ring
  · simp only
    ring

/-! ## K0: the `(3,2)` lattice at its triangle threshold, front at the pentagon placement (`N = 19`) -/

namespace K0

/-- Down vector, `tan β_D = -√3/4`. -/
def D : ℚ × ℚ := (4, -1)
/-- Up vector `U = D` rotated by `+60°`. -/
def U : ℚ × ℚ := (7 / 2, 3 / 2)
/-- Steep child `S = D` rotated by `-60°`. -/
def S : ℚ × ℚ := (1 / 2, -5 / 2)

theorem U_eq : U = rot60 D := by norm_num [U, rot60, D]
theorem S_eq : S = rotm60 D := by norm_num [S, rotm60, D]
theorem unit_D : nsq D = 19 := by norm_num [nsq, D]
theorem unit_U : nsq U = 19 := by norm_num [nsq, U]
theorem unit_S : nsq S = 19 := by norm_num [nsq, S]

/-- `tan β_D = -√3/4`. -/
theorem slope_D : (emb 19 D).2 / (emb 19 D).1 = -(√3 / 4) := by
  have hs : √19 ≠ 0 := by positivity
  simp only [emb, D]
  field_simp
  norm_num

/-- The lattice closes: three downs and two ups have zero total height. -/
theorem lattice_closes : 3 * D.2 + 2 * U.2 = 0 := by norm_num [D, U]

/-- Front points `z0, ..., z7` of the word `U S U S U U D` (lineage `D/+, D/−, Ua/−/+, Ua/−/−, Ub/+, Ua/+,
Ub/−`); `z1` is the burst disk, `z3, z4, z5, z6` are `P0, P1, P2, P3`. -/
def z0 : ℚ × ℚ := 0
def z1 : ℚ × ℚ := z0 + U
def z2 : ℚ × ℚ := z1 + S
def z3 : ℚ × ℚ := z2 + U
def z4 : ℚ × ℚ := z3 + S
def z5 : ℚ × ℚ := z4 + U
def z6 : ℚ × ℚ := z5 + U
def z7 : ℚ × ℚ := z6 + D

/-- The word closes horizontally with period `19/√19 = √19`. -/
theorem period : z7 = (19, 0) := by norm_num [z7, z6, z5, z4, z3, z2, z1, z0, U, S, D]

/-- Pentagon apex `Q = z4 + U (3/2 + i√3/2)`. -/
def Q : ℚ × ℚ := (11, 2)

theorem Q_eq : Q = z4 + (((3 : ℚ) / 2) • U + ((-3 * U.2 / 2, U.1 / 2) : ℚ × ℚ)) := by
  simp only [Q, z4, z3, z2, z1, z0, U, S, Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul, Prod.fst_zero, Prod.snd_zero]
  norm_num

/-- Triple degeneracy: `Q` is tangent to `P0 = z3`, `P2 = z5` and `P3 = z6`. -/
theorem Q_tangent : nsq (Q - z3) = 19 ∧ nsq (Q - z5) = 19 ∧ nsq (Q - z6) = 19 := by
  norm_num [nsq, Q, z6, z5, z4, z3, z2, z1, z0, U, S]

/-- `|Q - P1| = √3`. -/
theorem Q_P1 : nsq (Q - z4) = 3 * 19 := by norm_num [nsq, Q, z4, z3, z2, z1, z0, U, S]

/-- Lagging triangle on `D`: apex `T = z6 + U = z6 + rot60 D`, tangent to `z6` and `z7`. -/
def T : ℚ × ℚ := z6 + U

theorem T_tangent : nsq (T - z6) = 19 ∧ nsq (T - z7) = 19 := by
  norm_num [nsq, T, z7, z6, z5, z4, z3, z2, z1, z0, U, S, D]

/-- `|T - Q| = √3` and `|Q - z1| = √3`. -/
theorem sqrt3_distances : nsq (T - Q) = 3 * 19 ∧ nsq (Q - z1) = 3 * 19 := by
  norm_num [nsq, T, Q, z6, z5, z4, z3, z2, z1, z0, U, S]

/-- **Placement margin.** `T` lies `√(3/76)` above `Q`, and `Q` lies `√(3/76)` above the burst disk. -/
theorem height_gaps :
    (emb 19 T).2 - (emb 19 Q).2 = √(3 / 76) ∧ (emb 19 Q).2 - (emb 19 z1).2 = √(3 / 76) := by
  have key : √3 * ((1 / 2 : ℚ) : ℝ) / √19 = √(3 / 76) := by
    rw [show (3 / 76 : ℝ) = 3 / (2 ^ 2 * 19) by norm_num, sqrt_div' _ (by positivity),
      sqrt_mul' _ (by norm_num), sqrt_sq (by norm_num)]
    push_cast
    ring
  have hT : T.2 - Q.2 = 1 / 2 := by norm_num [T, Q, z6, z5, z4, z3, z2, z1, z0, U, S]
  have hQ : Q.2 - z1.2 = 1 / 2 := by norm_num [Q, z1, z0, U]
  exact ⟨by rw [height_emb, hT, key], by rw [height_emb, hQ, key]⟩

/-- Real-distance form of the tangencies and of the `√3` margins. -/
theorem real_distances :
    sqd (emb 19 Q) (emb 19 z3) = 1 ∧ sqd (emb 19 Q) (emb 19 z5) = 1 ∧
      sqd (emb 19 Q) (emb 19 z6) = 1 ∧ sqd (emb 19 T) (emb 19 Q) = 3 ∧
      sqd (emb 19 Q) (emb 19 z1) = 3 := by
  obtain ⟨h3, h5, h6⟩ := Q_tangent
  obtain ⟨hT, h1⟩ := sqrt3_distances
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [sqd_emb (by norm_num)] <;> [rw [h3]; rw [h5]; rw [h6]; rw [hT]; rw [h1]] <;> norm_num

end K0

/-! ## Step one: the `(1,2)` threshold tiling and the `(2,2)` alternation margin (`N = 7`) -/

namespace StepOne

/-- Down vector, `tan β_D = -√3/2`. -/
def D : ℚ × ℚ := (2, -1)
/-- Up vector `U = D` rotated by `+60°` (`β_U = 19.107°`). -/
def U : ℚ × ℚ := (5 / 2, 1 / 2)
/-- `Ub/+ = U` rotated by `+60°`. -/
def Up : ℚ × ℚ := (1 / 2, 3 / 2)

theorem U_eq : U = rot60 D := by norm_num [U, rot60, D]
theorem Up_eq : Up = rot60 U := by norm_num [Up, rot60, U]
theorem units : nsq D = 7 ∧ nsq U = 7 ∧ nsq Up = 7 := by norm_num [nsq, D, U, Up]

/-- `tan β_D = -√3/2`. -/
theorem slope_D : (emb 7 D).2 / (emb 7 D).1 = -(√3 / 2) := by
  have hs : √7 ≠ 0 := by positivity
  simp only [emb, D]
  field_simp
  norm_num

/-- The `(1,2)` lattice closes: one down and two ups have zero total height. -/
theorem lattice_closes : D.2 + 2 * U.2 = 0 := by norm_num [D, U]

/-- Word `Ua D Ub/+ Ub/−` (at the threshold `Ub/− = D`), points `w0, ..., w4`. -/
def w0 : ℚ × ℚ := 0
def w1 : ℚ × ℚ := w0 + U
def w2 : ℚ × ℚ := w1 + D
def w3 : ℚ × ℚ := w2 + Up
def w4 : ℚ × ℚ := w3 + D

/-- Period `7/√7 = √7`. -/
theorem period : w4 = (7, 0) := by norm_num [w4, w3, w2, w1, w0, U, D, Up]

/-- Lowest location: triangle on `(Ub/−, Ua)`, apex `w3 + U` tangent to `w3` and `w4`. -/
def Tlow : ℚ × ℚ := w3 + U
/-- Next location: rhombus on `(D, Ub/−)`, apex `w1 + Up` tangent to `w1` and `w3`, clear of `w2`. -/
def Rnext : ℚ × ℚ := w1 + Up

theorem Tlow_tangent : nsq (Tlow - w3) = 7 ∧ nsq (Tlow - w4) = 7 := by
  norm_num [nsq, Tlow, w4, w3, w2, w1, w0, U, D, Up]

theorem Rnext_valid : nsq (Rnext - w1) = 7 ∧ nsq (Rnext - w3) = 7 ∧ nsq (Rnext - w2) = 3 * 7 := by
  norm_num [nsq, Rnext, w3, w2, w1, w0, U, D, Up]

/-- **Alternation margin** `√(3/28)`. -/
theorem alternation_margin : (emb 7 Rnext).2 - (emb 7 Tlow).2 = √(3 / 28) := by
  have hd : Rnext.2 - Tlow.2 = 1 / 2 := by norm_num [Rnext, Tlow, w3, w2, w1, w0, U, D, Up]
  rw [height_emb, hd, show (3 / 28 : ℝ) = 3 / (2 ^ 2 * 7) by norm_num, sqrt_div' _ (by positivity),
    sqrt_mul' _ (by norm_num), sqrt_sq (by norm_num)]
  push_cast
  ring

end StepOne

end Phyllotaxis.Tilings
