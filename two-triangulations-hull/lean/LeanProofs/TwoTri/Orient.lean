import Mathlib.Tactic
import Mathlib.Analysis.Convex.Segment
import Mathlib.Data.Finset.Sym

/-!
# Orientation in the plane

Basic algebra of the orientation determinant over an ordered field `K`. Everything about
crossings, triangles and hulls in `TwoTri` is phrased through the sign of `orient`.
-/

set_option linter.unusedSectionVars false

namespace TwoTri

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Twice the signed area of `p q r`: positive iff `p, q, r` turn counterclockwise. -/
def orient (p q r : K × K) : K := (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- The point `(1 - t) a + t b` of the line through `a` and `b`. -/
def lerp (a b : K × K) (t : K) : K × K := (a.1 + t * (b.1 - a.1), a.2 + t * (b.2 - a.2))

section algebra
variable (p q r a b : K × K) (s t : K)

lemma orient_cyc : orient p q r = orient q r p := by unfold orient; ring
lemma orient_swap12 : orient q p r = -orient p q r := by unfold orient; ring
lemma orient_swap23 : orient p r q = -orient p q r := by unfold orient; ring
lemma orient_swap13 : orient r q p = -orient p q r := by unfold orient; ring
@[simp] lemma orient_self12 : orient p p r = 0 := by unfold orient; ring
@[simp] lemma orient_self13 : orient p q p = 0 := by unfold orient; ring
@[simp] lemma orient_self23 : orient p q q = 0 := by unfold orient; ring

lemma lerp_eq_smul : lerp a b t = (1 - t) • a + t • b := by
  unfold lerp; ext <;> simp <;> ring

@[simp] lemma lerp_zero : lerp a b 0 = a := by unfold lerp; ext <;> simp
@[simp] lemma lerp_one : lerp a b 1 = b := by unfold lerp; ext <;> simp

/-- `orient p q ·` is affine. -/
lemma orient_lerp : orient p q (lerp a b t) = (1 - t) * orient p q a + t * orient p q b := by
  unfold orient lerp; ring

lemma orient_lerp_self : orient a b (lerp a b t) = 0 := by unfold orient lerp; ring

lemma lerp_lerp : lerp (lerp a b s) b t = lerp a b (s + t - s * t) := by
  unfold lerp; ext <;> simp <;> ring

lemma lerp_lerp_left : lerp a (lerp a b s) t = lerp a b (s * t) := by
  unfold lerp; ext <;> simp <;> ring

/-- The three edge orientations of a triangle sum to its own orientation. -/
lemma orient_sum : orient q r a + orient r p a + orient p q a = orient p q r := by
  unfold orient; ring

/-- Barycentric identity: an affine function `orient u v ·` evaluated at `a` is the combination of
its values at the vertices of `p q r`, with weights the edge orientations at `a`. -/
lemma orient_bary (u v : K × K) :
    orient p q r * orient u v a =
      orient q r a * orient u v p + orient r p a * orient u v q + orient p q a * orient u v r := by
  unfold orient; ring

/-- The barycentric identity for the point itself (first coordinate). -/
lemma bary_fst : orient p q r * a.1 = orient q r a * p.1 + orient r p a * q.1 + orient p q a * r.1 := by
  unfold orient; ring

lemma bary_snd : orient p q r * a.2 = orient q r a * p.2 + orient r p a * q.2 + orient p q a * r.2 := by
  unfold orient; ring

lemma lerp_inj {a b : K × K} (h : a ≠ b) {s t : K} (e : lerp a b s = lerp a b t) : s = t := by
  by_contra hst
  apply h
  have h1 := congrArg Prod.fst e
  have h2 := congrArg Prod.snd e
  simp only [lerp] at h1 h2
  have hs : s - t ≠ 0 := sub_ne_zero.mpr hst
  ext
  · have : (s - t) * (b.1 - a.1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hs
    · linarith
  · have : (s - t) * (b.2 - a.2) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hs
    · linarith

end algebra

/-! ### Two signs -/

/-- If a combination `(1 - t) X + t Y` with `0 < t < 1` vanishes and `Y ≠ 0`, the signs differ. -/
lemma mul_neg_of_comb_zero {X Y t : K} (ht0 : 0 < t) (ht1 : t < 1) (hY : Y ≠ 0)
    (h : (1 - t) * X + t * Y = 0) : X * Y < 0 := by
  have h1 : 0 < 1 - t := by linarith
  have hX : X = -(t / (1 - t)) * Y := by field_simp; linarith
  rw [hX]
  have : 0 < t / (1 - t) := div_pos ht0 h1
  have : 0 < Y * Y := mul_self_pos.mpr hY
  nlinarith

/-- If `α X + β Y = 0` with `α, β > 0` and `X ≠ 0`, the signs differ. -/
lemma mul_neg_of_pos_comb {X Y α β : K} (hα : 0 < α) (hβ : 0 < β) (hX : X ≠ 0)
    (h : α * X + β * Y = 0) : X * Y < 0 := by
  have hY : Y = -(α / β) * X := by field_simp; linarith
  rw [hY]
  have : 0 < α / β := div_pos hα hβ
  have : 0 < X * X := mul_self_pos.mpr hX
  nlinarith

end TwoTri
