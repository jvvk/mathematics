import Mathlib.Tactic

/-!
# Unit hexagons: the two sign lemmas of the two-reflex case

`cross u v = u₁ v₂ - u₂ v₁`; a positive value means `v` is counterclockwise from `u`.

* If `F` lies in the hull triangle `ACE` (counterclockwise), the turn `E → F → A` is clockwise or straight,
  and straight only on `EA`.
* At the corner `C` of the strict quadrilateral `ACEF`, put `e = E - C`, `f = F - C`, `b = B - C`,
  `d = D - C`. If `b, d` are strictly inside the hull, `b` strictly on the `E`-side of `CF` and `d` strictly
  on the `A`-side, the turn `B → C → D` is negative, so `C` is reflex.
-/

namespace UnitHexagon

/-- Two-dimensional cross product. -/
def cross (u v : ℝ × ℝ) : ℝ := u.1 * v.2 - u.2 * v.1

/-- The orientation of a triple. -/
def orient (P Q R : ℝ × ℝ) : ℝ := cross (Q - P) (R - P)

/-- A point of the triangle `ACE` gives a nonpositive turn `E → F → A`, zero only on `EA`. -/
theorem turn_in_triangle {A C E : ℝ × ℝ} (hACE : 0 < orient A C E) {l μ ν : ℝ}
    (_hl : 0 ≤ l) (hμ : 0 ≤ μ) (_hν : 0 ≤ ν) (hs : l + μ + ν = 1) :
    let F := l • A + μ • C + ν • E
    cross (F - E) (A - F) = -μ * orient A C E ∧ cross (F - E) (A - F) ≤ 0 := by
  intro F
  have key : cross (F - E) (A - F) = -μ * orient A C E := by
    have hl' : l = 1 - μ - ν := by linarith
    simp only [F, cross, orient, hl', Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Prod.fst_sub, Prod.snd_sub, smul_eq_mul]
    ring
  exact ⟨key, by rw [key]; nlinarith⟩

/-- The ray order at `C` makes the turn `B → C → D` negative. -/
theorem ray_order_reflex {e f b d : ℝ × ℝ} (hef : 0 < cross e f) (hfb : cross f b < 0)
    (hfd : 0 < cross f d) (heb : 0 < cross e b) (hed : 0 < cross e d) :
    cross (-b) d < 0 := by
  have id : cross b d * cross e f = cross f d * cross e b - cross f b * cross e d := by
    simp only [cross]; ring
  have : 0 < cross b d * cross e f := by
    rw [id]; nlinarith [mul_pos hfd heb, mul_pos (neg_pos.2 hfb) hed]
  have hbd : 0 < cross b d := by
    by_contra hc; push Not at hc; nlinarith
  simp only [cross, Prod.fst_neg, Prod.snd_neg] at hbd ⊢
  linarith

end UnitHexagon
