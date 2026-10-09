import LeanProofs.CubeUnfoldings.Quotients

/-!
# Unfoldings of the cube: Example 6

An unfolding `P` of the five-cube with ten cells in `ℤ⁴`, the homomorphism
`φ x = (x₂ mod 2, 4x₁ + 2x₃ + x₄ mod 10)` onto `ℤ₂ × ℤ₁₀`, and `t = (-1,-1,0,-1)`.
`φ` is injective on `P` and `φ t ∉ φ(P) + φ(P)`, so by Lemma 5 the translates of `P` and
`t - P` by `ker φ` tile `ℤ⁴`. The finite checks are by `decide`, as the paper does by listing
the twenty images.
-/

open Pointwise

namespace CubeUnfoldings

/-- The ten cells, in the paper's order. -/
def P5 : Finset (Fin 4 → ℤ) :=
  {![0, 0, 0, 0], ![1, 0, 0, 0], ![1, -1, 0, 0], ![1, 0, 1, 0], ![1, 1, 1, 0],
   ![1, 1, 2, 0], ![1, 0, -1, 0], ![1, 0, 0, 1], ![1, 0, 0, -1], ![2, 0, 0, 0]}

/-- `φ x = (x₂ mod 2, 4x₁ + 2x₃ + x₄ mod 10)` (coordinates numbered from 1 in the paper). -/
def φ5 : (Fin 4 → ℤ) →+ ZMod 2 × ZMod 10 where
  toFun x := ((x 1 : ZMod 2), 4 * (x 0 : ZMod 10) + 2 * (x 2 : ZMod 10) + (x 3 : ZMod 10))
  map_zero' := by simp
  map_add' x y := by
    simp only [Pi.add_apply, Int.cast_add, Prod.mk_add_mk]
    congr 1; ring

def t5 : Fin 4 → ℤ := ![-1, -1, 0, -1]

lemma φ5_surjective : Function.Surjective φ5 := by
  rintro ⟨a, b⟩
  refine ⟨![4 * 0, (a.val : ℤ), 0, (b.val : ℤ)], ?_⟩
  simp [φ5]

lemma card_P5 : P5.card = 10 := by decide

/-- The images of `P5`, as the paper lists them. -/
lemma image_P5 : P5.image φ5 =
    {(0, 0), (0, 4), (1, 4), (0, 6), (1, 6), (1, 8), (0, 2), (0, 5), (0, 3), (0, 8)} := by
  decide

lemma injOn_P5 : Set.InjOn φ5 P5 := by
  rw [← Finset.card_image_iff, image_P5, card_P5]; decide

lemma φ5_t5 : φ5 t5 = (1, 5) := by decide

lemma not_mem_sumset : φ5 t5 ∉ P5.image φ5 + P5.image φ5 := by
  rw [φ5_t5, image_P5]; decide +kernel

/-- Example 6: `P` and its point reflection `t - P` tile `ℤ⁴` with period lattice `ker φ`. -/
theorem example_five : TilesTwo P5 (refl P5 t5) φ5.ker :=
  (tiles_refl_iff φ5_surjective (by simp [card_P5]) injOn_P5 t5).2 not_mem_sumset

end CubeUnfoldings
