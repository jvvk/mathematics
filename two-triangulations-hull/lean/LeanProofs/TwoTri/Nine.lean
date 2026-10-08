import LeanProofs.TwoTri.Step

/-!
# Section 3: the nine-point example

The points and triangulations of the paper (points numbered 1 to 9 as in the table), checked by
the kernel over `ℚ`.
-/

namespace TwoTri.Nine

def p1 : ℚ × ℚ := (33, 47)
def p2 : ℚ × ℚ := (47, 30)
def p3 : ℚ × ℚ := (47, 5)
def p4 : ℚ × ℚ := (29, 20)
def p5 : ℚ × ℚ := (28, 26)
def p6 : ℚ × ℚ := (21, 21)
def p7 : ℚ × ℚ := (23, 29)
def p8 : ℚ × ℚ := (2, 0)
def p9 : ℚ × ℚ := (0, 31)

def P9 : Finset (ℚ × ℚ) := {p1, p2, p3, p4, p5, p6, p7, p8, p9}

/-- The triangulation `A` of the paper. -/
def A9 : Finset (Sym2 (ℚ × ℚ)) :=
  {s(p1, p2), s(p2, p3), s(p3, p8), s(p8, p9), s(p9, p1), s(p1, p4), s(p1, p5), s(p1, p6), s(p1, p7), s(p1, p8), s(p2, p4), s(p2, p8), s(p4, p5), s(p4, p8), s(p5, p6), s(p5, p8), s(p6, p7), s(p6, p8), s(p7, p8)}

/-- The triangulation `B` of the paper. -/
def B9 : Finset (Sym2 (ℚ × ℚ)) :=
  {s(p1, p2), s(p2, p3), s(p3, p8), s(p8, p9), s(p9, p1), s(p2, p5), s(p2, p7), s(p2, p9), s(p3, p4), s(p3, p5), s(p3, p6), s(p3, p7), s(p3, p9), s(p4, p6), s(p4, p7), s(p4, p9), s(p5, p7), s(p6, p9), s(p7, p9)}

/-- The hull edges `12, 23, 38, 89, 91`. -/
def H9 : Finset (Sym2 (ℚ × ℚ)) := {s(p1, p2), s(p2, p3), s(p3, p8), s(p8, p9), s(p9, p1)}

theorem card_P9 : P9.card = 9 := by decide +kernel
theorem genPos_P9 : GenPos P9 := by decide +kernel
theorem hull_P9 : hullEdges P9 = H9 := by decide +kernel
theorem isTri_A9 : IsTri P9 A9 := by decide +kernel
theorem isTri_B9 : IsTri P9 B9 := by decide +kernel
theorem inter_A9_B9 : A9 ∩ B9 = H9 := by decide +kernel
theorem card_H9 : H9.card = 5 := by decide +kernel

/-- The invariant: the face `6 5 1` of `A` (side `65`), and the faces `4 7 9` and `4 3 7` of `B`,
which meet the open segment `65` at parameters `1/2` and `3/4`. -/
theorem inv9 : Inv P9 A9 B9 := by
  refine ⟨p6, p5, p1, p4, p7, p9, p4, p3, p7, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨p3, Or.inr (Or.inl rfl), by decide +kernel⟩, ⟨1 / 2, by norm_num, by norm_num, by decide +kernel⟩,
    ⟨3 / 4, by norm_num, by norm_num, by decide +kernel⟩⟩
  rintro v (rfl | rfl | rfl) <;> decide +kernel

end TwoTri.Nine
