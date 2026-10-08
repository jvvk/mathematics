/-
  The worked numbers of the paper, checked: Moroń's rectangle (Figure 1, Table 1, the balance and
  signed sums of Sections 2 and 3) and the inflation of the side-112 square with `v(112) = 0`
  (its signed split 273 − 161 = 112, the clash at `t = 1`, and the tiling of `R_224` in Figure 5).
-/
import AlmostSquares.Parity

namespace AlmostSq

/-- Moroń's 33 × 32 squared rectangle, code `(18,15)(7,8)(14,4)(10,1)(9)`. -/
def moron : List Tile :=
  [sq 18 0 14, sq 15 18 17, sq 7 18 10, sq 8 25 9, sq 14 0 0, sq 4 14 10, sq 10 14 0, sq 1 24 9,
    sq 9 24 0]

/-- Four vertical cut lines move one unit left. -/
def moronU (a : ℤ) : ℤ := if a = 14 ∨ a = 18 ∨ a = 24 ∨ a = 25 then -1 else 0

/-- One horizontal cut line moves one unit up. -/
def moronV (b : ℤ) : ℤ := if b = 10 then 1 else 0

theorem moron_dissects : Dissects 33 32 moron :=
  dissectsCheck_sound (by norm_num) (by norm_num) (by decide +kernel)

/-- Figure 1: the moved tiling is an admissible tiling of `R_32`. -/
theorem moron_admissible :
    Admissible 32 (moron.map (img (scaleShift 1 moronU) (scaleShift 1 moronV))) :=
  check_sound (by decide +kernel)

/-- Table 1, the size column. -/
theorem moron_sizes :
    (moron.map (img (scaleShift 1 moronU) (scaleShift 1 moronV))).map Tile.size =
      [17, 15, 6, 8, 13, 3, 10, 1, 9] := by decide +kernel

/-- Section 2: `∑ δu_i s_i = 0` for Moroń's shift. -/
theorem moron_moment : (moron.map (fun T => (moronU (T.x + T.w) - moronU T.x) * T.w)).sum = 0 := by
  decide +kernel

/-- Section 3: the `ε` column splits the sides as `43 = 43`. -/
theorem moron_signed : (moron.map (fun T => eps moronU moronV T * T.w)).sum = 0 ∧
    ((moron.filter (fun T => eps moronU moronV T = 1)).map Tile.w).sum = 43 := by decide +kernel

/-- The inflation of the side-112 square with `v(112) = 0` (Section 2). -/
def u112 (a : ℤ) : ℤ := if a = 29 then -1 else if a = 65 ∨ a = 112 then 1 else 0

def v112 (b : ℤ) : ℤ :=
  if b = 53 then -2 else if b = 33 ∨ b = 37 ∨ b = 60 ∨ b = 62 ∨ b = 77 then -1 else 0

theorem ex112_inflation : IsInflation 112 sq112 u112 v112 :=
  ⟨by decide, by decide, by decide, by decide +kernel⟩

theorem ex112_signed : (sq112.map (fun T => eps u112 v112 T * T.w)).sum = 112 ∧
    ((sq112.filter (fun T => eps u112 v112 T = 1)).map Tile.w).sum = 273 := by decide +kernel

/-- At `t = 1` two sizes clash (the 16- and 15-squares both give 15). -/
theorem ex112_clash : ¬ ((sq112.map (img (scaleShift 1 u112) (scaleShift 1 v112))).map Tile.size).Nodup := by
  decide +kernel

/-- Figure 5: at `t = 2` the inflation is an admissible tiling of `R_224`. -/
theorem ex112_t2 : Admissible 224 (sq112.map (img (scaleShift 2 u112) (scaleShift 2 v112))) :=
  check_sound (by decide +kernel)

end AlmostSq
