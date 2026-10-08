import MexSequence.Basic

/-! Arithmetic of `y` and `w`: the facts the hand proof uses about the growing values. -/

namespace MexE27

theorem yspec (b : ℕ) (hb : 3 ≤ b) :
    (y b = 4 * ((b - 3) / 3) + 2 ∧ (b - 3) % 3 = 0) ∨
    (y b = 4 * ((b - 3) / 3) + 5 ∧ (b - 3) % 3 = 1) ∨
    (y b = 4 * ((b - 3) / 3) + 4 ∧ (b - 3) % 3 = 2) := by
  unfold y; split_ifs <;> omega

theorem ysmall (b : ℕ) (hb : b < 3) : (b ≤ 1 ∧ y b = 1) ∨ (b = 2 ∧ y b = 3) := by
  unfold y; split_ifs <;> omega

theorem wspec (d : ℕ) : (d = 0 ∧ w d = 1) ∨ (1 ≤ d ∧ d ≤ 2 ∧ w d = 3) ∨ (3 ≤ d ∧ w d = 2) := by
  unfold w; split_ifs <;> omega

theorem y_pos (b : ℕ) : 1 ≤ y b := by
  rcases Nat.lt_or_ge b 3 with h | h
  · rcases ysmall b h with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
  · rcases yspec b h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega

theorem w_pos (d : ℕ) : 1 ≤ w d := by rcases wspec d with ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ <;> omega

theorem y_eq_one (b : ℕ) (h : y b = 1) : b ≤ 1 := by
  rcases Nat.lt_or_ge b 3 with hb | hb
  · rcases ysmall b hb with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
  · rcases yspec b hb with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega

theorem w_eq_one (d : ℕ) (h : w d = 1) : d = 0 := by
  rcases wspec d with ⟨_, h1⟩ | ⟨_, _, h1⟩ | ⟨_, h1⟩ <;> omega

/-- For `B ≥ 8`, the value `y B` is at least `8`, and it is never `3` mod `4`. -/
theorem yB_facts (B : ℕ) (hB : 8 ≤ B) : 8 ≤ y B ∧ y B % 4 ≠ 3 := by
  rcases yspec B (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

/-- `y` takes the value `y B` only at `B`, among smaller indices. -/
theorem y_ne_of_lt (B c : ℕ) (hB : 8 ≤ B) (hc : c < B) : y c ≠ y B := by
  rcases Nat.lt_or_ge c 3 with h | h
  · have := yB_facts B hB
    rcases ysmall c h with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
  · rcases yspec c h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases yspec B (by omega) with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega

/-- `y c + w d` is never `y B` when `c + d + 1 = B`. -/
theorem yw_ne (B c d : ℕ) (hB : 8 ≤ B) (hcd : c + d + 1 = B) : y c + w d ≠ y B := by
  have hBf := yB_facts B hB
  rcases wspec d with ⟨hd, hw⟩ | ⟨hd1, hd2, hw⟩ | ⟨hd, hw⟩
  · rcases yspec c (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases yspec B (by omega) with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  · rcases yspec c (by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases yspec B (by omega) with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
  · rcases Nat.lt_or_ge c 3 with h | h
    · rcases ysmall c h with ⟨_, h1⟩ | ⟨_, h1⟩ <;> omega
    · rcases yspec c h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases yspec B (by omega) with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega

/-- The index where `y` takes a given value `u ≥ 2` that is not `3` mod `4`. -/
def inv (u : ℕ) : ℕ := 3 * ((u - 2) / 4) + 3 + (if u % 4 = 2 then 0 else if u % 4 = 1 then 1 else 2)

theorem y_inv (u : ℕ) (hu : 2 ≤ u) (h3 : u % 4 ≠ 3) : 3 ≤ inv u ∧ y (inv u) = u := by
  have hi : 3 ≤ inv u := by unfold inv; split_ifs <;> omega
  refine ⟨hi, ?_⟩
  rcases yspec (inv u) hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> unfold inv at * <;> split_ifs at * <;> omega

/-- Every value below `y B` is `0`, `1`, some `y c` with `c < B`, or some `y c + w d` with
    `c + d + 1 = B`. -/
theorem cover (B u : ℕ) (hB : 8 ≤ B) (hu : u < y B) :
    u ≤ 1 ∨ (∃ c, c < B ∧ y c = u) ∨ (∃ c d, c + d + 1 = B ∧ y c + w d = u) := by
  rcases Nat.lt_or_ge u 2 with h | h
  · left; omega
  right
  by_cases h3 : u = 3
  · left; exact ⟨2, by omega, by rw [h3]; rfl⟩
  have hBy := yspec B (by omega)
  by_cases hm : u % 4 = 3
  · -- u = y c + 2 with w d = 2, or one of the three extra sums
    have hu2 := y_inv (u - 2) (by omega) (by omega)
    by_cases hc : inv (u - 2) + 4 ≤ B
    · right
      refine ⟨inv (u - 2), B - 1 - inv (u - 2), by omega, ?_⟩
      rcases wspec (B - 1 - inv (u - 2)) with ⟨_, hw⟩ | ⟨_, _, hw⟩ | ⟨_, hw⟩ <;> omega
    · right
      have e1 := yspec (B - 1) (by omega)
      have e2 := yspec (B - 2) (by omega)
      have e3 := yspec (B - 3) (by omega)
      have hI := yspec (inv (u - 2)) hu2.1
      by_cases x1 : y (B - 1) + 1 = u
      · exact ⟨B - 1, 0, by omega, by rw [show w 0 = 1 from rfl]; omega⟩
      by_cases x2 : y (B - 2) + 3 = u
      · exact ⟨B - 2, 1, by omega, by rw [show w 1 = 3 from rfl]; omega⟩
      by_cases x3 : y (B - 3) + 3 = u
      · exact ⟨B - 3, 2, by omega, by rw [show w 2 = 3 from rfl]; omega⟩
      exfalso
      omega
  · have hui := y_inv u h hm
    by_cases hc : inv u < B
    · left; exact ⟨inv u, hc, hui.2⟩
    · right
      have e1 := yspec (B - 1) (by omega)
      have e2 := yspec (B - 2) (by omega)
      have e3 := yspec (B - 3) (by omega)
      have hI := yspec (inv u) hui.1
      by_cases x1 : y (B - 1) + 1 = u
      · exact ⟨B - 1, 0, by omega, by rw [show w 0 = 1 from rfl]; omega⟩
      by_cases x2 : y (B - 2) + 3 = u
      · exact ⟨B - 2, 1, by omega, by rw [show w 1 = 3 from rfl]; omega⟩
      by_cases x3 : y (B - 3) + 3 = u
      · exact ⟨B - 3, 2, by omega, by rw [show w 2 = 3 from rfl]; omega⟩
      exfalso
      omega

end MexE27
