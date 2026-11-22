import Mathlib

/-!
# Biased hitomezashi loops: zeros in a label word

A word of steps `b₀ b₁ … b_{L-1}` (`true` = up, `false` = down) is read against an alternating parity
`par, !par, par, …`; position `t` *matches* when `b_t = par_t`. In the paper the label of the `t`-th
vertical line crossed by a loop is `b_t + t + κ (mod 2)` (Lemma 2), so the number of `0` labels is the
number of matches `zerosIdx`, and the number of `1` labels is `zerosIdx (!par)`.

For a closed step word (net displacement `0`), the matches are exactly twice the up-steps leaving an even
height, or exactly twice the up-steps leaving an odd height, according to whether `par` agrees with the
parity of the starting height. The proof is a potential argument: `⌈h/2⌉` (resp. `⌊h/2⌋`) increases by one
exactly at up-steps from even (resp. odd) heights and decreases by one exactly at down-steps from odd
(resp. even) heights.
-/

namespace HitomezashiBiased

/-- Signed value of a step. -/
def sv (b : Bool) : ℤ := if b then 1 else -1

/-- Net displacement of a step word. -/
def disp : List Bool → ℤ
  | [] => 0
  | b :: l => sv b + disp l

/-- Number of steps satisfying a predicate of (step, height before the step), starting at height `h`. -/
def cnt (f : Bool → ℤ → Bool) : ℤ → List Bool → ℕ
  | _, [] => 0
  | h, b :: l => (if f b h then 1 else 0) + cnt f (h + sv b) l

/-- up-step from an even height -/
def eu (b : Bool) (h : ℤ) : Bool := b && (h % 2 == 0)
/-- up-step from an odd height -/
def ou (b : Bool) (h : ℤ) : Bool := b && (h % 2 == 1)
/-- down-step from an even height -/
def ed (b : Bool) (h : ℤ) : Bool := !b && (h % 2 == 0)
/-- down-step from an odd height -/
def od (b : Bool) (h : ℤ) : Bool := !b && (h % 2 == 1)

/-- Matches of a word against the alternating parity starting with `par`. -/
def zerosIdx : Bool → List Bool → ℕ
  | _, [] => 0
  | par, b :: l => (if b == par then 1 else 0) + zerosIdx (!par) l

/-- Parity flag of a height (`true` for even). -/
def ev (h : ℤ) : Bool := h % 2 == 0

private lemma ev_step (h : ℤ) (b : Bool) : ev (h + sv b) = !ev h := by
  rcases Int.emod_two_eq_zero_or_one h with h0 | h0 <;> cases b <;> simp only [ev, sv] <;>
    simp [h0] <;> omega

private lemma step_eu_od (h : ℤ) (b : Bool) :
    ((if eu b h then 1 else 0 : ℕ) : ℤ) - ((if od b h then 1 else 0 : ℕ) : ℤ) =
      (h + sv b + 1) / 2 - (h + 1) / 2 := by
  rcases Int.emod_two_eq_zero_or_one h with h0 | h0 <;> cases b <;> simp [eu, od, sv, h0] <;> omega

private lemma step_ou_ed (h : ℤ) (b : Bool) :
    ((if ou b h then 1 else 0 : ℕ) : ℤ) - ((if ed b h then 1 else 0 : ℕ) : ℤ) =
      (h + sv b) / 2 - h / 2 := by
  rcases Int.emod_two_eq_zero_or_one h with h0 | h0 <;> cases b <;> simp [ou, ed, sv, h0] <;> omega

/-- Potential for up-from-even minus down-from-odd. -/
theorem eu_sub_od (h : ℤ) (l : List Bool) :
    (cnt eu h l : ℤ) - cnt od h l = (h + disp l + 1) / 2 - (h + 1) / 2 := by
  induction l generalizing h with
  | nil => simp [cnt, disp]
  | cons b l ih =>
    simp only [cnt, disp, Nat.cast_add]
    have := ih (h + sv b)
    have := step_eu_od h b
    rw [show h + (sv b + disp l) = h + sv b + disp l by ring]
    push_cast at *
    linarith

/-- Potential for up-from-odd minus down-from-even. -/
theorem ou_sub_ed (h : ℤ) (l : List Bool) :
    (cnt ou h l : ℤ) - cnt ed h l = (h + disp l) / 2 - h / 2 := by
  induction l generalizing h with
  | nil => simp [cnt, disp]
  | cons b l ih =>
    simp only [cnt, disp, Nat.cast_add]
    have := ih (h + sv b)
    have := step_ou_ed h b
    rw [show h + (sv b + disp l) = h + sv b + disp l by ring]
    push_cast at *
    linarith

/-- Matches against the parity aligned with the height: up-from-even plus down-from-odd. -/
theorem zeros_aligned (h : ℤ) (l : List Bool) :
    zerosIdx (ev h) l = cnt eu h l + cnt od h l := by
  induction l generalizing h with
  | nil => simp [zerosIdx, cnt]
  | cons b l ih =>
    simp only [zerosIdx, cnt]
    rw [← ev_step h b, ih]
    rcases Int.emod_two_eq_zero_or_one h with h0 | h0 <;> cases b <;> simp [eu, od, ev, h0] <;> omega

/-- Matches against the opposite parity: up-from-odd plus down-from-even. -/
theorem zeros_opposite (h : ℤ) (l : List Bool) :
    zerosIdx (!ev h) l = cnt ou h l + cnt ed h l := by
  induction l generalizing h with
  | nil => simp [zerosIdx, cnt]
  | cons b l ih =>
    simp only [zerosIdx, cnt]
    rw [show (!!ev h) = !ev (h + sv b) by rw [ev_step], ih]
    rcases Int.emod_two_eq_zero_or_one h with h0 | h0 <;> cases b <;> simp [ou, ed, ev, h0] <;> omega

/-- **Label-word lemma.** For a closed word, the matches are twice the up-steps from even heights
(aligned parity) or twice the up-steps from odd heights (opposite parity). -/
theorem zeros_closed (h : ℤ) (l : List Bool) (hl : disp l = 0) :
    zerosIdx (ev h) l = 2 * cnt eu h l ∧
    zerosIdx (!ev h) l = 2 * cnt ou h l := by
  have a := eu_sub_od h l
  have b := ou_sub_ed h l
  rw [hl, add_zero, sub_self] at a b
  rw [zeros_aligned, zeros_opposite]
  omega

theorem cnt_append (f : Bool → ℤ → Bool) (h : ℤ) (l₁ l₂ : List Bool) :
    cnt f h (l₁ ++ l₂) = cnt f h l₁ + cnt f (h + disp l₁) l₂ := by
  induction l₁ generalizing h with
  | nil => simp [cnt, disp]
  | cons b l ih => simp [cnt, disp, ih, add_assoc]

theorem disp_append (l₁ l₂ : List Bool) : disp (l₁ ++ l₂) = disp l₁ + disp l₂ := by
  induction l₁ with
  | nil => simp [disp]
  | cons b l ih => simp [disp, ih, add_assoc]

/-- Raising a word by one level swaps even and odd starting heights. -/
theorem cnt_eu_shift (h : ℤ) (l : List Bool) : cnt eu (h + 1) l = cnt ou h l := by
  induction l generalizing h with
  | nil => simp [cnt]
  | cons b l ih =>
    simp only [cnt]
    rw [show h + 1 + sv b = h + sv b + 1 by ring, ih]
    have h2 : ((h + 1) % 2 == 0) = (h % 2 == 1) := by
      rcases Int.emod_two_eq_zero_or_one h with h0 | h0 <;> simp [h0] <;> omega
    simp [eu, ou, h2]

theorem cnt_ou_shift (h : ℤ) (l : List Bool) : cnt ou (h + 1) l = cnt eu h l := by
  induction l generalizing h with
  | nil => simp [cnt]
  | cons b l ih =>
    simp only [cnt]
    rw [show h + 1 + sv b = h + sv b + 1 by ring, ih]
    have h2 : ((h + 1) % 2 == 1) = (h % 2 == 0) := by
      rcases Int.emod_two_eq_zero_or_one h with h0 | h0 <;> simp [h0] <;> omega
    simp [eu, ou, h2]

/-- **Weights of a loop's label word.** For a closed word `P` (in the paper, the Dyck path `P_vert(L)`),
the label word is read off the elevated word `U P D`. Whatever the offset `par`, the numbers of `0`
labels and `1` labels are `(2A, 2B)` or `(2B, 2A)`, with `A = 1 + #(up-steps of P from odd heights)` and
`B = #(up-steps of P from even heights)`. -/
theorem label_word (P : List Bool) (hP : disp P = 0) (par : Bool) :
    let w := true :: (P ++ [false])
    let A := 1 + cnt ou 0 P
    let B := cnt eu 0 P
    (zerosIdx par w = 2 * A ∧ zerosIdx (!par) w = 2 * B) ∨
    (zerosIdx par w = 2 * B ∧ zerosIdx (!par) w = 2 * A) := by
  intro w A B
  have hw : disp w = 0 := by simp [w, disp, disp_append, hP, sv]
  have key := zeros_closed 0 w hw
  have e1 : cnt eu 0 w = A := by
    show cnt eu 0 (true :: (P ++ [false])) = 1 + cnt ou 0 P
    rw [cnt, cnt_append, show (0 : ℤ) + sv true = 0 + 1 by simp [sv], cnt_eu_shift]
    simp [cnt, eu]
  have e2 : cnt ou 0 w = B := by
    show cnt ou 0 (true :: (P ++ [false])) = cnt eu 0 P
    rw [cnt, cnt_append, show (0 : ℤ) + sv true = 0 + 1 by simp [sv], cnt_ou_shift]
    simp [cnt, ou]
  rw [e1, e2] at key
  cases par
  · right
    simpa [ev] using And.symm key
  · left
    simpa [ev] using key

end HitomezashiBiased
