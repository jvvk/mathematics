import LeanProofs.ZeroSumGame.Order3

/-!
# Order three with distinct entries: the gap lemma and the five families

Normalise the second and third rows to `P = (0, p, p+q)` and `Q = (0, r, r+s)` with positive gaps.
By the criterion, a first-row value `a` is usable exactly when `-a` is a sum `x + y` (`x ∈ P`,
`y ∈ Q`) in two different ways. Two representations of one value are a coincidence between a
difference of `P` and a difference of `Q`; there are nine, and each forces the value to be `p`,
`p + r`, `p + q` or `p + q + r` (`collision`). Three distinct such values force one of five gap
patterns (`three_values`), and in each pattern the doubly represented values are exactly three
(`order3_distinct`).
-/

namespace ZeroSumGame

/-- The normalised rows. -/
def Pv (p q : ℝ) : Fin 3 → ℝ := ![0, p, p + q]
def Qv (r s : ℝ) : Fin 3 → ℝ := ![0, r, r + s]

/-- `t` is a sum `P i + Q j` in two different ways. -/
def Two (p q r s t : ℝ) : Prop :=
  ∃ i j i' j' : Fin 3, (i, j) ≠ (i', j') ∧ Pv p q i + Qv r s j = t ∧ Pv p q i' + Qv r s j' = t

/-- The nine coincidences of a `P`-difference with a `Q`-difference, and the value they double. -/
def Coll (p q r s t : ℝ) : Prop :=
  (t = p ∧ p = r) ∨ (t = p ∧ p = r + s) ∨ (t = p + r ∧ p = s) ∨
  (t = p + q ∧ q = r) ∨ (t = p + q ∧ q = r + s) ∨ (t = p + q ∧ p + q = r) ∨
  (t = p + q ∧ p + q = r + s) ∨ (t = p + q + r ∧ s = q) ∨ (t = p + q + r ∧ s = p + q)

set_option maxHeartbeats 1000000 in
/-- **Collision lemma.** -/
theorem collision {p q r s t : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    (h : Two p q r s t) : Coll p q r s t := by
  obtain ⟨i, j, i', j', hne, h1, h2⟩ := h
  unfold Coll
  fin_cases i <;> fin_cases j <;> fin_cases i' <;> fin_cases j' <;>
    simp [Pv, Qv] at hne h1 h2 ⊢ <;>
    first
    | (exfalso; linarith)
    | (left; constructor <;> linarith)
    | (right; left; constructor <;> linarith)
    | (right; right; left; constructor <;> linarith)
    | (right; right; right; left; constructor <;> linarith)
    | (right; right; right; right; left; constructor <;> linarith)
    | (right; right; right; right; right; left; constructor <;> linarith)
    | (right; right; right; right; right; right; left; constructor <;> linarith)
    | (right; right; right; right; right; right; right; left; constructor <;> linarith)
    | (right; right; right; right; right; right; right; right; constructor <;> linarith)

/-- The five gap patterns: `I` has `C = B`; `II` to `V` have `h > 0` with `(B, C)` equal to
`((0,h,2h), (0,h,3h))`, `((0,h,2h), (0,2h,3h))`, `((0,h,3h), (0,h,2h))`, `((0,2h,3h), (0,h,2h))`. -/
def Fam (p q r s : ℝ) : Prop :=
  (r = p ∧ s = q) ∨ (q = p ∧ r = p ∧ s = 2 * p) ∨ (q = p ∧ r = 2 * p ∧ s = p) ∨
  (q = 2 * p ∧ r = p ∧ s = p) ∨ (p = 2 * q ∧ r = q ∧ s = q)

set_option maxHeartbeats 4000000 in
/-- **Three doubled values force a family.** -/
theorem three_values {p q r s t₁ t₂ t₃ : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hs : 0 < s)
    (h₁ : Coll p q r s t₁) (h₂ : Coll p q r s t₂) (h₃ : Coll p q r s t₃)
    (d₁₂ : t₁ ≠ t₂) (d₁₃ : t₁ ≠ t₃) (d₂₃ : t₂ ≠ t₃) : Fam p q r s := by
  unfold Coll at h₁ h₂ h₃
  unfold Fam
  rcases h₁ with ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ |
      ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
  rcases h₂ with ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩ |
      ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
  rcases h₃ with ⟨a3, b3⟩ | ⟨a3, b3⟩ | ⟨a3, b3⟩ | ⟨a3, b3⟩ | ⟨a3, b3⟩ | ⟨a3, b3⟩ | ⟨a3, b3⟩ |
      ⟨a3, b3⟩ | ⟨a3, b3⟩ <;>
  first
    | exact absurd (by linarith) d₁₂
    | exact absurd (by linarith) d₁₃
    | exact absurd (by linarith) d₂₃
    | (exfalso; linarith)
    | (left; constructor <;> linarith)
    | (right; left; refine ⟨?_, ?_, ?_⟩ <;> linarith)
    | (right; right; left; refine ⟨?_, ?_, ?_⟩ <;> linarith)
    | (right; right; right; left; refine ⟨?_, ?_, ?_⟩ <;> linarith)
    | (right; right; right; right; refine ⟨?_, ?_, ?_⟩ <;> linarith)

/-- Each coincidence really doubles its value. -/
theorem coll_two {p q r s t : ℝ} (h : Coll p q r s t) : Two p q r s t := by
  unfold Coll at h
  rcases h with ⟨ht, h⟩ | ⟨ht, h⟩ | ⟨ht, h⟩ | ⟨ht, h⟩ | ⟨ht, h⟩ | ⟨ht, h⟩ | ⟨ht, h⟩ | ⟨ht, h⟩ |
      ⟨ht, h⟩
  · exact ⟨1, 0, 0, 1, by decide, by simp [Pv, Qv]; linarith, by simp [Pv, Qv]; linarith⟩
  · exact ⟨1, 0, 0, 2, by decide, by simp [Pv, Qv]; linarith, by simp [Pv, Qv]; linarith⟩
  · exact ⟨1, 1, 0, 2, by decide, by simp [Pv, Qv]; linarith, by simp [Pv, Qv]; linarith⟩
  · exact ⟨2, 0, 1, 1, by decide, by simp [Pv, Qv]; linarith, by simp [Pv, Qv]; linarith⟩
  · exact ⟨2, 0, 1, 2, by decide, by simp [Pv, Qv]; linarith, by simp [Pv, Qv]; linarith⟩
  · exact ⟨2, 0, 0, 1, by decide, by simp [Pv, Qv]; linarith, by simp [Pv, Qv]; linarith⟩
  · exact ⟨2, 0, 0, 2, by decide, by simp [Pv, Qv]; linarith, by simp [Pv, Qv]; linarith⟩
  · exact ⟨2, 1, 1, 2, by decide, by simp [Pv, Qv]; linarith, by simp [Pv, Qv]; linarith⟩
  · exact ⟨2, 1, 0, 2, by decide, by simp [Pv, Qv]; linarith, by simp [Pv, Qv]; linarith⟩

/-- The normalised matrix with first row `a`. -/
def mat (a : Fin 3 → ℝ) (p q r s : ℝ) : Array N3 := fun x =>
  if x.1 = 0 then a x.2 else if x.1 = 1 then Pv p q x.2 else Qv r s x.2

lemma Qv_injective {r s : ℝ} (hr : 0 < r) (hs : 0 < s) : Function.Injective (Qv r s) := by
  intro j j' h
  fin_cases j <;> fin_cases j' <;> simp [Qv] at h ⊢ <;> linarith

/-- **Order three, normalised.** The matrix is winning exactly when every `-a i` is doubled. -/
theorem win_iff_two {a : Fin 3 → ℝ} {p q r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Winning k3 (mat a p q r s) ↔ ∀ i, Two p q r s (-a i) := by
  rw [order3_criterion]
  simp only [mat, show ((1 : Fin 3) = 0) = False by decide,
    show ((2 : Fin 3) = 0) = False by decide, show ((2 : Fin 3) = 1) = False by decide, ↓reduceIte]
  constructor
  · intro h i
    obtain ⟨j, l, hj, hz⟩ := h i 0
    obtain ⟨j', l', hj', hz'⟩ := h i j
    exact ⟨j, l, j', l', fun e => hj' (Prod.mk.inj e).1.symm, by linarith, by linarith⟩
  · intro h i j₀
    obtain ⟨i₁, j₁, i₂, j₂, hne, h1, h2⟩ := h i
    have hi : i₁ ≠ i₂ := by
      intro e
      subst e
      have : Qv r s j₁ = Qv r s j₂ := by linarith
      exact hne (by rw [Qv_injective hr hs this])
    by_cases e : i₁ = j₀
    · exact ⟨i₂, j₂, fun e' => hi (e.trans e'.symm), by linarith⟩
    · exact ⟨i₁, j₁, e, by linarith⟩

/-- **Order three, distinct first row.** A winning normalised matrix whose first row has distinct
entries lies in one of the five families, and every first-row value is a coincidence value;
conversely coincidence values always win. -/
theorem order3_distinct {a : Fin 3 → ℝ} {p q r s : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hs : 0 < s) (ha : Function.Injective a) :
    Winning k3 (mat a p q r s) ↔ Fam p q r s ∧ ∀ i, Coll p q r s (-a i) := by
  rw [win_iff_two hr hs]
  constructor
  · intro h
    have hc : ∀ i, Coll p q r s (-a i) := fun i => collision hp hq hr hs (h i)
    refine ⟨three_values hp hq hr hs (hc 0) (hc 1) (hc 2) ?_ ?_ ?_, hc⟩ <;>
      intro e <;> have := ha (neg_injective e) <;> simp at this
  · exact fun h i => coll_two (h.2 i)

end ZeroSumGame
