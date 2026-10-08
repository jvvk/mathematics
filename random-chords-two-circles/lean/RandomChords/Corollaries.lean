import RandomChords.Centres

/-!
# Corollaries 5 and 6: Dan's question for every ratio, and chains of circles

* `cor5`: three touching circles in a row with radii `a, b, c`; `O` is the centre of the third,
  at distance `b + c` beyond `Q`. The distances from `O` to `AB` and to `BC` have the same law exactly
  when `ac = b²`, and then the law is that of `|b cos U - (b + c) cos V|`; so for every `ρ` the two
  lines meet the circle of radius `ρ` about `O` with the same probability (`cor5_hit`).
* `theorem4_mirror`: the same theorem with the roles of the circles exchanged (the line `AB` and a
  chord `AA'` of the first circle, seen from a point beyond `P`), by the reflection `x ↦ 2q - D - x`.
* `cor6`: along a row of touching circles of radii `r^k`, both versions apply to every consecutive
  pair.
-/

open Real MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Chords

variable {a b D : ℝ}

lemma measurable_dAB (a b D q o : ℝ) : Measurable (dAB a b D q o) := by
  unfold dAB lineDist
  exact (Continuous.measurable (by fun_prop)).div
    (measurable_len.comp (Continuous.measurable (by fun_prop)))

lemma measurable_dBC (b q o : ℝ) : Measurable (dBC b q o) := by
  unfold dBC lineDist
  exact (Continuous.measurable (by fun_prop)).div
    (measurable_len.comp (Continuous.measurable (by fun_prop)))

/-- **Corollary 5.** Three touching circles with collinear centres: the distances from the third
centre `O` to `AB` and to `BC` have the same law if and only if `ac = b²`; then the common law is
that of `|b cos U - (b + c) cos V|`. -/
theorem cor5 (ha : 0 < a) (hb : 0 < b) {c : ℝ} (hc : 0 < c) (q : ℝ) :
    (Measure.map (dAB a b (a + b) q (b + c)) volume = Measure.map (dBC b q (b + c)) volume ↔
      a * c = b ^ 2) ∧
    (a * c = b ^ 2 → Measure.map (dBC b q (b + c)) volume = (4 : ℝ≥0∞) • lawW (b, -(b + c))) := by
  refine ⟨?_, fun _ => ?_⟩
  · rw [theorem4 ha hb le_rfl]
    constructor
    · rintro (h | ⟨-, h⟩)
      · linarith
      · field_simp at h; nlinarith
    · intro h
      right
      refine ⟨rfl, ?_⟩
      field_simp; nlinarith
  · rw [law_dBC' hb, abs_of_pos (by linarith)]

/-- In Corollary 5, the two lines meet every circle about `O` with the same probability. -/
theorem cor5_hit (ha : 0 < a) (hb : 0 < b) {c : ℝ} (hc : 0 < c) (q : ℝ) (h : a * c = b ^ 2)
    (ρ : ℝ) :
    volume {ω | dAB a b (a + b) q (b + c) ω ≤ ρ} = volume {ω | dBC b q (b + c) ω ≤ ρ} := by
  have he := ((cor5 ha hb hc q).1).2 h
  have h1 := congrArg (fun μ : Measure ℝ => μ (Iic ρ)) he
  rwa [Measure.map_apply (measurable_dAB _ _ _ _ _) measurableSet_Iic,
    Measure.map_apply (measurable_dBC _ _ _) measurableSet_Iic] at h1

/-! ### The mirror image -/

/-- Reflection in the vertical line `x = k / 2`. -/
def refl (k : ℝ) (X : ℝ × ℝ) : ℝ × ℝ := (k - X.1, X.2)

lemma lineDist_refl (k : ℝ) (O X Y : ℝ × ℝ) :
    lineDist (refl k O) (refl k X) (refl k Y) = lineDist O X Y := by
  unfold lineDist len refl
  simp only [Prod.fst_sub, Prod.snd_sub]
  congr 1
  · rw [← abs_neg]; congr 1; ring
  · congr 1; ring

lemma lineDist_comm (O X Y : ℝ × ℝ) : lineDist O X Y = lineDist O Y X := by
  unfold lineDist len
  simp only [Prod.fst_sub, Prod.snd_sub]
  congr 1
  · rw [← abs_neg]; congr 1; ring
  · congr 1; ring

lemma ccos_pi_sub (α : Ang) : ccos (((π : ℝ) : Ang) - α) = -ccos α := by
  induction α using QuotientAddGroup.induction_on with
  | H x =>
    rw [show ((π : ℝ) : Ang) - (x : Ang) = ((π - x : ℝ) : Ang) from (QuotientAddGroup.mk_sub _ _ _).symm,
      ccos_coe, ccos_coe, cos_pi_sub]

lemma csin_pi_sub (α : Ang) : csin (((π : ℝ) : Ang) - α) = csin α := by
  induction α using QuotientAddGroup.induction_on with
  | H x =>
    rw [show ((π : ℝ) : Ang) - (x : Ang) = ((π - x : ℝ) : Ang) from (QuotientAddGroup.mk_sub _ _ _).symm,
      csin_coe, csin_coe, sin_pi_sub]

lemma refl_pt (k c r : ℝ) (α : Ang) : refl k (pt c r α) = pt (k - c) r (((π : ℝ) : Ang) - α) := by
  unfold refl pt
  rw [ccos_pi_sub, csin_pi_sub]
  ext <;> simp; ring

/-- The distance from `O' = (q - D - o', 0)`, beyond `P`, to the line `AB`. -/
def dAB' (a b D q o' : ℝ) (ω : Ang × Ang) : ℝ :=
  lineDist (q - D - o', 0) (pt (q - D) a ω.1) (pt q b ω.2)

/-- The distance from `O'` to the chord line `AA'` of the first circle. -/
def dAA (a D q o' : ℝ) (ω : Ang × Ang) : ℝ :=
  lineDist (q - D - o', 0) (pt (q - D) a ω.1) (pt (q - D) a ω.2)

/-- `α ↦ π - α` on both angles, exchanging them. -/
def flipSwap (ω : Ang × Ang) : Ang × Ang := (((π : ℝ) : Ang) - ω.2, ((π : ℝ) : Ang) - ω.1)

/-- `α ↦ π - α` on both angles. -/
def flip2 (ω : Ang × Ang) : Ang × Ang := (((π : ℝ) : Ang) - ω.1, ((π : ℝ) : Ang) - ω.2)

lemma mp_flip : MeasurePreserving (fun α : Ang => ((π : ℝ) : Ang) - α) volume volume :=
  Measure.measurePreserving_sub_left volume _

lemma mp_flip2 : MeasurePreserving flip2 volume volume := by
  have := mp_flip.prod mp_flip
  rw [← Measure.volume_eq_prod] at this
  exact this

lemma mp_flipSwap : MeasurePreserving flipSwap volume volume := by
  have h := mp_flip2.comp (Measure.measurePreserving_swap (μ := (volume : Measure Ang))
    (ν := (volume : Measure Ang)))
  rw [← Measure.volume_eq_prod] at h
  exact h

lemma dAB'_eq (a b D q o' : ℝ) (ω : Ang × Ang) :
    dAB' a b D q o' ω = dAB b a D q o' (flipSwap ω) := by
  unfold dAB' dAB flipSwap
  rw [← lineDist_refl (2 * q - D), refl_pt, refl_pt, lineDist_comm]
  have h1 : refl (2 * q - D) (q - D - o', 0) = (q + o', 0) := by unfold refl; ext <;> simp; ring
  rw [h1]
  congr 2 <;> ring_nf

lemma dAA_eq (a D q o' : ℝ) (ω : Ang × Ang) :
    dAA a D q o' ω = dBC a q o' (flip2 ω) := by
  unfold dAA dBC flip2
  rw [← lineDist_refl (2 * q - D), refl_pt, refl_pt]
  have h1 : refl (2 * q - D) (q - D - o', 0) = (q + o', 0) := by unfold refl; ext <;> simp; ring
  rw [h1]
  congr 2 <;> ring_nf

/-- **Theorem 4, mirrored.** `d(O', AB)` and `d(O', AA')` have the same law exactly when `O' = P`
(`o' = 0`), or the circles touch and `O'` lies beyond `P`, away from `Q`, with
`|PO'| = a (a + b) / b`. -/
theorem theorem4_mirror (ha : 0 < a) (hb : 0 < b) (hD : a + b ≤ D) (q o' : ℝ) :
    Measure.map (dAB' a b D q o') volume = Measure.map (dAA a D q o') volume ↔
      o' = 0 ∨ (D = a + b ∧ o' = a * (a + b) / b) := by
  have e1 : Measure.map (dAB' a b D q o') volume = Measure.map (dAB b a D q o') volume := by
    rw [show dAB' a b D q o' = dAB b a D q o' ∘ flipSwap from funext (dAB'_eq a b D q o'),
      ← Measure.map_map (measurable_dAB _ _ _ _ _) mp_flipSwap.measurable, mp_flipSwap.map_eq]
  have e2 : Measure.map (dAA a D q o') volume = Measure.map (dBC a q o') volume := by
    rw [show dAA a D q o' = dBC a q o' ∘ flip2 from funext (dAA_eq a D q o'),
      ← Measure.map_map (measurable_dBC _ _ _) mp_flip2.measurable, mp_flip2.map_eq]
  rw [e1, e2, theorem4 hb ha (by linarith)]
  constructor <;> rintro (h | ⟨h1, h2⟩)
  · exact Or.inl h
  · exact Or.inr ⟨by linarith, by rw [h2]; ring⟩
  · exact Or.inl h
  · exact Or.inr ⟨by linarith, by rw [h2]; ring⟩

/-! ### Chains -/

/-- **Corollary 6.** Circles `Γ_k` of radii `r^k` (`k ∈ ℤ`) touch in a row, with centres `(x k, 0)`
(`x (k + 1) = x k + r^k + r^(k+1)`). Then `d(O_{k+2}, A_k A_{k+1})` and `d(O_{k+2}, A_{k+1} A'_{k+1})`
have the same law, and so do `d(O_{k-1}, A_k A_{k+1})` and `d(O_{k-1}, A_k A'_k)`. -/
theorem cor6 {r : ℝ} (hr : 0 < r) (x : ℤ → ℝ) (hx : ∀ k, x (k + 1) = x k + r ^ k + r ^ (k + 1))
    (k : ℤ) :
    Measure.map (fun ω : Ang × Ang =>
        lineDist (x (k + 2), 0) (pt (x k) (r ^ k) ω.1) (pt (x (k + 1)) (r ^ (k + 1)) ω.2)) volume =
      Measure.map (fun ω : Ang × Ang =>
        lineDist (x (k + 2), 0) (pt (x (k + 1)) (r ^ (k + 1)) ω.1)
          (pt (x (k + 1)) (r ^ (k + 1)) ω.2)) volume ∧
    Measure.map (fun ω : Ang × Ang =>
        lineDist (x (k - 1), 0) (pt (x k) (r ^ k) ω.1) (pt (x (k + 1)) (r ^ (k + 1)) ω.2)) volume =
      Measure.map (fun ω : Ang × Ang =>
        lineDist (x (k - 1), 0) (pt (x k) (r ^ k) ω.1) (pt (x k) (r ^ k) ω.2)) volume := by
  have hk0 : 0 < r ^ k := zpow_pos hr k
  have hk1 : 0 < r ^ (k + 1) := zpow_pos hr (k + 1)
  have hz1 : r ^ (k + 1) = r ^ k * r := by rw [zpow_add_one₀ hr.ne']
  have hz2 : r ^ (k + 2) = r ^ k * r * r := by
    rw [show k + 2 = k + 1 + 1 by ring, zpow_add_one₀ hr.ne', zpow_add_one₀ hr.ne']
  have hzm : r ^ k = r ^ (k - 1) * r := by
    rw [← zpow_add_one₀ hr.ne', sub_add_cancel]
  have e1 : x (k + 1) - (r ^ k + r ^ (k + 1)) = x k := by rw [hx k]; ring
  have e3 : x (k + 1) + (r ^ (k + 1) + r ^ (k + 2)) = x (k + 2) := by
    rw [show k + 2 = k + 1 + 1 by ring, hx (k + 1)]; ring
  have e2 : x k - (r ^ (k - 1) + r ^ k) = x (k - 1) := by
    have := hx (k - 1); rw [sub_add_cancel] at this; linarith
  constructor
  · have h := (theorem4 hk0 hk1 le_rfl (x (k + 1)) (r ^ (k + 1) + r ^ (k + 2))).2 (Or.inr ⟨rfl, by
      rw [hz2, hz1]; field_simp⟩)
    unfold dAB dBC at h
    simp only [e1, e3] at h
    exact h
  · have h := (theorem4_mirror hk0 hk1 le_rfl (x (k + 1)) (r ^ (k - 1) + r ^ k)).2 (Or.inr ⟨rfl, by
      rw [hz1, hzm]; field_simp⟩)
    unfold dAB' dAA at h
    simp only [e1, e2] at h
    exact h

end Chords
