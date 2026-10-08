/-
  The residue classes of Section 4, in the paper's form: each class is an inflation `(u, v)` of the
  squared square of side 112 or 110 with a threshold `t₀`. A boolean check of the hypotheses of
  Lemma 4 at `t₀` gives, through `all_scales`, an admissible tiling of `R_{tS + v(S)}` for every
  `t ≥ t₀`. The data are in Inflations.lean.
-/
import AlmostSquares.Scales

namespace AlmostSq

/-- A shift given by its nonzero values. -/
def tab (L : List (ℤ × ℤ)) (a : ℤ) : ℤ := (L.lookup a).getD 0

/-- One class: an inflation `(u, v)` of the squared square of side `S`, with `v(S) = V`, valid
    from the scale `t₀`. -/
structure Infl where
  S : ℤ
  V : ℤ
  t0 : ℤ
  u : List (ℤ × ℤ)
  v : List (ℤ × ℤ)

/-- The squared square of side `S` (112 or 110). -/
def base (S : ℤ) : List Tile := if S = 112 then sq112 else sq110

theorem base_perfect {S : ℤ} (h : S = 112 ∨ S = 110) : PerfectSquaredSquare S (base S) := by
  rcases h with rfl | rfl
  · exact sq112_perfect
  · exact sq110_perfect

/-- All vertical cut lines, with repetitions. -/
def cutXs (S : ℤ) (ts : List Tile) : List ℤ := 0 :: S :: ts.flatMap (fun T => [T.x, T.x + T.w])

/-- All horizontal cut lines, with repetitions. -/
def cutYs (S : ℤ) (ts : List Tile) : List ℤ := 0 :: S :: ts.flatMap (fun T => [T.y, T.y + T.h])

theorem mem_cutXs {S : ℤ} {ts : List Tile} {a : ℤ} (h : a ∈ CutX S ts) : a ∈ cutXs S ts := by
  rcases h with rfl | rfl | ⟨T, hT, rfl | rfl⟩
  · simp [cutXs]
  · simp [cutXs]
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨T, hT, by simp⟩))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨T, hT, by simp⟩))

theorem mem_cutYs {S : ℤ} {ts : List Tile} {b : ℤ} (h : b ∈ CutY S ts) : b ∈ cutYs S ts := by
  rcases h with rfl | rfl | ⟨T, hT, rfl | rfl⟩
  · simp [cutYs]
  · simp [cutYs]
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨T, hT, by simp⟩))
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨T, hT, by simp⟩))

/-- `f` is strictly increasing on the list `L`. -/
def monoOn (f : ℤ → ℤ) (L : List ℤ) : Bool :=
  L.all fun a => L.all fun b => !decide (a < b) || decide (f a < f b)

theorem monoOn_sound {f : ℤ → ℤ} {L : List ℤ} {s : Set ℤ} (hs : ∀ a ∈ s, a ∈ L)
    (h : monoOn f L = true) : StrictMonoOn f s := by
  intro a ha b hb hab
  have := List.all_eq_true.mp (List.all_eq_true.mp h a (hs a ha)) b (hs b hb)
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at this
  tauto

/-- No integer collision point of squares `T` and `U` is at least `t₀`. -/
def colOK (t0 : ℤ) (u v : ℤ → ℤ) (T U : Tile) : Bool :=
  decide (T.w = U.w) || decide ((cmin u v U - cmin u v T) % (T.w - U.w) ≠ 0) ||
    decide ((cmin u v U - cmin u v T) / (T.w - U.w) < t0)

theorem colOK_sound {t0 : ℤ} {u v : ℤ → ℤ} {T U : Tile} (h : colOK t0 u v T U = true)
    (hw : T.w ≠ U.w) (t : ℤ) (he : t * T.w + cmin u v T = t * U.w + cmin u v U) : t < t0 := by
  have hd : T.w - U.w ≠ 0 := sub_ne_zero.mpr hw
  have he' : cmin u v U - cmin u v T = t * (T.w - U.w) := by linarith
  simp only [colOK, Bool.or_eq_true, decide_eq_true_eq] at h
  rw [he'] at h
  rcases h with (h | h) | h
  · exact absurd h hw
  · exact absurd (Int.mul_emod_left t _) h
  · rwa [Int.mul_ediv_cancel t hd] at h

/-- The hypotheses of Lemma 4 for one class, as a boolean. -/
def inflOK (I : Infl) : Bool :=
  decide (I.S = 112 ∨ I.S = 110) && decide (tab I.u 0 = 0) && decide (tab I.v 0 = 0) &&
    decide (tab I.u I.S - tab I.v I.S = 1) && decide (tab I.v I.S = I.V) &&
    (base I.S).all (fun T => decide (eps (tab I.u) (tab I.v) T = 1 ∨ eps (tab I.u) (tab I.v) T = -1)) &&
    monoOn (scaleShift I.t0 (tab I.u)) (cutXs I.S (base I.S)) &&
    monoOn (scaleShift I.t0 (tab I.v)) (cutYs I.S (base I.S)) &&
    (base I.S).all (fun T => decide (1 ≤ I.t0 * T.w + cmin (tab I.u) (tab I.v) T ∧
      I.t0 * T.w + cmin (tab I.u) (tab I.v) T < I.t0 * I.S + tab I.v I.S)) &&
    (base I.S).all (fun T => (base I.S).all (fun U => colOK I.t0 (tab I.u) (tab I.v) T U))

/-- A checked class tiles `R_{tS + V}` for every `t ≥ t₀`, by Lemma 4. -/
theorem inflOK_sound {I : Infl} (hI : inflOK I = true) {t : ℤ} (ht : I.t0 ≤ t) :
    Admissible (t * I.S + I.V).toNat
      ((base I.S).map (img (scaleShift t (tab I.u)) (scaleShift t (tab I.v)))) := by
  simp only [inflOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hI
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hS, hu0⟩, hv0⟩, hc⟩, hV⟩, he⟩, hX⟩, hY⟩, hb⟩, hcol⟩ := hI
  have hpos : 0 < I.S := by omega
  rw [← hV]
  exact all_scales hpos (base_perfect hS) ⟨hu0, hv0, hc, he⟩
    (monoOn_sound (fun _ => mem_cutXs) hX) (monoOn_sound (fun _ => mem_cutYs) hY)
    (fun T hT => (hb T hT).1) (fun T hT => (hb T hT).2)
    (fun T hT U hU hw => colOK_sound (hcol T hT U hU) hw) ht

end AlmostSq
