/-
  Lemma 4 of the paper (all large scales), in the paper's form: an inflation of a perfect squared
  square whose hypotheses hold at a threshold `t₀`, with `t₀` beyond every integer collision point,
  gives an admissible tiling of `R_{tS + v(S)}` for every `t ≥ t₀`.
-/
import AlmostSquares.Parity

namespace AlmostSq

/-- `c_i = min(δu_i, δv_i)`: the size of square `T` at scale `t` is `t s + c`. -/
def cmin (u v : ℤ → ℤ) (T : Tile) : ℤ := min (u (T.x + T.w) - u T.x) (v (T.y + T.h) - v T.y)

/-- Strict monotonicity on the cut lines at `t₀` persists for every `t ≥ t₀`. -/
theorem strictMonoOn_scale {s : Set ℤ} {u : ℤ → ℤ} {t0 t : ℤ} (ht : t0 ≤ t)
    (h : StrictMonoOn (scaleShift t0 u) s) : StrictMonoOn (scaleShift t u) s := by
  intro a ha b hb hab
  have := h ha hb hab
  simp only [scaleShift] at this ⊢
  nlinarith

/-- **Lemma 4 (All large scales).** -/
theorem all_scales {S : ℤ} (hS : 0 < S) {ts : List Tile} (hp : PerfectSquaredSquare S ts)
    {u v : ℤ → ℤ} (hi : IsInflation S ts u v) {t0 : ℤ}
    (hX : StrictMonoOn (scaleShift t0 u) (CutX S ts))
    (hY : StrictMonoOn (scaleShift t0 v) (CutY S ts))
    (hpos : ∀ T ∈ ts, 1 ≤ t0 * T.w + cmin u v T)
    (hlt : ∀ T ∈ ts, t0 * T.w + cmin u v T < t0 * S + v S)
    (hcol : ∀ T ∈ ts, ∀ U ∈ ts, T.w ≠ U.w →
      ∀ t : ℤ, t * T.w + cmin u v T = t * U.w + cmin u v U → t < t0)
    {t : ℤ} (ht : t0 ≤ t) :
    Admissible (t * S + v S).toNat (ts.map (img (scaleShift t u) (scaleShift t v))) := by
  obtain ⟨hd, hsq, hnd⟩ := hp
  obtain ⟨hD, halm⟩ := inflation hS.le hS.le hd t u v hi.u0 hi.v0
    (strictMonoOn_scale ht hX) (strictMonoOn_scale ht hY)
  -- Sizes at scale `t`.
  have hsize : ∀ T ∈ ts, (img (scaleShift t u) (scaleShift t v) T).size = t * T.w + cmin u v T :=
    fun T hT => (halm T hT (hsq T hT) (hi.eps T hT)).2
  have hwS : ∀ T ∈ ts, 0 < T.w ∧ T.w ≤ S := fun T hT => by
    have := hd.bounds hT; have := hd.pos T hT; omega
  have spos : ∀ T ∈ ts, 1 ≤ t * T.w + cmin u v T := fun T hT => by
    have := hpos T hT; have := hwS T hT; nlinarith
  have slt : ∀ T ∈ ts, t * T.w + cmin u v T < t * S + v S := fun T hT => by
    have := hlt T hT; have := hwS T hT; nlinarith
  -- `n = tS + v(S)` is positive: the cell `(0, 0)` lies in some square.
  have hn : 0 ≤ t * S + v S := by
    have h0 : ((0 : ℤ), (0 : ℤ)) ∈ box S S := by simp [box, hS]
    have hc := hd.cover _ h0
    obtain ⟨T, hT⟩ : ∃ T, T ∈ ts.filter (fun T => ((0 : ℤ), (0 : ℤ)) ∈ T.cells) := by
      rcases hl : ts.filter (fun T => ((0 : ℤ), (0 : ℤ)) ∈ T.cells) with _ | ⟨T, _⟩
      · rw [hl] at hc; simp at hc
      · exact ⟨T, by rw [hl]; exact List.mem_cons_self ..⟩
    have hT' := (List.mem_filter.mp hT).1
    have := spos T hT'; have := slt T hT'; omega
  have hN : (((t * S + v S).toNat : ℕ) : ℤ) = t * S + v S := Int.toNat_of_nonneg hn
  have hbox : box (t * S + u S) (t * S + v S) = rect (t * S + v S).toNat := by
    have hc := hi.corner
    simp only [box, rect, hN]
    congr 2; omega
  refine ⟨?_, ?_, ?_, ?_, by rw [← hbox]; exact hD.inside, by rw [← hbox]; exact hD.cover⟩
  · intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hT'
    exact (halm T hT (hsq T hT) (hi.eps T hT)).1
  · intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hT'
    rw [hsize T hT]; exact spos T hT
  · intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hT'
    rw [hsize T hT, hN]; exact slt T hT
  · rw [List.map_map]
    have hnd' : ts.Nodup := List.Nodup.of_map _ hnd
    refine List.Nodup.map_on (fun T hT U hU he => ?_) hnd'
    simp only [Function.comp] at he
    rw [hsize T hT, hsize U hU] at he
    by_cases hw : T.w = U.w
    · exact List.inj_on_of_nodup_map hnd hT hU hw
    · exact absurd (hcol T hT U hU hw t he) (not_lt.mpr ht)

end AlmostSq
