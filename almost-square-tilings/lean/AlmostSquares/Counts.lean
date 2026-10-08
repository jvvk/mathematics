/-
  The descriptive numbers of Sections 4 and 5 of the paper, checked: Table 2 (sets of sizes with the
  right area), the coverage counts of Section 4 (151 values left to explicit tilings, every n ≥ 249
  reached by the classes, t₀ ≤ 3, first n ≤ 360, one class per residue, 21 or 22 pieces, the shading
  of Figure 7), and a checker for inflating a squared rectangle at one fixed scale, used in Reach.lean
  for the 57 × 55 rectangle and for Moroń's rectangle.
-/
import AlmostSquares.Main
import AlmostSquares.Bouwkamp

namespace AlmostSq

/-! ### Table 2 -/

/-- The number of subsets of `{1, …, k}` whose `f`-values add up to `t`. -/
def cnt (f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, t => if t = 0 then 1 else 0
  | k + 1, t => cnt f k t + (if f (k + 1) ≤ t then cnt f k (t - f (k + 1)) else 0)

theorem Icc_succ (k : ℕ) : Finset.Icc 1 (k + 1) = insert (k + 1) (Finset.Icc 1 k) := by
  ext a; simp only [Finset.mem_Icc, Finset.mem_insert]; omega

/-- `cnt` really counts subsets. -/
theorem cnt_eq (f : ℕ → ℕ) : ∀ k t,
    cnt f k t = ((Finset.Icc 1 k).powerset.filter (fun s => s.sum f = t)).card
  | 0, t => by
    rw [Finset.Icc_eq_empty_of_lt (by norm_num), Finset.powerset_empty, Finset.filter_singleton]
    by_cases ht : t = 0
    · subst ht; simp [cnt]
    · simp [cnt, ht, Ne.symm ht]
  | k + 1, t => by
    have hk : k + 1 ∉ Finset.Icc 1 k := by simp
    have e : ∀ x ∈ (Finset.Icc 1 k).powerset, (insert (k + 1) x).sum f = f (k + 1) + x.sum f :=
      fun x hx => Finset.sum_insert (fun h => hk (Finset.mem_powerset.mp hx h))
    rw [Icc_succ, Finset.powerset_insert, Finset.filter_union, Finset.card_union_of_disjoint]
    · rw [cnt, cnt_eq f k t, Finset.filter_image, Finset.card_image_of_injOn]
      · congr 1
        try simp only [Function.comp_def]
        rw [Finset.filter_congr (fun x hx => by rw [e x hx])]
        split_ifs with h
        · rw [cnt_eq f k (t - f (k + 1))]
          congr 1; ext x; simp only [Finset.mem_filter]; constructor <;> rintro ⟨h1, h2⟩ <;>
            exact ⟨h1, by omega⟩
        · symm; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro x _ hx; omega
      · intro x hx y hy hxy
        have hx' : k + 1 ∉ x := fun h =>
          hk (Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1 h)
        have hy' : k + 1 ∉ y := fun h =>
          hk (Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).1 h)
        have hxy' : insert (k + 1) x = insert (k + 1) y := hxy
        rw [← Finset.erase_insert hx', ← Finset.erase_insert hy', hxy']
    · rw [Finset.disjoint_left]
      intro x hx hx2
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hx2).1
      exact hk (Finset.mem_powerset.mp (Finset.mem_filter.mp hx).1 (Finset.mem_insert_self _ _))

/-- Sets of distinct sizes below `n` whose almost-squares have total area `n (n+1)`. -/
def areaSets (n : ℕ) : ℕ := cnt (fun k => k * (k + 1)) (n - 1) (n * (n + 1))

theorem areaSets_eq (n : ℕ) : areaSets n =
    ((Finset.Icc 1 (n - 1)).powerset.filter (fun s => s.sum (fun k => k * (k + 1)) = n * (n + 1))).card :=
  cnt_eq _ _ _

/-- **Table 2**, the "area sets" row, for `n = 2, …, 19`. -/
theorem table2 : (List.range' 2 18).map areaSets =
    [0, 0, 1, 0, 1, 2, 1, 3, 6, 5, 3, 13, 14, 18, 30, 27, 42, 56] := by decide +kernel

/-! ### Section 4 counts -/

/-- For each even residue mod 112 and each odd residue mod 110 there is a class with `t₀ ≤ 3`
    whose first `n` is at most 360 (two spare classes have `t₀ = 4`). -/
theorem thresholds :
    (∀ r : ℕ, r < 112 → r % 2 = 0 → inflations.any (fun I => decide (I.S = 112 ∧
      (I.V - (r : ℤ)) % 112 = 0 ∧ I.t0 ≤ 3 ∧ I.t0 * I.S + I.V ≤ 360)) = true) ∧
    (∀ r : ℕ, r < 110 → r % 2 = 1 → inflations.any (fun I => decide (I.S = 110 ∧
      (I.V - (r : ℤ)) % 110 = 0 ∧ I.t0 ≤ 3 ∧ I.t0 * I.S + I.V ≤ 360)) = true) ∧
    (inflations.filter (fun I => decide (3 < I.t0))).length = 2 := by
  decide +kernel

/-- One class for each of the 56 even residues mod 112 and the 55 odd residues mod 110. -/
theorem residues :
    ((inflations.filter (fun I => I.S == 112)).map (fun I => I.V % 112)).dedup.length = 56 ∧
    ((inflations.filter (fun I => I.S == 110)).map (fun I => I.V % 110)).dedup.length = 55 ∧
    inflations.all (fun I => decide ((I.S = 112 ∧ I.V % 2 = 0) ∨ (I.S = 110 ∧ I.V % 2 = 1))) = true := by
  decide +kernel

/-- The inflations use 21 pieces (side 112) or 22 pieces (side 110). -/
theorem pieces : (base 112).length = 21 ∧ (base 110).length = 22 := by decide +kernel

/-- `n` is reached by some class. -/
def byClass (n : ℕ) : Bool := inflations.any (inflCovers n)

/-- Every `n ≥ 249` is reached by a class. -/
theorem byClass_above (n : ℕ) (hn : 249 ≤ n) : byClass n = true := by
  rcases Nat.lt_or_ge n 600 with h | h
  · have : ∀ m < 600, 249 ≤ m → byClass m = true := by decide +kernel
    exact this n h hn
  · simp only [byClass, List.any_eq_true]
    rcases Nat.mod_two_eq_zero_or_one n with hp | hp
    · obtain ⟨I, hm, hF⟩ := List.any_eq_true.mp (resid112 (n % 112) (Nat.mod_lt n (by norm_num))
        (by omega))
      obtain ⟨hS, hr, hb⟩ := of_decide_eq_true hF
      exact ⟨I, hm, decide_eq_true (by rw [hS]; omega)⟩
    · obtain ⟨I, hm, hF⟩ := List.any_eq_true.mp (resid110 (n % 110) (Nat.mod_lt n (by norm_num))
        (by omega))
      obtain ⟨hS, hr, hb⟩ := of_decide_eq_true hF
      exact ⟨I, hm, decide_eq_true (by rw [hS]; omega)⟩

/-- The values in `[20, 248]` not reached by any class. -/
def uncovered : List ℕ := (List.range' 20 229).filter (fun n => !byClass n)

/-- Exactly 151 values are left, and each has an explicit tiling. -/
theorem uncovered_count : uncovered.length = 151 ∧
    uncovered.all (fun n => (explicit.map Prod.fst).contains n) = true := by decide +kernel

/-- Figure 7: below 260, the classes of side 112 reach only even `n` and those of side 110 only odd
    `n`; everything else in `[20, 260)` has an explicit tiling. -/
theorem figure7 : (List.range' 20 240).all (fun n =>
    inflations.all (fun I => !inflCovers n I || decide ((I.S = 112 ∧ n % 2 = 0) ∨ (I.S = 110 ∧ n % 2 = 1))) &&
    (byClass n || (explicit.map Prod.fst).contains n)) = true := by decide +kernel

/-! ### Inflating a squared rectangle at one fixed scale -/

/-- Reflection in the diagonal. -/
def Tile.swap (T : Tile) : Tile := ⟨T.y, T.x, T.h, T.w⟩

/-- The hypotheses of the inflation lemma for a squared rectangle `W × H` at scale `t`, with the
    result the almost-square `R_n`. -/
def rectOK (W H : ℤ) (ts : List Tile) (t : ℤ) (u v : ℤ → ℤ) (n : ℕ) : Bool :=
  dissectsCheck W H ts && ts.all (fun T => decide (T.w = T.h)) && decide (0 ≤ W ∧ 0 ≤ H) &&
    decide (u 0 = 0 ∧ v 0 = 0 ∧ t * W + u W = (n : ℤ) + 1 ∧ t * H + v H = n) &&
    monoOn (scaleShift t u) (cutXs W ts) && monoOn (scaleShift t v) (cutYs H ts) &&
    ts.all (fun T => decide ((eps u v T = 1 ∨ eps u v T = -1) ∧ 1 ≤ t * T.w + cmin u v T ∧
      t * T.w + cmin u v T < n)) &&
    decide ((ts.map (fun T => t * T.w + cmin u v T)).Nodup)

/-- A checked rectangle inflation is an admissible tiling of `R_n`. -/
theorem rectOK_sound {W H : ℤ} {ts : List Tile} {t : ℤ} {u v : ℤ → ℤ} {n : ℕ}
    (h : rectOK W H ts t u v n = true) :
    Admissible n (ts.map (img (scaleShift t u) (scaleShift t v))) := by
  simp only [rectOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hd, hsq⟩, hW, hH⟩, hu0, hv0, hX, hY⟩, hmx⟩, hmy⟩, hT⟩, hnd⟩ := h
  have hD := dissectsCheck_sound hW hH hd
  have hcx : ∀ a ∈ CutX W ts, a ∈ cutXs W ts := fun _ ha => by
    rcases ha with rfl | rfl | ⟨T, hT, rfl | rfl⟩
    · simp [cutXs]
    · simp [cutXs]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨T, hT, by simp⟩))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨T, hT, by simp⟩))
  have hcy : ∀ b ∈ CutY H ts, b ∈ cutYs H ts := fun _ hb => by
    rcases hb with rfl | rfl | ⟨T, hT, rfl | rfl⟩
    · simp [cutYs]
    · simp [cutYs]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨T, hT, by simp⟩))
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨T, hT, by simp⟩))
  obtain ⟨hI, halm⟩ := inflation hW hH hD t u v hu0 hv0 (monoOn_sound hcx hmx) (monoOn_sound hcy hmy)
  have hsize : ∀ T ∈ ts, (img (scaleShift t u) (scaleShift t v) T).size = t * T.w + cmin u v T :=
    fun T hT' => (halm T hT' (hsq T hT') (hT T hT').1).2
  have hbox : box (t * W + u W) (t * H + v H) = rect n := by
    simp only [box, rect, hX, hY]
  refine ⟨?_, ?_, ?_, ?_, by rw [← hbox]; exact hI.inside, by rw [← hbox]; exact hI.cover⟩
  · intro T' hT'
    obtain ⟨T, hm, rfl⟩ := List.mem_map.mp hT'
    exact (halm T hm (hsq T hm) (hT T hm).1).1
  · intro T' hT'
    obtain ⟨T, hm, rfl⟩ := List.mem_map.mp hT'
    rw [hsize T hm]; exact (hT T hm).2.1
  · intro T' hT'
    obtain ⟨T, hm, rfl⟩ := List.mem_map.mp hT'
    rw [hsize T hm]; exact (hT T hm).2.2
  · have e : ts.map (Tile.size ∘ img (scaleShift t u) (scaleShift t v)) =
        ts.map (fun T => t * T.w + cmin u v T) := List.map_congr_left (fun T hm => hsize T hm)
    rw [List.map_map, e]
    exact hnd

end AlmostSq
