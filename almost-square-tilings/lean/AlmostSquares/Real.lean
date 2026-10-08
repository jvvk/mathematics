/-
  Lemma 8 of the paper (integer corners) and Theorem 1 for tilings by real rectangles.

  A real tiling of `[0,W] × [0,H]` is a finite list of closed rectangles with real corners and positive
  integer sides whose union is the rectangle and whose interiors are pairwise disjoint. Lemma 8 says
  every corner is then an integer point, so such a tiling is the same thing as a unit-cell tiling
  (`Admissible`, Basic.lean), and Theorem 1 transfers.
-/
import AlmostSquares.Final
import AlmostSquares.Inflation

namespace AlmostSq

open Classical

/-- A closed rectangle with real lower-left corner `(x, y)` and integer width `w` and height `h`. -/
structure RTile where
  x : ℝ
  y : ℝ
  w : ℕ
  h : ℕ

namespace RTile

def closed (T : RTile) : Set (ℝ × ℝ) := Set.Icc T.x (T.x + T.w) ×ˢ Set.Icc T.y (T.y + T.h)

def inner (T : RTile) : Set (ℝ × ℝ) := Set.Ioo T.x (T.x + T.w) ×ˢ Set.Ioo T.y (T.y + T.h)

/-- Reflection in the diagonal. -/
def swap (T : RTile) : RTile := ⟨T.y, T.x, T.h, T.w⟩

end RTile

/-- `ts` tiles `[0,W] × [0,H]`: positive sides, union equal to the rectangle, disjoint interiors. -/
structure RTiles (W H : ℝ) (ts : List RTile) : Prop where
  pos : ∀ T ∈ ts, 0 < T.w ∧ 0 < T.h
  union : ∀ p : ℝ × ℝ, (0 ≤ p.1 ∧ p.1 ≤ W ∧ 0 ≤ p.2 ∧ p.2 ≤ H) ↔ ∃ T ∈ ts, p ∈ T.closed
  disj : ts.Pairwise (fun T U => Disjoint T.inner U.inner)

def IsInt (r : ℝ) : Prop := ∃ m : ℤ, r = m

theorem isInt_add_nat {r : ℝ} (h : IsInt r) (k : ℕ) : IsInt (r + k) := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨m + k, by push_cast; ring⟩

theorem RTiles.bounds {W H : ℝ} {ts : List RTile} (ht : RTiles W H ts) {T : RTile} (hT : T ∈ ts) :
    0 ≤ T.x ∧ T.x + T.w ≤ W ∧ 0 ≤ T.y ∧ T.y + T.h ≤ H := by
  have h1 := (ht.union (T.x, T.y)).mpr ⟨T, hT, by
    simp only [RTile.closed, Set.mem_prod, Set.mem_Icc]; refine ⟨⟨le_rfl, ?_⟩, le_rfl, ?_⟩ <;>
      simp⟩
  have h2 := (ht.union (T.x + T.w, T.y + T.h)).mpr ⟨T, hT, by
    simp only [RTile.closed, Set.mem_prod, Set.mem_Icc]; refine ⟨⟨?_, le_rfl⟩, ?_, le_rfl⟩ <;>
      simp⟩
  exact ⟨h1.1, h2.2.1, h1.2.2.1, h2.2.2.2⟩

/-- **Lemma 8 (Integer corners), for `x`-coordinates.** -/
theorem left_isInt {W H : ℝ} {ts : List RTile} (ht : RTiles W H ts) : ∀ T ∈ ts, IsInt T.x := by
  by_contra hne
  push Not at hne
  obtain ⟨T0, hT0, hT0x⟩ := hne
  -- The finite set of vertical sides, and its least non-integer element `a`.
  set A : Finset ℝ := (ts.map RTile.x).toFinset ∪ (ts.map (fun T : RTile => T.x + (T.w : ℝ))).toFinset with hA
  have memL : ∀ T ∈ ts, T.x ∈ A := fun T hT => by simp [hA]; exact Or.inl ⟨T, hT, rfl⟩
  have memR : ∀ T ∈ ts, T.x + T.w ∈ A := fun T hT => by simp [hA]; exact Or.inr ⟨T, hT, rfl⟩
  have memA : ∀ r ∈ A, ∃ T ∈ ts, r = T.x ∨ r = T.x + T.w := by
    intro r hr
    simp only [hA, Finset.mem_union, List.mem_toFinset, List.mem_map] at hr
    rcases hr with ⟨T, hT, rfl⟩ | ⟨T, hT, rfl⟩
    · exact ⟨T, hT, Or.inl rfl⟩
    · exact ⟨T, hT, Or.inr rfl⟩
  set N := A.filter (fun r => ¬ IsInt r) with hN
  have hNne : N.Nonempty := ⟨T0.x, by simp [hN, memL T0 hT0, hT0x]⟩
  set a := N.min' hNne with ha
  have haN : a ∈ N := N.min'_mem hNne
  have haA : a ∈ A := (Finset.mem_filter.mp haN).1
  have haI : ¬ IsInt a := (Finset.mem_filter.mp haN).2
  have below : ∀ r ∈ A, r < a → IsInt r := by
    intro r hr hlt
    by_contra hri
    have : a ≤ r := N.min'_le r (by simp [hN, hr, hri])
    linarith
  -- `a` is the left side of a tile `P`.
  obtain ⟨P, hP, hPa⟩ : ∃ P ∈ ts, P.x = a := by
    obtain ⟨Q, hQ, hQa | hQa⟩ := memA a haA
    · exact ⟨Q, hQ, hQa.symm⟩
    · exfalso
      have hpos : (0 : ℝ) < Q.w := by exact_mod_cast (ht.pos Q hQ).1
      exact haI (hQa ▸ isInt_add_nat (below Q.x (memL Q hQ) (by linarith)) Q.w)
  have hPb := ht.bounds hP
  have hPw : (0 : ℝ) < P.w := by exact_mod_cast (ht.pos P hP).1
  have hPh : (0 : ℝ) < P.h := by exact_mod_cast (ht.pos P hP).2
  have ha0 : 0 < a := by
    rcases (hPa ▸ hPb.1 : 0 ≤ a).lt_or_eq with h | h
    · exact h
    · exact absurd ⟨0, by rw [← h]; simp⟩ haI
  -- `c`: the largest element of `A ∪ {0}` below `a`.
  set B := insert (0 : ℝ) (A.filter (· < a)) with hB
  have hBne : B.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  set c := B.max' hBne with hc
  have hcB : c ∈ B := B.max'_mem hBne
  have hc0 : 0 ≤ c := B.le_max' 0 (Finset.mem_insert_self _ _)
  have hca : c < a := by
    rcases Finset.mem_insert.mp hcB with h | h
    · rw [h]; exact ha0
    · exact (Finset.mem_filter.mp h).2
  have gap : ∀ r ∈ A, r < a → r ≤ c := fun r hr hlt =>
    B.le_max' r (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hr, hlt⟩))
  -- A height `y0` inside `P` on no horizontal side.
  set Ys : Set ℝ := {y : ℝ | ∃ T ∈ ts, y = T.y ∨ y = T.y + (T.h : ℝ)} with hYs
  have hYsf : Ys.Finite := by
    have : Ys = ((ts.map RTile.y) ++ (ts.map (fun T : RTile => T.y + (T.h : ℝ)))).toFinset := by
      ext y; simp only [hYs, Set.mem_ofPred_eq, List.coe_toFinset, List.mem_append, List.mem_map]
      constructor
      · rintro ⟨T, hT, rfl | rfl⟩
        · exact Or.inl ⟨T, hT, rfl⟩
        · exact Or.inr ⟨T, hT, rfl⟩
      · rintro (⟨T, hT, rfl⟩ | ⟨T, hT, rfl⟩)
        · exact ⟨T, hT, Or.inl rfl⟩
        · exact ⟨T, hT, Or.inr rfl⟩
    rw [this]; exact Finset.finite_toSet _
  obtain ⟨y0, hy0I, hy0Y⟩ : ∃ y0 ∈ Set.Ioo P.y (P.y + P.h), y0 ∉ Ys :=
    ((Set.Ioo_infinite (by linarith)).sdiff hYsf).nonempty
  obtain ⟨hy0a, hy0b⟩ := hy0I
  -- The tile `P'` covering the point midway between `c` and `a`.
  obtain ⟨P', hP', hpt⟩ := (ht.union ((c + a) / 2, y0)).mp
    ⟨by linarith, by linarith [hPb.2.1], by linarith [hPb.2.2.1], by linarith [hPb.2.2.2]⟩
  simp only [RTile.closed, Set.mem_prod, Set.mem_Icc] at hpt
  obtain ⟨⟨hl, hr⟩, hy1, hy2⟩ := hpt
  have hlc : P'.x ≤ c := gap _ (memL P' hP') (by linarith)
  have hra : a ≤ P'.x + P'.w := by
    by_contra h
    push Not at h
    have := gap _ (memR P' hP') h
    linarith
  rcases hra.lt_or_eq with hgt | heq
  · -- `P'` would overlap `P` just to the right of `(a, y0)`.
    exfalso
    have hne : P ≠ P' := by
      intro h; rw [← h] at hlc; linarith
    have : Std.Symm (fun T U : RTile => Disjoint T.inner U.inner) := ⟨fun _ _ h => h.symm⟩
    have hdisj : Disjoint P.inner P'.inner := ht.disj.forall hP hP' hne
    set d := min (P'.x + P'.w - a) P.w / 2 with hd
    have hd0 : 0 < d := by
      rw [hd]; apply div_pos (lt_min (by linarith) hPw) two_pos
    have hd1 : d < P'.x + P'.w - a := by
      have := min_le_left (P'.x + P'.w - a) (P.w : ℝ); rw [hd]; linarith
    have hd2 : d < P.w := by
      have := min_le_right (P'.x + P'.w - a) (P.w : ℝ); rw [hd]; linarith
    have hy1' : P'.y < y0 := lt_of_le_of_ne hy1 (fun h => hy0Y ⟨P', hP', Or.inl h.symm⟩)
    have hy2' : y0 < P'.y + P'.h := lt_of_le_of_ne hy2 (fun h => hy0Y ⟨P', hP', Or.inr h⟩)
    refine Set.disjoint_left.mp hdisj (?_ : (a + d, y0) ∈ P.inner) ?_
    · simp only [RTile.inner, Set.mem_prod, Set.mem_Ioo]
      exact ⟨⟨by linarith, by linarith⟩, hy0a, hy0b⟩
    · simp only [RTile.inner, Set.mem_prod, Set.mem_Ioo]
      exact ⟨⟨by linarith, by linarith⟩, hy1', hy2'⟩
  · -- `P'` ends exactly at `a`, so `a` is an integer.
    have hl' := below _ (memL P' hP') (by linarith)
    exact haI (heq ▸ isInt_add_nat hl' P'.w)

theorem RTiles.swap {W H : ℝ} {ts : List RTile} (ht : RTiles W H ts) :
    RTiles H W (ts.map RTile.swap) := by
  refine ⟨fun T hT => ?_, fun p => ?_, ?_⟩
  · obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hT
    exact ⟨(ht.pos U hU).2, (ht.pos U hU).1⟩
  · have := ht.union (p.2, p.1)
    simp only [List.mem_map, exists_exists_and_eq_and, RTile.swap, RTile.closed, Set.mem_prod,
      Set.mem_Icc] at this ⊢
    constructor
    · intro h
      obtain ⟨T, hT, h1, h2⟩ := this.mp ⟨h.2.2.1, h.2.2.2, h.1, h.2.1⟩
      exact ⟨T, hT, h2, h1⟩
    · rintro ⟨T, hT, h1, h2⟩
      have := this.mpr ⟨T, hT, h2, h1⟩
      exact ⟨this.2.2.1, this.2.2.2, this.1, this.2.1⟩
  · refine List.pairwise_map.mpr (ht.disj.imp fun {T U} h => ?_)
    rw [Set.disjoint_left] at h ⊢
    intro p hpT hpU
    simp only [RTile.swap, RTile.inner, Set.mem_prod] at hpT hpU
    exact h (a := (p.2, p.1)) (by simp only [RTile.inner, Set.mem_prod]; exact ⟨hpT.2, hpT.1⟩)
      (by simp only [RTile.inner, Set.mem_prod]; exact ⟨hpU.2, hpU.1⟩)

/-- **Lemma 8 (Integer corners).** In a tiling of a rectangle by finitely many closed rectangles with
    integer side lengths and disjoint interiors, every corner is an integer point. -/
theorem integer_corners {W H : ℝ} {ts : List RTile} (ht : RTiles W H ts) :
    ∀ T ∈ ts, IsInt T.x ∧ IsInt T.y := fun T hT =>
  ⟨left_isInt ht T hT, left_isInt ht.swap T.swap (List.mem_map_of_mem hT)⟩

/-! ### Theorem 1 for real tilings -/

/-- An admissible tiling of `R_n = [0, n+1] × [0, n]` by real rectangles: almost-squares of distinct
    sizes `1 ≤ k < n`, union `R_n`, disjoint interiors. -/
structure RAdmissible (n : ℕ) (ts : List RTile) : Prop where
  tiles : RTiles ((n : ℝ) + 1) n ts
  almost : ∀ T ∈ ts, T.w = T.h + 1 ∨ T.h = T.w + 1
  size_pos : ∀ T ∈ ts, 1 ≤ min T.w T.h
  size_lt : ∀ T ∈ ts, min T.w T.h < n
  distinct : (ts.map (fun T => min T.w T.h)).Nodup

/-- Integer tile from a real tile with integer corners. -/
noncomputable def RTile.toTile (T : RTile) : Tile := ⟨⌊T.x⌋, ⌊T.y⌋, T.w, T.h⟩

def Tile.toR (T : Tile) : RTile := ⟨T.x, T.y, T.w.toNat, T.h.toNat⟩

theorem floor_eq_of_isInt {r : ℝ} (h : IsInt r) : ((⌊r⌋ : ℤ) : ℝ) = r := by
  obtain ⟨m, rfl⟩ := h; simp

theorem filter_length_le_one_disj :
    ∀ {ts : List Tile}, ts.Pairwise (fun T U => Disjoint T.cells U.cells) → ∀ p : ℤ × ℤ,
      (ts.filter (fun T => p ∈ T.cells)).length ≤ 1
  | [], _, _ => by simp
  | T :: r, hs, p => by
    rw [List.pairwise_cons] at hs
    by_cases hp : p ∈ T.cells
    · have hnil : r.filter (fun T => p ∈ T.cells) = [] := by
        rw [List.filter_eq_nil_iff]
        intro U hU hpU
        simp only [decide_eq_true_eq] at hpU
        exact Finset.disjoint_left.mp (hs.1 U hU) hp hpU
      rw [List.filter_cons_of_pos (by simpa using hp), hnil]; simp
    · rw [List.filter_cons_of_neg (by simpa using hp)]
      exact filter_length_le_one_disj hs.2 p

/-- A real admissible tiling gives a unit-cell admissible tiling. -/
theorem RAdmissible.toAdmissible {n : ℕ} {ts : List RTile} (h : RAdmissible n ts) :
    Admissible n (ts.map RTile.toTile) := by
  have hint := integer_corners h.tiles
  have fx : ∀ T ∈ ts, ((⌊T.x⌋ : ℤ) : ℝ) = T.x := fun T hT => floor_eq_of_isInt (hint T hT).1
  have fy : ∀ T ∈ ts, ((⌊T.y⌋ : ℤ) : ℝ) = T.y := fun T hT => floor_eq_of_isInt (hint T hT).2
  -- Integer bounds of each tile.
  have ib : ∀ T ∈ ts, 0 ≤ ⌊T.x⌋ ∧ ⌊T.x⌋ + (T.w : ℤ) ≤ (n : ℤ) + 1 ∧ 0 ≤ ⌊T.y⌋ ∧
      ⌊T.y⌋ + (T.h : ℤ) ≤ n := by
    intro T hT
    have hb := h.tiles.bounds hT
    rw [← fx T hT, ← fy T hT] at hb
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact_mod_cast hb.1
    · have := hb.2.1; exact_mod_cast this
    · exact_mod_cast hb.2.2.1
    · have := hb.2.2.2; exact_mod_cast this
  -- Cell centres.
  have centre_closed : ∀ T ∈ ts, ∀ i j : ℤ, ((i : ℝ) + 1 / 2, (j : ℝ) + 1 / 2) ∈ T.closed →
      (i, j) ∈ T.toTile.cells := by
    intro T hT i j hc
    simp only [RTile.closed, Set.mem_prod, Set.mem_Icc] at hc
    rw [← fx T hT, ← fy T hT] at hc
    simp only [RTile.toTile, Tile.cells, Finset.mem_product, Finset.mem_Ico]
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hc
    have e1 : (⌊T.x⌋ : ℝ) < (i : ℝ) + 1 := by linarith
    have e2 : (i : ℝ) < (⌊T.x⌋ : ℝ) + (T.w : ℤ) := by push_cast; linarith
    have e3 : (⌊T.y⌋ : ℝ) < (j : ℝ) + 1 := by linarith
    have e4 : (j : ℝ) < (⌊T.y⌋ : ℝ) + (T.h : ℤ) := by push_cast; linarith
    have := (by exact_mod_cast e1 : ⌊T.x⌋ < i + 1)
    have := (by exact_mod_cast e2 : i < ⌊T.x⌋ + (T.w : ℤ))
    have := (by exact_mod_cast e3 : ⌊T.y⌋ < j + 1)
    have := (by exact_mod_cast e4 : j < ⌊T.y⌋ + (T.h : ℤ))
    omega
  have cell_inner : ∀ T ∈ ts, ∀ i j : ℤ, (i, j) ∈ T.toTile.cells →
      ((i : ℝ) + 1 / 2, (j : ℝ) + 1 / 2) ∈ T.inner := by
    intro T hT i j hc
    simp only [RTile.toTile, Tile.cells, Finset.mem_product, Finset.mem_Ico] at hc
    simp only [RTile.inner, Set.mem_prod, Set.mem_Ioo]
    rw [← fx T hT, ← fy T hT]
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hc
    have e1 : (⌊T.x⌋ : ℝ) ≤ i := by exact_mod_cast h1
    have e2 : (i : ℝ) + 1 ≤ ⌊T.x⌋ + (T.w : ℝ) := by
      have : i + 1 ≤ ⌊T.x⌋ + (T.w : ℤ) := by omega
      exact_mod_cast this
    have e3 : (⌊T.y⌋ : ℝ) ≤ j := by exact_mod_cast h3
    have e4 : (j : ℝ) + 1 ≤ ⌊T.y⌋ + (T.h : ℝ) := by
      have : j + 1 ≤ ⌊T.y⌋ + (T.h : ℤ) := by omega
      exact_mod_cast this
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hdisj : (ts.map RTile.toTile).Pairwise (fun T U => Disjoint T.cells U.cells) := by
    refine List.pairwise_map.mpr (h.tiles.disj.imp_of_mem fun {T U} hT hU hd => ?_)
    rw [Finset.disjoint_left]
    rintro ⟨i, j⟩ hpT hpU
    exact Set.disjoint_left.mp hd (cell_inner T hT i j hpT) (cell_inner U hU i j hpU)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hT'
    simp only [RTile.toTile]
    rcases h.almost T hT with e | e <;> [left; right] <;> rw [e] <;> push_cast <;> ring
  · intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hT'
    have := h.size_pos T hT
    simp only [RTile.toTile, Tile.size]
    rw [← Nat.cast_min]; exact_mod_cast this
  · intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hT'
    have := h.size_lt T hT
    simp only [RTile.toTile, Tile.size]
    rw [← Nat.cast_min]; exact_mod_cast this
  · rw [List.map_map]
    have e : (Tile.size ∘ RTile.toTile) = (fun k : ℕ => (k : ℤ)) ∘ (fun T : RTile => min T.w T.h) := by
      funext T; simp [Tile.size, RTile.toTile, Nat.cast_min]
    rw [e, ← List.map_map]
    exact h.distinct.map Nat.cast_injective
  · intro T' hT' p hp
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hT'
    have := ib T hT
    simp only [RTile.toTile, Tile.cells, rect, Finset.mem_product, Finset.mem_Ico] at hp ⊢
    omega
  · rintro ⟨i, j⟩ hp
    have hle := filter_length_le_one_disj hdisj (i, j)
    simp only [rect, Finset.mem_product, Finset.mem_Ico] at hp
    have hi0 : (0 : ℝ) ≤ i := by exact_mod_cast hp.1.1
    have hi1 : (i : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have : i + 1 ≤ (n : ℤ) + 1 := by omega
      exact_mod_cast this
    have hj0 : (0 : ℝ) ≤ j := by exact_mod_cast hp.2.1
    have hj1 : (j : ℝ) + 1 ≤ (n : ℝ) := by
      have : j + 1 ≤ (n : ℤ) := by omega
      exact_mod_cast this
    obtain ⟨T, hT, hc⟩ := (h.tiles.union ((i : ℝ) + 1 / 2, (j : ℝ) + 1 / 2)).mp
      ⟨by linarith, by linarith, by linarith, by linarith⟩
    have hmem : T.toTile ∈ (ts.map RTile.toTile).filter (fun U => (i, j) ∈ U.cells) := by
      simp only [List.mem_filter, List.mem_map, decide_eq_true_eq]
      exact ⟨⟨T, hT, rfl⟩, centre_closed T hT i j hc⟩
    have := List.length_pos_of_mem hmem
    omega

/-- A unit-cell admissible tiling, read as real rectangles, is a real admissible tiling. -/
theorem Admissible.toR {n : ℕ} (hn : 1 ≤ n) {ts : List Tile} (h : Admissible n ts) :
    RAdmissible n (ts.map Tile.toR) := by
  have hpos : ∀ T ∈ ts, 1 ≤ T.w ∧ 1 ≤ T.h := by
    intro T hT; have := h.size_pos T hT; have := h.almost T hT
    simp only [Tile.size] at *; omega
  have hd : Dissects ((n : ℤ) + 1) n ts :=
    ⟨fun T hT => ⟨by linarith [(hpos T hT).1], by linarith [(hpos T hT).2]⟩, h.inside, h.cover⟩
  have hb : ∀ T ∈ ts, 0 ≤ T.x ∧ 0 ≤ T.y ∧ T.x + T.w ≤ (n : ℤ) + 1 ∧ T.y + T.h ≤ n :=
    fun T hT => hd.bounds hT
  have cw : ∀ T ∈ ts, ((T.w.toNat : ℕ) : ℝ) = (T.w : ℝ) := fun T hT => by
    have : ((T.w.toNat : ℕ) : ℤ) = T.w := Int.toNat_of_nonneg (by linarith [(hpos T hT).1])
    exact_mod_cast this
  have ch : ∀ T ∈ ts, ((T.h.toNat : ℕ) : ℝ) = (T.h : ℝ) := fun T hT => by
    have : ((T.h.toNat : ℕ) : ℤ) = T.h := Int.toNat_of_nonneg (by linarith [(hpos T hT).2])
    exact_mod_cast this
  have hsep := hd.sep
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hT'
    have := hpos T hT
    simp only [Tile.toR]; omega
  · rintro ⟨px, py⟩
    simp only [List.mem_map, exists_exists_and_eq_and, Tile.toR, RTile.closed, Set.mem_prod,
      Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      -- The unit cell containing `(px, py)`, pushed inside `R_n` at the right and top edges.
      set i : ℤ := min ⌊px⌋ n with hi
      set j : ℤ := min ⌊py⌋ ((n : ℤ) - 1) with hj
      have fx0 : 0 ≤ ⌊px⌋ := Int.floor_nonneg.mpr h1
      have fy0 : 0 ≤ ⌊py⌋ := Int.floor_nonneg.mpr h3
      have hcell : (i, j) ∈ rect n := by
        simp only [rect, Finset.mem_product, Finset.mem_Ico]; omega
      have hc := h.cover _ hcell
      obtain ⟨T, hT⟩ : ∃ T, T ∈ ts.filter (fun T => (i, j) ∈ T.cells) := by
        rcases hl : ts.filter (fun T => (i, j) ∈ T.cells) with _ | ⟨T, _⟩
        · rw [hl] at hc; simp at hc
        · exact ⟨T, by rw [hl]; exact List.mem_cons_self ..⟩
      simp only [List.mem_filter, decide_eq_true_eq, Tile.cells, Finset.mem_product,
        Finset.mem_Ico] at hT
      obtain ⟨hT, ⟨e1, e2⟩, e3, e4⟩ := hT
      refine ⟨T, hT, ⟨?_, ?_⟩, ?_, ?_⟩
      · have : (T.x : ℝ) ≤ i := by exact_mod_cast e1
        have : (i : ℝ) ≤ ⌊px⌋ := by exact_mod_cast (min_le_left _ _)
        linarith [Int.floor_le px]
      · rw [cw T hT]
        have e2' : ((i + 1 : ℤ) : ℝ) ≤ ((T.x + T.w : ℤ) : ℝ) := by exact_mod_cast (by omega : i + 1 ≤ T.x + T.w)
        push_cast at e2'
        rcases le_total ⌊px⌋ (n : ℤ) with hle | hle
        · have : i = ⌊px⌋ := min_eq_left hle
          rw [this] at e2'; linarith [Int.lt_floor_add_one px]
        · have : i = n := min_eq_right hle
          rw [this] at e2'; push_cast at e2'; linarith
      · have : (T.y : ℝ) ≤ j := by exact_mod_cast e3
        have : (j : ℝ) ≤ ⌊py⌋ := by exact_mod_cast (min_le_left _ _)
        linarith [Int.floor_le py]
      · rw [ch T hT]
        have e4' : ((j + 1 : ℤ) : ℝ) ≤ ((T.y + T.h : ℤ) : ℝ) := by exact_mod_cast (by omega : j + 1 ≤ T.y + T.h)
        push_cast at e4'
        rcases le_total ⌊py⌋ ((n : ℤ) - 1) with hle | hle
        · have : j = ⌊py⌋ := min_eq_left hle
          rw [this] at e4'; linarith [Int.lt_floor_add_one py]
        · have : j = (n : ℤ) - 1 := min_eq_right hle
          rw [this] at e4'; push_cast at e4'; linarith
    · rintro ⟨T, hT, ⟨h1, h2⟩, h3, h4⟩
      obtain ⟨b1, b2, b3, b4⟩ := hb T hT
      rw [cw T hT] at h2; rw [ch T hT] at h4
      have r1 : (0 : ℝ) ≤ T.x := by exact_mod_cast b1
      have r2 : (0 : ℝ) ≤ T.y := by exact_mod_cast b2
      have r3 : (T.x : ℝ) + T.w ≤ (n : ℝ) + 1 := by exact_mod_cast b3
      have r4 : (T.y : ℝ) + T.h ≤ (n : ℝ) := by exact_mod_cast b4
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · refine List.pairwise_map.mpr (hsep.imp_of_mem fun {T U} hT hU hs => ?_)
    rw [Set.disjoint_left]
    rintro ⟨px, py⟩ hpT hpU
    simp only [Tile.toR, RTile.inner, Set.mem_prod, Set.mem_Ioo] at hpT hpU
    rw [cw T hT, ch T hT] at hpT; rw [cw U hU, ch U hU] at hpU
    unfold AlmostSq.Sep at hs
    rcases hs with e | e | e | e
    · have : (T.x : ℝ) + T.w ≤ U.x := by exact_mod_cast e
      linarith [hpT.1.2, hpU.1.1]
    · have : (U.x : ℝ) + U.w ≤ T.x := by exact_mod_cast e
      linarith [hpT.1.1, hpU.1.2]
    · have : (T.y : ℝ) + T.h ≤ U.y := by exact_mod_cast e
      linarith [hpT.2.2, hpU.2.1]
    · have : (U.y : ℝ) + U.h ≤ T.y := by exact_mod_cast e
      linarith [hpT.2.1, hpU.2.2]
  · intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hT'
    have := h.almost T hT; have := hpos T hT
    simp only [Tile.toR]; omega
  · intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hT'
    have := h.size_pos T hT
    simp only [Tile.toR, Tile.size] at *; omega
  · intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hT'
    have := h.size_lt T hT
    simp only [Tile.toR, Tile.size] at *; omega
  · rw [List.map_map]
    have e : ∀ T ∈ ts, ((fun T : RTile => min T.w T.h) ∘ Tile.toR) T = (Tile.size T).toNat := by
      intro T hT; simp only [Function.comp, Tile.toR, Tile.size]; omega
    rw [List.map_congr_left e,
      show (fun a : Tile => a.size.toNat) = (fun k : ℤ => k.toNat) ∘ Tile.size from rfl, ← List.map_map]
    refine List.Nodup.map_on (fun a ha b hb hab => ?_) h.distinct
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp ha
    obtain ⟨U, hU, rfl⟩ := List.mem_map.mp hb
    have := h.size_pos T hT; have := h.size_pos U hU
    omega

/-- **Theorem 1**, for tilings by real rectangles: for `n ≥ 1`, the `(n+1) × n` rectangle can be
    tiled by closed almost-squares of distinct sizes `1 ≤ k < n` (any real positions, disjoint
    interiors) if and only if `n ∈ {4, 10, 12, 14, 15, 18}` or `n ≥ 20`. -/
theorem almost_square_tilings_real (n : ℕ) (hn : 1 ≤ n) :
    (∃ ts : List RTile, RAdmissible n ts) ↔ n ∈ [4, 10, 12, 14, 15, 18] ∨ 20 ≤ n := by
  rw [← almost_square_tilings n hn]
  exact ⟨fun ⟨ts, h⟩ => ⟨_, h.toAdmissible⟩, fun ⟨ts, h⟩ => ⟨_, Admissible.toR hn h⟩⟩

end AlmostSq
