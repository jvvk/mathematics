/-
  Tiling an almost-square with distinct smaller almost-squares (Friedman's problem #20).

  Definitions, the counting lemma "pairwise separated + area = exact cover", and a boolean checker
  for concrete tilings with its soundness proof.
-/
import Mathlib.Tactic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Int.Interval

namespace AlmostSq

/-- A placed axis-parallel tile with lower-left corner `(x, y)`, width `w` and height `h`. -/
structure Tile where
  x : ℤ
  y : ℤ
  w : ℤ
  h : ℤ
deriving DecidableEq

namespace Tile

/-- The size `k` of a `k × (k+1)` tile. -/
def size (T : Tile) : ℤ := min T.w T.h

/-- The unit cells `[a, a+1) × [b, b+1)` of the tile, named by their lower-left corners. -/
def cells (T : Tile) : Finset (ℤ × ℤ) := Finset.Ico T.x (T.x + T.w) ×ˢ Finset.Ico T.y (T.y + T.h)

end Tile

/-- The unit cells of `R_n`, the rectangle of width `n + 1` and height `n`. -/
def rect (n : ℕ) : Finset (ℤ × ℤ) := Finset.Ico 0 ((n : ℤ) + 1) ×ˢ Finset.Ico 0 (n : ℤ)

/-- An admissible tiling of `R_n`: almost-squares of distinct sizes `1 ≤ k < n`, lying in `R_n`,
    covering every unit cell of `R_n` exactly once. -/
structure Admissible (n : ℕ) (ts : List Tile) : Prop where
  almost : ∀ T ∈ ts, T.w = T.h + 1 ∨ T.h = T.w + 1
  size_pos : ∀ T ∈ ts, 1 ≤ T.size
  size_lt : ∀ T ∈ ts, T.size < n
  distinct : (ts.map Tile.size).Nodup
  inside : ∀ T ∈ ts, T.cells ⊆ rect n
  cover : ∀ p ∈ rect n, (ts.filter (fun T => p ∈ T.cells)).length = 1

/-- Two tiles are separated by a vertical or a horizontal line. -/
def Sep (T U : Tile) : Prop :=
  T.x + T.w ≤ U.x ∨ U.x + U.w ≤ T.x ∨ T.y + T.h ≤ U.y ∨ U.y + U.h ≤ T.y

instance (T U : Tile) : Decidable (Sep T U) := by unfold Sep; infer_instance

theorem Sep.disjoint {T U : Tile} (h : Sep T U) : Disjoint T.cells U.cells := by
  rw [Finset.disjoint_left]
  intro p hp hq
  simp only [Tile.cells, Finset.mem_product, Finset.mem_Ico] at hp hq
  unfold Sep at h
  omega

/-- The hypotheses of the counting argument. -/
structure Good (n : ℕ) (ts : List Tile) : Prop where
  almost : ∀ T ∈ ts, T.w = T.h + 1 ∨ T.h = T.w + 1
  size_pos : ∀ T ∈ ts, 1 ≤ T.size
  size_lt : ∀ T ∈ ts, T.size < n
  distinct : (ts.map Tile.size).Nodup
  inside : ∀ T ∈ ts, 0 ≤ T.x ∧ 0 ≤ T.y ∧ T.x + T.w ≤ (n : ℤ) + 1 ∧ T.y + T.h ≤ n
  sep : ts.Pairwise Sep
  area : (ts.map (fun T => T.w * T.h)).sum = ((n : ℤ) + 1) * n

/-- The union of the cells of a list of tiles. -/
def cellsUnion (ts : List Tile) : Finset (ℤ × ℤ) := ts.foldr (fun T acc => T.cells ∪ acc) ∅

theorem mem_cellsUnion {ts : List Tile} {p : ℤ × ℤ} :
    p ∈ cellsUnion ts ↔ ∃ T ∈ ts, p ∈ T.cells := by
  induction ts with
  | nil => simp [cellsUnion]
  | cons T r ih =>
    simp only [cellsUnion, List.foldr_cons, Finset.mem_union, List.mem_cons] at ih ⊢
    rw [ih]
    constructor
    · rintro (h | ⟨U, hU, hp⟩)
      · exact ⟨T, Or.inl rfl, h⟩
      · exact ⟨U, Or.inr hU, hp⟩
    · rintro ⟨U, rfl | hU, hp⟩
      · exact Or.inl hp
      · exact Or.inr ⟨U, hU, hp⟩

theorem card_cells {T : Tile} (hw : 0 ≤ T.w) (hh : 0 ≤ T.h) :
    (T.cells.card : ℤ) = T.w * T.h := by
  simp only [Tile.cells, Finset.card_product, Int.card_Ico, add_sub_cancel_left]
  push_cast
  rw [Int.toNat_of_nonneg hw, Int.toNat_of_nonneg hh]

theorem card_cellsUnion {ts : List Tile} (hs : ts.Pairwise Sep)
    (hpos : ∀ T ∈ ts, 0 ≤ T.w ∧ 0 ≤ T.h) :
    ((cellsUnion ts).card : ℤ) = (ts.map (fun T => T.w * T.h)).sum := by
  induction ts with
  | nil => simp [cellsUnion]
  | cons T r ih =>
    rw [List.pairwise_cons] at hs
    have hd : Disjoint T.cells (cellsUnion r) := by
      rw [Finset.disjoint_left]
      intro p hp hq
      obtain ⟨U, hU, hpU⟩ := mem_cellsUnion.mp hq
      exact Finset.disjoint_left.mp (hs.1 U hU).disjoint hp hpU
    have hT := hpos T (List.mem_cons_self ..)
    show ((T.cells ∪ cellsUnion r).card : ℤ) = _
    rw [Finset.card_union_of_disjoint hd, List.map_cons, List.sum_cons]
    push_cast
    rw [card_cells hT.1 hT.2, ih hs.2 (fun U hU => hpos U (List.mem_cons_of_mem _ hU))]

theorem card_rect (n : ℕ) : ((rect n).card : ℤ) = ((n : ℤ) + 1) * n := by
  simp only [rect, Finset.card_product, Int.card_Ico, sub_zero]
  push_cast
  rw [Int.toNat_of_nonneg (by positivity), Int.toNat_of_nonneg (by positivity)]

theorem filter_length_le_one {ts : List Tile} (hs : ts.Pairwise Sep) (p : ℤ × ℤ) :
    (ts.filter (fun T => p ∈ T.cells)).length ≤ 1 := by
  induction ts with
  | nil => simp
  | cons T r ih =>
    rw [List.pairwise_cons] at hs
    by_cases hp : p ∈ T.cells
    · have hnil : r.filter (fun T => p ∈ T.cells) = [] := by
        rw [List.filter_eq_nil_iff]
        intro U hU hpU
        simp only [decide_eq_true_eq] at hpU
        exact Finset.disjoint_left.mp (hs.1 U hU).disjoint hp hpU
      simp [hp, hnil]
    · simpa [List.filter_cons, hp] using ih hs.2

/-- The counting argument: pairwise separated tiles inside `R_n` of total area `(n+1) n`
    cover every cell exactly once. -/
theorem Good.admissible {n : ℕ} {ts : List Tile} (g : Good n ts) : Admissible n ts := by
  have hpos : ∀ T ∈ ts, 0 ≤ T.w ∧ 0 ≤ T.h := by
    intro T hT
    have := g.size_pos T hT; have := g.almost T hT
    simp only [Tile.size] at *; omega
  have hin : ∀ T ∈ ts, T.cells ⊆ rect n := by
    intro T hT p hp
    have := g.inside T hT
    simp only [Tile.cells, rect, Finset.mem_product, Finset.mem_Ico] at hp ⊢
    omega
  have hsub : cellsUnion ts ⊆ rect n := by
    intro p hp
    obtain ⟨T, hT, hpT⟩ := mem_cellsUnion.mp hp
    exact hin T hT hpT
  have hcard : (rect n).card ≤ (cellsUnion ts).card := by
    have h1 := card_cellsUnion g.sep hpos
    have h2 := card_rect n
    rw [g.area] at h1
    omega
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  refine ⟨g.almost, g.size_pos, g.size_lt, g.distinct, hin, fun p hp => ?_⟩
  have hle := filter_length_le_one g.sep p
  rw [← heq] at hp
  obtain ⟨T, hT, hpT⟩ := mem_cellsUnion.mp hp
  have hmem : T ∈ ts.filter (fun T => p ∈ T.cells) := by simp [hT, hpT]
  have := List.length_pos_of_mem hmem
  omega

/-! ### A checker for concrete tilings -/

/-- The conditions on a single tile. -/
def tileOK (n : ℕ) (T : Tile) : Bool :=
  decide ((T.w = T.h + 1 ∨ T.h = T.w + 1) ∧ 1 ≤ T.size ∧ T.size < n ∧ 0 ≤ T.x ∧ 0 ≤ T.y ∧
    T.x + T.w ≤ (n : ℤ) + 1 ∧ T.y + T.h ≤ n)

/-- Pairwise separation, as a boolean. -/
def pwSep : List Tile → Bool
  | [] => true
  | T :: r => r.all (fun U => decide (Sep T U)) && pwSep r

theorem pwSep_sound : ∀ {ts : List Tile}, pwSep ts = true → ts.Pairwise Sep
  | [], _ => List.Pairwise.nil
  | T :: r, h => by
    simp only [pwSep, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact List.Pairwise.cons h.1 (pwSep_sound h.2)

/-- The checker: every tile is fine, sizes are distinct, tiles are pairwise separated,
    and the areas add up to `(n+1) n`. -/
def check (n : ℕ) (ts : List Tile) : Bool :=
  ts.all (tileOK n) && decide ((ts.map Tile.size).Nodup) && pwSep ts &&
    decide ((ts.map (fun T => T.w * T.h)).sum = ((n : ℤ) + 1) * n)

theorem check_sound {n : ℕ} {ts : List Tile} (h : check n ts = true) : Admissible n ts := by
  simp only [check, tileOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hT, hd⟩, hs⟩, ha⟩ := h
  exact Good.admissible
    { almost := fun T hm => (hT T hm).1
      size_pos := fun T hm => (hT T hm).2.1
      size_lt := fun T hm => (hT T hm).2.2.1
      distinct := hd
      inside := fun T hm => (hT T hm).2.2.2
      sep := pwSep_sound hs
      area := ha }

/-- Build a tile from a data line `w h x y`. -/
def mk (w h x y : ℤ) : Tile := ⟨x, y, w, h⟩

end AlmostSq
