/-
  Section 3 of the paper: the parity lemma (Lemma 5) and Proposition 6 on the squared squares of
  sides 112, 110 and 139. The three squares are taken from Moews's list of Bouwkamp codes; the files
  out/sq{112,110,139}.txt of the paper's ancillary data give the same layouts, one square per line
  as `side x y` with lower-left origin.
-/
import AlmostSquares.Inflation

namespace AlmostSq

/-- A square of side `s` with lower-left corner `(x, y)`. -/
def sq (s x y : ℤ) : Tile := ⟨x, y, s, s⟩

/-- Width change minus height change of `T` under the shift `(u, v)`: `ε = δu - δv`. -/
def eps (u v : ℤ → ℤ) (T : Tile) : ℤ := (u (T.x + T.w) - u T.x) - (v (T.y + T.h) - v T.y)

/-- An inflation of a squared square of side `S` (Section 2). -/
structure IsInflation (S : ℤ) (ts : List Tile) (u v : ℤ → ℤ) : Prop where
  u0 : u 0 = 0
  v0 : v 0 = 0
  corner : u S - v S = 1
  eps : ∀ T ∈ ts, eps u v T = 1 ∨ eps u v T = -1

/-- The four shift values on the sides of `T`. -/
def coordSum (u v : ℤ → ℤ) (T : Tile) : ℤ := u T.x + u (T.x + T.w) + v T.y + v (T.y + T.h)

/-- **Lemma 5 (Parity).** If `ε = ±1` on every square of `T`, the shift values on the sides of the
    squares of `T` add up to `|T|` modulo 2. -/
theorem parity (u v : ℤ → ℤ) : ∀ T : List Tile, (∀ q ∈ T, eps u v q = 1 ∨ eps u v q = -1) →
    ((T.map (coordSum u v)).sum - T.length) % 2 = 0
  | [], _ => by simp
  | q :: r, h => by
    have ih := parity u v r (fun q' hq' => h q' (List.mem_cons_of_mem _ hq'))
    have hq := h q (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons, List.length_cons, coordSum, eps] at ih hq ⊢
    push_cast
    omega

/-- The `x`-coordinates of the vertical sides of the squares of `T`, with multiplicity. -/
def xSides (T : List Tile) : List ℤ := T.flatMap (fun q => [q.x, q.x + q.w])

/-- The `y`-coordinates of the horizontal sides, with multiplicity. -/
def ySides (T : List Tile) : List ℤ := T.flatMap (fun q => [q.y, q.y + q.h])

theorem coordSum_split (u v : ℤ → ℤ) : ∀ T : List Tile,
    (T.map (coordSum u v)).sum = ((xSides T).map u).sum + ((ySides T).map v).sum
  | [] => by simp [xSides, ySides]
  | q :: r => by
    simp only [List.map_cons, List.sum_cons, xSides, ySides, List.flatMap_cons, List.map_append,
      List.sum_append, List.map_nil, List.sum_nil] at *
    rw [coordSum_split u v r, xSides, ySides, coordSum]
    ring

theorem even_sum_of_even_count (L : List ℤ) (f : ℤ → ℤ) (h : ∀ a, Even (L.count a)) :
    Even (L.map f).sum := by
  rw [Finset.sum_list_map_count]
  refine Finset.even_sum _ (fun a _ => ?_)
  obtain ⟨r, hr⟩ := h a
  exact ⟨r • f a, by rw [hr, add_smul]⟩

/-- **Lemma 5, second part.** If every coordinate occurs an even number of times among the sides of
    the squares in `T`, then `|T|` is even. -/
theorem parity_even (u v : ℤ → ℤ) (T : List Tile) (h : ∀ q ∈ T, eps u v q = 1 ∨ eps u v q = -1)
    (hx : ∀ a, Even ((xSides T).count a)) (hy : ∀ b, Even ((ySides T).count b)) :
    Even T.length := by
  have hp := parity u v T h
  rw [coordSum_split] at hp
  obtain ⟨a, ha⟩ := even_sum_of_even_count _ u hx
  obtain ⟨b, hb⟩ := even_sum_of_even_count _ v hy
  rw [ha, hb] at hp
  rw [Nat.even_iff]
  omega

/-! ### The three squared squares -/

def sq112 : List Tile := [
  sq 50 0 62,
  sq 35 50 77,
  sq 27 85 85,
  sq 8 85 77,
  sq 19 93 66,
  sq 15 50 62,
  sq 17 65 60,
  sq 11 82 66,
  sq 6 82 60,
  sq 24 88 42,
  sq 29 0 33,
  sq 25 29 37,
  sq 9 54 53,
  sq 2 63 60,
  sq 7 63 53,
  sq 18 70 42,
  sq 16 54 37,
  sq 42 70 0,
  sq 4 29 33,
  sq 37 33 0,
  sq 33 0 0
]
def sq110 : List Tile := [
  sq 60 0 50,
  sq 50 60 60,
  sq 27 60 33,
  sq 23 87 37,
  sq 24 0 26,
  sq 22 24 28,
  sq 14 46 36,
  sq 4 87 33,
  sq 19 91 18,
  sq 8 46 28,
  sq 6 54 30,
  sq 3 60 30,
  sq 12 63 21,
  sq 16 75 17,
  sq 9 54 21,
  sq 2 24 26,
  sq 28 26 0,
  sq 26 0 0,
  sq 21 54 0,
  sq 1 91 17,
  sq 18 92 0,
  sq 17 75 0
]
def sq139 : List Tile := [
  sq 80 0 59,
  sq 59 80 80,
  sq 21 80 59,
  sq 38 101 42,
  sq 29 0 30,
  sq 28 29 31,
  sq 17 57 42,
  sq 27 74 32,
  sq 7 57 35,
  sq 10 64 32,
  sq 18 101 24,
  sq 20 119 22,
  sq 4 57 31,
  sq 3 61 32,
  sq 32 61 0,
  sq 8 93 24,
  sq 1 29 30,
  sq 31 30 0,
  sq 30 0 0,
  sq 24 93 0,
  sq 2 117 22,
  sq 22 117 0
]

/-- A boolean certificate that `ts` dissects `[0,W] × [0,H]`: positive tiles inside the box,
    pairwise separated, with total area `W H`. -/
def dissectsCheck (W H : ℤ) (ts : List Tile) : Bool :=
  ts.all (fun T => decide (0 < T.w ∧ 0 < T.h ∧ 0 ≤ T.x ∧ 0 ≤ T.y ∧ T.x + T.w ≤ W ∧ T.y + T.h ≤ H)) &&
    pwSep ts && decide ((ts.map (fun T => T.w * T.h)).sum = W * H)

theorem dissectsCheck_sound {W H : ℤ} (hW : 0 ≤ W) (hH : 0 ≤ H) {ts : List Tile}
    (h : dissectsCheck W H ts = true) : Dissects W H ts := by
  simp only [dissectsCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hT, hs⟩, ha⟩ := h
  refine dissects_of_sep_area hW hH (fun T hm => ⟨(hT T hm).1, (hT T hm).2.1⟩) (fun T hm p hp => ?_)
    (pwSep_sound hs) ha
  have := hT T hm
  simp only [Tile.cells, box, Finset.mem_product, Finset.mem_Ico] at hp ⊢
  omega

/-- A perfect squared square of side `S`: a dissection into squares of distinct sides. -/
def PerfectSquaredSquare (S : ℤ) (ts : List Tile) : Prop :=
  Dissects S S ts ∧ (∀ T ∈ ts, T.w = T.h) ∧ (ts.map Tile.w).Nodup

theorem sq112_perfect : PerfectSquaredSquare 112 sq112 :=
  ⟨dissectsCheck_sound (by norm_num) (by norm_num) (by decide +kernel), by decide +kernel,
    by decide +kernel⟩

theorem sq110_perfect : PerfectSquaredSquare 110 sq110 :=
  ⟨dissectsCheck_sound (by norm_num) (by norm_num) (by decide +kernel), by decide +kernel,
    by decide +kernel⟩

theorem sq139_perfect : PerfectSquaredSquare 139 sq139 :=
  ⟨dissectsCheck_sound (by norm_num) (by norm_num) (by decide +kernel), by decide +kernel,
    by decide +kernel⟩

/-! ### Proposition 6 -/

/-- The stack of Figure 5. -/
def T112 : List Tile := [sq 42 70 0, sq 18 70 42, sq 6 82 60, sq 11 82 66, sq 8 85 77, sq 27 85 85]

def T110 : List Tile := [sq 26 0 0, sq 22 24 28, sq 18 92 0, sq 16 75 17, sq 14 46 36, sq 12 63 21,
  sq 9 54 21, sq 6 54 30, sq 2 24 26, sq 1 91 17]

def T139 : List Tile := [sq 80 0 59, sq 59 80 80, sq 38 101 42, sq 32 61 0, sq 30 0 0, sq 28 29 31,
  sq 24 93 0, sq 22 117 0, sq 20 119 22, sq 18 101 24, sq 7 57 35, sq 3 61 32, sq 1 29 30]

/-- **Proposition 6 (1).** Every inflation of Duijvestijn's square of side 112 has `v(112)` even. -/
theorem prop_112 (u v : ℤ → ℤ) (h : IsInflation 112 sq112 u v) : Even (v 112) := by
  have hs : ∀ q ∈ T112, q ∈ sq112 := by decide +kernel
  have hp := parity u v T112 (fun q hq => h.eps q (hs q hq))
  simp [T112, sq, coordSum] at hp
  have := h.v0
  rw [Int.even_iff]
  omega

/-- **Proposition 6 (2).** Every inflation of the order-22 square of side 110 with code
    `(60,50)(27,23)...` has `v(110)` odd. -/
theorem prop_110 (u v : ℤ → ℤ) (h : IsInflation 110 sq110 u v) : Odd (v 110) := by
  have hs : ∀ q ∈ T110, q ∈ sq110 := by decide +kernel
  have hp := parity u v T110 (fun q hq => h.eps q (hs q hq))
  simp [T110, sq, coordSum] at hp
  have := h.u0
  have := h.corner
  rw [Int.odd_iff]
  omega

/-- **Proposition 6 (3).** The order-22 square of side 139 with code `(80,59)(21,38)...` has no
    inflation: no shift at all makes every `ε = ±1`. -/
theorem prop_139 : ¬ ∃ u v : ℤ → ℤ, ∀ T ∈ sq139, eps u v T = 1 ∨ eps u v T = -1 := by
  rintro ⟨u, v, h⟩
  have hs : ∀ q ∈ T139, q ∈ sq139 := by decide +kernel
  have hp := parity u v T139 (fun q hq => h q (hs q hq))
  simp [T139, sq, coordSum] at hp
  omega

end AlmostSq
