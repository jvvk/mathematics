/-
  Section 2 of the paper, in general form: the balance identity (Lemma 2), the inflation lemma
  (Lemma 3) and the signed identity (Corollary 7).

  A dissection is stated at the level of unit cells (`Dissects`): every cell of `[0,W] × [0,H]` lies
  in exactly one tile. `integer_corners` (Real.lean) connects this to tilings by real rectangles.
-/
import AlmostSquares.Basic

namespace AlmostSq

open Finset

/-- The unit cells of `[0,W] × [0,H]`, named by their lower-left corners. -/
def box (W H : ℤ) : Finset (ℤ × ℤ) := Ico 0 W ×ˢ Ico 0 H

/-- `ts` dissects `[0,W] × [0,H]`: tiles of positive size inside the box, covering every unit cell
    exactly once. -/
structure Dissects (W H : ℤ) (ts : List Tile) : Prop where
  pos : ∀ T ∈ ts, 0 < T.w ∧ 0 < T.h
  inside : ∀ T ∈ ts, T.cells ⊆ box W H
  cover : ∀ p ∈ box W H, (ts.filter (fun T => p ∈ T.cells)).length = 1

/-- The forward difference `f (a+1) - f a`. -/
def fd (f : ℤ → ℤ) (a : ℤ) : ℤ := f (a + 1) - f a

theorem sum_Ico_fd_nat (f : ℤ → ℤ) (x : ℤ) (k : ℕ) :
    ∑ a ∈ Ico x (x + k), fd f a = f (x + k) - f x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h : Ico x (x + ((k + 1 : ℕ) : ℤ)) = insert (x + k) (Ico x (x + k)) := by
      ext a; simp only [mem_Ico, mem_insert]; push_cast; omega
    rw [h, sum_insert (by simp), ih, fd]
    push_cast; ring_nf

theorem sum_Ico_fd (f : ℤ → ℤ) (x w : ℤ) (hw : 0 ≤ w) :
    ∑ a ∈ Ico x (x + w), fd f a = f (x + w) - f x := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hw
  exact sum_Ico_fd_nat f x k

/-- One tile's term in the balance identity is the total weight of its cells. -/
theorem tile_term (f g : ℤ → ℤ) (T : Tile) (hw : 0 ≤ T.w) (hh : 0 ≤ T.h) :
    (f (T.x + T.w) - f T.x) * (g (T.y + T.h) - g T.y) = ∑ p ∈ T.cells, fd f p.1 * fd g p.2 := by
  rw [Tile.cells, sum_product, ← sum_Ico_fd f _ _ hw, ← sum_Ico_fd g _ _ hh, sum_mul_sum]

/-- Exchanging the sum over tiles with the sum over cells. -/
theorem sum_tiles_cells (S : Finset (ℤ × ℤ)) (F : ℤ × ℤ → ℤ) :
    ∀ ts : List Tile, (∀ T ∈ ts, T.cells ⊆ S) →
      (ts.map (fun T => ∑ p ∈ T.cells, F p)).sum =
        ∑ p ∈ S, ((ts.filter (fun T => p ∈ T.cells)).length : ℤ) * F p
  | [], _ => by simp
  | T :: r, hin => by
    rw [List.map_cons, List.sum_cons,
      sum_tiles_cells S F r (fun U hU => hin U (List.mem_cons_of_mem _ hU))]
    have hT : ∑ p ∈ T.cells, F p = ∑ p ∈ S, (if p ∈ T.cells then F p else 0) := by
      rw [sum_ite_mem, inter_eq_right.mpr (hin T (List.mem_cons_self ..))]
    rw [hT, ← sum_add_distrib]
    refine sum_congr rfl (fun p _ => ?_)
    by_cases hp : p ∈ T.cells
    · simp [hp]; ring
    · simp [hp]

/-- **Lemma 2 (Balance).** For a dissection of `[0,W] × [0,H]` and any `f, g : ℤ → ℤ`,
    `∑ (f r - f l)(g t - g b) = (f W - f 0)(g H - g 0)`. -/
theorem balance {W H : ℤ} (hW : 0 ≤ W) (hH : 0 ≤ H) {ts : List Tile} (hd : Dissects W H ts)
    (f g : ℤ → ℤ) :
    (ts.map (fun T => (f (T.x + T.w) - f T.x) * (g (T.y + T.h) - g T.y))).sum =
      (f W - f 0) * (g H - g 0) := by
  have h1 : ts.map (fun T => (f (T.x + T.w) - f T.x) * (g (T.y + T.h) - g T.y)) =
      ts.map (fun T => ∑ p ∈ T.cells, fd f p.1 * fd g p.2) :=
    List.map_congr_left (fun T hT => tile_term f g T (hd.pos T hT).1.le (hd.pos T hT).2.le)
  rw [h1, sum_tiles_cells (box W H) _ ts hd.inside]
  rw [sum_congr rfl (fun p hp => by rw [hd.cover p hp, Nat.cast_one, one_mul])]
  rw [box, sum_product]
  dsimp only
  rw [← sum_mul_sum]
  have hf := sum_Ico_fd f 0 W hW
  have hg := sum_Ico_fd g 0 H hH
  simp only [zero_add] at hf hg
  rw [hf, hg]

/-! ### Inflation -/

/-- Distinct tiles of a dissection are separated by a vertical or horizontal line. -/
theorem pairwise_sep_of_le_one :
    ∀ {ts : List Tile}, (∀ T ∈ ts, 0 < T.w ∧ 0 < T.h) →
      (∀ p, (ts.filter (fun T => p ∈ T.cells)).length ≤ 1) → ts.Pairwise Sep
  | [], _, _ => List.Pairwise.nil
  | T :: r, hpos, h1 => by
    refine List.Pairwise.cons (fun U hU => ?_) (pairwise_sep_of_le_one
      (fun U hU => hpos U (List.mem_cons_of_mem _ hU)) (fun p => ?_))
    · by_contra hn
      have hT := hpos T (List.mem_cons_self ..)
      have hU' := hpos U (List.mem_cons_of_mem _ hU)
      let p : ℤ × ℤ := (max T.x U.x, max T.y U.y)
      unfold AlmostSq.Sep at hn
      have hpT : p ∈ T.cells := by
        simp only [p, Tile.cells, mem_product, mem_Ico]; omega
      have hpU : p ∈ U.cells := by
        simp only [p, Tile.cells, mem_product, mem_Ico]; omega
      have hmem : U ∈ r.filter (fun T => p ∈ T.cells) := by simp [hU, hpU]
      have hl := List.length_pos_of_mem hmem
      have := h1 p
      rw [List.filter_cons_of_pos (by simpa using hpT), List.length_cons] at this
      omega
    · have := h1 p
      by_cases hp : p ∈ T.cells
      · rw [List.filter_cons_of_pos (by simpa using hp), List.length_cons] at this; omega
      · rwa [List.filter_cons_of_neg (by simpa using hp)] at this

theorem Dissects.le_one {W H : ℤ} {ts : List Tile} (hd : Dissects W H ts) (p : ℤ × ℤ) :
    (ts.filter (fun T => p ∈ T.cells)).length ≤ 1 := by
  by_cases hp : p ∈ box W H
  · exact (hd.cover p hp).le
  · have : ts.filter (fun T => p ∈ T.cells) = [] := by
      rw [List.filter_eq_nil_iff]
      intro T hT hpT
      simp only [decide_eq_true_eq] at hpT
      exact hp (hd.inside T hT hpT)
    simp [this]

theorem Dissects.sep {W H : ℤ} {ts : List Tile} (hd : Dissects W H ts) : ts.Pairwise Sep :=
  pairwise_sep_of_le_one hd.pos hd.le_one

theorem Dissects.bounds {W H : ℤ} {ts : List Tile} (hd : Dissects W H ts) {T : Tile}
    (hT : T ∈ ts) : 0 ≤ T.x ∧ 0 ≤ T.y ∧ T.x + T.w ≤ W ∧ T.y + T.h ≤ H := by
  have hp := hd.pos T hT
  have h1 : (T.x, T.y) ∈ box W H := hd.inside T hT (by
    simp only [Tile.cells, mem_product, mem_Ico]; omega)
  have h2 : (T.x + T.w - 1, T.y + T.h - 1) ∈ box W H := hd.inside T hT (by
    simp only [Tile.cells, mem_product, mem_Ico]; omega)
  simp only [box, mem_product, mem_Ico] at h1 h2
  omega

/-- Separated tiles inside a box whose areas add up to the area of the box cover it exactly. -/
theorem dissects_of_sep_area {W H : ℤ} (hW : 0 ≤ W) (hH : 0 ≤ H) {ts : List Tile}
    (hpos : ∀ T ∈ ts, 0 < T.w ∧ 0 < T.h) (hin : ∀ T ∈ ts, T.cells ⊆ box W H)
    (hs : ts.Pairwise Sep) (harea : (ts.map (fun T => T.w * T.h)).sum = W * H) :
    Dissects W H ts := by
  have hsub : cellsUnion ts ⊆ box W H := by
    intro p hp
    obtain ⟨T, hT, hpT⟩ := mem_cellsUnion.mp hp
    exact hin T hT hpT
  have hbox : ((box W H).card : ℤ) = W * H := by
    simp only [box, card_product, Int.card_Ico, sub_zero]
    push_cast
    rw [Int.toNat_of_nonneg hW, Int.toNat_of_nonneg hH]
  have hcard : (box W H).card ≤ (cellsUnion ts).card := by
    have h1 := card_cellsUnion hs (fun T hT => ⟨(hpos T hT).1.le, (hpos T hT).2.le⟩)
    omega
  have heq := eq_of_subset_of_card_le hsub hcard
  refine ⟨hpos, hin, fun p hp => ?_⟩
  have hle := filter_length_le_one hs p
  rw [← heq] at hp
  obtain ⟨T, hT, hpT⟩ := mem_cellsUnion.mp hp
  have hmem : T ∈ ts.filter (fun T => p ∈ T.cells) := by simp [hT, hpT]
  have := List.length_pos_of_mem hmem
  omega

/-- The cut lines of a dissection: `0`, `W` and the vertical sides of the tiles (for `x`). -/
def CutX (W : ℤ) (ts : List Tile) : Set ℤ := {a | a = 0 ∨ a = W ∨ ∃ T ∈ ts, a = T.x ∨ a = T.x + T.w}

/-- The horizontal cut lines. -/
def CutY (H : ℤ) (ts : List Tile) : Set ℤ := {b | b = 0 ∨ b = H ∨ ∃ T ∈ ts, b = T.y ∨ b = T.y + T.h}

/-- The image of a tile when the cut lines move by `X` and `Y`. -/
def img (X Y : ℤ → ℤ) (T : Tile) : Tile :=
  ⟨X T.x, Y T.y, X (T.x + T.w) - X T.x, Y (T.y + T.h) - Y T.y⟩

/-- **Lemma 3 (Inflation), first part.** Moving the cut lines of a dissection by maps that are
    strictly increasing on the cut lines, and fix `0`, gives a dissection. -/
theorem dissects_img {W H : ℤ} (hW : 0 ≤ W) (hH : 0 ≤ H) {ts : List Tile} (hd : Dissects W H ts)
    (X Y : ℤ → ℤ) (hX0 : X 0 = 0) (hY0 : Y 0 = 0)
    (hX : StrictMonoOn X (CutX W ts)) (hY : StrictMonoOn Y (CutY H ts)) :
    Dissects (X W) (Y H) (ts.map (img X Y)) := by
  have cx : ∀ T ∈ ts, T.x ∈ CutX W ts ∧ T.x + T.w ∈ CutX W ts := fun T hT =>
    ⟨Or.inr (Or.inr ⟨T, hT, Or.inl rfl⟩), Or.inr (Or.inr ⟨T, hT, Or.inr rfl⟩)⟩
  have cy : ∀ T ∈ ts, T.y ∈ CutY H ts ∧ T.y + T.h ∈ CutY H ts := fun T hT =>
    ⟨Or.inr (Or.inr ⟨T, hT, Or.inl rfl⟩), Or.inr (Or.inr ⟨T, hT, Or.inr rfl⟩)⟩
  have x0 : (0 : ℤ) ∈ CutX W ts := Or.inl rfl
  have xW : W ∈ CutX W ts := Or.inr (Or.inl rfl)
  have y0 : (0 : ℤ) ∈ CutY H ts := Or.inl rfl
  have yH : H ∈ CutY H ts := Or.inr (Or.inl rfl)
  have hXW : 0 ≤ X W := by rw [← hX0]; exact (hX.le_iff_le x0 xW).mpr hW
  have hYH : 0 ≤ Y H := by rw [← hY0]; exact (hY.le_iff_le y0 yH).mpr hH
  have hpos : ∀ T' ∈ ts.map (img X Y), 0 < T'.w ∧ 0 < T'.h := by
    intro T' hT'
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hT'
    have hp := hd.pos T hT
    have h1 := hX (cx T hT).1 (cx T hT).2 (by omega)
    have h2 := hY (cy T hT).1 (cy T hT).2 (by omega)
    simp only [img]; omega
  refine dissects_of_sep_area hXW hYH hpos ?_ ?_ ?_
  · intro T' hT' p hp
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hT'
    have hb := hd.bounds hT
    have h1 := (hX.le_iff_le x0 (cx T hT).1).mpr hb.1
    have h2 := (hY.le_iff_le y0 (cy T hT).1).mpr hb.2.1
    have h3 := (hX.le_iff_le (cx T hT).2 xW).mpr hb.2.2.1
    have h4 := (hY.le_iff_le (cy T hT).2 yH).mpr hb.2.2.2
    rw [hX0] at h1; rw [hY0] at h2
    simp only [img, Tile.cells, box, mem_product, mem_Ico] at hp ⊢
    omega
  · refine List.pairwise_map.mpr (hd.sep.imp_of_mem ?_)
    · intro T U hT hU hs
      unfold AlmostSq.Sep at hs ⊢
      simp only [img]
      rcases hs with h | h | h | h
      · have := (hX.le_iff_le (cx T hT).2 (cx U hU).1).mpr h; omega
      · have := (hX.le_iff_le (cx U hU).2 (cx T hT).1).mpr h; omega
      · have := (hY.le_iff_le (cy T hT).2 (cy U hU).1).mpr h; omega
      · have := (hY.le_iff_le (cy U hU).2 (cy T hT).1).mpr h; omega
  · have hb := balance hW hH hd X Y
    rw [hX0, hY0, sub_zero, sub_zero] at hb
    rw [List.map_map]
    exact hb

/-- A shift at scale `t`: cut line `a` moves to `t a + u a`. -/
def scaleShift (t : ℤ) (u : ℤ → ℤ) (a : ℤ) : ℤ := t * a + u a

/-- **Lemma 3 (Inflation).** If the scaled and shifted cut lines stay in order, the images of the
    squares dissect the new rectangle; a square whose width and height changes differ by one becomes
    an almost-square of size `t s + min δu δv`. -/
theorem inflation {W H : ℤ} (hW : 0 ≤ W) (hH : 0 ≤ H) {ts : List Tile} (hd : Dissects W H ts)
    (t : ℤ) (u v : ℤ → ℤ) (hu0 : u 0 = 0) (hv0 : v 0 = 0)
    (hX : StrictMonoOn (scaleShift t u) (CutX W ts))
    (hY : StrictMonoOn (scaleShift t v) (CutY H ts)) :
    Dissects (t * W + u W) (t * H + v H) (ts.map (img (scaleShift t u) (scaleShift t v))) ∧
    ∀ T ∈ ts, T.w = T.h →
      (u (T.x + T.w) - u T.x) - (v (T.y + T.h) - v T.y) = 1 ∨
        (u (T.x + T.w) - u T.x) - (v (T.y + T.h) - v T.y) = -1 →
      let T' := img (scaleShift t u) (scaleShift t v) T
      (T'.w = T'.h + 1 ∨ T'.h = T'.w + 1) ∧
        T'.size = t * T.w + min (u (T.x + T.w) - u T.x) (v (T.y + T.h) - v T.y) := by
  refine ⟨dissects_img hW hH hd _ _ (by simp [scaleShift, hu0]) (by simp [scaleShift, hv0]) hX hY,
    fun T _ hsq hε => ?_⟩
  simp only [img, Tile.size, scaleShift]
  have e1 : t * (T.x + T.w) + u (T.x + T.w) - (t * T.x + u T.x) = t * T.w + (u (T.x + T.w) - u T.x) := by
    ring
  have e2 : t * (T.y + T.h) + v (T.y + T.h) - (t * T.y + v T.y) = t * T.w + (v (T.y + T.h) - v T.y) := by
    rw [hsq]; ring
  rw [e1, e2]
  constructor
  · omega
  · exact min_add_add_left _ _ _

/-! ### The signed identity -/

/-- `∑ δu_i h_i = H u(W)` and `∑ w_i δv_i = W v(H)` for any dissection (first part of Corollary 7). -/
theorem shift_moments {W H : ℤ} (hW : 0 ≤ W) (hH : 0 ≤ H) {ts : List Tile} (hd : Dissects W H ts)
    (u v : ℤ → ℤ) (hu0 : u 0 = 0) (hv0 : v 0 = 0) :
    (ts.map (fun T => (u (T.x + T.w) - u T.x) * T.h)).sum = u W * H ∧
    (ts.map (fun T => T.w * (v (T.y + T.h) - v T.y))).sum = W * v H := by
  constructor
  · have := balance hW hH hd u id
    simp only [id, add_sub_cancel_left, hu0, sub_zero] at this
    exact this
  · have := balance hW hH hd id v
    simp only [id, add_sub_cancel_left, hv0, sub_zero] at this
    exact this

theorem list_sum_map_sub {α : Type*} (f g : α → ℤ) :
    ∀ l : List α, (l.map fun x => f x - g x).sum = (l.map f).sum - (l.map g).sum
  | [] => by simp
  | x :: r => by simp only [List.map_cons, List.sum_cons, list_sum_map_sub f g r]; ring

/-- **Corollary 7 (Signed identity).** For a dissection of a square of side `S` into squares and a
    shift with `u 0 = v 0 = 0`, `∑ ε_i s_i = S (u S - v S)`, where `ε_i = δu_i - δv_i`; for an
    inflation (`u S - v S = 1`) the right side is `S`. -/
theorem signed_identity {S : ℤ} (hS : 0 ≤ S) {ts : List Tile} (hd : Dissects S S ts)
    (hsq : ∀ T ∈ ts, T.w = T.h) (u v : ℤ → ℤ) (hu0 : u 0 = 0) (hv0 : v 0 = 0) :
    (ts.map (fun T => ((u (T.x + T.w) - u T.x) - (v (T.y + T.h) - v T.y)) * T.w)).sum =
      S * (u S - v S) := by
  obtain ⟨h1, h2⟩ := shift_moments hS hS hd u v hu0 hv0
  have e : ts.map (fun T => ((u (T.x + T.w) - u T.x) - (v (T.y + T.h) - v T.y)) * T.w) =
      ts.map (fun T => (u (T.x + T.w) - u T.x) * T.h - T.w * (v (T.y + T.h) - v T.y)) :=
    List.map_congr_left (fun T hT => by rw [← hsq T hT]; ring)
  rw [e, list_sum_map_sub, h1, h2]
  ring

end AlmostSq
