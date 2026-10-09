import LeanProofs.BalancedMast.Grid

/-!
# The 2048-leaf example: `M(2^11) ≤ 2^5` (Bordewich et al., Theorem 4.6 with `k = 3`)

Both trees cut at depth 4 into sixteen blocks of height 7. Block `i` of `S` holds the labels
`128 i + w`, `w < 128`, in order. The template tree of height 7 carries sixteen label-disjoint
8-caterpillars that use all 128 leaves (their Corollary 4.4); `pos j r` is the leaf of rank `r` in
caterpillar `j`, found by the recursion of their Lemma 4.3 (`balanced-mast/lean-aux/caterpillars.py`).
The cell of block `i` of `S` and block `j` of `T` is `{128 i + pos j r : r < 8}`; in `S` it is
caterpillar `j` of block `i`, and in `T` it is caterpillar `i` of block `j` read in reverse. So
each cell is a pair of anti-caterpillars, no three of its labels agree, and Lemma 4.5 gives
`mast(S, T) ≤ 2 · 16 = 32`.
-/

namespace BalancedMast

open Tree

def catTab : List (List ℕ) :=
  [[0, 1, 2, 7, 11, 20, 38, 86], [8, 9, 10, 15, 3, 21, 44, 92],
    [16, 17, 18, 23, 27, 4, 45, 93], [24, 25, 26, 31, 19, 5, 46, 94],
    [32, 33, 34, 39, 43, 52, 6, 118], [40, 41, 42, 47, 35, 53, 12, 124],
    [48, 49, 50, 55, 59, 36, 13, 125], [56, 57, 58, 63, 51, 37, 14, 126],
    [64, 65, 66, 71, 75, 84, 102, 22], [72, 73, 74, 79, 67, 85, 108, 28],
    [80, 81, 82, 87, 91, 68, 109, 29], [88, 89, 90, 95, 83, 69, 110, 30],
    [96, 97, 98, 103, 107, 116, 70, 54], [104, 105, 106, 111, 99, 117, 76, 60],
    [112, 113, 114, 119, 123, 100, 77, 61], [120, 121, 122, 127, 115, 101, 78, 62]]

def invTab : List (ℕ × ℕ) :=
  [(0, 0), (0, 1), (0, 2), (1, 4), (2, 5), (3, 5), (4, 6), (0, 3),
    (1, 0), (1, 1), (1, 2), (0, 4), (5, 6), (6, 6), (7, 6), (1, 3),
    (2, 0), (2, 1), (2, 2), (3, 4), (0, 5), (1, 5), (8, 7), (2, 3),
    (3, 0), (3, 1), (3, 2), (2, 4), (9, 7), (10, 7), (11, 7), (3, 3),
    (4, 0), (4, 1), (4, 2), (5, 4), (6, 5), (7, 5), (0, 6), (4, 3),
    (5, 0), (5, 1), (5, 2), (4, 4), (1, 6), (2, 6), (3, 6), (5, 3),
    (6, 0), (6, 1), (6, 2), (7, 4), (4, 5), (5, 5), (12, 7), (6, 3),
    (7, 0), (7, 1), (7, 2), (6, 4), (13, 7), (14, 7), (15, 7), (7, 3),
    (8, 0), (8, 1), (8, 2), (9, 4), (10, 5), (11, 5), (12, 6), (8, 3),
    (9, 0), (9, 1), (9, 2), (8, 4), (13, 6), (14, 6), (15, 6), (9, 3),
    (10, 0), (10, 1), (10, 2), (11, 4), (8, 5), (9, 5), (0, 7), (10, 3),
    (11, 0), (11, 1), (11, 2), (10, 4), (1, 7), (2, 7), (3, 7), (11, 3),
    (12, 0), (12, 1), (12, 2), (13, 4), (14, 5), (15, 5), (8, 6), (12, 3),
    (13, 0), (13, 1), (13, 2), (12, 4), (9, 6), (10, 6), (11, 6), (13, 3),
    (14, 0), (14, 1), (14, 2), (15, 4), (12, 5), (13, 5), (4, 7), (14, 3),
    (15, 0), (15, 1), (15, 2), (14, 4), (5, 7), (6, 7), (7, 7), (15, 3)]
/-- The leaf of rank `r` in caterpillar `j` of the template tree. -/
def pos (j r : ℕ) : ℕ := (catTab.getD j []).getD r 0

/-- The caterpillar and rank of leaf `w` of the template tree. -/
def cat (w : ℕ) : ℕ × ℕ := invTab.getD w (0, 0)

/-- The triples of `std h o`, computed by the recursion of `displays_node`. -/
def dstd : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, o, a, b, c => a == o && b == o && !(c == o)
  | h + 1, o, a, b, c =>
    (decide (o ≤ a ∧ a < o + 2 ^ h ∧ o ≤ b ∧ b < o + 2 ^ h) &&
      (!decide (o ≤ c ∧ c < o + 2 ^ h) || dstd h o a b c)) ||
    (decide (o + 2 ^ h ≤ a ∧ a < o + 2 ^ h + 2 ^ h ∧ o + 2 ^ h ≤ b ∧ b < o + 2 ^ h + 2 ^ h) &&
      (!decide (o + 2 ^ h ≤ c ∧ c < o + 2 ^ h + 2 ^ h) || dstd h (o + 2 ^ h) a b c))

lemma displays_std (h : ℕ) : ∀ o a b c : ℕ, c ∈ (std h o).L →
    ((std h o).Displays a b c ↔ dstd h o a b c = true) := by
  induction h with
  | zero =>
    intro o a b c _
    simp [std, Displays, subtrees, dstd, and_assoc]
  | succ h ih =>
    intro o a b c hc
    have e : std (h + 1) o = node (std h o) (std h (o + 2 ^ h)) := rfl
    rw [e] at hc ⊢
    rw [displays_node hc, imp_congr_right fun hc' => ih o a b c hc',
      imp_congr_right fun hc' => ih (o + 2 ^ h) a b c hc']
    simp only [dstd, mem_L_std, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', decide_eq_false_iff_not, imp_iff_not_or]
    tauto

/-! ## Finite facts about the template, checked by evaluation -/

lemma fact_inv : ∀ w < 128, pos (cat w).1 (cat w).2 = w ∧ (cat w).1 < 16 ∧ (cat w).2 < 8 := by
  decide +kernel

lemma fact_pos : ∀ j < 16, ∀ r < 8, cat (pos j r) = (j, r) ∧ pos j r < 128 := by
  decide +kernel

/-- The caterpillar facts, as one Boolean computation. -/
def catOK : Bool :=
  (List.range 16).all fun j => (List.range 8).all fun u => (List.range 8).all fun v =>
    (List.range 8).all fun w =>
      u == v || u == w || v == w || dstd 7 0 (pos j u) (pos j v) (pos j w) == decide (u < w ∧ v < w)

theorem catOK_true : catOK = true := by decide +kernel

/-- Each `pos j ·` is a caterpillar: among three of its leaves, the two of lower rank form the
displayed pair. -/
lemma fact_cat : ∀ j < 16, ∀ u < 8, ∀ v < 8, ∀ w < 8, u ≠ v → u ≠ w → v ≠ w →
    (dstd 7 0 (pos j u) (pos j v) (pos j w) = true ↔ u < w ∧ v < w) := by
  intro j hj u hu v hv w hw huv huw hvw
  have h := catOK_true
  simp only [catOK, List.all_eq_true, List.mem_range] at h
  have := h j hj u hu v hv w hw
  simp only [Bool.or_eq_true, beq_iff_eq, huv, huw, hvw, false_or] at this
  rw [this]; simp

/-- A caterpillar and its reverse agree on no three labels. -/
lemma fact_reverse : ∀ x < 8, ∀ y < 8, ∀ z < 8, x ≠ y → x ≠ z → y ≠ z →
    ¬((x < z ∧ y < z ↔ 7 - x < 7 - z ∧ 7 - y < 7 - z) ∧
      (x < y ∧ z < y ↔ 7 - x < 7 - y ∧ 7 - z < 7 - y) ∧
      (y < x ∧ z < x ↔ 7 - y < 7 - x ∧ 7 - z < 7 - x)) := by
  intro x hx y hy z hz hxy hxz hyz ⟨h₁, h₂, h₃⟩
  -- the label of largest rank is last in one of the three triples
  rcases (by omega : (x < z ∧ y < z) ∨ (x < y ∧ z < y) ∨ (y < x ∧ z < x)) with h | h | h
  · have := h₁.1 h; omega
  · have := h₂.1 h; omega
  · have := h₃.1 h; omega

/-! ## The two trees -/

def fS (i w : ℕ) : ℕ := 128 * i + w

def fT (j w : ℕ) : ℕ := 128 * (cat w).1 + pos j (7 - (cat w).2)

def SA (i : ℕ) : Tree ℕ := (std 7 0).map (fS i)

def TB (j : ℕ) : Tree ℕ := (std 7 0).map (fT j)

def S11 : Tree ℕ := (std 4 0).bind SA

def T11 : Tree ℕ := (std 4 0).bind TB

lemma mem_std7 {w : ℕ} : w ∈ (std 7 0).L ↔ w < 128 := by simp [mem_L_std]

lemma mem_std4 {i : ℕ} : i ∈ (std 4 0).L ↔ i < 16 := by simp [mem_L_std]

lemma pos_ne {j r r' : ℕ} (hj : j < 16) (hr : r < 8) (hr' : r' < 8) (h : r ≠ r') :
    pos j r ≠ pos j r' := fun e => h (by
  have := congrArg cat e
  rw [(fact_pos j hj r hr).1, (fact_pos j hj r' hr').1] at this
  exact (Prod.ext_iff.1 this).2)

lemma injS (i : ℕ) : Set.InjOn (fS i) (std 7 0).L := fun w _ w' _ h => by
  simp only [fS] at h; omega

lemma injT {j : ℕ} (hj : j < 16) : Set.InjOn (fT j) (std 7 0).L := by
  intro w hw w' hw' h
  have hw := mem_std7.1 hw
  have hw' := mem_std7.1 hw'
  obtain ⟨p, c1, c2⟩ := fact_inv w hw
  obtain ⟨p', c1', c2'⟩ := fact_inv w' hw'
  obtain ⟨q, q'⟩ := fact_pos j hj (7 - (cat w).2) (by omega)
  obtain ⟨r, r'⟩ := fact_pos j hj (7 - (cat w').2) (by omega)
  simp only [fT] at h
  have e1 : (cat w).1 = (cat w').1 := by omega
  have e2 : pos j (7 - (cat w).2) = pos j (7 - (cat w').2) := by omega
  have e3 := congrArg cat e2
  rw [q, r] at e3
  have e4 : (cat w).2 = (cat w').2 := by have := (Prod.ext_iff.1 e3).2; omega
  rw [← p, ← p', e1, e4]

lemma disjS : (std 4 0).BlocksDisjoint SA := by
  intro z _ z' _ hne
  refine Finset.disjoint_left.2 fun x hx hx' => hne ?_
  obtain ⟨w, hw, rfl⟩ := mem_L_map.1 hx
  obtain ⟨w', hw', e⟩ := mem_L_map.1 hx'
  have := mem_std7.1 hw; have := mem_std7.1 hw'
  simp only [fS] at e; omega

lemma disjT : (std 4 0).BlocksDisjoint TB := by
  intro z hz z' hz' hne
  refine Finset.disjoint_left.2 fun x hx hx' => hne ?_
  have hz := mem_std4.1 hz
  have hz' := mem_std4.1 hz'
  obtain ⟨w, hw, rfl⟩ := mem_L_map.1 hx
  obtain ⟨w', hw', e⟩ := mem_L_map.1 hx'
  have hw := mem_std7.1 hw
  have hw' := mem_std7.1 hw'
  obtain ⟨_, _, c2⟩ := fact_inv w hw
  obtain ⟨_, _, c2'⟩ := fact_inv w' hw'
  obtain ⟨q, q'⟩ := fact_pos z hz (7 - (cat w).2) (by omega)
  obtain ⟨r, r'⟩ := fact_pos z' hz' (7 - (cat w').2) (by omega)
  simp only [fT] at e
  have e2 : pos z' (7 - (cat w').2) = pos z (7 - (cat w).2) := by omega
  have e3 := congrArg cat e2
  rw [q, r] at e3
  exact (Prod.ext_iff.1 e3).1.symm

lemma bal_S11 : Bal 11 S11 := (bal_std 4 0).bind fun i _ => (bal_std 7 0).map (fS i)

lemma bal_T11 : Bal 11 T11 := (bal_std 4 0).bind fun j _ => (bal_std 7 0).map (fT j)

lemma phylo_S11 : S11.Phylo :=
  phylo_bind (phylo_std 4 0) (fun i _ => phylo_map (injS i) (phylo_std 7 0)) disjS

lemma phylo_T11 : T11.Phylo :=
  phylo_bind (phylo_std 4 0) (fun j hj => phylo_map (injT (mem_std4.1 hj)) (phylo_std 7 0)) disjT

lemma mem_S11 {x : ℕ} : x ∈ S11.L ↔ x < 2048 := by
  simp only [S11, mem_L_bind, SA, mem_L_map, mem_std4, mem_std7, fS]
  constructor
  · rintro ⟨i, hi, w, hw, rfl⟩; omega
  · intro hx; exact ⟨x / 128, by omega, x % 128, by omega, by omega⟩

lemma mem_T11 {x : ℕ} : x ∈ T11.L ↔ x < 2048 := by
  simp only [T11, mem_L_bind, TB, mem_L_map, mem_std4, mem_std7]
  constructor
  · rintro ⟨j, hj, w, hw, rfl⟩
    obtain ⟨_, c1, c2⟩ := fact_inv w hw
    have := (fact_pos j hj (7 - (cat w).2) (by omega)).2
    simp only [fT]; omega
  · intro hx
    obtain ⟨p, c1, c2⟩ := fact_inv (x % 128) (by omega)
    obtain ⟨q, q'⟩ := fact_pos (x / 128) (by omega) (7 - (cat (x % 128)).2) (by omega)
    refine ⟨(cat (x % 128)).1, c1, pos (x / 128) (7 - (cat (x % 128)).2), q', ?_⟩
    simp only [fT, q]
    rw [show 7 - (7 - (cat (x % 128)).2) = (cat (x % 128)).2 by omega, p]
    omega

lemma L_S11_T11 : S11.L = T11.L := by ext x; rw [mem_S11, mem_T11]

/-! ## Every cell is a pair of anti-caterpillars -/

lemma cell {i j x : ℕ} (hj : j < 16) (hS : x ∈ (SA i).L) (hT : x ∈ (TB j).L) :
    ∃ ρ < 8, x = fS i (pos j ρ) ∧ x = fT j (pos i (7 - ρ)) := by
  obtain ⟨w, hw, rfl⟩ := mem_L_map.1 hS
  obtain ⟨w', hw', e⟩ := mem_L_map.1 hT
  have hw := mem_std7.1 hw
  have hw' := mem_std7.1 hw'
  obtain ⟨p', c1', c2'⟩ := fact_inv w' hw'
  have q' := (fact_pos j hj (7 - (cat w').2) (by omega)).2
  simp only [fS, fT] at e ⊢
  have ei : (cat w').1 = i := by omega
  refine ⟨7 - (cat w').2, by omega, by omega, ?_⟩
  rw [show 7 - (7 - (cat w').2) = (cat w').2 by omega, ← ei, p']
  omega

lemma displays_S11 {i j ρa ρb ρc : ℕ} (hi : i < 16) (hj : j < 16) (ha : ρa < 8) (hb : ρb < 8)
    (hc : ρc < 8) (hab : ρa ≠ ρb) (hac : ρa ≠ ρc) (hbc : ρb ≠ ρc) :
    S11.Displays (fS i (pos j ρa)) (fS i (pos j ρb)) (fS i (pos j ρc)) ↔ ρa < ρc ∧ ρb < ρc := by
  have m : ∀ ρ < 8, pos j ρ ∈ (std 7 0).L := fun ρ hρ => mem_std7.2 (fact_pos j hj ρ hρ).2
  rw [S11, displays_bind_block disjS (mem_std4.2 hi) (mem_L_map.2 ⟨_, m ρa ha, rfl⟩)
    (mem_L_map.2 ⟨_, m ρc hc, rfl⟩), SA,
    displays_map (injS i) (m ρa ha) (m ρb hb) (m ρc hc) (pos_ne hj ha hb hab),
    displays_std 7 0 _ _ _ (m ρc hc)]
  exact fact_cat j hj ρa ha ρb hb ρc hc hab hac hbc

lemma displays_T11 {i j σa σb σc : ℕ} (hi : i < 16) (hj : j < 16) (ha : σa < 8) (hb : σb < 8)
    (hc : σc < 8) (hab : σa ≠ σb) (hac : σa ≠ σc) (hbc : σb ≠ σc) :
    T11.Displays (fT j (pos i σa)) (fT j (pos i σb)) (fT j (pos i σc)) ↔ σa < σc ∧ σb < σc := by
  have m : ∀ σ < 8, pos i σ ∈ (std 7 0).L := fun σ hσ => mem_std7.2 (fact_pos i hi σ hσ).2
  rw [T11, displays_bind_block disjT (mem_std4.2 hj) (mem_L_map.2 ⟨_, m σa ha, rfl⟩)
    (mem_L_map.2 ⟨_, m σc hc, rfl⟩), TB,
    displays_map (injT hj) (m σa ha) (m σb hb) (m σc hc) (pos_ne hi ha hb hab),
    displays_std 7 0 _ _ _ (m σc hc)]
  exact fact_cat i hi σa ha σb hb σc hc hab hac hbc

lemma cellsSmall_11 : CellsSmall S11 T11 4 4 := by
  intro s hs t ht Y hY hA
  rw [S11, blocks_bind (bal_std 4 0), labels_std] at hs
  rw [T11, blocks_bind (bal_std 4 0), labels_std] at ht
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hs
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ht
  rw [List.mem_range'_1] at hi hj
  replace hi : i < 16 := by omega
  replace hj : j < 16 := by omega
  by_contra hlt
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.1 (not_le.1 hlt)
  have get : ∀ x ∈ Y, ∃ ρ < 8, x = fS i (pos j ρ) ∧ x = fT j (pos i (7 - ρ)) := fun x hx =>
    cell hj (Finset.mem_inter.1 (hY hx)).1 (Finset.mem_inter.1 (hY hx)).2
  obtain ⟨ρa, ra, ea, ea'⟩ := get a ha
  obtain ⟨ρb, rb, eb, eb'⟩ := get b hb
  obtain ⟨ρc, rc, ec, ec'⟩ := get c hc
  have nab : ρa ≠ ρb := fun e => hab (by rw [ea, eb, e])
  have nac : ρa ≠ ρc := fun e => hac (by rw [ea, ec, e])
  have nbc : ρb ≠ ρc := fun e => hbc (by rw [eb, ec, e])
  have tri : ∀ x ∈ Y, ∀ y ∈ Y, ∀ z ∈ Y, ∀ ρx ρy ρz, ρx < 8 → ρy < 8 → ρz < 8 →
      ρx ≠ ρy → ρx ≠ ρz → ρy ≠ ρz →
      x = fS i (pos j ρx) → x = fT j (pos i (7 - ρx)) →
      y = fS i (pos j ρy) → y = fT j (pos i (7 - ρy)) →
      z = fS i (pos j ρz) → z = fT j (pos i (7 - ρz)) →
      (ρx < ρz ∧ ρy < ρz ↔ 7 - ρx < 7 - ρz ∧ 7 - ρy < 7 - ρz) := by
    intro x hx y hy z hz ρx ρy ρz hx8 hy8 hz8 nxy nxz nyz ex ex' ey ey' ez ez'
    have h := hA.2 x hx y hy z hz
    rw [ex, ey, ez] at h
    rw [displays_S11 hi hj hx8 hy8 hz8 nxy nxz nyz] at h
    rw [← ex, ← ey, ← ez, ex', ey', ez'] at h
    rwa [displays_T11 hi hj (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      at h
  exact fact_reverse ρa ra ρb rb ρc rc nab nac nbc
    ⟨tri a ha b hb c hc ρa ρb ρc ra rb rc nab nac nbc ea ea' eb eb' ec ec',
     tri a ha c hc b hb ρa ρc ρb ra rc rb nac nab nbc.symm ea ea' ec ec' eb eb',
     tri b hb c hc a ha ρb ρc ρa rb rc ra nbc nab.symm nac.symm eb eb' ec ec' ea ea'⟩

/-- **`M(2^11) ≤ 2^5`.** -/
theorem M_eleven : M 11 ≤ 2 ^ 5 :=
  (M_le bal_S11 bal_T11 phylo_S11 phylo_T11 L_S11_T11).trans
    (mast_le_of_cellsSmall phylo_S11 phylo_T11 cellsSmall_11)

/-- **Theorem 1.1(2).** `M(n) ≤ 2^10 n^(5/11)` for `n = 2^m`. -/
theorem M_upper (m : ℕ) : (M m : ℝ) ≤ 2 ^ 10 * (2 : ℝ) ^ ((5 : ℝ) * m / 11) :=
  M_le_of_M11 M_eleven m

/-- **Theorem 1.1(2).** `β ≤ 5/11`. -/
theorem beta_le_five_elevenths : beta ≤ 5 / 11 := beta_le_of_M11 M_eleven

end BalancedMast
