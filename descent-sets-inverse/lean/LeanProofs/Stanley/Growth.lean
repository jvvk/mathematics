/-
  Stanley, MathOverflow 486548. Part F. Two standard Young tableaux of the same shape come from a
  permutation (the existence half of Robinson–Schensted, with both descent properties), proved with
  Fomin's growth diagrams written on edge labels.

  A standard Young tableau with `n` entries is encoded by its row word `r : ℕ → ℕ` (`r i` is the
  row, from `0`, of the entry `i + 1`); it is a lattice word, and its descent set (entries `i + 1`
  with `i + 2` in a strictly lower row) is `asc n r = {i | r i < r (i + 1)}`.

  The growth diagram is an `n × n` grid. Each unit edge carries a label: `some r` (the shape grows
  by a box in row `r` along the edge) or `none`. The top edges carry `u` (the tableau `Q`), the right
  edges carry `v` (the tableau `P`), and every cell obeys Fomin's backward rule `back`, which reads the
  labels of the cell's top and right edges and returns those of its bottom and left edges and whether
  the cell holds a cross. Writing shapes as integer row-length vectors, every corner shape is a
  partition (`lam_isPart`), so the left and bottom boundaries are empty, every row and column holds
  exactly one cross, and the crosses form a permutation `w`. A local invariant on two adjacent columns
  (`local_inv`) gives `D(w) = asc u`; the rule is symmetric, so the transposed grid gives
  `D(w⁻¹) = asc v`.
-/
import LeanProofs.Stanley.Count

namespace Stanley

namespace Growth

open Finset

/-- Fomin's backward local rule on edge labels: from the labels `b` (top edge) and `d` (right
edge) of a cell, the labels of the bottom and left edges and whether the cell holds a cross. -/
def back : Option ℕ → Option ℕ → Option ℕ × Option ℕ × Bool
  | none, none => (none, none, false)
  | none, some s => (none, some s, false)
  | some r, none => (some r, none, false)
  | some r, some s =>
    if r = s then (if r = 0 then (none, none, true) else (some (r - 1), some (r - 1), false))
    else (some r, some s, false)

@[simp] theorem back_nn : back none none = (none, none, false) := rfl
@[simp] theorem back_ns (s : ℕ) : back none (some s) = (none, some s, false) := rfl
@[simp] theorem back_sn (r : ℕ) : back (some r) none = (some r, none, false) := rfl
@[simp] theorem back_zero : back (some 0) (some 0) = (none, none, true) := by simp [back]
@[simp] theorem back_succ (k : ℕ) : back (some (k + 1)) (some (k + 1)) = (some k, some k, false) := by
  simp [back]
theorem back_ne {r s : ℕ} (h : r ≠ s) : back (some r) (some s) = (some r, some s, false) := by
  simp [back, h]

/-- Case analysis of `back` on two labels. -/
theorem back_cases (b d : Option ℕ) :
    (b = none ∧ back b d = (none, d, false)) ∨
    (∃ r, b = some r ∧ d = none ∧ back b d = (some r, none, false)) ∨
    (∃ r s, b = some r ∧ d = some s ∧ r ≠ s ∧ back b d = (some r, some s, false)) ∨
    (b = some 0 ∧ d = some 0 ∧ back b d = (none, none, true)) ∨
    (∃ k, b = some (k + 1) ∧ d = some (k + 1) ∧ back b d = (some k, some k, false)) := by
  rcases b with _ | r
  · left; rcases d with _ | s <;> simp
  · rcases d with _ | s
    · right; left; exact ⟨r, rfl, rfl, rfl⟩
    · by_cases h : r = s
      · subst h
        rcases r with _ | k
        · right; right; right; left; simp
        · right; right; right; right; exact ⟨k, rfl, rfl, by simp⟩
      · right; right; left; exact ⟨r, s, rfl, rfl, h, back_ne h⟩

theorem back_symm (b d : Option ℕ) :
    back d b = ((back b d).2.1, (back b d).1, (back b d).2.2) := by
  rcases b with _ | r <;> rcases d with _ | s
  · rfl
  · rfl
  · rfl
  · by_cases h : r = s
    · subst h; rcases r with _ | k <;> simp
    · rw [back_ne h, back_ne (Ne.symm h)]

/-- Order key on labels: `none` below every row. -/
def key : Option ℕ → ℤ
  | none => -1
  | some r => r

/-- **The local invariant.** Two adjacent cells in one row of the grid, the right one read first:
whether the left column's label is below the right column's is preserved from the top edges to
the bottom edges, as long as neither pair of labels is `none, none`. -/
theorem local_inv (A' B' d : Option ℕ) (h1 : ¬(A' = none ∧ B' = none))
    (h2 : ¬((back A' (back B' d).2.1).1 = none ∧ (back B' d).1 = none)) :
    key (back A' (back B' d).2.1).1 < key (back B' d).1 ↔ key A' < key B' := by
  have kge : ∀ o, -1 ≤ key o := by intro o; cases o <;> simp [key]
  have kn : key none = -1 := rfl
  have ks : ∀ r : ℕ, key (some r) = r := fun _ => rfl
  rcases B' with _ | b
  · have := kge A'; have := kge (back A' d).1
    rcases d with _ | c <;> simp only [back_nn, back_ns] at * <;> rw [kn] <;> constructor <;>
      intro <;> omega
  rcases d with _ | c
  · simp only [back_sn]; rcases A' with _ | a <;> simp only [back_nn, back_sn]
  by_cases hbc : b = c
  · subst hbc
    rcases b with _ | k
    · simp only [back_zero] at h2 ⊢
      rcases A' with _ | a
      · simp at h2
      · simp only [back_sn, ks, kn] <;> try (constructor <;> intro <;> omega)
    · simp only [back_succ] at h2 ⊢
      rcases A' with _ | a
      · simp only [back_ns, ks, kn] <;> try (constructor <;> intro <;> omega)
      · by_cases hak : a = k
        · subst hak
          rcases a with _ | j
          · simp only [back_zero, ks, kn] <;> try (constructor <;> intro <;> omega)
          · simp only [back_succ, ks] <;> try (constructor <;> intro <;> omega)
        · simp only [back_ne hak, ks] <;> try (constructor <;> intro <;> omega)
  · simp only [back_ne hbc] at h2 ⊢
    rcases A' with _ | a
    · simp only [back_ns, ks, kn] <;> try (constructor <;> intro <;> omega)
    · by_cases hac : a = c
      · subst hac
        rcases a with _ | j
        · simp only [back_zero, ks, kn] <;> try (constructor <;> intro <;> omega)
        · simp only [back_succ, ks] <;> try (constructor <;> intro <;> omega)
      · simp only [back_ne hac, ks]

theorem back_none_left (d : Option ℕ) : (back none d).1 = none := by
  rcases d with _ | s <;> rfl

theorem back_cross (b d : Option ℕ) :
    (back b d).2.2 = true ↔ (b ≠ none ∧ (back b d).1 = none) := by
  rcases b with _ | r <;> rcases d with _ | s
  · simp
  · simp
  · simp
  · by_cases h : r = s
    · subst h; rcases r with _ | k <;> simp
    · simp [back_ne h]

/-- Indicator vector of a label. -/
def e (o : Option ℕ) (r : ℕ) : ℤ := if o = some r then 1 else 0

theorem e_nonneg (o : Option ℕ) (r : ℕ) : 0 ≤ e o r := by unfold e; split_ifs <;> norm_num

/-- The shape is conserved around a cell: top + left = right + bottom. -/
theorem back_content (b d : Option ℕ) (r : ℕ) :
    e b r + e (back b d).2.1 r = e d r + e (back b d).1 r := by
  rcases b with _ | x <;> rcases d with _ | y
  · rfl
  · simp only [back_ns]; ring
  · simp only [back_sn]; ring
  · by_cases h : x = y
    · subst h; rcases x with _ | k
      · simp [e]
      · simp only [back_succ, e, Option.some.injEq]
    · simp only [back_ne h]; ring

/-- Integer vectors that are partitions. -/
def IsPart (f : ℕ → ℤ) : Prop := (∀ r, 0 ≤ f r) ∧ ∀ r, f (r + 1) ≤ f r

/-- Removing the boxes of the bottom-left path of a cell keeps a partition. -/
theorem back_isPart {ρ : ℕ → ℤ} (b d : Option ℕ) (hρ : IsPart ρ)
    (hb : IsPart (fun r => ρ r - e b r)) (hd : IsPart (fun r => ρ r - e d r)) :
    IsPart (fun r => ρ r - e b r - e (back b d).2.1 r) := by
  rcases b with _ | x <;> rcases d with _ | y
  · simpa [e] using hρ
  · simpa [e] using hd
  · simpa [e] using hb
  · by_cases hxy : x = y
    · subst hxy
      rcases x with _ | k
      · simpa [e] using hb
      · simp only [back_succ]
        refine ⟨fun j => ?_, fun j => ?_⟩
        · have h1 := hρ.2 j; have h2 := hb.1 (j + 1); have h3 := hb.1 j
          simp only [e, Option.some.injEq] at h1 h2 h3 ⊢
          split_ifs at h1 h2 h3 ⊢ <;> omega
        · have h1 := hρ.2 j; have h2 := hb.2 j; have h3 := hb.1 j
          have h4 := hρ.2 (j + 1); have h5 := hb.1 (j + 1)
          simp only [e, Option.some.injEq] at h1 h2 h3 h4 h5 ⊢
          split_ifs at h1 h2 h3 h4 h5 ⊢ <;> omega
    · simp only [back_ne hxy]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have h2 := hb.1 j; have h3 := hd.1 j
        simp only [e, Option.some.injEq] at h2 h3 ⊢
        split_ifs at h2 h3 ⊢ <;> omega
      · have h1 := hρ.2 j; have h2 := hb.2 j; have h3 := hd.2 j
        have h4 := hb.1 j; have h5 := hd.1 j
        simp only [e, Option.some.injEq] at h1 h2 h3 h4 h5 ⊢
        split_ifs at h1 h2 h3 h4 h5 ⊢ <;> omega

/-- Row counts of the first `k` letters of a word. -/
def cnt (u : ℕ → ℕ) (k r : ℕ) : ℤ := ∑ i ∈ range k, e (some (u i)) r

/-- Lattice word of length `n`: every prefix has partition content. -/
def Lattice (n : ℕ) (u : ℕ → ℕ) : Prop := ∀ k ≤ n, ∀ r, cnt u k (r + 1) ≤ cnt u k r

theorem cnt_nonneg (u : ℕ → ℕ) (k r : ℕ) : 0 ≤ cnt u k r :=
  Finset.sum_nonneg fun i _ => e_nonneg _ _

theorem cnt_succ (u : ℕ → ℕ) (k r : ℕ) : cnt u (k + 1) r = cnt u k r + e (some (u k)) r := by
  simp [cnt, Finset.sum_range_succ]

/-- Ascent set of a row word: the descent set of its tableau. -/
def asc (n : ℕ) (u : ℕ → ℕ) : Finset ℕ := (range (n - 1)).filter (fun i => u i < u (i + 1))

/-- A growth diagram with top word `u` and right word `v`. `H i j`: edge from corner `(i, j)` to
`(i + 1, j)`; `V i j`: edge from `(i, j)` to `(i, j + 1)`; `X i j`: cross in cell `(i, j)`. -/
structure Grid (n : ℕ) (u v : ℕ → ℕ) where
  H : ℕ → ℕ → Option ℕ
  V : ℕ → ℕ → Option ℕ
  X : ℕ → ℕ → Bool
  top : ∀ i < n, H i n = some (u i)
  right : ∀ j < n, V n j = some (v j)
  cell : ∀ i < n, ∀ j < n, back (H i (j + 1)) (V (i + 1) j) = (H i j, V i j, X i j)

variable {n : ℕ} {u v : ℕ → ℕ}

/-- The transposed diagram. -/
def Grid.tr (g : Grid n u v) : Grid n v u where
  H i j := g.V j i
  V i j := g.H j i
  X i j := g.X j i
  top i hi := g.right i hi
  right j hj := g.top j hj
  cell i hi j hj := by
    rw [back_symm, g.cell j hj i hi]

theorem Grid.cell_H (g : Grid n u v) {i j : ℕ} (hi : i < n) (hj : j < n) :
    g.H i j = (back (g.H i (j + 1)) (g.V (i + 1) j)).1 := by rw [g.cell i hi j hj]

theorem Grid.cell_V (g : Grid n u v) {i j : ℕ} (hi : i < n) (hj : j < n) :
    g.V i j = (back (g.H i (j + 1)) (g.V (i + 1) j)).2.1 := by rw [g.cell i hi j hj]

theorem Grid.cell_X (g : Grid n u v) {i j : ℕ} (hi : i < n) (hj : j < n) :
    g.X i j = (back (g.H i (j + 1)) (g.V (i + 1) j)).2.2 := by rw [g.cell i hi j hj]

/-- The shape at corner `(i, j)`, read down the vertical line `i` from the top. -/
def Grid.lam (g : Grid n u v) (i j : ℕ) (r : ℕ) : ℤ :=
  cnt u i r - ∑ k ∈ Ico j n, e (g.V i k) r

theorem Grid.lam_succ (g : Grid n u v) (i : ℕ) {j : ℕ} (hj : j < n) (r : ℕ) :
    g.lam i j r = g.lam i (j + 1) r - e (g.V i j) r := by
  unfold Grid.lam
  rw [Finset.sum_eq_sum_Ico_succ_bot hj]
  ring

/-- Moving right along a horizontal edge adds its box. -/
theorem Grid.lam_horiz (g : Grid n u v) {i : ℕ} (hi : i < n) :
    ∀ t ≤ n, ∀ r, g.lam (i + 1) (n - t) r = g.lam i (n - t) r + e (g.H i (n - t)) r := by
  intro t
  induction t with
  | zero =>
    intro _ r
    simp only [Nat.sub_zero, Grid.lam, Finset.Ico_self, Finset.sum_empty, sub_zero, cnt_succ,
      g.top i hi]
  | succ t ih =>
    intro ht r
    have hj : n - (t + 1) < n := by omega
    have hj1 : n - (t + 1) + 1 = n - t := by omega
    rw [g.lam_succ (i + 1) hj, g.lam_succ i hj, hj1, ih (by omega) r]
    have hc := back_content (g.H i (n - (t + 1) + 1)) (g.V (i + 1) (n - (t + 1))) r
    rw [← g.cell_V hi hj, ← g.cell_H hi hj, hj1] at hc
    linarith

theorem isPart_cnt {u : ℕ → ℕ} (hu : Lattice n u) {k : ℕ} (hk : k ≤ n) : IsPart (cnt u k) :=
  ⟨fun r => cnt_nonneg u k r, fun r => hu k hk r⟩

theorem cnt_split (u : ℕ → ℕ) {j : ℕ} (hj : j ≤ n) (r : ℕ) :
    cnt u n r = cnt u j r + ∑ k ∈ Ico j n, e (some (u k)) r := by
  unfold cnt
  rw [Finset.sum_range_add_sum_Ico _ hj]

/-- **Every corner shape is a partition.** -/
theorem Grid.lam_isPart (g : Grid n u v) (hu : Lattice n u) (hv : Lattice n v)
    (huv : ∀ r, cnt u n r = cnt v n r) :
    ∀ s ≤ n, ∀ t ≤ n, IsPart (g.lam (n - s) (n - t)) := by
  intro s
  induction s with
  | zero =>
    intro _ t ht
    have hlam : g.lam (n - 0) (n - t) = cnt v (n - t) := by
      funext r
      have hs := cnt_split v (show n - t ≤ n by omega) r
      have hsum : ∑ k ∈ Ico (n - t) n, e (g.V n k) r = ∑ k ∈ Ico (n - t) n, e (some (v k)) r :=
        Finset.sum_congr rfl fun k hk => by rw [g.right k (Finset.mem_Ico.mp hk).2]
      simp only [Nat.sub_zero, Grid.lam, hsum, huv r]
      linarith
    rw [hlam]
    exact isPart_cnt hv (by omega)
  | succ s ihs =>
    intro hsn t
    induction t with
    | zero =>
      intro _
      have hlam : g.lam (n - (s + 1)) (n - 0) = cnt u (n - (s + 1)) := by
        funext r; simp [Grid.lam]
      rw [hlam]
      exact isPart_cnt hu (by omega)
    | succ t iht =>
      intro ht
      by_cases hs : s + 1 ≤ n
      · set i := n - (s + 1) with hi_def
        set j := n - (t + 1) with hj_def
        have hi : i < n := by omega
        have hj : j < n := by omega
        have hi1 : i + 1 = n - s := by omega
        have hj1 : j + 1 = n - t := by omega
        -- ρ = lam (i+1) (j+1); lam i (j+1) = ρ - e b; lam (i+1) j = ρ - e d
        have hρ : IsPart (g.lam (i + 1) (j + 1)) := by
          rw [hi1, hj1]; exact ihs (by omega) t (by omega)
        have hb : IsPart (fun r => g.lam (i + 1) (j + 1) r - e (g.H i (j + 1)) r) := by
          have h := iht (by omega)
          have hh := g.lam_horiz hi t (by omega)
          rw [← hj1] at hh
          have : (fun r => g.lam (i + 1) (j + 1) r - e (g.H i (j + 1)) r) = g.lam i (j + 1) := by
            funext r; rw [hh r]; ring
          rw [this, hj1]; exact h
        have hd : IsPart (fun r => g.lam (i + 1) (j + 1) r - e (g.V (i + 1) j) r) := by
          have h := ihs (by omega) (t + 1) ht
          rw [← hi1] at h
          have : (fun r => g.lam (i + 1) (j + 1) r - e (g.V (i + 1) j) r) = g.lam (i + 1) j := by
            funext r; rw [g.lam_succ (i + 1) hj r]
          rw [this]; exact h
        have key := back_isPart (g.H i (j + 1)) (g.V (i + 1) j) hρ hb hd
        have : (fun r => g.lam (i + 1) (j + 1) r - e (g.H i (j + 1)) r -
            e (back (g.H i (j + 1)) (g.V (i + 1) j)).2.1 r) = g.lam i j := by
          funext r
          have hh := g.lam_horiz hi t (by omega) r
          rw [← hj1] at hh
          rw [g.lam_succ i hj r, ← g.cell_V hi hj, hh]; ring
        rw [this] at key; exact key
      · have h0 : n - (s + 1) = n - s := by omega
        rw [h0]; exact ihs (by omega) (t + 1) ht

/-- The left boundary of the diagram is empty. -/
theorem Grid.V_zero (g : Grid n u v) (hu : Lattice n u) (hv : Lattice n v)
    (huv : ∀ r, cnt u n r = cnt v n r) {j : ℕ} (hj : j < n) : g.V 0 j = none := by
  have hp := (g.lam_isPart hu hv huv n le_rfl (n - j) (by omega)).1
  simp only [Nat.sub_self, Nat.sub_sub_self hj.le, Grid.lam, cnt, Finset.range_zero,
    Finset.sum_empty, zero_sub, Left.nonneg_neg_iff] at hp
  have hz : ∀ r, ∑ k ∈ Ico j n, e (g.V 0 k) r = 0 := fun r =>
    le_antisymm (hp r) (Finset.sum_nonneg fun k _ => e_nonneg _ _)
  rcases hV : g.V 0 j with _ | r
  · rfl
  · have h := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => e_nonneg (g.V 0 k) r)).mp (hz r) j
      (Finset.mem_Ico.mpr ⟨le_rfl, hj⟩)
    simp [e, hV] at h

theorem cnt_comm_hyp (huv : ∀ r, cnt u n r = cnt v n r) : ∀ r, cnt v n r = cnt u n r :=
  fun r => (huv r).symm

/-- The bottom boundary of the diagram is empty. -/
theorem Grid.H_zero (g : Grid n u v) (hu : Lattice n u) (hv : Lattice n v)
    (huv : ∀ r, cnt u n r = cnt v n r) {i : ℕ} (hi : i < n) : g.H i 0 = none :=
  g.tr.V_zero hv hu (cnt_comm_hyp huv) hi

/-- Going down a column, an empty label stays empty. -/
theorem Grid.H_none_down (g : Grid n u v) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j < n)
    (h : g.H i (j + 1) = none) : g.H i j = none := by
  rw [g.cell_H hi hj, h, back_none_left]

theorem Grid.H_none_le (g : Grid n u v) {i : ℕ} (hi : i < n) {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ n)
    (h : g.H i k = none) : g.H i j = none := by
  induction k, hjk using Nat.le_induction with
  | base => exact h
  | succ k hjk ih => exact ih (by omega) (g.H_none_down hi (by omega) h)

/-- The height of the cross in column `i`. -/
noncomputable def Grid.col (g : Grid n u v) (i : ℕ) : ℕ :=
  Nat.findGreatest (fun j => g.H i j = none) n

theorem Grid.H_none_iff (g : Grid n u v) (hu : Lattice n u) (hv : Lattice n v)
    (huv : ∀ r, cnt u n r = cnt v n r) {i : ℕ} (hi : i < n) {j : ℕ} (hj : j ≤ n) :
    g.H i j = none ↔ j ≤ g.col i := by
  constructor
  · intro h; exact Nat.le_findGreatest hj h
  · intro h
    have h0 : g.H i 0 = none := g.H_zero hu hv huv hi
    have hc : g.H i (g.col i) = none :=
      Nat.findGreatest_spec (P := fun j => g.H i j = none) (Nat.zero_le n) h0
    exact g.H_none_le hi h (Nat.findGreatest_le n) hc

theorem Grid.col_lt (g : Grid n u v) (hu : Lattice n u) (hv : Lattice n v)
    (huv : ∀ r, cnt u n r = cnt v n r) {i : ℕ} (hi : i < n) : g.col i < n := by
  by_contra h
  have hle : n ≤ g.col i := by omega
  have := (g.H_none_iff hu hv huv hi le_rfl).mpr hle
  rw [g.top i hi] at this
  exact Option.some_ne_none _ this

/-- Column `i` holds exactly one cross, at height `col i`. -/
theorem Grid.X_iff (g : Grid n u v) (hu : Lattice n u) (hv : Lattice n v)
    (huv : ∀ r, cnt u n r = cnt v n r) {i j : ℕ} (hi : i < n) (hj : j < n) :
    g.X i j = true ↔ j = g.col i := by
  rw [g.cell_X hi hj, back_cross, ← g.cell_H hi hj, Ne, g.H_none_iff hu hv huv hi (by omega),
    g.H_none_iff hu hv huv hi hj.le]
  omega

/-- The row of the cross in row `j` (the column of the transposed diagram). -/
noncomputable def Grid.row (g : Grid n u v) (j : ℕ) : ℕ := g.tr.col j

theorem Grid.X_iff_row (g : Grid n u v) (hu : Lattice n u) (hv : Lattice n v)
    (huv : ∀ r, cnt u n r = cnt v n r) {i j : ℕ} (hi : i < n) (hj : j < n) :
    g.X i j = true ↔ i = g.row j :=
  g.tr.X_iff hv hu (cnt_comm_hyp huv) hj hi

/-- **Descents of the columns.** `col (i+1) < col i` iff `u i < u (i+1)`. -/
theorem Grid.col_desc (g : Grid n u v) (hu : Lattice n u) (hv : Lattice n v)
    (huv : ∀ r, cnt u n r = cnt v n r) {i : ℕ} (hi : i + 1 < n) :
    g.col (i + 1) < g.col i ↔ u i < u (i + 1) := by
  have hi0 : i < n := by omega
  have hne : g.col i ≠ g.col (i + 1) := by
    intro h
    have h1 := (g.X_iff hu hv huv hi0 (g.col_lt hu hv huv hi0)).mpr rfl
    have h2 := (g.X_iff hu hv huv hi (g.col_lt hu hv huv hi)).mpr rfl
    rw [g.X_iff_row hu hv huv hi0 (g.col_lt hu hv huv hi0)] at h1
    rw [← h, g.X_iff_row hu hv huv hi (g.col_lt hu hv huv hi0)] at h2
    omega
  set M := max (g.col i) (g.col (i + 1)) with hM
  have hMn : M < n := max_lt (g.col_lt hu hv huv hi0) (g.col_lt hu hv huv hi)
  have hnone : ∀ j, M ≤ j → j ≤ n → ¬(g.H i j = none ∧ g.H (i + 1) j = none) := by
    intro j hj hjn ⟨h1, h2⟩
    rw [g.H_none_iff hu hv huv hi0 hjn] at h1
    rw [g.H_none_iff hu hv huv hi hjn] at h2
    omega
  -- the comparison of the two labels is the same at every height from `M` to `n`
  have hinv : ∀ t, t ≤ n - M →
      (key (g.H i (n - t)) < key (g.H (i + 1) (n - t)) ↔ key (g.H i n) < key (g.H (i + 1) n)) := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have hj : n - (t + 1) < n := by omega
      have hj1 : n - (t + 1) + 1 = n - t := by omega
      rw [← ih (by omega)]
      have hloc := local_inv (g.H i (n - (t + 1) + 1)) (g.H (i + 1) (n - (t + 1) + 1))
        (g.V (i + 1 + 1) (n - (t + 1)))
      rw [← g.cell_V hi hj, ← g.cell_H hi hj, ← g.cell_H hi0 hj, hj1] at hloc
      exact hloc (hnone _ (by omega) (by omega)) (hnone _ (by omega) (by omega))
  have hfin := hinv (n - M) le_rfl
  rw [Nat.sub_sub_self hMn.le, g.top i hi0, g.top (i + 1) hi] at hfin
  simp only [key, Nat.cast_lt] at hfin
  rw [← hfin]
  rcases lt_or_gt_of_ne hne with h | h
  · -- column `i + 1` is higher: at height `M` only its label is `none`
    have hMe : M = g.col (i + 1) := by omega
    have h1 : g.H (i + 1) M = none := (g.H_none_iff hu hv huv hi hMn.le).mpr (by omega)
    have h2 : g.H i M ≠ none := fun c => by
      have := (g.H_none_iff hu hv huv hi0 hMn.le).mp c; omega
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp h2
    rw [h1, hr]
    simp only [key]
    constructor
    · intro c; omega
    · intro c; omega
  · have hMe : M = g.col i := by omega
    have h1 : g.H i M = none := (g.H_none_iff hu hv huv hi0 hMn.le).mpr (by omega)
    have h2 : g.H (i + 1) M ≠ none := fun c => by
      have := (g.H_none_iff hu hv huv hi hMn.le).mp c; omega
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp h2
    rw [h1, hr]
    simp only [key]
    constructor
    · intro _; omega
    · intro _; exact h

/-! ### Building the diagram -/

/-- Labels down one column: `t` steps below the top, with top label `top` and right line `Vr`. -/
def hcol (n : ℕ) (top : Option ℕ) (Vr : ℕ → Option ℕ) : ℕ → Option ℕ
  | 0 => top
  | t + 1 => (back (hcol n top Vr t) (Vr (n - 1 - t))).1

/-- The vertical line `m` steps from the right. -/
def line (n : ℕ) (u v : ℕ → ℕ) : ℕ → ℕ → Option ℕ
  | 0 => fun j => some (v j)
  | m + 1 => fun j =>
    (back (hcol n (some (u (n - 1 - m))) (line n u v m) (n - 1 - j)) (line n u v m j)).2.1

/-- The growth diagram of `(u, v)`. -/
def build (n : ℕ) (u v : ℕ → ℕ) : Grid n u v where
  H i j := hcol n (some (u i)) (line n u v (n - 1 - i)) (n - j)
  V i j := line n u v (n - i) j
  X i j := (back (hcol n (some (u i)) (line n u v (n - 1 - i)) (n - 1 - j))
    (line n u v (n - 1 - i) j)).2.2
  top i _ := by simp [hcol]
  right j _ := by simp [line]
  cell i hi j hj := by
    have h1 : n - (j + 1) = n - 1 - j := by omega
    have h2 : n - (i + 1) = n - 1 - i := by omega
    have h3 : n - j = n - 1 - j + 1 := by omega
    have h4 : n - i = n - 1 - i + 1 := by omega
    have h5 : n - 1 - (n - 1 - j) = j := by omega
    have h6 : n - 1 - (n - 1 - i) = i := by omega
    simp only [h1, h2]
    rw [h3, h4]
    simp only [hcol, line, h5, h6]

/-! ### The reduction -/

/-- **Lemma 2.1 of the paper (the direction used).** If two lattice words of length `n` have the
same content, their ascent sets are the descent sets of some permutation and of its inverse. -/
theorem mem_pairs_of_words {u v : ℕ → ℕ} (hu : Lattice n u) (hv : Lattice n v)
    (huv : ∀ r, cnt u n r = cnt v n r) : (asc n u, asc n v) ∈ pairs n := by
  let g := build n u v
  have hw : ∀ q < n, g.col q < n := fun q hq => g.col_lt hu hv huv hq
  have hr : ∀ x < n, g.row x < n := fun x hx => g.tr.col_lt hv hu (cnt_comm_hyp huv) hx
  have hrw : ∀ q < n, g.row (g.col q) = q := fun q hq =>
    ((g.X_iff_row hu hv huv hq (hw q hq)).mp ((g.X_iff hu hv huv hq (hw q hq)).mpr rfl)).symm
  have hwr : ∀ x < n, g.col (g.row x) = x := fun x hx =>
    ((g.X_iff hu hv huv (hr x hx) hx).mp ((g.X_iff_row hu hv huv (hr x hx) hx).mpr rfl)).symm
  obtain ⟨h1, h2⟩ := descP_toPerm hw hr hrw hwr
  refine Finset.mem_image.mpr ⟨toPerm _ _ hw hr hrw hwr, Finset.mem_univ _, ?_⟩
  rw [h1, h2]
  congr 1
  · ext i
    simp only [desc, asc, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, h⟩; exact ⟨hi, (g.col_desc hu hv huv (by omega)).mp h⟩
    · rintro ⟨hi, h⟩; exact ⟨hi, (g.col_desc hu hv huv (by omega)).mpr h⟩
  · ext i
    simp only [desc, asc, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hi, h⟩; exact ⟨hi, (g.tr.col_desc hv hu (cnt_comm_hyp huv) (by omega)).mp h⟩
    · rintro ⟨hi, h⟩; exact ⟨hi, (g.tr.col_desc hv hu (cnt_comm_hyp huv) (by omega)).mpr h⟩

end Growth

end Stanley
