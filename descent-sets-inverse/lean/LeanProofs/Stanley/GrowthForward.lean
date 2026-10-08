/-
  Stanley, MathOverflow 486548. Lemma 2.1 of the paper, the converse direction: every permutation
  `w` comes from two standard Young tableaux of a common shape, with `D(w)` and `D(w⁻¹)` their
  descent sets. Together with `Growth.mem_pairs_of_words` this gives the full equivalence
  `mem_pairs_iff_words`.

  Fomin's forward rule `fwd` grows the diagram from the empty bottom and left boundaries, with a
  cross in column `i` at height `w i`. It inverts the backward rule `back` cell by cell
  (`back_fwd`), so the forward diagram is a `Growth.Grid`. Corner shapes stay partitions
  (`fwd_isPart`), so the top and right words are lattice words of equal content, and the column
  lemmas of `Growth` read off the descent sets. No insertion algorithm is used.
-/
import LeanProofs.Stanley.Growth

namespace Stanley

namespace Growth

open Finset

/-- Fomin's forward local rule: from the bottom label `b`, the left label `l` and whether the cell
holds a cross, the labels of the top and right edges. -/
def fwd : Option ℕ → Option ℕ → Bool → Option ℕ × Option ℕ
  | _, _, true => (some 0, some 0)
  | none, l, false => (none, l)
  | some r, none, false => (some r, none)
  | some r, some s, false => if r = s then (some (r + 1), some (r + 1)) else (some r, some s)

/-- A cell is valid when a cross has empty incoming labels. -/
def FValid (b l : Option ℕ) (x : Bool) : Prop := x = true → b = none ∧ l = none

theorem back_fwd (b l : Option ℕ) (x : Bool) (hv : FValid b l x) :
    back (fwd b l x).1 (fwd b l x).2 = (b, l, x) := by
  cases x
  · rcases b with _ | p <;> rcases l with _ | q
    · rfl
    · rfl
    · rfl
    · by_cases h : p = q
      · subst h; simp [fwd]
      · simp [fwd, h, back_ne h]
  · obtain ⟨rfl, rfl⟩ := hv rfl
    simp [fwd]

theorem fwd_top_none (b l : Option ℕ) (x : Bool) :
    (fwd b l x).1 = none ↔ b = none ∧ x = false := by
  cases x
  · rcases b with _ | p <;> rcases l with _ | q <;> simp [fwd]
    split_ifs <;> simp
  · simp [fwd]

theorem fwd_right_none (b l : Option ℕ) (x : Bool) :
    (fwd b l x).2 = none ↔ l = none ∧ x = false := by
  cases x
  · rcases b with _ | p <;> rcases l with _ | q <;> simp [fwd]
    split_ifs <;> simp
  · simp [fwd]

/-- Conservation around a valid cell: left + top = bottom + right. -/
theorem fwd_content (b l : Option ℕ) (x : Bool) (hv : FValid b l x) (r : ℕ) :
    e l r + e (fwd b l x).1 r = e b r + e (fwd b l x).2 r := by
  have h := back_content (fwd b l x).1 (fwd b l x).2 r
  rw [back_fwd b l x hv] at h
  simp only at h
  linarith

/-- Adding the boxes of the top-left path of a valid cell keeps a partition. -/
theorem fwd_isPart {ρ : ℕ → ℤ} (b l : Option ℕ) (x : Bool) (hv : FValid b l x)
    (hρ : IsPart ρ) (hb : IsPart (fun r => ρ r + e b r)) (hl : IsPart (fun r => ρ r + e l r)) :
    IsPart (fun r => ρ r + e l r + e (fwd b l x).1 r) := by
  refine ⟨fun j => ?_, fun j => ?_⟩
  · have := hρ.1 j; have := e_nonneg l j; have := e_nonneg (fwd b l x).1 j; linarith
  have h1 := hρ.2 j; have h2 := hb.2 j; have h3 := hl.2 j
  cases x
  · rcases b with _ | p <;> rcases l with _ | q
    · simpa [fwd, e] using h1
    · simpa [fwd, e] using h3
    · simpa [fwd, e] using h2
    · simp only [e, Option.some.injEq] at h1 h2 h3 ⊢
      by_cases hpq : p = q
      · subst hpq
        simp only [fwd, ite_true, Option.some.injEq]
        split_ifs at h1 h2 h3 ⊢ <;> omega
      · simp only [fwd, hpq, ite_false, Option.some.injEq]
        split_ifs at h1 h2 h3 ⊢ <;> omega
  · obtain ⟨rfl, rfl⟩ := hv rfl
    simp only [fwd, e, Option.some.injEq, reduceCtorEq, ite_false, add_zero] at h1 ⊢
    split_ifs <;> omega

/-! ### The forward diagram of a cross pattern -/

/-- Horizontal labels up column `m`, given the vertical line `Vl` on its left. -/
def fup (X : ℕ → ℕ → Bool) (Vl : ℕ → Option ℕ) (m : ℕ) : ℕ → Option ℕ
  | 0 => none
  | j + 1 => (fwd (fup X Vl m j) (Vl j) (X m j)).1

/-- The vertical line `m` steps from the left. -/
def fline (X : ℕ → ℕ → Bool) : ℕ → ℕ → Option ℕ
  | 0 => fun _ => none
  | m + 1 => fun j => (fwd (fup X (fline X m) m j) (fline X m j) (X m j)).2

/-- Horizontal edge labels of the forward diagram. -/
abbrev FH (X : ℕ → ℕ → Bool) (i j : ℕ) : Option ℕ := fup X (fline X i) i j

/-- Crosses lie in distinct rows and columns. -/
def XValid (X : ℕ → ℕ → Bool) : Prop :=
  ∀ i j, X i j = true → (∀ k < j, X i k = false) ∧ (∀ k < i, X k j = false)

variable {X : ℕ → ℕ → Bool}

theorem FH_none_iff (i : ℕ) : ∀ j, FH X i j = none ↔ ∀ k < j, X i k = false := by
  intro j
  induction j with
  | zero => simp [FH, fup]
  | succ j ih =>
    change (fwd (FH X i j) (fline X i j) (X i j)).1 = none ↔ _
    rw [fwd_top_none, ih]
    constructor
    · rintro ⟨h, hx⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact h k hk
      · exact hx
    · intro h; exact ⟨fun k hk => h k (by omega), h j (by omega)⟩

theorem fline_none_iff (j : ℕ) : ∀ i, fline X i j = none ↔ ∀ k < i, X k j = false := by
  intro i
  induction i with
  | zero => simp [fline]
  | succ i ih =>
    change (fwd (FH X i j) (fline X i j) (X i j)).2 = none ↔ _
    rw [fwd_right_none, ih]
    constructor
    · rintro ⟨h, hx⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact h k hk
      · exact hx
    · intro h; exact ⟨fun k hk => h k (by omega), h i (by omega)⟩

theorem cell_valid (hX : XValid X) (i j : ℕ) : FValid (FH X i j) (fline X i j) (X i j) := by
  intro hx
  exact ⟨(FH_none_iff i j).mpr (hX i j hx).1, (fline_none_iff j i).mpr (hX i j hx).2⟩

/-- The shape at corner `(i, j)`, read up the vertical line `i`. -/
def nu (X : ℕ → ℕ → Bool) (i j : ℕ) (r : ℕ) : ℤ := ∑ k ∈ range j, e (fline X i k) r

theorem nu_zero_left (j r : ℕ) : nu X 0 j r = 0 := by
  simp [nu, fline, e]

theorem nu_succ_left (hX : XValid X) (i : ℕ) :
    ∀ j r, nu X (i + 1) j r = nu X i j r + e (FH X i j) r := by
  intro j
  induction j with
  | zero => intro r; simp [nu, FH, fup, e]
  | succ j ih =>
    intro r
    have hc := fwd_content (FH X i j) (fline X i j) (X i j) (cell_valid hX i j) r
    change e (fline X i j) r + e (FH X i (j + 1)) r = e (FH X i j) r + e (fline X (i + 1) j) r
      at hc
    simp only [nu, sum_range_succ] at ih ⊢
    rw [ih r]
    linarith

theorem nu_isPart (hX : XValid X) : ∀ i j, IsPart (nu X i j) := by
  have h0 : IsPart (fun _ : ℕ => (0 : ℤ)) := ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  intro i
  induction i with
  | zero =>
    intro j
    have : nu X 0 j = fun _ => 0 := funext (nu_zero_left j)
    rw [this]; exact h0
  | succ i ihi =>
    intro j
    induction j with
    | zero =>
      have : nu X (i + 1) 0 = fun _ => 0 := by funext r; simp [nu]
      rw [this]; exact h0
    | succ j ihj =>
      have hSE : IsPart (fun r => nu X i j r + e (FH X i j) r) := by
        have : (fun r => nu X i j r + e (FH X i j) r) = nu X (i + 1) j :=
          funext fun r => (nu_succ_left hX i j r).symm
        rw [this]; exact ihj
      have hNW : IsPart (fun r => nu X i j r + e (fline X i j) r) := by
        have : (fun r => nu X i j r + e (fline X i j) r) = nu X i (j + 1) := by
          funext r; simp [nu, sum_range_succ]
        rw [this]; exact ihi (j + 1)
      have key := fwd_isPart (FH X i j) (fline X i j) (X i j) (cell_valid hX i j)
        (ihi j) hSE hNW
      have : (fun r => nu X i j r + e (fline X i j) r +
          e (fwd (FH X i j) (fline X i j) (X i j)).1 r) = nu X (i + 1) (j + 1) := by
        funext r
        rw [nu_succ_left hX i (j + 1) r]
        simp only [nu, sum_range_succ]
        rfl
      rw [← this]; exact key

/-- Reading along a horizontal line gives the same shape. -/
theorem sum_FH_eq_nu (hX : XValid X) (j : ℕ) :
    ∀ i r, ∑ k ∈ range i, e (FH X k j) r = nu X i j r := by
  intro i
  induction i with
  | zero => intro r; simp [nu_zero_left]
  | succ i ih => intro r; rw [sum_range_succ, ih r, nu_succ_left hX i j r]

/-! ### The diagram of a permutation -/

variable {n : ℕ}

/-- The permutation as a function on `ℕ` (value `n` off the domain). -/
def wf (w : Equiv.Perm (Fin n)) (i : ℕ) : ℕ := if h : i < n then (w ⟨i, h⟩ : ℕ) else n

/-- Crosses of `w`: column `i`, height `w i`. -/
def xw (w : Equiv.Perm (Fin n)) (i j : ℕ) : Bool := decide (i < n ∧ wf w i = j)

theorem wf_eq (w : Equiv.Perm (Fin n)) {i : ℕ} (h : i < n) : wf w i = (w ⟨i, h⟩ : ℕ) := by simp [wf, h]

theorem xw_iff (w : Equiv.Perm (Fin n)) (i j : ℕ) : xw w i j = true ↔ i < n ∧ wf w i = j := by
  simp [xw]

theorem xw_valid (w : Equiv.Perm (Fin n)) : XValid (xw w) := by
  intro i j hx
  obtain ⟨hi, hij⟩ := (xw_iff w i j).mp hx
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · simp only [xw, decide_eq_false_iff_not, not_and]; intro _; omega
  · simp only [xw, decide_eq_false_iff_not, not_and]
    intro hk' hkj
    rw [wf_eq w hk'] at hkj
    rw [wf_eq w hi] at hij
    have : w ⟨k, hk'⟩ = w ⟨i, hi⟩ := Fin.ext (hkj.trans hij.symm)
    have := congrArg Fin.val (w.injective this)
    simp at this; omega

theorem xw_wf (w : Equiv.Perm (Fin n)) {i : ℕ} (hi : i < n) : xw w i (wf w i) = true :=
  (xw_iff w i _).mpr ⟨hi, rfl⟩

theorem xw_inv (w : Equiv.Perm (Fin n)) {j : ℕ} (hj : j < n) :
    xw w (w⁻¹ ⟨j, hj⟩ : ℕ) j = true := by
  refine (xw_iff w _ j).mpr ⟨(w⁻¹ ⟨j, hj⟩).is_lt, ?_⟩
  rw [wf_eq w (w⁻¹ ⟨j, hj⟩).is_lt]
  simp

theorem FH_top_ne (w : Equiv.Perm (Fin n)) {i : ℕ} (hi : i < n) : FH (xw w) i n ≠ none := by
  rw [Ne, FH_none_iff]
  intro h
  have h1 := h (wf w i) (by rw [wf_eq w hi]; exact (w ⟨i, hi⟩).is_lt)
  rw [xw_wf w hi] at h1
  exact Bool.noConfusion h1

theorem fline_right_ne (w : Equiv.Perm (Fin n)) {j : ℕ} (hj : j < n) :
    fline (xw w) n j ≠ none := by
  rw [Ne, fline_none_iff]
  intro h
  have h1 := h _ (w⁻¹ ⟨j, hj⟩).is_lt
  rw [xw_inv w hj] at h1
  exact Bool.noConfusion h1

/-- The top word (the tableau `Q`). -/
def uw (w : Equiv.Perm (Fin n)) (i : ℕ) : ℕ := (FH (xw w) i n).getD 0

/-- The right word (the tableau `P`). -/
def vw (w : Equiv.Perm (Fin n)) (j : ℕ) : ℕ := (fline (xw w) n j).getD 0

theorem some_uw (w : Equiv.Perm (Fin n)) {i : ℕ} (hi : i < n) : some (uw w i) = FH (xw w) i n := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (FH_top_ne w hi)
  simp [uw, ha]

theorem some_vw (w : Equiv.Perm (Fin n)) {j : ℕ} (hj : j < n) :
    some (vw w j) = fline (xw w) n j := by
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp (fline_right_ne w hj)
  simp [vw, ha]

theorem cnt_uw (w : Equiv.Perm (Fin n)) {k : ℕ} (hk : k ≤ n) (r : ℕ) :
    cnt (uw w) k r = nu (xw w) k n r := by
  rw [← sum_FH_eq_nu (xw_valid w) n k r, cnt]
  exact sum_congr rfl fun m hm => by rw [some_uw w (by simp at hm; omega)]

theorem cnt_vw (w : Equiv.Perm (Fin n)) {k : ℕ} (hk : k ≤ n) (r : ℕ) :
    cnt (vw w) k r = nu (xw w) n k r := by
  rw [cnt, nu]
  exact sum_congr rfl fun m hm => by rw [some_vw w (by simp at hm; omega)]

theorem lattice_uw (w : Equiv.Perm (Fin n)) : Lattice n (uw w) := by
  intro k hk r
  rw [cnt_uw w hk, cnt_uw w hk]
  exact (nu_isPart (xw_valid w) k n).2 r

theorem lattice_vw (w : Equiv.Perm (Fin n)) : Lattice n (vw w) := by
  intro k hk r
  rw [cnt_vw w hk, cnt_vw w hk]
  exact (nu_isPart (xw_valid w) n k).2 r

theorem content_uw_vw (w : Equiv.Perm (Fin n)) (r : ℕ) : cnt (uw w) n r = cnt (vw w) n r := by
  rw [cnt_uw w le_rfl, cnt_vw w le_rfl]

/-- The forward growth diagram of `w`, as a diagram for the backward rule. -/
def fgrid (w : Equiv.Perm (Fin n)) : Grid n (uw w) (vw w) where
  H i j := FH (xw w) i j
  V i j := fline (xw w) i j
  X := xw w
  top i hi := (some_uw w hi).symm
  right j hj := (some_vw w hj).symm
  cell i _ j _ := back_fwd _ _ _ (cell_valid (xw_valid w) i j)

theorem fgrid_col (w : Equiv.Perm (Fin n)) {i : ℕ} (hi : i < n) : (fgrid w).col i = wf w i := by
  have hlt : wf w i < n := by rw [wf_eq w hi]; exact (w ⟨i, hi⟩).is_lt
  exact ((fgrid w).X_iff (lattice_uw w) (lattice_vw w) (content_uw_vw w) hi hlt).mp
    (xw_wf w hi) |>.symm

theorem fgrid_row (w : Equiv.Perm (Fin n)) {j : ℕ} (hj : j < n) :
    (fgrid w).row j = (w⁻¹ ⟨j, hj⟩ : ℕ) :=
  (((fgrid w).X_iff_row (lattice_uw w) (lattice_vw w) (content_uw_vw w)
    (w⁻¹ ⟨j, hj⟩).is_lt hj).mp (xw_inv w hj)).symm

theorem descP_eq_asc (w : Equiv.Perm (Fin n)) : descP w = asc n (uw w) := by
  have hu := lattice_uw w; have hv := lattice_vw w; have huv := content_uw_vw w
  ext i
  simp only [descP, asc, mem_filter, mem_range]
  constructor
  · rintro ⟨hi, h, hlt⟩
    refine ⟨hi, ((fgrid w).col_desc hu hv huv h).mp ?_⟩
    rw [fgrid_col w h, fgrid_col w (by omega), wf_eq w h, wf_eq w (by omega)]
    exact hlt
  · rintro ⟨hi, hlt⟩
    have h : i + 1 < n := by omega
    refine ⟨hi, h, ?_⟩
    have := ((fgrid w).col_desc hu hv huv h).mpr hlt
    rw [fgrid_col w h, fgrid_col w (by omega), wf_eq w h, wf_eq w (by omega)] at this
    exact this

theorem descP_inv_eq_asc (w : Equiv.Perm (Fin n)) : descP w⁻¹ = asc n (vw w) := by
  have hu := lattice_uw w; have hv := lattice_vw w; have huv := content_uw_vw w
  have hcd := fun {j : ℕ} (h : j + 1 < n) =>
    (fgrid w).tr.col_desc hv hu (cnt_comm_hyp huv) (i := j) h
  ext i
  simp only [descP, asc, mem_filter, mem_range]
  constructor
  · rintro ⟨hi, h, hlt⟩
    refine ⟨hi, (hcd h).mp ?_⟩
    change (fgrid w).row (i + 1) < (fgrid w).row i
    rw [fgrid_row w h, fgrid_row w (by omega)]
    exact hlt
  · rintro ⟨hi, hlt⟩
    have h : i + 1 < n := by omega
    refine ⟨hi, h, ?_⟩
    have := (hcd h).mpr hlt
    change (fgrid w).row (i + 1) < (fgrid w).row i at this
    rw [fgrid_row w h, fgrid_row w (by omega)] at this
    exact this

/-- **Lemma 2.1 of the paper, converse direction.** Every permutation comes from two lattice
words of equal content, whose ascent sets are `D(w)` and `D(w⁻¹)`. -/
theorem words_of_perm (w : Equiv.Perm (Fin n)) :
    ∃ u v : ℕ → ℕ, Lattice n u ∧ Lattice n v ∧ (∀ r, cnt u n r = cnt v n r) ∧
      asc n u = descP w ∧ asc n v = descP w⁻¹ :=
  ⟨uw w, vw w, lattice_uw w, lattice_vw w, content_uw_vw w,
    (descP_eq_asc w).symm, (descP_inv_eq_asc w).symm⟩

/-- **Lemma 2.1 of the paper.** A pair `(S, T)` occurs if and only if some shape has a standard
Young tableau with descent set `S` and one with descent set `T` (as lattice row words of equal
content). -/
theorem mem_pairs_iff_words {S T : Finset ℕ} :
    (S, T) ∈ pairs n ↔ ∃ u v : ℕ → ℕ, Lattice n u ∧ Lattice n v ∧
      (∀ r, cnt u n r = cnt v n r) ∧ asc n u = S ∧ asc n v = T := by
  constructor
  · intro h
    obtain ⟨w, _, he⟩ := mem_image.mp h
    obtain ⟨u, v, hu, hv, huv, h1, h2⟩ := words_of_perm w
    exact ⟨u, v, hu, hv, huv, h1.trans (congrArg Prod.fst he),
      h2.trans (congrArg Prod.snd he)⟩
  · rintro ⟨u, v, hu, hv, huv, rfl, rfl⟩
    exact mem_pairs_of_words hu hv huv

end Growth

end Stanley
