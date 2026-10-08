/-
  Stanley, MathOverflow 486548. Part G. The row-word fillings of Section 3 of the paper.

  Positions and breaks are 0-indexed: `X ⊆ {0, …, n-2}` is a set of breaks, `x ∈ X` separating
  positions `x` and `x + 1`. The run of a position `p` has index `rk X p` (the number of breaks
  before `p`), and `p ≥ 1` starts its run when `p - 1 ∈ X`. A word `fill X L E` puts `0` on run `0`,
  `L p` at the start `p` of every later run, `1` on the positions of `E`, and `0` elsewhere.

  `asc_fill` reads off its ascent set and `lattice_of` checks the lattice condition. The two
  fillings of the paper, Lemma 3.1 (extra twos) and Lemma 3.2 (two-started runs), are `exWord` and
  `tsWord`; `pair_of_fillings` is Corollary 3.3.
-/
import LeanProofs.Stanley.Growth

namespace Stanley

namespace Fill

open Finset Growth

/-! ### Ranks -/

/-- Number of elements of `Y` below `y`. -/
def rk (Y : Finset ℕ) (y : ℕ) : ℕ := (Y.filter (· < y)).card

theorem rk_mono (Y : Finset ℕ) {y z : ℕ} (h : y ≤ z) : rk Y y ≤ rk Y z :=
  Finset.card_le_card fun a ha => by
    simp only [Finset.mem_filter] at ha ⊢; exact ⟨ha.1, by omega⟩

theorem rk_lt_rk {Y : Finset ℕ} {y z : ℕ} (hy : y ∈ Y) (h : y < z) : rk Y y < rk Y z := by
  apply Finset.card_lt_card
  refine ⟨fun a ha => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter] at ha ⊢; exact ⟨ha.1, by omega⟩
  · have := hsub (Finset.mem_filter.mpr ⟨hy, h⟩)
    simp at this

theorem lt_of_rk_lt {Y : Finset ℕ} {y z : ℕ} (h : rk Y y < rk Y z) : y < z := by
  by_contra hc; exact absurd (rk_mono Y (not_lt.mp hc)) (not_le.mpr h)

theorem rk_lt_card {Y : Finset ℕ} {y : ℕ} (hy : y ∈ Y) : rk Y y < Y.card :=
  Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub => by
    have := hsub hy; simp at this⟩

theorem rk_injOn (Y : Finset ℕ) : Set.InjOn (rk Y) Y := by
  intro y hy z hz h
  rcases lt_trichotomy y z with hl | he | hg
  · exact absurd h (rk_lt_rk hy hl).ne
  · exact he
  · exact absurd h (rk_lt_rk hz hg).ne'

theorem rk_surj {Y : Finset ℕ} {k : ℕ} (hk : k < Y.card) : ∃ y ∈ Y, rk Y y = k := by
  have hmaps : ∀ y ∈ Y, rk Y y ∈ range Y.card := fun y hy => Finset.mem_range.mpr (rk_lt_card hy)
  have himg : Y.image (rk Y) = range Y.card := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ha
      exact hmaps y hy
    · rw [Finset.card_image_of_injOn (rk_injOn Y), Finset.card_range]
  have : k ∈ Y.image (rk Y) := himg ▸ Finset.mem_range.mpr hk
  obtain ⟨y, hy, h⟩ := Finset.mem_image.mp this
  exact ⟨y, hy, h⟩

theorem card_rk_eq (Y : Finset ℕ) (k : ℕ) :
    (Y.filter (fun y => rk Y y = k)).card = if k < Y.card then 1 else 0 := by
  split_ifs with hk
  · obtain ⟨y, hy, hyk⟩ := rk_surj hk
    rw [Finset.card_eq_one]
    refine ⟨y, Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hy, hyk⟩, ?_⟩⟩
    intro z hz
    rw [Finset.mem_filter] at hz
    exact rk_injOn Y hz.1 hy (hz.2.trans hyk.symm)
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy hyk
    exact hk (hyk ▸ rk_lt_card hy)

theorem rk_zero (Y : Finset ℕ) : rk Y 0 = 0 := by simp [rk]

theorem rk_succ (Y : Finset ℕ) (p : ℕ) : rk Y (p + 1) = rk Y p + if p ∈ Y then 1 else 0 := by
  unfold rk
  by_cases hp : p ∈ Y
  · rw [if_pos hp, show Y.filter (· < p + 1) = insert p (Y.filter (· < p)) by
      ext a; simp only [Finset.mem_filter, Finset.mem_insert]; constructor
      · rintro ⟨ha, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
        · exact Or.inr ⟨ha, h⟩
        · exact Or.inl h
      · rintro (rfl | ⟨ha, h⟩)
        · exact ⟨hp, by omega⟩
        · exact ⟨ha, by omega⟩]
    rw [Finset.card_insert_of_notMem (by simp)]
  · rw [if_neg hp, add_zero]
    congr 1; ext a; simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha, h⟩
      refine ⟨ha, ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · exact h
      · exact absurd (h ▸ ha) hp
    · rintro ⟨ha, h⟩; exact ⟨ha, by omega⟩

/-- The run index after a break. -/
theorem rk_succ_of_mem {X : Finset ℕ} {x : ℕ} (hx : x ∈ X) : rk X (x + 1) = rk X x + 1 := by
  rw [rk_succ, if_pos hx]

theorem rk_succ_of_not_mem {X : Finset ℕ} {x : ℕ} (hx : x ∉ X) : rk X (x + 1) = rk X x := by
  rw [rk_succ, if_neg hx, add_zero]

/-! ### Counting letters -/

theorem e_some (a r : ℕ) : e (some a) r = if a = r then 1 else 0 := by
  simp [e]

theorem cnt_eq_card (u : ℕ → ℕ) (k r : ℕ) :
    cnt u k r = (((range k).filter (fun p => u p = r)).card : ℤ) := by
  unfold cnt
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [e_some]; split_ifs <;> simp

theorem cnt_mono (u : ℕ → ℕ) {k k' : ℕ} (h : k ≤ k') (r : ℕ) : cnt u k r ≤ cnt u k' r := by
  rw [cnt_eq_card, cnt_eq_card]
  exact_mod_cast Finset.card_le_card fun p hp => by
    simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢; exact ⟨by omega, hp.2⟩

/-- **Lattice criterion.** Letters `≥ 2` occur at most once, each letter `r + 1 ≥ 2` is preceded
by a letter `r`, and every prefix has at most as many `1`s as `0`s. -/
theorem lattice_of {n : ℕ} {u : ℕ → ℕ}
    (h1 : ∀ r, 2 ≤ r → ∀ p q, u p = r → u q = r → p = q)
    (h2 : ∀ r, 1 ≤ r → ∀ p, u p = r + 1 → ∃ q < p, u q = r)
    (h0 : ∀ k ≤ n, cnt u k 1 ≤ cnt u k 0) : Lattice n u := by
  intro k hk r
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact h0 k hk
  rw [cnt_eq_card, cnt_eq_card]
  have hle : ((range k).filter (fun p => u p = r + 1)).card ≤ 1 :=
    Finset.card_le_one.mpr fun p hp q hq => by
      simp only [Finset.mem_filter] at hp hq
      exact h1 (r + 1) (by omega) p q hp.2 hq.2
  rcases Nat.eq_zero_or_pos ((range k).filter (fun p => u p = r + 1)).card with h | h
  · rw [h]; exact_mod_cast Nat.zero_le _
  · obtain ⟨p, hp⟩ := Finset.card_pos.mp h
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨q, hqp, hq⟩ := h2 r hr p hp.2
    have : 1 ≤ ((range k).filter (fun p => u p = r)).card :=
      Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq⟩⟩
    exact_mod_cast hle.trans this

/-- The `1`s-versus-`0`s condition, from a supply of `0`s below `m` and `1`s only at one early
position and at positions `≥ m`. -/
theorem ones_le_zeros {n m b P1 : ℕ} {u : ℕ → ℕ} (X : Finset ℕ) (hu0 : u 0 = 0)
    (hP1 : 1 ≤ P1) (hones : ∀ p, u p = 1 → p = P1 ∨ m ≤ p) (htot : cnt u n 1 ≤ b)
    (hA : b ≤ ((range (m - 1)).filter (· ∉ X)).card)
    (hzero : ∀ x < m - 1, x ∉ X → u (x + 1) = 0) :
    ∀ k ≤ n, cnt u k 1 ≤ cnt u k 0 := by
  intro k hk
  by_cases hkm : k ≤ m
  · rw [cnt_eq_card, cnt_eq_card]
    have hsub : (range k).filter (fun p => u p = 1) ⊆ {P1} := fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      rcases hones p hp.2 with h | h
      · exact Finset.mem_singleton.mpr h
      · omega
    rcases Nat.eq_zero_or_pos ((range k).filter (fun p => u p = 1)).card with h | h
    · rw [h]; exact_mod_cast Nat.zero_le _
    · obtain ⟨p, hp⟩ := Finset.card_pos.mp h
      have hpP := Finset.mem_singleton.mp (hsub hp)
      simp only [Finset.mem_filter, Finset.mem_range] at hp
      have h0 : 1 ≤ ((range k).filter (fun p => u p = 0)).card :=
        Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hu0⟩⟩
      have h1 := (Finset.card_le_card hsub).trans (Finset.card_singleton P1).le
      exact_mod_cast h1.trans h0
  · have hA' : ((((range (m - 1)).filter (· ∉ X)).card : ℕ) : ℤ) ≤ cnt u k 0 := by
      apply le_trans _ (cnt_mono u (show m ≤ k by omega) 0)
      rw [cnt_eq_card]
      exact_mod_cast Finset.card_le_card_of_injOn (· + 1)
        (fun x hx => by
          simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hx ⊢
          exact ⟨by omega, hzero x hx.1 hx.2⟩)
        (fun a _ b _ h => by simpa using h)
    have := cnt_mono u hk 1
    have hb : (b : ℤ) ≤ (((range (m - 1)).filter (· ∉ X)).card : ℤ) := by exact_mod_cast hA
    linarith

/-! ### Fillings -/

/-- The filled word. -/
def fill (X : Finset ℕ) (L : ℕ → ℕ) (E : Finset ℕ) (p : ℕ) : ℕ :=
  if rk X p = 0 then 0 else if 1 ≤ p ∧ p - 1 ∈ X then L p else if p ∈ E then 1 else 0

theorem fill_zero (X : Finset ℕ) (L : ℕ → ℕ) (E : Finset ℕ) : fill X L E 0 = 0 := by
  simp [fill, rk_zero]

theorem fill_start {X : Finset ℕ} {L : ℕ → ℕ} {E : Finset ℕ} {x : ℕ} (hx : x ∈ X) :
    fill X L E (x + 1) = L (x + 1) := by
  simp [fill, rk_succ_of_mem hx, hx]

theorem fill_nonstart {X : Finset ℕ} {L : ℕ → ℕ} {E : Finset ℕ} {x : ℕ} (hx : x ∉ X) :
    fill X L E (x + 1) = if rk X x = 0 then 0 else if x + 1 ∈ E then 1 else 0 := by
  simp [fill, rk_succ_of_not_mem hx, hx]

/-- **Ascent set of a filling.** -/
theorem asc_fill {n : ℕ} {X : Finset ℕ} {L : ℕ → ℕ} {E : Finset ℕ} (hX : X ⊆ range (n - 1))
    (hL : ∀ x ∈ X, 1 ≤ L (x + 1))
    (hjump : ∀ x ∈ X, fill X L E x < L (x + 1))
    (hE : ∀ p, p + 1 ∈ E → p ∉ X → 1 ≤ rk X p → (1 ≤ p ∧ p - 1 ∈ X) ∨ p ∈ E) :
    asc n (fill X L E) = X := by
  ext i
  simp only [asc, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hi, h⟩
    by_contra hiX
    rw [fill_nonstart hiX] at h
    split_ifs at h with h0 h1
    · omega
    · rcases hE i h1 hiX (by omega) with hs | hs
      · have h2 : fill X L E i = L i := by unfold fill; rw [if_neg h0, if_pos hs]
        have := hL (i - 1) hs.2
        rw [show i - 1 + 1 = i by omega] at this
        omega
      · have h2 : 1 ≤ fill X L E i := by
          unfold fill
          rw [if_neg h0]
          by_cases hs' : 1 ≤ i ∧ i - 1 ∈ X
          · rw [if_pos hs']
            have := hL (i - 1) hs'.2
            rwa [show i - 1 + 1 = i by omega] at this
          · rw [if_neg hs', if_pos hs]
        omega
    · omega
  · intro hi
    have := Finset.mem_range.mp (hX hi)
    exact ⟨this, by rw [fill_start hi]; exact hjump i hi⟩

/-! ### Letter counts of a filling -/

section Counts

variable {n : ℕ} {X : Finset ℕ} {L : ℕ → ℕ} {E : Finset ℕ}

/-- Hypotheses shared by both fillings: breaks below `n - 1`, start letters `≥ 1`, and `E` a set of
non-start positions in runs `≥ 1`, below `n`. -/
structure Good (n : ℕ) (X : Finset ℕ) (L : ℕ → ℕ) (E : Finset ℕ) : Prop where
  hX : X ⊆ range (n - 1)
  hL : ∀ x ∈ X, 1 ≤ L (x + 1)
  hEn : ∀ p ∈ E, p < n
  hEs : ∀ p ∈ E, ¬(1 ≤ p ∧ p - 1 ∈ X)
  hEr : ∀ p ∈ E, rk X p ≠ 0

theorem Good.lt (h : Good n X L E) {x : ℕ} (hx : x ∈ X) : x + 1 < n := by
  have := Finset.mem_range.mp (h.hX hx); omega

/-- Positions holding letter `r ≥ 1`. -/
theorem Good.filter_eq (h : Good n X L E) {r : ℕ} (hr : 1 ≤ r) :
    (range n).filter (fun p => fill X L E p = r) =
      (X.filter (fun x => L (x + 1) = r)).image (· + 1) ∪ (if r = 1 then E else ∅) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hp, hf⟩
    by_cases hs : 1 ≤ p ∧ p - 1 ∈ X
    · left
      refine ⟨p - 1, ⟨hs.2, ?_⟩, by omega⟩
      have := fill_start (L := L) (E := E) hs.2
      rw [show p - 1 + 1 = p by omega] at this ⊢
      rw [← this]; exact hf
    · right
      unfold fill at hf
      rw [if_neg hs] at hf
      split_ifs at hf with h0 hE <;> first | omega | (subst hf; simp [hE])
  · rintro (⟨x, ⟨hx, hLx⟩, rfl⟩ | hp)
    · exact ⟨h.lt hx, by rw [fill_start hx, hLx]⟩
    · split_ifs at hp with hr1
      · subst hr1
        refine ⟨h.hEn p hp, ?_⟩
        unfold fill; rw [if_neg (h.hEr p hp), if_neg (h.hEs p hp), if_pos hp]
      · simp at hp

theorem Good.cnt_pos (h : Good n X L E) {r : ℕ} (hr : 1 ≤ r) :
    cnt (fill X L E) n r =
      ((X.filter (fun x => L (x + 1) = r)).card : ℤ) + (if r = 1 then (E.card : ℤ) else 0) := by
  rw [cnt_eq_card, h.filter_eq hr, Finset.card_union_of_disjoint,
    Finset.card_image_of_injective _ (add_left_injective 1)]
  · split_ifs <;> simp
  · split_ifs
    · rw [Finset.disjoint_left]
      rintro p hp hpE
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      exact h.hEs _ hpE ⟨by omega, by simpa using (Finset.mem_filter.mp hx).1⟩
    · exact Finset.disjoint_empty_right _

theorem Good.cnt_zero (h : Good n X L E) :
    cnt (fill X L E) n 0 = (n : ℤ) - X.card - E.card := by
  rw [cnt_eq_card]
  have hsplit : (range n).filter (fun p => fill X L E p = 0) =
      ((range n) \ X.image (· + 1)) \ E := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_sdiff, Finset.mem_image]
    constructor
    · rintro ⟨hp, hf⟩
      refine ⟨⟨hp, ?_⟩, fun hE => ?_⟩
      · rintro ⟨x, hx, rfl⟩
        have := h.hL x hx; rw [fill_start hx] at hf; omega
      · unfold fill at hf
        rw [if_neg (h.hEr p hE), if_neg (h.hEs p hE), if_pos hE] at hf
        omega
    · rintro ⟨⟨hp, hns⟩, hE⟩
      refine ⟨hp, ?_⟩
      unfold fill
      split_ifs with h0 hs
      · rfl
      · exact absurd ⟨p - 1, hs.2, by omega⟩ hns
      · rfl
  rw [hsplit, Finset.card_sdiff, Finset.card_sdiff, Finset.card_range]
  · have h1 : (X.image (· + 1) ∩ range n).card = X.card := by
      rw [Finset.inter_eq_left.mpr, Finset.card_image_of_injective _ (add_left_injective 1)]
      intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_range.mpr (h.lt hx)
    have h2 : (E ∩ (range n \ X.image (· + 1))).card = E.card := by
      rw [Finset.inter_eq_left.mpr]
      intro p hp
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (h.hEn p hp), fun hi => ?_⟩
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
      exact h.hEs _ hp ⟨by omega, by simpa using hx⟩
    have hle1 : X.card ≤ n := by
      have := Finset.card_le_card h.hX; simp at this; omega
    have hle2 : E.card ≤ n - X.card := by
      have := Finset.card_le_card (show E ⊆ range n \ X.image (· + 1) from fun p hp =>
        Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (h.hEn p hp), fun hi => by
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
          exact h.hEs _ hp ⟨by omega, by simpa using hx⟩⟩)
      rw [Finset.card_sdiff, Finset.card_range, h1] at this
      omega
    simp only [h1, h2]
    push_cast [hle1, hle2]
    ring

end Counts

/-! ### Lemma 3.1: extra twos -/

section Extra

variable (n m : ℕ) (X : Finset ℕ)

/-- Position `p` lies in a late run: a run of index `≥ 2` starting at a position `≥ m`. -/
def Late (p : ℕ) : Prop := 2 ≤ rk X p ∧ ∃ y ∈ X, m ≤ y + 1 ∧ y < p

instance (p : ℕ) : Decidable (Late m X p) := by unfold Late; infer_instance

/-- Non-start positions of late runs (each may carry an extra `1`, the paper's letter `2`). -/
def exC : Finset ℕ := (range n).filter (fun p => 1 ≤ p ∧ p - 1 ∉ X ∧ Late m X p)

/-- Start letters: run `1` gets `1`, run `j ≥ 2` its leg letter `j`. -/
def exL (p : ℕ) : ℕ := if rk X p = 1 then 1 else rk X p

/-- The filling of Lemma 3.1, with extra `1`s on the late non-start positions below `θ`. -/
def exWord (θ : ℕ) : ℕ → ℕ := fill X (exL X) ((exC n m X).filter (· < θ))

variable {n m X}

theorem mem_exC {p : ℕ} : p ∈ exC n m X ↔ p < n ∧ 1 ≤ p ∧ p - 1 ∉ X ∧ Late m X p := by
  simp [exC]

theorem exGood (hX : X ⊆ range (n - 1)) (θ : ℕ) :
    Good n X (exL X) ((exC n m X).filter (· < θ)) where
  hX := hX
  hL x hx := by unfold exL; rw [rk_succ_of_mem hx]; split_ifs <;> omega
  hEn p hp := by rw [Finset.mem_filter, mem_exC] at hp; exact hp.1.1
  hEs p hp h := by rw [Finset.mem_filter, mem_exC] at hp; exact hp.1.2.2.1 h.2
  hEr p hp := by rw [Finset.mem_filter, mem_exC] at hp; have := hp.1.2.2.2.1; omega

theorem exWord_le_rk {θ : ℕ} (p : ℕ) : exWord n m X θ p ≤ rk X p := by
  unfold exWord fill exL
  split_ifs <;> omega

theorem asc_exWord (hX : X ⊆ range (n - 1)) (θ : ℕ) : asc n (exWord n m X θ) = X := by
  unfold exWord
  apply asc_fill hX (exGood (m := m) hX θ).hL
  · intro x hx
    have hle : fill X (exL X) ((exC n m X).filter (· < θ)) x ≤ rk X x :=
      exWord_le_rk (n := n) (m := m) (X := X) (θ := θ) x
    have h1 : exL X (x + 1) = if rk X x = 0 then 1 else rk X x + 1 := by
      unfold exL; rw [rk_succ_of_mem hx]; split_ifs <;> omega
    rw [h1]
    split_ifs with h0
    · have : fill X (exL X) ((exC n m X).filter (· < θ)) x = 0 := by unfold fill; rw [if_pos h0]
      omega
    · omega
  · intro p hp hpX hrk
    rw [Finset.mem_filter, mem_exC] at hp
    obtain ⟨⟨hpn, _, _, hr2, y, hy, hym, hyp⟩, hθ⟩ := hp
    have hp1 : 1 ≤ p := by
      rcases Nat.eq_zero_or_pos p with rfl | h
      · simp [rk_zero] at hrk
      · exact h
    by_cases hs : p - 1 ∈ X
    · exact Or.inl ⟨hp1, hs⟩
    · right
      have hyp' : y < p := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hyp with h | h
        · exact h
        · exact absurd (h ▸ hy) hpX
      rw [Finset.mem_filter, mem_exC]
      rw [rk_succ_of_not_mem hpX] at hr2
      exact ⟨⟨by omega, hp1, hs, hr2, y, hy, hym, hyp'⟩, by omega⟩

/-- Letter counts of the extra-twos filling. -/
theorem cnt_exWord (hX : X ⊆ range (n - 1)) (hX1 : 1 ≤ X.card) {θ : ℕ} (r : ℕ) :
    cnt (exWord n m X θ) n r =
      if r = 0 then (n : ℤ) - X.card - ((exC n m X).filter (· < θ)).card
      else if r = 1 then 1 + ((exC n m X).filter (· < θ)).card
      else if r ≤ X.card then 1 else 0 := by
  have hg := exGood (m := m) hX θ
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · unfold exWord; simpa using hg.cnt_zero
  · unfold exWord
    rw [hg.cnt_pos hr, if_neg (show r ≠ 0 by omega)]
    have hfil : X.filter (fun x => exL X (x + 1) = r) = X.filter (fun x => rk X x = r - 1) := by
      apply Finset.filter_congr
      intro x hx
      unfold exL; rw [rk_succ_of_mem hx]; split_ifs <;> omega
    rw [hfil, card_rk_eq]
    by_cases h1 : r = 1
    · subst h1; simp [show 0 < X.card by omega]
    · rw [if_neg h1, if_neg h1]
      split_ifs <;> push_cast <;> omega

end Extra

/-! ### Lemma 3.2: two-started runs -/

section TwoStart

variable (n m : ℕ) (X : Finset ℕ)

/-- Starts `q ≥ m` of runs of index `≥ 2` whose previous run has length `≥ 2`. -/
def tsG : Finset ℕ :=
  (range n).filter (fun q => 2 ≤ q ∧ q - 1 ∈ X ∧ q - 2 ∉ X ∧ m ≤ q ∧ 2 ≤ rk X q)

/-- Leg starts: starts of runs of index `≥ 2` other than the chosen two-started ones `Q`. -/
def tsLeg (Q : Finset ℕ) : Finset ℕ :=
  (range n).filter (fun q => 1 ≤ q ∧ q - 1 ∈ X ∧ 2 ≤ rk X q ∧ q ∉ Q)

/-- Start letters: `1` on run `1` and on `Q`, the next leg letter elsewhere. -/
def tsL (Q : Finset ℕ) (p : ℕ) : ℕ := if rk X p = 1 ∨ p ∈ Q then 1 else 2 + rk (tsLeg n X Q) p

/-- The filling of Lemma 3.2, with two-started runs at the good starts below `θ`. -/
def tsWord (θ : ℕ) : ℕ → ℕ := fill X (tsL n X ((tsG n m X).filter (· < θ))) ∅

variable {n m X}

theorem mem_tsG {q : ℕ} :
    q ∈ tsG n m X ↔ q < n ∧ 2 ≤ q ∧ q - 1 ∈ X ∧ q - 2 ∉ X ∧ m ≤ q ∧ 2 ≤ rk X q := by
  simp [tsG]

theorem mem_tsLeg {Q : Finset ℕ} {q : ℕ} :
    q ∈ tsLeg n X Q ↔ q < n ∧ 1 ≤ q ∧ q - 1 ∈ X ∧ 2 ≤ rk X q ∧ q ∉ Q := by
  simp [tsLeg]

theorem tsGood (hX : X ⊆ range (n - 1)) (Q : Finset ℕ) : Good n X (tsL n X Q) ∅ where
  hX := hX
  hL x _ := by unfold tsL; split_ifs <;> omega
  hEn p hp := by simp at hp
  hEs p hp := by simp at hp
  hEr p hp := by simp at hp

theorem asc_tsWord (hX : X ⊆ range (n - 1)) (θ : ℕ) : asc n (tsWord n m X θ) = X := by
  unfold tsWord
  set Q := (tsG n m X).filter (· < θ)
  apply asc_fill hX (tsGood hX Q).hL
  · intro x hx
    have hxn : x + 1 < n := (tsGood hX Q).lt hx
    by_cases h1 : rk X (x + 1) = 1 ∨ x + 1 ∈ Q
    · have hL1 : tsL n X Q (x + 1) = 1 := by unfold tsL; rw [if_pos h1]
      rw [hL1]
      have : fill X (tsL n X Q) ∅ x = 0 := by
        rcases h1 with h1 | h1
        · rw [rk_succ_of_mem hx] at h1
          unfold fill; rw [if_pos (by omega)]
        · rw [Finset.mem_filter, mem_tsG] at h1
          obtain ⟨⟨_, h2, _, hx2, _⟩, _⟩ := h1
          unfold fill
          split_ifs with h0 hs
          · rfl
          · exact absurd (show x + 1 - 2 ∈ X by rw [show x + 1 - 2 = x - 1 by omega]; exact hs.2) hx2
          all_goals simp_all
      omega
    · have hL2 : tsL n X Q (x + 1) = 2 + rk (tsLeg n X Q) (x + 1) := by
        unfold tsL; rw [if_neg h1]
      rw [hL2]
      unfold fill
      split_ifs with h0 hs
      · omega
      · unfold tsL
        split_ifs with h3
        · omega
        · have hmem : x ∈ tsLeg n X Q := by
            rw [mem_tsLeg]
            push_neg at h3
            exact ⟨by omega, hs.1, hs.2, by omega, h3.2⟩
          have := rk_lt_rk hmem (show x < x + 1 by omega)
          omega
      all_goals first | omega | simp_all
  · intro p hp; simp at hp

/-- Letter counts of the two-started-runs filling. -/
theorem cnt_tsWord (hX : X ⊆ range (n - 1)) (hX1 : 1 ≤ X.card) {θ : ℕ} (r : ℕ) :
    cnt (tsWord n m X θ) n r =
      if r = 0 then (n : ℤ) - X.card
      else if r = 1 then 1 + ((tsG n m X).filter (· < θ)).card
      else if r ≤ 1 + (tsLeg n X ((tsG n m X).filter (· < θ))).card then 1 else 0 := by
  set Q := (tsG n m X).filter (· < θ)
  have hg := tsGood hX Q
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · unfold tsWord; simpa using hg.cnt_zero
  · unfold tsWord
    rw [hg.cnt_pos hr, if_neg (show r ≠ 0 by omega)]
    simp only [Finset.card_empty, Nat.cast_zero, ite_self, add_zero]
    by_cases h1 : r = 1
    · subst h1
      rw [if_pos rfl]
      -- starts carrying `1`: the run-1 start and `Q`
      have hfil : X.filter (fun x => tsL n X Q (x + 1) = 1) =
          X.filter (fun x => rk X x = 0) ∪ X.filter (fun x => x + 1 ∈ Q) := by
        ext x
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
        unfold tsL
        constructor
        · rintro ⟨hx, h⟩
          split_ifs at h with hc
          · rw [rk_succ_of_mem hx] at hc
            rcases hc with hc | hc
            · exact Or.inl ⟨hx, by omega⟩
            · exact Or.inr ⟨hx, hc⟩
          · omega
        · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
          · refine ⟨hx, ?_⟩; rw [if_pos (Or.inl (by rw [rk_succ_of_mem hx]; omega))]
          · exact ⟨hx, by rw [if_pos (Or.inr h)]⟩
      rw [hfil, Finset.card_union_of_disjoint, card_rk_eq, if_pos (by omega)]
      · have hQ : (X.filter (fun x => x + 1 ∈ Q)).card = Q.card := by
          rw [← Finset.card_image_of_injective _ (add_left_injective 1)]
          congr 1
          ext q
          simp only [Finset.mem_image, Finset.mem_filter]
          constructor
          · rintro ⟨x, ⟨_, hq⟩, rfl⟩; exact hq
          · intro hq
            have hq' := hq
            rw [Finset.mem_filter, mem_tsG] at hq'
            exact ⟨q - 1, ⟨hq'.1.2.2.1, by rw [show q - 1 + 1 = q by omega]; exact hq⟩, by omega⟩
        rw [hQ]; push_cast; ring
      · rw [Finset.disjoint_left]
        intro x h0 hq
        rw [Finset.mem_filter] at h0 hq
        have hq2 := hq.2
        rw [Finset.mem_filter, mem_tsG, rk_succ_of_mem h0.1] at hq2
        omega
    · rw [if_neg h1]
      have hr2 : 2 ≤ r := by omega
      have hfil : X.filter (fun x => tsL n X Q (x + 1) = r) =
          (X.filter (fun x => x + 1 ∈ tsLeg n X Q ∧ rk (tsLeg n X Q) (x + 1) = r - 2)) := by
        apply Finset.filter_congr
        intro x hx
        have hxn : x + 1 < n := hg.lt hx
        unfold tsL
        rw [mem_tsLeg, rk_succ_of_mem hx]
        split_ifs with hc
        · constructor
          · intro h; omega
          · rintro ⟨⟨_, _, _, h2, hQ⟩, _⟩
            rcases hc with hc | hc
            · omega
            · exact absurd hc hQ
        · push_neg at hc
          constructor
          · intro h
            refine ⟨⟨hxn, by omega, by simpa using hx, by omega, hc.2⟩, by omega⟩
          · rintro ⟨_, h⟩; omega
      have himg : (X.filter (fun x => x + 1 ∈ tsLeg n X Q ∧
          rk (tsLeg n X Q) (x + 1) = r - 2)).image (· + 1) =
          (tsLeg n X Q).filter (fun q => rk (tsLeg n X Q) q = r - 2) := by
        ext q
        simp only [Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨x, ⟨_, h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          have h1' := mem_tsLeg.mp h1
          exact ⟨q - 1, ⟨h1'.2.2.1, by rw [show q - 1 + 1 = q by omega]; exact ⟨h1, h2⟩⟩, by omega⟩
      rw [hfil, ← Finset.card_image_of_injective _ (add_left_injective 1), himg, card_rk_eq]
      split_ifs <;> push_cast <;> omega

end TwoStart

/-! ### Lattice property and Corollary 3.3 -/

theorem fill_ge_two {X : Finset ℕ} {L : ℕ → ℕ} {E : Finset ℕ} {p : ℕ}
    (h : 2 ≤ fill X L E p) : 1 ≤ p ∧ p - 1 ∈ X ∧ fill X L E p = L p := by
  unfold fill at h ⊢
  split_ifs at h ⊢ with h0 hs hE <;> first | omega | exact ⟨hs.1, hs.2, rfl⟩

theorem rk_le_card (X : Finset ℕ) (p : ℕ) : rk X p ≤ X.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem exists_threshold (C : Finset ℕ) {k : ℕ} (hk : k ≤ C.card) :
    ∃ θ, (C.filter (· < θ)).card = k := by
  rcases lt_or_eq_of_le hk with h | rfl
  · obtain ⟨y, _, hy⟩ := rk_surj h; exact ⟨y, hy⟩
  · refine ⟨C.sup id + 1, congrArg _ (Finset.filter_true_of_mem fun y hy => ?_)⟩
    have := Finset.le_sup (f := id) hy; simp only [id] at this; omega

/-- The start with run index `1`. -/
theorem exists_first {X : Finset ℕ} (hX1 : 1 ≤ X.card) : ∃ x0 ∈ X, rk X x0 = 0 := rk_surj hX1

section Lattice

variable {n m : ℕ} {X : Finset ℕ}

theorem lattice_exWord (hX : X ⊆ range (n - 1)) (hX1 : 1 ≤ X.card) {b θ : ℕ}
    (hE : ((exC n m X).filter (· < θ)).card = b - 1) (hb : 1 ≤ b)
    (hA : b ≤ ((range (m - 1)).filter (· ∉ X)).card) : Lattice n (exWord n m X θ) := by
  obtain ⟨x0, hx0, hr0⟩ := exists_first hX1
  have hval : ∀ p, 2 ≤ exWord n m X θ p → ∃ x ∈ X, p = x + 1 ∧ exWord n m X θ p = rk X x + 1 := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := fill_ge_two hp
    refine ⟨p - 1, h2, by omega, ?_⟩
    unfold exWord at hp ⊢; rw [h3]; rw [h3] at hp
    unfold exL at hp ⊢
    have := rk_succ_of_mem h2; rw [show p - 1 + 1 = p by omega] at this
    split_ifs at hp ⊢ <;> omega
  refine lattice_of (u := exWord n m X θ) ?_ ?_ ?_
  · intro r hr p q hp hq
    obtain ⟨x, hx, rfl, hpx⟩ := hval p (by omega)
    obtain ⟨y, hy, rfl, hqy⟩ := hval q (by omega)
    have := rk_injOn X hx hy (by omega)
    rw [this]
  · intro r hr p hp
    obtain ⟨x, hx, rfl, hpx⟩ := hval p (by omega)
    have hrx : rk X x = r := by omega
    obtain ⟨y, hy, hyr⟩ := rk_surj (show r - 1 < X.card by
      have := rk_lt_card hx; omega)
    refine ⟨y + 1, ?_, ?_⟩
    · have := lt_of_rk_lt (Y := X) (show rk X y < rk X x by omega); omega
    · unfold exWord; rw [fill_start hy]; unfold exL; rw [rk_succ_of_mem hy]
      split_ifs <;> omega
  · apply ones_le_zeros (n := n) (m := m) (u := exWord n m X θ) X (fill_zero _ _ _)
      (show 1 ≤ x0 + 1 by omega) (b := b)
    · intro p hp
      unfold exWord fill at hp
      split_ifs at hp with h0 hs hEp
      · left
        unfold exL at hp
        have := rk_succ_of_mem hs.2; rw [show p - 1 + 1 = p by omega] at this
        split_ifs at hp with h1
        · have := rk_injOn X hs.2 hx0 (by omega); omega
        · omega
      · right
        rw [Finset.mem_filter, mem_exC] at hEp
        obtain ⟨_, _, _, _, y, _, hym, hyp⟩ := hEp.1
        omega
    · have := cnt_exWord (m := m) (θ := θ) hX hX1 1
      simp only [one_ne_zero, if_false, if_true] at this
      rw [this, hE]; push_cast [hb]; omega
    · exact hA
    · intro x hx hxX
      unfold exWord; rw [fill_nonstart hxX]
      split_ifs with h0 hEx
      · rfl
      · rw [Finset.mem_filter, mem_exC] at hEx
        obtain ⟨_, _, _, _, y, _, hym, hyp⟩ := hEx.1
        omega
      · rfl

theorem card_tsLeg (hX : X ⊆ range (n - 1)) (hX1 : 1 ≤ X.card) (θ : ℕ) :
    (tsLeg n X ((tsG n m X).filter (· < θ))).card + ((tsG n m X).filter (· < θ)).card =
      X.card - 1 := by
  set Q := (tsG n m X).filter (· < θ)
  have hQ : Q ⊆ (X.filter (fun x => rk X x ≠ 0)).image (· + 1) := by
    intro q hq
    have hq' := hq
    rw [Finset.mem_filter, mem_tsG] at hq'
    obtain ⟨⟨_, h2, h1, _, _, hrk⟩, _⟩ := hq'
    refine Finset.mem_image.mpr ⟨q - 1, Finset.mem_filter.mpr ⟨h1, ?_⟩, by omega⟩
    have := rk_succ_of_mem h1; rw [show q - 1 + 1 = q by omega] at this; omega
  have hLeg : tsLeg n X Q = (X.filter (fun x => rk X x ≠ 0)).image (· + 1) \ Q := by
    ext q
    rw [mem_tsLeg, Finset.mem_sdiff, Finset.mem_image]
    constructor
    · rintro ⟨hqn, hq1, hqX, hrk, hQ'⟩
      refine ⟨⟨q - 1, Finset.mem_filter.mpr ⟨hqX, ?_⟩, by omega⟩, hQ'⟩
      have := rk_succ_of_mem hqX; rw [show q - 1 + 1 = q by omega] at this; omega
    · rintro ⟨⟨x, hx, rfl⟩, hQ'⟩
      rw [Finset.mem_filter] at hx
      have := rk_succ_of_mem hx.1
      have hxn := Finset.mem_range.mp (hX hx.1)
      exact ⟨by omega, by omega, by simpa using hx.1, by omega, hQ'⟩
  rw [hLeg, Finset.card_sdiff_of_subset hQ, Finset.card_image_of_injective _ (add_left_injective 1)]
  have hcard := Finset.card_le_card hQ
  rw [Finset.card_image_of_injective _ (add_left_injective 1)] at hcard
  have h0 : (X.filter (fun x => rk X x ≠ 0)).card = X.card - 1 := by
    have := Finset.card_filter_add_card_filter_not (s := X) (p := fun x => rk X x = 0)
    rw [card_rk_eq, if_pos (by omega)] at this
    simp only [ne_eq]; omega
  omega

theorem lattice_tsWord (hX : X ⊆ range (n - 1)) (hX1 : 1 ≤ X.card) {b θ : ℕ}
    (hQ : ((tsG n m X).filter (· < θ)).card = b - 1) (hb : 1 ≤ b)
    (hA : b ≤ ((range (m - 1)).filter (· ∉ X)).card) : Lattice n (tsWord n m X θ) := by
  obtain ⟨x0, hx0, hr0⟩ := exists_first hX1
  set Q := (tsG n m X).filter (· < θ)
  set Leg := tsLeg n X Q
  have hval : ∀ p, 2 ≤ tsWord n m X θ p →
      p ∈ Leg ∧ tsWord n m X θ p = 2 + rk Leg p := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := fill_ge_two hp
    unfold tsWord at hp ⊢; rw [h3]; rw [h3] at hp
    unfold tsL at hp ⊢
    split_ifs at hp ⊢ with hc
    · omega
    · push_neg at hc
      have := rk_succ_of_mem h2; rw [show p - 1 + 1 = p by omega] at this
      have hpn : p < n := by have := Finset.mem_range.mp (hX h2); omega
      exact ⟨mem_tsLeg.mpr ⟨hpn, h1, h2, by omega, hc.2⟩, rfl⟩
  have hLegval : ∀ q ∈ Leg, tsWord n m X θ q = 2 + rk Leg q := by
    intro q hq
    have hq' := mem_tsLeg.mp hq
    unfold tsWord
    have := fill_start (L := tsL n X Q) (E := ∅) hq'.2.2.1
    rw [show q - 1 + 1 = q by omega] at this
    rw [this]; unfold tsL; rw [if_neg (by push_neg; exact ⟨by omega, hq'.2.2.2.2⟩)]
  refine lattice_of (u := tsWord n m X θ) ?_ ?_ ?_
  · intro r hr p q hp hq
    obtain ⟨hpL, hpv⟩ := hval p (by omega)
    obtain ⟨hqL, hqv⟩ := hval q (by omega)
    exact rk_injOn Leg hpL hqL (by omega)
  · intro r hr p hp
    obtain ⟨hpL, hpv⟩ := hval p (by omega)
    rcases Nat.lt_or_ge r 2 with hr2 | hr2
    · -- the first leg letter follows the run-`1` start
      refine ⟨x0 + 1, ?_, ?_⟩
      · have hp' := mem_tsLeg.mp hpL
        have := rk_succ_of_mem hx0
        exact lt_of_rk_lt (Y := X) (by omega)
      · unfold tsWord; rw [fill_start hx0]; unfold tsL
        rw [if_pos (Or.inl (by rw [rk_succ_of_mem hx0]; omega))]; omega
    · obtain ⟨q, hq, hqr⟩ := rk_surj (show r - 2 < Leg.card by
        have := rk_lt_card hpL; omega)
      refine ⟨q, lt_of_rk_lt (Y := Leg) (by omega), ?_⟩
      rw [hLegval q hq]; omega
  · apply ones_le_zeros (n := n) (m := m) (u := tsWord n m X θ) X (fill_zero _ _ _)
      (show 1 ≤ x0 + 1 by omega) (b := b)
    · intro p hp
      unfold tsWord fill at hp
      split_ifs at hp with h0 hs hEp
      · unfold tsL at hp
        split_ifs at hp with hc
        · rcases hc with hc | hc
          · left
            have := rk_succ_of_mem hs.2; rw [show p - 1 + 1 = p by omega] at this
            have := rk_injOn X hs.2 hx0 (by omega); omega
          · right
            rw [Finset.mem_filter, mem_tsG] at hc
            exact hc.1.2.2.2.2.1
        · omega
      · simp at hEp
    · have := cnt_tsWord (m := m) (θ := θ) hX hX1 1
      simp only [one_ne_zero, if_false, if_true] at this
      rw [this, hQ]; push_cast [hb]; omega
    · exact hA
    · intro x _ hxX
      unfold tsWord; rw [fill_nonstart hxX]
      split_ifs <;> first | rfl | simp_all

end Lattice

/-- **Corollary 3.3.** If `1 ≤ |S| < |T|`, `S` meets the hypotheses of Lemma 3.1 and `T` those of
Lemma 3.2 (with `c = |S| - 1` and `b = |T| - |S| + 1`), then `(S, T)` occurs. -/
theorem pair_of_fillings {n m : ℕ} {S T : Finset ℕ} (hS : S ⊆ range (n - 1))
    (hT : T ⊆ range (n - 1)) (hs : 1 ≤ S.card) (hst : S.card < T.card)
    (hAS : T.card - S.card + 1 ≤ ((range (m - 1)).filter (· ∉ S)).card)
    (hAT : T.card - S.card + 1 ≤ ((range (m - 1)).filter (· ∉ T)).card)
    (hCS : T.card - S.card ≤ (exC n m S).card)
    (hGT : T.card - S.card ≤ (tsG n m T).card) : (S, T) ∈ pairs n := by
  obtain ⟨θ, hθ⟩ := exists_threshold (exC n m S) hCS
  obtain ⟨θ', hθ'⟩ := exists_threshold (tsG n m T) hGT
  have hT1 : 1 ≤ T.card := by omega
  have hb : T.card - S.card + 1 - 1 = T.card - S.card := by omega
  have hu := lattice_exWord hS hs (b := T.card - S.card + 1) (by rw [hb]; exact hθ) (by omega) hAS
  have hv := lattice_tsWord hT hT1 (b := T.card - S.card + 1) (by rw [hb]; exact hθ') (by omega)
    hAT
  have hleg := card_tsLeg (m := m) hT hT1 θ'
  rw [hθ'] at hleg
  have hcont : ∀ r, cnt (exWord n m S θ) n r = cnt (tsWord n m T θ') n r := by
    intro r
    rw [cnt_exWord hS hs, cnt_tsWord hT hT1, hθ, hθ']
    split_ifs <;> push_cast <;> omega
  have := Growth.mem_pairs_of_words hu hv hcont
  rwa [asc_exWord hS, asc_tsWord hT] at this

end Fill

end Stanley
