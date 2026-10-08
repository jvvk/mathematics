/-
  Part C. Choosing the pivot and the marked sets.

  For `X ⊆ {0, …, n-2}` and a pivot `c`, the marked set is
    `mark X c = {c} ∪ {x ∈ X | x < c} ∪ {x + 1 | x ∈ X, c ≤ x}`.
  The pivot position `p` is found by a discrete intermediate value argument: with
  `a p = #{s ∈ S | s < p}`, `b x = #{t ∈ T | t < x}` and `ψ p = b (p + k - 2 a p) + a p`,
  `ψ 0 ≤ k ≤ ψ (n-1)` and `ψ` rises by at most one per step, so `ψ p = k` for some `p`.
-/
import LeanProofs.Stanley.Construct

namespace Stanley

open Finset

/-- Marked set for a descent set `X` and pivot `c`. -/
def mark (X : Finset ℕ) (c : ℕ) : Finset ℕ :=
  insert c (X.filter (· < c) ∪ (X.filter (c ≤ ·)).image (· + 1))

theorem mem_mark {X : Finset ℕ} {c y : ℕ} :
    y ∈ mark X c ↔ y = c ∨ (y ∈ X ∧ y < c) ∨ (∃ x ∈ X, c ≤ x ∧ x + 1 = y) := by
  simp only [mark, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro (h | h | ⟨x, ⟨hx, hc⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨x, hx, hc, rfl⟩)
  · rintro (h | h | ⟨x, hx, hc, rfl⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨x, ⟨hx, hc⟩, rfl⟩)

/-- The descent pattern of the marked set recovers `X`. -/
theorem mark_desc {n : ℕ} {X : Finset ℕ} (hX : X ⊆ range (n - 1)) (c : ℕ) :
    (range (n - 1)).filter (fun i => (i ∈ mark X c ∧ i < c) ∨ (i + 1 ∈ mark X c ∧ c ≤ i)) = X := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, mem_mark]
  constructor
  · rintro ⟨_, ⟨h, hlt⟩ | ⟨h, hge⟩⟩
    · rcases h with h | ⟨hx, _⟩ | ⟨x, _, hcx, hx1⟩
      · omega
      · exact hx
      · omega
    · rcases h with h | ⟨_, h2⟩ | ⟨x, hx, _, hx1⟩
      · omega
      · omega
      · have : x = i := by omega
        exact this ▸ hx
  · intro hi
    have hin := Finset.mem_range.mp (hX hi)
    refine ⟨hin, ?_⟩
    rcases lt_or_ge i c with hlt | hge
    · exact Or.inl ⟨Or.inr (Or.inl ⟨hi, hlt⟩), hlt⟩
    · exact Or.inr ⟨Or.inr (Or.inr ⟨i, hi, hge, rfl⟩), hge⟩

theorem mark_subset {n : ℕ} {X : Finset ℕ} (hX : X ⊆ range (n - 1)) {c : ℕ} (hc : c < n) :
    mark X c ⊆ range n := by
  intro y hy
  have := fun x (h : x ∈ X) => Finset.mem_range.mp (hX h)
  rcases mem_mark.mp hy with rfl | ⟨hy, _⟩ | ⟨x, hx, _, rfl⟩
  · exact Finset.mem_range.mpr hc
  · exact Finset.mem_range.mpr (by have := this y hy; omega)
  · exact Finset.mem_range.mpr (by have := this x hx; omega)

theorem card_filter_lt_add_ge (X : Finset ℕ) (c : ℕ) :
    (X.filter (· < c)).card + (X.filter (c ≤ ·)).card = X.card := by
  have := Finset.card_filter_add_card_filter_not (s := X) (p := fun x => x < c)
  have h2 : X.filter (fun x => ¬ x < c) = X.filter (c ≤ ·) := by
    ext x; simp only [Finset.mem_filter, not_lt]
  rw [h2] at this
  exact this

theorem card_mark (X : Finset ℕ) (c : ℕ) : (mark X c).card = X.card + 1 := by
  unfold mark
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (add_left_injective 1),
      card_filter_lt_add_ge]
    rw [Finset.disjoint_left]
    intro y hy hy'
    simp only [Finset.mem_filter, Finset.mem_image] at hy hy'
    obtain ⟨x, ⟨_, hx⟩, rfl⟩ := hy'
    omega
  · simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image, not_or, not_and, not_exists]
    exact ⟨fun _ h => lt_irrefl _ h, fun x _ hx => by omega⟩

/-- Marked elements below the pivot are the elements of `X` below it. -/
theorem mark_filter_lt (X : Finset ℕ) (c : ℕ) :
    (mark X c).filter (· < c) = X.filter (· < c) := by
  ext y
  simp only [Finset.mem_filter, mem_mark]
  constructor
  · rintro ⟨h | ⟨hy, _⟩ | ⟨x, _, hcx, rfl⟩, hlt⟩
    · omega
    · exact ⟨hy, hlt⟩
    · omega
  · rintro ⟨hy, hlt⟩; exact ⟨Or.inr (Or.inl ⟨hy, hlt⟩), hlt⟩

/-- Marked elements above the pivot are the shifted elements of `X` at or above it. -/
theorem card_mark_filter_gt (X : Finset ℕ) (c : ℕ) :
    ((mark X c).filter (c < ·)).card = (X.filter (c ≤ ·)).card := by
  have : (mark X c).filter (c < ·) = (X.filter (c ≤ ·)).image (· + 1) := by
    ext y
    simp only [Finset.mem_filter, mem_mark, Finset.mem_image]
    constructor
    · rintro ⟨h | ⟨_, hlt⟩ | ⟨x, hx, hcx, rfl⟩, hgt⟩
      · omega
      · omega
      · exact ⟨x, ⟨hx, hcx⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hcx⟩, rfl⟩
      exact ⟨Or.inr (Or.inr ⟨x, hx, hcx, rfl⟩), by omega⟩
  rw [this, Finset.card_image_of_injective _ (add_left_injective 1)]

/-- Unmarked elements of `{0, …, n-1}` below the pivot. -/
theorem card_compl_mark_filter_lt {n : ℕ} (X : Finset ℕ) {c : ℕ} (hc : c < n) :
    ((range n \ mark X c).filter (· < c)).card = c - (X.filter (· < c)).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := range c) (p := fun y => y ∈ X)
  have h1 : (range c).filter (fun y => y ∈ X) = X.filter (· < c) := by
    ext y; simp only [Finset.mem_filter, Finset.mem_range]; tauto
  have h2 : (range n \ mark X c).filter (· < c) = (range c).filter (fun y => y ∉ X) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_range, mem_mark]
    constructor
    · rintro ⟨⟨_, hm⟩, hlt⟩
      exact ⟨hlt, fun hy => hm (Or.inr (Or.inl ⟨hy, hlt⟩))⟩
    · rintro ⟨hlt, hy⟩
      refine ⟨⟨by omega, ?_⟩, hlt⟩
      rintro (h | ⟨h, _⟩ | ⟨x, _, hcx, hx⟩)
      · omega
      · exact hy h
      · omega
  rw [h2, Finset.card_range] at *
  rw [h1] at hsplit
  omega

section IVT

/-- `a p = #{s ∈ S | s < p}`. -/
def acount (S : Finset ℕ) (p : ℕ) : ℕ := (S.filter (· < p)).card

/-- `ψ p = #{t ∈ T | t < p + k - 2 a p} + a p`. -/
def psi (S T : Finset ℕ) (k p : ℕ) : ℕ :=
  (T.filter (· < p + k - 2 * acount S p)).card + acount S p

theorem acount_le (S : Finset ℕ) (p : ℕ) : acount S p ≤ p := by
  unfold acount
  calc (S.filter (· < p)).card ≤ (range p).card := by
        apply Finset.card_le_card; intro x hx
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
    _ = p := Finset.card_range p

theorem acount_le_card (S : Finset ℕ) (p : ℕ) : acount S p ≤ S.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem acount_succ (S : Finset ℕ) (p : ℕ) :
    acount S (p + 1) = acount S p + if p ∈ S then 1 else 0 := by
  unfold acount
  split_ifs with hp
  · have : S.filter (· < p + 1) = insert p (S.filter (· < p)) := by
      ext x; simp only [Finset.mem_filter, Finset.mem_insert]; constructor
      · rintro ⟨hx, hlt⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl h
      · rintro (rfl | ⟨hx, hlt⟩)
        · exact ⟨hp, Nat.lt_succ_self _⟩
        · exact ⟨hx, by omega⟩
    rw [this, Finset.card_insert_of_notMem (by simp)]
  · have : S.filter (· < p + 1) = S.filter (· < p) := by
      ext x; simp only [Finset.mem_filter]; constructor
      · rintro ⟨hx, hlt⟩
        refine ⟨hx, ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
        · exact h
        · exact absurd (h ▸ hx) hp
      · rintro ⟨hx, hlt⟩; exact ⟨hx, by omega⟩
    rw [this, add_zero]

theorem acount_lt_of_mem {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) : acount S p < S.card := by
  unfold acount
  apply Finset.card_lt_card
  refine ⟨Finset.filter_subset _ _, fun h => ?_⟩
  have := Finset.mem_filter.mp (h hp)
  exact lt_irrefl _ this.2

theorem bcount_mono (T : Finset ℕ) {x y : ℕ} (h : x ≤ y) :
    (T.filter (· < x)).card ≤ (T.filter (· < y)).card := by
  apply Finset.card_le_card
  intro z hz
  simp only [Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, by omega⟩

theorem bcount_succ_le (T : Finset ℕ) (x : ℕ) :
    (T.filter (· < x + 1)).card ≤ (T.filter (· < x)).card + 1 := by
  calc (T.filter (· < x + 1)).card ≤ (insert x (T.filter (· < x))).card := by
        apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_insert] at hz ⊢
        rcases Nat.lt_succ_iff_lt_or_eq.mp hz.2 with h | h
        · exact Or.inr ⟨hz.1, h⟩
        · exact Or.inl h
    _ ≤ (T.filter (· < x)).card + 1 := Finset.card_insert_le _ _

theorem psi_succ_le (S T : Finset ℕ) (p : ℕ) :
    psi S T S.card (p + 1) ≤ psi S T S.card p + 1 := by
  unfold psi
  have hap := acount_le S p
  have hak := acount_le_card S p
  rw [acount_succ]
  split_ifs with hp
  · have hlt := acount_lt_of_mem hp
    have hv : p + 1 + S.card - 2 * (acount S p + 1) ≤ p + S.card - 2 * acount S p := by omega
    have := bcount_mono T hv
    omega
  · have hv : p + 1 + S.card - 2 * (acount S p + 0) = (p + S.card - 2 * acount S p) + 1 := by
      omega
    rw [hv]
    have := bcount_succ_le T (p + S.card - 2 * acount S p)
    omega

theorem exists_psi_eq {n : ℕ} {S : Finset ℕ} (T : Finset ℕ) (hS : S ⊆ range (n - 1)) :
    ∃ p, p ≤ n - 1 ∧ psi S T S.card p = S.card := by
  have h0 : psi S T S.card 0 ≤ S.card := by
    have ha0 : acount S 0 = 0 := Nat.le_zero.mp (acount_le S 0)
    unfold psi
    rw [ha0, mul_zero, Nat.sub_zero, zero_add, add_zero]
    calc (T.filter (· < S.card)).card ≤ (range S.card).card := by
          apply Finset.card_le_card; intro x hx
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hx).2
      _ = S.card := Finset.card_range _
  have hN : S.card ≤ psi S T S.card (n - 1) := by
    have : acount S (n - 1) = S.card := by
      unfold acount
      congr 1
      ext x; simp only [Finset.mem_filter, and_iff_left_iff_imp]
      intro hx; exact Finset.mem_range.mp (hS hx)
    unfold psi; rw [this]; exact Nat.le_add_left _ _
  classical
  have hex : ∃ p, S.card ≤ psi S T S.card p := ⟨n - 1, hN⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hN, ?_⟩
  have hge := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h] at hge ⊢; omega
  · obtain ⟨q, hq⟩ : ∃ q, Nat.find hex = q + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hlt : ¬ S.card ≤ psi S T S.card q := Nat.find_min hex (by omega)
    have hstep := psi_succ_le S T q
    rw [hq] at hge ⊢
    omega

end IVT

/-- Non-descents below `p` are at most the non-descents in `{0, …, n-2}`. -/
theorem sub_acount_le {n : ℕ} {S : Finset ℕ} (hS : S ⊆ range (n - 1)) {p : ℕ} (hp : p ≤ n - 1) :
    p - acount S p ≤ (n - 1) - S.card := by
  have e1 := Finset.card_filter_add_card_filter_not (s := range p) (p := fun y => y ∈ S)
  have e2 := Finset.card_filter_add_card_filter_not (s := range (n - 1)) (p := fun y => y ∈ S)
  have f1 : (range p).filter (fun y => y ∈ S) = S.filter (· < p) := by
    ext y; simp only [Finset.mem_filter, Finset.mem_range]; tauto
  have f2 : (range (n - 1)).filter (fun y => y ∈ S) = S := by
    ext y; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_range.mp (hS h), h⟩⟩
  have hsub : (range p).filter (fun y => y ∉ S) ⊆ (range (n - 1)).filter (fun y => y ∉ S) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_range] at hy ⊢
    exact ⟨by omega, hy.2⟩
  have := Finset.card_le_card hsub
  rw [f1, Finset.card_range] at e1
  rw [f2, Finset.card_range] at e2
  unfold acount
  omega

/-- **Main construction.** If `S, T ⊆ {0, …, n-2}` have the same size, there is a bijection
`w` of `{0, …, n-1}` (with inverse `u`) whose descent set is `S` and whose inverse has descent
set `T`. -/
theorem exists_pair {n : ℕ} {S T : Finset ℕ} (hS : S ⊆ range (n - 1)) (hT : T ⊆ range (n - 1))
    (hk : S.card = T.card) :
    ∃ w u : ℕ → ℕ, (∀ q < n, w q < n) ∧ (∀ x < n, u x < n) ∧ (∀ q < n, u (w q) = q) ∧
      (∀ x < n, w (u x) = x) ∧ desc n w = S ∧ desc n u = T := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hS0 : S = ∅ := Finset.subset_empty.mp (by simpa using hS)
    have hT0 : T = ∅ := Finset.subset_empty.mp (by simpa using hT)
    refine ⟨id, id, fun q h => h, fun x h => h, fun _ _ => rfl, fun _ _ => rfl, ?_, ?_⟩ <;>
      simp [desc, hS0, hT0]
  obtain ⟨p, hpn, hpsi⟩ := exists_psi_eq T hS
  have hap : acount S p ≤ p := acount_le S p
  have hak : acount S p ≤ S.card := acount_le_card S p
  have hsa := sub_acount_le hS hpn
  obtain ⟨v, hvdef⟩ : ∃ v, v = p + S.card - 2 * acount S p := ⟨_, rfl⟩
  have hb : (T.filter (· < v)).card + acount S p = S.card := by
    rw [hvdef]; exact hpsi
  obtain ⟨k, hkdef⟩ : ∃ k, k = S.card := ⟨_, rfl⟩
  obtain ⟨a, hadef⟩ : ∃ a, a = acount S p := ⟨_, rfl⟩
  rw [← hkdef, ← hadef] at hb hvdef hak hsa
  rw [← hadef] at hap
  have hkn : k ≤ n - 1 := by
    rw [hkdef]; simpa using Finset.card_le_card hS
  have hvn : v < n := by omega
  have hp_lt : p < n := by omega
  set P := mark S p
  set V := mark T v
  have hPn : P ⊆ range n := mark_subset hS hp_lt
  have hVn : V ⊆ range n := mark_subset hT hvn
  have hPcard : P.card = k + 1 := by rw [card_mark, hkdef]
  have hVcard : V.card = k + 1 := by rw [card_mark, ← hk, hkdef]
  have hPc : (range n \ P).card = n - (k + 1) := by
    rw [Finset.card_sdiff_of_subset hPn, Finset.card_range, hPcard]
  have hVc : (range n \ V).card = n - (k + 1) := by
    rw [Finset.card_sdiff_of_subset hVn, Finset.card_range, hVcard]
  have hA : (P.filter (· < p)).card = (V.filter (v < ·)).card := by
    rw [mark_filter_lt, card_mark_filter_gt]
    have := card_filter_lt_add_ge T v
    unfold acount at hadef
    rw [← hadef]
    omega
  have hD : ((range n \ P).filter (· < p)).card = ((range n \ V).filter (· < v)).card := by
    rw [card_compl_mark_filter_lt S hp_lt, card_compl_mark_filter_lt T hvn]
    unfold acount at hadef
    rw [← hadef]
    omega
  have hpP : p ∈ P := by simp [P, mark]
  have hvV : v ∈ V := by simp [V, mark]
  set w := rmatch n (k + 1) (n - (k + 1)) P V hPcard hVcard hPc hVc
  set u := rmatch n (k + 1) (n - (k + 1)) V P hVcard hPcard hVc hPc
  have hgood : Good n w P p v := rmatch_good hPcard hVcard hPc hVc hpP hvV hA hD
  have memc : ∀ q < n, q ∉ P → q ∈ range n \ P := fun q hq h =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hq, h⟩
  have memcV : ∀ x < n, x ∉ V → x ∈ range n \ V := fun x hx h =>
    Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hx, h⟩
  have hw : ∀ q < n, w q < n := by
    intro q hq
    by_cases h : q ∈ P
    · exact Finset.mem_range.mp (hVn (rmatch_mem hPcard hVcard hPc hVc h))
    · exact Finset.mem_range.mp (Finset.mem_sdiff.mp (rmatch_mem_c hPcard hVcard hPc hVc (memc q hq h))).1
  have hu : ∀ x < n, u x < n := by
    intro x hx
    by_cases h : x ∈ V
    · exact Finset.mem_range.mp (hPn (rmatch_mem hVcard hPcard hVc hPc h))
    · exact Finset.mem_range.mp (Finset.mem_sdiff.mp (rmatch_mem_c hVcard hPcard hVc hPc (memcV x hx h))).1
  have huw : ∀ q < n, u (w q) = q := by
    intro q hq
    by_cases h : q ∈ P
    · exact rmatch_inv hPcard hVcard hPc hVc h
    · exact rmatch_inv_c hPcard hVcard hPc hVc (memc q hq h)
  have hwu : ∀ x < n, w (u x) = x := by
    intro x hx
    by_cases h : x ∈ V
    · exact rmatch_inv hVcard hPcard hVc hPc h
    · exact rmatch_inv_c hVcard hPcard hVc hPc (memcV x hx h)
  have himg : P.image w = V := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      exact rmatch_mem hPcard hVcard hPc hVc hq
    · rw [Finset.card_image_of_injOn, hPcard, hVcard]
      intro q hq q' hq' he
      have h1 := huw q (Finset.mem_range.mp (hPn hq))
      have h2 := huw q' (Finset.mem_range.mp (hPn hq'))
      rw [← h1, ← h2]
      exact congrArg u he
  have hgood' : Good n u V v p := by
    have := hgood.inv (fun q hq => Finset.mem_range.mp (hPn hq)) hw hu huw hwu
    rwa [himg] at this
  refine ⟨w, u, hw, hu, huw, hwu, ?_, ?_⟩
  · rw [desc_eq hgood]; exact mark_desc hS p
  · rw [desc_eq hgood']; exact mark_desc hT v

end Stanley
