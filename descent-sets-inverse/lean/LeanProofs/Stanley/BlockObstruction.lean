/- The block obstruction. If `D(w⁻¹)` contains `|D(w)| + 1` consecutive integers, then the values
`i, i+1, …, i+|D(w)|+1` occur in `w` in decreasing order of position, which needs `|D(w)| + 1`
descents. Hence `(S, T)` never occurs when `T ⊇ {0, …, |S|}` (zero-indexed), and counting these
pairs and their mirror images gives `f(n) ≤ 4^(n-1) - 3^(n-1) + 1`. -/
import LeanProofs.Stanley.LowerGap

namespace Stanley
open Finset

/-- If the value drops from position `a` to a later position `b`, a descent lies in `[a, b)`. -/
theorem exists_desc_between {n : ℕ} (w : Equiv.Perm (Fin n)) {a b : ℕ} (hab : a < b) (hb : b < n)
    (h : w ⟨b, hb⟩ < w ⟨a, by omega⟩) : ∃ q ∈ descP w, a ≤ q ∧ q < b := by
  by_contra hno
  push Not at hno
  have mono : ∀ k, a ≤ k → k ≤ b → ∀ hk : k < n, w ⟨a, by omega⟩ ≤ w ⟨k, hk⟩ := by
    intro k hak
    induction k, hak using Nat.le_induction with
    | base => intro _ _; exact le_rfl
    | succ k hak ih =>
      intro hkb hk1
      have hk : k < n := by omega
      refine (ih (by omega) hk).trans (not_lt.mp fun hlt => ?_)
      have hmem : k ∈ descP w := by
        simp only [descP, mem_filter, mem_range]
        exact ⟨by omega, hk1, hlt⟩
      exact absurd (show k < b by omega) (not_lt.mpr (hno k hmem hak))
  exact absurd (mono b hab.le le_rfl hb) (not_le.mpr h)

/-- **The block obstruction.** -/
theorem not_mem_pairs_block {n : ℕ} {S T : Finset ℕ} {i : ℕ}
    (hT : ∀ j ≤ S.card, i + j ∈ T) : (S, T) ∉ pairs n := by
  intro hp
  obtain ⟨w, _, he⟩ := mem_image.mp hp
  have hS : descP w = S := congrArg Prod.fst he
  have hT' : descP w⁻¹ = T := congrArg Prod.snd he
  set s := S.card
  have hd : ∀ j ≤ s, ∃ h : i + j + 1 < n,
      w⁻¹ ⟨i + j + 1, h⟩ < w⁻¹ ⟨i + j, by omega⟩ := by
    intro j hj
    have := hT j hj
    rw [← hT'] at this
    simp only [descP, mem_filter, mem_range] at this
    exact this.2
  have hn : i + s + 1 < n := (hd s le_rfl).1
  -- positions of the values i, i+1, …, i+s+1
  let p : ℕ → ℕ := fun j => if h : i + j < n then (w⁻¹ ⟨i + j, h⟩ : ℕ) else 0
  have hp_lt : ∀ j, j ≤ s + 1 → p j < n := by
    intro j hj
    simp only [p, dif_pos (show i + j < n by omega)]
    exact (w⁻¹ _).is_lt
  have hp_dec : ∀ j ≤ s, p (j + 1) < p j := by
    intro j hj
    obtain ⟨h1, h2⟩ := hd j hj
    simp only [p, dif_pos h1, dif_pos (show i + j < n by omega), ← add_assoc]
    exact h2
  have hval : ∀ j (hj : j ≤ s + 1), w ⟨p j, hp_lt j hj⟩ = ⟨i + j, by omega⟩ := by
    intro j hj
    have hfin : (⟨p j, hp_lt j hj⟩ : Fin n) = w⁻¹ ⟨i + j, by omega⟩ := by
      ext; simp [p, dif_pos (show i + j < n by omega)]
    rw [hfin]; simp
  have hq : ∀ j ≤ s, ∃ q ∈ descP w, p (j + 1) ≤ q ∧ q < p j := by
    intro j hj
    apply exists_desc_between w (hp_dec j hj) (hp_lt j (by omega))
    rw [hval j (by omega), hval (j + 1) (by omega), Fin.lt_def]
    simp
  choose! q hqS hqlo hqhi using hq
  have hanti : ∀ j k, j ≤ k → k ≤ s + 1 → p k ≤ p j := by
    intro j k hjk hk
    induction k, hjk using Nat.le_induction with
    | base => exact le_rfl
    | succ k hjk ih => exact (hp_dec k (by omega)).le.trans (ih (by omega))
  have hinj : Set.InjOn q (range (s + 1) : Set ℕ) := by
    intro j hj k hk hjk
    simp only [coe_range, Set.mem_Iio] at hj hk
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := hqhi k (by omega); have := hqlo j (by omega)
      have := hanti (j + 1) k (by omega) (by omega); omega
    · have := hqhi j (by omega); have := hqlo k (by omega)
      have := hanti (k + 1) j (by omega) (by omega); omega
  have hsub : (range (s + 1)).image q ⊆ S := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hx
    rw [← hS]; exact hqS j (by simp at hj; omega)
  have := card_le_card hsub
  rw [card_image_of_injOn hinj, card_range] at this
  omega

/-- Supersets of `range k` inside `range N`. -/
theorem card_supersets {N k : ℕ} (hk : k ≤ N) :
    ((range N).powerset.filter (fun T => range k ⊆ T)).card = 2 ^ (N - k) := by
  have hkN : range k ⊆ range N := by intro x hx; simp at hx ⊢; omega
  have heq : ((range N).powerset.filter (fun T => range k ⊆ T)) =
      ((range N \ range k).powerset).image (fun U => U ∪ range k) := by
    ext T
    simp only [mem_filter, mem_powerset, mem_image]
    constructor
    · rintro ⟨hT, hk'⟩
      exact ⟨T \ range k, sdiff_subset_sdiff hT le_rfl, sdiff_union_of_subset hk'⟩
    · rintro ⟨U, hU, rfl⟩
      exact ⟨union_subset (hU.trans sdiff_subset) hkN, subset_union_right⟩
  have hinj : Set.InjOn (fun U => U ∪ range k) ((range N \ range k).powerset : Set _) := by
    intro U hU V hV hUV
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at hU hV
    have hdU : Disjoint U (range k) := disjoint_of_subset_left hU disjoint_sdiff_self_left
    have hdV : Disjoint V (range k) := disjoint_of_subset_left hV disjoint_sdiff_self_left
    have := congrArg (· \ range k) hUV
    simpa [union_sdiff_right, hdU.sdiff_eq_left, hdV.sdiff_eq_left] using this
  have hsd : (range N \ range k).card = N - k := by
    rw [show range N \ range k = Ico k N by ext x; simp; omega, Nat.card_Ico]
  rw [heq, card_image_of_injOn hinj, card_powerset, hsd]

/-- `2 ∑_{m<N} C(N,m) 2^(N-1-m) = 3^N - 1`. -/
theorem sum_choose_two_pow (N : ℕ) :
    2 * ∑ m ∈ range (N + 1), N.choose m * (if m + 1 ≤ N then 2 ^ (N - (m + 1)) else 0) =
      3 ^ N - 1 := by
  have h3 : 3 ^ N = ∑ m ∈ range (N + 1), N.choose m * 2 ^ (N - m) := by
    rw [show (3 : ℕ) = 1 + 2 by rfl, add_pow]
    exact sum_congr rfl fun m _ => by simp [mul_comm]
  have hterm : ∀ m ∈ range N, 2 * (N.choose m * (if m + 1 ≤ N then 2 ^ (N - (m + 1)) else 0)) =
      N.choose m * 2 ^ (N - m) := by
    intro m hm
    have hm' : m + 1 ≤ N := by simp at hm; omega
    rw [if_pos hm', show N - m = N - (m + 1) + 1 by omega, pow_succ]
    ring
  rw [h3, sum_range_succ, sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, mul_one,
    if_neg (show ¬ N + 1 ≤ N by omega), mul_zero, add_zero, mul_sum, sum_congr rfl hterm]
  omega

/-- The pairs carrying the block obstruction: `T ⊇ {0, …, |S|}` or `S ⊇ {0, …, |T|}`. -/
def blockPairs (n : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((range (n - 1)).powerset ×ˢ (range (n - 1)).powerset).filter
    (fun st => range (st.1.card + 1) ⊆ st.2 ∨ range (st.2.card + 1) ⊆ st.1)

theorem card_blockPairs (n : ℕ) : (blockPairs n).card = 3 ^ (n - 1) - 1 := by
  set N := n - 1
  set P := (range N).powerset
  let bad1 := (P ×ˢ P).filter (fun st : Finset ℕ × Finset ℕ => range (st.1.card + 1) ⊆ st.2)
  let bad2 := (P ×ˢ P).filter (fun st : Finset ℕ × Finset ℕ => range (st.2.card + 1) ⊆ st.1)
  have hsplit : blockPairs n = bad1 ∪ bad2 := filter_or _ _ _
  have hd : Disjoint bad1 bad2 := by
    apply disjoint_left.mpr
    rintro ⟨S, T⟩ h1 h2
    have h1' := card_le_card (mem_filter.mp h1).2
    have h2' := card_le_card (mem_filter.mp h2).2
    simp only [card_range] at h1' h2'
    omega
  have hb2 : bad2.card = bad1.card := by
    apply card_bij (fun st _ => (st.2, st.1))
    · rintro ⟨S, T⟩ h
      simp only [bad1, bad2, mem_filter, mem_product] at h ⊢
      exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩
    · rintro ⟨_, _⟩ _ ⟨_, _⟩ _ h
      simp only [Prod.mk.injEq] at h ⊢
      exact ⟨h.2, h.1⟩
    · rintro ⟨S, T⟩ h
      refine ⟨(T, S), ?_, rfl⟩
      simp only [bad1, bad2, mem_filter, mem_product] at h ⊢
      exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩
  have hb1 : 2 * bad1.card = 3 ^ N - 1 := by
    have hcard : bad1.card = ∑ S ∈ P, (if S.card + 1 ≤ N then 2 ^ (N - (S.card + 1)) else 0) := by
      have h0 : bad1.card = ∑ S ∈ P, (P.filter (fun T => range (S.card + 1) ⊆ T)).card := by
        simp only [bad1, card_filter, sum_product]
      rw [h0]
      refine sum_congr rfl fun S _ => ?_
      split_ifs with h
      · exact card_supersets h
      · rw [card_eq_zero, filter_eq_empty_iff]
        intro T hT hsub'
        have h1 := card_le_card hsub'
        have h2 := card_le_card (mem_powerset.mp hT)
        simp only [card_range] at h1 h2
        omega
    rw [hcard]
    simp only [P]
    rw [sum_powerset_apply_card (f := fun m => if m + 1 ≤ N then 2 ^ (N - (m + 1)) else 0),
      card_range]
    simp only [smul_eq_mul]
    exact sum_choose_two_pow N
  rw [hsplit, card_union_of_disjoint hd, hb2]
  omega

/-- No pair carrying the block obstruction occurs. -/
theorem disjoint_pairs_blockPairs (n : ℕ) : Disjoint (pairs n) (blockPairs n) := by
  have hblock : ∀ S T : Finset ℕ, range (S.card + 1) ⊆ T → (S, T) ∉ pairs n := by
    intro S T h
    exact not_mem_pairs_block (i := 0) fun j hj => h (by simp; omega)
  have hinv : ∀ S T : Finset ℕ, (S, T) ∈ pairs n → (T, S) ∈ pairs n := by
    intro S T h
    obtain ⟨w, _, he⟩ := mem_image.mp h
    refine mem_image.mpr ⟨w⁻¹, mem_univ _, ?_⟩
    rw [inv_inv]
    simp only [Prod.mk.injEq] at he ⊢
    exact ⟨he.2, he.1⟩
  apply disjoint_right.mpr
  rintro ⟨S, T⟩ h hp
  rcases (mem_filter.mp h).2 with h1 | h2
  · exact hblock S T h1 hp
  · exact hblock T S h2 (hinv S T hp)

theorem pairs_subset (n : ℕ) :
    pairs n ⊆ (range (n - 1)).powerset ×ˢ (range (n - 1)).powerset := by
  intro st hst
  obtain ⟨σ, _, rfl⟩ := mem_image.mp hst
  simp only [mem_product, mem_powerset]
  exact ⟨filter_subset _ _, filter_subset _ _⟩

/-- **Upper bound on `f`.** `f(n) + 3^(n-1) - 1 ≤ 4^(n-1)`. -/
theorem f_add_three_pow_le (n : ℕ) : f n + (3 ^ (n - 1) - 1) ≤ 4 ^ (n - 1) := by
  have hb : blockPairs n ⊆ (range (n - 1)).powerset ×ˢ (range (n - 1)).powerset :=
    filter_subset _ _
  have hU := card_le_card (union_subset (pairs_subset n) hb)
  rw [card_union_of_disjoint (disjoint_pairs_blockPairs n), card_product, card_powerset,
    card_range, card_blockPairs] at hU
  have h4 : 2 ^ (n - 1) * 2 ^ (n - 1) = 4 ^ (n - 1) := by rw [← mul_pow]; norm_num
  change (pairs n).card + (3 ^ (n - 1) - 1) ≤ 4 ^ (n - 1)
  omega

/-- **Remark 3.4, sharpened.** `1 - f(n)/4^(n-1) ≥ (3^(n-1) - 1)/4^(n-1)`. -/
theorem density_gap_lower_three (n : ℕ) :
    ((3 : ℝ) ^ (n - 1) - 1) / 4 ^ (n - 1) ≤ 1 - (f n : ℝ) / 4 ^ (n - 1) := by
  have h := f_add_three_pow_le n
  have h1 : 1 ≤ 3 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
  have hc : ((f n : ℕ) : ℝ) + ((3 : ℝ) ^ (n - 1) - 1) ≤ (4 : ℝ) ^ (n - 1) := by
    have := (Nat.cast_le (α := ℝ)).mpr h
    push_cast [Nat.cast_sub h1] at this
    linarith
  have hpos : (0 : ℝ) < 4 ^ (n - 1) := by positivity
  rw [div_le_iff₀ hpos, sub_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
  linarith

end Stanley
