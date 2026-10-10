import LeanProofs.PowTwoTrees.Reductions

/-!
# Universal label sets

A finite set `S` containing `0` is *universal* if every tree with `|S|` vertices fits `S` with root `0`.
The question asks whether every interval `{0, …, n - 1}` is universal.

* `tail`: if `S` is universal with at least two elements and `p` is its least positive element, then `p`
  is a power of two and `{s - p : s ∈ S, s > 0}` is universal.
* `primitive_tail`: if moreover `S` has an odd element and at least three elements, the tail has an odd
  element and some element of the tail is at least `p`.
* `span_bound`: a universal set with an odd element and `n ≥ 2` elements lies in `[0, 2^(n-2)]`.
-/

namespace PowTwoTrees

open Finset

/-- Every tree with `|S|` vertices fits `S` with root `0`. -/
def Universal (S : Finset ℕ) : Prop := 0 ∈ S ∧ ∀ t : BT, t.size = S.card → Fits t S 0

/-- A path with `n + 1` vertices. -/
def path (n : ℕ) : BT := BT.pre n .leaf

lemma size_path (n : ℕ) : (path n).size = n + 1 := by
  simp [path, BT.size_pre, BT.size]; omega

/-- Inverting a labelling of a tree with a unary root labelled `0`. -/
lemma fits_one_inv {t : BT} {S : Finset ℕ} (h : Fits (.one t) S 0) :
    ∃ k, 0 ∉ S.erase 0 ∧ Fits t (S.erase 0) (2 ^ k) := by
  cases h with
  | one k hc hr =>
    refine ⟨k, by simp, ?_⟩
    rw [Finset.erase_insert hr]
    simpa using hc

/-- The tail lemma. -/
theorem tail {S : Finset ℕ} (hS : Universal S) (h2 : 2 ≤ S.card) :
    ∃ p k, p = 2 ^ k ∧ p ∈ S ∧ (∀ x ∈ S, x ≠ 0 → p ≤ x) ∧
      Universal ((S.erase 0).image (· - p)) := by
  obtain ⟨h0, hU⟩ := hS
  have hcard : (S.erase 0).card = S.card - 1 := Finset.card_erase_of_mem h0
  -- the path tree fixes p
  obtain ⟨k, -, hk⟩ := fits_one_inv (hU (.one (path (S.card - 2))) (by
    simp [BT.size, size_path]; omega))
  obtain ⟨hk1, hk2, -⟩ := hk.basic
  refine ⟨2 ^ k, k, rfl, Finset.mem_of_mem_erase hk1, ?_, ?_⟩
  · intro x hx hx0
    exact hk2 x (Finset.mem_erase.mpr ⟨hx0, hx⟩)
  · refine ⟨Finset.mem_image.mpr ⟨2 ^ k, hk1, by simp⟩, ?_⟩
    intro t ht
    have hinj : Set.InjOn (· - 2 ^ k) (S.erase 0 : Set ℕ) := by
      intro x hx y hy hxy
      have := hk2 x hx; have := hk2 y hy
      simp only at hxy; omega
    rw [Finset.card_image_of_injOn hinj, hcard] at ht
    obtain ⟨k', -, hk'⟩ := fits_one_inv (hU (.one t) (by simp [BT.size]; omega))
    obtain ⟨h1, h2', -⟩ := hk'.basic
    -- both 2^k and 2^k' are the least element of S \ {0}
    have e : 2 ^ k' = 2 ^ k := le_antisymm (h2' _ hk1) (hk2 _ h1)
    rw [e] at hk'
    simpa using hk'.unshift (2 ^ k) hk2

/-- A universal set with at least three elements contains two different positive powers of two. -/
lemma two_powers {S : Finset ℕ} (hS : Universal S) (h3 : 3 ≤ S.card) :
    ∃ i j, i ≠ j ∧ 2 ^ i ∈ S ∧ 2 ^ j ∈ S := by
  obtain ⟨_, hU⟩ := hS
  have h := hU (.two .leaf (path (S.card - 3))) (by simp [BT.size, size_path]; omega)
  cases h with
  | two i j ha hb hd hrA hrB =>
    obtain ⟨a1, -, -⟩ := ha.basic
    obtain ⟨b1, -, -⟩ := hb.basic
    refine ⟨i, j, ?_, ?_, ?_⟩
    · rintro rfl
      exact Finset.disjoint_left.mp hd (by simpa using a1) (by simpa using b1)
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (by simpa using a1))
    · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (by simpa using b1))

/-- The primitive-tail lemma. -/
theorem primitive_tail {S : Finset ℕ} (hS : Universal S) (h3 : 3 ≤ S.card) (hodd : ∃ x ∈ S, Odd x) :
    ∃ p k, p = 2 ^ k ∧ p ∈ S ∧ (∀ x ∈ S, x ≠ 0 → p ≤ x) ∧
      Universal ((S.erase 0).image (· - p)) ∧
      (∃ y ∈ (S.erase 0).image (· - p), Odd y) ∧ (∃ y ∈ (S.erase 0).image (· - p), p ≤ y) := by
  obtain ⟨p, k, rfl, hp, hmin, hT⟩ := tail hS (by omega)
  obtain ⟨i, j, hij, hi, hj⟩ := two_powers hS h3
  -- a power of two in S other than 2^k
  obtain ⟨q, hq, hqS⟩ : ∃ q, q ≠ k ∧ 2 ^ q ∈ S := by
    by_cases h : i = k
    · exact ⟨j, by omega, hj⟩
    · exact ⟨i, h, hi⟩
  have hkq : k < q := by
    rcases Nat.lt_or_gt_of_ne hq with h | h
    · have := hmin _ hqS (by positivity)
      have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) h
      omega
    · exact h
  have hq2 : 2 ^ (k + 1) ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hkq
  have hqmem : 2 ^ q - 2 ^ k ∈ (S.erase 0).image (· - 2 ^ k) :=
    Finset.mem_image.mpr ⟨2 ^ q, Finset.mem_erase.mpr ⟨by positivity, hqS⟩, rfl⟩
  refine ⟨2 ^ k, k, rfl, hp, hmin, hT, ?_, ⟨_, hqmem, by rw [pow_succ] at hq2; omega⟩⟩
  -- the tail has an odd element
  by_contra hall
  push_neg at hall
  obtain ⟨x, hxS, hxodd⟩ := hodd
  have hx0 : x ≠ 0 := by rintro rfl; simp at hxodd
  have hxk := hmin x hxS hx0
  have hev : Even (x - 2 ^ k) :=
    Nat.not_odd_iff_even.mp (hall _ (Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hx0, hxS⟩, rfl⟩))
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- p = 1: then 2^q - 1 is even, so 2^q is odd, impossible for q ≥ 1
    subst hk
    have hev2 : Even (2 ^ q - 2 ^ 0) :=
      Nat.not_odd_iff_even.mp (hall _ hqmem)
    have : Even (2 ^ q) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    have h1 : 1 ≤ 2 ^ q := Nat.one_le_two_pow
    rw [pow_zero] at hev2
    obtain ⟨m, hm⟩ := hev2
    obtain ⟨m', hm'⟩ := this
    omega
  · -- p even: then x = p + (x - p) is even
    have : Even (2 ^ k) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have hxe : Even x := by
      have := this.add hev
      rwa [Nat.add_sub_cancel' hxk] at this
    exact (Nat.not_even_iff_odd.mpr hxodd) hxe

/-- The span bound: a universal set with an odd element and `n ≥ 2` elements lies in `[0, 2^(n-2)]`. -/
theorem span_bound : ∀ (n : ℕ) (S : Finset ℕ), S.card = n + 2 → Universal S → (∃ x ∈ S, Odd x) →
    ∀ x ∈ S, x ≤ 2 ^ n := by
  intro n
  induction n with
  | zero =>
    intro S hcard hS hodd x hx
    obtain ⟨p, k, rfl, hp, hmin, -⟩ := tail hS (by omega)
    -- S = {0, 2^k}, and it has an odd element, so 2^k = 1
    have hS2 : S = {0, 2 ^ k} := by
      have h0 := hS.1
      have hne : (0 : ℕ) ≠ 2 ^ k := by positivity
      symm
      apply Finset.eq_of_subset_of_card_le
      · intro y hy; simp at hy; rcases hy with rfl | rfl <;> assumption
      · rw [hcard, Finset.card_pair hne]
    obtain ⟨y, hy, hyodd⟩ := hodd
    rw [hS2] at hy hx
    simp at hy hx
    rcases hy with rfl | rfl
    · simp at hyodd
    · rcases hx with rfl | rfl
      · simp
      · rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk; simp
        · exact absurd hyodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, by omega⟩))
  | succ n ih =>
    intro S hcard hS hodd x hx
    obtain ⟨p, k, rfl, hp, hmin, hT, hTodd, ⟨y0, hy0, hpy0⟩⟩ := primitive_tail hS (by omega) hodd
    have hcardT : ((S.erase 0).image (· - 2 ^ k)).card = n + 2 := by
      have hinj : Set.InjOn (· - 2 ^ k) (S.erase 0 : Set ℕ) := by
        intro a ha b hb hab
        have := hmin a (Finset.mem_of_mem_erase ha) (Finset.ne_of_mem_erase ha)
        have := hmin b (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)
        simp only at hab; omega
      rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hS.1, hcard]; rfl
    have hbound := ih _ hcardT hT hTodd
    by_cases hx0 : x = 0
    · subst hx0; positivity
    · have hxk := hmin x hx hx0
      have h1 := hbound (x - 2 ^ k) (Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hx0, hx⟩, rfl⟩)
      have h2 := hbound y0 hy0
      rw [pow_succ]
      omega

end PowTwoTrees
