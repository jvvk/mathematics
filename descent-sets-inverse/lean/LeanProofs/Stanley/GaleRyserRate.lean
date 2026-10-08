/- Theorem 3.6: the Gale–Ryser obstruction has rate exactly log(4/3).

Let `P_n` be the proportion of pairs `(S, T)` of subsets of `[n-1]` violating the cross-dominance
inequalities (3.2), in the subset form `RunDominance` of `DominanceNecessity.lean`. Then

  (3^(n-1) - 1) / 4^(n-1) ≤ P_n ≤ (4n³ + 2^(m-1) C(n,m)²) (3/4)^(n-1) + 4 n^m / 2^n,

with `m = ⌈2 log₂ n⌉ + 1 = clog₂(n²) + 1`.

The paper's probabilities become counts. Both union bounds of the paper ("choose the long parts",
"choose the `m` largest parts") are one lemma, `card_bigBlocks`: a family of `j` position blocks
of a cut set `A` is recorded by its `j` first and `j` last positions, and these two sets alone
determine the interior positions of the family (`mem_interior_iff`), which `A` must avoid. -/
import LeanProofs.Stanley.DominanceNecessity
import LeanProofs.Stanley.BlockObstruction
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Stanley.Alt
open Finset

/-! ### Blocks of a cut set -/

theorem block_zero (A : Finset ℕ) : block A 0 = 0 := by simp [block]

theorem block_succ (A : Finset ℕ) (i : ℕ) :
    block A (i + 1) = block A i + if i ∈ A then 1 else 0 := by
  unfold block
  split_ifs with hi
  · rw [show A.filter (· < i + 1) = insert i (A.filter (· < i)) by
      ext r; simp only [mem_filter, mem_insert]; constructor
      · rintro ⟨hr, hlt⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | h
        · exact Or.inr ⟨hr, h⟩
        · exact Or.inl h
      · rintro (rfl | ⟨hr, hlt⟩)
        · exact ⟨hi, by omega⟩
        · exact ⟨hr, by omega⟩]
    rw [card_insert_of_notMem (by simp)]
  · rw [add_zero]; congr 1; ext r; simp only [mem_filter]; constructor
    · rintro ⟨hr, hlt⟩
      refine ⟨hr, ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h | rfl
      · exact h
      · exact absurd hr hi
    · rintro ⟨hr, hlt⟩; exact ⟨hr, by omega⟩

/-- `block X (i+1)` counts the elements of `X` up to `i`. -/
theorem block_succ_eq_card (X : Finset ℕ) (i : ℕ) :
    block X (i + 1) = (X.filter (· ≤ i)).card := by
  unfold block; congr 1; ext r; simp only [mem_filter, Nat.lt_succ_iff]

/-- The length of block `b` of the cut set `A`, on positions `0, …, n-1`. -/
def blen (n : ℕ) (A : Finset ℕ) (b : ℕ) : ℕ := ((range n).filter (fun i => block A i = b)).card

theorem sum_blen (n : ℕ) (A R : Finset ℕ) :
    ∑ b ∈ R, blen n A b = ((range n).filter (fun i => block A i ∈ R)).card := by
  rw [card_eq_sum_card_fiberwise (s := (range n).filter (fun i => block A i ∈ R)) (t := R)
    (f := block A) (fun i hi => (mem_filter.mp hi).2)]
  refine sum_congr rfl fun b hb => ?_
  unfold blen; congr 1; ext i; simp only [mem_filter]
  constructor
  · rintro ⟨hi, h⟩; exact ⟨⟨hi, h ▸ hb⟩, h⟩
  · rintro ⟨⟨hi, _⟩, h⟩; exact ⟨hi, h⟩

theorem blen_eq_zero_of_lt {n : ℕ} (A : Finset ℕ) {b : ℕ} (hb : n ≤ b) : blen n A b = 0 := by
  unfold blen
  rw [card_eq_zero, filter_eq_empty_iff]
  intro i hi h
  have := block_le A i
  simp at hi
  omega

theorem sum_range_blen (n : ℕ) (A : Finset ℕ) : ∑ b ∈ range (n + 1), blen n A b = n := by
  rw [sum_blen, filter_true_of_mem, card_range]
  intro i hi
  have := block_le A i
  simp at hi ⊢
  omega

theorem blen_le (n : ℕ) (A : Finset ℕ) (b : ℕ) : blen n A b ≤ n := by
  unfold blen
  exact (card_filter_le _ _).trans (card_range n).le

/-! ### First and last positions of a family of blocks -/

/-- First positions of the blocks with labels in `R`. -/
def firsts (n : ℕ) (A R : Finset ℕ) : Finset ℕ :=
  (range n).filter (fun i => block A i ∈ R ∧ (i = 0 ∨ i - 1 ∈ A))

/-- Last positions of the blocks with labels in `R`. -/
def lasts (n : ℕ) (A R : Finset ℕ) : Finset ℕ :=
  (range n).filter (fun i => block A i ∈ R ∧ (i + 1 = n ∨ i ∈ A))

/-- Positions up to `i` that are first, minus those before `i` that are last: one exactly when
position `i` lies in a chosen block. -/
theorem firsts_count (n : ℕ) (A R : Finset ℕ) :
    ∀ i, i < n → block (firsts n A R) (i + 1) =
      block (lasts n A R) i + if block A i ∈ R then 1 else 0 := by
  intro i
  induction i with
  | zero =>
    intro hn
    rw [block_succ, block_zero, block_zero, block_zero]
    simp [firsts, hn, block_zero]
  | succ i ih =>
    intro hn
    have h := ih (by omega)
    have hP : i + 1 ∈ firsts n A R ↔ block A (i + 1) ∈ R ∧ i ∈ A := by
      simp only [firsts, mem_filter, mem_range, Nat.add_sub_cancel]
      constructor
      · rintro ⟨_, hb, h0 | h1⟩
        · omega
        · exact ⟨hb, h1⟩
      · rintro ⟨hb, hA⟩; exact ⟨hn, hb, Or.inr hA⟩
    have hQ : i ∈ lasts n A R ↔ block A i ∈ R ∧ i ∈ A := by
      simp only [lasts, mem_filter, mem_range]
      constructor
      · rintro ⟨_, hb, h0 | h1⟩
        · omega
        · exact ⟨hb, h1⟩
      · rintro ⟨hb, hA⟩; exact ⟨by omega, hb, Or.inr hA⟩
    rw [block_succ (firsts n A R) (i + 1), h, block_succ (lasts n A R) i]
    have hs := block_succ A i
    by_cases hA : i ∈ A
    · rw [ite_eq_left hA] at hs
      simp only [hP, hQ, hA, and_true, hs]
    · rw [ite_eq_right hA, add_zero] at hs
      simp only [hP, hQ, hA, and_false, ite_false, hs, add_zero]

/-- Interior positions of the family with first positions `P` and last positions `Q`:
more firsts than lasts up to `i`. Depends on `P` and `Q` only. -/
def interior (P Q : Finset ℕ) (N : ℕ) : Finset ℕ :=
  (range N).filter (fun i => block Q (i + 1) < block P (i + 1))

theorem mem_interior_iff {n : ℕ} (A R : Finset ℕ) {i : ℕ} (hi : i + 1 < n) :
    i ∈ interior (firsts n A R) (lasts n A R) (n - 1) ↔ block A i ∈ R ∧ i ∉ A := by
  have h := firsts_count n A R i (by omega)
  have hq := block_succ (lasts n A R) i
  simp only [interior, mem_filter, mem_range, show i < n - 1 by omega, true_and]
  rw [h, hq]
  simp only [lasts, mem_filter, mem_range, show i < n by omega, true_and,
    show i + 1 ≠ n by omega, false_or]
  by_cases hb : block A i ∈ R <;> by_cases hA : i ∈ A <;> simp [hb, hA]

theorem card_lasts {n : ℕ} (A R : Finset ℕ) (hR : ∀ b ∈ R, ∃ i < n, block A i = b) :
    (lasts n A R).card = R.card := by
  apply card_nbij (fun i => block A i)
  · intro i hi; exact (mem_filter.mp hi).2.1
  · intro i hi j hj hij
    simp only [lasts, coe_filter, Set.mem_ofPred_eq, mem_range] at hi hj
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hiA : i ∈ A := hi.2.2.resolve_left (by omega)
      have := block_monotone A (show i + 1 ≤ j by omega)
      rw [block_succ, ite_eq_left hiA] at this
      simp only at hij; omega
    · have hjA : j ∈ A := hj.2.2.resolve_left (by omega)
      have := block_monotone A (show j + 1 ≤ i by omega)
      rw [block_succ, ite_eq_left hjA] at this
      simp only at hij; omega
  · intro b hb
    obtain ⟨i, hi, hib⟩ := hR b hb
    set F := (range n).filter (fun i => block A i = b)
    have hF : F.Nonempty := ⟨i, by simp [F, hi, hib]⟩
    set i0 := F.max' hF
    have hi0 : i0 ∈ F := max'_mem F hF
    simp only [F, mem_filter, mem_range] at hi0
    refine ⟨i0, ?_, hi0.2⟩
    simp only [lasts, coe_filter, Set.mem_ofPred_eq, mem_range]
    refine ⟨hi0.1, hi0.2 ▸ hb, ?_⟩
    by_cases hlast : i0 + 1 = n
    · exact Or.inl hlast
    · right
      by_contra hA
      have hs := block_succ A i0
      rw [ite_eq_right hA, add_zero] at hs
      have hmem : i0 + 1 ∈ F := by simp [F]; omega
      have := le_max' F (i0 + 1) hmem
      omega

theorem card_firsts {n : ℕ} (hn : 1 ≤ n) (A R : Finset ℕ) :
    (firsts n A R).card = (lasts n A R).card := by
  have h := firsts_count n A R (n - 1) (by omega)
  have hP : block (firsts n A R) (n - 1 + 1) = (firsts n A R).card := by
    unfold block; congr 1; apply filter_true_of_mem
    intro i hi; simp [firsts] at hi; omega
  have hQ := block_succ (lasts n A R) (n - 1)
  have hQ' : block (lasts n A R) (n - 1 + 1) = (lasts n A R).card := by
    unfold block; congr 1; apply filter_true_of_mem
    intro i hi; simp [lasts] at hi; omega
  have hmem : (n - 1 ∈ lasts n A R) ↔ block A (n - 1) ∈ R := by
    simp only [lasts, mem_filter, mem_range]
    constructor
    · rintro ⟨_, hb, _⟩; exact hb
    · intro hb; exact ⟨by omega, hb, Or.inl (by omega)⟩
  rw [hP] at h
  rw [hQ'] at hQ
  by_cases hb : block A (n - 1) ∈ R
  · have hm := hmem.mpr hb
    simp only [hb, hm, ite_true] at h hQ
    omega
  · have hm : n - 1 ∉ lasts n A R := fun h' => hb (hmem.mp h')
    simp only [hb, hm, ite_false] at h hQ
    omega

theorem card_interior {n : ℕ} (hn : 1 ≤ n) (A R : Finset ℕ) :
    (interior (firsts n A R) (lasts n A R) (n - 1)).card + (lasts n A R).card =
      ((range n).filter (fun i => block A i ∈ R)).card := by
  have hsplit : (range n).filter (fun i => block A i ∈ R) =
      interior (firsts n A R) (lasts n A R) (n - 1) ∪ lasts n A R := by
    ext i
    simp only [mem_filter, mem_range, mem_union]
    constructor
    · rintro ⟨hi, hb⟩
      by_cases hl : i + 1 < n
      · by_cases hA : i ∈ A
        · right; simp [lasts, hi, hb, hA]
        · left; exact (mem_interior_iff A R hl).mpr ⟨hb, hA⟩
      · right; simp only [lasts, mem_filter, mem_range]; exact ⟨hi, hb, Or.inl (by omega)⟩
    · rintro (h | h)
      · have hi : i < n - 1 := by simp [interior] at h; exact h.1
        exact ⟨by omega, ((mem_interior_iff A R (by omega)).mp h).1⟩
      · simp only [lasts, mem_filter, mem_range] at h; exact ⟨h.1, h.2.1⟩
  have hdisj : Disjoint (interior (firsts n A R) (lasts n A R) (n - 1)) (lasts n A R) := by
    rw [disjoint_left]
    intro i h1 h2
    have hi : i < n - 1 := by simp [interior] at h1; exact h1.1
    have := (mem_interior_iff A R (by omega)).mp h1
    simp only [lasts, mem_filter, mem_range] at h2
    rcases h2.2.2 with h | h
    · omega
    · exact this.2 h
  rw [hsplit, card_union_of_disjoint hdisj]

/-! ### The union bound over families of blocks -/

open scoped Classical in
/-- Cut sets having `j` nonempty blocks covering at least `y + j` positions. -/
noncomputable def bigBlocks (n j y : ℕ) : Finset (Finset ℕ) :=
  (range (n - 1)).powerset.filter (fun A => ∃ R : Finset ℕ, R.card = j ∧
    (∀ b ∈ R, ∃ i < n, block A i = b) ∧ y + j ≤ ((range n).filter (fun i => block A i ∈ R)).card)

theorem bigBlocks_subset (n j y : ℕ) : bigBlocks n j y ⊆ (range (n - 1)).powerset := by
  intro A hA; simp only [bigBlocks, mem_filter] at hA; exact hA.1

/-- **The union bound.** `#bigBlocks · 2^y ≤ C(n,j)² 2^(n-1)`. -/
theorem card_bigBlocks (n j y : ℕ) :
    (bigBlocks n j y).card * 2 ^ y ≤ (n.choose j) ^ 2 * 2 ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have key : ∀ A ∈ bigBlocks 0 j y, j = 0 ∧ y = 0 := by
      intro A hA
      simp only [bigBlocks, mem_filter] at hA
      obtain ⟨-, R, hRc, hRb, hy⟩ := hA
      have hR : R = ∅ := eq_empty_of_forall_notMem fun b hb => by
        obtain ⟨i, hi, -⟩ := hRb b hb; omega
      subst hR
      simp at hRc hy
      omega
    by_cases h0 : j = 0 ∧ y = 0
    · obtain ⟨rfl, rfl⟩ := h0
      simp only [pow_zero, mul_one, Nat.choose_self, one_pow, Nat.zero_sub]
      calc (bigBlocks 0 0 0).card ≤ ((range (0 - 1)).powerset).card := card_le_card (bigBlocks_subset 0 0 0)
        _ = 1 := by simp
    · rw [card_eq_zero.mpr (eq_empty_of_forall_notMem fun A hA => h0 (key A hA))]; simp
  let PQ := (range n).powersetCard j ×ˢ (range n).powersetCard j
  let piece : Finset ℕ × Finset ℕ → Finset (Finset ℕ) := fun pq =>
    (range (n - 1)).powerset.filter (fun A => Disjoint A (interior pq.1 pq.2 (n - 1)) ∧
      y ≤ (interior pq.1 pq.2 (n - 1)).card)
  have hsub : bigBlocks n j y ⊆ PQ.biUnion piece := by
    intro A hA
    simp only [bigBlocks, mem_filter] at hA
    obtain ⟨hAN, R, hRc, hRb, hy⟩ := hA
    have hl := card_lasts A R hRb
    have hf := card_firsts hn A R
    have hi := card_interior hn A R
    rw [mem_biUnion]
    refine ⟨(firsts n A R, lasts n A R), ?_, ?_⟩
    · simp only [PQ, mem_product, mem_powersetCard]
      exact ⟨⟨filter_subset _ _, by omega⟩, ⟨filter_subset _ _, by omega⟩⟩
    · simp only [piece, mem_filter]
      refine ⟨hAN, ?_, by omega⟩
      rw [disjoint_left]
      intro i hiA hiX
      have hlt : i < (n - 1) := by simp [interior] at hiX; exact hiX.1
      exact ((mem_interior_iff A R (by omega)).mp hiX).2 hiA
  have hpiece : ∀ pq ∈ PQ, (piece pq).card * 2 ^ y ≤ 2 ^ (n - 1) := by
    intro pq _
    set X := interior pq.1 pq.2 (n - 1)
    by_cases hy : y ≤ X.card
    · have hXN : X ⊆ range (n - 1) := filter_subset _ _
      have hsub' : piece pq ⊆ (range (n - 1) \ X).powerset := by
        intro A hA
        simp only [piece, mem_filter, mem_powerset] at hA ⊢
        exact subset_sdiff.mpr ⟨hA.1, hA.2.1⟩
      have hc := card_le_card hsub'
      rw [card_powerset, card_sdiff_of_subset hXN, card_range] at hc
      calc (piece pq).card * 2 ^ y ≤ 2 ^ ((n - 1) - X.card) * 2 ^ X.card :=
            Nat.mul_le_mul hc (Nat.pow_le_pow_right (by norm_num) hy)
        _ = 2 ^ (n - 1) := by
          rw [← pow_add]; congr 1
          have := card_le_card hXN; rw [card_range] at this; omega
    · rw [card_eq_zero.mpr (filter_eq_empty_iff.mpr fun A _ h => hy h.2)]; simp
  calc (bigBlocks n j y).card * 2 ^ y ≤ (PQ.biUnion piece).card * 2 ^ y :=
        Nat.mul_le_mul_right _ (card_le_card hsub)
    _ ≤ (∑ pq ∈ PQ, (piece pq).card) * 2 ^ y := Nat.mul_le_mul_right _ card_biUnion_le
    _ = ∑ pq ∈ PQ, (piece pq).card * 2 ^ y := sum_mul _ _ _
    _ ≤ ∑ pq ∈ PQ, 2 ^ (n - 1) := sum_le_sum hpiece
    _ = (n.choose j) ^ 2 * 2 ^ (n - 1) := by
      rw [sum_const, card_product, card_powersetCard, card_range, smul_eq_mul, sq]

/-! ### From `RunDominance` to block lengths -/

theorem fib_blk (n : ℕ) (A : Finset ℕ) (j : Fin (n + 1)) : fib (blk n A) j = blen n A j := by
  unfold fib blen
  refine card_bij (fun (p : Fin n) _ => p.val) ?_ ?_ ?_
  · intro p hp
    simp only [mem_filter, mem_univ, true_and] at hp
    simp only [mem_filter, mem_range, p.is_lt, true_and, ← blk_val, hp]
  · intro p _ q _ h; exact Fin.ext h
  · intro i hi
    simp only [mem_filter, mem_range] at hi
    refine ⟨⟨i, hi.1⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    exact Fin.ext (by rw [blk_val]; exact hi.2)

/-- Failure of the subset-form inequality, in terms of block lengths. -/
theorem not_runDominance_iff (n : ℕ) (A B : Finset ℕ) :
    ¬ RunDominance n A B ↔ ∃ R : Finset ℕ, R ⊆ range (n + 1) ∧
      ∑ j ∈ range (n + 1), min R.card (blen n B j) < ∑ b ∈ R, blen n A b := by
  have hR : ∀ R : Finset (Fin (n + 1)),
      (∑ i ∈ R, fib (blk n A) i = ∑ b ∈ R.map Fin.valEmbedding, blen n A b) ∧
      (∑ j : Fin (n + 1), min R.card (fib (blk n B) j) =
        ∑ j ∈ range (n + 1), min (R.map Fin.valEmbedding).card (blen n B j)) := by
    intro R
    refine ⟨by rw [sum_map]; exact sum_congr rfl fun i _ => fib_blk n A i, ?_⟩
    rw [card_map]
    simp_rw [fib_blk]
    exact Fin.sum_univ_eq_sum_range (fun j => min R.card (blen n B j)) (n + 1)
  unfold RunDominance
  constructor
  · intro h
    push Not at h
    obtain ⟨R, hlt⟩ := h
    refine ⟨R.map Fin.valEmbedding, ?_, ?_⟩
    · intro b hb
      obtain ⟨j, _, rfl⟩ := mem_map.mp hb
      simp only [Fin.valEmbedding_apply, mem_range]; exact j.is_lt
    · rw [← (hR R).1, ← (hR R).2]; exact hlt
  · rintro ⟨R, hRs, hlt⟩ h
    let R' : Finset (Fin (n + 1)) := univ.filter (fun j => (j : ℕ) ∈ R)
    have hmap : R'.map Fin.valEmbedding = R := by
      ext b
      simp only [R', mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply]
      constructor
      · rintro ⟨j, hj, rfl⟩; exact hj
      · intro hb
        exact ⟨⟨b, by simpa using hRs hb⟩, hb, rfl⟩
    have := h R'
    rw [(hR R').1, (hR R').2, hmap] at this
    omega

/-- A cut set inside `[n-1]` has at least `|A| + 1` nonempty blocks. -/
theorem card_nonempty_blocks {n : ℕ} (hn : 1 ≤ n) {A : Finset ℕ} (hA : A ⊆ range (n - 1)) :
    A.card + 1 ≤ ((range (n + 1)).filter (fun j => 0 < blen n A j)).card := by
  have hnA : n - 1 ∉ A := fun h => by simpa using hA h
  rw [← card_insert_of_notMem hnA]
  apply card_le_card_of_injOn (block A)
  · intro i hi
    have hin : i < n := by
      rcases mem_insert.mp hi with rfl | h
      · omega
      · have := hA h; simp at this; omega
    have := block_le A i
    simp only [coe_filter, Set.mem_ofPred_eq, mem_range]
    refine ⟨by omega, card_pos.mpr ⟨i, by simp [hin]⟩⟩
  · intro i hi j hj hij
    have hlt : ∀ a b, a ∈ insert (n - 1) A → b ∈ insert (n - 1) A → a < b →
        block A a ≠ block A b := by
      intro a b ha hb hab
      have hbn : b ≤ n - 1 := by
        rcases mem_insert.mp hb with rfl | h
        · exact le_rfl
        · have := hA h; simp at this; omega
      have haA : a ∈ A := by
        rcases mem_insert.mp ha with rfl | h
        · omega
        · exact h
      have h1 := block_monotone A (show a + 1 ≤ b by omega)
      rw [block_succ, ite_eq_left haA] at h1
      omega
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hlt i j hi hj h hij
    · exact hlt j i hj hi h hij.symm

/-- `E_k(δ) = ∑ (δ_j - k)₊`, the excess of the blocks of `B` over `k`. -/
def excess (n : ℕ) (B : Finset ℕ) (k : ℕ) : ℕ := ∑ j ∈ range (n + 1), (blen n B j - k)

/-- **The two regimes.** A failure is one of: few runs; `m` runs covering more than `|B| + 1`
positions; or a failure at `k > m`, with `|A| + 2 ≤ k + E_k(B)`. -/
theorem fail_cases {n m : ℕ} {A B R : Finset ℕ} (hA : A ⊆ range (n - 1))
    (hR : R ⊆ range (n + 1))
    (hfail : ∑ j ∈ range (n + 1), min R.card (blen n B j) < ∑ b ∈ R, blen n A b)
    (hB1 : B.card + 1 ≤ ((range (n + 1)).filter (fun j => 0 < blen n B j)).card) :
    A.card + 2 ≤ m ∨ A ∈ bigBlocks n m (B.card + 2 - m) ∨
      ∃ k ∈ Ioo m n, ∃ e ∈ Icc 1 n, A.card + 2 ≤ k + e ∧ e ≤ excess n B k := by
  set k := R.card
  set x := ∑ b ∈ R, blen n A b
  set s := ∑ j ∈ range (n + 1), min k (blen n B j)
  have hxn : x ≤ n :=
    (sum_le_sum_of_subset hR).trans (sum_range_blen n A).le
  have hse : s + excess n B k = n := by
    calc s + excess n B k = ∑ j ∈ range (n + 1), blen n B j := by
          rw [excess, ← sum_add_distrib]
          exact sum_congr rfl fun j _ => by omega
      _ = n := sum_range_blen n B
  have hn : 1 ≤ n := by omega
  have hNE := card_nonempty_blocks hn hA
  set NE := (range (n + 1)).filter (fun j => 0 < blen n A j)
  have hk : 1 ≤ k := by
    by_contra h0
    have : R = ∅ := card_eq_zero.mp (by omega)
    simp [x, this] at hfail
  by_cases hsmall : A.card + 2 ≤ m
  · exact Or.inl hsmall
  right
  by_cases hkm : k ≤ m
  · left
    -- `s ≥ #(nonempty blocks of B) ≥ |B| + 1`
    have hs : ((range (n + 1)).filter (fun j => 0 < blen n B j)).card ≤ s := by
      rw [card_eq_sum_ones]
      calc ∑ j ∈ (range (n + 1)).filter (fun j => 0 < blen n B j), 1
          ≤ ∑ j ∈ (range (n + 1)).filter (fun j => 0 < blen n B j), min k (blen n B j) := by
            apply sum_le_sum; intro j hj; have := (mem_filter.mp hj).2; omega
        _ ≤ s := sum_le_sum_of_subset (filter_subset _ _)
    set R' := R.filter (fun b => 0 < blen n A b)
    have hR'x : ∑ b ∈ R', blen n A b = x := by
      apply sum_filter_of_ne; intro b _ h; omega
    have hR'NE : R' ⊆ NE := by
      intro b hb
      simp only [R', mem_filter] at hb
      simp only [NE, mem_filter]; exact ⟨hR hb.1, hb.2⟩
    have hR'c : R'.card ≤ m := (card_filter_le _ _).trans hkm
    obtain ⟨R'', h1, h2, h3⟩ := exists_subsuperset_card_eq hR'NE hR'c (by omega)
    simp only [bigBlocks, mem_filter, mem_powerset]
    refine ⟨hA, R'', h3, ?_, ?_⟩
    · intro b hb
      have hpos := (mem_filter.mp (h2 hb)).2
      obtain ⟨i, hi⟩ := card_pos.mp hpos
      simp only [mem_filter, mem_range] at hi
      exact ⟨i, hi.1, hi.2⟩
    · rw [← sum_blen]
      have hge : ∑ b ∈ R', blen n A b ≤ ∑ b ∈ R'', blen n A b :=
        sum_le_sum_of_subset h1
      have hm : R''.card ≤ ∑ b ∈ R'', blen n A b := by
        rw [card_eq_sum_ones]; apply sum_le_sum
        intro b hb; exact (mem_filter.mp (h2 hb)).2
      omega
  · right
    push Not at hkm
    -- the runs outside `R` hold at least `|A| + 1 - k` positions
    have hout : x + (NE \ R).card ≤ n := by
      have h1 : (NE \ R).card ≤ ∑ b ∈ NE \ R, blen n A b := by
        rw [card_eq_sum_ones]; apply sum_le_sum
        intro b hb; exact (mem_filter.mp (mem_sdiff.mp hb).1).2
      have h2 : x + ∑ b ∈ NE \ R, blen n A b ≤ n := by
        rw [← sum_union (disjoint_sdiff)]
        exact (sum_le_sum_of_subset (union_subset hR ((sdiff_subset).trans
          (filter_subset _ _)))).trans (sum_range_blen n A).le
      omega
    have hsd := le_card_sdiff R NE
    set e := excess n B k
    have he1 : 1 ≤ e := by omega
    refine ⟨k, mem_Ioo.mpr ⟨hkm, ?_⟩, e, mem_Icc.mpr ⟨he1, by omega⟩, by omega, le_rfl⟩
    by_contra hkn
    push Not at hkn
    have : e = 0 := sum_eq_zero fun j _ => by have := blen_le n B j; omega
    omega

/-! ### Counting -/

/-- Few runs: `#{A ⊆ [n-1] : |A| + 2 ≤ m} ≤ n^m`. -/
theorem card_few_cuts {n : ℕ} (hn : 1 ≤ n) (m : ℕ) :
    ((range (n - 1)).powerset.filter (fun A => A.card + 2 ≤ m)).card ≤ n ^ m := by
  set N := n - 1
  have h1 : ((range N).powerset.filter (fun A => A.card + 2 ≤ m)).card =
      ∑ t ∈ (range (N + 1)).filter (fun t => t + 2 ≤ m), N.choose t := by
    rw [card_filter, sum_powerset_apply_card (f := fun t => if t + 2 ≤ m then 1 else 0),
      card_range, sum_filter]
    simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [h1]
  calc ∑ t ∈ (range (N + 1)).filter (fun t => t + 2 ≤ m), N.choose t
      ≤ ∑ t ∈ range (m - 2 + 1), N.choose t := by
        apply sum_le_sum_of_subset
        intro t ht; simp only [mem_filter, mem_range] at ht ⊢; omega
    _ ≤ ∑ t ∈ range (m - 2 + 1), N ^ t * 1 ^ (m - 2 - t) * (m - 2).choose t := by
        apply sum_le_sum
        intro t ht
        have hc : 1 ≤ (m - 2).choose t := Nat.choose_pos (by simp at ht; omega)
        calc N.choose t ≤ N ^ t := Nat.choose_le_pow N t
          _ ≤ N ^ t * 1 ^ (m - 2 - t) * (m - 2).choose t := by
            rw [one_pow, mul_one]; exact Nat.le_mul_of_pos_right _ hc
    _ = (N + 1) ^ (m - 2) := (add_pow _ _ _).symm
    _ ≤ n ^ m := by
        rw [show N + 1 = n by omega]
        exact Nat.pow_le_pow_right hn (by omega)

theorem sum_half_pow (N : ℕ) :
    ∑ A ∈ (range N).powerset, (1 / 2 : ℝ) ^ A.card = (3 / 2) ^ N := by
  have h := sum_pow_mul_eq_add_pow (1 / 2 : ℝ) 1 (range N)
  simp only [one_pow, mul_one, card_range] at h
  rw [h]; norm_num

/-- The second regime, for one `B`. -/
theorem card_bigBlocks_real (n m b : ℕ) :
    ((bigBlocks n m (b + 2 - m)).card : ℝ) ≤
      (n.choose m : ℝ) ^ 2 * 2 ^ (n - 1) * 2 ^ m / 4 * (1 / 2) ^ b := by
  have h := card_bigBlocks n m (b + 2 - m)
  have hp : 2 ^ (b + 2) ≤ 2 ^ (b + 2 - m) * 2 ^ m := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : ((bigBlocks n m (b + 2 - m)).card : ℝ) * 2 ^ (b + 2) ≤
      (n.choose m : ℝ) ^ 2 * 2 ^ (n - 1) * 2 ^ m := by
    have h3 := Nat.mul_le_mul_left (bigBlocks n m (b + 2 - m)).card hp
    have h4 : (bigBlocks n m (b + 2 - m)).card * (2 ^ (b + 2 - m) * 2 ^ m) ≤
        n.choose m ^ 2 * 2 ^ (n - 1) * 2 ^ m := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_right _ h
    exact_mod_cast h3.trans h4
  have hpos : (0 : ℝ) < 2 ^ (b + 2) := by positivity
  rw [show (n.choose m : ℝ) ^ 2 * 2 ^ (n - 1) * 2 ^ m / 4 * (1 / 2) ^ b =
      (n.choose m : ℝ) ^ 2 * 2 ^ (n - 1) * 2 ^ m / 2 ^ (b + 2) by
    rw [pow_add, one_div_pow]; field_simp; norm_num]
  rw [le_div_iff₀ hpos]; exact h2

/-- **The tail of `E_k(δ)`.** If `4n² ≤ 2^k`, then `#{B : E_k(B) ≥ e} ≤ 4n² 2^(n-1) 2^(-k-e)`. -/
theorem card_excess_ge {n k e : ℕ} (hk : 1 ≤ k) (he : 1 ≤ e) (hkn : 4 * n ^ 2 ≤ 2 ^ k) :
    (((range (n - 1)).powerset.filter (fun B => e ≤ excess n B k)).card : ℝ) ≤
      4 * n ^ 2 * 2 ^ (n - 1) * (1 / 2) ^ (k + e) := by
  set U := (range (n - 1)).powerset
  have hsub : U.filter (fun B => e ≤ excess n B k) ⊆
      (Icc 1 (n + 1)).biUnion (fun a => bigBlocks n a (e + a * (k - 1))) := by
    intro B hB
    obtain ⟨hBU, he'⟩ := mem_filter.mp hB
    set L := (range (n + 1)).filter (fun j => k < blen n B j)
    have hexc : excess n B k = ∑ j ∈ L, (blen n B j - k) := by
      unfold excess; rw [sum_filter_of_ne]; intro j _ h; omega
    have hsumL : ∑ j ∈ L, blen n B j = excess n B k + L.card * k := by
      rw [hexc, card_eq_sum_ones, sum_mul, ← sum_add_distrib]
      refine sum_congr rfl fun j hj => ?_
      have := (mem_filter.mp hj).2; omega
    have ha1 : 1 ≤ L.card := by
      by_contra h0
      have : L = ∅ := card_eq_zero.mp (by omega)
      rw [hexc, this, sum_empty] at he'; omega
    have ha2 : L.card ≤ n + 1 := (card_filter_le _ _).trans (card_range _).le
    have hak : L.card * (k - 1) + L.card = L.card * k := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp [Nat.mul_succ]
    rw [mem_biUnion]
    refine ⟨L.card, mem_Icc.mpr ⟨ha1, ha2⟩, ?_⟩
    simp only [bigBlocks, mem_filter]
    refine ⟨hBU, L, rfl, ?_, ?_⟩
    · intro b hb
      have hpos := (mem_filter.mp hb).2
      obtain ⟨i, hi⟩ := card_pos.mp (show 0 < blen n B b by omega)
      simp only [mem_filter, mem_range] at hi
      exact ⟨i, hi.1, hi.2⟩
    · rw [← sum_blen, hsumL]; omega
  have hρ : (n : ℝ) ^ 2 / 2 ^ (k - 1) ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    have : (4 * (n : ℝ) ^ 2) ≤ 2 ^ k := by exact_mod_cast hkn
    rw [div_le_iff₀ (by positivity)]; linarith
  set ρ := (n : ℝ) ^ 2 / 2 ^ (k - 1)
  have hρ0 : 0 ≤ ρ := by positivity
  have hterm : ∀ a ∈ Icc 1 (n + 1), ((bigBlocks n a (e + a * (k - 1))).card : ℝ) ≤
      2 ^ (n - 1) * (1 / 2) ^ e * ρ ^ a := by
    intro a _
    have h := card_bigBlocks n a (e + a * (k - 1))
    have hc : ((n.choose a : ℕ) : ℝ) ≤ (n : ℝ) ^ a := by exact_mod_cast Nat.choose_le_pow n a
    have hpos : (0 : ℝ) < 2 ^ (e + a * (k - 1)) := by positivity
    have h' : ((bigBlocks n a (e + a * (k - 1))).card : ℝ) * 2 ^ (e + a * (k - 1)) ≤
        ((n : ℝ) ^ a) ^ 2 * 2 ^ (n - 1) := by
      have : ((bigBlocks n a (e + a * (k - 1))).card : ℝ) * 2 ^ (e + a * (k - 1)) ≤
          ((n.choose a : ℕ) : ℝ) ^ 2 * 2 ^ (n - 1) := by exact_mod_cast h
      refine this.trans ?_
      gcongr
    have hid : 2 ^ (n - 1) * (1 / 2) ^ e * ρ ^ a =
        ((n : ℝ) ^ a) ^ 2 * 2 ^ (n - 1) / 2 ^ (e + a * (k - 1)) := by
      simp only [ρ, div_pow, pow_add, ← pow_mul]
      field_simp
      ring
    rw [hid, le_div_iff₀ hpos]; exact h'
  have hgeom : ∑ a ∈ Icc 1 (n + 1), ρ ^ a ≤ 2 * ρ := by
    have : Icc 1 (n + 1) = Ico 1 (n + 2) := by ext; simp; omega
    rw [this]
    have := geom_sum_Ico_le_of_lt_one hρ0 (by linarith : ρ < 1) (m := 1) (n := n + 2)
    refine this.trans ?_
    rw [pow_one, div_le_iff₀ (by linarith)]
    nlinarith
  calc ((U.filter (fun B => e ≤ excess n B k)).card : ℝ)
      ≤ (((Icc 1 (n + 1)).biUnion (fun a => bigBlocks n a (e + a * (k - 1)))).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ a ∈ Icc 1 (n + 1), ((bigBlocks n a (e + a * (k - 1))).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ a ∈ Icc 1 (n + 1), 2 ^ (n - 1) * (1 / 2) ^ e * ρ ^ a := sum_le_sum hterm
    _ = 2 ^ (n - 1) * (1 / 2) ^ e * ∑ a ∈ Icc 1 (n + 1), ρ ^ a := by rw [mul_sum]
    _ ≤ 2 ^ (n - 1) * (1 / 2) ^ e * (2 * ρ) := by gcongr
    _ = 4 * n ^ 2 * 2 ^ (n - 1) * (1 / 2) ^ (k + e) := by
        have h2 : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
          rw [← pow_succ']; congr 1; omega
        simp only [ρ, pow_add, one_div_pow]
        field_simp
        rw [h2]; ring

/-- `∑_{e ≥ 1} #{A : |A| + 2 ≤ k + e} 2^(-k-e) ≤ (3/2)^(n-1) / 2`. -/
theorem sum_few_cuts_weighted (n k : ℕ) :
    ∑ e ∈ Icc 1 n, (((range (n - 1)).powerset.filter (fun A => A.card + 2 ≤ k + e)).card : ℝ) *
      (1 / 2) ^ (k + e) ≤ (1 / 2) * (3 / 2) ^ (n - 1) := by
  set U := (range (n - 1)).powerset
  have hinner : ∀ A ∈ U, ∑ e ∈ Icc 1 n,
      (if A.card + 2 ≤ k + e then (1 / 2 : ℝ) ^ (k + e) else 0) ≤ (1 / 2) * (1 / 2) ^ A.card := by
    intro A _
    rw [← sum_filter]
    have hmap : ∑ e ∈ (Icc 1 n).filter (fun e => A.card + 2 ≤ k + e), (1 / 2 : ℝ) ^ (k + e) =
        ∑ u ∈ ((Icc 1 n).filter (fun e => A.card + 2 ≤ k + e)).map (addLeftEmbedding k),
          (1 / 2 : ℝ) ^ u := by
      rw [sum_map]; rfl
    rw [hmap]
    have hsub : ((Icc 1 n).filter (fun e => A.card + 2 ≤ k + e)).map (addLeftEmbedding k) ⊆
        Ico (A.card + 2) (k + n + 1) := by
      intro u hu
      obtain ⟨e, he, rfl⟩ := mem_map.mp hu
      simp only [mem_filter, mem_Icc] at he
      simp only [mem_Ico, addLeftEmbedding_apply]; omega
    refine (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
    refine (geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)).trans ?_
    rw [pow_add]; apply le_of_eq; ring
  calc ∑ e ∈ Icc 1 n, ((U.filter (fun A => A.card + 2 ≤ k + e)).card : ℝ) * (1 / 2) ^ (k + e)
      = ∑ e ∈ Icc 1 n, ∑ A ∈ U, (if A.card + 2 ≤ k + e then (1 / 2 : ℝ) ^ (k + e) else 0) := by
        refine sum_congr rfl fun e _ => ?_
        rw [card_filter, Nat.cast_sum, sum_mul]
        refine sum_congr rfl fun A _ => ?_
        split_ifs <;> simp
    _ = ∑ A ∈ U, ∑ e ∈ Icc 1 n,
          (if A.card + 2 ≤ k + e then (1 / 2 : ℝ) ^ (k + e) else 0) := sum_comm
    _ ≤ ∑ A ∈ U, (1 / 2) * (1 / 2 : ℝ) ^ A.card := sum_le_sum hinner
    _ = (1 / 2) * (3 / 2) ^ (n - 1) := by rw [← mul_sum, sum_half_pow]

/-! ### Failures of one inequality -/

open scoped Classical in
/-- Pairs of cut sets `(A, B)` failing `RunDominance n A B`. -/
noncomputable def runFail (n : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((range (n - 1)).powerset ×ˢ (range (n - 1)).powerset).filter
    (fun ab => ¬ RunDominance n ab.1 ab.2)

/-- **The two regimes, counted.** If `4n² ≤ 2^(m+1)`, then
`#runFail ≤ 2n³ 3^(n-1) + C(n,m)² 2^m 3^(n-1) / 4 + n^m 2^(n-1)`. -/
theorem card_runFail (n m : ℕ) (hm : 4 * n ^ 2 ≤ 2 ^ (m + 1)) :
    ((runFail n).card : ℝ) ≤ 2 * n ^ 3 * 3 ^ (n - 1) +
      (n.choose m : ℝ) ^ 2 * 2 ^ m * 3 ^ (n - 1) / 4 + n ^ m * 2 ^ (n - 1) := by
  classical
  set U := (range (n - 1)).powerset
  have h32 : (3 : ℝ) ^ (n - 1) = 2 ^ (n - 1) * (3 / 2) ^ (n - 1) := by
    rw [← mul_pow]; norm_num
  rcases (runFail n).eq_empty_or_nonempty with h0 | ⟨⟨A0, B0⟩, h0⟩
  · rw [h0, card_empty, Nat.cast_zero]; positivity
  have hn : 1 ≤ n := by
    simp only [runFail, mem_filter] at h0
    obtain ⟨R, hR, hlt⟩ := (not_runDominance_iff n A0 B0).mp h0.2
    have := (sum_le_sum_of_subset (f := blen n A0) hR).trans (sum_range_blen n A0).le
    omega
  let Ae : ℕ → ℕ → Finset (Finset ℕ) := fun k e => U.filter (fun A => A.card + 2 ≤ k + e)
  let Be : ℕ → ℕ → Finset (Finset ℕ) := fun k e => U.filter (fun B => e ≤ excess n B k)
  let S1 := (U.filter (fun A => A.card + 2 ≤ m)) ×ˢ U
  let S2 := U.biUnion (fun B => bigBlocks n m (B.card + 2 - m) ×ˢ {B})
  let S3 := (Ioo m n).biUnion (fun k => (Icc 1 n).biUnion (fun e => Ae k e ×ˢ Be k e))
  have hsub : runFail n ⊆ S1 ∪ S2 ∪ S3 := by
    rintro ⟨A, B⟩ h
    simp only [runFail, mem_filter, mem_product, mem_powerset] at h
    obtain ⟨⟨hA, hB⟩, hf⟩ := h
    obtain ⟨R, hR, hlt⟩ := (not_runDominance_iff n A B).mp hf
    rcases fail_cases (m := m) hA hR hlt (card_nonempty_blocks hn hB) with
      h1 | h2 | ⟨k, hk, e, he, h3, h4⟩
    · apply mem_union_left; apply mem_union_left
      simp only [S1, U, mem_product, mem_filter, mem_powerset]
      exact ⟨⟨hA, h1⟩, hB⟩
    · apply mem_union_left; apply mem_union_right
      simp only [S2, mem_biUnion, mem_product, mem_singleton]
      exact ⟨B, mem_powerset.mpr hB, h2, rfl⟩
    · apply mem_union_right
      simp only [S3, Ae, Be, mem_biUnion, mem_product, mem_filter]
      exact ⟨k, hk, e, he, ⟨mem_powerset.mpr hA, h3⟩, ⟨mem_powerset.mpr hB, h4⟩⟩
  have hS1 : (S1.card : ℝ) ≤ n ^ m * 2 ^ (n - 1) := by
    simp only [S1, card_product, U, card_powerset, card_range]
    push_cast
    gcongr
    exact_mod_cast card_few_cuts hn m
  have hS2 : (S2.card : ℝ) ≤ (n.choose m : ℝ) ^ 2 * 2 ^ m * 3 ^ (n - 1) / 4 := by
    calc (S2.card : ℝ)
        ≤ ∑ B ∈ U, ((bigBlocks n m (B.card + 2 - m) ×ˢ {B}).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ = ∑ B ∈ U, ((bigBlocks n m (B.card + 2 - m)).card : ℝ) := by
          simp only [card_product, card_singleton, mul_one]
      _ ≤ ∑ B ∈ U, (n.choose m : ℝ) ^ 2 * 2 ^ (n - 1) * 2 ^ m / 4 * (1 / 2) ^ B.card :=
          sum_le_sum fun B _ => card_bigBlocks_real n m B.card
      _ = (n.choose m : ℝ) ^ 2 * 2 ^ (n - 1) * 2 ^ m / 4 * (3 / 2) ^ (n - 1) := by
          rw [← mul_sum, sum_half_pow]
      _ = _ := by rw [h32]; ring
  have hk : ∀ k ∈ Ioo m n,
      (((Icc 1 n).biUnion (fun e => Ae k e ×ˢ Be k e)).card : ℝ) ≤ 2 * n ^ 2 * 3 ^ (n - 1) := by
    intro k hk
    have hk' := mem_Ioo.mp hk
    have hkn : 4 * n ^ 2 ≤ 2 ^ k :=
      hm.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    calc (((Icc 1 n).biUnion (fun e => Ae k e ×ˢ Be k e)).card : ℝ)
        ≤ ∑ e ∈ Icc 1 n, ((Ae k e).card : ℝ) * (Be k e).card := by
          have := card_biUnion_le (s := Icc 1 n) (t := fun e => Ae k e ×ˢ Be k e)
          simp only [card_product] at this
          exact_mod_cast this
      _ ≤ ∑ e ∈ Icc 1 n, ((Ae k e).card : ℝ) * (4 * n ^ 2 * 2 ^ (n - 1) * (1 / 2) ^ (k + e)) := by
          apply sum_le_sum
          intro e he
          gcongr
          exact card_excess_ge (by omega) (mem_Icc.mp he).1 hkn
      _ = 4 * n ^ 2 * 2 ^ (n - 1) * ∑ e ∈ Icc 1 n, ((Ae k e).card : ℝ) * (1 / 2) ^ (k + e) := by
          rw [mul_sum]; exact sum_congr rfl fun e _ => by ring
      _ ≤ 4 * n ^ 2 * 2 ^ (n - 1) * ((1 / 2) * (3 / 2) ^ (n - 1)) := by
          gcongr; exact sum_few_cuts_weighted n k
      _ = 2 * n ^ 2 * 3 ^ (n - 1) := by rw [h32]; ring
  have hS3 : (S3.card : ℝ) ≤ 2 * n ^ 3 * 3 ^ (n - 1) := by
    calc (S3.card : ℝ)
        ≤ ∑ k ∈ Ioo m n, (((Icc 1 n).biUnion (fun e => Ae k e ×ˢ Be k e)).card : ℝ) := by
          exact_mod_cast card_biUnion_le
      _ ≤ ∑ k ∈ Ioo m n, 2 * (n : ℝ) ^ 2 * 3 ^ (n - 1) := sum_le_sum hk
      _ = (Ioo m n).card * (2 * (n : ℝ) ^ 2 * 3 ^ (n - 1)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ n * (2 * (n : ℝ) ^ 2 * 3 ^ (n - 1)) := by
          gcongr
          rw [Nat.card_Ioo]; exact_mod_cast Nat.sub_le_sub_right (Nat.sub_le n m) 1 |>.trans
            (Nat.sub_le _ _)
      _ = 2 * n ^ 3 * 3 ^ (n - 1) := by ring
  have hU := card_le_card hsub
  have hU' : ((runFail n).card : ℝ) ≤ S1.card + S2.card + S3.card := by
    have := (hU.trans (card_union_le _ _)).trans (Nat.add_le_add_right (card_union_le _ _) _)
    exact_mod_cast this
  linarith

/-! ### Theorem 3.6 -/

open scoped Classical in
/-- Pairs `(S, T)` violating the cross-dominance inequalities (3.2), in subset form. -/
noncomputable def grBad (n : ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  ((range (n - 1)).powerset ×ˢ (range (n - 1)).powerset).filter (fun st =>
    ¬ (RunDominance n st.1 (complementCuts n st.2) ∧ RunDominance n st.2 (complementCuts n st.1)))

/-- Each inequality of (3.2) is a `RunDominance` for cut sets; `T ↦ [n-1] \ T` and the swap
`(S, T) ↦ (T, S)` carry both to `runFail`. -/
theorem card_grBad_le (n : ℕ) : (grBad n).card ≤ 2 * (runFail n).card := by
  classical
  set U := (range (n - 1)).powerset
  let F1 := (U ×ˢ U).filter (fun st => ¬ RunDominance n st.1 (complementCuts n st.2))
  let F2 := (U ×ˢ U).filter (fun st => ¬ RunDominance n st.2 (complementCuts n st.1))
  have hsub : grBad n ⊆ F1 ∪ F2 := by
    intro st h
    simp only [grBad, mem_filter] at h
    simp only [F1, F2, mem_union, mem_filter]
    tauto
  have hccU : ∀ T, complementCuts n T ⊆ range (n - 1) := fun T => sdiff_subset
  have hcc : ∀ T ⊆ range (n - 1), complementCuts n (complementCuts n T) = T :=
    fun T hT => Finset.sdiff_sdiff_eq_self hT
  have h1 : F1.card = (runFail n).card := by
    refine card_nbij' (fun st => (st.1, complementCuts n st.2))
      (fun st => (st.1, complementCuts n st.2)) ?_ ?_ ?_ ?_
    · rintro ⟨S, T⟩ h
      simp only [F1, U, runFail, coe_filter, mem_product, mem_powerset, Set.mem_ofPred_eq] at h ⊢
      exact ⟨⟨h.1.1, hccU T⟩, h.2⟩
    · rintro ⟨A, B⟩ h
      simp only [F1, U, runFail, coe_filter, mem_product, mem_powerset, Set.mem_ofPred_eq] at h ⊢
      exact ⟨⟨h.1.1, hccU B⟩, by rw [hcc B h.1.2]; exact h.2⟩
    · rintro ⟨S, T⟩ h
      simp only [F1, U, coe_filter, mem_product, mem_powerset, Set.mem_ofPred_eq] at h
      simp [hcc T h.1.2]
    · rintro ⟨A, B⟩ h
      simp only [runFail, coe_filter, mem_product, mem_powerset, Set.mem_ofPred_eq] at h
      simp [hcc B h.1.2]
  have h2 : F2.card = F1.card := by
    refine card_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_
    · rintro ⟨S, T⟩ h
      simp only [F1, F2, coe_filter, mem_product, Set.mem_ofPred_eq, Prod.fst_swap,
        Prod.snd_swap] at h ⊢
      exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩
    · rintro ⟨S, T⟩ h
      simp only [F1, F2, coe_filter, mem_product, Set.mem_ofPred_eq, Prod.fst_swap,
        Prod.snd_swap] at h ⊢
      exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩
    · intro _ _; rfl
    · intro _ _; rfl
  calc (grBad n).card ≤ (F1 ∪ F2).card := card_le_card hsub
    _ ≤ F1.card + F2.card := card_union_le _ _
    _ = 2 * (runFail n).card := by rw [h2, h1]; ring

/-- The consecutive-integer obstruction violates (3.2): if `T ⊇ {0, …, |S|}`, the block of
`[n-1] \ T` at `0` is longer than `|S| + 1`, while the `|S| + 1` runs of `S` cover all `n`. -/
theorem not_runDominance_block {n : ℕ} {S T : Finset ℕ} (hT : T ⊆ range (n - 1))
    (h : range (S.card + 1) ⊆ T) : ¬ RunDominance n S (complementCuts n T) := by
  rw [not_runDominance_iff]
  have hST : S.card + 2 ≤ n := by
    have h1 := card_le_card h; have h2 := card_le_card hT
    simp only [card_range] at h1 h2; omega
  refine ⟨range (S.card + 1), fun b hb => by simp only [mem_range] at hb ⊢; omega, ?_⟩
  rw [card_range]
  have hA : ∑ b ∈ range (S.card + 1), blen n S b = n := by
    rw [sum_blen, filter_true_of_mem, card_range]
    intro i _
    have : block S i ≤ S.card := card_le_card (filter_subset _ _)
    simp only [mem_range]; omega
  have h0 : S.card + 2 ≤ blen n (complementCuts n T) 0 := by
    unfold blen
    have hs : range (S.card + 2) ⊆
        (range n).filter (fun i => block (complementCuts n T) i = 0) := by
      intro i hi
      simp only [mem_range] at hi
      simp only [mem_filter, mem_range]
      refine ⟨by omega, ?_⟩
      unfold block
      rw [card_eq_zero, filter_eq_empty_iff]
      intro c hc hci
      simp only [complementCuts, mem_sdiff] at hc
      exact hc.2 (h (by simp only [mem_range]; omega))
    simpa using card_le_card hs
  rw [hA]
  calc ∑ j ∈ range (n + 1), min (S.card + 1) (blen n (complementCuts n T) j)
      < ∑ j ∈ range (n + 1), blen n (complementCuts n T) j :=
        sum_lt_sum (fun j _ => min_le_right _ _)
          ⟨0, by simp, min_lt_iff.mpr (Or.inl (by omega))⟩
    _ = n := sum_range_blen n _

theorem blockPairs_subset_grBad (n : ℕ) : Stanley.blockPairs n ⊆ grBad n := by
  rintro ⟨S, T⟩ h
  simp only [Stanley.blockPairs, mem_filter, mem_product, mem_powerset] at h
  obtain ⟨⟨hS, hT⟩, h1 | h2⟩ := h
  · simp only [grBad, mem_filter, mem_product, mem_powerset]
    exact ⟨⟨hS, hT⟩, fun hh => not_runDominance_block hT h1 hh.1⟩
  · simp only [grBad, mem_filter, mem_product, mem_powerset]
    exact ⟨⟨hS, hT⟩, fun hh => not_runDominance_block hS h2 hh.2⟩

/-- Every pair violating (3.2) fails to occur (Lemma 3.5). -/
theorem disjoint_pairs_grBad (n : ℕ) : Disjoint (Stanley.pairs n) (grBad n) := by
  rw [disjoint_left]
  rintro ⟨S, T⟩ hp hb
  have hbeta := (Stanley.beta_pos_iff_mem_pairs n S T).mpr hp
  simp only [grBad, mem_filter] at hb
  exact hb.2 (beta_pos_implies_cross_dominance S T hbeta)

theorem f_add_card_grBad_le (n : ℕ) : Stanley.f n + (grBad n).card ≤ 4 ^ (n - 1) := by
  have hb : grBad n ⊆ (range (n - 1)).powerset ×ˢ (range (n - 1)).powerset := by
    intro st h; simp only [grBad, mem_filter] at h; exact h.1
  have hU := card_le_card (union_subset (Stanley.pairs_subset n) hb)
  rw [card_union_of_disjoint (disjoint_pairs_grBad n), card_product, card_powerset,
    card_range] at hU
  have h4 : 2 ^ (n - 1) * 2 ^ (n - 1) = 4 ^ (n - 1) := by rw [← mul_pow]; norm_num
  change (Stanley.pairs n).card + (grBad n).card ≤ 4 ^ (n - 1)
  omega

/-- **Theorem 3.6.** With `P_n = #grBad / 4^(n-1)` and `m = ⌈2 log₂ n⌉ + 1 = clog₂(n²) + 1`,
`(3^(n-1) - 1)/4^(n-1) ≤ P_n ≤ (4n³ + 2^(m-1) C(n,m)²)(3/4)^(n-1) + 4n^m/2^n`,
and `P_n ≤ 1 - f(n)/4^(n-1)`. -/
theorem gr_rate (n : ℕ) :
    ((3 : ℝ) ^ (n - 1) - 1) / 4 ^ (n - 1) ≤ (grBad n).card / 4 ^ (n - 1) ∧
    ((grBad n).card : ℝ) / 4 ^ (n - 1) ≤
      (4 * n ^ 3 + 2 ^ (Nat.clog 2 (n ^ 2) + 1 - 1) *
        (n.choose (Nat.clog 2 (n ^ 2) + 1) : ℝ) ^ 2) * (3 / 4) ^ (n - 1) +
        4 * n ^ (Nat.clog 2 (n ^ 2) + 1) / 2 ^ n ∧
    ((grBad n).card : ℝ) / 4 ^ (n - 1) ≤ 1 - Stanley.f n / 4 ^ (n - 1) := by
  set m := Nat.clog 2 (n ^ 2) + 1
  have h4 : (0 : ℝ) < 4 ^ (n - 1) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · -- lower bound: the block obstruction
    have h := card_le_card (blockPairs_subset_grBad n)
    rw [Stanley.card_blockPairs] at h
    have h1 : 1 ≤ 3 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
    have h' : ((3 : ℝ) ^ (n - 1) - 1) ≤ (grBad n).card := by
      have := (Nat.cast_le (α := ℝ)).mpr h
      push_cast [Nat.cast_sub h1] at this
      exact this
    exact div_le_div_of_nonneg_right h' h4.le
  · -- upper bound
    have hm : 4 * n ^ 2 ≤ 2 ^ (m + 1) := by
      have := Nat.le_pow_clog (by norm_num : 1 < 2) (n ^ 2)
      rw [show m + 1 = Nat.clog 2 (n ^ 2) + 2 by rfl, pow_add]
      omega
    have hr := card_runFail n m hm
    have hg : ((grBad n).card : ℝ) ≤ 2 * (runFail n).card := by
      exact_mod_cast card_grBad_le n
    have hm1 : (2 : ℝ) ^ m = 2 * 2 ^ (m - 1) := by
      have hmm : m = (m - 1) + 1 := by omega
      calc (2 : ℝ) ^ m = 2 ^ ((m - 1) + 1) := by rw [← hmm]
        _ = 2 * 2 ^ (m - 1) := pow_succ' _ _
    have h34 : (3 / 4 : ℝ) ^ (n - 1) * 4 ^ (n - 1) = 3 ^ (n - 1) := by
      rw [← mul_pow]; norm_num
    have h2n : (2 : ℝ) ^ n ≤ 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h44 : (4 : ℝ) ^ (n - 1) = 2 ^ (n - 1) * 2 ^ (n - 1) := by
      rw [← mul_pow]; norm_num
    have hlast : (n : ℝ) ^ m * 2 * 2 ^ (n - 1) ≤ 4 * n ^ m / 2 ^ n * 4 ^ (n - 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), h44]
      have : (0 : ℝ) ≤ n ^ m * 2 ^ (n - 1) := by positivity
      nlinarith
    rw [div_le_iff₀ h4, add_mul, mul_assoc _ ((3 / 4 : ℝ) ^ (n - 1)), h34]
    rw [hm1] at hr
    linear_combination hg + 2 * hr + hlast
  · -- every counted pair fails to occur
    have h := f_add_card_grBad_le n
    have h' : (Stanley.f n : ℝ) + (grBad n).card ≤ 4 ^ (n - 1) := by exact_mod_cast h
    rw [div_le_iff₀ h4, sub_mul, div_mul_cancel₀ _ h4.ne', one_mul]
    linarith

/-- The explicit bound in polynomial form: `#grBad ≤ 3^(n-1) (4n)^(2m+3)`. -/
theorem card_grBad_le_poly {n : ℕ} (hn : 1 ≤ n) :
    ((grBad n).card : ℝ) ≤ 3 ^ (n - 1) * (4 * n) ^ (2 * (Nat.clog 2 (n ^ 2) + 1) + 3) := by
  set m := Nat.clog 2 (n ^ 2) + 1
  have hm : 4 * n ^ 2 ≤ 2 ^ (m + 1) := by
    have := Nat.le_pow_clog (by norm_num : 1 < 2) (n ^ 2)
    rw [show m + 1 = Nat.clog 2 (n ^ 2) + 2 by rfl, pow_add]
    omega
  have hr := card_runFail n m hm
  have hg : ((grBad n).card : ℝ) ≤ 2 * (runFail n).card := by exact_mod_cast card_grBad_le n
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : (n.choose m : ℝ) ^ 2 ≤ (n : ℝ) ^ (2 * m) := by
    rw [pow_mul']; gcongr; exact_mod_cast Nat.choose_le_pow n m
  have h23 : (2 : ℝ) ^ (n - 1) ≤ 3 ^ (n - 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  set a := (n : ℝ) ^ (2 * m + 3)
  have ha3 : (n : ℝ) ^ 3 ≤ a := pow_le_pow_right₀ hn1 (by omega)
  have ha2 : (n : ℝ) ^ (2 * m) ≤ a := pow_le_pow_right₀ hn1 (by omega)
  have ha1 : (n : ℝ) ^ m ≤ a := pow_le_pow_right₀ hn1 (by omega)
  have hts : (2 : ℝ) ^ m ≤ 16 ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hs1 : (1 : ℝ) ≤ 16 ^ m := one_le_pow₀ (by norm_num)
  have h4n : (4 * (n : ℝ)) ^ (2 * m + 3) = 64 * 16 ^ m * a := by
    rw [mul_pow, pow_add, pow_mul]; norm_num; ring
  have h3 : (0 : ℝ) ≤ 3 ^ (n - 1) := by positivity
  have hkey : 4 * (n : ℝ) ^ 3 + (n : ℝ) ^ (2 * m) * 2 ^ m / 2 + 2 * n ^ m ≤ 64 * 16 ^ m * a := by
    have hp : (n : ℝ) ^ (2 * m) * 2 ^ m ≤ a * 16 ^ m :=
      mul_le_mul ha2 hts (by positivity) (by positivity)
    have ha0 : 0 ≤ a := by positivity
    nlinarith
  calc ((grBad n).card : ℝ) ≤ 2 * (2 * n ^ 3 * 3 ^ (n - 1) +
        (n.choose m : ℝ) ^ 2 * 2 ^ m * 3 ^ (n - 1) / 4 + n ^ m * 2 ^ (n - 1)) := by linarith
    _ ≤ 2 * (2 * n ^ 3 * 3 ^ (n - 1) +
        (n : ℝ) ^ (2 * m) * 2 ^ m * 3 ^ (n - 1) / 4 + n ^ m * 3 ^ (n - 1)) := by gcongr
    _ = 3 ^ (n - 1) * (4 * (n : ℝ) ^ 3 + (n : ℝ) ^ (2 * m) * 2 ^ m / 2 + 2 * n ^ m) := by ring
    _ ≤ 3 ^ (n - 1) * (64 * 16 ^ m * a) := by gcongr
    _ = 3 ^ (n - 1) * (4 * n) ^ (2 * m + 3) := by rw [h4n]

/-- **Theorem 3.6, asymptotic form.** `P_n = (3/4)^(n + O(log² n))`. -/
theorem gr_rate_asymp : ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
    (3 / 4 : ℝ) ^ (n + 1) ≤ (grBad n).card / 4 ^ (n - 1) ∧
    ((grBad n).card : ℝ) / 4 ^ (n - 1) ≤ (3 / 4 : ℝ) ^ ((n : ℝ) - C * Real.log n ^ 2) := by
  set l2 := Real.log 2 with hl2def
  set L := Real.log (4 / 3) with hLdef
  have hl2 : 0 < l2 := Real.log_pos (by norm_num)
  have hL : 0 < L := Real.log_pos (by norm_num)
  refine ⟨1 / l2 ^ 2 + 33 / (l2 * L), fun n hn => ⟨?_, ?_⟩⟩
  · have h := (gr_rate n).1
    have h4 : (0 : ℝ) < 4 ^ (n - 1) := by positivity
    have h3 : (3 : ℝ) ≤ 3 ^ (n - 1) := by
      calc (3 : ℝ) = 3 ^ 1 := (pow_one _).symm
        _ ≤ 3 ^ (n - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    refine le_trans ?_ h
    rw [le_div_iff₀ h4]
    have : (3 / 4 : ℝ) ^ (n + 1) * 4 ^ (n - 1) = 9 / 16 * 3 ^ (n - 1) := by
      rw [show n + 1 = (n - 1) + 2 by omega, pow_add, mul_comm, ← mul_assoc, ← mul_pow]
      norm_num; ring
    rw [this]; linarith
  · set m := Nat.clog 2 (n ^ 2) + 1
    set x := Real.log n with hxdef
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hx : l2 ≤ x := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have hx0 : 0 < x := hl2.trans_le hx
    -- `m < 2 log₂ n + 2`
    have hm : (m : ℝ) * l2 ≤ 2 * x + 2 * l2 := by
      have h := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2)
        (show 1 < n ^ 2 by nlinarith)
      have h' : ((2 : ℝ) ^ (Nat.clog 2 (n ^ 2)).pred) < (n : ℝ) ^ 2 := by exact_mod_cast h
      have hlog := Real.log_lt_log (by positivity) h'
      rw [Real.log_pow, Real.log_pow] at hlog
      have hcl : (Nat.clog 2 (n ^ 2) : ℝ) ≤ ((Nat.clog 2 (n ^ 2)).pred : ℕ) + 1 := by
        exact_mod_cast (show Nat.clog 2 (n ^ 2) ≤ (Nat.clog 2 (n ^ 2)).pred + 1 by
          rw [Nat.pred_eq_sub_one]; omega)
      have hlog' : (((Nat.clog 2 (n ^ 2)).pred : ℕ) : ℝ) * l2 < 2 * x := by
        push_cast at hlog; exact hlog
      have : (m : ℝ) = Nat.clog 2 (n ^ 2) + 1 := by push_cast [m]; ring
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_right hcl hl2.le]
    have hP := card_grBad_le_poly (n := n) (by omega)
    have h4 : (0 : ℝ) < 4 ^ (n - 1) := by positivity
    set Q := (3 / 4 : ℝ) ^ (n - 1) * (4 * n) ^ (2 * m + 3)
    have hPQ : ((grBad n).card : ℝ) / 4 ^ (n - 1) ≤ Q := by
      rw [div_le_iff₀ h4]
      have : Q * 4 ^ (n - 1) = 3 ^ (n - 1) * (4 * n) ^ (2 * m + 3) := by
        simp only [Q]; rw [mul_comm, ← mul_assoc, ← mul_pow]; norm_num
      rw [this]; exact hP
    have hQ : 0 < Q := by positivity
    have hlogQ : Real.log Q = -(((n - 1 : ℕ) : ℝ) * L) + (2 * m + 3) * (2 * l2 + x) := by
      simp only [Q]
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
        Real.log_mul (by norm_num) hn0.ne', show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num,
        Real.log_inv, ← hLdef, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, ← hl2def,
        ← hxdef]
      push_cast; ring
    have hn1 : ((n - 1 : ℕ) : ℝ) = n - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    -- the exponent comparison, with `u = log n / log 2 ≥ 1`
    set u := x / l2
    have hu : 1 ≤ u := by rw [le_div_iff₀ hl2]; linarith
    have hxu : x = u * l2 := (div_mul_cancel₀ x hl2.ne').symm
    have hm' : (m : ℝ) ≤ 2 * u + 2 := by
      rw [hxu] at hm
      exact le_of_mul_le_mul_right (by linarith : (m : ℝ) * l2 ≤ (2 * u + 2) * l2) hl2
    have hgoal : Real.log Q ≤ Real.log (3 / 4) * ((n : ℝ) - (1 / l2 ^ 2 + 33 / (l2 * L)) * x ^ 2) := by
      rw [hlogQ, hn1, show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv]
      have e1 : (1 / l2 ^ 2 + 33 / (l2 * L)) * x ^ 2 * L = L * u ^ 2 + 33 * u ^ 2 * l2 := by
        rw [hxu]; field_simp
      have hA : (2 * (m : ℝ) + 3) * (2 * l2 + x) ≤ 33 * u ^ 2 * l2 := by
        rw [hxu]
        have hm0 : (0 : ℝ) ≤ m := by positivity
        have h1 : 2 * (m : ℝ) + 3 ≤ 11 * u := by linarith
        have h2 : 2 * l2 + u * l2 ≤ 3 * u * l2 := by nlinarith
        calc (2 * (m : ℝ) + 3) * (2 * l2 + u * l2) ≤ (11 * u) * (3 * u * l2) :=
              mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = 33 * u ^ 2 * l2 := by ring
      have hu2 : 1 ≤ u ^ 2 := by nlinarith
      have hB : L ≤ L * u ^ 2 :=
        calc L = L * 1 := (mul_one L).symm
          _ ≤ L * u ^ 2 := mul_le_mul_of_nonneg_left hu2 hL.le
      nlinarith [e1]
    calc ((grBad n).card : ℝ) / 4 ^ (n - 1) ≤ Q := hPQ
      _ = Real.exp (Real.log Q) := (Real.exp_log hQ).symm
      _ ≤ Real.exp (Real.log (3 / 4) * ((n : ℝ) - (1 / l2 ^ 2 + 33 / (l2 * L)) * x ^ 2)) :=
          Real.exp_le_exp.mpr hgoal
      _ = (3 / 4 : ℝ) ^ ((n : ℝ) - (1 / l2 ^ 2 + 33 / (l2 * L)) * x ^ 2) :=
          (Real.rpow_def_of_pos (by norm_num) _).symm

/-- **Corollary 3.7.** If (3.2) is sufficient (Conjecture 5.1), the pairs that fail to occur are
exactly those violating (3.2), so `1 - f(n)/4^(n-1) = P_n = (3/4)^(n + O(log² n))`. -/
theorem cor_rate {n : ℕ} (hconj : ∀ S T, S ⊆ range (n - 1) → T ⊆ range (n - 1) →
      RunDominance n S (complementCuts n T) → RunDominance n T (complementCuts n S) →
      (S, T) ∈ Stanley.pairs n) :
    1 - (Stanley.f n : ℝ) / 4 ^ (n - 1) = (grBad n).card / 4 ^ (n - 1) := by
  classical
  have hle := f_add_card_grBad_le n
  have hge : 4 ^ (n - 1) ≤ Stanley.f n + (grBad n).card := by
    have hsub : (range (n - 1)).powerset ×ˢ (range (n - 1)).powerset ⊆
        Stanley.pairs n ∪ grBad n := by
      rintro ⟨S, T⟩ h
      simp only [mem_product, mem_powerset] at h
      by_cases hd : RunDominance n S (complementCuts n T) ∧ RunDominance n T (complementCuts n S)
      · exact mem_union_left _ (hconj S T h.1 h.2 hd.1 hd.2)
      · apply mem_union_right
        simp only [grBad, mem_filter, mem_product, mem_powerset]
        exact ⟨h, hd⟩
    have hc := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_product, card_powerset, card_range] at hc
    have h4 : 2 ^ (n - 1) * 2 ^ (n - 1) = 4 ^ (n - 1) := by rw [← mul_pow]; norm_num
    change 4 ^ (n - 1) ≤ (Stanley.pairs n).card + (grBad n).card
    omega
  have heq : (Stanley.f n : ℝ) + (grBad n).card = 4 ^ (n - 1) := by
    exact_mod_cast le_antisymm hle hge
  have h4 : (0 : ℝ) < 4 ^ (n - 1) := by positivity
  field_simp
  linarith

end Stanley.Alt
