import Mathlib

/-!
# Capped dice: the most distinguishable pair (MSE 5149864)

Two dice `p`, `q` on `k` faces, every face probability at most `r` (with `k r ≥ 1`). Over `n` rolls the overlap
`∑_w min(P(w), Q(w))` is at least its value for the staircase pair: `p* = (r, …, r, 1 - m r, 0, …, 0)`, `m = ⌊1/r⌋`,
and `q*` its reversal. For `k = 4`, `1/3 < r < 1/2` this is the asker's pair, so the asker's bound is exact.

* `excess_le`: for any admissible pair, `∑ (u pᵢ - v qᵢ)⁺ ≤ u min(1, a r) - v max(0, 1 - (k - a) r)`, `a = |A|`.
* `stair_excess_ge`: the staircase pair attains that bound on its first `a` faces.
* `dominates`: hence the staircase excess is the largest, at every pair of rates `(u, v)`.
* `G_le`: domination at every rate survives products, one roll at a time.
* `overlap_ge`, `asker_optimal`: the overlap statements.
-/

namespace CappedDice

open Finset

/-! ### One roll -/

/-- Face probabilities in `[0, r]`, total `1`. -/
def Adm {k : ℕ} (r : ℝ) (p : Fin k → ℝ) : Prop := (∀ i, 0 ≤ p i ∧ p i ≤ r) ∧ ∑ i, p i = 1

/-- The excess of `u p` over `v q`. -/
noncomputable def g {k : ℕ} (p q : Fin k → ℝ) (u v : ℝ) : ℝ := ∑ i, max (u * p i - v * q i) 0

theorem sum_pos_part {k : ℕ} (x : Fin k → ℝ) :
    ∑ i, max (x i) 0 = ∑ i ∈ univ.filter (fun i => 0 < x i), x i := by
  rw [sum_filter]
  refine sum_congr rfl fun i _ => ?_
  split_ifs with h
  · exact max_eq_left h.le
  · exact max_eq_right (not_lt.mp h)

/-- Any `a` faces carry at most `min(1, a r)` of `p` and at least `max(0, 1 - (k - a) r)` of `q`. -/
theorem excess_le {k : ℕ} {r : ℝ} {p q : Fin k → ℝ} (hp : Adm r p) (hq : Adm r q) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) :
    ∃ a ≤ k, g p q u v ≤ u * min 1 (a * r) - v * max 0 (1 - (k - a) * r) := by
  set A := univ.filter (fun i => 0 < u * p i - v * q i)
  refine ⟨A.card, card_le_univ A |>.trans (by simp), ?_⟩
  have hg : g p q u v = u * ∑ i ∈ A, p i - v * ∑ i ∈ A, q i := by
    rw [g, sum_pos_part, sum_sub_distrib, mul_sum, mul_sum]
  have hpA : ∑ i ∈ A, p i ≤ min 1 (A.card * r) := by
    refine le_min ?_ ?_
    · rw [← hp.2]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ A) fun i _ _ => (hp.1 i).1
    · have := sum_le_card_nsmul A p r fun i _ => (hp.1 i).2
      simpa using this
  have hqA : max 0 (1 - (k - A.card) * r) ≤ ∑ i ∈ A, q i := by
    refine max_le (sum_nonneg fun i _ => (hq.1 i).1) ?_
    have hsplit := sum_add_sum_compl A q
    rw [hq.2] at hsplit
    have hc : ∑ i ∈ Aᶜ, q i ≤ (Aᶜ.card : ℝ) * r := by
      have := sum_le_card_nsmul Aᶜ q r fun i _ => (hq.1 i).2
      simpa using this
    have hcard : (Aᶜ.card : ℝ) = k - A.card := by
      rw [card_compl, Fintype.card_fin, Nat.cast_sub (card_le_univ A |>.trans (by simp))]
    rw [hcard] at hc
    linarith
  rw [hg]
  nlinarith [mul_le_mul_of_nonneg_left hpA hu, mul_le_mul_of_nonneg_left hqA hv]

/-! ### The staircase pair -/

/-- `stair r i = clamp(1 - i r, 0, r)`: `r` for `i < m`, then `1 - m r`, then `0`. -/
noncomputable def stair (r : ℝ) (i : ℕ) : ℝ := max 0 (min r (1 - i * r))

theorem stair_nonneg (r : ℝ) (i : ℕ) : 0 ≤ stair r i := le_max_left _ _

theorem stair_le {r : ℝ} (hr : 0 ≤ r) (i : ℕ) : stair r i ≤ r :=
  max_le hr (min_le_left _ _)

/-- The first `a` steps of the staircase carry `min(1, a r)`. -/
theorem stair_sum {r : ℝ} (hr : 0 ≤ r) (a : ℕ) : ∑ i ∈ range a, stair r i = min 1 (a * r) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [sum_range_succ, ih, stair]
    push_cast
    rcases le_total (a * r) 1 with h | h
    · rw [min_eq_right h]
      rcases le_total r (1 - a * r) with h' | h'
      · rw [min_eq_left h', max_eq_right hr, min_eq_right (by linarith)]; ring
      · rw [min_eq_right h', max_eq_right (by linarith), min_eq_left (by linarith)]; ring
    · rw [min_eq_left h, max_eq_left (min_le_of_right_le (by linarith)), min_eq_left (by nlinarith)]
      ring

noncomputable def pstar (k : ℕ) (r : ℝ) : Fin k → ℝ := fun i => stair r i
noncomputable def qstar (k : ℕ) (r : ℝ) : Fin k → ℝ := fun i => stair r (k - 1 - i)

/-- The reversed staircase on faces `0, …, a-1` carries what the staircase leaves on faces `k - a, …, k - 1`. -/
theorem rev_sum {r : ℝ} (hr : 0 ≤ r) {k a : ℕ} (hk : 1 ≤ k) (ha : a ≤ k) :
    ∑ i ∈ range a, stair r (k - 1 - i) = min 1 (k * r) - min 1 ((k - a : ℕ) * r) := by
  have h := sum_Ico_reflect (stair r) 0 (m := a) (n := k - 1) (by omega)
  rw [range_eq_Ico, h, show k - 1 + 1 - a = k - a by omega, show k - 1 + 1 - 0 = k by omega,
    sum_Ico_eq_sub _ (by omega : k - a ≤ k), stair_sum hr, stair_sum hr]

theorem pstar_adm {k : ℕ} {r : ℝ} (hr : 0 ≤ r) (hk : 1 ≤ k * r) : Adm r (pstar k r) := by
  refine ⟨fun i => ⟨stair_nonneg _ _, stair_le hr _⟩, ?_⟩
  rw [show (∑ i, pstar k r i) = ∑ i : Fin k, stair r i from rfl,
    Fin.sum_univ_eq_sum_range (fun i => stair r i), stair_sum hr, min_eq_left hk]

theorem qstar_adm {k : ℕ} {r : ℝ} (hr : 0 ≤ r) (hk : 1 ≤ k * r) : Adm r (qstar k r) := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk; linarith
    · exact h
  refine ⟨fun i => ⟨stair_nonneg _ _, stair_le hr _⟩, ?_⟩
  rw [show (∑ i, qstar k r i) = ∑ i : Fin k, stair r (k - 1 - i) from rfl,
    Fin.sum_univ_eq_sum_range (fun i => stair r (k - 1 - i)), rev_sum hr hk1 le_rfl]
  simp [min_eq_left hk]

/-- The staircase pair meets the bound of `excess_le` on its first `a` faces. -/
theorem stair_excess_ge {k : ℕ} {r : ℝ} (hr : 0 ≤ r) (hk : 1 ≤ k * r) {u v : ℝ} {a : ℕ} (ha : a ≤ k) :
    u * min 1 (a * r) - v * max 0 (1 - (k - a) * r) ≤ g (pstar k r) (qstar k r) u v := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hk; linarith
    · exact h
  rw [show g (pstar k r) (qstar k r) u v = ∑ i : Fin k, max (u * stair r i - v * stair r (k - 1 - i)) 0
    from rfl, Fin.sum_univ_eq_sum_range (fun i => max (u * stair r i - v * stair r (k - 1 - i)) 0)]
  calc u * min 1 (a * r) - v * max 0 (1 - (k - a) * r)
      = ∑ i ∈ range a, (u * stair r i - v * stair r (k - 1 - i)) := by
        rw [sum_sub_distrib, ← mul_sum, ← mul_sum, stair_sum hr, rev_sum hr hk1 ha, min_eq_left hk,
          Nat.cast_sub ha]
        congr 1
        rcases le_total ((k - a) * r) 1 with h | h
        · rw [min_eq_right h, max_eq_right (by linarith)]
        · rw [min_eq_left h, max_eq_left (by linarith)]; ring
    _ ≤ ∑ i ∈ range a, max (u * stair r i - v * stair r (k - 1 - i)) 0 :=
        sum_le_sum fun i _ => le_max_left _ _
    _ ≤ ∑ i ∈ range k, max (u * stair r i - v * stair r (k - 1 - i)) 0 :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr ha) fun i _ _ => le_max_right _ _

/-- One roll: the staircase pair has the largest excess at every pair of rates. -/
theorem dominates {k : ℕ} {r : ℝ} (hr : 0 ≤ r) (hk : 1 ≤ k * r) {p q : Fin k → ℝ} (hp : Adm r p)
    (hq : Adm r q) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) : g p q u v ≤ g (pstar k r) (qstar k r) u v := by
  obtain ⟨a, ha, h⟩ := excess_le hp hq hu hv
  exact h.trans (stair_excess_ge hr hk ha)

/-! ### `n` rolls -/

/-- Probability of the word `w` when roll `j` uses the pair `D j`. -/
def P {k n : ℕ} (D : Fin n → (Fin k → ℝ) × (Fin k → ℝ)) (w : Fin n → Fin k) : ℝ := ∏ j, (D j).1 (w j)
def Q {k n : ℕ} (D : Fin n → (Fin k → ℝ) × (Fin k → ℝ)) (w : Fin n → Fin k) : ℝ := ∏ j, (D j).2 (w j)

/-- The excess over words. -/
noncomputable def G {k n : ℕ} (D : Fin n → (Fin k → ℝ) × (Fin k → ℝ)) (u v : ℝ) : ℝ :=
  ∑ w : Fin n → Fin k, max (u * P D w - v * Q D w) 0

/-- Peel off the first roll. -/
theorem G_succ {k n : ℕ} (D : Fin (n + 1) → (Fin k → ℝ) × (Fin k → ℝ)) (u v : ℝ) :
    G D u v = ∑ i, G (fun j => D j.succ) (u * (D 0).1 i) (v * (D 0).2 i) := by
  rw [G, ← (Fin.consEquiv fun _ => Fin k).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => sum_congr rfl fun w _ => ?_
  simp only [Fin.consEquiv_apply, P, Q, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring_nf

/-- The same, with the first roll innermost. -/
theorem G_succ' {k n : ℕ} (D : Fin (n + 1) → (Fin k → ℝ) × (Fin k → ℝ)) (u v : ℝ) :
    G D u v = ∑ w : Fin n → Fin k,
      g (D 0).1 (D 0).2 (u * P (fun j => D j.succ) w) (v * Q (fun j => D j.succ) w) := by
  rw [G_succ]
  simp only [G, g]
  rw [sum_comm]
  refine sum_congr rfl fun w _ => sum_congr rfl fun i _ => ?_
  ring_nf

theorem P_nonneg {k n : ℕ} {D : Fin n → (Fin k → ℝ) × (Fin k → ℝ)} (h : ∀ j i, 0 ≤ (D j).1 i)
    (w : Fin n → Fin k) : 0 ≤ P D w := prod_nonneg fun j _ => h j (w j)

theorem Q_nonneg {k n : ℕ} {D : Fin n → (Fin k → ℝ) × (Fin k → ℝ)} (h : ∀ j i, 0 ≤ (D j).2 i)
    (w : Fin n → Fin k) : 0 ≤ Q D w := prod_nonneg fun j _ => h j (w j)

/-- Domination at every rate survives products: replace the rolls one at a time. -/
theorem G_le {k : ℕ} {p₀ q₀ : Fin k → ℝ} (h₀p : ∀ i, 0 ≤ p₀ i) (h₀q : ∀ i, 0 ≤ q₀ i) :
    ∀ (n : ℕ) (D : Fin n → (Fin k → ℝ) × (Fin k → ℝ)),
      (∀ j i, 0 ≤ (D j).1 i) → (∀ j i, 0 ≤ (D j).2 i) →
      (∀ j u v, 0 ≤ u → 0 ≤ v → g (D j).1 (D j).2 u v ≤ g p₀ q₀ u v) →
      ∀ u v, 0 ≤ u → 0 ≤ v → G D u v ≤ G (fun _ : Fin n => (p₀, q₀)) u v := by
  intro n
  induction n with
  | zero => intro D _ _ _ u v _ _; exact le_of_eq (by simp [G, P, Q])
  | succ n ih =>
    intro D hDp hDq hD u v hu hv
    calc G D u v
        = ∑ i, G (fun j => D j.succ) (u * (D 0).1 i) (v * (D 0).2 i) := G_succ D u v
      _ ≤ ∑ i, G (fun _ : Fin n => (p₀, q₀)) (u * (D 0).1 i) (v * (D 0).2 i) :=
          sum_le_sum fun i _ => ih _ (fun j => hDp j.succ) (fun j => hDq j.succ) (fun j => hD j.succ) _ _
            (mul_nonneg hu (hDp 0 i)) (mul_nonneg hv (hDq 0 i))
      _ = G (Fin.cons (D 0) fun _ : Fin n => (p₀, q₀)) u v := by
          rw [G_succ (Fin.cons (D 0) fun _ : Fin n => (p₀, q₀))]
          simp only [Fin.cons_zero, Fin.cons_succ]
      _ = ∑ w : Fin n → Fin k, g (D 0).1 (D 0).2 (u * P (fun _ : Fin n => (p₀, q₀)) w)
            (v * Q (fun _ : Fin n => (p₀, q₀)) w) := by
          rw [G_succ']
          simp only [Fin.cons_zero, Fin.cons_succ]
      _ ≤ ∑ w : Fin n → Fin k, g p₀ q₀ (u * P (fun _ : Fin n => (p₀, q₀)) w)
            (v * Q (fun _ : Fin n => (p₀, q₀)) w) :=
          sum_le_sum fun w _ => hD 0 _ _ (mul_nonneg hu (P_nonneg (fun _ => h₀p) w))
            (mul_nonneg hv (Q_nonneg (fun _ => h₀q) w))
      _ = G (fun _ : Fin (n + 1) => (p₀, q₀)) u v := by
          rw [G_succ' (fun _ : Fin (n + 1) => (p₀, q₀))]

/-! ### The overlap -/

/-- The quantity in the question: `∑_w min(P(w), Q(w))`. -/
noncomputable def overlap {k n : ℕ} (D : Fin n → (Fin k → ℝ) × (Fin k → ℝ)) : ℝ :=
  ∑ w : Fin n → Fin k, min (P D w) (Q D w)

theorem sum_P {k n : ℕ} {D : Fin n → (Fin k → ℝ) × (Fin k → ℝ)} (h : ∀ j, ∑ i, (D j).1 i = 1) :
    ∑ w, P D w = 1 := by
  rw [show (∑ w, P D w) = ∏ j, ∑ i, (D j).1 i from (Fintype.prod_sum fun j i => (D j).1 i).symm]
  simp [h]

/-- `overlap = 1 - excess at rate 1`. -/
theorem overlap_eq {k n : ℕ} {D : Fin n → (Fin k → ℝ) × (Fin k → ℝ)} (h : ∀ j, ∑ i, (D j).1 i = 1) :
    overlap D = 1 - G D 1 1 := by
  have hw : ∀ w, min (P D w) (Q D w) = P D w - max (1 * P D w - 1 * Q D w) 0 := by
    intro w
    rcases le_total (P D w) (Q D w) with hw | hw
    · rw [min_eq_left hw, max_eq_right (by linarith)]; ring
    · rw [min_eq_right hw, max_eq_left (by linarith)]; ring
  rw [overlap, G, sum_congr rfl fun w _ => hw w, sum_sub_distrib, sum_P h]

/-- **Theorem.** If `(p₀, q₀)` is admissible and dominates every admissible pair at every rate, then `n` rolls of
`(p₀, q₀)` have the least overlap among all admissible dice, mixed freely across rolls. -/
theorem overlap_ge_of_dominant {k : ℕ} {r : ℝ} {p₀ q₀ : Fin k → ℝ} (h₀p : Adm r p₀) (h₀q : Adm r q₀)
    (hdom : ∀ p q : Fin k → ℝ, Adm r p → Adm r q → ∀ u v, 0 ≤ u → 0 ≤ v → g p q u v ≤ g p₀ q₀ u v)
    (n : ℕ) (D : Fin n → (Fin k → ℝ) × (Fin k → ℝ)) (hD : ∀ j, Adm r (D j).1 ∧ Adm r (D j).2) :
    overlap (fun _ : Fin n => (p₀, q₀)) ≤ overlap D := by
  rw [overlap_eq fun j => (hD j).1.2, overlap_eq fun _ => h₀p.2]
  have := G_le (fun i => (h₀p.1 i).1) (fun i => (h₀q.1 i).1) n D (fun j i => ((hD j).1.1 i).1)
    (fun j i => ((hD j).2.1 i).1) (fun j u v hu hv => hdom _ _ (hD j).1 (hD j).2 u v hu hv) 1 1
    zero_le_one zero_le_one
  linarith

/-- **Main theorem.** `k` faces, cap `r` with `k r ≥ 1`: the staircase pair has the least overlap over `n` rolls. -/
theorem overlap_ge {k : ℕ} {r : ℝ} (hr : 0 ≤ r) (hk : 1 ≤ k * r) (n : ℕ)
    (D : Fin n → (Fin k → ℝ) × (Fin k → ℝ)) (hD : ∀ j, Adm r (D j).1 ∧ Adm r (D j).2) :
    overlap (fun _ : Fin n => (pstar k r, qstar k r)) ≤ overlap D :=
  overlap_ge_of_dominant (pstar_adm hr hk) (qstar_adm hr hk)
    (fun _ _ hp hq _ _ hu hv => dominates hr hk hp hq hu hv) n D hD

/-! ### The asker's pair (`k = 4`, `1/3 < r < 1/2`) -/

/-- The pair in the question: `p = (r, 1 - 2r, r, 0)`, `q = (0, r, 1 - 2r, r)`. -/
def pA (r : ℝ) : Fin 4 → ℝ := ![r, 1 - 2 * r, r, 0]
def qA (r : ℝ) : Fin 4 → ℝ := ![0, r, 1 - 2 * r, r]

theorem stair_values {r : ℝ} (h1 : 1 / 3 < r) (h2 : r < 1 / 2) :
    stair r 0 = r ∧ stair r 1 = r ∧ stair r 2 = 1 - 2 * r ∧ stair r 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stair, Nat.cast_zero, zero_mul, sub_zero, min_eq_left (by linarith), max_eq_right (by linarith)]
  · rw [stair, Nat.cast_one, one_mul, min_eq_left (by linarith), max_eq_right (by linarith)]
  · rw [stair, Nat.cast_ofNat, min_eq_right (by linarith), max_eq_right (by linarith)]
  · rw [stair, Nat.cast_ofNat, max_eq_left (min_le_of_right_le (by linarith))]

/-- The asker's pair is the staircase pair `((r, r, 1-2r, 0), (0, 1-2r, r, r))` up to
relabelling, so it has the same excess at every rate. -/
theorem g_asker {r : ℝ} (h1 : 1 / 3 < r) (h2 : r < 1 / 2) (u v : ℝ) :
    g (pA r) (qA r) u v = g (pstar 4 r) (qstar 4 r) u v := by
  obtain ⟨e0, e1, e2, e3⟩ := stair_values h1 h2
  simp [g, Fin.sum_univ_four, pA, qA, pstar, qstar, e0, e1, e2, e3]
  ring

theorem asker_adm {r : ℝ} (h1 : 1 / 3 < r) (h2 : r < 1 / 2) : Adm r (pA r) ∧ Adm r (qA r) := by
  refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun i => ?_, ?_⟩⟩
  · fin_cases i <;> simp [pA] <;> (try constructor) <;> linarith
  · simp [pA, Fin.sum_univ_four]; ring
  · fin_cases i <;> simp [qA] <;> (try constructor) <;> linarith
  · simp [qA, Fin.sum_univ_four]; ring

/-- **The question answered.** For `1/3 < r < 1/2` and every `n`, the asker's pair has the least overlap, so the
asker's bound (2) is the exact value of `C_n(r)`. -/
theorem asker_optimal {r : ℝ} (h1 : 1 / 3 < r) (h2 : r < 1 / 2) (n : ℕ)
    (D : Fin n → (Fin 4 → ℝ) × (Fin 4 → ℝ)) (hD : ∀ j, Adm r (D j).1 ∧ Adm r (D j).2) :
    overlap (fun _ : Fin n => (pA r, qA r)) ≤ overlap D := by
  have hr : (0 : ℝ) ≤ r := by linarith
  have hk : 1 ≤ (4 : ℕ) * r := by push_cast; linarith
  exact overlap_ge_of_dominant (asker_adm h1 h2).1 (asker_adm h1 h2).2
    (fun p q hp hq u v hu hv => (g_asker h1 h2 u v).symm ▸ dominates hr hk hp hq hu hv) n D hD

end CappedDice
