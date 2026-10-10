import Mathlib

/-!
# Five numbers that need many pairwise averages (MO 421671)

A move replaces two entries by their average. For `k ≥ 1` and `t = (-1/2)^k` the five numbers
`B_k = (2, -3, 1, 5t/2, 5t/2)` have mean `t`, and the least number of moves that makes them all equal is
exactly `k + 3`.

* `seq x mv r`: the entries after the moves `mv 0, …, mv (r-1)`; any strategy is a function `mv`.
* `weights`: after `r` moves each entry is `∑ mᵢ xᵢ / 2^r` with natural `mᵢ`, `∑ mᵢ = 2^r`.
* `no_mean_before`: for the integer tuple `N • B_k` (`N = 2^(k+1)`), no entry equals the mean before move `k`.
* `count_step`, `count_ne_four`: the number of entries equal to the mean changes by at most `0` or exactly `+2`
  in a move, and is never `4`.
* `lower_bound`: every strategy needs at least `k + 3` moves; `upper_bound`: `k + 3` moves suffice.
* `affine`: moves commute with `x ↦ c x + d`, so the same holds for `(5N, 0, 4N, 3N+5ε, 3N+5ε)`.
* `no_balanced_subset`: for `k ≥ 2` no nonempty proper subset of `B_k` has mean `t`.
-/

namespace PairwiseAveraging

open Finset

section General

variable {n : ℕ}

/-- One move: entries `p.1` and `p.2` both become their average. -/
def avg (x : Fin n → ℚ) (p : Fin n × Fin n) : Fin n → ℚ :=
  fun a => if a = p.1 ∨ a = p.2 then (x p.1 + x p.2) / 2 else x a

/-- The entries after the moves `mv 0, …, mv (r-1)`. -/
def seq (x : Fin n → ℚ) (mv : ℕ → Fin n × Fin n) : ℕ → Fin n → ℚ
  | 0 => x
  | r + 1 => avg (seq x mv r) (mv r)

theorem avg_of_ne {x : Fin n → ℚ} {p : Fin n × Fin n} {a : Fin n} (h1 : a ≠ p.1) (h2 : a ≠ p.2) :
    avg x p a = x a := by
  simp [avg, h1, h2]

/-- After `r` moves each entry is a dyadic convex combination of the inputs with denominator `2^r`. -/
theorem weights (x : Fin n → ℚ) (mv : ℕ → Fin n × Fin n) (r : ℕ) (a : Fin n) :
    ∃ m : Fin n → ℕ, ∑ i, m i = 2 ^ r ∧ seq x mv r a = (∑ i, (m i : ℚ) * x i) / 2 ^ r := by
  induction r generalizing a with
  | zero =>
    refine ⟨fun i => if i = a then 1 else 0, by simp, ?_⟩
    simp [seq]
  | succ r ih =>
    by_cases h : a = (mv r).1 ∨ a = (mv r).2
    · obtain ⟨m₁, hs₁, he₁⟩ := ih (mv r).1
      obtain ⟨m₂, hs₂, he₂⟩ := ih (mv r).2
      refine ⟨m₁ + m₂, by simp [sum_add_distrib, hs₁, hs₂, pow_succ]; ring, ?_⟩
      simp only [seq, avg, h, ↓reduceIte, he₁, he₂, Pi.add_apply, Nat.cast_add, add_mul, sum_add_distrib]
      field_simp
      ring
    · obtain ⟨m, hs, he⟩ := ih a
      refine ⟨fun i => 2 * m i, by rw [← mul_sum, hs, pow_succ]; ring, ?_⟩
      simp only [seq, avg, h, ↓reduceIte, he, Nat.cast_mul, Nat.cast_ofNat, mul_assoc, ← mul_sum]
      field_simp
      ring

/-- Moves commute with affine maps. -/
theorem affine (x : Fin n → ℚ) (mv : ℕ → Fin n × Fin n) (c d : ℚ) (r : ℕ) (a : Fin n) :
    seq (fun i => c * x i + d) mv r a = c * seq x mv r a + d := by
  induction r generalizing a with
  | zero => rfl
  | succ r ih =>
    simp only [seq, avg]
    split_ifs <;> simp only [ih] <;> ring1

/-- A move preserves the sum. -/
theorem sum_avg (u : Fin n → ℚ) (p : Fin n × Fin n) : ∑ a, avg u p a = ∑ a, u a := by
  obtain ⟨i, j⟩ := p
  by_cases hij : i = j
  · subst hij
    refine sum_congr rfl fun a _ => ?_
    simp only [avg, or_self]
    split_ifs with h
    · subst h; ring
    · rfl
  · have key : ∀ a, avg u (i, j) a = u a + (if a = i then (u j - u i) / 2 else 0)
        + (if a = j then (u i - u j) / 2 else 0) := by
      intro a
      simp only [avg]
      by_cases hi : a = i
      · subst hi; simp [hij]; ring
      · by_cases hj : a = j
        · subst hj; simp [hi]; ring
        · simp [hi, hj]
    simp only [key, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
    ring

/-- Moves preserve the sum. -/
theorem sum_seq (x : Fin n → ℚ) (mv : ℕ → Fin n × Fin n) (r : ℕ) :
    ∑ a, seq x mv r a = ∑ a, x a := by
  induction r with
  | zero => rfl
  | succ r ih => rw [seq, sum_avg, ih]

/-- The set of entries equal to `μ`. -/
def hits (u : Fin n → ℚ) (μ : ℚ) : Finset (Fin n) := univ.filter (fun a => u a = μ)

/-- In one move the number of entries equal to `μ` does not grow, or grows by exactly two. -/
theorem count_step (u : Fin n → ℚ) (p : Fin n × Fin n) (μ : ℚ) :
    (hits (avg u p) μ).card ≤ (hits u μ).card ∨ (hits (avg u p) μ).card = (hits u μ).card + 2 := by
  obtain ⟨i, j⟩ := p
  by_cases hij : i = j
  · subst hij
    left
    apply le_of_eq
    congr 1
    ext a
    simp only [hits, mem_filter, mem_univ, true_and, avg, or_self]
    split_ifs with h
    · subst h; constructor <;> intro h' <;> linarith
    · rfl
  by_cases hm : (u i + u j) / 2 = μ
  · by_cases hi : u i = μ
    · -- then u j = μ too, and nothing changes
      have hj : u j = μ := by linarith
      left
      apply le_of_eq
      congr 1
      ext a
      simp only [hits, mem_filter, mem_univ, true_and, avg]
      split_ifs with h
      · rcases h with rfl | rfl <;> simp [hi, hj]
      · rfl
    · have hj : u j ≠ μ := by intro hj; apply hi; linarith
      right
      have : hits (avg u (i, j)) μ = insert i (insert j (hits u μ)) := by
        ext a
        simp only [hits, mem_filter, mem_univ, true_and, mem_insert, avg]
        split_ifs with h
        · simp only [hm, true_iff]; tauto
        · push Not at h; simp [h.1, h.2]
      rw [this, card_insert_of_notMem, card_insert_of_notMem]
      · simp [hits, hj]
      · simp [hits, hi, hij]
  · left
    apply card_le_card
    intro a
    simp only [hits, mem_filter, mem_univ, true_and, avg]
    split_ifs with h
    · intro h'; exact absurd h' hm
    · exact id

/-- If the entries sum to `n μ`, then not exactly `n - 1` of them equal `μ`. -/
theorem count_ne_pred (hn : 1 ≤ n) (u : Fin n → ℚ) (μ : ℚ) (hsum : ∑ a, u a = n * μ) :
    (hits u μ).card ≠ n - 1 := by
  intro h
  have hc : (univ.filter (fun a => ¬ u a = μ)).card = 1 := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun a => u a = μ)
    simp only [card_univ, Fintype.card_fin] at this
    unfold hits at h
    omega
  obtain ⟨c, hc⟩ := card_eq_one.mp hc
  have hcmem : c ∈ univ.filter (fun a => ¬ u a = μ) := by rw [hc]; exact mem_singleton_self c
  have hcne : u c ≠ μ := (mem_filter.mp hcmem).2
  have split := sum_filter_add_sum_filter_not (univ : Finset (Fin n)) (fun a => u a = μ) u
  rw [hc, sum_singleton] at split
  have h1 : ∑ a ∈ univ.filter (fun a => u a = μ), u a = (n - 1 : ℕ) * μ := by
    rw [sum_congr rfl (fun a ha => (mem_filter.mp ha).2), sum_const, nsmul_eq_mul]
    unfold hits at h
    rw [h]
  apply hcne
  rw [hsum, h1, Nat.cast_sub hn] at split
  push_cast at split
  linarith

end General

section Five

/-- `t = (-1/2)^k`. -/
def t (k : ℕ) : ℚ := (-1 / 2) ^ k

/-- The five numbers `(2, -3, 1, 5t/2, 5t/2)`. -/
def B (k : ℕ) : Fin 5 → ℚ := ![2, -3, 1, 5 * t k / 2, 5 * t k / 2]

theorem sum_B (k : ℕ) : ∑ a, B k a = 5 * t k := by
  simp [B, Fin.sum_univ_five]; ring

/-- The arithmetic heart of the first-hit bound: for `r < k` and `0 ≤ q ≤ 2^r`, `2^(k+1)` does not divide
`5q - 2^(r+1)`. -/
theorem no_congruence {k r q : ℕ} (hr : r < k) (hq : q ≤ 2 ^ r)
    (hd : (2 : ℤ) ^ (k + 1) ∣ 5 * q - 2 ^ (r + 1)) : False := by
  have h1 : (2 : ℤ) ^ (r + 1) ∣ 2 ^ (k + 1) := pow_dvd_pow 2 (by omega)
  have h2 : (2 : ℤ) ^ (r + 1) ∣ 5 * q := by
    have := dvd_add (h1.trans hd) (dvd_refl ((2 : ℤ) ^ (r + 1)))
    simpa using this
  have h3 : (2 : ℤ) ^ (r + 1) ∣ q := by
    have hcop : IsCoprime ((2 : ℤ) ^ (r + 1)) 5 := by
      apply IsCoprime.pow_left
      rw [Int.isCoprime_iff_gcd_eq_one]; rfl
    exact hcop.dvd_of_dvd_mul_left h2
  have hq0 : q = 0 := by
    rcases Nat.eq_zero_or_pos q with h | h
    · exact h
    · exfalso
      have := Int.le_of_dvd (by exact_mod_cast h) h3
      have : (2 : ℤ) ^ (r + 1) ≤ 2 ^ r := le_trans this (by exact_mod_cast hq)
      have : (2 : ℤ) ^ r < 2 ^ (r + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
      omega
  subst hq0
  have : (2 : ℤ) ^ (k + 1) ∣ 2 ^ (r + 1) := by simpa using hd.neg_right
  have := Int.le_of_dvd (by positivity) this
  have : (2 : ℤ) ^ (r + 1) < 2 ^ (k + 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
  omega

/-- No entry equals the mean `t` before move `k`, whatever the strategy. -/
theorem no_mean_before (k : ℕ) (mv : ℕ → Fin 5 × Fin 5) {r : ℕ} (hr : r < k) (a : Fin 5) :
    seq (B k) mv r a ≠ t k := by
  intro h
  set E : ℚ := (-1) ^ k with hE
  have hNt : (2 : ℚ) ^ (k + 1) * t k = 2 * E := by
    rw [hE, t, pow_succ, mul_comm ((2 : ℚ) ^ k), mul_assoc, ← mul_pow]; norm_num
  have hε : E ^ 2 = 1 := by rw [hE, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hseq := affine (B k) mv (2 ^ (k + 1)) 0 r a
  rw [h] at hseq
  obtain ⟨m, hs, he⟩ := weights (fun i => 2 ^ (k + 1) * B k i + 0) mv r a
  rw [hseq, eq_div_iff (by positivity)] at he
  simp only [Fin.sum_univ_five, add_zero] at he
  have hB : ∀ i, B k i = ![2, -3, 1, 5 * t k / 2, 5 * t k / 2] i := fun _ => rfl
  simp only [hB, Matrix.cons_val] at he
  have he' : (2 : ℚ) ^ (k + 1) * (2 * m 0 - 3 * m 1 + m 2) + 5 * ((m 3 : ℚ) + m 4) * E
      = 2 * E * 2 ^ r := by
    linear_combination -he + (2 ^ r - (5 / 2) * ((m 3 : ℚ) + m 4)) * hNt
  have key : ((5 * ((m 3 : ℤ) + m 4) - 2 ^ (r + 1) : ℤ) : ℚ)
      = (((2 : ℤ) ^ (k + 1) * (-(-1) ^ k * (2 * m 0 - 3 * m 1 + m 2)) : ℤ) : ℚ) := by
    push_cast
    rw [← hE]
    linear_combination E * he' - (5 * ((m 3 : ℚ) + m 4) - 2 * 2 ^ r) * hε
  have hq : m 3 + m 4 ≤ 2 ^ r := by
    rw [← hs, Fin.sum_univ_five]; omega
  exact no_congruence hr (q := m 3 + m 4) hq ⟨_, by push_cast; exact_mod_cast key⟩

/-- Every strategy that makes all five entries equal uses at least `k + 3` moves. -/
theorem lower_bound (k : ℕ) (hk : 1 ≤ k) (mv : ℕ → Fin 5 × Fin 5) (R : ℕ)
    (hR : ∀ a, seq (B k) mv R a = t k) : k + 3 ≤ R := by
  set M : ℕ → ℕ := fun r => (hits (seq (B k) mv r) (t k)).card with hM
  have hsum : ∀ r, ∑ a, seq (B k) mv r a = (5 : ℕ) * t k := by
    intro r; rw [sum_seq, sum_B]; norm_num
  have hne4 : ∀ r, M r ≠ 4 := fun r => count_ne_pred (by norm_num) _ _ (hsum r)
  have hstep : ∀ r, M (r + 1) ≤ M r ∨ M (r + 1) = M r + 2 := fun r => count_step _ _ _
  have hMR : M R = 5 := by
    simp only [hM, hits]
    rw [filter_true_of_mem (fun a _ => hR a)]; rfl
  have hex : ∃ r, 0 < M r := ⟨R, by omega⟩
  classical
  let r₀ := Nat.find hex
  have hr₀ : 0 < M r₀ := Nat.find_spec hex
  have hbefore : ∀ r < r₀, M r = 0 := fun r hr => by
    have := Nat.find_min hex hr; omega
  have hkr₀ : k ≤ r₀ := by
    by_contra hlt
    push Not at hlt
    obtain ⟨a, ha⟩ := card_pos.mp hr₀
    exact no_mean_before k mv hlt a (mem_filter.mp ha).2
  have hR₀ : r₀ ≤ R := Nat.find_min' hex (by omega)
  -- M(r₀) = 2
  have hM0 : r₀ ≠ 0 := by omega
  obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero hM0
  have hMs : M s = 0 := hbefore s (by omega)
  have hMr₀ : M r₀ = 2 := by
    have := hstep s; rw [show s + 1 = r₀ from hs.symm] at this; omega
  have h1 : M (r₀ + 1) ≤ 2 := by have := hstep r₀; have := hne4 (r₀ + 1); omega
  have h2 : M (r₀ + 2) ≤ 3 := by
    have := hstep (r₀ + 1); have := hne4 (r₀ + 2); rw [show r₀ + 1 + 1 = r₀ + 2 from rfl] at *; omega
  have : R ≠ r₀ := by intro h; rw [h] at hMR; omega
  have : R ≠ r₀ + 1 := by intro h; rw [h] at hMR; omega
  have : R ≠ r₀ + 2 := by intro h; rw [h] at hMR; omega
  omega

/-- The strategy: average entries 0 and 1; then `k` times average the odd one out of the first three entries with
entry 0; then entries 0 and 3, and the remaining copy of `-t/2` with entry 4. -/
def sing (m : ℕ) : Fin 5 := if Even m then 1 else 2

def strategy (k : ℕ) : ℕ → Fin 5 × Fin 5 := fun m =>
  if m = 0 then (0, 1) else if m ≤ k then (sing m, 0) else if m = k + 1 then (0, 3) else (sing k, 4)

/-- The shape `(s, s, -2s)` of the first three entries, with `s = (-1/2)^m`, after `m` moves, `1 ≤ m ≤ k + 1`. -/
theorem triple (k : ℕ) {m : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k + 1) :
    seq (B k) (strategy k) m = ![(-1 / 2) ^ m, if Even m then -2 * (-1 / 2) ^ m else (-1 / 2) ^ m,
      if Even m then (-1 / 2) ^ m else -2 * (-1 / 2) ^ m, 5 * t k / 2, 5 * t k / 2] := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · funext a
      fin_cases a <;> simp [seq, strategy, avg, B] <;> try norm_num
    · rw [seq, ih hm (by omega)]
      have hs : strategy k m = (sing m, 0) := by
        simp [strategy, show m ≠ 0 by omega, show m ≤ k by omega]
      rw [hs]
      funext a
      rcases Nat.even_or_odd m with he | ho
      · have hn : ¬ Even (m + 1) := by simpa [Nat.even_add_one] using he
        fin_cases a <;> (simp [avg, sing, he, hn, pow_succ]; try ring1)
      · have hn : Even (m + 1) := by simpa [Nat.even_add_one, Nat.not_even_iff_odd] using ho
        have hne : ¬ Even m := Nat.not_even_iff_odd.mpr ho
        fin_cases a <;> (simp [avg, sing, hne, hn, pow_succ]; try ring1)

/-- `k + 3` moves suffice. -/
theorem upper_bound (k : ℕ) (hk : 1 ≤ k) : ∀ a, seq (B k) (strategy k) (k + 3) a = t k := by
  have h := triple k (m := k + 1) (by omega) le_rfl
  have s1 : strategy k (k + 1) = (0, 3) := by simp [strategy]
  have s2 : strategy k (k + 2) = (sing k, 4) := by simp [strategy]
  intro a
  show avg (avg (seq (B k) (strategy k) (k + 1)) (strategy k (k + 1))) (strategy k (k + 2)) a = t k
  rw [h, s1, s2]
  rcases Nat.even_or_odd k with he | ho
  · have hn : ¬ Even (k + 1) := by simpa [Nat.even_add_one] using he
    fin_cases a <;> (simp [avg, sing, he, hn, t, pow_succ]; try ring1)
  · have hn : Even (k + 1) := by simpa [Nat.even_add_one, Nat.not_even_iff_odd] using ho
    have hne : ¬ Even k := Nat.not_even_iff_odd.mpr ho
    fin_cases a <;> (simp [avg, sing, hne, hn, t, pow_succ]; try ring1)

/-- The least number of moves is exactly `k + 3`. -/
theorem optimum (k : ℕ) (hk : 1 ≤ k) :
    (∃ mv : ℕ → Fin 5 × Fin 5, ∀ a, seq (B k) mv (k + 3) a = t k) ∧
    ∀ (mv : ℕ → Fin 5 × Fin 5) (R : ℕ), (∀ a, seq (B k) mv R a = t k) → k + 3 ≤ R :=
  ⟨⟨strategy k, upper_bound k hk⟩, fun mv R hR => lower_bound k hk mv R hR⟩

/-- The nonnegative integer version `(5N, 0, 4N, 3N + 5ε, 3N + 5ε)`, `N = 2^(k+1)`, `ε = (-1)^k`, is the affine
image `N x + 3N` of `B_k`, with mean `3N + 2ε`. -/
theorem integer_version (k : ℕ) (i : Fin 5) :
    (2 : ℚ) ^ (k + 1) * B k i + 3 * 2 ^ (k + 1) =
      ![5 * 2 ^ (k + 1), 0, 4 * 2 ^ (k + 1), 3 * 2 ^ (k + 1) + 5 * (-1) ^ k, 3 * 2 ^ (k + 1) + 5 * (-1) ^ k] i := by
  have : (2 : ℚ) ^ (k + 1) * t k = 2 * (-1) ^ k := by
    simp only [t]; rw [pow_succ, mul_comm ((2 : ℚ) ^ k), mul_assoc, ← mul_pow]; norm_num
  fin_cases i <;> simp [B] <;> first | ring1 | linear_combination (5 / 2 : ℚ) * this

/-- For `k ≥ 2` no nonempty proper subset of `B_k` has mean `t`. -/
theorem no_balanced_subset (k : ℕ) (hk : 2 ≤ k) (S : Finset (Fin 5)) (hS : S.Nonempty) (hSu : S ≠ univ) :
    ∑ i ∈ S, B k i ≠ S.card * t k := by
  have ht0 : t k ≠ 0 := by simp [t]
  have hlo : -1 / 8 ≤ t k := by
    simp only [t]
    rw [show (-1 / 2 : ℚ) = -(1 / 2) by norm_num]
    rcases Nat.even_or_odd k with he | ho
    · rw [he.neg_pow]; linarith [show (0 : ℚ) ≤ (1 / 2) ^ k by positivity]
    · rw [ho.neg_pow]
      have : (1 / 2 : ℚ) ^ k ≤ (1 / 2) ^ 3 := pow_le_pow_of_le_one (by norm_num) (by norm_num)
        (by rcases ho with ⟨j, rfl⟩; omega)
      linarith
  have hhi : t k ≤ 1 / 4 := by
    simp only [t]
    calc ((-1 / 2) : ℚ) ^ k ≤ |(-1 / 2 : ℚ) ^ k| := le_abs_self _
      _ = (1 / 2) ^ k := by rw [abs_pow]; norm_num
      _ ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      _ = 1 / 4 := by norm_num
  intro h
  rcases lt_or_gt_of_ne ht0 with hneg | hpos
  · fin_cases S <;> first | exact absurd (by decide) hSu | (simp_all [B]; try linarith)
  · fin_cases S <;> first | exact absurd (by decide) hSu | (simp_all [B]; try linarith)

end Five

end PairwiseAveraging
