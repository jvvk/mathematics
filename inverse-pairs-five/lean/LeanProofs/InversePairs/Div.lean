import Mathlib

/-!
# Inverse pairs: the divisor bound (used in Lemma 3)

`divisor_bound`: for every `ε > 0` there is `D` with `d(n) ≤ D n^ε` for all `n ≥ 1`. With
`n = ∏ q^e`, `d(n) = ∏ (e + 1)`; each factor is at most `c (q^ε)^e` with `c = 1 + 1/(ε log 2)`
(`succ_le`), and at most `(q^ε)^e` once `q^ε ≥ 2`, which leaves fewer than `2^(1/ε) + 1` primes
paying the factor `c`.
-/

open Finset Real

namespace InversePairs

lemma succ_le (ε : ℝ) (hε : 0 < ε) (q : ℕ) (hq : 2 ≤ q) (e : ℕ) :
    (e + 1 : ℝ) ≤ (1 + 1 / (ε * log 2)) * ((q : ℝ) ^ ε) ^ e := by
  have hl : 0 < log 2 := log_pos one_lt_two
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have h1 : (1 : ℝ) ≤ ((q : ℝ) ^ ε) ^ e := one_le_pow₀ (one_le_rpow hq1 hε.le)
  have h2 : (e : ℝ) * ε * log 2 + 1 ≤ ((q : ℝ) ^ ε) ^ e := by
    calc (e : ℝ) * ε * log 2 + 1 ≤ exp (e * ε * log 2) := add_one_le_exp _
      _ = ((2 : ℝ) ^ ε) ^ e := by
          rw [← rpow_natCast, ← rpow_mul (by norm_num), rpow_def_of_pos (by norm_num)]; ring_nf
      _ ≤ ((q : ℝ) ^ ε) ^ e := by
          gcongr; exact_mod_cast hq
  have h3 : (e : ℝ) ≤ (((q : ℝ) ^ ε) ^ e - 1) / (ε * log 2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have h4 : (((q : ℝ) ^ ε) ^ e - 1) / (ε * log 2) ≤ ((q : ℝ) ^ ε) ^ e / (ε * log 2) :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  calc (e + 1 : ℝ) ≤ ((q : ℝ) ^ ε) ^ e / (ε * log 2) + ((q : ℝ) ^ ε) ^ e := by linarith
    _ = _ := by ring

/-- The divisor bound `d(n) ≤ D n^ε`. -/
theorem divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, n ≠ 0 → (#n.divisors : ℝ) ≤ D * (n : ℝ) ^ ε := by
  set c : ℝ := 1 + 1 / (ε * log 2) with hc
  have hl : 0 < log 2 := log_pos one_lt_two
  have hc1 : 1 ≤ c := by rw [hc]; have : 0 < 1 / (ε * log 2) := by positivity
                         linarith
  set M := ⌈(2 : ℝ) ^ (1 / ε)⌉₊
  refine ⟨c ^ M, by positivity, fun n hn => ?_⟩
  rw [Nat.card_divisors hn]
  push_cast
  have hnε : (n : ℝ) ^ ε = ∏ q ∈ n.primeFactors, ((q : ℝ) ^ ε) ^ (n.factorization q) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    push_cast
    rw [← Real.finsetProd_rpow _ _ (fun q _ => by positivity)]
    refine prod_congr rfl fun q _ => ?_
    rw [← rpow_natCast, ← rpow_natCast, ← rpow_mul (by positivity), ← rpow_mul (by positivity),
      mul_comm]
  rw [hnε]
  have hfac : ∀ q ∈ n.primeFactors, ((n.factorization q : ℝ) + 1) ≤
      (if q < M then c else 1) * ((q : ℝ) ^ ε) ^ (n.factorization q) := fun q hq => by
    have hq2 : 2 ≤ q := (Nat.prime_of_mem_primeFactors hq).two_le
    split_ifs with hM
    · exact succ_le ε hε q hq2 _
    · have hMq : (2 : ℝ) ^ (1 / ε) ≤ q :=
        (Nat.le_ceil _).trans (by exact_mod_cast (not_lt.1 hM))
      have hqε : 2 ≤ (q : ℝ) ^ ε := by
        calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
              rw [← rpow_mul (by norm_num), one_div_mul_cancel hε.ne', rpow_one]
          _ ≤ (q : ℝ) ^ ε := rpow_le_rpow (by positivity) hMq hε.le
      have hpow : (n.factorization q : ℝ) + 1 ≤ 2 ^ (n.factorization q) := by
        exact_mod_cast Nat.lt_two_pow_self
      calc (n.factorization q : ℝ) + 1 ≤ 2 ^ (n.factorization q) := hpow
        _ ≤ ((q : ℝ) ^ ε) ^ (n.factorization q) := pow_le_pow_left₀ (by norm_num) hqε _
        _ = 1 * ((q : ℝ) ^ ε) ^ (n.factorization q) := by ring
  calc ∏ q ∈ n.primeFactors, ((n.factorization q : ℝ) + 1)
      ≤ ∏ q ∈ n.primeFactors, ((if q < M then c else 1) * ((q : ℝ) ^ ε) ^ (n.factorization q)) :=
        prod_le_prod₀ (fun _ _ => by positivity) hfac
    _ = (∏ q ∈ n.primeFactors, (if q < M then c else 1)) *
          ∏ q ∈ n.primeFactors, ((q : ℝ) ^ ε) ^ (n.factorization q) := prod_mul_distrib
    _ ≤ c ^ M * ∏ q ∈ n.primeFactors, ((q : ℝ) ^ ε) ^ (n.factorization q) := by
        gcongr
        rw [prod_ite, prod_const, prod_const_one, mul_one]
        refine pow_le_pow_right₀ hc1 ?_
        calc #(n.primeFactors.filter (· < M)) ≤ #(range M) :=
              card_le_card fun q hq => mem_range.2 (mem_filter.1 hq).2
          _ = M := card_range M

end InversePairs
