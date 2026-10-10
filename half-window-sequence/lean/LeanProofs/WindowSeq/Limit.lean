import LeanProofs.WindowSeq.Harm

/-!
# Half a window: `n a n → 1/(1 - log 2)` (Theorem 1)

With `A = 1/(1 - log 2)`, so that `A = 1 + A log 2`, and `e n = c n - A`, the window identity gives
`e n = ∑_{k ∈ W n} e k / k + A (s n - log 2)`, hence
`|e n| ≤ s n · max_{W n} |e k| + A |s n - log 2|`.
* `c_bdd`: `c` is bounded (eventually `s n ≤ 3/4`, so `c n ≤ 1 + (3/4) max` cannot run away);
* `tendsto_zero_of_contract`: a bounded sequence with `|e n| ≤ q R + δ n` whenever `|e| ≤ R` on the
  window, `q < 1`, `δ → 0`, tends to `0` (iterate: eventually `|e n| ≤ qʲ M + η/(1-q)` for every `j`);
* `tendsto_c`: Theorem 1.
-/

open Finset Filter Topology Real

namespace WindowSeq

/-- The limit `A = 1/(1 - log 2)`. -/
noncomputable def A : ℝ := 1 / (1 - log 2)

lemma log_two_lt : log 2 < 7 / 10 := by
  have := Real.log_two_lt_d9; norm_num at this ⊢; linarith

lemma one_sub_log_two_pos : 0 < 1 - log 2 := by linarith [log_two_lt]

lemma A_pos : 0 < A := by unfold A; exact div_pos one_pos one_sub_log_two_pos

lemma A_fixed : A = 1 + A * log 2 := by
  unfold A; have := one_sub_log_two_pos; field_simp; ring

lemma s_nonneg (n : ℕ) : 0 ≤ s n := Finset.sum_nonneg fun k _ => by positivity

lemma eventually_s_le : ∀ᶠ n in atTop, s n ≤ 3 / 4 :=
  tendsto_s.eventually (eventually_le_nhds (by linarith [log_two_lt]))

lemma c_nonneg (n : ℕ) : 0 ≤ c n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [c]
  · exact (zero_le_one.trans (one_le_c n hn))

/-- One step of the window identity as an inequality. -/
lemma c_le_of {n : ℕ} (hn : 1 ≤ n) {R : ℝ} (hR : ∀ k ∈ W n, c k ≤ R) : c n ≤ 1 + s n * R := by
  rw [window_c n hn, s, Finset.sum_mul]
  gcongr with k hk
  obtain ⟨h1, h2⟩ := mem_W hk
  have hk0 : (0 : ℝ) < k := by have : 1 ≤ k := by omega
                               exact_mod_cast this
  rw [one_div_mul_eq_div]
  exact div_le_div_of_nonneg_right (hR k hk) hk0.le

/-- `c` is bounded. -/
theorem c_bdd : ∃ B, ∀ n, c n ≤ B := by
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 eventually_s_le
  set B := max 4 (∑ m ∈ range (N0 + 1), c m) with hB
  refine ⟨B, fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n ≤ N0
    · have := Finset.single_le_sum (f := c) (fun m _ => c_nonneg m)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hn))
      exact this.trans (le_max_right _ _)
    · have h1 : 1 ≤ n := by omega
      have hle := c_le_of h1 (R := B) fun k hk => ih k (mem_W hk).2
      have hs := hN0 n (by omega)
      have hB4 : 4 ≤ B := le_max_left _ _
      nlinarith [s_nonneg n]

/-- A contraction over windows forces convergence to `0`. -/
theorem tendsto_zero_of_contract (e δ : ℕ → ℝ) (M q : ℝ) (hq0 : 0 ≤ q) (hq : q < 1)
    (hM : ∀ n, |e n| ≤ M) (hδ : Tendsto δ atTop (𝓝 0)) (N0 : ℕ)
    (h : ∀ n ≥ N0, ∀ R, 0 ≤ R → (∀ k ∈ W n, |e k| ≤ R) → |e n| ≤ q * R + δ n) :
    Tendsto e atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have h1q : 0 < 1 - q := by linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := (1 - q) * ε / 2 with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hδ.eventually (eventually_le_nhds hηpos))
  have claim : ∀ j : ℕ, ∃ N, ∀ n ≥ N, |e n| ≤ q ^ j * M + η / (1 - q) := by
    intro j
    induction j with
    | zero =>
      refine ⟨0, fun n _ => ?_⟩
      have : 0 ≤ η / (1 - q) := by positivity
      simp only [pow_zero, one_mul]; linarith [hM n]
    | succ j ihj =>
      obtain ⟨N, hN⟩ := ihj
      refine ⟨max (2 * N + 1) (max N0 N1), fun n hn => ?_⟩
      have hw : ∀ k ∈ W n, |e k| ≤ q ^ j * M + η / (1 - q) := fun k hk => by
        have := (mem_W hk).1
        exact hN k (by omega)
      have hR0 : 0 ≤ q ^ j * M + η / (1 - q) := by positivity
      have hstep := h n (by omega) _ hR0 hw
      have hδn := hN1 n (by omega)
      have key : q * (q ^ j * M + η / (1 - q)) + η = q ^ (j + 1) * M + η / (1 - q) := by
        field_simp; ring
      linarith
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (2 * (M + 1)) by positivity) hq
  obtain ⟨N, hN⟩ := claim j
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  have hqj : 0 ≤ q ^ j := pow_nonneg hq0 j
  have h1 : q ^ j * M ≤ q ^ j * (M + 1) := by nlinarith
  have h2 : q ^ j * (M + 1) < ε / 2 := by
    have hM1 : 0 < M + 1 := by linarith
    calc q ^ j * (M + 1) < ε / (2 * (M + 1)) * (M + 1) := mul_lt_mul_of_pos_right hj hM1
      _ = ε / 2 := by field_simp
  have h3 : η / (1 - q) = ε / 2 := by rw [hη]; field_simp
  linarith [hN n hn]

/-- The error identity: `c n - A = ∑_{k ∈ W n} (c k - A)/k + A (s n - log 2)`. -/
lemma error_eq {n : ℕ} (hn : 1 ≤ n) :
    c n - A = ∑ k ∈ W n, (c k - A) / k + A * (s n - log 2) := by
  rw [window_c n hn, s]
  have hsum : ∑ k ∈ W n, (c k - A) / k = ∑ k ∈ W n, c k / k - A * ∑ k ∈ W n, (1 : ℝ) / k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => by ring
  rw [hsum]
  have := A_fixed
  linarith

/-- Theorem 1: `n a n → 1/(1 - log 2)`. -/
theorem tendsto_c : Tendsto (fun n : ℕ => (n : ℝ) * a n) atTop (𝓝 (1 / (1 - log 2))) := by
  obtain ⟨B, hB⟩ := c_bdd
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 eventually_s_le
  set e : ℕ → ℝ := fun n => c n - A
  have hM : ∀ n, |e n| ≤ B + A := fun n => by
    have h0 := c_nonneg n
    have hb := hB n
    have hA := A_pos
    rw [abs_le]; constructor <;> simp only [e] <;> linarith
  have hδ : Tendsto (fun n => A * |s n - log 2|) atTop (𝓝 0) := by
    have := ((tendsto_s.sub_const (log 2)).abs).const_mul A
    simpa using this
  have hcon := tendsto_zero_of_contract e (fun n => A * |s n - log 2|) (B + A) (3 / 4)
    (by norm_num) (by norm_num) hM hδ (max N0 1) (fun n hn R hR hw => by
      have hn1 : 1 ≤ n := le_of_max_le_right hn
      have hs := hN0 n (le_of_max_le_left hn)
      simp only [e]
      rw [error_eq hn1]
      calc |∑ k ∈ W n, (c k - A) / k + A * (s n - log 2)|
          ≤ |∑ k ∈ W n, (c k - A) / k| + |A * (s n - log 2)| := abs_add_le _ _
        _ ≤ ∑ k ∈ W n, |c k - A| / k + A * |s n - log 2| := by
            gcongr
            · exact (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl
                fun k _ => by rw [abs_div, Nat.abs_cast]))
            · rw [abs_mul, abs_of_pos A_pos]
        _ ≤ ∑ k ∈ W n, R / k + A * |s n - log 2| := by
            gcongr with k hk
            exact hw k hk
        _ = s n * R + A * |s n - log 2| := by
            rw [s, Finset.sum_mul]; congr 1
            exact Finset.sum_congr rfl fun k _ => by ring
        _ ≤ 3 / 4 * R + A * |s n - log 2| := by gcongr)
  have := hcon.add_const A
  simp only [e, sub_add_cancel, zero_add] at this
  unfold A at this
  exact this.congr fun n => rfl

end WindowSeq
