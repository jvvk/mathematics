import LeanProofs.WindowSeq.Seq

/-!
# Half a window: the window weights tend to `log 2` (Lemma 2)

`s n = ∑_{k ∈ W n} 1/k`. With `N = n - 1` and `t = ⌈n/2⌉ - 1` the window is `[t + 1, N]`, so
`s n = H_N - H_t = (H_N - log N) - (H_t - log t) + log (N / 2t) + log 2`. The first two brackets both
tend to Euler's constant (`Real.tendsto_harmonic_sub_log`), and `2t ≤ N ≤ 2t + 1` squeezes the third to `0`.
-/

open Finset Filter Topology Real

namespace WindowSeq

/-- The total weight `s n = ∑_{k ∈ W n} 1/k` of the window. -/
noncomputable def s (n : ℕ) : ℝ := ∑ k ∈ W n, (1 : ℝ) / k

lemma harmonic_real (n : ℕ) : (harmonic n : ℝ) = ∑ k ∈ Ico 1 (n + 1), (1 : ℝ) / k := by
  rw [harmonic_eq_sum_Icc]; push_cast
  rw [show Icc 1 n = Ico 1 (n + 1) by ext; simp]; simp [one_div]

lemma s_eq (n : ℕ) (hn : 2 ≤ n) :
    s n = (harmonic (n - 1) : ℝ) - harmonic ((n + 1) / 2 - 1) := by
  rw [harmonic_real, harmonic_real, s, W, eq_sub_iff_add_eq, add_comm]
  rw [show (n + 1) / 2 - 1 + 1 = (n + 1) / 2 by omega, show n - 1 + 1 = n by omega]
  exact Finset.sum_Ico_consecutive _ (by omega) (by omega)

/-- `N n = n - 1` and `t n = ⌈n/2⌉ - 1` both tend to infinity. -/
lemma tendsto_N : Tendsto (fun n : ℕ => n - 1) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨b + 1, fun n hn => by omega⟩

lemma tendsto_t : Tendsto (fun n : ℕ => (n + 1) / 2 - 1) atTop atTop :=
  tendsto_atTop_atTop.2 fun b => ⟨2 * b + 3, fun n hn => by omega⟩

/-- Lemma 2: `s n → log 2`. -/
theorem tendsto_s : Tendsto s atTop (𝓝 (log 2)) := by
  set N : ℕ → ℕ := fun n => n - 1
  set t : ℕ → ℕ := fun n => (n + 1) / 2 - 1
  have h1 := (tendsto_harmonic_sub_log.comp tendsto_N)
  have h2 := (tendsto_harmonic_sub_log.comp tendsto_t)
  -- the logarithm of the ratio `N / 2t` tends to `0`
  have hr : Tendsto (fun n : ℕ => log (N n) - log (2 * (t n : ℝ))) atTop (𝓝 0) := by
    have hup : Tendsto (fun n : ℕ => 1 / (2 * (t n : ℝ))) atTop (𝓝 0) := by
      have := (tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_t
      have h2t : Tendsto (fun n : ℕ => 2 * (t n : ℝ)) atTop atTop :=
        Tendsto.const_mul_atTop (by norm_num) this
      exact h2t.inv_tendsto_atTop.congr fun n => by simp [one_div]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop 4] with n hn
      have ht : 0 < (t n : ℝ) := by simp only [t]; exact_mod_cast (by omega : 0 < (n + 1) / 2 - 1)
      have hle : 2 * (t n : ℝ) ≤ N n := by
        simp only [t, N]; exact_mod_cast (by omega : 2 * ((n + 1) / 2 - 1) ≤ n - 1)
      exact sub_nonneg.2 (log_le_log (by positivity) hle)
    · filter_upwards [eventually_ge_atTop 4] with n hn
      have ht : 0 < (t n : ℝ) := by simp only [t]; exact_mod_cast (by omega : 0 < (n + 1) / 2 - 1)
      have hle : (N n : ℝ) ≤ 2 * t n + 1 := by
        simp only [t, N]; exact_mod_cast (by omega : n - 1 ≤ 2 * ((n + 1) / 2 - 1) + 1)
      have hNpos : 0 < (N n : ℝ) := by simp only [N]; exact_mod_cast (by omega : 0 < n - 1)
      calc log (N n) - log (2 * t n) ≤ log (2 * t n + 1) - log (2 * t n) := by
            gcongr
        _ = log (1 + 1 / (2 * t n)) := by
            rw [← log_div (by positivity) (by positivity)]
            congr 1; field_simp
        _ ≤ 1 / (2 * t n) := by
            have := log_le_sub_one_of_pos (show 0 < 1 + 1 / (2 * (t n : ℝ)) by positivity)
            linarith
  have hsum := ((h1.sub h2).add hr).add_const (log 2)
  rw [sub_self, add_zero, zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 4] with n hn
  have ht : 0 < (t n : ℝ) := by simp only [t]; exact_mod_cast (by omega : 0 < (n + 1) / 2 - 1)
  simp only [Function.comp, s_eq n (by omega), N, t]
  rw [log_mul (by norm_num) ht.ne']
  ring

end WindowSeq
