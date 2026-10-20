import Mathlib

/-!
# Proposition 2: front shape is a first-order invariant of rhombic phases

The cancellation argument of `open-questions/sunflower-phyllotaxis/PROOF_prop2.md`, with explicit
constants, by a matching simpler than the cycle regrouping of the notes: pair the `k`-th pass of up
`u`
with the `(k + δ)`-th pass of up `v`, where `δ` is the offset of their cyclic sweeps. Paired passes
meet
the same down, at times at most `3nm` apart, so their phases differ by at most `3nmε`; the unpaired
passes
number at most `3m`.

Inputs (each supplied elsewhere):
* phases `f d t` (the factor `e^{iβ_d(t)}` of down `d` at step `t`): `‖f d t‖ ≤ 1` and Lipschitz in
  `t`
  with constant `ε = O(|c|)` (Lemma 1: every vector changes by `O(c)` per step);
* the cyclic sweep (`du k ≡ αu - k mod m`): item (d) of the notes;
* bounded lag `|n k - t_k| ≤ n m` and pass balance `|K_u - K_v| ≤ m`: `PassBalance.pass_lag`,
  `PassBalance.pass_balance`;
* per-pass factors `1 + i c f + r` with `‖r‖ ≤ R c²` (Lemma 1, uniform remainder).

* `sum_decomp`: exact splitting of `∑ a - ∑ b` into matched pairs and three leftover windows.
* `matched_sum_bound`: `‖∑_{k<K_u} a_k - ∑_{k<K_v} b_k‖ ≤ K_u η + 3m`.
* `sweep_offset`: two cyclic sweeps over the same `m` downs agree after a shift `δ < m`.
* `prop2`: the accumulated log factors of two ups differ by at most
  `|c| (3 n m ε K_u + 3m) + (K_u + K_v) e(c)`, `e(c) = (|c| + R c²)² + R c²` (for
  `|c| + R c² ≤ 1/2`).
  With `K_u ≈ L/n` and `ε = O(|c|)` this is `O_{m,n}(|c| + c² L)`.
-/

namespace Phyllotaxis.Prop2

open Finset Complex

/-- Exact decomposition: `a k` is paired with `b (k + δ)` for `k < K`. -/
theorem sum_decomp (a b : ℕ → ℂ) {K Ku Kv δ : ℕ} (h1 : K ≤ Ku) (h2 : K + δ ≤ Kv) :
    ∑ k ∈ range Ku, a k - ∑ k ∈ range Kv, b k =
      ∑ k ∈ range K, (a k - b (k + δ)) + ∑ k ∈ Ico K Ku, a k - ∑ j ∈ range δ, b j -
        ∑ j ∈ Ico (K + δ) Kv, b j := by
  rw [← sum_range_add_sum_Ico a h1, ← sum_range_add_sum_Ico b h2, add_comm K δ, sum_range_add,
    sum_sub_distrib]
  have : ∑ k ∈ range K, b (k + δ) = ∑ x ∈ range K, b (δ + x) :=
    sum_congr rfl fun k _ => by rw [add_comm]
  rw [this]
  ring

theorem norm_sum_le_card {s : Finset ℕ} {f : ℕ → ℂ} (hf : ∀ k, ‖f k‖ ≤ 1) :
    ‖∑ k ∈ s, f k‖ ≤ s.card := by
  calc ‖∑ k ∈ s, f k‖ ≤ ∑ k ∈ s, ‖f k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ s, (1 : ℝ) := sum_le_sum fun k _ => hf k
    _ = s.card := by simp

/-- **Matched sums.** If `a k` and `b (k + δ)` are within `η` whenever both are passes, then
`‖∑_{k<K_u} a_k - ∑_{k<K_v} b_k‖ ≤ K_u η + 3m` (given `δ < m`, `|K_u - K_v| ≤ m`). -/
theorem matched_sum_bound {a b : ℕ → ℂ} (ha : ∀ k, ‖a k‖ ≤ 1) (hb : ∀ k, ‖b k‖ ≤ 1)
    {Ku Kv δ m : ℕ} {η : ℝ} (hη : 0 ≤ η) (hδ : δ < m) (hbal : Ku ≤ Kv + m ∧ Kv ≤ Ku + m)
    (hmatch : ∀ k, k < Ku → k + δ < Kv → ‖a k - b (k + δ)‖ ≤ η) :
    ‖∑ k ∈ range Ku, a k - ∑ k ∈ range Kv, b k‖ ≤ Ku * η + 3 * m := by
  by_cases hK : δ ≤ Kv
  · set K := min Ku (Kv - δ) with hKdef
    have h1 : K ≤ Ku := min_le_left _ _
    have h2 : K + δ ≤ Kv := by omega
    rw [sum_decomp a b h1 h2]
    have hpair : ‖∑ k ∈ range K, (a k - b (k + δ))‖ ≤ K * η := by
      calc ‖∑ k ∈ range K, (a k - b (k + δ))‖ ≤ ∑ k ∈ range K, ‖a k - b (k + δ)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _k ∈ range K, η := sum_le_sum fun k hk => by
            rw [mem_range] at hk
            exact hmatch k (by omega) (by omega)
        _ = K * η := by simp
    have e1 := norm_sum_le_card (s := Ico K Ku) ha
    have e2 := norm_sum_le_card (s := range δ) hb
    have e3 := norm_sum_le_card (s := Ico (K + δ) Kv) hb
    simp only [Nat.card_Ico, card_range] at e1 e2 e3
    have hc : ((Ku - K : ℕ) : ℝ) + δ + ((Kv - (K + δ) : ℕ) : ℝ) ≤ 3 * m := by
      have : Ku - K + δ + (Kv - (K + δ)) ≤ 3 * m := by omega
      exact_mod_cast this
    have hKη : (K : ℝ) * η ≤ Ku * η := by gcongr
    calc ‖∑ k ∈ range K, (a k - b (k + δ)) + ∑ k ∈ Ico K Ku, a k - ∑ j ∈ range δ, b j -
          ∑ j ∈ Ico (K + δ) Kv, b j‖
        ≤ ‖∑ k ∈ range K, (a k - b (k + δ))‖ + ‖∑ k ∈ Ico K Ku, a k‖ + ‖∑ j ∈ range δ, b j‖ +
          ‖∑ j ∈ Ico (K + δ) Kv, b j‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          refine (norm_sub_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ Ku * η + 3 * m := by linarith
  · -- fewer than `δ` passes of `v`: everything is a leftover
    have e1 := norm_sum_le_card (s := range Ku) ha
    have e2 := norm_sum_le_card (s := range Kv) hb
    simp only [card_range] at e1 e2
    have : (Ku : ℝ) + Kv ≤ 3 * m := by
      have : Ku + Kv ≤ 3 * m := by omega
      exact_mod_cast this
    have hKη : 0 ≤ (Ku : ℝ) * η := by positivity
    calc ‖∑ k ∈ range Ku, a k - ∑ k ∈ range Kv, b k‖
        ≤ ‖∑ k ∈ range Ku, a k‖ + ‖∑ k ∈ range Kv, b k‖ := norm_sub_le _ _
      _ ≤ Ku * η + 3 * m := by linarith

/-- **Cyclic sweep offset.** If up `u` meets down `αu - k (mod m)` at its `k`-th pass and up `v`
meets
`αv - k (mod m)`, then with `δ = (αv - αu) mod m` they meet the same down at passes `k` and
`k + δ`. -/
theorem sweep_offset {m : ℕ} (hm : 0 < m) {αu αv : ℤ} {du dv : ℕ → ℕ}
    (hu : ∀ k, (du k : ℤ) = (αu - k) % m) (hv : ∀ k, (dv k : ℤ) = (αv - k) % m) (k : ℕ) :
    du k = dv (k + ((αv - αu) % m).toNat) := by
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hδ : (((αv - αu) % m).toNat : ℤ) = (αv - αu) % m :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ hm'.ne')
  have h := hv (k + ((αv - αu) % m).toNat)
  push_cast at h
  rw [hδ] at h
  have : (dv (k + ((αv - αu) % m).toNat) : ℤ) = (αu - k) % m := by
    rw [h, Int.emod_def (αv - αu),
      show αv - (↑k + (αv - αu - ↑m * ((αv - αu) / ↑m))) = (αu - ↑k) + ↑m * ((αv - αu) / ↑m) by
        ring]
    exact Int.add_mul_emod_self_left _ _ _
  exact_mod_cast (hu k).trans this.symm

/-- **Paired passes are close.** Same down (`du k = dv (k + δ)`), phases `ε`-Lipschitz in time, lag
`|n k - t_k| ≤ n m` for both ups, `δ ≤ m`: the paired phases differ by at most `3 n m ε`. -/
theorem phase_match {f : ℕ → ℕ → ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (hlip : ∀ d t t', ‖f d t - f d t'‖ ≤ ε * |(t : ℝ) - t'|) {n m δ k : ℕ} (hδ : δ ≤ m)
    {du dv tu tv : ℕ → ℕ} (hd : du k = dv (k + δ))
    (hlu : |(n : ℝ) * k - tu k| ≤ n * m) (hlv : |(n : ℝ) * ↑(k + δ) - tv (k + δ)| ≤ n * m) :
    ‖f (du k) (tu k) - f (dv (k + δ)) (tv (k + δ))‖ ≤ 3 * n * m * ε := by
  rw [hd]
  refine (hlip _ _ _).trans ?_
  have hδ' : (n : ℝ) * δ ≤ n * m := by gcongr
  have hn : (0 : ℝ) ≤ n := by positivity
  have habs : |(tu k : ℝ) - tv (k + δ)| ≤ 3 * n * m := by
    push_cast at hlv
    rw [abs_le] at hlu hlv ⊢
    constructor <;> nlinarith
  calc ε * |(tu k : ℝ) - tv (k + δ)| ≤ ε * (3 * n * m) := by gcongr
    _ = 3 * n * m * ε := by ring

/-- One factor `1 + i c a + r` with `‖a‖ ≤ 1`, `‖r‖ ≤ R c²`, `|c| + R c² ≤ 1/2`: its log is `i c a`
up to
`(|c| + R c²)² + R c²`. -/
theorem log_factor {c R : ℝ} (hc : |c| + R * c ^ 2 ≤ 1 / 2) {a r : ℂ} (ha : ‖a‖ ≤ 1)
    (hr : ‖r‖ ≤ R * c ^ 2) :
    ‖log (1 + (I * c * a + r)) - I * c * a‖ ≤ (|c| + R * c ^ 2) ^ 2 + R * c ^ 2 := by
  set z := I * c * a + r
  have hz : ‖z‖ ≤ |c| + R * c ^ 2 := by
    calc ‖z‖ ≤ ‖I * c * a‖ + ‖r‖ := norm_add_le _ _
      _ ≤ |c| * 1 + R * c ^ 2 := by
          gcongr
          simp only [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]
          gcongr
      _ = |c| + R * c ^ 2 := by ring
  have hz2 : ‖z‖ < 1 := by linarith
  have hlog := Complex.norm_log_one_add_sub_self_le hz2
  have hinv : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    linarith
  have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
  have hsq : ‖z‖ ^ 2 ≤ (|c| + R * c ^ 2) ^ 2 := by gcongr
  have h1 : ‖log (1 + z) - z‖ ≤ (|c| + R * c ^ 2) ^ 2 := by
    calc ‖log (1 + z) - z‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := hlog
      _ ≤ ‖z‖ ^ 2 * 2 / 2 := by gcongr
      _ ≤ (|c| + R * c ^ 2) ^ 2 := by linarith
  calc ‖log (1 + z) - I * c * a‖ = ‖(log (1 + z) - z) + r‖ := by
        congr 1
        simp only [z]
        ring
    _ ≤ ‖log (1 + z) - z‖ + ‖r‖ := norm_add_le _ _
    _ ≤ (|c| + R * c ^ 2) ^ 2 + R * c ^ 2 := by linarith

theorem sum_log_err {K : ℕ} {c : ℝ} {a r : ℕ → ℂ} {E : ℝ}
    (h : ∀ k, ‖log (1 + (I * c * a k + r k)) - I * c * a k‖ ≤ E) :
    ‖∑ k ∈ range K, log (1 + (I * c * a k + r k)) - I * c * ∑ k ∈ range K, a k‖ ≤ K * E := by
  rw [mul_sum, ← sum_sub_distrib]
  calc ‖∑ k ∈ range K, (log (1 + (I * c * a k + r k)) - I * c * a k)‖
      ≤ ∑ k ∈ range K, ‖log (1 + (I * c * a k + r k)) - I * c * a k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ range K, E := sum_le_sum fun k _ => h k
    _ = K * E := by simp

/-- **Proposition 2 (explicit).** Over a rhombic phase, the accumulated log factors of two ups `u`,
`v`
(the change of `log (U_u / U_v)`) differ by at most
`|c| (3 n m ε K_u + 3 m) + (K_u + K_v) ((|c| + R c²)² + R c²)`. -/
theorem prop2 {m n Ku Kv : ℕ} (hm : 0 < m) {c ε R : ℝ} (hε : 0 ≤ ε)
    (hc : |c| + R * c ^ 2 ≤ 1 / 2)
    (f : ℕ → ℕ → ℂ) (hf1 : ∀ d t, ‖f d t‖ ≤ 1)
    (hlip : ∀ d t t', ‖f d t - f d t'‖ ≤ ε * |(t : ℝ) - t'|)
    {αu αv : ℤ} {du dv : ℕ → ℕ} (hu : ∀ k, (du k : ℤ) = (αu - k) % m)
    (hv : ∀ k, (dv k : ℤ) = (αv - k) % m)
    {tu tv : ℕ → ℕ} (hlu : ∀ k < Ku, |(n : ℝ) * k - tu k| ≤ n * m)
    (hlv : ∀ k < Kv, |(n : ℝ) * k - tv k| ≤ n * m) (hbal : Ku ≤ Kv + m ∧ Kv ≤ Ku + m)
    {ru rv : ℕ → ℂ} (hru : ∀ k, ‖ru k‖ ≤ R * c ^ 2) (hrv : ∀ k, ‖rv k‖ ≤ R * c ^ 2) :
    ‖∑ k ∈ range Ku, log (1 + (I * c * f (du k) (tu k) + ru k)) -
        ∑ k ∈ range Kv, log (1 + (I * c * f (dv k) (tv k) + rv k))‖ ≤
      |c| * (Ku * (3 * n * m * ε) + 3 * m) + (Ku + Kv) * ((|c| + R * c ^ 2) ^ 2 + R * c ^ 2) := by
  set a : ℕ → ℂ := fun k => f (du k) (tu k)
  set b : ℕ → ℂ := fun k => f (dv k) (tv k)
  set E := (|c| + R * c ^ 2) ^ 2 + R * c ^ 2
  set δ := ((αv - αu) % m).toNat
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  have hδ : δ < m := by
    have h1 : (αv - αu) % m < m := Int.emod_lt_of_pos _ hm'
    have h0 : 0 ≤ (αv - αu) % m := Int.emod_nonneg _ hm'.ne'
    have : (δ : ℤ) < m := by rw [show (δ : ℤ) = (αv - αu) % m from Int.toNat_of_nonneg h0]; exact h1
    exact_mod_cast this
  have hsweep : ∀ k, du k = dv (k + δ) := sweep_offset hm hu hv
  have hmatch : ∀ k, k < Ku → k + δ < Kv → ‖a k - b (k + δ)‖ ≤ 3 * n * m * ε := fun k hk hkv =>
    phase_match hε hlip hδ.le (hsweep k) (hlu k hk) (hlv _ hkv)
  have hsum := matched_sum_bound (a := a) (b := b) (fun k => hf1 _ _) (fun k => hf1 _ _)
    (by positivity) hδ hbal hmatch
  have eu := sum_log_err (K := Ku) (a := a) (r := ru)
    (fun k => log_factor hc (hf1 _ _) (hru k))
  have ev := sum_log_err (K := Kv) (a := b) (r := rv)
    (fun k => log_factor hc (hf1 _ _) (hrv k))
  have hmain : ‖I * c * ∑ k ∈ range Ku, a k - I * c * ∑ k ∈ range Kv, b k‖ ≤
      |c| * (Ku * (3 * n * m * ε) + 3 * m) := by
    rw [← mul_sub, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    gcongr
  calc _ = ‖(∑ k ∈ range Ku, log (1 + (I * c * a k + ru k)) - I * c * ∑ k ∈ range Ku, a k) -
          (∑ k ∈ range Kv, log (1 + (I * c * b k + rv k)) - I * c * ∑ k ∈ range Kv, b k) +
          (I * c * ∑ k ∈ range Ku, a k - I * c * ∑ k ∈ range Kv, b k)‖ := by
        congr 1
        ring
    _ ≤ Ku * E + Kv * E + |c| * (Ku * (3 * n * m * ε) + 3 * m) := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans (add_le_add eu ev)) hmain
    _ = _ := by ring

end Phyllotaxis.Prop2
