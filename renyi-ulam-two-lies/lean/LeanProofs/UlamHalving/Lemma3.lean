import LeanProofs.UlamHalving.Lemma2

/-!
# Lemma 3, sufficiency (PROOF.md, Section 4)

For the halving child `z = (a, a + b, b)` at depth `m = n + 1 ≥ 15` and `g = gcd(n, C(n, 2))`, the criterion
`Crit g n a b` (integers `t ∈ [H - s, H]`, `w ∈ [0, b]` with `g ∣ t - K - w`) together with the volume bound
makes `z` solvable within `n + 1` questions. If `b + s ≥ C(n+1, 2)`, Lemma 2 applies at depth `n + 1` after
padding the last class. Otherwise (13) forces `a ≥ (n+1)^2`; a `u` within 1 of `a/2` makes
`n ∣ t - K - D u - w`, and `v = (t - K - D u - w)/n` gives a question with YES-volume `t` whose children both
meet Lemma 2 at depth `n`.
-/

namespace UlamHalving

/-- (13): `2 · 2^m ≥ m^4 + 4m^3 + 5m^2 - 2m` for `m ≥ 15`. -/
lemma growth13 (m : ℕ) (hm : 15 ≤ m) : (m : ℤ) ^ 4 + 4 * m ^ 3 + 5 * m ^ 2 - 2 * m ≤ 2 * 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h15 : (15 : ℤ) ≤ m := by exact_mod_cast hm
    push_cast
    rw [pow_succ (2 : ℤ) m]
    nlinarith [mul_le_mul_of_nonneg_left h15 (by positivity : (0 : ℤ) ≤ (m : ℤ) ^ 3),
      mul_le_mul_of_nonneg_left h15 (by positivity : (0 : ℤ) ≤ (m : ℤ) ^ 2),
      mul_le_mul_of_nonneg_left h15 (by positivity : (0 : ℤ) ≤ (m : ℤ))]

/-- The choice of `u`: if `gcd(n, C(n,2))` divides `X`, some `u ∈ {⌊a/2⌋, ⌊a/2⌋ + 1}` has
`n ∣ X - C(n,2) u`. For odd `n`, `n ∣ C(n,2)` and `g = n`; for even `n = 2k`, `g = k`, `C(n,2) = k(2k-1)`, and the
parity of `u` is chosen. -/
lemma choose_u (n a : ℕ) (hn : 1 ≤ n) (X : ℤ) (hX : ((Nat.gcd n (n.choose 2) : ℕ) : ℤ) ∣ X) :
    ∃ u : ℕ, a / 2 ≤ u ∧ u ≤ a / 2 + 1 ∧ (n : ℤ) ∣ X - (n.choose 2 : ℕ) * u := by
  have hD := choose_two_mul n
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- n = 2k, C(n,2) = k(2k-1), gcd = k
    have hk1 : 1 ≤ k := by omega
    have hDk : n.choose 2 = k * (2 * k - 1) := by
      have : (n.choose 2 : ℤ) = k * (2 * k - 1) := by
        have : (n : ℤ) = 2 * k := by exact_mod_cast (by omega : n = 2 * k)
        rw [this] at hD; linarith
      have e : ((k * (2 * k - 1) : ℕ) : ℤ) = k * (2 * k - 1) := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]; ring
      exact_mod_cast this.trans e.symm
    have hg : Nat.gcd n (n.choose 2) = k := by
      rw [hDk, (by omega : n = k * 2), Nat.gcd_mul_left]
      have : Nat.Coprime 2 (2 * k - 1) := Nat.coprime_two_left.mpr ⟨k - 1, by omega⟩
      rw [this]; ring
    rw [hg] at hX
    obtain ⟨j, hj⟩ := hX
    have hDkZ : ((n.choose 2 : ℕ) : ℤ) = k * (2 * k - 1) := by
      rw [hDk]; push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * k)]; ring
    have hnZ : (n : ℤ) = 2 * k := by exact_mod_cast (by omega : n = 2 * k)
    rcases Int.even_or_odd (j + (a / 2 : ℕ)) with ⟨r, hr⟩ | ⟨r, hr⟩
    · refine ⟨a / 2, le_rfl, by omega, ?_⟩
      rw [hj, hDkZ, hnZ]
      exact ⟨r - k * (a / 2 : ℕ), by linear_combination (k : ℤ) * hr⟩
    · refine ⟨a / 2 + 1, by omega, le_rfl, ?_⟩
      rw [hj, hDkZ, hnZ]
      refine ⟨r + 1 - k * ((a / 2 : ℕ) + 1), ?_⟩
      simp only [Nat.cast_add, Nat.cast_one]
      linear_combination (k : ℤ) * hr
  · -- n odd: n ∣ C(n,2)
    have hdvd : n ∣ n.choose 2 := by
      refine ⟨k, ?_⟩
      have : (n.choose 2 : ℤ) = n * k := by
        have : (n : ℤ) = 2 * k + 1 := by exact_mod_cast hk
        nlinarith
      exact_mod_cast this
    rw [Nat.gcd_eq_left hdvd] at hX
    refine ⟨a / 2, le_rfl, by omega, ?_⟩
    exact dvd_sub hX (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hdvd) _)

/-- The arithmetic of the explicit question in the case `b + s < C(m, 2)`, `a ≥ m^2`. Child depth `n`,
`D = C(n,2)`; `ρ = 2u - a ∈ [-1, 2]`; `n v = t - K - D u - w`. -/
lemma lemma3_arith (n D a b s t w u v : ℤ) (hn : 14 ≤ n) (hD : 2 * D = n * (n - 1))
    (hs0 : 0 ≤ s) (hbs : b + s < D + n) (ha : (n + 1) ^ 2 ≤ a) (hb0 : 0 ≤ b)
    (ht1 : 2 * t - ((D + 3 * n + 4) * a + (n + 3) * b) ≤ s)
    (ht2 : -s ≤ 2 * t - ((D + 3 * n + 4) * a + (n + 3) * b))
    (hw0 : 0 ≤ w) (hwb : w ≤ b) (hu1 : a ≤ 2 * u + 1) (hu2 : 2 * u ≤ a + 2)
    (hv : n * v = t - ((n + 2) * a + b) - D * u - w) :
    2 ≤ v ∧ v + 1 ≤ a + b ∧ D ≤ a + b - v ∧ D ≤ v := by
  have hD0 : 0 ≤ D := by nlinarith
  set E := 2 * n * v - n * (a + b) with hE
  have hEid : E = (2 * t - ((D + 3 * n + 4) * a + (n + 3) * b)) + b - 2 * w - D * (2 * u - a) := by
    rw [hE]; linear_combination 2 * hv
  have hρ1 : D * (2 * u - a) ≤ D * 2 := mul_le_mul_of_nonneg_left (by linarith) hD0
  have hρ2 : -D ≤ D * (2 * u - a) := by nlinarith
  have hEu : E ≤ 3 * D + n := by linarith
  have hEl : -(3 * D + n) ≤ E := by linarith
  have hna : n * (n + 1) ^ 2 ≤ n * (a + b) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hnD : 2 * (n * D) = n * (n * (n - 1)) := by rw [← hD]; ring
  have big : 2 * (n * D) + 3 * D + 5 * n ≤ n * (a + b) := by nlinarith
  have pos : (0 : ℤ) < n := by linarith
  have hnD0 : 0 ≤ n * D := mul_nonneg (by linarith) hD0
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : n * 2 ≤ n * v := by linarith
    exact le_of_mul_le_mul_left this pos
  · have : n * (v + 1) ≤ n * (a + b) := by linarith
    exact le_of_mul_le_mul_left this pos
  · have : n * D ≤ n * (a + b - v) := by linarith
    exact le_of_mul_le_mul_left this pos
  · have : n * D ≤ n * v := by linarith
    exact le_of_mul_le_mul_left this pos

/-- **Lemma 3, sufficiency.** At depth `m = n + 1 ≥ 15`, with `g = gcd(n, C(n,2))`, the criterion and the
volume bound make the halving child `(a, a + b, b)` solvable. Conditional on the depth-12 base of Lemma 2. -/
theorem lemma3 (base12 : ∀ a b c : ℕ, a ≤ b → 66 ≤ c → V 12 ⟨a, b, c⟩ ≤ 2 ^ 12 → Solv 12 ⟨a, b, c⟩)
    (n : ℕ) (hn : 14 ≤ n) (a b : ℕ) (hcrit : Crit (Nat.gcd n (n.choose 2)) n a b)
    (hV : V (n + 1) ⟨a, a + b, b⟩ ≤ 2 ^ (n + 1)) : Solv (n + 1) ⟨a, a + b, b⟩ := by
  obtain ⟨t, w, ht1, ht2, hw0, hwb, hdvd⟩ := hcrit
  obtain ⟨D, hDdef⟩ : ∃ D, D = n.choose 2 := ⟨_, rfl⟩
  have hD : 2 * (D : ℤ) = n * (n - 1) := hDdef ▸ choose_two_mul n
  have hC : (n + 1).choose 2 = D + n := hDdef ▸ choose_two_succ n
  have hVz : (V (n + 1) ⟨a, a + b, b⟩ : ℤ) = (D + 3 * n + 4) * a + (n + 3) * b := by
    simp only [V, W]; rw [hC]; push_cast; ring
  obtain ⟨s, hs⟩ : ∃ s : ℤ, s = 2 ^ (n + 1) - V (n + 1) ⟨a, a + b, b⟩ := ⟨_, rfl⟩
  rw [← hs] at ht1
  have hs0 : 0 ≤ s := by
    have : (V (n + 1) ⟨a, a + b, b⟩ : ℤ) ≤ 2 ^ (n + 1) := by exact_mod_cast hV
    linarith
  rcases le_or_gt ((D : ℤ) + n) (b + s) with hbig | hsmall
  · -- Lemma 2 at depth n + 1 after padding the last class up to C(n+1, 2)
    have hVk : V (n + 1) ⟨a, a + b, b + (D + n - b)⟩ = V (n + 1) ⟨a, a + b, b⟩ + (D + n - b) := by
      simp only [V]; ring
    have h := lemma2 base12 (n + 1) (by omega) a (a + b) (b + (D + n - b)) (by omega) (by rw [hC]; omega)
      (by
        rw [hVk]
        have : ((V (n + 1) ⟨a, a + b, b⟩ + (D + n - b) : ℕ) : ℤ) ≤ 2 ^ (n + 1) := by
          push_cast [Nat.cast_sub (by omega : b ≤ b + (D + n - b))]
          rcases le_or_gt b (D + n) with hb | hb
          · push_cast [Nat.cast_sub hb]; linarith
          · rw [Nat.sub_eq_zero_of_le hb.le]; push_cast; linarith
        exact_mod_cast this)
    exact h.mono _ le_rfl le_rfl (by simp only; omega)
  · -- b + s < C(n+1, 2): the explicit question
    have hG := growth13 (n + 1) (by omega)
    push_cast at hG
    -- (14): a ≥ (n + 1)^2
    have ha : ((n : ℤ) + 1) ^ 2 ≤ a := by
      by_contra hlt
      rw [not_le] at hlt
      have h1 : (D + 3 * (n : ℤ) + 4) * a ≤ (D + 3 * n + 4) * ((n + 1) ^ 2 - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h2 : ((n : ℤ) + 2) * b ≤ (n + 2) * (D + n - 1) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have hnD : 2 * ((n : ℤ) * D) = n * (n * (n - 1)) := by rw [← hD]; ring
      nlinarith
    obtain ⟨u, hu1, hu2, hu⟩ := choose_u n a (by omega) (t - ((n + 2) * a + b) - w) hdvd
    rw [← hDdef] at hu
    obtain ⟨v, hv⟩ := hu
    have hv' : (n : ℤ) * v = t - ((n + 2) * a + b) - D * u - w := by rw [← hv]; ring
    have hsV : s = 2 * 2 ^ n - ((D + 3 * n + 4) * a + (n + 3) * b) := by rw [hs, hVz, pow_succ]; ring
    obtain ⟨h2v, hvab, hlastY, hlastN⟩ := lemma3_arith n D a b s t w u v (by exact_mod_cast hn) hD hs0 hsmall
      ha (by positivity) (by linarith) (by linarith) hw0 hwb
      (by omega) (by omega) hv'
    have hvN : ((v.toNat : ℕ) : ℤ) = v := Int.toNat_of_nonneg (by linarith)
    have hwN : ((w.toNat : ℕ) : ℤ) = w := Int.toNat_of_nonneg hw0
    have hua : u ≤ a := by
      have : (2 : ℤ) * (n + 1) ^ 2 ≤ 2 * a := by linarith
      have : 2 ≤ a := by nlinarith
      omega
    have hvb : v.toNat ≤ a + b := by omega
    have hwb' : w.toNat ≤ b := by omega
    have hYv := V_yes n ⟨a, a + b, b⟩ u v.toNat w.toNat hua hvb
    have cons := V_conserve n ⟨a, a + b, b⟩ u v.toNat w.toNat hua hvb hwb'
    simp only at hYv
    rw [hvN, hwN, ← hDdef] at hYv
    have hYt : (V n (yes ⟨a, a + b, b⟩ u v.toNat w.toNat) : ℤ) = t := by
      rw [hYv]; push_cast; linear_combination hv'
    have cons' : (V (n + 1) ⟨a, a + b, b⟩ : ℤ) = V n (yes ⟨a, a + b, b⟩ u v.toNat w.toNat) +
        V n (no ⟨a, a + b, b⟩ u v.toNat w.toNat) := by exact_mod_cast cons
    have hDn : n.choose 2 = D := hDdef.symm
    refine Solv.step u v.toNat w.toNat hua hvb hwb' ?_ ?_
    · refine lemma2 base12 n (by omega) _ _ _ (by simp only; omega) (by simp only; omega) ?_
      have : (V n (yes ⟨a, a + b, b⟩ u v.toNat w.toNat) : ℤ) ≤ 2 ^ n := by rw [hYt]; exact ht2
      exact_mod_cast this
    · refine lemma2 base12 n (by omega) _ _ _ (by simp only; omega) (by simp only; omega) ?_
      have : (V n (no ⟨a, a + b, b⟩ u v.toNat w.toNat) : ℤ) ≤ 2 ^ n := by
        linarith
      exact_mod_cast this

end UlamHalving
