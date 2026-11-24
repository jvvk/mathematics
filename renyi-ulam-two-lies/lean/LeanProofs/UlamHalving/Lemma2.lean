import LeanProofs.UlamHalving.Padding
import LeanProofs.UlamHalving.Key

/-!
# Lemma 2: many last-class candidates suffice (PROOF.md, Section 3)

For every `n ≥ 12`: if `a ≤ b`, `c ≥ C(n, 2)` and `V n (a, b, c) ≤ 2^n`, then `(a, b, c)` is solvable within `n`
questions. The finite base `n = 12` is a hypothesis (`base12`, the certificate's 44 boundary checks); the
induction step `n → n + 1` is the paper's explicit question. Pad to full volume, take `u = ⌊a/2⌋`, and

* if `b ≥ n + 1`, take `v` a nearest integer to `b/2 + εD/(2(n+1))` (encoded by
  `2(n+1)v ≤ (n+1)b + εD + (n+1) < 2(n+1)(v+1)`) and `w` making the YES-volume `2^n`;
* if `b ≤ n`, take `v = ⌊b/2⌋` and `2w = c + εD + ηn`.

Both children then meet the hypotheses one level down. The growth inequalities (9) and `2^N ≥ 2N^3` (`N ≥ 13`)
are proved by induction.
-/

namespace UlamHalving

/-- (9): `4 · 2^N ≥ N^4 + N^2 - 2N + 16` for `N ≥ 13`. -/
lemma growth9 (N : ℕ) (hN : 13 ≤ N) : (N : ℤ) ^ 4 + N ^ 2 - 2 * N + 16 ≤ 4 * 2 ^ N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    have h13 : (13 : ℤ) ≤ N := by exact_mod_cast hN
    push_cast
    rw [pow_succ 2 N]
    nlinarith [mul_le_mul_of_nonneg_left h13 (by positivity : (0 : ℤ) ≤ (N : ℤ) ^ 3),
      mul_le_mul_of_nonneg_left h13 (by positivity : (0 : ℤ) ≤ (N : ℤ) ^ 2),
      mul_le_mul_of_nonneg_left h13 (by positivity : (0 : ℤ) ≤ (N : ℤ))]

/-- `2^N ≥ 2 N^3` for `N ≥ 13`. -/
lemma growth_cube (N : ℕ) (hN : 13 ≤ N) : 2 * (N : ℤ) ^ 3 ≤ 2 ^ N := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    have h13 : (13 : ℤ) ≤ N := by exact_mod_cast hN
    push_cast
    rw [pow_succ 2 N]
    nlinarith [mul_le_mul_of_nonneg_left h13 (by positivity : (0 : ℤ) ≤ (N : ℤ) ^ 2),
      mul_le_mul_of_nonneg_left h13 (by positivity : (0 : ℤ) ≤ (N : ℤ))]

/-- Case `b ≥ N` of the induction step, pure arithmetic. Child depth `n`, parent depth `N = n + 1`,
`D = C(n, 2)`, `H = 2^n`; `v` is a nearest integer to `b/2 + εD/(2N)` and `w` makes the YES-volume `H`. -/
lemma case1_arith (n D a b c u ε v H w : ℤ) (hn : 12 ≤ n) (hD : 2 * D = n * (n - 1))
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : a = 2 * u + ε)
    (hab : a ≤ b) (hbN : n + 1 ≤ b) (hc : D + n ≤ c)
    (hFV : (D + 2 * n + 2) * a + (n + 2) * b + c = 2 * H)
    (hG : (D + 3 * (n + 1) + 1) * (D + 1) + D + n ≤ 2 * H)
    (hv1 : 2 * (n + 1) * v ≤ (n + 1) * b + ε * D + (n + 1))
    (hv2 : (n + 1) * b + ε * D + (n + 1) < 2 * (n + 1) * (v + 1))
    (hw : w = H - (n + 1) * a - b - D * u - n * v) :
    v + ε ≤ b ∧ 0 ≤ w ∧ w ≤ c ∧ D ≤ w + b - v ∧ D ≤ c - w + v := by
  have hD0 : 0 ≤ D := by nlinarith
  set R := 2 * (n + 1) * v - ((n + 1) * b + ε * D) with hR
  have hRu : R ≤ n + 1 := by linarith
  have hRl : -(n + 1) < R := by linarith
  have I1 : 2 * (n + 1) * w = (n + 1) * c + ε * D - n * R := by
    rw [hw, hR]; subst ha; linear_combination (-(n + 1)) * hFV
  have I2 : 2 * (w + b - v) = b + c - R := by
    rw [hw, hR]; subst ha; linear_combination (-1 : ℤ) * hFV
  have hεD : ε * D ≤ D := by nlinarith
  have hεN : ε * (n + 1) ≤ n + 1 := by nlinarith
  -- b + c ≥ 2D + N, from (9)
  have hB : 2 * D + (n + 1) ≤ b + c := by
    by_contra hcon
    rw [not_le] at hcon
    have hbD : b ≤ D := by linarith
    have h1 : (D + 2 * n + 2) * a ≤ (D + 2 * n + 2) * b := mul_le_mul_of_nonneg_left hab (by linarith)
    have h2 : (D + 3 * n + 3) * b ≤ (D + 3 * n + 3) * D := mul_le_mul_of_nonneg_left hbD (by linarith)
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hNN : (n + 1) * (n + 1) ≤ (n + 1) * b := mul_le_mul_of_nonneg_left hbN (by linarith)
    have : D + 3 * (n + 1) ≤ (n + 1) * (n + 1) := by nlinarith
    have : (n + 1) * (v + ε) ≤ (n + 1) * b := by nlinarith
    exact le_of_mul_le_mul_left this (by linarith)
  · have : n * R ≤ n * (n + 1) := mul_le_mul_of_nonneg_left hRu (by linarith)
    have : (n + 1) * n ≤ (n + 1) * c := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have : 0 ≤ (n + 1) * w := by nlinarith
    by_contra h0
    rw [not_le] at h0
    have : (n + 1) * w < 0 := mul_neg_of_pos_of_neg (by linarith) h0
    linarith
  · have h1 : n * (-R) ≤ n * (n + 1) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : (n + 1) * (D + n) ≤ (n + 1) * c := mul_le_mul_of_nonneg_left hc (by linarith)
    have h3 : 0 ≤ n * D := mul_nonneg (by linarith) hD0
    have : (n + 1) * w ≤ (n + 1) * c := by linarith
    exact le_of_mul_le_mul_left this (by linarith)
  · linarith
  · linarith

/-- Case `b < N` of the induction step, pure arithmetic: `v = ⌊b/2⌋` and `2w = c + εD + ηn`. -/
lemma case2_arith (n D a b c u ε v η H w : ℤ) (hn : 12 ≤ n) (hD : 2 * D = n * (n - 1))
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : a = 2 * u + ε) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hb : b = 2 * v + η)
    (hv0 : 0 ≤ v) (ha0 : 0 ≤ a) (hab : a ≤ b) (hbn : b ≤ n) (hc : D + n ≤ c)
    (hFV : (D + 2 * n + 2) * a + (n + 2) * b + c = 2 * H)
    (hG : 2 * (n + 1) ^ 3 ≤ 2 * H)
    (hw : w = H - D * u - 2 * (n + 1) * u - (n + 1) * ε - (n + 2) * v - η) :
    0 ≤ w ∧ w ≤ c ∧ D ≤ w + b - v ∧ D ≤ c - w + v ∧ D * u + n * v + (n + 1) * a + b + w = H := by
  have hD0 : 0 ≤ D := by nlinarith
  have I : 2 * w = c + ε * D + n * η := by rw [hw]; subst ha hb; linear_combination (-1 : ℤ) * hFV
  have hεD : ε * D ≤ D := by nlinarith
  have hηn : η * n ≤ n := by nlinarith
  have h1 : (D + 2 * n + 2) * a ≤ (D + 2 * n + 2) * n :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (n + 2) * b ≤ (n + 2) * n := mul_le_mul_of_nonneg_left hbn (by linarith)
  have hnD : 2 * (n * D) = n * (n * (n - 1)) := by rw [← hD]; ring
  have hcb : 3 * D + n ≤ c := by nlinarith
  refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, ?_⟩
  rw [hw]; subst ha hb; ring

/-- The statement of Lemma 2 at depth `n`. -/
def L2 (n : ℕ) : Prop :=
  ∀ a b c : ℕ, a ≤ b → n.choose 2 ≤ c → V n ⟨a, b, c⟩ ≤ 2 ^ n → Solv n ⟨a, b, c⟩

lemma choose_two_mul (n : ℕ) : 2 * (n.choose 2 : ℤ) = n * (n - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : 2 * n.choose 2 = n * (n - 1) := by
    rw [Nat.choose_two_right]
    have := (Nat.even_mul_pred_self n).two_dvd
    omega
  have : ((n * (n - 1) : ℕ) : ℤ) = n * (n - 1) := by push_cast [Nat.cast_sub (by omega : 1 ≤ n)]; ring
  rw [← this]; exact_mod_cast h1

lemma choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right]; ring

/-- A question whose YES-volume is exactly `2^n`, from a state of volume exactly `2^(n+1)`, whose two children
both meet the hypotheses of Lemma 2 at depth `n`, wins. -/
lemma finish {n a b c u v w : ℕ} (IH : L2 n) (hu : u ≤ a) (hv : v ≤ b) (hw : w ≤ c)
    (hfull : V (n + 1) ⟨a, b, c⟩ = 2 ^ (n + 1)) (hY : V n (yes ⟨a, b, c⟩ u v w) = 2 ^ n)
    (h1 : u ≤ v + (a - u)) (h2 : a - u ≤ b - v + u)
    (h3 : n.choose 2 ≤ w + (b - v)) (h4 : n.choose 2 ≤ c - w + v) : Solv (n + 1) ⟨a, b, c⟩ := by
  have cons := V_conserve n ⟨a, b, c⟩ u v w hu hv hw
  refine Solv.step u v w hu hv hw (IH _ _ _ h1 h3 hY.le) (IH _ _ _ h2 h4 ?_)
  show V n (no ⟨a, b, c⟩ u v w) ≤ 2 ^ n
  rw [pow_succ] at hfull
  omega

/-- (9) in the form used by the step: `2^(n+1) ≥ A (D + 1) + C` with `D = C(n, 2)`, `A = D + 3(n+1) + 1`. -/
lemma growth9' (n : ℕ) (hn : 12 ≤ n) :
    ((n.choose 2 : ℕ) + 3 * ((n : ℤ) + 1) + 1) * ((n.choose 2 : ℕ) + 1) + (n.choose 2 : ℕ) + n ≤ 2 * 2 ^ n := by
  have hD := choose_two_mul n
  have hg := growth9 (n + 1) (by omega)
  push_cast at hg
  rw [pow_succ (2 : ℤ) n] at hg
  have e : 4 * (((n.choose 2 : ℕ) + 3 * ((n : ℤ) + 1) + 1) * ((n.choose 2 : ℕ) + 1) + (n.choose 2 : ℕ) + n) =
      ((n : ℤ) + 1) ^ 4 + (n + 1) ^ 2 - 2 * (n + 1) + 16 := by
    linear_combination (2 * ((n.choose 2 : ℕ) : ℤ) + n * (n - 1) + 6 * (n + 1) + 6) * hD
  linarith

/-- The induction step at full volume. -/
lemma L2_full (n : ℕ) (hn : 12 ≤ n) (IH : L2 n) (a b c : ℕ) (hab : a ≤ b) (hc : (n + 1).choose 2 ≤ c)
    (hfull : V (n + 1) ⟨a, b, c⟩ = 2 ^ (n + 1)) : Solv (n + 1) ⟨a, b, c⟩ := by
  obtain ⟨D, hDdef⟩ : ∃ D, D = n.choose 2 := ⟨_, rfl⟩
  have hD : 2 * (D : ℤ) = n * (n - 1) := hDdef ▸ choose_two_mul n
  have hC : (n + 1).choose 2 = D + n := hDdef ▸ choose_two_succ n
  rw [hC] at hc
  have hFV : ((D : ℤ) + 2 * n + 2) * a + (n + 2) * b + c = 2 * 2 ^ n := by
    have h : (V (n + 1) ⟨a, b, c⟩ : ℤ) = 2 ^ (n + 1) := by exact_mod_cast hfull
    simp only [V, W] at h
    rw [hC] at h
    push_cast at h
    rw [pow_succ] at h
    linear_combination h
  have hG := growth9' n hn
  rw [← hDdef] at hG
  obtain ⟨u, hu⟩ : ∃ u, u = a / 2 := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε, ε = a % 2 := ⟨_, rfl⟩
  have ha2 : (a : ℤ) = 2 * u + ε := by omega
  have hY : ∀ v w : ℕ, v ≤ b → (V n (yes ⟨a, b, c⟩ u v w) : ℤ) = D * u + n * v + (n + 1) * a + b + w := by
    intro v w hv
    rw [V_yes n _ _ _ _ (show u ≤ a by omega) hv, hDdef]
  rcases le_or_gt (n + 1) b with hbN | hbn
  · -- Case b ≥ N: v is a nearest integer to b/2 + εD/(2N)
    obtain ⟨X, hX⟩ : ∃ X, X = (n + 1) * b + ε * D + (n + 1) := ⟨_, rfl⟩
    obtain ⟨v, hvdef⟩ : ∃ v, v = X / (2 * (n + 1)) := ⟨_, rfl⟩
    have hv1 : v * (2 * (n + 1)) ≤ X := hvdef ▸ Nat.div_mul_le_self X (2 * (n + 1))
    have hv2 : X < v * (2 * (n + 1)) + 2 * (n + 1) := hvdef ▸ Nat.lt_div_mul_add (by omega)
    have hv1' : 2 * ((n : ℤ) + 1) * v ≤ (n + 1) * b + ε * D + (n + 1) := by
      have : ((v * (2 * (n + 1)) : ℕ) : ℤ) ≤ (X : ℤ) := by exact_mod_cast hv1
      rw [hX] at this; push_cast at this; linarith
    have hv2' : ((n : ℤ) + 1) * b + ε * D + (n + 1) < 2 * (n + 1) * (v + 1) := by
      have : (X : ℤ) < ((v * (2 * (n + 1)) + 2 * (n + 1) : ℕ) : ℤ) := by exact_mod_cast hv2
      rw [hX] at this; push_cast at this; linarith
    obtain ⟨wZ, hwZ⟩ : ∃ wZ : ℤ, wZ = 2 ^ n - (n + 1) * a - b - D * u - n * v := ⟨_, rfl⟩
    obtain ⟨hvε, hw0, hwc, h3, h4⟩ := case1_arith n D a b c u ε v (2 ^ n) wZ
      (by exact_mod_cast hn) hD (by positivity) (by omega) ha2 (by exact_mod_cast hab)
      (by exact_mod_cast hbN) (by exact_mod_cast hc) hFV hG hv1' hv2' hwZ
    have hwN : ((wZ.toNat : ℕ) : ℤ) = wZ := Int.toNat_of_nonneg hw0
    have hvb : v ≤ b := by omega
    refine finish (u := u) (v := v) (w := wZ.toNat) IH (by omega) hvb (by omega) hfull ?_ (by omega) (by omega)
      (by rw [← hDdef]; omega) (by rw [← hDdef]; omega)
    have hy := hY v wZ.toNat hvb
    rw [hwN] at hy
    have : (V n (yes ⟨a, b, c⟩ u v wZ.toNat) : ℤ) = 2 ^ n := by rw [hy, hwZ]; ring
    exact_mod_cast this
  · -- Case b < N: v = ⌊b/2⌋
    obtain ⟨v, hv⟩ : ∃ v, v = b / 2 := ⟨_, rfl⟩
    obtain ⟨η, hη⟩ : ∃ η, η = b % 2 := ⟨_, rfl⟩
    obtain ⟨wZ, hwZ⟩ : ∃ wZ : ℤ, wZ = 2 ^ n - D * u - 2 * (n + 1) * u - (n + 1) * ε - (n + 2) * v - η :=
      ⟨_, rfl⟩
    have hG3 := growth_cube (n + 1) (by omega)
    push_cast at hG3
    rw [pow_succ (2 : ℤ) n] at hG3
    obtain ⟨hw0, hwc, h3, h4, hvol⟩ := case2_arith n D a b c u ε v η (2 ^ n) wZ
      (by exact_mod_cast hn) hD (by positivity) (by omega) ha2 (by positivity) (by omega)
      (by omega) (by positivity) (by positivity) (by exact_mod_cast hab) (by omega) (by exact_mod_cast hc) hFV
      (by linarith) hwZ
    have hwN : ((wZ.toNat : ℕ) : ℤ) = wZ := Int.toNat_of_nonneg hw0
    refine finish (u := u) (v := v) (w := wZ.toNat) IH (by omega) (by omega) (by omega) hfull ?_
      (by omega) (by omega) (by rw [← hDdef]; omega) (by rw [← hDdef]; omega)
    have hy := hY v wZ.toNat (by omega)
    rw [hwN] at hy
    have : (V n (yes ⟨a, b, c⟩ u v wZ.toNat) : ℤ) = 2 ^ n := by rw [hy]; linarith
    exact_mod_cast this

/-- The induction step of Lemma 2. -/
lemma L2_step (n : ℕ) (hn : 12 ≤ n) (IH : L2 n) : L2 (n + 1) := by
  intro a b c hab hc hV
  have hVk : ∀ k, V (n + 1) ⟨a, b, c + k⟩ = V (n + 1) ⟨a, b, c⟩ + k := fun k => by simp only [V]; ring
  have hfull : V (n + 1) ⟨a, b, c + (2 ^ (n + 1) - V (n + 1) ⟨a, b, c⟩)⟩ = 2 ^ (n + 1) := by rw [hVk]; omega
  exact (L2_full n hn IH a b _ hab (by omega) hfull).mono _ le_rfl le_rfl (by simp only; omega)

/-- **Lemma 2**, conditional on the finite base at depth 12: for every `n ≥ 12`, a state `(a, b, c)` with
`a ≤ b`, `c ≥ C(n, 2)` and `V n (a, b, c) ≤ 2^n` is solvable within `n` questions. -/
theorem lemma2 (base12 : ∀ a b c : ℕ, a ≤ b → 66 ≤ c → V 12 ⟨a, b, c⟩ ≤ 2 ^ 12 → Solv 12 ⟨a, b, c⟩)
    (n : ℕ) (hn : 12 ≤ n) (a b c : ℕ) (hab : a ≤ b) (hc : n.choose 2 ≤ c) (hV : V n ⟨a, b, c⟩ ≤ 2 ^ n) :
    Solv n ⟨a, b, c⟩ := by
  revert a b c
  induction n, hn using Nat.le_induction with
  | base =>
    intro a b c hab hc hV
    exact base12 a b c hab (by rwa [show (12 : ℕ).choose 2 = 66 by rw [Nat.choose_two_right]] at hc) hV
  | succ n hn ih => exact L2_step n hn ih

end UlamHalving
