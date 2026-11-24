import LeanProofs.UlamHalving.Basic

/-!
# The key step: no first question beats halving the modular obstruction

For the halving child `z = (a, a + b, b)` of `(2a, 2b, 0)` at depth `m = n + 1`, put `H = 2^n`,
`s = 2^(n+1) - V (n+1) z`, `K = (n + 2) a + b`, and let `g` divide both `n` and `C(n, 2)`. The **criterion**
`Crit` asks for integers `t ∈ [H - s, H]` and `w ∈ [0, b]` with `g ∣ t - K - w`: the yes-volume and the class-2
count of a root question of `z` must look like that (Lemma 3, necessity).

`key`: if the parent `(2a, 2b, 0)` is solvable in `n + 2` questions, then `Crit` holds for `z`. Either `s + b` is
large enough for `Crit` to hold outright, or every winning first question of the parent shifts the volumes by
`δ = C(n+1, 2) d + (n+1) f ≡ f (mod g)` with `|δ - f| < g`, so `δ = f`, and the root question of the winning child
supplies the witness.
-/

namespace UlamHalving

/-- The root of a solvable state with at least two candidates: a legal question whose children both satisfy the
volume bound. -/
lemma root {n : ℕ} {x : St} (h : Solv (n + 1) x) (hs : 2 ≤ x.size) :
    ∃ u v w, u ≤ x.a ∧ v ≤ x.b ∧ w ≤ x.c ∧ V n (yes x u v w) ≤ 2 ^ n ∧ V n (no x u v w) ≤ 2 ^ n := by
  cases h with
  | win h => omega
  | step u v w hu hv hw hY hN => exact ⟨u, v, w, hu, hv, hw, V_le _ _ hY, V_le _ _ hN⟩

/-- The yes-volume one level down, in closed form. -/
lemma V_yes (n : ℕ) (x : St) (u v w : ℕ) (hu : u ≤ x.a) (hv : v ≤ x.b) :
    (V n (yes x u v w) : ℤ) = n.choose 2 * u + n * v + (n + 1) * x.a + x.b + w := by
  obtain ⟨a, b, c⟩ := x
  simp only [V, yes, W] at *
  push_cast [Nat.cast_sub hu, Nat.cast_sub hv]; ring

/-- The criterion for `z = (a, a + b, b)` at depth `n + 1`. -/
def Crit (g n a b : ℕ) : Prop :=
  ∃ t w : ℤ, (2 : ℤ) ^ n - (2 ^ (n + 1) - V (n + 1) ⟨a, a + b, b⟩) ≤ t ∧ t ≤ 2 ^ n ∧ 0 ≤ w ∧ w ≤ b ∧
    (g : ℤ) ∣ t - ((n + 2) * a + b) - w

lemma V_z (n a b : ℕ) : (V (n + 1) ⟨a, a + b, b⟩ : ℤ) = (W (n + 1) + (n + 2)) * a + (n + 3) * b := by
  simp only [V]; push_cast; ring

lemma halve_eq (a b : ℕ) :
    (⟨a, b + (2 * a - a), 0 + (2 * b - b)⟩ : St) = ⟨a, a + b, b⟩ ∧
    (⟨2 * a - a, 2 * b - b + a, 0 - 0 + b⟩ : St) = ⟨a, a + b, b⟩ := by
  constructor <;> congr 1 <;> omega

lemma V_parent (n a b : ℕ) : V (n + 2) ⟨2 * a, 2 * b, 0⟩ = 2 * V (n + 1) ⟨a, a + b, b⟩ := by
  simp only [V, W_succ]; ring

/-- The halving child of a solvable parent satisfies the volume bound: `s ≥ 0`. -/
lemma s_nonneg (n a b : ℕ) (h : Solv (n + 2) ⟨2 * a, 2 * b, 0⟩) :
    (0 : ℤ) ≤ 2 ^ (n + 1) - V (n + 1) ⟨a, a + b, b⟩ := by
  have hv := V_le _ _ h
  rw [V_parent, pow_succ 2 (n + 1)] at hv
  have : V (n + 1) ⟨a, a + b, b⟩ ≤ 2 ^ (n + 1) := by omega
  have : (V (n + 1) ⟨a, a + b, b⟩ : ℤ) ≤ 2 ^ (n + 1) := by exact_mod_cast this
  linarith

/-- **Key step.** -/
theorem key (n a b g : ℕ) (hg : 0 < g) (hgn : g ∣ n) (hgD : g ∣ n.choose 2)
    (h : Solv (n + 2) ⟨2 * a, 2 * b, 0⟩) : Crit g n a b := by
  set s : ℤ := 2 ^ (n + 1) - V (n + 1) ⟨a, a + b, b⟩ with hs_def
  set K : ℤ := (n + 2) * a + b with hK
  set H : ℤ := 2 ^ n with hH
  -- Case A: the window is long enough
  by_cases hA : (g : ℤ) ≤ s + b + 1
  · set r : ℤ := (H - K) % g with hr
    have r0 : 0 ≤ r := Int.emod_nonneg _ (by exact_mod_cast hg.ne')
    have rg : r < g := Int.emod_lt_of_pos _ (by exact_mod_cast hg)
    have hdiv : (g : ℤ) ∣ H - K - r := ⟨(H - K) / g, by have := Int.emod_add_ediv_mul (H - K) g; linarith⟩
    refine ⟨H - r + max 0 (r - s), max 0 (r - s), ?_, ?_, le_max_left _ _, ?_, ?_⟩
    · have := le_max_right 0 (r - s); linarith
    · -- s ≥ 0 is not needed: max 0 (r - s) ≤ r unless s < 0, handled by the volume bound
      have hs0 : 0 ≤ s := s_nonneg n a b h
      have : max 0 (r - s) ≤ r := max_le r0 (by linarith)
      linarith
    · have : max 0 (r - s) ≤ b := max_le (by positivity) (by linarith)
      exact this
    · have : H - r + max 0 (r - s) - K - max 0 (r - s) = H - K - r := by ring
      rw [this]; exact hdiv
  -- Case B: s + b < g, so every winning first question has δ = f
  push_neg at hA
  have hs0 : 0 ≤ s := s_nonneg n a b h
  rcases Nat.eq_zero_or_pos (a + b) with hab | hab
  · -- empty state: t = K = 0 works
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst ha hb
    refine ⟨0, 0, ?_, by positivity, le_refl _, by simp, by simp⟩
    have h0 : (V (n + 1) ⟨0, 0 + 0, 0⟩ : ℤ) = 0 := by simp [V]
    rw [h0, pow_succ]; have := pow_pos (by norm_num : (0 : ℤ) < 2) n; linarith
  cases h with
  | win hw => simp [St.size] at hw; omega
  | step q0 q1 q2 h0 h1 h2 hY hN =>
    simp only at h0 h1 h2
    have hq2 : q2 = 0 := by omega
    subst hq2
    set d : ℤ := (q0 : ℤ) - a with hd
    set f : ℤ := (q1 : ℤ) - b with hf
    set δ : ℤ := ((n + 1).choose 2 : ℕ) * d + (n + 1) * f with hδ
    have hC : (((n + 1).choose 2 : ℕ) : ℤ) = (n.choose 2 : ℕ) + n := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]; push_cast; ring
    have hW1 : (W (n + 1) : ℤ) = (((n + 1).choose 2 : ℕ) : ℤ) + n + 2 := by
      simp only [W]; push_cast; ring
    -- the two children's volumes are V z ± δ
    have eY : (V (n + 1) (yes ⟨2 * a, 2 * b, 0⟩ q0 q1 0) : ℤ) = V (n + 1) ⟨a, a + b, b⟩ + δ := by
      simp only [V, yes]; push_cast [Nat.cast_sub h0, Nat.cast_sub h1]; rw [hW1]; ring
    have eN : (V (n + 1) (no ⟨2 * a, 2 * b, 0⟩ q0 q1 0) : ℤ) = V (n + 1) ⟨a, a + b, b⟩ - δ := by
      simp only [V, no]; push_cast [Nat.cast_sub h0, Nat.cast_sub h1]; rw [hW1]; ring
    have vY : (V (n + 1) (yes ⟨2 * a, 2 * b, 0⟩ q0 q1 0) : ℤ) ≤ 2 ^ (n + 1) := by exact_mod_cast V_le _ _ hY
    have vN : (V (n + 1) (no ⟨2 * a, 2 * b, 0⟩ q0 q1 0) : ℤ) ≤ 2 ^ (n + 1) := by exact_mod_cast V_le _ _ hN
    have hf1 : f ≤ b := by simp only [hf]; push_cast; omega
    have hf2 : -(b : ℤ) ≤ f := by simp only [hf]; omega
    -- δ = f
    have hdvd : (g : ℤ) ∣ δ - f := by
      have e : δ - f = (n.choose 2 : ℕ) * d + n * (d + f) := by rw [hδ, hC]; ring
      rw [e]
      exact dvd_add (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hgD) _)
        (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hgn) _)
    have habs : |δ - f| < g := by
      rw [abs_lt]; constructor <;> linarith
    have hδf : δ = f := by linarith [Int.eq_zero_of_abs_lt_dvd hdvd habs]
    have size2 : ∀ q0 q1 : ℕ, q0 ≤ 2 * a → q1 ≤ 2 * b →
        2 ≤ (yes ⟨2 * a, 2 * b, 0⟩ q0 q1 0).size ∧ 2 ≤ (no ⟨2 * a, 2 * b, 0⟩ q0 q1 0).size := by
      intro q0 q1 h0 h1; simp only [St.size, yes, no]; omega
    rcases le_or_gt 0 f with hf0 | hf0
    · -- the yes child wins; its root question is the witness
      obtain ⟨u, v, w, hu, hv, hw, hyY, hnY⟩ := root hY (size2 q0 q1 h0 h1).1
      have cons := V_conserve n _ u v w hu hv hw
      have tY := V_yes n (yes ⟨2 * a, 2 * b, 0⟩ q0 q1 0) u v w hu hv
      simp only [yes] at hw
      have hnY' : (V n (no (yes ⟨2 * a, 2 * b, 0⟩ q0 q1 0) u v w) : ℤ) ≤ 2 ^ n := by exact_mod_cast hnY
      have hyY' : (V n (yes (yes ⟨2 * a, 2 * b, 0⟩ q0 q1 0) u v w) : ℤ) ≤ 2 ^ n := by exact_mod_cast hyY
      have cons' : (V (n + 1) (yes ⟨2 * a, 2 * b, 0⟩ q0 q1 0) : ℤ) =
          V n (yes (yes ⟨2 * a, 2 * b, 0⟩ q0 q1 0) u v w) + V n (no (yes ⟨2 * a, 2 * b, 0⟩ q0 q1 0) u v w) := by
        exact_mod_cast cons
      refine ⟨V n (yes (yes ⟨2 * a, 2 * b, 0⟩ q0 q1 0) u v w) - f, w, ?_, ?_, by positivity, ?_, ?_⟩
      · rw [pow_succ] at *; linarith
      · linarith
      · have : (w : ℤ) ≤ 2 * b - q1 := by push_cast [Nat.cast_sub h1] at hw ⊢; omega
        simp only [hf] at hf0; push_cast at this; linarith
      · rw [tY]
        have e : ((n.choose 2 : ℕ) : ℤ) * u + n * v + (n + 1) * ((yes ⟨2 * a, 2 * b, 0⟩ q0 q1 0).a : ℤ)
            + ((yes ⟨2 * a, 2 * b, 0⟩ q0 q1 0).b : ℤ) + w - f - ((n + 2) * a + b) - w
            = ((n.choose 2 : ℕ) : ℤ) * u + n * (v + d) := by
          simp only [yes]; push_cast [Nat.cast_sub h0]; simp only [hd, hf]; ring
        rw [e]
        exact dvd_add (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hgD) _)
          (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hgn) _)
    · -- the no child wins
      obtain ⟨u, v, w, hu, hv, hw, hyN, hnN⟩ := root hN (size2 q0 q1 h0 h1).2
      have cons := V_conserve n _ u v w hu hv hw
      have tN := V_yes n (no ⟨2 * a, 2 * b, 0⟩ q0 q1 0) u v w hu hv
      simp only [no] at hw
      have hnN' : (V n (no (no ⟨2 * a, 2 * b, 0⟩ q0 q1 0) u v w) : ℤ) ≤ 2 ^ n := by exact_mod_cast hnN
      have hyN' : (V n (yes (no ⟨2 * a, 2 * b, 0⟩ q0 q1 0) u v w) : ℤ) ≤ 2 ^ n := by exact_mod_cast hyN
      have cons' : (V (n + 1) (no ⟨2 * a, 2 * b, 0⟩ q0 q1 0) : ℤ) =
          V n (yes (no ⟨2 * a, 2 * b, 0⟩ q0 q1 0) u v w) + V n (no (no ⟨2 * a, 2 * b, 0⟩ q0 q1 0) u v w) := by
        exact_mod_cast cons
      refine ⟨V n (yes (no ⟨2 * a, 2 * b, 0⟩ q0 q1 0) u v w) + f, w, ?_, ?_, by positivity, ?_, ?_⟩
      · rw [pow_succ] at *; linarith
      · linarith
      · have : (w : ℤ) ≤ q1 := by exact_mod_cast (by omega : w ≤ q1)
        simp only [hf] at hf0; linarith
      · rw [tN]
        have e : ((n.choose 2 : ℕ) : ℤ) * u + n * v + (n + 1) * ((no ⟨2 * a, 2 * b, 0⟩ q0 q1 0).a : ℤ)
            + ((no ⟨2 * a, 2 * b, 0⟩ q0 q1 0).b : ℤ) + w + f - ((n + 2) * a + b) - w
            = ((n.choose 2 : ℕ) : ℤ) * u + n * (v - d) := by
          simp only [no]; push_cast [Nat.cast_sub h0, Nat.cast_sub h1]; simp only [hd, hf]; ring
        rw [e]
        exact dvd_add (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hgD) _)
          (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hgn) _)

end UlamHalving
