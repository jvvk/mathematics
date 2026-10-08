import LeanProofs.RandPascal.TheoremA

/-!
# Randomized Pascal triangle, Theorem B (local inequality ⇒ growth)

Potential `F = S + t V + u V₂ + v W`, where `V₂ = ∑ |x_{j+2} - x_j|` and
`W = ∑ ||x_{j+2} - x_{j+1}| - |x_{j+1} - x_j||`. Summing a *local* inequality `G ≥ 0` on four
consecutive entries over all windows gives `E[F'] ≥ λ F`; hence `E[S_n] ≥ λⁿ`.

The local inequality itself, for the certificate `t = 1249/2500, u = 3/100, v = 557/2500,
λ = 5001/5000` and `p ∈ [29/125, 1]`, is the hypothesis `LocalIneq`. It is proved outside Lean by an
exact finite certificate (41 hyperplanes, 251 extreme rays, 1004 nonnegative Bernstein
coefficients), checked by two programs that share no code.
-/

open Finset

namespace RandPascal

def V2 (M : ℕ) (x : ℕ → ℝ) : ℝ := ∑ j ∈ range M, |x (j + 2) - x j|

def W (M : ℕ) (x : ℕ → ℝ) : ℝ := ∑ j ∈ range M, abs (abs (x (j + 2) - x (j + 1)) - abs (x (j + 1) - x j))

/-- Coefficients of a drift certificate. -/
structure Cert where
  t : ℝ
  u : ℝ
  v : ℝ
  lam : ℝ
  al : ℝ
  be : ℝ

def Fpot (C : Cert) (M : ℕ) (x : ℕ → ℝ) : ℝ := S M x + C.t * V M x + C.u * V2 M x + C.v * W M x

/-- Input window average. -/
noncomputable def Iloc (C : Cert) (a b c d : ℝ) : ℝ :=
  (a + b + c + d) / 4 + C.t * ((|b - a| + |c - b| + |d - c|) / 3) + C.u * ((|c - a| + |d - b|) / 2)
    + C.v * ((abs (abs (c - b) - abs (b - a)) + abs (abs (d - c) - abs (c - b))) / 2)

/-- Output window average, with the telescoping correction. -/
noncomputable def Oloc (C : Cert) (A B D : ℝ) : ℝ :=
  (A + B + D) / 3 + C.t * ((|B - A| + |D - B|) / 2) + C.u * |D - A| + C.v * abs (abs (D - B) - abs (B - A))
    - C.al * (A + D - 2 * B)

/-- The local drift `G_p(a, b, c, d)`. -/
noncomputable def Gloc (C : Cert) (p a b c d : ℝ) : ℝ :=
  E3 p (Oloc C) a b c d - C.lam * Iloc C a b c d + C.be * (a + d - b - c)

/-- The local inequality, certified outside Lean. -/
def LocalIneq (C : Cert) (p : ℝ) : Prop :=
  ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → 0 ≤ c → 0 ≤ d → 0 ≤ Gloc C p a b c d

/-! ## Shifts of the local summands on valid rows -/

section shifts
variable {m : ℕ} {x : ℕ → ℝ} (hx : Valid m x) {N : ℕ} (hN : m + 4 ≤ N)
include hx hN

lemma shX (k : ℕ) (hk : k ≤ 3) : ∑ j ∈ range N, x (j + k) = ∑ j ∈ range N, x j :=
  sum_shift x N k (fun j hj => hx.2.1 j (by omega)) (fun j hj => hx.2.2 j (by omega))

lemma shV (k : ℕ) (hk : k ≤ 2) :
    ∑ j ∈ range N, |x (j + k + 1) - x (j + k)| = ∑ j ∈ range N, |x (j + 1) - x j| := by
  have := sum_shift (fun j => |x (j + 1) - x j|) N k
    (fun j hj => by simp [hx.2.1 j (by omega), hx.2.1 (j + 1) (by omega)])
    (fun j hj => by simp [hx.2.2 j (by omega), hx.2.2 (j + 1) (by omega)])
  beta_reduce at this; exact this

lemma shV2 (k : ℕ) (hk : k ≤ 1) :
    ∑ j ∈ range N, |x (j + k + 2) - x (j + k)| = ∑ j ∈ range N, |x (j + 2) - x j| := by
  have := sum_shift (fun j => |x (j + 2) - x j|) N k
    (fun j hj => by simp [hx.2.1 j (by omega), hx.2.1 (j + 2) (by omega)])
    (fun j hj => by simp [hx.2.2 j (by omega), hx.2.2 (j + 2) (by omega)])
  beta_reduce at this; exact this

lemma shW (k : ℕ) (hk : k ≤ 1) :
    ∑ j ∈ range N, abs (abs (x (j + k + 2) - x (j + k + 1)) - abs (x (j + k + 1) - x (j + k))) =
      ∑ j ∈ range N, abs (abs (x (j + 2) - x (j + 1)) - abs (x (j + 1) - x j)) := by
  have := sum_shift (fun j => abs (abs (x (j + 2) - x (j + 1)) - abs (x (j + 1) - x j))) N k
    (fun j hj => by
      simp [hx.2.1 j (by omega), hx.2.1 (j + 1) (by omega), hx.2.1 (j + 2) (by omega)])
    (fun j hj => by
      simp [hx.2.2 j (by omega), hx.2.2 (j + 1) (by omega), hx.2.2 (j + 2) (by omega)])
  beta_reduce at this
  rw [← this]

end shifts

/-! ## Window identities -/

/-- Summing the input windows of a valid row at level `n` gives `F`. -/
lemma sum_Iloc (C : Cert) {n : ℕ} {x : ℕ → ℝ} (hx : Valid n x) :
    ∑ j ∈ range (n + 5), Iloc C (x j) (x (j + 1)) (x (j + 2)) (x (j + 3)) = Fpot C (n + 4) x := by
  have hN : n + 4 ≤ n + 5 := by omega
  have e : ∀ j, Iloc C (x j) (x (j + 1)) (x (j + 2)) (x (j + 3)) =
      (x (j + 0) + x (j + 1) + x (j + 2) + x (j + 3)) / 4
      + C.t * ((|x (j + 0 + 1) - x (j + 0)| + |x (j + 1 + 1) - x (j + 1)| +
          |x (j + 2 + 1) - x (j + 2)|) / 3)
      + C.u * ((|x (j + 0 + 2) - x (j + 0)| + |x (j + 1 + 2) - x (j + 1)|) / 2)
      + C.v * ((abs (abs (x (j + 0 + 2) - x (j + 0 + 1)) - abs (x (j + 0 + 1) - x (j + 0))) +
          abs (abs (x (j + 1 + 2) - x (j + 1 + 1)) - abs (x (j + 1 + 1) - x (j + 1)))) / 2) := by
    intro j
    simp only [Iloc]
    ring_nf
  simp only [e, sum_add_distrib, ← mul_sum, ← sum_div]
  rw [shX hx hN 0 (by norm_num), shX hx hN 1 (by norm_num), shX hx hN 2 (by norm_num),
    shX hx hN 3 (by norm_num), shV hx hN 0 (by norm_num), shV hx hN 1 (by norm_num),
    shV hx hN 2 (by norm_num), shV2 hx hN 0 (by norm_num), shV2 hx hN 1 (by norm_num),
    shW hx hN 0 (by norm_num), shW hx hN 1 (by norm_num)]
  have hS : ∑ j ∈ range (n + 5), x j = S (n + 4) x := sum_x_zero hx
  have hV : ∑ j ∈ range (n + 5), |x (j + 1) - x j| = V (n + 4) x :=
    sum_succ_zero hx _ (by simp [hx.2.2 (n + 4) (by omega), hx.2.2 (n + 5) (by omega)])
  have hV2 : ∑ j ∈ range (n + 5), |x (j + 2) - x j| = V2 (n + 4) x :=
    sum_succ_zero hx _ (by simp [hx.2.2 (n + 4) (by omega), hx.2.2 (n + 6) (by omega)])
  have hW : ∑ j ∈ range (n + 5), abs (abs (x (j + 2) - x (j + 1)) - abs (x (j + 1) - x j)) = W (n + 4) x :=
    sum_succ_zero hx _ (by
      simp [hx.2.2 (n + 4) (by omega), hx.2.2 (n + 5) (by omega), hx.2.2 (n + 6) (by omega)])
  simp only [add_zero] at *
  rw [hS, hV, hV2, hW]; unfold Fpot; ring

/-- Summing the output windows of a valid row at level `n + 1` gives `F`. -/
lemma sum_Oloc (C : Cert) {n : ℕ} {y : ℕ → ℝ} (hy : Valid (n + 1) y) :
    ∑ j ∈ range (n + 5), Oloc C (y (j + 1)) (y (j + 2)) (y (j + 3)) = Fpot C (n + 5) y := by
  have hN : n + 1 + 4 ≤ n + 5 := le_rfl
  have e : ∀ j, Oloc C (y (j + 1)) (y (j + 2)) (y (j + 3)) =
      (y (j + 1) + y (j + 2) + y (j + 3)) / 3
      + C.t * ((|y (j + 1 + 1) - y (j + 1)| + |y (j + 2 + 1) - y (j + 2)|) / 2)
      + C.u * |y (j + 1 + 2) - y (j + 1)|
      + C.v * abs (abs (y (j + 1 + 2) - y (j + 1 + 1)) - abs (y (j + 1 + 1) - y (j + 1)))
      - C.al * (y (j + 1) + y (j + 3) - 2 * y (j + 2)) := by
    intro j
    simp only [Oloc]
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_div]
  rw [shX hy hN 1 (by norm_num), shX hy hN 2 (by norm_num), shX hy hN 3 (by norm_num),
    shV hy hN 1 (by norm_num), shV hy hN 2 (by norm_num), shV2 hy hN 1 (by norm_num),
    shW hy hN 1 (by norm_num)]
  unfold Fpot S V V2 W; ring

/-! ## Theorem B from the local inequality -/

lemma V2_le_two_S {n : ℕ} {x : ℕ → ℝ} (hx : Valid n x) : V2 (n + 4) x ≤ 2 * S (n + 4) x := by
  have h2 : ∑ j ∈ range (n + 4), x (j + 2) = S (n + 4) x := by
    rw [sum_shift x (n + 4) 2 (fun j hj => hx.2.1 j (by omega)) (fun j hj => hx.2.2 j (by omega))]
    rfl
  calc V2 (n + 4) x ≤ ∑ j ∈ range (n + 4), (x (j + 2) + x j) :=
        sum_le_sum fun j _ => by
          rw [abs_le]; constructor <;> linarith [hx.1 j, hx.1 (j + 2)]
    _ = 2 * S (n + 4) x := by rw [sum_add_distrib, h2]; unfold S; ring

lemma W_le_V2 (M : ℕ) (x : ℕ → ℝ) : W M x ≤ V2 M x :=
  sum_le_sum fun j _ => by
    have := abs_abs_sub_abs_le_abs_sub (x (j + 2) - x (j + 1)) (x j - x (j + 1))
    rw [abs_sub_comm (x j)] at this
    calc _ ≤ |x (j + 2) - x (j + 1) - (x j - x (j + 1))| := this
      _ = |x (j + 2) - x j| := by ring_nf

lemma V2_x0 : V2 4 x0 = 2 := by simp [V2, x0, sum_range_succ]; norm_num

lemma W_x0 : W 4 x0 = 2 := by simp [W, x0, sum_range_succ]; norm_num

/-- **Theorem B (conditional).** A certificate with nonnegative coefficients and a valid local
inequality gives `E[S_n] ≥ λⁿ`. -/
theorem theoremB_of_local (C : Cert) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ht : 0 ≤ C.t) (hu : 0 ≤ C.u) (hv : 0 ≤ C.v) (hl : 0 ≤ C.lam) (hloc : LocalIneq C p) (n : ℕ) :
    C.lam ^ n ≤ Exp p n (S (n + 4)) := by
  let F : ℕ → (ℕ → ℝ) → ℝ := fun m y => Fpot C (m + 4) y
  have hdrift : ∀ m y, Valid m y → C.lam * F m y ≤ P p m (F (m + 1)) y := by
    intro m y hy
    have e : P p m (F (m + 1)) y = ∑ j ∈ range (m + 5), E3 p (Oloc C) (y j) (y (j + 1)) (y (j + 2))
        (y (j + 3)) := by
      rw [P_congr (h := fun z => ∑ j ∈ range (m + 5), Oloc C (z (j + 1)) (z (j + 2)) (z (j + 3)))
        (fun z hz => (sum_Oloc C hz).symm) hy]
      exact P_window p m y (Oloc C)
    have hz : ∑ j ∈ range (m + 5), (y j + y (j + 3) - y (j + 1) - y (j + 2)) = 0 := by
      simp only [sum_add_distrib, sum_sub_distrib]
      rw [shX hy (by omega : m + 4 ≤ m + 5) 1 (by norm_num),
        shX hy (by omega : m + 4 ≤ m + 5) 2 (by norm_num),
        shX hy (by omega : m + 4 ≤ m + 5) 3 (by norm_num)]
      ring
    have hsplit : ∑ j ∈ range (m + 5), Gloc C p (y j) (y (j + 1)) (y (j + 2)) (y (j + 3)) =
        ∑ j ∈ range (m + 5), E3 p (Oloc C) (y j) (y (j + 1)) (y (j + 2)) (y (j + 3))
        - C.lam * ∑ j ∈ range (m + 5), Iloc C (y j) (y (j + 1)) (y (j + 2)) (y (j + 3))
        + C.be * ∑ j ∈ range (m + 5), (y j + y (j + 3) - y (j + 1) - y (j + 2)) := by
      simp only [Gloc]
      rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
    have hsum := sum_nonneg fun j (_ : j ∈ range (m + 5)) =>
      hloc (y j) (y (j + 1)) (y (j + 2)) (y (j + 3)) (hy.1 _) (hy.1 _) (hy.1 _) (hy.1 _)
    rw [hsplit, sum_Iloc C hy, hz, mul_zero, add_zero] at hsum
    rw [e]
    show C.lam * Fpot C (m + 4) y ≤ _
    linarith
  have hgrow := Exp_growth hp0 hp1 hl F hdrift n
  set K := 1 + 2 * C.t + 2 * C.u + 2 * C.v
  have hF0 : F 0 x0 = K := by
    show Fpot C (0 + 4) x0 = K
    simp only [Fpot, zero_add, S_x0, V_x0, V2_x0, W_x0, K]; ring
  have hmono := Exp_mono hp0 hp1 n (g := F n) (h := fun y => K * S (n + 4) y) fun y hy => by
    show Fpot C (n + 4) y ≤ _
    unfold Fpot
    have h1 := V_le_two_S hy
    have h2 := V2_le_two_S hy
    have h3 := (W_le_V2 (n + 4) y).trans h2
    nlinarith [mul_le_mul_of_nonneg_left h1 ht, mul_le_mul_of_nonneg_left h2 hu,
      mul_le_mul_of_nonneg_left h3 hv]
  rw [Exp_smul] at hmono
  have hK : 0 < K := by simp only [K]; linarith
  have h := hgrow.trans hmono
  rw [hF0] at h
  exact le_of_mul_le_mul_left (by linarith) hK

/-- The main certificate. -/
noncomputable def mainCert : Cert :=
  ⟨1249 / 2500, 3 / 100, 557 / 2500, 5001 / 5000, 81 / 2500, 999 / 10000⟩

/-- The quarter certificate. -/
noncomputable def quarterCert : Cert :=
  ⟨12 / 25, 1 / 32, 1 / 5, 51 / 50, 3 / 100, 1 / 10⟩

/-- **Theorem B.** For `29/125 ≤ p ≤ 1`, given the certified local inequality,
`E[S_n] ≥ (5001/5000)ⁿ`. -/
theorem theoremB {p : ℝ} (hp0 : 29 / 125 ≤ p) (hp1 : p ≤ 1) (hloc : LocalIneq mainCert p)
    (n : ℕ) : (5001 / 5000 : ℝ) ^ n ≤ Exp p n (S (n + 4)) :=
  theoremB_of_local mainCert (by linarith) hp1 (by norm_num [mainCert]) (by norm_num [mainCert])
    (by norm_num [mainCert]) (by norm_num [mainCert]) hloc n

/-- For `1/4 ≤ p ≤ 1`, given the certified local inequality, `E[S_n] ≥ (51/50)ⁿ`. -/
theorem theoremB_quarter {p : ℝ} (hp0 : 1 / 4 ≤ p) (hp1 : p ≤ 1)
    (hloc : LocalIneq quarterCert p) (n : ℕ) : (51 / 50 : ℝ) ^ n ≤ Exp p n (S (n + 4)) :=
  theoremB_of_local quarterCert (by linarith) hp1 (by norm_num [quarterCert])
    (by norm_num [quarterCert]) (by norm_num [quarterCert]) (by norm_num [quarterCert]) hloc n

end RandPascal
