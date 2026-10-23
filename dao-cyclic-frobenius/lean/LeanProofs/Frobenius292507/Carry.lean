import LeanProofs.Frobenius292507.Defs

/-!
# MO 292507: steps 1 to 5 of the answer

* `carry`: step 1, `aᵢ xᵢ₊₁ = xᵢ + N`; `carry_b`: its wrap-around form `a_{i-1} xᵢ = x_{i-1} + N`
  with `bᵢ = a (i + n - 1)` (so `b₀ = aₙ₋₁`).
* `sum_identity`: step 2, `∑ᵢ (a_{i-1} - 1) xᵢ = nN`.
* `N_pos`: step 3, `N ≥ 1` under the gcd hypothesis.
* `coprime_x0_N`: step 4, `gcd (x₀, N) = 1` by descending induction.
* `x_cong`: step 5, `xᵢ ≡ πᵢ x₀ (mod N)` with `π₀ = 1`, `πᵢ = aᵢ⋯aₙ₋₁`.
-/

namespace Frobenius292507

open Finset

variable {n : ℕ} {a : ℕ → ℕ}

/-- The digit bound attached to `xᵢ`: `bᵢ = a_{i-1}` (indices mod `n`), written `a (i + n - 1)`. -/
def b (n : ℕ) (a : ℕ → ℕ) (i : ℕ) : ℕ := a (i + n - 1)

/-- The place value `πᵢ`: `π₀ = 1` and `πᵢ = aᵢaᵢ₊₁⋯aₙ₋₁` for `1 ≤ i`. -/
def pi (n : ℕ) (a : ℕ → ℕ) (i : ℕ) : ℕ := if i = 0 then 1 else ∏ j ∈ Ico i n, a j

/-- Sums of an `n`-periodic function over a window of length `n` do not depend on the window. -/
lemma sum_shift {f : ℕ → ℕ} (hf : ∀ i, f (i + n) = f i) (c : ℕ) :
    ∑ i ∈ range n, f (i + c) = ∑ i ∈ range n, f i := by
  induction c with
  | zero => simp
  | succ c ih =>
    have h1 := sum_range_succ' (fun i => f (i + c)) n
    have h2 := sum_range_succ (fun i => f (i + c)) n
    have h3 : f (n + c) = f c := by rw [Nat.add_comm, hf]
    beta_reduce at h1 h2
    simp only [Nat.zero_add] at h1
    have h4 : ∑ i ∈ range n, f (i + (c + 1)) = ∑ i ∈ range n, f (i + 1 + c) :=
      sum_congr rfl fun i _ => congrArg f (by omega)
    rw [h4, ← ih]
    omega

lemma prod_shift (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i) (c : ℕ) :
    ∏ j ∈ range n, a (c + j) = P n a := by
  induction c with
  | zero => simp [P]
  | succ c ih =>
    rw [← ih]
    have h1 := prod_range_succ' (fun j => a (c + j)) n
    have h2 := prod_range_succ (fun j => a (c + j)) n
    beta_reduce at h1 h2
    rw [Nat.add_zero] at h1
    rw [hper c, h1] at h2
    have h4 : ∏ j ∈ range n, a (c + 1 + j) = ∏ j ∈ range n, a (c + (j + 1)) :=
      prod_congr rfl fun j _ => congrArg a (by omega)
    rw [h4]
    exact mul_right_cancel₀ (hpos c).ne' h2

lemma P_pos (hpos : ∀ i, 0 < a i) : 0 < P n a := prod_pos fun i _ => hpos i

lemma x_periodic (hper : ∀ i, a (i + n) = a i) (i : ℕ) : x n a (i + n) = x n a i := by
  unfold x
  refine sum_congr rfl fun k _ => prod_congr rfl fun j _ => ?_
  rw [show i + n + j = (i + j) + n by omega, hper]

lemma x_mod (hper : ∀ i, a (i + n) = a i) (i : ℕ) : x n a (i % n) = x n a i :=
  Function.Periodic.map_mod_nat (x_periodic hper) i

lemma x_pos (hn : 1 ≤ n) (i : ℕ) : 1 ≤ x n a i := by
  unfold x
  have := single_le_sum (f := fun k => ∏ j ∈ range k, a (i + j)) (fun _ _ => Nat.zero_le _)
    (mem_range.2 (show 0 < n by omega))
  simpa using this

/-- **Step 1** (carry identity), in the form `aᵢ xᵢ₊₁ + 1 = xᵢ + P`. -/
lemma carry_P (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i) (i : ℕ) :
    a i * x n a (i + 1) + 1 = x n a i + P n a := by
  have hg : ∀ k, a i * ∏ j ∈ range k, a (i + 1 + j) = ∏ j ∈ range (k + 1), a (i + j) := by
    intro k
    rw [prod_range_succ', Nat.add_zero, mul_comm]
    congr 1
    exact prod_congr rfl fun j _ => congrArg a (by omega)
  unfold x
  rw [mul_sum, sum_congr rfl fun k _ => hg k]
  have h1 := sum_range_succ' (fun k => ∏ j ∈ range k, a (i + j)) n
  have h2 := sum_range_succ (fun k => ∏ j ∈ range k, a (i + j)) n
  beta_reduce at h1 h2
  rw [prod_shift hper hpos i] at h2
  simp only [range_zero, prod_empty] at h1
  omega

/-- **Step 1** (carry identity): `aᵢ xᵢ₊₁ = xᵢ + N`. -/
lemma carry (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i) (i : ℕ) :
    a i * x n a (i + 1) = x n a i + N n a := by
  have := carry_P hper hpos i
  have := P_pos (n := n) hpos
  unfold N
  omega

/-- Step 1 read backwards from `xᵢ`: `bᵢ xᵢ = x_{i-1} + N`,
with `x_{i-1}` written `x ((i + n - 1) % n)`. -/
lemma carry_b (hn : 1 ≤ n) (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i) (i : ℕ) :
    b n a i * x n a i = x n a ((i + n - 1) % n) + N n a := by
  have := carry hper hpos (i + n - 1)
  rw [show i + n - 1 + 1 = i + n by omega, x_periodic hper] at this
  rw [x_mod hper, b, this]

/-- **Step 2** (sum identity): `∑ᵢ (a_{i-1} - 1) xᵢ = nN`. -/
lemma sum_identity (hn : 1 ≤ n) (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i) :
    ∑ i ∈ range n, (b n a i - 1) * x n a i = n * N n a := by
  have hb : ∀ i, 1 ≤ b n a i := fun i => hpos _
  have h1 : ∑ i ∈ range n, (b n a i - 1) * x n a i + ∑ i ∈ range n, x n a i
      = ∑ i ∈ range n, b n a i * x n a i := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    obtain ⟨r, hr⟩ : ∃ r, b n a i = r + 1 := ⟨b n a i - 1, by have := hb i; omega⟩
    rw [hr, Nat.add_sub_cancel]
    ring
  have h2 : ∑ i ∈ range n, b n a i * x n a i = ∑ i ∈ range n, x n a i + n * N n a := by
    rw [sum_congr rfl fun i _ => carry_b hn hper hpos i, sum_add_distrib, sum_const, card_range,
      smul_eq_mul]
    congr 1
    rw [sum_congr rfl fun i _ => x_mod hper (i + n - 1)]
    have := sum_shift (f := x n a) (x_periodic hper) (n - 1)
    rw [← this]
    exact sum_congr rfl fun i _ => congrArg _ (by omega)
  omega

/-- **Step 3**: `N ≥ 1` when `gcd (x₀, …, xₙ₋₁) = 1` and `n ≥ 2`. -/
lemma N_pos (hn : 2 ≤ n) (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i)
    (hgcd : (range n).gcd (x n a) = 1) : 1 ≤ N n a := by
  by_contra hN
  have hP : P n a = 1 := by have := P_pos (n := n) hpos; unfold N at hN; omega
  have ha1 : ∀ j < n, a j = 1 := fun j hj =>
    Nat.dvd_one.1 (hP ▸ dvd_prod_of_mem a (mem_range.2 hj))
  have ha : ∀ j, a j = 1 := fun j => by
    rw [← Function.Periodic.map_mod_nat (show Function.Periodic a n from hper) j]
    exact ha1 _ (Nat.mod_lt _ (by omega))
  have hx : ∀ i, x n a i = n := fun i => by simp [x, ha]
  have : n ∣ (range n).gcd (x n a) := dvd_gcd fun i _ => (hx i).symm ▸ dvd_refl n
  rw [hgcd, Nat.dvd_one] at this
  omega

/-- **Step 4**: `gcd (x₀, N) = 1`. A common divisor of `x₀ = xₙ` and `N` divides `xₙ₋₁`,
then `xₙ₋₂`, … (by `xᵢ = aᵢ xᵢ₊₁ - N`), hence the gcd of all the `xᵢ`. -/
lemma coprime_x0_N (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i)
    (hgcd : (range n).gcd (x n a) = 1) : Nat.Coprime (x n a 0) (N n a) := by
  set g := Nat.gcd (x n a 0) (N n a)
  have hg0 : g ∣ x n a 0 := Nat.gcd_dvd_left _ _
  have hgN : g ∣ N n a := Nat.gcd_dvd_right _ _
  have desc : ∀ k ≤ n, g ∣ x n a (n - k) := by
    intro k
    induction k with
    | zero => intro _; simpa [show x n a n = x n a 0 by simpa using x_periodic hper 0] using hg0
    | succ k ih =>
      intro hk
      have hc := carry hper hpos (n - (k + 1))
      rw [show n - (k + 1) + 1 = n - k by omega] at hc
      have : g ∣ x n a (n - (k + 1)) + N n a := hc ▸ dvd_mul_of_dvd_right (ih (by omega)) _
      exact (Nat.dvd_add_left hgN).1 this
  have : g ∣ (range n).gcd (x n a) := dvd_gcd fun i hi => by
    have := desc (n - i) (by omega)
    rwa [show n - (n - i) = i by have := mem_range.1 hi; omega] at this
  rw [hgcd] at this
  exact Nat.dvd_one.1 this

/-- **Step 5**: `xᵢ ≡ πᵢ x₀ (mod N)` for `i < n`. -/
lemma x_cong (hper : ∀ i, a (i + n) = a i) (hpos : ∀ i, 0 < a i) {i : ℕ} (hi : i < n) :
    (x n a i : ZMod (N n a)) = pi n a i * x n a 0 := by
  have desc : ∀ k ≤ n,
      (x n a (n - k) : ZMod (N n a)) = (∏ j ∈ Ico (n - k) n, a j : ℕ) * x n a 0 := by
    intro k
    induction k with
    | zero => intro _; simpa using congrArg (Nat.cast (R := ZMod (N n a))) (x_periodic hper 0)
    | succ k ih =>
      intro hk
      have hc := congrArg (Nat.cast (R := ZMod (N n a))) (carry hper hpos (n - (k + 1)))
      rw [show n - (k + 1) + 1 = n - k by omega] at hc
      push_cast at hc
      rw [ZMod.natCast_self, add_zero] at hc
      rw [← hc, ih (by omega), prod_eq_prod_Ico_succ_bot (show n - (k + 1) < n by omega),
        show n - (k + 1) + 1 = n - k by omega]
      push_cast
      ring
  by_cases h0 : i = 0
  · subst h0; simp [pi]
  · have := desc (n - i) (by omega)
    rw [show n - (n - i) = i by omega] at this
    rw [this, pi, ite_eq_right h0]
end Frobenius292507
