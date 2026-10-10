import Mathlib

/-!
# Sixteen words cover all 15-bit strings (MO 142857)

A set `S` of binary words covers length `n` if every binary word of length `n` has a subsequence in `S`. The
16-word cover of length 15 by words of length 10 is a finite certificate, checked by two independent programs; this
file proves the argument that turns it into the bound on the growth rate.

* `covers_append`: concatenating a cover for length `n₁` with a cover for length `n₂` covers length `n₁ + n₂`, with
  at most `|S| |T|` words (`card_append_le`): the block argument.
* `covers_pow`: a cover of length `n` by `c` words of length `m` gives, for every `k`, a cover of length `k n` by at
  most `c^k` words of length `k m`.
* `rate_16`, `rate_17`: `1.2030 < 16^(1/15) < 1.2031 < 1.2078 < 17^(1/15)`.
-/

namespace DeletionCover

open Finset

/-- Every binary word of length `n` has a subsequence in `S`. -/
def Covers (S : Finset (List Bool)) (n : ℕ) : Prop := ∀ x : List Bool, x.length = n → ∃ y ∈ S, y.Sublist x

/-- All words of `S` have length `m`. -/
def Uniform (S : Finset (List Bool)) (m : ℕ) : Prop := ∀ y ∈ S, y.length = m

/-- Concatenations of a word of `S` and a word of `T`. -/
def cat (S T : Finset (List Bool)) : Finset (List Bool) := (S ×ˢ T).image fun p => p.1 ++ p.2

/-- The block argument: split a word of length `n₁ + n₂` into its first `n₁` letters and the rest. -/
theorem covers_append {S T : Finset (List Bool)} {n₁ n₂ : ℕ} (hS : Covers S n₁) (hT : Covers T n₂) :
    Covers (cat S T) (n₁ + n₂) := by
  intro x hx
  obtain ⟨y₁, hy₁, h₁⟩ := hS (x.take n₁) (by simp [hx])
  obtain ⟨y₂, hy₂, h₂⟩ := hT (x.drop n₁) (by simp [hx])
  refine ⟨y₁ ++ y₂, mem_image.mpr ⟨(y₁, y₂), mem_product.mpr ⟨hy₁, hy₂⟩, rfl⟩, ?_⟩
  rw [← List.take_append_drop n₁ x]
  exact h₁.append h₂

theorem uniform_append {S T : Finset (List Bool)} {m₁ m₂ : ℕ} (hS : Uniform S m₁) (hT : Uniform T m₂) :
    Uniform (cat S T) (m₁ + m₂) := by
  intro y hy
  obtain ⟨⟨y₁, y₂⟩, hp, rfl⟩ := mem_image.mp hy
  obtain ⟨h₁, h₂⟩ := mem_product.mp hp
  simp [hS y₁ h₁, hT y₂ h₂]

theorem card_append_le (S T : Finset (List Bool)) : (cat S T).card ≤ S.card * T.card :=
  card_image_le.trans (card_product S T).le

/-- The `k`-fold block construction. -/
theorem covers_pow {S : Finset (List Bool)} {n m : ℕ} (hS : Covers S n) (hU : Uniform S m) (k : ℕ) :
    ∃ T : Finset (List Bool), Covers T (k * n) ∧ Uniform T (k * m) ∧ T.card ≤ S.card ^ k := by
  induction k with
  | zero =>
    refine ⟨{[]}, fun x hx => ⟨[], mem_singleton_self _, List.nil_sublist x⟩, ?_, by simp⟩
    intro y hy; simp at hy; simp [hy]
  | succ k ih =>
    obtain ⟨T, hT, hTU, hTc⟩ := ih
    refine ⟨cat T S, ?_, ?_, ?_⟩
    · have := covers_append hT hS; rwa [show k * n + n = (k + 1) * n by ring] at this
    · have := uniform_append hTU hU; rwa [show k * m + m = (k + 1) * m by ring] at this
    · calc (cat T S).card ≤ T.card * S.card := card_append_le T S
        _ ≤ S.card ^ k * S.card := Nat.mul_le_mul_right _ hTc
        _ = S.card ^ (k + 1) := (pow_succ _ _).symm

/-! ### The minimum `H(n, b)` and the growth rate -/

/-- All binary words of length `m`. -/
def words (m : ℕ) : Finset (List Bool) := (univ : Finset (Fin m → Bool)).image List.ofFn

theorem mem_words {m : ℕ} {y : List Bool} : y ∈ words m ↔ y.length = m := by
  constructor
  · intro h; obtain ⟨f, -, rfl⟩ := mem_image.mp h; simp
  · intro h; exact mem_image.mpr ⟨fun i => y.get (i.cast h.symm), mem_univ _, by
      apply List.ext_get <;> simp [h]⟩

/-- All words of length `n - b` cover length `n`: keep the first `n - b` letters. -/
theorem covers_words (n b : ℕ) : Covers (words (n - b)) n := by
  intro x hx
  exact ⟨x.take (n - b), mem_words.mpr (by simp [hx]), List.take_sublist _ _⟩

/-- `H(n, b)`: the fewest words of length `n - b` that cover length `n`. -/
noncomputable def H (n b : ℕ) : ℕ :=
  sInf {c | ∃ S : Finset (List Bool), Covers S n ∧ Uniform S (n - b) ∧ S.card = c}

theorem H_spec (n b : ℕ) : ∃ S : Finset (List Bool), Covers S n ∧ Uniform S (n - b) ∧ S.card = H n b :=
  Nat.sInf_mem (s := {c | ∃ S : Finset (List Bool), Covers S n ∧ Uniform S (n - b) ∧ S.card = c})
    ⟨(words (n - b)).card, words (n - b), covers_words n b, fun _ hy => mem_words.mp hy, rfl⟩

theorem H_le {n b : ℕ} {S : Finset (List Bool)} (hS : Covers S n) (hU : Uniform S (n - b)) : H n b ≤ S.card :=
  Nat.sInf_le ⟨S, hS, hU, rfl⟩

theorem H_pos (n b : ℕ) : 0 < H n b := by
  obtain ⟨S, hS, -, hc⟩ := H_spec n b
  obtain ⟨y, hy, -⟩ := hS (List.replicate n false) (by simp)
  rw [← hc]; exact card_pos.mpr ⟨y, hy⟩

/-- Submultiplicativity, from the block argument. -/
theorem H_mul {n₁ b₁ n₂ b₂ : ℕ} (h₁ : b₁ ≤ n₁) (h₂ : b₂ ≤ n₂) :
    H (n₁ + n₂) (b₁ + b₂) ≤ H n₁ b₁ * H n₂ b₂ := by
  obtain ⟨S, hS, hSU, hSc⟩ := H_spec n₁ b₁
  obtain ⟨T, hT, hTU, hTc⟩ := H_spec n₂ b₂
  have hU := uniform_append hSU hTU
  rw [show n₁ - b₁ + (n₂ - b₂) = n₁ + n₂ - (b₁ + b₂) by omega] at hU
  calc H (n₁ + n₂) (b₁ + b₂) ≤ (cat S T).card := H_le (covers_append hS hT) hU
    _ ≤ S.card * T.card := card_append_le S T
    _ = H n₁ b₁ * H n₂ b₂ := by rw [hSc, hTc]

/-- `u k = log H(3k, k)` is subadditive. -/
theorem subadditive_log : Subadditive fun k => Real.log (H (3 * k) k) := by
  intro m k
  simp only
  rw [← Real.log_mul (by exact_mod_cast (H_pos _ _).ne') (by exact_mod_cast (H_pos _ _).ne')]
  apply Real.log_le_log (by exact_mod_cast H_pos _ _)
  have := H_mul (n₁ := 3 * m) (b₁ := m) (n₂ := 3 * k) (b₂ := k) (by omega) (by omega)
  rw [show 3 * m + 3 * k = 3 * (m + k) by ring] at this
  exact_mod_cast this

theorem bdd_log : BddBelow (Set.range fun k : ℕ => Real.log (H (3 * k) k) / k) :=
  ⟨0, by rintro _ ⟨k, rfl⟩; exact div_nonneg (Real.log_nonneg (by exact_mod_cast H_pos _ _)) (Nat.cast_nonneg k)⟩

/-- Fekete: `log H(3k, k) / k` converges, to its infimum `L`; the growth rate per bit is `α = exp(L/3)`. -/
theorem rate_exists : Filter.Tendsto (fun k : ℕ => Real.log (H (3 * k) k) / k) Filter.atTop
    (nhds subadditive_log.lim) :=
  subadditive_log.tendsto_lim bdd_log

/-- With the 16-word cover of length 15, `α = exp(L/3) ≤ 16^(1/15)`. -/
theorem alpha_le (h16 : ∃ S : Finset (List Bool), Covers S 15 ∧ Uniform S 10 ∧ S.card = 16) :
    Real.exp (subadditive_log.lim / 3) ≤ (16 : ℝ) ^ ((1 : ℝ) / 15) := by
  obtain ⟨S, hS, hU, hc⟩ := h16
  have hH : H 15 5 ≤ 16 := hc ▸ H_le hS hU
  have hlim := subadditive_log.lim_le_div bdd_log (n := 5) (by norm_num)
  simp only [show 3 * 5 = 15 by norm_num] at hlim
  have hlog : Real.log (H 15 5) ≤ Real.log 16 :=
    Real.log_le_log (by exact_mod_cast H_pos _ _) (by exact_mod_cast hH)
  rw [Real.rpow_def_of_pos (by norm_num)]
  apply Real.exp_le_exp.mpr
  push_cast at hlim
  nlinarith [hlim, hlog]

/-- `1.2030 < 16^(1/15) < 1.2031`. -/
theorem rate_16 : (1.2030 : ℝ) < (16 : ℝ) ^ ((1 : ℝ) / 15) ∧ (16 : ℝ) ^ ((1 : ℝ) / 15) < 1.2031 := by
  have h15 : (0 : ℝ) < 1 / 15 := by norm_num
  have key : ∀ a : ℝ, 0 ≤ a → (a ^ (15 : ℕ)) ^ ((1 : ℝ) / 15) = a := by
    intro a ha
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]; norm_num
  constructor
  · rw [← key 1.2030 (by norm_num)]
    exact Real.rpow_lt_rpow (by positivity) (by norm_num) h15
  · rw [← key 1.2031 (by norm_num)]
    exact Real.rpow_lt_rpow (by norm_num) (by norm_num) h15

/-- `1.2078 < 17^(1/15)`, the bound from the earlier 17-word cover. -/
theorem rate_17 : (1.2078 : ℝ) < (17 : ℝ) ^ ((1 : ℝ) / 15) := by
  have key : ((1.2078 : ℝ) ^ (15 : ℕ)) ^ ((1 : ℝ) / 15) = 1.2078 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  rw [← key]
  exact Real.rpow_lt_rpow (by positivity) (by norm_num) (by norm_num)

end DeletionCover
