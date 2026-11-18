import LeanProofs.Hankel456683.Defs

/-!
# Weighted Motzkin paths: basic facts

* `walk_eq_zero_of_lt`, `walk_top`: a path of length `n` from `l` ends at height `≤ l + n`, and
  exactly one path (all up steps, weight `1`) ends at `l + n`.
* `walk_add`: cutting a path of length `i + j` after `i` steps (Chapman-Kolmogorov).
* `walk_succ_left`: the first-step recursion
  `walk (j+1) l k = walk j (l-1) k + s l * walk j l k + walk j (l+1) k`.
* `pow_add_algebraMap_apply`: `((X + c)^m v) k = ∑_j C(m,j) c^(m-j) (X^j v) k` for a linear
  operator `X` on sequences, from the binomial theorem (`c` commutes with `X`).
* `walk_add_const`: the binomial transform of Step 1,
  `walk (s + c) n l k = ∑_j C(n,j) c^(n-j) walk s j l k`, proved as in the answer: the transfer
  operator of `s + c` is `T s + c`, and `(T s + c)^n` is expanded by the binomial theorem.
-/

namespace Hankel456683

open Finset

variable {R : Type*} [CommRing R]

@[simp] theorem walk_zero (s : ℕ → R) (l k : ℕ) : walk s 0 l k = if l = k then 1 else 0 := rfl

theorem walk_succ (s : ℕ → R) (n l k : ℕ) :
    walk s (n + 1) l k =
      (if k = 0 then 0 else walk s n l (k - 1)) + s k * walk s n l k + walk s n l (k + 1) := rfl

/-- No path of length `n` from `l` reaches a height above `l + n`. -/
theorem walk_eq_zero_of_lt (s : ℕ → R) : ∀ n l k, l + n < k → walk s n l k = 0
  | 0, l, k, h => by simp only [walk_zero]; rw [ite_eq_right (by omega)]
  | n + 1, l, k, h => by
    rw [walk_succ, walk_eq_zero_of_lt s n l k (by omega),
      walk_eq_zero_of_lt s n l (k + 1) (by omega), ite_eq_right (by omega),
      walk_eq_zero_of_lt s n l (k - 1) (by omega)]
    ring

/-- Exactly one path of length `n` from `l` to `l + n`: all steps up. -/
theorem walk_top (s : ℕ → R) : ∀ n l, walk s n l (l + n) = 1
  | 0, l => by simp
  | n + 1, l => by
    rw [walk_succ, ite_eq_right (by omega), show l + (n + 1) - 1 = l + n by omega, walk_top s n l,
      walk_eq_zero_of_lt s n l _ (by omega), walk_eq_zero_of_lt s n l _ (by omega)]
    ring

/-- Cutting a path of length `i + j` after `i` steps. -/
theorem walk_add (s : ℕ → R) (i l : ℕ) :
    ∀ j k, walk s (i + j) l k = ∑ m ∈ range (l + i + 1), walk s i l m * walk s j m k
  | 0, k => by
    simp only [add_zero, walk_zero, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    split_ifs with hk
    · rfl
    · exact walk_eq_zero_of_lt s i l k (by simp at hk; omega)
  | j + 1, k => by
    rw [← add_assoc, walk_succ, walk_add s i l j k, walk_add s i l j (k + 1)]
    simp only [walk_succ, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    split_ifs with hk
    · simp only [mul_zero, Finset.sum_const_zero, zero_add]
      congr 1
      exact Finset.sum_congr rfl fun m _ => by ring
    · rw [walk_add s i l j (k - 1)]
      congr 1
      congr 1
      exact Finset.sum_congr rfl fun m _ => by ring

/-- The first-step recursion. -/
theorem walk_succ_left (s : ℕ → R) :
    ∀ j l k, walk s (j + 1) l k =
      (if l = 0 then 0 else walk s j (l - 1) k) + s l * walk s j l k + walk s j (l + 1) k
  | 0, l, k => by
    rcases l with _ | l <;> rcases k with _ | k <;> simp only [walk_succ, walk_zero] <;>
      split_ifs <;> simp_all
  | j + 1, l, k => by
    have ih := walk_succ_left s j
    rw [walk_succ s (j + 1) l k]
    rcases k with _ | k <;> rcases l with _ | l <;>
      simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    · conv_lhs => rw [ih 0 0, ih 0 1]
      conv_rhs => rw [walk_succ s j 0 0, walk_succ s j 1 0]
      simp only [↓reduceIte]
      ring
    · conv_lhs => rw [ih (l + 1) 0, ih (l + 1) 1]
      conv_rhs => rw [walk_succ s j l 0, walk_succ s j (l + 1) 0, walk_succ s j (l + 1 + 1) 0]
      simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      ring
    · conv_lhs => rw [ih 0 k, ih 0 (k + 1), ih 0 (k + 1 + 1)]
      conv_rhs => rw [walk_succ s j 0 (k + 1), walk_succ s j 1 (k + 1)]
      simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      ring
    · conv_lhs => rw [ih (l + 1) k, ih (l + 1) (k + 1), ih (l + 1) (k + 1 + 1)]
      conv_rhs => rw [walk_succ s j l (k + 1), walk_succ s j (l + 1) (k + 1),
        walk_succ s j (l + 1 + 1) (k + 1)]
      simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
      ring

/-- The transfer operator of the weights `s`, acting on sequences by the last-step recursion. -/
def T (s : ℕ → R) : Module.End R (ℕ → R) where
  toFun f k := (if k = 0 then 0 else f (k - 1)) + s k * f k + f (k + 1)
  map_add' f g := by
    funext k; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' r f := by
    funext k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

theorem walk_eq_pow (s : ℕ → R) (n l k : ℕ) :
    walk s n l k = (((T s) ^ n) (Pi.single l 1)) k := by
  induction n generalizing k with
  | zero => simp [Pi.single_apply, eq_comm]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, walk_succ]
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, ih]

/-- The transfer operator of `s + c` is `T s + c`. -/
theorem T_add_const (s : ℕ → R) (c : R) :
    T (fun h => s h + c) = T s + algebraMap R (Module.End R (ℕ → R)) c := by
  refine LinearMap.ext fun f => funext fun k => ?_
  simp only [T, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Pi.add_apply,
    Module.algebraMap_end_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The binomial theorem for `X + c` applied to a sequence. -/
theorem pow_add_algebraMap_apply (X : Module.End R (ℕ → R)) (c : R) (m : ℕ) (v : ℕ → R)
    (k : ℕ) :
    (((X + algebraMap R _ c) ^ m) v) k =
      ∑ j ∈ range (m + 1), (m.choose j : R) * c ^ (m - j) * ((X ^ j) v) k := by
  rw [(Algebra.commute_algebraMap_right c X).add_pow, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← map_pow, Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply,
    Module.algebraMap_end_apply, map_smul, map_nsmul, Pi.smul_apply, Pi.smul_apply,
    nsmul_eq_mul, smul_eq_mul]
  ring

/-- Step 1 (binomial transform in `c`):
`walk (s + c) n l k = ∑_j C(n,j) c^(n-j) walk s j l k`. -/
theorem walk_add_const (s : ℕ → R) (c : R) (n l k : ℕ) :
    walk (fun h => s h + c) n l k =
      ∑ j ∈ range (n + 1), (n.choose j : R) * c ^ (n - j) * walk s j l k := by
  rw [walk_eq_pow, T_add_const, pow_add_algebraMap_apply]
  simp only [walk_eq_pow]

end Hankel456683
