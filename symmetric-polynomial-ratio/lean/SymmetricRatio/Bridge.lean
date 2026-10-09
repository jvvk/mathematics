import SymmetricRatio.Main
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Data.Sym.Card

/-!
# MO 467261: bridge to `MvPolynomial.hsymm`

`h_ℓ(1^{[n-t]}, x^{[t]})`, i.e. `MvPolynomial.hsymm (Fin n) ℝ ℓ` evaluated at the vector whose
first `n - t` entries are `1` and the rest `x`, equals `H N ℓ t x` (`n = N + 1`). The count goes
through the recursion `h_{ℓ+1}(z_0, z) = z_0 h_ℓ(z_0, z) + h_{ℓ+1}(z)` (split on whether the
multiset uses the first variable).
-/

open Polynomial Finset

namespace Haddou

/-- `h_ℓ` evaluated at `v`, as a sum over multisets of size `ℓ`. -/
noncomputable def S {α : Type*} [Fintype α] [DecidableEq α] (ℓ : ℕ) (v : α → ℝ) : ℝ :=
  ∑ s : Sym α ℓ, ((s : Multiset α).map v).prod

lemma eval_hsymm {α : Type*} [Fintype α] [DecidableEq α] (ℓ : ℕ) (v : α → ℝ) :
    MvPolynomial.eval v (MvPolynomial.hsymm α ℝ ℓ) = S ℓ v := by
  simp only [MvPolynomial.hsymm, map_sum, map_multiset_prod, Multiset.map_map, S]
  refine Fintype.sum_congr _ _ fun s => ?_
  congr 1
  refine Multiset.map_congr rfl fun j _ => ?_
  simp

lemma S_zero {α : Type*} [Fintype α] [DecidableEq α] (v : α → ℝ) : S 0 v = 1 := by
  have h : ((default : Sym α 0) : Multiset α) = 0 := Multiset.card_eq_zero.1 (default : Sym α 0).2
  simp [S, h]

lemma S_equiv {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (ℓ : ℕ) (w : β → ℝ) : S ℓ w = S ℓ (w ∘ e) := by
  unfold S
  refine (Fintype.sum_equiv (Sym.equivCongr e) _ _ fun s => ?_).symm
  simp [Sym.equivCongr, Multiset.map_map]

lemma S_option_succ {α : Type*} [Fintype α] [DecidableEq α] (ℓ : ℕ) (v : Option α → ℝ) :
    S (ℓ + 1) v = v none * S ℓ v + S (ℓ + 1) (v ∘ some) := by
  unfold S
  rw [← Fintype.sum_equiv (symOptionSuccEquiv).symm _ _ (fun _ => rfl), Fintype.sum_sum_type,
    Finset.mul_sum]
  congr 1
  · refine Fintype.sum_congr _ _ fun s => ?_
    simp [symOptionSuccEquiv, Sym.coe_cons]
  · refine Fintype.sum_congr _ _ fun s => ?_
    simp [symOptionSuccEquiv, Multiset.map_map]

lemma S_fin_succ (m ℓ : ℕ) (v : Fin (m + 1) → ℝ) :
    S (ℓ + 1) v = v 0 * S ℓ v + S (ℓ + 1) (v ∘ Fin.succ) := by
  rw [S_equiv (finSuccEquiv m).symm (ℓ + 1) v, S_option_succ, ← S_equiv (finSuccEquiv m).symm ℓ v]
  congr 2

lemma S_fin_zero (ℓ : ℕ) (v : Fin 0 → ℝ) : S (ℓ + 1) v = 0 := by
  simp [S]

lemma S_const (x : ℝ) : ∀ q ℓ : ℕ, S ℓ (fun _ : Fin q => x) = (q.multichoose ℓ : ℝ) * x ^ ℓ := by
  intro q
  induction q with
  | zero => intro ℓ; cases ℓ <;> simp [S_zero, S_fin_zero, Nat.multichoose_zero_succ]
  | succ q ihq =>
    intro ℓ
    induction ℓ with
    | zero => simp [S_zero]
    | succ ℓ ihl =>
      rw [S_fin_succ, ihl]
      have := ihq (ℓ + 1)
      simp only [Function.comp_def] at this ⊢
      rw [this, Nat.multichoose_succ_succ]; push_cast; ring

/-- The closed form: `∑_k C(p+q+ℓ-1, ℓ-k) · multichoose(q,k) · (x-1)^k`. -/
noncomputable def Hf (p q ℓ : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (ℓ + 1), (((p + q + ℓ - 1).choose (ℓ - k) : ℕ) : ℝ) * (q.multichoose k : ℝ) * (x - 1) ^ k

lemma Hf_zero (p q : ℕ) (x : ℝ) : Hf p q 0 x = 1 := by
  simp [Hf, Nat.multichoose_zero_right]

lemma Hf_rec (p q ℓ : ℕ) (x : ℝ) : Hf (p + 1) q (ℓ + 1) x = Hf (p + 1) q ℓ x + Hf p q (ℓ + 1) x := by
  unfold Hf
  rw [Finset.sum_range_succ _ (ℓ + 1), Finset.sum_range_succ (fun k => _ * _ * (x - 1) ^ k) (ℓ + 1),
    show p + 1 + q + (ℓ + 1) - 1 = p + q + ℓ + 1 by omega, show p + 1 + q + ℓ - 1 = p + q + ℓ by omega,
    show p + q + (ℓ + 1) - 1 = p + q + ℓ by omega, Nat.sub_self, Nat.choose_zero_right,
    Nat.choose_zero_right, ← add_assoc, add_left_inj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ ℓ := Nat.lt_succ_iff.1 (mem_range.1 hk)
  rw [show ℓ + 1 - k = (ℓ - k) + 1 by omega, Nat.choose_succ_succ]
  push_cast; ring

/-- Base case: all `q` variables equal to `x` gives `multichoose(q,ℓ) x^ℓ`. -/
lemma Hf_base (q ℓ : ℕ) (x : ℝ) : Hf 0 q ℓ x = (q.multichoose ℓ : ℝ) * x ^ ℓ := by
  have key : ∀ k ∈ range (ℓ + 1), (((0 + q + ℓ - 1).choose (ℓ - k) : ℕ) : ℝ) * (q.multichoose k : ℝ) =
      (q.multichoose ℓ : ℝ) * (ℓ.choose k : ℝ) := by
    intro k hk
    have hk' : k ≤ ℓ := Nat.lt_succ_iff.1 (mem_range.1 hk)
    norm_cast
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · rcases Nat.eq_zero_or_pos ℓ with rfl | hl
        · simp
        · obtain ⟨l, rfl⟩ : ∃ l, ℓ = l + 1 := ⟨ℓ - 1, by omega⟩
          simp [Nat.multichoose_zero_succ]
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        obtain ⟨l, rfl⟩ : ∃ l, ℓ = l + 1 := ⟨ℓ - 1, by omega⟩
        simp [Nat.multichoose_zero_succ]
    · rw [Nat.multichoose_eq, Nat.multichoose_eq, show 0 + q + ℓ - 1 = q + ℓ - 1 by omega]
      -- C(m, ℓ-k) C(q+k-1, k) = C(m, ℓ) C(ℓ, k),  m = q + ℓ - 1
      have h := Nat.choose_mul (n := q + ℓ - 1) (k := ℓ) (s := ℓ - k) (by omega)
      rw [show q + ℓ - 1 - (ℓ - k) = q + k - 1 by omega, show ℓ - (ℓ - k) = k by omega,
        Nat.choose_symm hk'] at h
      rw [← h]
  unfold Hf
  have hx : x ^ ℓ = ((x - 1) + 1) ^ ℓ := by ring
  rw [hx, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have := key k hk
  rw [one_pow, mul_one, this]; ring

/-- The vector `(1, …, 1, x, …, x)` with `p` ones in front. -/
def vec (m p : ℕ) (x : ℝ) : Fin m → ℝ := fun j => if (j : ℕ) < p then 1 else x

lemma S_vec (x : ℝ) : ∀ p m, p ≤ m → ∀ ℓ, S ℓ (vec m p x) = Hf p (m - p) ℓ x := by
  intro p
  induction p with
  | zero =>
    intro m _ ℓ
    have : vec m 0 x = fun _ => x := by funext j; simp [vec]
    rw [this, S_const, Nat.sub_zero, Hf_base]
  | succ p ih =>
    intro m hm ℓ
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    induction ℓ with
    | zero => rw [S_zero, Hf_zero]
    | succ ℓ ihl =>
      rw [S_fin_succ, ihl, show m' + 1 - (p + 1) = m' - p by omega, Hf_rec]
      have h0 : vec (m' + 1) (p + 1) x 0 = 1 := by simp [vec]
      have hs : vec (m' + 1) (p + 1) x ∘ Fin.succ = vec m' p x := by
        funext j; simp [vec, Fin.val_succ]
      rw [h0, hs, ih m' (by omega) (ℓ + 1), one_mul]

/-- `h_ℓ(1^{[n-t]}, x^{[t]})` via Mathlib's complete homogeneous symmetric polynomial. -/
noncomputable def h (n ℓ t : ℕ) (x : ℝ) : ℝ :=
  MvPolynomial.eval (vec n (n - t) x) (MvPolynomial.hsymm (Fin n) ℝ ℓ)

lemma h_eq_H (N ℓ t : ℕ) (ht : t ≤ N + 1) (x : ℝ) : h (N + 1) ℓ t x = H N ℓ t x := by
  rw [h, eval_hsymm, S_vec x (N + 1 - t) (N + 1) (by omega), show N + 1 - (N + 1 - t) = t by omega]
  simp only [Hf, H, HP, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show N + 1 - t + t + ℓ - 1 = N + ℓ by omega]

/-- **MO 467261 (Ait-Haddou), formalised.** For `n ≥ 1`, `ℓ ≥ 1` and `1 ≤ i ≤ n - 1`,
`Ψ_{i,n}(x) = h_ℓ(1^{[n-i]}, x^{[i]})^2 / (h_ℓ(1^{[n-i-1]}, x^{[i+1]}) · h_ℓ(1^{[n-i+1]}, x^{[i-1]}))`
is strictly increasing on `(1, ∞)`. (The question asks for `2 ≤ i ≤ n - 2`.) -/
theorem ait_haddou (n ℓ i : ℕ) (hℓ : 1 ≤ ℓ) (hi : 1 ≤ i) (hin : i + 1 ≤ n) :
    StrictMonoOn (fun x => h n ℓ i x ^ 2 / (h n ℓ (i + 1) x * h n ℓ (i - 1) x)) (Set.Ioi 1) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have hfun : (fun x => h (N + 1) (m + 1) i x ^ 2 / (h (N + 1) (m + 1) (i + 1) x * h (N + 1) (m + 1) (i - 1) x)) =
      (fun x => H N (m + 1) i x ^ 2 / (H N (m + 1) (i + 1) x * H N (m + 1) (i - 1) x)) := by
    funext x
    rw [h_eq_H N _ i (by omega), h_eq_H N _ (i + 1) (by omega), h_eq_H N _ (i - 1) (by omega)]
  rw [hfun]
  exact psi_strictMonoOn N m i hi

end Haddou
