/-
  Stanley, MathOverflow 486548. Part L. The alternating ribbon character and `n! g(n) = Σ_w ψ(w)²`.

  `flagChar n A w` counts flags of type `A` fixed by `w`. Burnside's lemma gives
  `Σ_w flagChar A w · flagChar B w = n! · #orbits`, and `card_joint_eq_orbits` identifies the orbit
  count with `#{w : D(w) ⊆ A, D(w⁻¹) ⊆ B}`. The signed sum
  `ψ(w) = Σ_{S ⊆ alt} (-1)^|S| flagChar (alt \ S) w` (the character of the alternating ribbon) then
  satisfies `n! g(n) = Σ_w ψ(w)²` by inclusion-exclusion (`g_mul_factorial_eq`).
-/
import LeanProofs.Stanley.DoubleCoset
import LeanProofs.Stanley.EulerCount

namespace Stanley.Alt

open Finset Equiv
open scoped Nat

/-- Flags of type `A` fixed by `w`. -/
def flagChar (n : ℕ) (A : Finset ℕ) (w : Perm (Fin n)) : ℕ :=
  (univ.filter (fun f : Flag n A => w • f = f)).card

theorem flagChar_inner (n : ℕ) (A B : Finset ℕ) :
    (∑ w : Perm (Fin n), flagChar n A w * flagChar n B w) = Nat.card (FQ n A B) * n ! := by
  classical
  let : Fintype (FQ n A B) := Fintype.ofFinite _
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Perm (Fin n)) (Flag n A × Flag n B)
  have hp (w : Perm (Fin n)) :
      Fintype.card (MulAction.fixedBy (Flag n A × Flag n B) w) = flagChar n A w * flagChar n B w := by
    rw [Fintype.card_congr (fixedByProdEquiv w), Fintype.card_prod]
    unfold flagChar
    rw [Fintype.card_subtype, Fintype.card_subtype]
    rfl
  simpa only [hp, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] using h

/-- The alternating ribbon character. -/
def ψ (n : ℕ) (w : Perm (Fin n)) : ℤ :=
  ∑ S ∈ (altS n).powerset, (-1 : ℤ) ^ S.card * (flagChar n (altS n \ S) w : ℤ)

theorem g_mul_factorial_eq (n : ℕ) :
    (g n : ℤ) * n ! = ∑ w : Perm (Fin n), ψ n w ^ 2 := by
  have hg := g_inclusion_exclusion n
  have hR : (g n : ℝ) = ∑ S ∈ (altS n).powerset, ∑ T ∈ (altS n).powerset,
      (-1 : ℝ) ^ (S.card + T.card) * (Nat.card (FQ n (altS n \ S) (altS n \ T)) : ℝ) := by
    rw [hg]
    refine Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun T _ => ?_
    rw [card_joint_eq_orbits]
  have hsq : ∑ w : Perm (Fin n), ψ n w ^ 2 = ∑ S ∈ (altS n).powerset, ∑ T ∈ (altS n).powerset,
      (-1 : ℤ) ^ (S.card + T.card) * ((Nat.card (FQ n (altS n \ S) (altS n \ T)) * n ! : ℕ) : ℤ) := by
    simp_rw [pow_two, ψ, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [← flagChar_inner, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    push_cast; rw [pow_add]; ring
  have : ((g n : ℤ) * n ! : ℝ) = ((∑ w : Perm (Fin n), ψ n w ^ 2 : ℤ) : ℝ) := by
    rw [hsq]; push_cast; rw [hR, Finset.sum_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  exact_mod_cast this

end Stanley.Alt

/-! ### The identity: `ψ(1) = E_n` -/

namespace Stanley.Alt

open Finset Equiv
open scoped Nat

/-- With the full block set, flags are bijective labellings and the action is free and
transitive, so orbits of pairs are flags of the first type. -/
theorem card_orbits_full (n : ℕ) (A : Finset ℕ) :
    Nat.card (FQ n A (range (n - 1))) = Fintype.card (Flag n A) := by
  classical
  have hfull : ∀ p : Fin n, (blk n (range (n - 1)) p : ℕ) = p := by
    intro p
    rw [blk_val]; unfold block
    have : (range (n - 1)).filter (· < (p : ℕ)) = range p := by
      ext r; simp only [Finset.mem_filter, Finset.mem_range]; constructor
      · rintro ⟨_, h⟩; exact h
      · intro h; exact ⟨by omega, h⟩
    rw [this, card_range]
  have hinj : Function.Injective (blk n (range (n - 1))) := fun a b h => by
    have := congrArg Fin.val h; rw [hfull, hfull] at this; exact Fin.ext this
  rw [← Nat.card_eq_fintype_card]
  symm
  apply Nat.card_eq_of_bijective
    (fun f : Flag n A => Quotient.mk (MulAction.orbitRel _ _) (f, canon n (range (n - 1))))
  constructor
  · intro f f' h
    simp only at h
    rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
    obtain ⟨σ, hσ⟩ := h
    have h2 : ∀ p, blk n (range (n - 1)) (σ⁻¹ p) = blk n (range (n - 1)) p := fun p =>
      congrFun (congrArg (fun x : Flag n A × Flag n (range (n - 1)) => x.2.1) hσ) p
    have hσ1 : σ = 1 := by
      have : σ⁻¹ = 1 := Equiv.ext fun p => hinj (h2 p)
      simpa using this
    have h1 := congrArg Prod.fst hσ
    rw [hσ1, one_smul] at h1
    exact h1.symm
  · intro q
    induction q using Quotient.inductionOn with
    | h x =>
    obtain ⟨f, g⟩ := x
    obtain ⟨π, hπ⟩ := exists_perm_of_flag g
    refine ⟨π • f, ?_⟩
    simp only
    have hg : π • g = canon n (range (n - 1)) := Subtype.ext (by
      funext p; rw [smul_val]; simp [hπ, canon])
    rw [← hg, ← Prod.smul_mk, mk_smul]

/-- `#{w : D(w) ⊆ A}` is the number of flags of type `A`. -/
theorem card_descP_subset (n : ℕ) (A : Finset ℕ) :
    ((univ : Finset (Perm (Fin n))).filter (fun w => descP w ⊆ A)).card = Fintype.card (Flag n A) := by
  rw [← card_orbits_full, ← card_joint_eq_orbits]
  unfold jointSubsetCount
  congr 1
  exact Finset.filter_congr fun w _ => ⟨fun h => ⟨h, Finset.filter_subset _ _⟩, fun h => h.1⟩

theorem flagChar_one (n : ℕ) (A : Finset ℕ) : flagChar n A 1 = Fintype.card (Flag n A) := by
  unfold flagChar; simp

/-- **The identity value.** `ψ(1) = E_n`. -/
theorem ψ_one (n : ℕ) : ψ n 1 = E n := by
  have hE := E_eq_card_alternating n
  unfold ψ
  simp_rw [flagChar_one, ← card_descP_subset]
  have key : ∀ w : Perm (Fin n),
      (∑ S ∈ (altS n).powerset, (-1 : ℝ) ^ S.card * if descP w ⊆ altS n \ S then 1 else 0) =
        if descP w = altS n then 1 else 0 := fun w => descent_indicator (altS n) (descP w)
  have hR : ((∑ S ∈ (altS n).powerset, (-1 : ℤ) ^ S.card *
      (((univ : Finset (Perm (Fin n))).filter (fun w => descP w ⊆ altS n \ S)).card : ℤ) : ℤ) : ℝ) =
      (E n : ℝ) := by
    push_cast
    simp_rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ w : Perm (Fin n), (∑ S ∈ (altS n).powerset, (-1 : ℝ) ^ S.card *
        ((if descP w ⊆ altS n \ S then 1 else 0 : ℕ) : ℝ)) = if descP w = altS n then 1 else 0 := by
      intro w; rw [← key w]; refine Finset.sum_congr rfl fun S _ => ?_; split_ifs <;> simp
    simp_rw [this]
    rw [hE, Finset.card_filter]; push_cast; rfl
  exact_mod_cast hR

end Stanley.Alt
