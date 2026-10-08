/-
  Stanley, MathOverflow 486548. Part O. Fixed flags are labellings of cycles, so
  `ψ(w) = (-1)^|alt| Φ(cycle lengths of w)` (`ψ_eq_Φ`).
-/
import LeanProofs.Stanley.CycleLink
import Mathlib.Algebra.BigOperators.Ring.Nat

namespace Stanley.Alt

open Finset Equiv

variable {n : ℕ}

/-- The cycles of `w` (fixed points included). -/
abbrev cyc {α : Type*} (w : Perm α) := Quotient (Perm.SameCycle.setoid w)

noncomputable instance {α : Type*} [Finite α] (w : Perm α) : Fintype (cyc w) := Fintype.ofFinite _

noncomputable instance {α : Type*} (w : Perm α) : DecidableEq (cyc w) := Classical.decEq _

/-- Cycle lengths. -/
noncomputable def len {α : Type*} [Fintype α] (w : Perm α) (q : cyc w) : ℕ :=
  (univ.filter (fun p : α => (Quotient.mk _ p : cyc w) = q)).card

theorem len_pos (w : Perm (Fin n)) (q : cyc w) : 1 ≤ len w q := by
  obtain ⟨p, rfl⟩ := Quotient.exists_rep q
  exact Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

theorem sum_len (w : Perm (Fin n)) : ∑ q, len w q = n := by
  unfold len
  have := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (t := univ)
    (f := fun p => (Quotient.mk _ p : cyc w)) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at this
  exact this.symm

/-- A `w`-invariant labelling is constant on cycles. -/
theorem invariant_sameCycle {β : Type*} {w : Perm (Fin n)} {f : Fin n → β}
    (hf : ∀ p, f (w p) = f p) {p q : Fin n} (h : Perm.SameCycle w p q) : f p = f q := by
  obtain ⟨i, rfl⟩ := h
  have key : ∀ i : ℤ, ∀ p, f ((w ^ i) p) = f p := by
    intro i
    induction i using Int.induction_on with
    | zero => intro p; simp
    | succ i ih =>
      intro p
      rw [zpow_add_one, Perm.mul_apply, ih (w p), hf]
    | pred i ih =>
      intro p
      rw [zpow_sub_one, Perm.mul_apply, ih (w⁻¹ p)]
      have := hf (w⁻¹ p); simp at this; exact this.symm
  exact (key i p).symm

theorem fib_lift (w : Perm (Fin n)) (h : cyc w → Fin (n + 1)) (j : Fin (n + 1)) :
    fib (fun p => h (Quotient.mk _ p)) j = fibW h (len w) j := by
  unfold fib fibW len
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p => (Quotient.mk _ p : cyc w))
    (t := univ.filter (fun q => h q = j))]
  · refine Finset.sum_congr rfl fun q hq => ?_
    have hqj := (Finset.mem_filter.mp hq).2
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hp; exact hp.2
    · intro hp; exact ⟨by rw [hp]; exact hqj, hp⟩
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩

theorem smul_eq_iff {A : Finset ℕ} (w : Perm (Fin n)) (f : Flag n A) :
    w • f = f ↔ ∀ p, f.1 (w p) = f.1 p := by
  constructor
  · intro h p
    have := congrFun (congrArg Subtype.val h) (w p)
    rw [smul_val] at this; simpa using this.symm
  · intro h
    apply Subtype.ext; funext p
    rw [smul_val]
    have := h (w⁻¹ p); simp at this
    simpa [Function.comp_apply, Perm.inv_def] using this.symm

/-- Fixed flags of type `A` are labellings of the cycles with the right weighted fibres. -/
theorem flagChar_eq (w : Perm (Fin n)) (A : Finset ℕ) :
    flagChar n A w = (univ.filter (fun h : cyc w → Fin (n + 1) => Fits (len w) h A)).card := by
  unfold flagChar
  refine Finset.card_bij' (fun f hf => Quotient.lift f.1 (fun p q hpq =>
      invariant_sameCycle ((smul_eq_iff w f).mp (Finset.mem_filter.mp hf).2) hpq))
    (fun h hh => ⟨fun p => h (Quotient.mk _ p), fun j => by
      rw [fib_lift]; exact (Finset.mem_filter.mp hh).2 j⟩) ?_ ?_ ?_ ?_
  · intro f hf
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩
    rw [← fib_lift]
    exact f.2 j
  · intro h hh
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (smul_eq_iff w _).mpr fun p => ?_⟩
    show h (Quotient.mk _ (w p)) = h (Quotient.mk _ p)
    congr 1
    exact Quotient.sound (Perm.SameCycle.symm ⟨1, by simp⟩)
  · intro f _; rfl
  · intro h _; funext q; obtain ⟨p, rfl⟩ := Quotient.exists_rep q; rfl

/-- **The character in terms of cycles.** -/
theorem ψ_eq_Φ (w : Perm (Fin n)) (hn : 1 ≤ n) :
    ψ n w = (-1 : ℤ) ^ (altS n).card * Atoms.Φ (len w) := by
  rw [← signed_fits (len_pos w) (sum_len w).symm hn]
  unfold ψ
  simp_rw [flagChar_eq]
  -- reindex `S ↦ alt \ S`
  refine Finset.sum_nbij' (fun S => altS n \ S) (fun A => altS n \ A) ?_ ?_ ?_ ?_ ?_
  · intro S hS; simp [Finset.mem_powerset, Finset.sdiff_subset]
  · intro A hA; simp [Finset.mem_powerset, Finset.sdiff_subset]
  · intro S hS; exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hS)
  · intro A hA; exact Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hA)
  · intro S hS
    rw [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hS)]

end Stanley.Alt

/-! ### Evaluating Φ -/

namespace Stanley.Alt

open Finset Equiv

namespace Atoms

theorem Φ_congr {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    (e : κ ≃ κ') (c : κ → ℕ) (c' : κ' → ℕ) (hc : ∀ a, c' (e a) = c a) : Φ c' = Φ c := by
  unfold Φ
  rw [Fintype.card_congr e]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  refine Finset.card_bij' (fun h' _ => h' ∘ e) (fun h _ => h ∘ e.symm) ?_ ?_ ?_ ?_
  · intro h' hh
    obtain ⟨hs, hodd⟩ := (Finset.mem_filter.mp hh).2
    have hw : ∀ t, wcum c (h' ∘ e) t = wcum c' h' t := fun t => by
      unfold wcum
      rw [Finset.sum_filter, Finset.sum_filter]
      exact Fintype.sum_equiv e _ _ (fun a => by simp [Function.comp_apply, hc])
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y => ?_, fun t ht => ?_⟩
    · obtain ⟨b, hb⟩ := hs y; exact ⟨e.symm b, by simp [hb]⟩
    · rw [hw]; exact hodd t ht
  · intro h hh
    obtain ⟨hs, hodd⟩ := (Finset.mem_filter.mp hh).2
    have hw : ∀ t, wcum c' (h ∘ e.symm) t = wcum c h t := fun t => by
      unfold wcum
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Fintype.sum_equiv e.symm _ _ (fun b => ?_)
      have := hc (e.symm b); simp only [Equiv.apply_symm_apply] at this
      simp [Function.comp_apply, this]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y => ?_, fun t ht => ?_⟩
    · obtain ⟨a, ha⟩ := hs y; exact ⟨e a, by simp [ha]⟩
    · rw [hw]; exact hodd t ht
  · intro h' _; funext b; simp
  · intro h _; funext a; simp

theorem odd_wcum_iff {κ : Type*} [Fintype κ] [DecidableEq κ] {c c' : κ → ℕ}
    (hcc : ∀ a, Odd (c a) ↔ Odd (c' a)) {k : ℕ} (h : κ → Fin (k + 1)) (t : ℕ) :
    Odd (wcum c h t) ↔ Odd (wcum c' h t) := by
  unfold wcum
  rw [Finset.odd_sum_iff_odd_card_odd, Finset.odd_sum_iff_odd_card_odd]
  have : (univ.filter (fun a => (h a : ℕ) ≤ t)).filter (fun a => Odd (c a)) =
      (univ.filter (fun a => (h a : ℕ) ≤ t)).filter (fun a => Odd (c' a)) :=
    Finset.filter_congr fun a _ => hcc a
  rw [this]

theorem Φ_parity {κ : Type*} [Fintype κ] [DecidableEq κ] {c c' : κ → ℕ}
    (hcc : ∀ a, Odd (c a) ↔ Odd (c' a)) : Φ c = Φ c' := by
  unfold Φ V
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 3
  exact Finset.filter_congr fun h _ => and_congr_right fun _ =>
    forall_congr' fun t => imp_congr_right fun _ => odd_wcum_iff hcc h t

theorem Φ_card_one {κ : Type*} [Fintype κ] [DecidableEq κ] (hκ : Fintype.card κ = 1)
    (c : κ → ℕ) : Φ c = 1 := by
  unfold Φ
  rw [hκ, Finset.sum_range_one, pow_zero, one_mul]
  have : V c 0 = univ := by
    ext h
    simp only [V, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    refine ⟨fun y => ?_, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
    obtain ⟨a⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card κ)
    exact ⟨a, Fin.ext (by have := (h a).2; have := y.2; omega)⟩
  rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]; simp

end Atoms

/-- The cycles of the identity are its points. -/
noncomputable def cycOneEquiv (m : ℕ) : Fin m ≃ cyc (1 : Perm (Fin m)) :=
  Equiv.ofBijective (fun p => Quotient.mk _ p)
    ⟨fun p q h => (Perm.sameCycle_one).mp (Quotient.exact h),
     fun q => by obtain ⟨p, rfl⟩ := Quotient.exists_rep q; exact ⟨p, rfl⟩⟩

theorem len_one (m : ℕ) (p : Fin m) : len 1 (cycOneEquiv m p) = 1 := by
  unfold len cycOneEquiv
  rw [Finset.card_eq_one]
  refine ⟨p, ?_⟩
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    Equiv.ofBijective_apply]
  constructor
  · intro h; exact (Perm.sameCycle_one).mp (Quotient.exact h)
  · rintro rfl; rfl

theorem Φ_ones_sq {m : ℕ} (hm : 1 ≤ m) : Atoms.Φ (fun _ : Fin m => 1) ^ 2 = (E m : ℤ) ^ 2 := by
  have h1 := ψ_one m
  rw [ψ_eq_Φ 1 hm, Atoms.Φ_congr (cycOneEquiv m) (fun _ => 1) (len 1) (len_one m)] at h1
  rw [← h1, mul_pow, ← pow_mul, mul_comm (altS m).card 2, pow_mul]
  norm_num

end Stanley.Alt

namespace Stanley.Alt

open Finset Equiv

theorem card_subtype_ne_filter {κ : Type} [Fintype κ] [DecidableEq κ] (z : κ) (P : κ → Prop)
    [DecidablePred P] :
    (univ.filter (fun a : {a // a ≠ z} => P a.1)).card = (univ.filter (fun a => P a ∧ a ≠ z)).card := by
  refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
  · intro a ha; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2, a.2⟩
  · intro a _ b _ h; exact Subtype.ext h
  · intro b hb
    obtain ⟨hP, hz⟩ := (Finset.mem_filter.mp hb).2
    exact ⟨⟨b, hz⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩, rfl⟩

/-- **Foulkes's evaluation, atom form.** With `m` odd and `e` even positive weights,
`Φ² = E_m²` if `m` is even or `e = 0`, and `0` otherwise. -/
theorem Φ_eval : ∀ (e : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ] [Nonempty κ] (c : κ → ℕ),
    (∀ a, 1 ≤ c a) → (univ.filter (fun a => Even (c a))).card = e →
    Atoms.Φ c ^ 2 = if Even (univ.filter (fun a => Odd (c a))).card ∨ e = 0
      then (E (univ.filter (fun a => Odd (c a))).card : ℤ) ^ 2 else 0 := by
  intro e
  induction e with
  | zero =>
    intro κ _ _ _ c hc he
    have hall : ∀ a, Odd (c a) := fun a => by
      by_contra h
      have : a ∈ univ.filter (fun a => Even (c a)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.not_odd_iff_even.mp h⟩
      rw [Finset.card_eq_zero.mp he] at this; simp at this
    have hm : (univ.filter (fun a => Odd (c a))).card = Fintype.card κ := by
      rw [Finset.filter_true_of_mem fun a _ => hall a, Finset.card_univ]
    rw [if_pos (Or.inr rfl), hm]
    rw [Atoms.Φ_parity (c' := fun _ => 1) (fun a => ⟨fun _ => odd_one, fun _ => hall a⟩)]
    rw [← Atoms.Φ_congr (Fintype.equivFin κ) (fun _ => 1) (fun _ => 1) (fun _ => rfl)]
    exact Φ_ones_sq Fintype.card_pos
  | succ e ih =>
    intro κ _ _ _ c hc he
    obtain ⟨z, hz⟩ : ∃ z, Even (c z) := by
      by_contra h; push_neg at h
      rw [Finset.filter_false_of_mem (fun a _ => h a)] at he; simp at he
    have hzodd : ¬ Odd (c z) := Nat.not_odd_iff_even.mpr hz
    set m := (univ.filter (fun a => Odd (c a))).card
    -- split off the even atom `z`
    let c₀ : {a // a ≠ z} → ℕ := fun a => c a.1
    have hΦ : Atoms.Φ c = Atoms.Φ (Atoms.ext c₀ (c z)) :=
      Atoms.Φ_congr (optionSubtypeNe z) (Atoms.ext c₀ (c z)) c (fun o => by
        cases o with
        | none => simp [Atoms.ext]
        | some a => simp [Atoms.ext, c₀])
    have hm₀ : (univ.filter (fun a : {a // a ≠ z} => Odd (c₀ a))).card = m := by
      rw [card_subtype_ne_filter z (fun a => Odd (c a))]
      congr 1
      exact Finset.filter_congr fun a _ => ⟨fun h => h.1, fun h => ⟨h, fun e => hzodd (e ▸ h)⟩⟩
    simp only [Nat.add_one_ne_zero, or_false]
    by_cases hne : Nonempty {a // a ≠ z}
    · have he₀ : (univ.filter (fun a : {a // a ≠ z} => Even (c₀ a))).card = e := by
        rw [card_subtype_ne_filter z (fun a => Even (c a))]
        have hins : univ.filter (fun a => Even (c a)) =
            insert z (univ.filter (fun a => Even (c a) ∧ a ≠ z)) := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
          constructor
          · intro ha; by_cases haz : a = z
            · exact Or.inl haz
            · exact Or.inr ⟨ha, haz⟩
          · rintro (rfl | ⟨ha, _⟩)
            · exact hz
            · exact ha
        rw [hins, Finset.card_insert_of_notMem (by simp)] at he
        omega
      have hrec := ih {a // a ≠ z} c₀ (fun a => hc a.1) he₀
      rw [hm₀] at hrec
      rw [hΦ, Atoms.Φ_option c₀ hz, mul_pow, hrec]
      have hpar : Even (∑ a, c₀ a) ↔ Even m := by
        rw [Finset.even_sum_iff_even_card_odd, hm₀]
      by_cases hem : Even m
      · rw [if_pos (hpar.mpr hem), if_pos (Or.inl hem), if_pos hem]; ring
      · rw [if_neg (fun h => hem (hpar.mp h)), if_neg hem]; ring
    · rw [not_nonempty_iff] at hne
      have hcard : Fintype.card κ = 1 := by
        rw [← Fintype.card_congr (optionSubtypeNe z), Fintype.card_option, Fintype.card_eq_zero]
      have hm0 : m = 0 := by rw [← hm₀]; simp
      rw [Atoms.Φ_card_one hcard, hm0, if_pos (by decide : Even 0)]
      simp [show E 0 = 1 by decide]

/-- **Foulkes's theorem** (squared): for `n ≥ 1`, `ψ(w)² = E_m²` when `w` has `m` odd cycles and
either `m` is even or `w` has no even cycle; otherwise `ψ(w) = 0`. -/
theorem ψ_sq {n : ℕ} (hn : 1 ≤ n) (w : Perm (Fin n)) :
    ψ n w ^ 2 = if Even (univ.filter (fun q : cyc w => Odd (len w q))).card ∨
        (univ.filter (fun q : cyc w => Even (len w q))).card = 0
      then (E (univ.filter (fun q : cyc w => Odd (len w q))).card : ℤ) ^ 2 else 0 := by
  have : Nonempty (cyc w) := ⟨Quotient.mk _ ⟨0, by omega⟩⟩
  rw [ψ_eq_Φ w hn, mul_pow, ← pow_mul, mul_comm (altS n).card 2, pow_mul, neg_one_sq, one_pow,
    one_mul]
  exact Φ_eval _ (cyc w) (len w) (len_pos w) rfl

end Stanley.Alt
