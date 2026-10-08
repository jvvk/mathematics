/-
  Stanley, MathOverflow 486548. Part P. Counting permutations by odd and even cycles.

  `oddC σ` and `evenC σ` count the cycles (fixed points included) of odd and even length. Two
  correspondence lemmas compare the cycles of related permutations:
  * `collapse`: a map `ι : α → β` with a left inverse `π`, compatible with the two permutations up to
    `SameCycle`, identifies cycles; a cycle's length becomes the total `π`-fibre size over it
    (relabelling, and splicing two points into a cycle);
  * `extend`: an equivariant embedding adds the cycles of the complement (a fixed point, a 2-cycle).
-/
import LeanProofs.Stanley.PermCycles
import LeanProofs.Stanley.CycleSeries

namespace Stanley.Alt

open Finset Equiv Perm

section General

variable {α β : Type*}

/-- `SameCycle` is the finest `σ`-stable equivalence. -/
theorem sameCycle_le {σ : Perm α} (s : Setoid α) (h : ∀ a, s.r a (σ a)) {a b : α}
    (hab : SameCycle σ a b) : s.r a b := by
  obtain ⟨i, rfl⟩ := hab
  have key : ∀ i : ℤ, ∀ a, s.r a ((σ ^ i) a) := by
    intro i
    induction i using Int.induction_on with
    | zero => intro a; simp only [zpow_zero, Perm.one_apply]; exact s.iseqv.refl a
    | succ i ih =>
      intro a
      rw [zpow_add_one, Perm.mul_apply]
      exact s.iseqv.trans (h a) (ih (σ a))
    | pred i ih =>
      intro a
      rw [zpow_sub_one, Perm.mul_apply]
      have h1 := h (σ⁻¹ a); rw [show σ (σ⁻¹ a) = a by simp] at h1
      exact s.iseqv.trans (s.iseqv.symm h1) (ih (σ⁻¹ a))
  exact key i a

/-- The pullback of `SameCycle σ'` along `ι`. -/
def pullSetoid (σ' : Perm β) (ι : α → β) : Setoid α where
  r a b := SameCycle σ' (ι a) (ι b)
  iseqv := ⟨fun _ => SameCycle.refl _ _, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

theorem collapse_iff {σ : Perm α} {σ' : Perm β} {ι : α → β} {π : β → α}
    (hπι : ∀ a, π (ι a) = a) (h1 : ∀ a, SameCycle σ' (ι a) (ι (σ a)))
    (h2 : ∀ z, SameCycle σ (π z) (π (σ' z))) (a b : α) :
    SameCycle σ a b ↔ SameCycle σ' (ι a) (ι b) := by
  constructor
  · intro h; exact sameCycle_le (pullSetoid σ' ι) h1 h
  · intro h
    have h' : SameCycle σ (π (ι a)) (π (ι b)) := sameCycle_le (pullSetoid σ π) h2 h
    rwa [hπι, hπι] at h'

end General

section Counts

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Number of cycles of odd length. -/
noncomputable def oddC (σ : Perm α) : ℕ := (univ.filter (fun q : cyc σ => Odd (len σ q))).card

/-- Number of cycles of even length. -/
noncomputable def evenC (σ : Perm α) : ℕ := (univ.filter (fun q : cyc σ => Even (len σ q))).card

/-- Cycle counts agree along a length-parity preserving equivalence of cycle sets. -/
theorem counts_eq_of_equiv {σ : Perm α} {σ' : Perm β} (E : cyc σ ≃ cyc σ')
    (hE : ∀ q, Odd (len σ' (E q)) ↔ Odd (len σ q)) : oddC σ' = oddC σ ∧ evenC σ' = evenC σ := by
  constructor
  · unfold oddC
    refine (Finset.card_bij' (fun q' _ => E.symm q') (fun q _ => E q) ?_ ?_ ?_ ?_)
    · intro q' hq'; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq' ⊢
      rw [← hE]; simpa using hq'
    · intro q hq; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [hE]; exact hq
    · intro q' _; simp
    · intro q _; simp
  · unfold evenC
    refine (Finset.card_bij' (fun q' _ => E.symm q') (fun q _ => E q) ?_ ?_ ?_ ?_)
    · intro q' hq'; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq' ⊢
      rw [← Nat.not_odd_iff_even, ← hE, Nat.not_odd_iff_even]; simpa using hq'
    · intro q hq; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rw [← Nat.not_odd_iff_even, hE, Nat.not_odd_iff_even]; exact hq
    · intro q' _; simp
    · intro q _; simp

/-- **Collapse.** The cycles of `σ` and `σ'` correspond; lengths become fibre totals. -/
noncomputable def collapseEquiv {σ : Perm α} {σ' : Perm β} {ι : α → β} {π : β → α}
    (hπι : ∀ a, π (ι a) = a) (h1 : ∀ a, SameCycle σ' (ι a) (ι (σ a)))
    (h2 : ∀ z, SameCycle σ (π z) (π (σ' z))) (h3 : ∀ z, SameCycle σ' z (ι (π z))) :
    cyc σ ≃ cyc σ' :=
  Equiv.ofBijective (Quotient.map ι (fun a b h => (collapse_iff hπι h1 h2 a b).mp h))
    ⟨fun q r h => by
      obtain ⟨a, rfl⟩ := Quotient.exists_rep q
      obtain ⟨b, rfl⟩ := Quotient.exists_rep r
      exact Quotient.sound ((collapse_iff hπι h1 h2 a b).mpr (Quotient.exact h)),
     fun q' => by
      obtain ⟨z, rfl⟩ := Quotient.exists_rep q'
      exact ⟨Quotient.mk _ (π z), Quotient.sound (h3 z).symm⟩⟩

theorem len_collapse {σ : Perm α} {σ' : Perm β} {ι : α → β} {π : β → α}
    (hπι : ∀ a, π (ι a) = a) (h1 : ∀ a, SameCycle σ' (ι a) (ι (σ a)))
    (h2 : ∀ z, SameCycle σ (π z) (π (σ' z))) (h3 : ∀ z, SameCycle σ' z (ι (π z))) (a : α) :
    len σ' (collapseEquiv hπι h1 h2 h3 (Quotient.mk _ a)) =
      ∑ b ∈ univ.filter (fun b => (Quotient.mk _ b : cyc σ) = Quotient.mk _ a),
        (univ.filter (fun z => π z = b)).card := by
  have hE : collapseEquiv hπι h1 h2 h3 (Quotient.mk _ a) = Quotient.mk _ (ι a) := rfl
  rw [hE]
  unfold len
  have hset : univ.filter (fun z : β => (Quotient.mk _ z : cyc σ') = Quotient.mk _ (ι a)) =
      univ.filter (fun z : β => (Quotient.mk _ (π z) : cyc σ) = Quotient.mk _ a) := by
    apply Finset.filter_congr
    intro z _
    constructor
    · intro h
      apply Quotient.sound
      show SameCycle σ (π z) a
      rw [collapse_iff hπι h1 h2]
      exact (h3 z).symm.trans (Quotient.exact h)
    · intro h
      apply Quotient.sound
      exact (h3 z).trans ((collapse_iff hπι h1 h2 _ _).mp (Quotient.exact h))
  rw [hset, Finset.card_eq_sum_card_fiberwise (f := π)
    (t := univ.filter (fun b => (Quotient.mk _ b : cyc σ) = Quotient.mk _ a))]
  · refine Finset.sum_congr rfl fun b hb => ?_
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨by rw [h]; exact (Finset.mem_filter.mp hb).2, h⟩
  · intro z hz; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hz).2⟩

end Counts

section Cor

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem sameCycle_of_eq {σ : Perm α} {a b : α} (h : σ a = b) : SameCycle σ a b :=
  ⟨1, by simp [h]⟩

theorem len_eq_card (σ : Perm α) (a : α) :
    len σ (Quotient.mk _ a) = (univ.filter (fun b => (Quotient.mk _ b : cyc σ) = Quotient.mk _ a)).card :=
  rfl

/-- **Relabelling** preserves the cycle counts. -/
theorem counts_permCongr (e : α ≃ β) (σ : Perm α) :
    oddC (e.permCongr σ) = oddC σ ∧ evenC (e.permCongr σ) = evenC σ := by
  have hπι : ∀ a, e.symm (e a) = a := fun a => by simp
  have h1 : ∀ a, SameCycle (e.permCongr σ) (e a) (e (σ a)) := fun a =>
    sameCycle_of_eq (by simp [Equiv.permCongr_apply])
  have h2 : ∀ z, SameCycle σ (e.symm z) (e.symm (e.permCongr σ z)) := fun z =>
    sameCycle_of_eq (by simp [Equiv.permCongr_apply])
  have h3 : ∀ z, SameCycle (e.permCongr σ) z (e (e.symm z)) := fun z => by
    rw [Equiv.apply_symm_apply]
  refine counts_eq_of_equiv (collapseEquiv hπι h1 h2 h3) fun q => ?_
  obtain ⟨a, rfl⟩ := Quotient.exists_rep q
  rw [len_collapse, len_eq_card, Finset.card_eq_sum_ones]
  refine Iff.of_eq (congrArg Odd (Finset.sum_congr rfl fun b _ => ?_))
  rw [Finset.card_eq_one]
  exact ⟨e b, by ext z; simp [Equiv.symm_apply_eq]⟩

/-- **Extension.** An equivariant embedding whose complement is one nonempty cycle adds that
cycle to the counts. -/
theorem counts_extend {σ : Perm α} {σ' : Perm β} {ι : α → β} (hι : Function.Injective ι)
    (heq : ∀ a, σ' (ι a) = ι (σ a)) {z0 : β} (hz0 : z0 ∉ Set.range ι)
    (hR : ∀ z w, z ∉ Set.range ι → w ∉ Set.range ι → SameCycle σ' z w) :
    oddC σ' = oddC σ + (if Odd (univ.filter (fun z => z ∉ Set.range ι)).card then 1 else 0) ∧
    evenC σ' = evenC σ + (if Even (univ.filter (fun z => z ∉ Set.range ι)).card then 1 else 0) := by
  classical
  -- equivariance for all powers
  have hpow : ∀ i : ℤ, ∀ a, (σ' ^ i) (ι a) = ι ((σ ^ i) a) := by
    intro i
    induction i using Int.induction_on with
    | zero => intro a; simp
    | succ i ih => intro a; rw [zpow_add_one, zpow_add_one, Perm.mul_apply, Perm.mul_apply, heq, ih]
    | pred i ih =>
      intro a
      have hinv : σ'⁻¹ (ι a) = ι (σ⁻¹ a) := by
        have := heq (σ⁻¹ a); rw [show σ (σ⁻¹ a) = a by simp] at this
        rw [← this]; simp
      rw [zpow_sub_one, zpow_sub_one, Perm.mul_apply, Perm.mul_apply, hinv, ih]
  have hiff : ∀ a b, SameCycle σ' (ι a) (ι b) ↔ SameCycle σ a b := by
    intro a b; constructor
    · rintro ⟨i, hi⟩; rw [hpow] at hi; exact ⟨i, hι hi⟩
    · rintro ⟨i, hi⟩; exact ⟨i, by rw [hpow, hi]⟩
  have hclosed : ∀ z w, z ∉ Set.range ι → SameCycle σ' z w → w ∉ Set.range ι := by
    rintro z w hz ⟨i, rfl⟩ ⟨b, hb⟩
    apply hz
    refine ⟨(σ ^ (-i)) b, ?_⟩
    rw [← hpow, hb]; simp
  set R := univ.filter (fun z => z ∉ Set.range ι)
  -- the cycles of `σ'`
  let E : cyc σ → cyc σ' := Quotient.map ι (fun a b h => (hiff a b).mpr h)
  have hEinj : Function.Injective E := fun q r h => by
    obtain ⟨a, rfl⟩ := Quotient.exists_rep q
    obtain ⟨b, rfl⟩ := Quotient.exists_rep r
    exact Quotient.sound ((hiff a b).mp (Quotient.exact h))
  have hlenE : ∀ a, len σ' (E (Quotient.mk _ a)) = len σ (Quotient.mk _ a) := by
    intro a
    show len σ' (Quotient.mk _ (ι a)) = _
    rw [len_eq_card, len_eq_card]
    rw [← Finset.card_image_of_injective _ hι]
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hw
      have hwr : w ∈ Set.range ι := by
        by_contra hn
        exact hclosed w (ι a) hn (Quotient.exact hw) ⟨a, rfl⟩
      obtain ⟨b, rfl⟩ := hwr
      exact ⟨b, Quotient.sound ((hiff b a).mp (Quotient.exact hw)), rfl⟩
    · rintro ⟨b, hb, rfl⟩; exact Quotient.sound ((hiff b a).mpr (Quotient.exact hb))
  have hlen0 : len σ' (Quotient.mk _ z0) = R.card := by
    rw [len_eq_card]; congr 1; ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, R]
    constructor
    · intro hw; exact hclosed z0 w hz0 (Quotient.exact hw).symm
    · intro hw; exact Quotient.sound (hR w z0 hw hz0)
  have hsplit : (univ : Finset (cyc σ')) = (univ.image E) ∪ {Quotient.mk _ z0} := by
    ext q'
    simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_image, true_and,
      Finset.mem_singleton, true_iff]
    obtain ⟨z, rfl⟩ := Quotient.exists_rep q'
    by_cases hz : z ∈ Set.range ι
    · obtain ⟨a, rfl⟩ := hz; exact Or.inl ⟨Quotient.mk _ a, rfl⟩
    · exact Or.inr (Quotient.sound (hR z z0 hz hz0))
  have hdisj : Disjoint (univ.image E) {Quotient.mk _ z0} := by
    rw [Finset.disjoint_singleton_right, Finset.mem_image]
    rintro ⟨q, _, hq⟩
    obtain ⟨a, rfl⟩ := Quotient.exists_rep q
    exact hclosed z0 (ι a) hz0 (Quotient.exact hq).symm ⟨a, rfl⟩
  have hcount : ∀ (P : ℕ → Prop) [DecidablePred P],
      (univ.filter (fun q' : cyc σ' => P (len σ' q'))).card =
        (univ.filter (fun q : cyc σ => P (len σ q))).card + (if P R.card then 1 else 0) := by
    intro P _
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj), Finset.filter_image,
      Finset.card_image_of_injective _ hEinj, Finset.filter_singleton, hlen0]
    congr 1
    · congr 1
      exact Finset.filter_congr fun q _ => by
        obtain ⟨a, rfl⟩ := Quotient.exists_rep q; simp only [Function.comp_apply, hlenE]
    · split_ifs <;> simp
  exact ⟨hcount Odd, hcount Even⟩

end Cor

section Splice

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Insert the two new points `none ↦ some none` right after `d` in the cycle of `τ`. -/
def splice (τ : Perm α) (d : α) : Perm (Option (Option α)) where
  toFun z := match z with
    | none => some none
    | some none => some (some (τ d))
    | some (some a) => if a = d then none else some (some (τ a))
  invFun z := match z with
    | none => some (some d)
    | some none => none
    | some (some b) => if b = τ d then some none else some (some (τ⁻¹ b))
  left_inv z := by
    rcases z with _ | _ | a
    · simp
    · simp
    · by_cases h : a = d
      · simp [h]
      · have : τ a ≠ τ d := fun e => h (τ.injective e)
        simp [h, this]
  right_inv z := by
    rcases z with _ | _ | b
    · simp
    · simp
    · by_cases h : b = τ d
      · simp [h]
      · have : τ.symm b ≠ d := fun e => h (by rw [← e]; simp)
        simp [h, this]

@[simp] theorem splice_none (τ : Perm α) (d : α) : splice τ d none = some none := rfl
@[simp] theorem splice_some_none (τ : Perm α) (d : α) : splice τ d (some none) = some (some (τ d)) := rfl
theorem splice_some_some (τ : Perm α) (d a : α) :
    splice τ d (some (some a)) = if a = d then none else some (some (τ a)) := rfl

/-- The projection collapsing the two new points onto `d`. -/
def collapseTo (d : α) : Option (Option α) → α
  | none => d
  | some none => d
  | some (some a) => a

/-- **Splicing preserves the cycle counts.** -/
theorem counts_splice (τ : Perm α) (d : α) :
    oddC (splice τ d) = oddC τ ∧ evenC (splice τ d) = evenC τ := by
  set σ := splice τ d
  have hπι : ∀ a, collapseTo d (some (some a)) = a := fun a => rfl
  have h1 : ∀ a, SameCycle σ (some (some a)) (some (some (τ a))) := by
    intro a
    by_cases h : a = d
    · subst h
      refine ⟨3, ?_⟩
      simp [σ, pow_succ, Perm.mul_apply, splice_some_some]
    · exact sameCycle_of_eq (by simp [σ, splice_some_some, h])
  have h2 : ∀ z, SameCycle τ (collapseTo d z) (collapseTo d (σ z)) := by
    intro z
    rcases z with _ | _ | a
    · exact SameCycle.refl _ _
    · exact sameCycle_of_eq (by simp [σ, collapseTo])
    · by_cases h : a = d
      · subst h
        show SameCycle τ a (collapseTo a (splice τ a (some (some a))))
        rw [splice_some_some, if_pos rfl]; exact SameCycle.refl _ _
      · exact sameCycle_of_eq (by simp [σ, splice_some_some, h, collapseTo])
  have h3 : ∀ z, SameCycle σ z (some (some (collapseTo d z))) := by
    intro z
    rcases z with _ | _ | a
    · show SameCycle σ none (some (some d))
      exact (sameCycle_of_eq (by simp [σ, splice_some_some])).symm
    · refine (show SameCycle σ (some (some d)) (some none) from ⟨2, ?_⟩).symm
      simp [σ, pow_succ, Perm.mul_apply, splice_some_some]
    · exact SameCycle.refl _ _
  refine counts_eq_of_equiv (collapseEquiv hπι h1 h2 h3) fun q => ?_
  obtain ⟨a, rfl⟩ := Quotient.exists_rep q
  rw [len_collapse, len_eq_card, Finset.card_eq_sum_ones]
  have hfib : ∀ b, (univ.filter (fun z => collapseTo d z = b)).card = if b = d then 3 else 1 := by
    intro b
    by_cases hb : b = d
    · subst hb
      rw [if_pos rfl]
      have : univ.filter (fun z => collapseTo b z = b) = {none, some none, some (some b)} := by
        ext z; rcases z with _ | _ | a <;> simp [collapseTo, eq_comm]
      rw [this]; rfl
    · rw [if_neg hb, Finset.card_eq_one]
      refine ⟨some (some b), ?_⟩
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rcases z with _ | _ | a
      · simp only [collapseTo]; constructor
        · intro h; exact absurd h.symm hb
        · intro h; cases h
      · simp only [collapseTo]; constructor
        · intro h; exact absurd h.symm hb
        · intro h; cases h
      · simp only [collapseTo]; constructor
        · rintro rfl; rfl
        · intro h; cases h; rfl
  simp_rw [hfib]
  set A := univ.filter (fun b => (Quotient.mk _ b : cyc τ) = Quotient.mk _ a)
  have hsum : (∑ b ∈ A, if b = d then 3 else 1) = A.card + 2 * (A.filter (fun b => b = d)).card := by
    rw [Finset.card_eq_sum_ones, Finset.card_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  rw [hsum, Nat.odd_add, ← Finset.card_eq_sum_ones]
  constructor
  · intro h; exact h.mpr (even_two_mul _)
  · intro h; exact ⟨fun _ => even_two_mul _, fun _ => h⟩

end Splice

section Rec

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- The property counted by `cycleNumbers all _ m`. -/
def Pc (all : Bool) (m : ℕ) (σ : Perm β) : Prop := oddC σ = m ∧ (all = true ∨ evenC σ = 0)

noncomputable instance (all : Bool) (m : ℕ) (σ : Perm β) : Decidable (Pc all m σ) := by
  unfold Pc; infer_instance

/-- The count. -/
noncomputable def Qc (β : Type*) [Fintype β] [DecidableEq β] (all : Bool) (m : ℕ) : ℕ :=
  (univ.filter (fun σ : Perm β => Pc all m σ)).card

theorem Qc_congr (e : α ≃ β) (all : Bool) (m : ℕ) : Qc α all m = Qc β all m := by
  unfold Qc
  refine Finset.card_bij' (fun σ _ => e.permCongr σ) (fun σ _ => e.symm.permCongr σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    have h := counts_permCongr e σ
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hσ).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1.trans h1, by rw [h.2]; exact h2⟩
  · intro σ hσ
    have h := counts_permCongr e.symm σ
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hσ).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.1.trans h1, by rw [h.2]; exact h2⟩
  · intro σ _; ext x; simp [Equiv.permCongr_apply]
  · intro σ _; ext x; simp [Equiv.permCongr_apply]

theorem counts_optionCongr (τ : Perm α) :
    oddC (optionCongr τ : Perm (Option α)) = oddC τ + 1 ∧
      evenC (optionCongr τ : Perm (Option α)) = evenC τ := by
  have hR : (univ.filter (fun z : Option α => z ∉ Set.range some)) = {none} := by
    ext z; cases z <;> simp
  have h := counts_extend (σ := τ) (σ' := optionCongr τ) (ι := some) (Option.some_injective α)
    (fun a => by simp) (z0 := none) (by simp)
    (fun z w hz hw => by
      cases z with
      | none => cases w with
        | none => exact SameCycle.refl _ _
        | some b => exact absurd ⟨b, rfl⟩ hw
      | some a => exact absurd ⟨a, rfl⟩ hz)
  rw [hR, Finset.card_singleton] at h
  simpa using h

/-- A 2-cycle on the two new points. -/
def twoCyc (τ : Perm α) : Perm (Option (Option α)) :=
  swap none (some none) * optionCongr (optionCongr τ)

theorem counts_twoCyc (τ : Perm α) : oddC (twoCyc τ) = oddC τ ∧ evenC (twoCyc τ) = evenC τ + 1 := by
  have hR : (univ.filter (fun z : Option (Option α) => z ∉ Set.range (some ∘ some))) =
      {none, some none} := by
    ext z; rcases z with _ | _ | a <;> simp
  have hinj : Function.Injective (some ∘ some : α → Option (Option α)) :=
    (Option.some_injective _).comp (Option.some_injective _)
  have h := counts_extend (σ := τ) (σ' := twoCyc τ) (ι := some ∘ some) hinj
    (fun a => by simp [twoCyc, swap_apply_of_ne_of_ne]) (z0 := none) (by simp)
    (fun z w hz hw => by
      have hz' : z = none ∨ z = some none := by
        rcases z with _ | _ | a
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd ⟨a, rfl⟩ hz
      have hw' : w = none ∨ w = some none := by
        rcases w with _ | _ | a
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact absurd ⟨a, rfl⟩ hw
      have hstep : SameCycle (twoCyc τ) none (some none) :=
        sameCycle_of_eq (by simp [twoCyc])
      rcases hz' with rfl | rfl <;> rcases hw' with rfl | rfl
      · exact SameCycle.refl _ _
      · exact hstep
      · exact hstep.symm
      · exact SameCycle.refl _ _)
  rw [hR] at h
  have hc : ({none, some none} : Finset (Option (Option α))).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
  rw [hc] at h
  simpa [show ¬ Odd 2 by decide] using h

theorem optionCongr_removeNone_of (σ : Perm (Option β)) (h : σ none = none) :
    (optionCongr (removeNone σ) : Perm (Option β)) = σ := by
  ext z
  cases z with
  | none => simp [h]
  | some x =>
    have hx : ∃ x', σ (some x) = some x' := by
      rcases hσ : σ (some x) with _ | x'
      · exact absurd (σ.injective (hσ.trans h.symm)) (by simp)
      · exact ⟨x', rfl⟩
    simp only [optionCongr_apply, Option.map_some]
    rw [removeNone_some σ hx]

end Rec

section Cases

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- New point fixed. -/
theorem count_fixed (all : Bool) (m : ℕ) :
    (univ.filter (fun σ : Perm (Option β) => σ none = none ∧ Pc all m σ)).card =
      if m = 0 then 0 else Qc β all (m - 1) := by
  split_ifs with hm
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro σ - ⟨hσ, h1, -⟩
    have := (counts_optionCongr (removeNone σ)).1
    rw [optionCongr_removeNone_of σ hσ] at this
    omega
  · unfold Qc
    refine Finset.card_bij' (fun σ _ => removeNone σ) (fun τ _ => optionCongr τ) ?_ ?_ ?_ ?_
    · intro σ hσ
      obtain ⟨hn, h1, h2⟩ := (Finset.mem_filter.mp hσ).2
      have h := counts_optionCongr (removeNone σ)
      rw [optionCongr_removeNone_of σ hn] at h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, by rw [← h.2]; exact h2⟩
    · intro τ hτ
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hτ).2
      have h := counts_optionCongr τ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp, by omega, by rw [h.2]; exact h2⟩
    · intro σ hσ; exact optionCongr_removeNone_of σ (Finset.mem_filter.mp hσ).2.1
    · intro τ _; exact removeNone_optionCongr τ

/-- The swap moving `some b` to `some none`. -/
def cb (b : Option α) : Perm (Option (Option α)) := swap (some none) (some b)

theorem cb_conj (b : Option α) (σ : Perm (Option (Option α))) :
    cb b * σ * cb b = (cb b).permCongr σ := by
  ext x; simp [cb, Equiv.permCongr_apply, swap_inv]

/-- New point moved: conjugate so that it goes to `some none`. -/
theorem count_moved (all : Bool) (m : ℕ) :
    (univ.filter (fun σ : Perm (Option (Option α)) => σ none ≠ none ∧ Pc all m σ)).card =
      (Fintype.card α + 1) *
        (univ.filter (fun σ : Perm (Option (Option α)) => σ none = some none ∧ Pc all m σ)).card := by
  rw [← Fintype.card_option, ← Finset.card_univ, ← Finset.card_product]
  symm
  refine Finset.card_bij' (fun p _ => cb p.1 * p.2 * cb p.1)
    (fun σ hσ => ((σ none).get (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hσ).2.1),
      cb ((σ none).get (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hσ).2.1)) * σ *
        cb ((σ none).get (Option.isSome_iff_ne_none.mpr (Finset.mem_filter.mp hσ).2.1)))) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨-, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hn, h1, h2⟩ := (Finset.mem_filter.mp hp2).2
    have hc := counts_permCongr (cb p.1) p.2
    rw [← cb_conj] at hc
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hc.1.trans h1, by rw [hc.2]; exact h2⟩
    simp [cb, hn, swap_apply_of_ne_of_ne]
  · intro σ hσ
    obtain ⟨hn, h1, h2⟩ := (Finset.mem_filter.mp hσ).2
    set b := (σ none).get (Option.isSome_iff_ne_none.mpr hn) with hb
    have hσb : σ none = some b := by simp [hb]
    have hc := counts_permCongr (cb b) σ
    rw [← cb_conj] at hc
    refine Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ?_, hc.1.trans h1, by rw [hc.2]; exact h2⟩⟩
    simp [cb, hσb, swap_apply_of_ne_of_ne]
  · intro p hp
    obtain ⟨-, hp2⟩ := Finset.mem_product.mp hp
    have hn := (Finset.mem_filter.mp hp2).2.1
    have hval : (cb p.1 * p.2 * cb p.1) none = some p.1 := by
      simp [cb, hn, swap_apply_of_ne_of_ne]
    ext1
    · simp [hval]
    · simp only [hval, Option.get_some]
      ext x; simp [cb, mul_assoc, swap_mul_self_mul]
  · intro σ hσ
    simp only
    ext x
    simp [cb, mul_assoc]

end Cases

section Cases2

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem removeNone_fix {σ : Perm (Option (Option α))} (h : σ (some none) = some none) :
    removeNone σ none = none := by
  have := removeNone_some σ ⟨none, h⟩
  rw [h] at this; exact Option.some_injective _ this

/-- Rebuild a permutation fixing both new points from its restriction. -/
theorem optionCongr2_removeNone {σ : Perm (Option (Option α))} (h0 : σ none = none)
    (h1 : σ (some none) = some none) :
    (optionCongr (optionCongr (removeNone (removeNone σ))) : Perm (Option (Option α))) = σ := by
  rw [optionCongr_removeNone_of (removeNone σ) (removeNone_fix h1), optionCongr_removeNone_of σ h0]

/-- The new points form a 2-cycle. -/
theorem count_twoCyc (all : Bool) (m : ℕ) :
    (univ.filter (fun σ : Perm (Option (Option α)) =>
      σ none = some none ∧ σ (some none) = none ∧ Pc all m σ)).card =
      if all then Qc α all m else 0 := by
  have hrep : ∀ σ : Perm (Option (Option α)), σ none = some none → σ (some none) = none →
      twoCyc (removeNone (removeNone (swap none (some none) * σ))) = σ := by
    intro σ h0 h1
    unfold twoCyc
    rw [optionCongr2_removeNone (by simp [h0]) (by simp [h1])]
    rw [← mul_assoc, swap_mul_self, one_mul]
  split_ifs with hall
  · subst hall
    unfold Qc
    refine Finset.card_bij' (fun σ _ => removeNone (removeNone (swap none (some none) * σ)))
      (fun τ _ => twoCyc τ) ?_ ?_ ?_ ?_
    · intro σ hσ
      obtain ⟨h0, h1, h2, -⟩ := (Finset.mem_filter.mp hσ).2
      have hc := counts_twoCyc (removeNone (removeNone (swap none (some none) * σ)))
      rw [hrep σ h0 h1] at hc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.1 ▸ h2, Or.inl rfl⟩
    · intro τ hτ
      obtain ⟨h1, -⟩ := (Finset.mem_filter.mp hτ).2
      have hc := counts_twoCyc τ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [twoCyc], by simp [twoCyc],
        hc.1.trans h1, Or.inl rfl⟩
    · intro σ hσ
      obtain ⟨h0, h1, -⟩ := (Finset.mem_filter.mp hσ).2
      exact hrep σ h0 h1
    · intro τ _
      unfold twoCyc
      rw [← mul_assoc, swap_mul_self, one_mul]
      rw [removeNone_optionCongr, removeNone_optionCongr]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro σ - ⟨h0, h1, -, h2⟩
    have hc := counts_twoCyc (removeNone (removeNone (swap none (some none) * σ)))
    rw [hrep σ h0 h1] at hc
    rcases h2 with h2 | h2
    · simp_all
    · omega

/-- The inverse 3-cycle used to undo a splice. -/
def unsplice (d : α) : Perm (Option (Option α)) := swap (some none) none * swap none (some (some d))

/-- The new points are spliced into an old cycle. -/
theorem count_splice (all : Bool) (m : ℕ) :
    (univ.filter (fun σ : Perm (Option (Option α)) =>
      σ none = some none ∧ σ (some none) ≠ none ∧ Pc all m σ)).card =
      Fintype.card α * Qc α all m := by
  unfold Qc
  rw [← Finset.card_univ (α := α), ← Finset.card_product]
  symm
  apply Finset.card_bij (fun p _ => splice p.2 p.1)
  · intro p hp
    obtain ⟨-, hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hp2).2
    have hc := counts_splice p.2 p.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, by simp, hc.1.trans h1,
      by rw [hc.2]; exact h2⟩
  · intro p _ q _ h
    have hd : p.1 = q.1 := by
      have e1 : splice p.2 p.1 (some (some p.1)) = none := by simp [splice_some_some]
      rw [h, splice_some_some] at e1
      split_ifs at e1 with he
      · exact he
    have ht : p.2 = q.2 := by
      ext a
      by_cases ha : a = p.1
      · have := congrArg (fun σ => σ (some none)) h
        simp only [splice_some_none, Option.some.injEq] at this
        rw [ha, this, hd]
      · have := congrArg (fun σ => σ (some (some a))) h
        simp only [splice_some_some] at this
        rw [if_neg ha, if_neg (hd ▸ ha)] at this
        simpa using this
    exact Prod.ext hd ht
  · intro σ hσ
    obtain ⟨h0, h1, h2, h3⟩ := (Finset.mem_filter.mp hσ).2
    -- the predecessor of `none`
    obtain ⟨d, hd⟩ : ∃ d, σ (some (some d)) = none := by
      rcases hz : σ⁻¹ none with _ | _ | d
      · have := congrArg σ hz; simp [h0] at this
      · have := congrArg σ hz; simp at this; exact absurd this.symm h1
      · exact ⟨d, by have := congrArg σ hz; simpa using this.symm⟩
    set τh := σ * unsplice d
    have e0 : τh none = none := by simp [τh, unsplice, swap_apply_of_ne_of_ne, hd]
    have e1 : τh (some none) = some none := by simp [τh, unsplice, swap_apply_of_ne_of_ne, h0]
    set τ := removeNone (removeNone τh)
    have hτ : ∀ a, some (some (τ a)) = τh (some (some a)) := by
      intro a
      have hc := optionCongr2_removeNone e0 e1
      have h2 : (optionCongr (optionCongr τ) : Perm (Option (Option α))) (some (some a)) =
          some (some (τ a)) := by simp [Equiv.optionCongr_apply]
      rw [← h2, hc]
    have hsp : splice τ d = σ := by
      ext1 z
      rcases z with _ | _ | a
      · simp [h0]
      · rw [splice_some_none, hτ]
        simp [τh, unsplice, swap_apply_of_ne_of_ne]
      · rw [splice_some_some]
        split_ifs with ha
        · rw [ha, hd]
        · rw [hτ]
          have hne : some (some a) ≠ some (some d) := by simp [ha]
          simp [τh, unsplice, swap_apply_of_ne_of_ne, hne]
    refine ⟨(d, τ), Finset.mem_product.mpr ⟨Finset.mem_univ _, ?_⟩, hsp⟩
    have hc := counts_splice τ d
    rw [hsp] at hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.1 ▸ h2, by rw [← hc.2]; exact h3⟩

end Cases2

section Recurrence

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **The cycle-count recurrence.** -/
theorem Qc_rec (all : Bool) (m : ℕ) :
    Qc (Option (Option α)) all m = (if m = 0 then 0 else Qc (Option α) all (m - 1)) +
      (Fintype.card α + 1) * ((if all then 1 else 0) + Fintype.card α) * Qc α all m := by
  have hsplit1 := Finset.card_filter_add_card_filter_not
    (s := univ.filter (fun σ : Perm (Option (Option α)) => Pc all m σ)) (p := fun σ => σ none = none)
  have e1 : (univ.filter (fun σ : Perm (Option (Option α)) => Pc all m σ)).filter
      (fun σ => σ none = none) = univ.filter (fun σ => σ none = none ∧ Pc all m σ) := by
    rw [Finset.filter_filter]; exact Finset.filter_congr fun _ _ => and_comm
  have e2 : (univ.filter (fun σ : Perm (Option (Option α)) => Pc all m σ)).filter
      (fun σ => ¬ σ none = none) = univ.filter (fun σ => σ none ≠ none ∧ Pc all m σ) := by
    rw [Finset.filter_filter]; exact Finset.filter_congr fun _ _ => and_comm
  have hsplit2 := Finset.card_filter_add_card_filter_not
    (s := univ.filter (fun σ : Perm (Option (Option α)) => σ none = some none ∧ Pc all m σ))
    (p := fun σ => σ (some none) = none)
  have e3 : (univ.filter (fun σ : Perm (Option (Option α)) => σ none = some none ∧ Pc all m σ)).filter
      (fun σ => σ (some none) = none) =
      univ.filter (fun σ => σ none = some none ∧ σ (some none) = none ∧ Pc all m σ) := by
    rw [Finset.filter_filter]; exact Finset.filter_congr fun _ _ => by tauto
  have e4 : (univ.filter (fun σ : Perm (Option (Option α)) => σ none = some none ∧ Pc all m σ)).filter
      (fun σ => ¬ σ (some none) = none) =
      univ.filter (fun σ => σ none = some none ∧ σ (some none) ≠ none ∧ Pc all m σ) := by
    rw [Finset.filter_filter]; exact Finset.filter_congr fun _ _ => by tauto
  rw [e3, e4, count_twoCyc, count_splice] at hsplit2
  rw [e1, e2, count_fixed, count_moved, ← hsplit2] at hsplit1
  unfold Qc at hsplit1 ⊢
  rw [← hsplit1]
  split_ifs <;> ring

theorem oddC_evenC_fin_zero (σ : Perm (Fin 0)) : oddC σ = 0 ∧ evenC σ = 0 := by
  have hq : ∀ q : cyc σ, False := fun q => by
    obtain ⟨p, -⟩ := Quotient.exists_rep q; exact p.elim0
  constructor
  · unfold oddC; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro q; exact (hq q).elim
  · unfold evenC; rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]; intro q; exact (hq q).elim

theorem oddC_evenC_fin_one (σ : Perm (Fin 1)) : oddC σ = 1 ∧ evenC σ = 0 := by
  have huniv : (univ : Finset (cyc σ)) = {Quotient.mk _ 0} := by
    ext q; simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    obtain ⟨p, rfl⟩ := Quotient.exists_rep q
    rw [Subsingleton.elim p 0]
  have hlen : len σ (Quotient.mk _ 0) = 1 := by
    rw [len_eq_card, Finset.card_eq_one]
    exact ⟨0, by ext p; simp [Subsingleton.elim p 0]⟩
  constructor
  · unfold oddC; rw [huniv, Finset.filter_singleton, hlen, if_pos odd_one, Finset.card_singleton]
  · unfold evenC; rw [huniv, Finset.filter_singleton, hlen, if_neg (by decide), Finset.card_empty]

/-- **Permutations counted by odd cycles satisfy the `cycleNumbers` recurrence.** -/
theorem Qc_fin (all : Bool) : ∀ n m, Qc (Fin n) all m = cycleNumbers all n m := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    intro m
    unfold Qc
    simp only [cycleNumbers]
    split_ifs with hm
    · subst hm
      rw [Finset.filter_true_of_mem (fun σ _ => ⟨(oddC_evenC_fin_zero σ).1, Or.inr (oddC_evenC_fin_zero σ).2⟩),
        Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      rfl
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro σ _ h
      exact hm ((oddC_evenC_fin_zero σ).1 ▸ h.1).symm
  | one =>
    intro m
    unfold Qc
    simp only [cycleNumbers]
    split_ifs with hm
    · subst hm
      rw [Finset.filter_true_of_mem (fun σ _ => ⟨(oddC_evenC_fin_one σ).1, Or.inr (oddC_evenC_fin_one σ).2⟩),
        Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      rfl
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro σ _ h
      exact hm ((oddC_evenC_fin_one σ).1 ▸ h.1).symm
  | more n ih0 ih1 =>
    intro m
    have e2 : Fin (n + 2) ≃ Option (Option (Fin n)) :=
      (finSuccEquiv (n + 1)).trans (optionCongr (finSuccEquiv n))
    rw [Qc_congr e2, Qc_rec, Fintype.card_fin, ← Qc_congr (finSuccEquiv n), ih0, cycleNumbers]
    simp only [ih1]
    ring

end Recurrence

end Stanley.Alt
