import LeanProofs.Orbits516140.Aut

/-!
# Disjoint unions of fences do not attain `g(n)` for `n ≥ 181`

* `two_pow_mul_card_linExt_le` (L1): `t` pairwise disjoint comparable pairs give
  `2^t · e(α) ≤ n!`.
* `factorial_le_card_aut` (L2): `k` isolated points give `k! ≤ #Aut(α)`.
* `exists_matching` (L3): a disjoint union of fences has `t` disjoint comparable pairs with
  `n ≤ 3t + k`, `k` the number of isolated points.
* `orbitCount_mul_le` (L4): hence `f(α) · 2^t · k! ≤ n!` for such `t, k`.
* `Gr`, `orbitCount_Gr`, `exists_poset_orbitCount_ge` (L5): the construction from the MO answer
  of "graham": `j` tops, `m` bottoms indexed by distinct subsets of the tops, one of them the
  full set, `b_S < a ↔ a ∈ S`; then `f ≥ m!` whenever `1 ≤ m ≤ 2^j` (the empty set may be one
  of the indices: it gives an isolated bottom, which is still minimal).
* `J`, `factorial_lt` (L6): `J n` is the least `j` with `n ≤ 2^j + j - 1`; for `n ≥ 181` and
  `n ≤ 3t + k`, `n! < (n - J n)! · 2^t · k!`.
* `fence_union_not_max` (T).
-/

namespace Orbits516140

open Finset Nat

/-! ## L1: a matching of comparable pairs -/

section Matching

variable {α : Type*} [Fintype α] [PartialOrder α] [DecidableEq α]

/-- The bijections `α ≃ Fin n` that put `q.1` before `q.2` for every `q ∈ C`. -/
def sat (C : Finset (α × α)) : Finset (α ≃ Fin (Fintype.card α)) :=
  univ.filter fun σ => ∀ q ∈ C, σ q.1 < σ q.2

omit [PartialOrder α] in
theorem two_mul_card_sat_insert (p : α × α) (C : Finset (α × α))
    (hC : ∀ q ∈ C, p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) :
    2 * (sat (insert p C)).card ≤ (sat C).card := by
  set A := sat (insert p C)
  let sw : (α ≃ Fin (Fintype.card α)) → (α ≃ Fin (Fintype.card α)) :=
    fun σ => (Equiv.swap p.1 p.2).trans σ
  have hsw : ∀ σ x, sw σ x = σ (Equiv.swap p.1 p.2 x) := fun _ _ => rfl
  have hinj : Function.Injective sw := by
    intro σ τ h
    apply Equiv.ext
    intro x
    have := congrArg (fun f : α ≃ Fin (Fintype.card α) => f (Equiv.swap p.1 p.2 x)) h
    simpa [hsw] using this
  have hmemA : ∀ σ, σ ∈ A ↔ σ p.1 < σ p.2 ∧ ∀ q ∈ C, σ q.1 < σ q.2 := by
    intro σ; simp [A, sat]
  have hA : A ⊆ sat C := by
    intro σ hσ
    simp only [sat, mem_filter, mem_univ, true_and]
    exact ((hmemA σ).1 hσ).2
  have hB : A.image sw ⊆ sat C := by
    intro σ hσ
    obtain ⟨τ, hτ, rfl⟩ := mem_image.1 hσ
    simp only [sat, mem_filter, mem_univ, true_and]
    intro q hq
    obtain ⟨h1, h2, h3, h4⟩ := hC q hq
    rw [hsw, hsw, Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) (Ne.symm h3),
      Equiv.swap_apply_of_ne_of_ne (Ne.symm h2) (Ne.symm h4)]
    exact ((hmemA τ).1 hτ).2 q hq
  have hdisj : Disjoint A (A.image sw) := by
    rw [disjoint_left]
    intro σ hσ hσ'
    obtain ⟨τ, hτ, rfl⟩ := mem_image.1 hσ'
    have h1 := ((hmemA _).1 hσ).1
    have h2 := ((hmemA τ).1 hτ).1
    rw [hsw, hsw, Equiv.swap_apply_left, Equiv.swap_apply_right] at h1
    exact lt_asymm h1 h2
  calc 2 * A.card = A.card + (A.image sw).card := by
        rw [card_image_of_injective _ hinj]; ring
    _ = (A ∪ A.image sw).card := (card_union_of_disjoint hdisj).symm
    _ ≤ (sat C).card := card_le_card (union_subset hA hB)

end Matching

section MatchingBound

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- **L1.** If `M` is a set of pairs `a < b` with pairwise disjoint supports, then
`2^#M · e(α) ≤ n!`. -/
theorem two_pow_mul_card_linExt_le (M : Finset (α × α)) (hlt : ∀ p ∈ M, p.1 < p.2)
    (hdisj : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) :
    2 ^ M.card * Nat.card (LinExt α) ≤ (Fintype.card α)! := by
  classical
  have key : ∀ C ⊆ M, 2 ^ C.card * (sat C).card ≤ (Fintype.card α)! := by
    intro C
    induction C using Finset.induction_on with
    | empty =>
      intro _
      simp [sat, Fintype.card_equiv (Fintype.equivFin α)]
    | insert p C hp ih =>
      intro hsub
      have hpM : p ∈ M := hsub (mem_insert_self _ _)
      have h1 := two_mul_card_sat_insert p C
        (fun q hq => hdisj p hpM q (hsub (mem_insert_of_mem hq)) (by rintro rfl; exact hp hq))
      rw [card_insert_of_notMem hp, pow_succ]
      calc 2 ^ C.card * 2 * (sat (insert p C)).card
          = 2 ^ C.card * (2 * (sat (insert p C)).card) := by ring
        _ ≤ 2 ^ C.card * (sat C).card := Nat.mul_le_mul_left _ h1
        _ ≤ _ := ih ((subset_insert _ _).trans hsub)
  have hle : Nat.card (LinExt α) ≤ (sat M).card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective
      (fun σ => ⟨σ.1, by simp only [sat, mem_filter, mem_univ, true_and]
                         exact fun q hq => σ.2 (hlt q hq)⟩) ?_
    intro σ τ h
    exact Subtype.ext (congrArg (fun x : sat M => x.1) h)
  exact (Nat.mul_le_mul_left _ hle).trans (key M Subset.rfl)

/-! ## L2: isolated points -/

/-- `x` is comparable with no element. -/
def Isolated (x : α) : Prop := ∀ y, ¬ x < y ∧ ¬ y < x

set_option linter.unusedFintypeInType false in
/-- **L2.** `k` isolated points give `k!` automorphisms: permute them, fix the rest. -/
theorem factorial_le_card_aut (S : Finset α) (hS : ∀ x ∈ S, Isolated x) :
    S.card ! ≤ Nat.card (α ≃o α) := by
  classical
  let f : Equiv.Perm S → Equiv.Perm α := Equiv.Perm.ofSubtype
  have hmem : ∀ π x, f π x ∈ S ↔ x ∈ S := by
    intro π x
    by_cases hx : x ∈ S
    · simp only [f, Equiv.Perm.ofSubtype_apply_of_mem π hx, hx, iff_true]
      exact (π ⟨x, hx⟩).2
    · simp [f, Equiv.Perm.ofSubtype_apply_of_not_mem π hx, hx]
  have hfix : ∀ π x, x ∉ S → f π x = x := fun π x hx =>
    Equiv.Perm.ofSubtype_apply_of_not_mem π hx
  have hlt : ∀ x y : α, x < y → x ∉ S ∧ y ∉ S := fun x y h =>
    ⟨fun hx => (hS x hx y).1 h, fun hy => (hS y hy x).2 h⟩
  let g : Equiv.Perm S → (α ≃o α) := fun π =>
    { toEquiv := f π
      map_rel_iff' := by
        intro a b
        change f π a ≤ f π b ↔ a ≤ b
        rw [le_iff_eq_or_lt, le_iff_eq_or_lt, (f π).injective.eq_iff]
        refine or_congr_right ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨ha, hb⟩ := hlt _ _ h
          rw [hmem] at ha hb
          rwa [hfix π a ha, hfix π b hb] at h
        · obtain ⟨ha, hb⟩ := hlt _ _ h
          rwa [hfix π a ha, hfix π b hb] }
  have hg : Function.Injective g := by
    intro π ρ h
    apply Equiv.Perm.ofSubtype_injective
    exact Equiv.ext fun x => DFunLike.congr_fun h x
  calc S.card ! = Nat.card (Equiv.Perm S) := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe]
    _ ≤ Nat.card (α ≃o α) := Nat.card_le_card_of_injective g hg

/-- The isolated points of `α`. -/
noncomputable def isoSet (α : Type*) [Fintype α] [PartialOrder α] : Finset α := by
  classical exact univ.filter Isolated

theorem mem_isoSet {x : α} : x ∈ isoSet α ↔ Isolated x := by
  classical
  unfold isoSet
  simp

end MatchingBound

/-! ## L3: a disjoint union of fences has a large matching -/

section Runs

variable (R : ℕ → Prop) [DecidablePred R]

/-- The length of the run of consecutive `R`-positions ending at `i`. -/
def runLen : ℕ → ℕ
  | 0 => if R 0 then 1 else 0
  | i + 1 => if R (i + 1) then runLen (i) + 1 else 0

variable {R}

theorem runLen_ne_zero (i : ℕ) : runLen R i ≠ 0 ↔ R i := by
  cases i with
  | zero => by_cases h : R 0 <;> simp [runLen, h]
  | succ i => by_cases h : R (i + 1) <;> simp [runLen, h]

theorem runLen_succ {i : ℕ} (h : R (i + 1)) : runLen R (i + 1) = runLen R i + 1 := by
  simp [runLen, h]

/-- Odd run lengths are never adjacent. -/
theorem runLen_not_odd_odd (i : ℕ) (h1 : runLen R i % 2 = 1) (h2 : runLen R (i + 1) % 2 = 1) :
    False := by
  have hR : R (i + 1) := (runLen_ne_zero _).1 (by omega)
  rw [runLen_succ hR] at h2
  omega

/-- An `R`-position has odd run length, or its predecessor does. -/
theorem runLen_cover {p : ℕ} (hp : R p) :
    runLen R p % 2 = 1 ∨ ∃ q, p = q + 1 ∧ runLen R q % 2 = 1 := by
  cases p with
  | zero => left; simp [runLen, hp]
  | succ q =>
    by_cases h : runLen R (q + 1) % 2 = 1
    · exact Or.inl h
    · right
      refine ⟨q, rfl, ?_⟩
      rw [runLen_succ hp] at h
      omega

end Runs

section Fence

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- **L3.** A disjoint union of fences on `n` points with `k` isolated points has `t` pairwise
disjoint comparable pairs with `n ≤ 3t + k`. (Greedy matching along the listing: in each maximal
run of comparable neighbours, take every other edge.) -/
theorem exists_matching (hα : IsFenceUnion α) :
    ∃ M : Finset (α × α), (∀ p ∈ M, p.1 < p.2) ∧
      (∀ p ∈ M, ∀ q ∈ M, p ≠ q → p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2) ∧
      Fintype.card α ≤ 3 * M.card + (isoSet α).card := by
  classical
  obtain ⟨e, he⟩ := hα
  let R : ℕ → Prop := fun i => ∃ a b : α, (e a).val = i ∧ (e b).val = i + 1 ∧ (a < b ∨ b < a)
  let I : Finset ℕ := (range (Fintype.card α)).filter fun i => runLen R i % 2 = 1
  have hI : ∀ i, i ∈ I ↔ i < Fintype.card α ∧ runLen R i % 2 = 1 := by intro i; simp [I]
  have hIR : ∀ i ∈ I, R i := fun i hi => (runLen_ne_zero i).1 (by have := ((hI i).1 hi).2; omega)
  have hI2 : ∀ i ∈ I, i + 1 ∉ I := fun i hi hi' =>
    runLen_not_odd_odd i ((hI i).1 hi).2 ((hI _).1 hi').2
  -- the position of the lower element of a pair
  let lo : α × α → ℕ := fun p => min (e p.1).val (e p.2).val
  let M : Finset (α × α) := univ.filter fun p => p.1 < p.2 ∧ lo p ∈ I ∧
    ((e p.1).val + 1 = (e p.2).val ∨ (e p.2).val + 1 = (e p.1).val)
  have hM : ∀ p, p ∈ M ↔ p.1 < p.2 ∧ lo p ∈ I ∧
      ((e p.1).val + 1 = (e p.2).val ∨ (e p.2).val + 1 = (e p.1).val) := by
    intro p; simp [M]
  have hval : ∀ x y : α, (e x).val = (e y).val → x = y := fun x y h =>
    e.injective (Fin.ext h)
  refine ⟨M, fun p hp => ((hM p).1 hp).1, ?_, ?_⟩
  · -- disjointness
    intro p hp q hq hpq
    obtain ⟨hp1, hpI, hpa⟩ := (hM p).1 hp
    obtain ⟨hq1, hqI, hqa⟩ := (hM q).1 hq
    have hne1 : lo p + 1 ≠ lo q := fun h => hI2 _ hpI (h ▸ hqI)
    have hne2 : lo q + 1 ≠ lo p := fun h => hI2 _ hqI (h ▸ hpI)
    simp only [lo] at hne1 hne2
    have hlo : lo p ≠ lo q := by
      intro h
      apply hpq
      simp only [lo] at h
      rcases hpa with hpa | hpa <;> rcases hqa with hqa | hqa
      · have h1 : (e p.1).val = (e q.1).val := by omega
        have h2 : (e p.2).val = (e q.2).val := by omega
        exact Prod.ext (hval _ _ h1) (hval _ _ h2)
      · have h1 : (e p.1).val = (e q.2).val := by omega
        have h2 : (e p.2).val = (e q.1).val := by omega
        rw [hval _ _ h1, hval _ _ h2] at hp1
        exact absurd hp1 (lt_asymm hq1)
      · have h1 : (e p.1).val = (e q.2).val := by omega
        have h2 : (e p.2).val = (e q.1).val := by omega
        rw [hval _ _ h1, hval _ _ h2] at hp1
        exact absurd hp1 (lt_asymm hq1)
      · have h1 : (e p.1).val = (e q.1).val := by omega
        have h2 : (e p.2).val = (e q.2).val := by omega
        exact Prod.ext (hval _ _ h1) (hval _ _ h2)
    simp only [lo] at hlo
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩ <;>
      · have := congrArg (fun x => (e x).val) h
        beta_reduce at this
        omega
  · -- counting
    have hIM : I.card ≤ M.card := by
      have hsub : I ⊆ M.image lo := by
        intro i hi
        obtain ⟨a, b, ha, hb, hab⟩ := hIR i hi
        rw [mem_image]
        rcases hab with hab | hab
        · refine ⟨(a, b), (hM _).2 ⟨hab, ?_, ?_⟩, ?_⟩
          · simp only [lo, ha, hb]; rwa [min_eq_left (Nat.le_succ i)]
          · left; simp only [ha, hb]
          · simp only [lo, ha, hb]; exact min_eq_left (Nat.le_succ i)
        · refine ⟨(b, a), (hM _).2 ⟨hab, ?_, ?_⟩, ?_⟩
          · simp only [lo, ha, hb]; rwa [min_eq_right (Nat.le_succ i)]
          · right; simp only [ha, hb]
          · simp only [lo, ha, hb]; exact min_eq_right (Nat.le_succ i)
      exact (card_le_card hsub).trans card_image_le
    let N : Finset α := (isoSet α)ᶜ
    have hcover : N.image (fun x => (e x).val) ⊆ I ∪ I.image (· + 1) ∪ I.image (· + 2) := by
      intro p hp
      obtain ⟨x, hx, rfl⟩ := mem_image.1 hp
      simp only [N, mem_compl, mem_isoSet, Isolated, not_forall] at hx
      obtain ⟨y, hy⟩ := hx
      have hcomp : x < y ∨ y < x := by
        by_contra h; exact hy ⟨fun h' => h (Or.inl h'), fun h' => h (Or.inr h')⟩
      have key : ∀ i : ℕ, R i → (i = (e x).val ∨ i + 1 = (e x).val) →
          (e x).val ∈ I ∪ I.image (· + 1) ∪ I.image (· + 2) := by
        intro i hRi hix
        have hin : ∀ m, runLen R m % 2 = 1 → m ≤ i → m ∈ I := by
          intro m hm hmi
          obtain ⟨a, b, -, hb, -⟩ := hRi
          exact (hI m).2 ⟨by have := (e b).isLt; omega, hm⟩
        simp only [mem_union, mem_image]
        rcases runLen_cover hRi with h | ⟨q, rfl, hq⟩
        · rcases hix with hix | hix
          · left; left; rw [← hix]; exact hin i h le_rfl
          · left; right; exact ⟨i, hin i h le_rfl, hix⟩
        · rcases hix with hix | hix
          · left; right; exact ⟨q, hin q hq (Nat.le_succ q), hix⟩
          · right; exact ⟨q, hin q hq (Nat.le_succ q), by omega⟩
      rcases hcomp with h | h
      · rcases he x y h with h' | h'
        · exact key _ ⟨x, y, rfl, h'.symm, Or.inl h⟩ (Or.inl rfl)
        · exact key _ ⟨y, x, rfl, h'.symm, Or.inr h⟩ (Or.inr h')
      · rcases he y x h with h' | h'
        · exact key _ ⟨y, x, rfl, h'.symm, Or.inl h⟩ (Or.inr h')
        · exact key _ ⟨x, y, rfl, h'.symm, Or.inr h⟩ (Or.inl rfl)
    have hN : N.card ≤ 3 * I.card := by
      calc N.card = (N.image (fun x => (e x).val)).card :=
            (card_image_of_injective _ (fun x y h => hval x y h)).symm
        _ ≤ (I ∪ I.image (· + 1) ∪ I.image (· + 2)).card := card_le_card hcover
        _ ≤ I.card + I.card + I.card := by
            refine (card_union_le _ _).trans (Nat.add_le_add ((card_union_le _ _).trans
              (Nat.add_le_add_left card_image_le _)) card_image_le)
        _ = 3 * I.card := by ring
    have hsplit : (isoSet α).card + N.card = Fintype.card α := by
      exact card_add_card_compl _
    omega

/-! ## L4 -/

/-- **L4.** For a disjoint union of fences, `f(α) · 2^t · k! ≤ n!` for some `t, k` with
`n ≤ 3t + k`. -/
theorem orbitCount_mul_le (hα : IsFenceUnion α) :
    ∃ t k : ℕ, Fintype.card α ≤ 3 * t + k ∧
      orbitCount α * 2 ^ t * k ! ≤ (Fintype.card α)! := by
  obtain ⟨M, hlt, hdisj, hcard⟩ := exists_matching hα
  refine ⟨M.card, (isoSet α).card, hcard, ?_⟩
  have h1 := two_pow_mul_card_linExt_le M hlt hdisj
  have h2 := factorial_le_card_aut (isoSet α) (fun x hx => mem_isoSet.1 hx)
  rw [card_linExt_eq] at h1
  calc orbitCount α * 2 ^ M.card * (isoSet α).card !
      ≤ orbitCount α * 2 ^ M.card * Nat.card (α ≃o α) := Nat.mul_le_mul_left _ h2
    _ = 2 ^ M.card * (Nat.card (α ≃o α) * orbitCount α) := by ring
    _ ≤ _ := h1

end Fence

/-! ## L5: the construction -/

/-- Graham's poset: tops `Fin j`, bottoms indexed by the subsets in `𝒮`. -/
inductive Gr (j : ℕ) (𝒮 : Finset (Finset (Fin j))) : Type
  | top : Fin j → Gr j 𝒮
  | bot : 𝒮 → Gr j 𝒮
  deriving DecidableEq

namespace Gr

variable {j : ℕ} {𝒮 : Finset (Finset (Fin j))}

/-- `Gr j 𝒮 ≃ Fin j ⊕ 𝒮`. -/
def equivSum : Gr j 𝒮 ≃ Fin j ⊕ 𝒮 where
  toFun
    | top a => .inl a
    | bot S => .inr S
  invFun
    | .inl a => top a
    | .inr S => bot S
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

instance : Fintype (Gr j 𝒮) := Fintype.ofEquiv _ equivSum.symm

/-- The strict order: `b_S < a ↔ a ∈ S`, nothing else. -/
def rel : Gr j 𝒮 → Gr j 𝒮 → Prop
  | bot S, top a => a ∈ S.1
  | _, _ => False

theorem rel_two {x y z : Gr j 𝒮} (h1 : rel x y) (h2 : rel y z) : False := by
  rcases x with a | S <;> rcases y with b | T <;> rcases z with c | U <;> simp [rel] at h1 h2

instance : PartialOrder (Gr j 𝒮) where
  le x y := x = y ∨ rel x y
  lt x y := rel x y
  le_refl _ := Or.inl rfl
  le_trans x y z := by
    rintro (rfl | hxy) (rfl | hyz)
    · exact Or.inl rfl
    · exact Or.inr hyz
    · exact Or.inr hxy
    · exact (rel_two hxy hyz).elim
  lt_iff_le_not_ge x y := by
    constructor
    · intro h
      refine ⟨Or.inr h, ?_⟩
      rintro (rfl | h')
      · exact rel_two h h
      · exact rel_two h h'
    · rintro ⟨rfl | h, h'⟩
      · exact absurd (Or.inl rfl) h'
      · exact h
  le_antisymm x y := by
    rintro (rfl | hxy) (h | hyx)
    · rfl
    · rfl
    · exact h.symm
    · exact (rel_two hxy hyx).elim

theorem lt_iff {x y : Gr j 𝒮} : x < y ↔ rel x y := Iff.rfl

theorem bot_lt_top_iff (S : 𝒮) (a : Fin j) : (bot S : Gr j 𝒮) < top a ↔ a ∈ S.1 := Iff.rfl

theorem not_lt_bot (x : Gr j 𝒮) (S : 𝒮) : ¬ x < bot S := by
  rw [lt_iff]; rcases x with a | T <;> simp [rel]

theorem card_eq : Fintype.card (Gr j 𝒮) = 𝒮.card + j := by
  rw [Fintype.card_congr equivSum, Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, add_comm]

/-- Bottoms first in the order `πB`, then tops in the order `πT`. -/
def ext (πB : 𝒮 ≃ Fin 𝒮.card) (πT : Fin j ≃ Fin j) : Gr j 𝒮 ≃ Fin (Fintype.card (Gr j 𝒮)) :=
  ((equivSum.trans ((Equiv.sumComm (Fin j) 𝒮).trans (Equiv.sumCongr πB πT))).trans
    finSumFinEquiv).trans (finCongr card_eq.symm)

theorem ext_bot (πB : 𝒮 ≃ Fin 𝒮.card) (πT : Fin j ≃ Fin j) (S : 𝒮) :
    (ext πB πT (bot S)).val = (πB S).val := rfl

theorem ext_top (πB : 𝒮 ≃ Fin 𝒮.card) (πT : Fin j ≃ Fin j) (a : Fin j) :
    (ext πB πT (top a)).val = 𝒮.card + (πT a).val := rfl

theorem le_card_linExt : 𝒮.card ! * j ! ≤ Nat.card (LinExt (Gr j 𝒮)) := by
  let F : (𝒮 ≃ Fin 𝒮.card) × (Fin j ≃ Fin j) → LinExt (Gr j 𝒮) := fun π =>
    ⟨ext π.1 π.2, by
      intro x y h
      rcases x with a | S <;> rcases y with b | T <;> simp [lt_iff, rel] at h
      rw [Fin.lt_def, ext_bot, ext_top]
      have := (π.1 S).isLt
      omega⟩
  have hF : Function.Injective F := by
    rintro ⟨πB, πT⟩ ⟨ρB, ρT⟩ h
    have h' : ext πB πT = ext ρB ρT := congrArg Subtype.val h
    have hB : πB = ρB := by
      ext S
      have := congrArg (fun σ => (σ (bot S : Gr j 𝒮)).val) h'
      simpa [ext_bot] using this
    have hT : πT = ρT := by
      ext a
      have := congrArg (fun σ => (σ (top a : Gr j 𝒮)).val) h'
      simpa [ext_top] using this
    rw [hB, hT]
  calc 𝒮.card ! * j ! = Nat.card ((𝒮 ≃ Fin 𝒮.card) × (Fin j ≃ Fin j)) := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
          Fintype.card_equiv (Fintype.equivFinOfCardEq (Fintype.card_coe 𝒮)),
          Fintype.card_equiv (Equiv.refl _), Fintype.card_coe, Fintype.card_fin]
    _ ≤ _ := Nat.card_le_card_of_injective F hF

variable (hU : (univ : Finset (Fin j)) ∈ 𝒮)
include hU

/-- Tops are not minimal (each lies above `b_A`), so automorphisms map tops to tops. -/
theorem top_maps (u : Gr j 𝒮 ≃o Gr j 𝒮) (a : Fin j) : ∃ b, u (top a) = top b := by
  have h : (bot ⟨univ, hU⟩ : Gr j 𝒮) < top a := (bot_lt_top_iff _ _).2 (mem_univ a)
  have h' := u.lt_iff_lt.2 h
  generalize u (top a) = x at h'
  rcases x with b | T
  · exact ⟨b, rfl⟩
  · exact (not_lt_bot _ _ h').elim

/-- Bottoms are minimal, so automorphisms map bottoms to bottoms. -/
theorem bot_maps (u : Gr j 𝒮 ≃o Gr j 𝒮) (S : 𝒮) : ∃ T, u (bot S) = bot T := by
  rcases hx : u (bot S) with b | T
  · exfalso
    have h : (bot ⟨univ, hU⟩ : Gr j 𝒮) < top b := (bot_lt_top_iff _ _).2 (mem_univ b)
    rw [← hx, ← u.apply_symm_apply (bot ⟨univ, hU⟩), u.lt_iff_lt] at h
    exact not_lt_bot _ _ h
  · exact ⟨T, rfl⟩

/-- The action of an automorphism on the tops. -/
noncomputable def topMap (u : Gr j 𝒮 ≃o Gr j 𝒮) : Fin j ↪ Fin j where
  toFun a := (top_maps hU u a).choose
  inj' a b h := by
    have ha := (top_maps hU u a).choose_spec
    have hb := (top_maps hU u b).choose_spec
    have h' : (top_maps hU u a).choose = (top_maps hU u b).choose := h
    rw [← h'] at hb
    have := u.injective (ha.trans hb.symm)
    cases this
    rfl

theorem topMap_spec (u : Gr j 𝒮 ≃o Gr j 𝒮) (a : Fin j) :
    u (top a) = top (topMap hU u a) := (top_maps hU u a).choose_spec

/-- An automorphism is determined by its action on the tops: `b_S` is the unique bottom with
up-set `S`. -/
theorem topMap_injective : Function.Injective (topMap (𝒮 := 𝒮) hU) := by
  intro u v h
  have hT : ∀ a, u (top a) = v (top a) := by
    intro a; rw [topMap_spec hU, topMap_spec hU, h]
  ext x
  rcases x with a | S
  · rw [hT]
  · obtain ⟨T, hT1⟩ := bot_maps hU u S
    obtain ⟨T', hT2⟩ := bot_maps hU v S
    rw [hT1, hT2]
    congr 1
    apply Subtype.ext
    ext c
    obtain ⟨a, ha⟩ := top_maps hU u.symm c
    have hu : u (top a) = top c := by rw [← ha, u.apply_symm_apply]
    have hv : v (top a) = top c := by rw [← hT, hu]
    rw [← bot_lt_top_iff T c, ← bot_lt_top_iff T' c, ← hT1, ← hT2]
    calc u (bot S) < top c ↔ u (bot S) < u (top a) := by rw [hu]
      _ ↔ bot S < top a := u.lt_iff_lt
      _ ↔ v (bot S) < v (top a) := v.lt_iff_lt.symm
      _ ↔ v (bot S) < top c := by rw [hv]

theorem card_aut_le : Nat.card (Gr j 𝒮 ≃o Gr j 𝒮) ≤ j ! := by
  classical
  calc Nat.card (Gr j 𝒮 ≃o Gr j 𝒮) ≤ Nat.card (Fin j ↪ Fin j) :=
        Nat.card_le_card_of_injective _ (topMap_injective hU)
    _ = j ! := by
        rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq, Fintype.card_fin,
          Nat.descFactorial_self]

/-- `f(Gr) ≥ m!`, `m = #𝒮`, as soon as the full set indexes a bottom. -/
theorem orbitCount_Gr : 𝒮.card ! ≤ orbitCount (Gr j 𝒮) := by
  have he := le_card_linExt (j := j) (𝒮 := 𝒮)
  have ha := card_aut_le hU
  rw [card_linExt_eq] at he
  have : 𝒮.card ! * j ! ≤ orbitCount (Gr j 𝒮) * j ! :=
    he.trans (by rw [mul_comm]; exact Nat.mul_le_mul_left _ ha)
  exact Nat.le_of_mul_le_mul_right this (Nat.factorial_pos j)

end Gr

/-- **L5 (strong form).** If `1 ≤ n - j ≤ 2^j` there is an `n`-element poset with
`f ≥ (n - j)!`. (The bottoms may be indexed by any `n - j` subsets containing the full set;
the empty set is allowed.) -/
theorem exists_poset_orbitCount_ge' (n j : ℕ) (h1 : 1 ≤ n - j) (h2 : n - j ≤ 2 ^ j) :
    ∃ (β : Type) (_ : Fintype β) (_ : PartialOrder β),
      Fintype.card β = n ∧ (n - j)! ≤ orbitCount β := by
  obtain ⟨𝒮, hs, -, hcard⟩ := exists_subsuperset_card_eq
    (singleton_subset_iff.2 (mem_univ (univ : Finset (Fin j)))) (by simpa using h1)
    (by simpa [Fintype.card_finset] using h2)
  refine ⟨Gr j 𝒮, inferInstance, inferInstance, ?_, ?_⟩
  · rw [Gr.card_eq, hcard]; omega
  · rw [← hcard]; exact Gr.orbitCount_Gr (hs (mem_singleton_self _))

/-- **L5** as in the answer: bottoms indexed by `n - j ≤ 2^j - 1` nonempty subsets. -/
theorem exists_poset_orbitCount_ge (n j : ℕ) (h1 : 1 ≤ n - j) (h2 : n - j ≤ 2 ^ j - 1) :
    ∃ (β : Type) (_ : Fintype β) (_ : PartialOrder β),
      Fintype.card β = n ∧ (n - j)! ≤ orbitCount β :=
  exists_poset_orbitCount_ge' n j h1 (h2.trans (Nat.sub_le _ _))

/-! ## L6: arithmetic -/

theorem exists_J (n : ℕ) : ∃ j, n ≤ 2 ^ j + j - 1 :=
  ⟨n, by have := Nat.one_le_two_pow (n := n); omega⟩

/-- `J n`: the least `j` with `n ≤ 2^j + j - 1`. -/
def J (n : ℕ) : ℕ := Nat.find (exists_J n)

theorem J_spec (n : ℕ) : n ≤ 2 ^ J n + J n - 1 := Nat.find_spec (exists_J n)

theorem J_le {n j : ℕ} (h : n ≤ 2 ^ j + j - 1) : J n ≤ j := Nat.find_min' (exists_J n) h

theorem two_pow_le_two_mul_factorial_cube (k : ℕ) : 2 ^ k ≤ 2 * (k !) ^ 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have h2 : 2 ≤ (k + 1) ^ 3 :=
        (show 2 ≤ k + 1 by omega).trans (Nat.le_self_pow (by norm_num) _)
      calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
        _ ≤ 2 * (2 * (k !) ^ 3) := Nat.mul_le_mul_left _ ih
        _ ≤ 2 * ((k + 1) ^ 3 * (k !) ^ 3) := by
            have := Nat.mul_le_mul_right ((k !) ^ 3) h2
            omega
        _ = 2 * ((k + 1)! ) ^ 3 := by rw [Nat.factorial_succ]; ring

theorem small_range : ∀ n, n < 256 → 181 ≤ n → 2 * n ^ 24 < 2 ^ n := by
  intro n h1 h2
  interval_cases n <;> norm_num

theorem r_bound (r : ℕ) (hr : 8 ≤ r) : 3 * (r + 1) ^ 2 + 1 ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    rw [pow_succ 2 r]
    nlinarith [ih, Nat.mul_le_mul hr hr]

theorem two_mul_pow_J_lt {n : ℕ} (hn : 181 ≤ n) : 2 * n ^ (3 * J n) < 2 ^ n := by
  set r := Nat.log 2 n
  have h1 : 2 ^ r ≤ n := Nat.pow_log_le_self 2 (by omega)
  have h2 : n < 2 ^ (r + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hJ : J n ≤ r + 1 := J_le (by omega)
  have hn1 : 1 ≤ n := by omega
  by_cases hr : r ≤ 7
  · have h256 : n < 256 :=
      lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by norm_num) (by omega) : 2 ^ (r + 1) ≤ 2 ^ 8)
    have hJ8 : J n ≤ 8 := J_le (by norm_num; omega)
    calc 2 * n ^ (3 * J n) ≤ 2 * n ^ 24 :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn1 (by omega))
      _ < 2 ^ n := small_range n h256 hn
  · replace hr : 8 ≤ r := by omega
    have h3 : n ^ (3 * J n) ≤ n ^ (3 * (r + 1)) := Nat.pow_le_pow_right hn1 (by omega)
    have h4 : n ^ (3 * (r + 1)) < (2 ^ (r + 1)) ^ (3 * (r + 1)) :=
      Nat.pow_lt_pow_left h2 (by omega)
    have h5 : 3 * (r + 1) ^ 2 + 1 ≤ n := (r_bound r hr).trans h1
    calc 2 * n ^ (3 * J n) < 2 * (2 ^ (r + 1)) ^ (3 * (r + 1)) :=
          Nat.mul_lt_mul_of_pos_left (h3.trans_lt h4) (by norm_num)
      _ = 2 ^ (3 * (r + 1) ^ 2 + 1) := by rw [← pow_mul]; ring
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h5

/-- **L6.** For `n ≥ 181` and `n ≤ 3t + k`: `n! < (n - J n)! · 2^t · k!`. -/
theorem factorial_lt {n t k : ℕ} (hn : 181 ≤ n) (h : n ≤ 3 * t + k) :
    n ! < (n - J n)! * 2 ^ t * k ! := by
  have hJn : J n ≤ n := J_le (by have := Nat.one_le_two_pow (n := n); omega)
  set P := n.descFactorial (J n)
  have hP : P ≤ n ^ J n := Nat.descFactorial_le_pow n _
  have hfac : (n - J n)! * P = n ! := Nat.factorial_mul_descFactorial hJn
  have ha : 2 * P ^ 3 ≤ 2 * n ^ (3 * J n) := by
    rw [mul_comm 3, pow_mul]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP 3)
  have hb : 2 ^ n ≤ 2 * (2 ^ t * k !) ^ 3 := by
    calc 2 ^ n ≤ 2 ^ (3 * t + k) := Nat.pow_le_pow_right (by norm_num) h
      _ = (2 ^ t) ^ 3 * 2 ^ k := by ring
      _ ≤ (2 ^ t) ^ 3 * (2 * (k !) ^ 3) :=
          Nat.mul_le_mul_left _ (two_pow_le_two_mul_factorial_cube k)
      _ = 2 * (2 ^ t * k !) ^ 3 := by ring
  have hcube : P ^ 3 < (2 ^ t * k !) ^ 3 :=
    Nat.lt_of_mul_lt_mul_left ((ha.trans_lt (two_mul_pow_J_lt hn)).trans_le hb)
  have hlt : P < 2 ^ t * k ! := (Nat.pow_lt_pow_iff_left (by norm_num)).1 hcube
  rw [← hfac, mul_assoc]
  exact Nat.mul_lt_mul_of_pos_left hlt (Nat.factorial_pos _)

/-! ## T -/

/-- **T.** For `n ≥ 181`, an `n`-element disjoint union of fences has fewer orbits than Graham's
poset with `j = J n`, so it does not attain `g(n)`. -/
theorem fence_union_not_max {α : Type*} [Fintype α] [PartialOrder α]
    (hn : 181 ≤ Fintype.card α) (hα : IsFenceUnion α) :
    ∃ (β : Type) (_ : Fintype β) (_ : PartialOrder β),
      Fintype.card β = Fintype.card α ∧ orbitCount α < orbitCount β := by
  set n := Fintype.card α
  obtain ⟨t, k, hcard, hle⟩ := orbitCount_mul_le hα
  have hlt := factorial_lt hn hcard
  have hJn : J n ≤ n - 1 := J_le (by
    have : 1 < 2 ^ (n - 1) := Nat.one_lt_two_pow (by omega)
    omega)
  have h1 : 1 ≤ n - J n := by omega
  have h2 : n - J n ≤ 2 ^ J n - 1 := by
    have := J_spec n; have := Nat.one_le_two_pow (n := J n); omega
  obtain ⟨β, iF, iP, hβ, hf⟩ := exists_poset_orbitCount_ge n (J n) h1 h2
  refine ⟨β, iF, iP, hβ, ?_⟩
  have : orbitCount α * (2 ^ t * k !) < orbitCount β * (2 ^ t * k !) := by
    calc orbitCount α * (2 ^ t * k !) = orbitCount α * 2 ^ t * k ! := by ring
      _ ≤ n ! := hle
      _ < (n - J n)! * 2 ^ t * k ! := hlt
      _ ≤ orbitCount β * 2 ^ t * k ! := by gcongr
      _ = orbitCount β * (2 ^ t * k !) := by ring
  exact Nat.lt_of_mul_lt_mul_right this

/-- **T**, negative form: no `n`-element disjoint union of fences with `n ≥ 181` maximises
`f` among `n`-element posets. -/
theorem fence_union_not_max' {α : Type*} [Fintype α] [PartialOrder α]
    (hn : 181 ≤ Fintype.card α) (hα : IsFenceUnion α) :
    ¬ ∀ (β : Type) [Fintype β] [PartialOrder β],
      Fintype.card β = Fintype.card α → orbitCount β ≤ orbitCount α := by
  intro h
  obtain ⟨β, iF, iP, hβ, hlt⟩ := fence_union_not_max hn hα
  exact absurd (h β hβ) (not_le.2 hlt)

end Orbits516140
