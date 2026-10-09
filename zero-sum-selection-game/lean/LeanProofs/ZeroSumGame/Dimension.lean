import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.GroupTheory.CosetCover
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!+# The matrix selection game (MathOverflow 453809)

Positions, rather than numerical values, are selected. Row lengths may vary.
The incidence-rank bound is proved by coordinate deletion, without Helly.
-/

noncomputable section
open Finset Module

namespace ZeroSumGame

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Transversal (N : I → ℕ) := (i : I) → Fin (N i)
abbrev Position (N : I → ℕ) := Sigma (fun i => Fin (N i))
abbrev Array (N : I → ℕ) := Position N → ℝ

def incidence {N : I → ℕ} (t : Transversal N) : Array N :=
  fun p => if t p.1 = p.2 then 1 else 0

def incidenceSpan {N : I → ℕ} (H : Set (Transversal N)) : Submodule ℝ (Array N) :=
  Submodule.span ℝ (incidence '' H)

/-- Every deletion profile within the given budgets leaves a surviving edge. -/
def Hits {N : I → ℕ} (q : I → ℕ) (H : Set (Transversal N)) : Prop :=
  ∀ D : (i : I) → Finset (Fin (N i)), (∀ i, (D i).card ≤ q i) →
    ∃ t ∈ H, ∀ i, t i ∉ D i

omit [Fintype I] [DecidableEq I] in
lemma hits_nonempty {N : I → ℕ} {q : I → ℕ} {H : Set (Transversal N)}
    (h : Hits q H) : H.Nonempty := by
  obtain ⟨t, ht, _⟩ := h (fun _ => ∅) (by simp)
  exact ⟨t, ht⟩

omit [Fintype I] [DecidableEq I] in
lemma incidenceSpan_mono {N : I → ℕ} {H G : Set (Transversal N)} (h : H ⊆ G) :
    incidenceSpan H ≤ incidenceSpan G :=
  Submodule.span_mono (Set.image_mono h)

omit [Fintype I] [DecidableEq I] in
lemma span_coordinate_zero {N : I → ℕ} {H : Set (Transversal N)}
    (i : I) (j : Fin (N i)) (h : ∀ t ∈ H, t i ≠ j)
    {v : Array N} (hv : v ∈ incidenceSpan H) : v ⟨i, j⟩ = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    simp [incidence, h t ht]
  | zero => rfl
  | add x y hx hy ihx ihy => simp [ihx, ihy]
  | smul a x hx ih => simp [ih]

omit [DecidableEq I] in
/-- Deleting an occupied coordinate strictly lowers incidence rank. -/
lemma deletion_rank_lt {N : I → ℕ} {H : Set (Transversal N)}
    (t : Transversal N) (ht : t ∈ H) (i : I) :
    finrank ℝ (incidenceSpan {u | u ∈ H ∧ u i ≠ t i}) <
      finrank ℝ (incidenceSpan H) := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne (incidenceSpan_mono (by intro u hu; exact hu.1))
  intro heq
  have htspan : incidence t ∈ incidenceSpan H :=
    Submodule.subset_span ⟨t, ht, rfl⟩
  rw [← heq] at htspan
  have hz := span_coordinate_zero i (t i) (fun u hu => hu.2) htspan
  simp [incidence] at hz

/-- The sharp incidence-rank bound, valid for arbitrary row lengths and budgets. -/
theorem incidence_rank_bound [Nonempty I] {N : I → ℕ}
    (q : I → ℕ) (H : Set (Transversal N)) (h : Hits q H) :
    (∑ i, q i) + 1 ≤ finrank ℝ (incidenceSpan H) := by
  generalize hs : (∑ i, q i) = s
  induction s using Nat.strong_induction_on generalizing q H with
  | h s ih =>
    obtain ⟨t, ht⟩ := hits_nonempty h
    by_cases hz : s = 0
    · subst s
      have hn : incidenceSpan H ≠ ⊥ := by
        intro heq
        have hm : incidence t ∈ incidenceSpan H := Submodule.subset_span ⟨t, ht, rfl⟩
        rw [heq, Submodule.mem_bot] at hm
        let i : I := Classical.arbitrary I
        have := congrFun hm (⟨i, t i⟩ : Position N)
        simp [incidence] at this
      have hp : 0 < finrank ℝ (incidenceSpan H) := by
        exact Nat.pos_of_ne_zero (fun h0 => hn (Submodule.finrank_eq_zero.mp h0))
      omega
    · have hpos : 0 < ∑ i, q i := by omega
      obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hpos
      let q' := Function.update q i (q i - 1)
      let H' : Set (Transversal N) := {u | u ∈ H ∧ u i ≠ t i}
      have hsum : (∑ a, q' a) + 1 = ∑ a, q a := by
        dsimp [q']
        rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
        have he := Finset.sum_erase_add (s := Finset.univ) q (Finset.mem_univ i)
        have hd : (Finset.univ \ {i} : Finset I) = Finset.univ.erase i := by ext a; simp
        rw [hd]
        omega
      have hh : Hits q' H' := by
        intro D hD
        let E : (a : I) → Finset (Fin (N a)) :=
          fun a => if ha : a = i then insert (ha.symm ▸ t i) (D a) else D a
        have hE : ∀ a, (E a).card ≤ q a := by
          intro a
          by_cases ha : a = i
          · subst a
            have hc := Finset.card_insert_le (t i) (D i)
            have hd := hD i
            simp [q'] at hd
            simpa [E] using (show (insert (t i) (D i)).card ≤ q i by omega)
          · simpa [E, ha, q', Function.update, ha] using hD a
        obtain ⟨u, hu, hav⟩ := h E hE
        have hui : u i ≠ t i := by
          have := hav i
          simp [E, Finset.mem_insert] at this
          exact this.1
        refine ⟨u, ⟨hu, hui⟩, ?_⟩
        intro a
        by_cases ha : a = i
        · subst a
          have := hav i
          simp [E, Finset.mem_insert] at this
          exact this.2
        · simpa [E, ha] using hav a
      have hlt : (∑ a, q' a) < s := by omega
      have hind := ih (∑ a, q' a) hlt q' H' hh rfl
      have hrank := deletion_rank_lt t ht i
      change finrank ℝ (incidenceSpan H') < finrank ℝ (incidenceSpan H) at hrank
      omega

def transversalSum {N : I → ℕ} (a : Array N) (t : Transversal N) : ℝ :=
  ∑ i, a ⟨i, t i⟩

def Winning {N : I → ℕ} (k : I → ℕ) (a : Array N) : Prop :=
  ∀ S : (i : I) → Finset (Fin (N i)), (∀ i, (S i).card = k i) →
    ∃ t : Transversal N, (∀ i, t i ∈ S i) ∧ transversalSum a t = 0

def zeroTransversals {N : I → ℕ} (a : Array N) : Set (Transversal N) :=
  {t | transversalSum a t = 0}

omit [DecidableEq I] in
/-- The deletion formulation agrees with the original exact-quota game. -/
theorem winning_iff_hits {N : I → ℕ} (k : I → ℕ) (hk : ∀ i, k i ≤ N i)
    (a : Array N) : Winning k a ↔ Hits (fun i => N i - k i) (zeroTransversals a) := by
  constructor
  · intro hw D hD
    have hc : ∀ i, k i ≤ (D i)ᶜ.card := by
      intro i
      rw [Finset.card_compl, Fintype.card_fin]
      have hb : (D i).card ≤ N i - k i := hD i
      have := hk i
      omega
    choose S hsub hcard using fun i => Finset.exists_subset_card_eq (hc i)
    obtain ⟨t, ht, hz⟩ := hw S hcard
    exact ⟨t, hz, fun i => by simpa using hsub i (ht i)⟩
  · intro hh S hS
    have hD : ∀ i, (S i)ᶜ.card ≤ N i - k i := by
      intro i
      simp [Finset.card_compl, hS i]
    obtain ⟨t, hz, ht⟩ := hh (fun i => (S i)ᶜ) hD
    exact ⟨t, by simpa using ht, hz⟩

def dotEquiv (N : I → ℕ) : Array N ≃ₗ[ℝ] Module.Dual ℝ (Array N) :=
  (Pi.basisFun ℝ (Position N)).toDualEquiv

lemma dotEquiv_apply {N : I → ℕ} (v a : Array N) :
    dotEquiv N v a = ∑ p, v p * a p := by
  let b := Pi.basisFun ℝ (Position N)
  change b.toDual v a = _
  conv_lhs => arg 2; rw [← b.sum_repr a]
  simp only [map_sum, map_smul, smul_eq_mul]
  simp_rw [b.toDual_apply_left]
  simp [b, mul_comm]

lemma incidence_dot {N : I → ℕ} (t : Transversal N) (a : Array N) :
    dotEquiv N (incidence t) a = transversalSum a t := by
  rw [dotEquiv_apply, Fintype.sum_sigma]
  simp [incidence, transversalSum, ite_mul]

/-- All arrays on which the specified transversals have zero sum. -/
def template {N : I → ℕ} (H : Set (Transversal N)) : Submodule ℝ (Array N) :=
  ((incidenceSpan H).map (dotEquiv N).toLinearMap).dualCoannihilator

lemma mem_template_iff {N : I → ℕ} (H : Set (Transversal N)) (a : Array N) :
    a ∈ template H ↔ ∀ t ∈ H, transversalSum a t = 0 := by
  rw [template, Submodule.mem_dualCoannihilator]
  constructor
  · intro ha t ht
    rw [← incidence_dot]
    exact ha _ ⟨incidence t, Submodule.subset_span ⟨t, ht, rfl⟩, rfl⟩
  · intro ha f hf
    obtain ⟨v, hv, rfl⟩ := hf
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      exact (incidence_dot t a).trans (ha t ht)
    | zero => simp
    | add x y hx hy ihx ihy =>
      change dotEquiv N x a = 0 at ihx
      change dotEquiv N y a = 0 at ihy
      simp [ihx, ihy]
    | smul c x hx ih =>
      change dotEquiv N x a = 0 at ih
      simp [ih]

lemma template_dimension_identity {N : I → ℕ} (H : Set (Transversal N)) :
    finrank ℝ (incidenceSpan H) + finrank ℝ (template H) = ∑ i, N i := by
  have h := Subspace.finrank_add_finrank_dualCoannihilator_eq
    ((incidenceSpan H).map (dotEquiv N).toLinearMap)
  rw [(dotEquiv N).finrank_map_eq] at h
  change finrank ℝ (incidenceSpan H) + finrank ℝ (template H) = finrank ℝ (Array N) at h
  rw [show finrank ℝ (Array N) = ∑ i, N i by
    simp [Array, Position, Fintype.card_sigma]] at h
  exact h

theorem template_dimension_bound [Nonempty I] {N : I → ℕ}
    (k : I → ℕ) (hk : ∀ i, k i ≤ N i) (H : Set (Transversal N))
    (hH : Hits (fun i => N i - k i) H) :
    finrank ℝ (template H) ≤ (∑ i, k i) - 1 := by
  have hr := incidence_rank_bound (fun i => N i - k i) H hH
  have hd := template_dimension_identity H
  have hs : (∑ i, (N i - k i)) + (∑ i, k i) = ∑ i, N i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.sub_add_cancel (hk i)
  omega

theorem template_winning {N : I → ℕ} (k : I → ℕ) (hk : ∀ i, k i ≤ N i)
    (H : Set (Transversal N)) (hH : Hits (fun i => N i - k i) H)
    {a : Array N} (ha : a ∈ template H) : Winning k a := by
  rw [winning_iff_hits k hk]
  intro D hD
  obtain ⟨t, ht, hav⟩ := hH D hD
  exact ⟨t, (mem_template_iff H a).mp ha t ht, hav⟩

/-- An exact finite union of linear spaces, indexed by covering zero patterns. -/
theorem winning_iff_mem_template {N : I → ℕ} (k : I → ℕ)
    (hk : ∀ i, k i ≤ N i) (a : Array N) :
    Winning k a ↔ ∃ H : Set (Transversal N),
      Hits (fun i => N i - k i) H ∧ a ∈ template H := by
  constructor
  · intro ha
    exact ⟨zeroTransversals a, (winning_iff_hits k hk a).mp ha,
      (mem_template_iff _ _).mpr (fun _ ht => ht)⟩
  · rintro ⟨H, hH, ha⟩
    exact template_winning k hk H hH ha

/-- Every linear family of winning arrays is contained in one covering template. -/
theorem winning_subspace_contained {N : I → ℕ} (k : I → ℕ)
    (hk : ∀ i, k i ≤ N i) (L : Submodule ℝ (Array N))
    (hL : ∀ a ∈ L, Winning k a) :
    ∃ H : Set (Transversal N), Hits (fun i => N i - k i) H ∧ L ≤ template H := by
  classical
  let J := {H : Set (Transversal N) // Hits (fun i => N i - k i) H}
  let p : J → Submodule ℝ L := fun H => (template H.val).comap L.subtype
  have hc : (⋃ H : J, (p H : Set L)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    obtain ⟨H, hH, ha⟩ := (winning_iff_mem_template k hk a.val).mp (hL a.val a.property)
    exact Set.mem_iUnion.mpr ⟨⟨H, hH⟩, ha⟩
  obtain ⟨H, hH⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hc
  refine ⟨H.val, H.property, ?_⟩
  intro a ha
  have hm : (⟨a, ha⟩ : L) ∈ p H := by rw [hH]; trivial
  exact hm

/-- Upper bound for every winning linear family, not only the listed templates. -/
theorem winning_subspace_dimension_bound [Nonempty I] {N : I → ℕ}
    (k : I → ℕ) (hk : ∀ i, k i ≤ N i) (L : Submodule ℝ (Array N))
    (hL : ∀ a ∈ L, Winning k a) : finrank ℝ L ≤ (∑ i, k i) - 1 := by
  obtain ⟨H, hH, hLH⟩ := winning_subspace_contained k hk L hL
  exact (Submodule.finrank_mono hLH).trans (template_dimension_bound k hk H hH)

def rowSum : (I → ℝ) →ₗ[ℝ] ℝ where
  toFun b := ∑ i, b i
  map_add' b c := by simp [Finset.sum_add_distrib]
  map_smul' c b := by simp [Finset.mul_sum]

lemma rowSum_surjective [Nonempty I] : Function.Surjective (rowSum (I := I)) := by
  intro x
  let i : I := Classical.arbitrary I
  exact ⟨Pi.single i x, by simp [rowSum]⟩

lemma rowSum_ker_dimension [Nonempty I] :
    finrank ℝ (LinearMap.ker (rowSum (I := I))) = Fintype.card I - 1 := by
  have h := (rowSum (I := I)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr rowSum_surjective] at h
  simp only [finrank_top, finrank_self, Module.finrank_pi] at h
  omega

abbrev FreePosition (k : I → ℕ) := Sigma (fun i => Fin (k i - 1))
abbrev Parameters (k : I → ℕ) :=
  (FreePosition k → ℝ) × LinearMap.ker (rowSum (I := I))

/-- Free leading positions followed by a repeated row value whose row sums vanish. -/
def dominantMap (N k : I → ℕ) : Parameters k →ₗ[ℝ] Array N where
  toFun p pos := if h : pos.2.val < k pos.1 - 1
    then p.1 ⟨pos.1, ⟨pos.2.val, h⟩⟩ else p.2.val pos.1
  map_add' p r := by ext pos; dsimp; split <;> rfl
  map_smul' c p := by ext pos; dsimp; split <;> rfl

omit [DecidableEq I] in
lemma dominantMap_injective {N : I → ℕ} (k : I → ℕ)
    (hk : ∀ i, k i ≤ N i) (hpos : ∀ i, 0 < k i) :
    Function.Injective (dominantMap N k) := by
  intro p r h
  have hb : p.2 = r.2 := by
    apply Subtype.ext
    funext i
    let j : Fin (N i) := ⟨k i - 1, by have := hk i; have := hpos i; omega⟩
    have he := congrFun h (⟨i, j⟩ : Position N)
    simpa [dominantMap, j] using he
  have hf : p.1 = r.1 := by
    funext pos
    let j : Fin (N pos.1) := ⟨pos.2.val, by
      have := pos.2.isLt; have := hk pos.1; omega⟩
    have he := congrFun h (⟨pos.1, j⟩ : Position N)
    simpa [dominantMap, j, pos.2.isLt] using he
  exact Prod.ext hf hb

lemma large_menu_has_tail {n k : ℕ} (hk : k ≤ n) (hpos : 0 < k)
    (S : Finset (Fin n)) (hS : S.card = k) :
    ∃ j ∈ S, k - 1 ≤ j.val := by
  by_contra! h
  let b : Fin n := ⟨k - 1, by omega⟩
  have hs : S ⊆ Finset.Iio b := by
    intro j hj
    exact Finset.mem_Iio.mpr (h j hj)
  have hc := Finset.card_le_card hs
  rw [Fin.card_Iio, hS] at hc
  dsimp [b] at hc
  omega

omit [DecidableEq I] in
theorem dominantMap_winning {N : I → ℕ} (k : I → ℕ)
    (hk : ∀ i, k i ≤ N i) (hpos : ∀ i, 0 < k i) (p : Parameters k) :
    Winning k (dominantMap N k p) := by
  intro S hS
  choose t ht htail using fun i => large_menu_has_tail (hk i) (hpos i) (S i) (hS i)
  refine ⟨t, ht, ?_⟩
  have hz := p.2.property
  change (∑ i, p.2.val i) = 0 at hz
  simpa [transversalSum, dominantMap, not_lt.mpr (htail _)] using hz

lemma parameters_dimension [Nonempty I] (k : I → ℕ) (hpos : ∀ i, 0 < k i) :
    finrank ℝ (Parameters k) = (∑ i, k i) - 1 := by
  have hs : (∑ i, (k i - 1)) + Fintype.card I = ∑ i, k i := by
    have hc : Fintype.card I = ∑ _i : I, 1 := by simp
    rw [hc, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have := hpos i
    omega
  have hi : 0 < Fintype.card I := Fintype.card_pos
  simp only [Parameters, Module.finrank_prod, Module.finrank_pi,
    rowSum_ker_dimension, Fintype.card_sigma, Fintype.card_fin]
  omega

/-- A winning family with exactly the claimed number of independent parameters. -/
theorem sharp_winning_subspace [Nonempty I] {N : I → ℕ} (k : I → ℕ)
    (hk : ∀ i, k i ≤ N i) (hpos : ∀ i, 0 < k i) :
    ∃ L : Submodule ℝ (Array N),
      (∀ a ∈ L, Winning k a) ∧ finrank ℝ L = (∑ i, k i) - 1 := by
  refine ⟨(dominantMap N k).range, ?_, ?_⟩
  · rintro a ⟨p, rfl⟩
    exact dominantMap_winning k hk hpos p
  · rw [LinearMap.finrank_range_of_inj (dominantMap_injective k hk hpos)]
    exact parameters_dimension k hpos

/-- The sharp general dimension theorem, formulated as an upper bound plus attainment. -/
theorem sharp_dimension_theorem [Nonempty I] {N : I → ℕ} (k : I → ℕ)
    (hk : ∀ i, k i ≤ N i) (hpos : ∀ i, 0 < k i) :
    (∀ L : Submodule ℝ (Array N), (∀ a ∈ L, Winning k a) →
      finrank ℝ L ≤ (∑ i, k i) - 1) ∧
    (∃ L : Submodule ℝ (Array N), (∀ a ∈ L, Winning k a) ∧
      finrank ℝ L = (∑ i, k i) - 1) := by
  exact ⟨fun L hL => winning_subspace_dimension_bound k hk L hL,
    sharp_winning_subspace k hk hpos⟩

/-- The winning set is literally a finite union of bounded-dimensional submodules. -/
theorem winning_finite_union [Nonempty I] {N : I → ℕ} (k : I → ℕ)
    (hk : ∀ i, k i ≤ N i) :
    ∃ F : Finset (Submodule ℝ (Array N)),
      (∀ L ∈ F, finrank ℝ L ≤ (∑ i, k i) - 1) ∧
      {a : Array N | Winning k a} = ⋃ L ∈ F, (L : Set (Array N)) := by
  classical
  let J := {H : Set (Transversal N) // Hits (fun i => N i - k i) H}
  let : Fintype J := Fintype.ofFinite J
  let F := Finset.univ.image (fun H : J => template H.val)
  refine ⟨F, ?_, ?_⟩
  · intro L hL
    obtain ⟨H, _, rfl⟩ := Finset.mem_image.mp hL
    exact template_dimension_bound k hk H.val H.property
  · ext a
    constructor
    · intro ha
      obtain ⟨H, hH, hm⟩ := (winning_iff_mem_template k hk a).mp ha
      apply Set.mem_iUnion.mpr
      refine ⟨template H, Set.mem_iUnion.mpr ⟨?_, hm⟩⟩
      exact Finset.mem_image.mpr ⟨⟨H, hH⟩, Finset.mem_univ _, rfl⟩
    · intro ha
      obtain ⟨L, hL⟩ := Set.mem_iUnion.mp ha
      obtain ⟨hLF, haL⟩ := Set.mem_iUnion.mp hL
      obtain ⟨H, _, rfl⟩ := Finset.mem_image.mp hLF
      exact template_winning k hk H.val H.property haL

lemma square_quota_sum (n : ℕ) :
    (∑ i : Fin n, (i.val + 1)) = n * (n + 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => j + 1) n]
  have h := Finset.sum_range_id (n + 1)
  rw [Finset.sum_range_succ'] at h
  simpa [Nat.mul_comm] using h

/-- The original game has maximum winning-family dimension n(n+1)/2 - 1. -/
theorem square_sharp_dimension (n : ℕ) (hn : 0 < n) :
    (∀ L : Submodule ℝ (Array (fun _ : Fin n => n)),
      (∀ a ∈ L, Winning (fun i : Fin n => i.val + 1) a) →
      finrank ℝ L ≤ n * (n + 1) / 2 - 1) ∧
    (∃ L : Submodule ℝ (Array (fun _ : Fin n => n)),
      (∀ a ∈ L, Winning (fun i : Fin n => i.val + 1) a) ∧
      finrank ℝ L = n * (n + 1) / 2 - 1) := by
  let : NeZero n := ⟨by omega⟩
  have h := sharp_dimension_theorem (N := fun _ : Fin n => n)
    (fun i : Fin n => i.val + 1) (fun i => by have := i.isLt; omega)
    (fun _ => by omega)
  simpa only [square_quota_sum] using h

omit [DecidableEq I] in
lemma transversalSum_add {N : I → ℕ} (a b : Array N) (t : Transversal N) :
    transversalSum (a + b) t = transversalSum a t + transversalSum b t := by
  simp [transversalSum, Finset.sum_add_distrib]

omit [DecidableEq I] in
lemma transversalSum_smul {N : I → ℕ} (r : ℝ) (b : Array N) (t : Transversal N) :
    transversalSum (r • b) t = r * transversalSum b t := by
  simp [transversalSum, Finset.mul_sum]

/-- If an entire affine line is winning, its direction is winning. -/
theorem winning_line_direction {N : I → ℕ} (k : I → ℕ) (a b : Array N)
    (h : ∀ r : ℝ, Winning k (a + r • b)) : Winning k b := by
  classical
  intro S hS
  by_contra hn
  have hb : ∀ t : Transversal N, (∀ i, t i ∈ S i) → transversalSum b t ≠ 0 := by
    intro t ht hz
    exact hn ⟨t, ht, hz⟩
  let T : Finset (Transversal N) := Finset.univ.filter (fun t => ∀ i, t i ∈ S i)
  let roots : Finset ℝ := T.image (fun t => -transversalSum a t / transversalSum b t)
  obtain ⟨r, hr⟩ := roots.finite_toSet.exists_notMem
  obtain ⟨t, ht, hz⟩ := h r S hS
  rw [transversalSum_add, transversalSum_smul] at hz
  have he : r = -transversalSum a t / transversalSum b t := by
    apply (eq_div_iff (hb t ht)).mpr
    linarith
  apply hr
  exact Finset.mem_image.mpr ⟨t, by simp [T, ht], he.symm⟩

/-- The same dimension bound holds for affine families a + L. -/
theorem winning_affine_family_dimension_bound [Nonempty I] {N : I → ℕ}
    (k : I → ℕ) (hk : ∀ i, k i ≤ N i) (a : Array N)
    (L : Submodule ℝ (Array N)) (h : ∀ b ∈ L, Winning k (a + b)) :
    finrank ℝ L ≤ (∑ i, k i) - 1 := by
  apply winning_subspace_dimension_bound k hk L
  intro b hb
  exact winning_line_direction k a b (fun r => h (r • b) (L.smul_mem r hb))

end ZeroSumGame
