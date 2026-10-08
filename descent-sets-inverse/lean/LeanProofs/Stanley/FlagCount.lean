/-
  Finite permutation characters for descent blocks. Burnside's lemma evaluates
  the Gram matrix of these characters as diagonal orbit counts. The bridge
  between these orbits and jointSubsetCount is a separate combinatorial task.
-/
import LeanProofs.Stanley.JointCount
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Order.Interval.Set.Monotone

namespace Stanley.Alt
open Finset
open scoped Nat

/-- Allowed descent positions separate consecutive position blocks. -/
def block (A : Finset ℕ) (i : ℕ) : ℕ := (A.filter (· < i)).card

theorem block_monotone (A : Finset ℕ) : Monotone (block A) := by
  intro i j hij
  apply card_le_card
  intro r hr
  simp only [mem_filter] at hr ⊢
  exact ⟨hr.1, lt_of_lt_of_le hr.2 hij⟩

theorem block_succ_eq_iff (A : Finset ℕ) (i : ℕ) :
    block A (i + 1) = block A i ↔ i ∉ A := by
  by_cases hi : i ∈ A
  · have hs : A.filter (· < i + 1) = insert i (A.filter (· < i)) := by
      ext r
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨hr, hlt⟩
        by_cases he : r = i
        · exact Or.inl he
        · exact Or.inr ⟨hr, by omega⟩
      · rintro (rfl | ⟨hr, hlt⟩)
        · exact ⟨hi, by omega⟩
        · exact ⟨hr, by omega⟩
    unfold block
    rw [hs, card_insert_of_notMem (by simp)]
    simp [hi]
  · have hs : A.filter (· < i + 1) = A.filter (· < i) := by
      ext r
      simp only [mem_filter]
      constructor
      · rintro ⟨hr, hlt⟩
        refine ⟨hr, ?_⟩
        have : r ≠ i := fun he => hi (he ▸ hr)
        omega
      · rintro ⟨hr, hlt⟩; exact ⟨hr, by omega⟩
    unfold block
    rw [hs]
    simp [hi]

/-- Containment of the descent set means that each position block is increasing. -/
theorem descP_subset_iff_blocks {n : ℕ} (w : Equiv.Perm (Fin n)) (A : Finset ℕ) :
    descP w ⊆ A ↔ ∀ (i j : Fin n), block A i = block A j → i < j → w i < w j := by
  constructor
  · intro hw i j hb hij
    let f : ℕ → ℕ := fun r => if h : r < n then (w ⟨r, h⟩ : ℕ) else 0
    let Q : Set ℕ := {r | r < n ∧ block A r = block A i}
    have hQ : Q.OrdConnected := by
      constructor
      intro a ha b hb r hr
      refine ⟨lt_of_le_of_lt hr.2 hb.1, ?_⟩
      have h1 := block_monotone A hr.1
      have h2 := block_monotone A hr.2
      exact le_antisymm (h2.trans (le_of_eq hb.2)) ((le_of_eq ha.2.symm).trans h1)
    have hf : StrictMonoOn f Q := by
      apply strictMonoOn_of_lt_succ hQ
      intro r _ hr hs
      have hn : r + 1 < n := hs.1
      have he : block A (r + 1) = block A r := hs.2.trans hr.2.symm
      have hnot := (block_succ_eq_iff A r).mp he
      have hnd : ¬ w ⟨r + 1, hn⟩ < w ⟨r, by omega⟩ := by
        intro hd
        apply hnot
        apply hw
        simp only [descP, mem_filter, mem_range]
        exact ⟨by omega, ⟨hn, hd⟩⟩
      have hne : w ⟨r, by omega⟩ ≠ w ⟨r + 1, hn⟩ := by
        intro heq
        have h := congrArg Fin.val (w.injective heq)
        simp at h
      have hlt : w ⟨r, by omega⟩ < w ⟨r + 1, hn⟩ :=
        lt_of_le_of_ne (le_of_not_gt hnd) hne
      simpa [f, show r < n by omega, hn] using hlt
    have h := hf ⟨i.is_lt, rfl⟩ ⟨j.is_lt, hb.symm⟩ hij
    simpa [f, i.is_lt, j.is_lt] using h
  · intro hw r hr
    simp only [descP, mem_filter, mem_range] at hr
    obtain ⟨hn, hlt⟩ := hr.2
    by_contra hnot
    have he := (block_succ_eq_iff A r).mpr hnot
    have h := hw ⟨r, by omega⟩ ⟨r + 1, hn⟩ he.symm (by simp)
    exact (lt_asymm h hlt)

/-- The Young subgroup permuting positions within each descent block. -/
def blockSubgroup (n : ℕ) (A : Finset ℕ) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {w | ∀ i, block A (w i) = block A i}
  one_mem' := by intro i; rfl
  mul_mem' := by
    intro w v hw hv i
    change block A (w (v i)) = block A i
    rw [hw, hv]
  inv_mem' := by
    intro w hw i
    have h := hw (w⁻¹ i)
    simpa using h.symm

/-- Flags with the cardinalities specified by the descent blocks. -/
abbrev BlockFlag (n : ℕ) (A : Finset ℕ) :=
  Equiv.Perm (Fin n) ⧸ blockSubgroup n A

/-- The number of block flags fixed by a permutation. -/
noncomputable def flagCharacter (n : ℕ) (A : Finset ℕ) (w : Equiv.Perm (Fin n)) : ℕ :=
  Nat.card (MulAction.fixedBy (BlockFlag n A) w)

/-- Orbits of pairs of flags under simultaneous relabeling. -/
noncomputable def flagOrbitCount (n : ℕ) (A B : Finset ℕ) : ℕ :=
  Nat.card (MulAction.orbitRel.Quotient (Equiv.Perm (Fin n))
    (BlockFlag n A × BlockFlag n B))

/-- The fixed flags of a product action form a product of the fixed flag sets. -/
def fixedByProdEquiv {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y] (w : G) :
    MulAction.fixedBy (X × Y) w ≃ MulAction.fixedBy X w × MulAction.fixedBy Y w where
  toFun p := (⟨p.1.1, congrArg Prod.fst p.2⟩, ⟨p.1.2, congrArg Prod.snd p.2⟩)
  invFun p := ⟨(p.1.1, p.2.1), Prod.ext p.1.2 p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Burnside's lemma gives the Gram matrix of the permutation characters. -/
theorem flagCharacter_inner (n : ℕ) (A B : Finset ℕ) :
    (∑ w : Equiv.Perm (Fin n), flagCharacter n A w * flagCharacter n B w) =
      flagOrbitCount n A B * n ! := by
  classical
  let : Fintype (BlockFlag n A) := Fintype.ofFinite _
  let : Fintype (BlockFlag n B) := Fintype.ofFinite _
  let : Fintype (MulAction.orbitRel.Quotient (Equiv.Perm (Fin n))
      (BlockFlag n A × BlockFlag n B)) := Fintype.ofFinite _
  have h := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Equiv.Perm (Fin n)) (BlockFlag n A × BlockFlag n B)
  have hp (w : Equiv.Perm (Fin n)) :
      Fintype.card (MulAction.fixedBy (BlockFlag n A × BlockFlag n B) w) =
        flagCharacter n A w * flagCharacter n B w := by
    rw [Fintype.card_congr (fixedByProdEquiv w), Fintype.card_prod]
    simp [flagCharacter, Nat.card_eq_fintype_card]
  simpa only [hp, flagOrbitCount, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin] using h

/-- Inclusion-exclusion of the permutation characters, for an exact descent set. -/
noncomputable def descentCharacter (n : ℕ) (A : Finset ℕ) (w : Equiv.Perm (Fin n)) : ℝ :=
  ∑ S ∈ A.powerset, (-1 : ℝ) ^ S.card * (flagCharacter n (A \ S) w : ℝ)

/-- Squared virtual characters are the corresponding signed orbit counts.
This is the finite group-action step of the ribbon-character argument. -/
theorem descentCharacter_inner (n : ℕ) (A B : Finset ℕ) :
    (∑ w : Equiv.Perm (Fin n), descentCharacter n A w * descentCharacter n B w) =
      (n ! : ℝ) * ∑ S ∈ A.powerset, ∑ T ∈ B.powerset,
        (-1 : ℝ) ^ (S.card + T.card) * (flagOrbitCount n (A \ S) (B \ T) : ℝ) := by
  unfold descentCharacter
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  simp_rw [sum_comm (s := univ) (t := B.powerset)]
  apply sum_congr rfl
  intro S _
  apply sum_congr rfl
  intro T _
  calc
    _ = (-1 : ℝ) ^ (S.card + T.card) *
        ∑ w : Equiv.Perm (Fin n),
          (flagCharacter n (A \ S) w : ℝ) * (flagCharacter n (B \ T) w : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro w _
      rw [pow_add]
      ring
    _ = (-1 : ℝ) ^ (S.card + T.card) *
        ((flagOrbitCount n (A \ S) (B \ T) : ℝ) * (n ! : ℝ)) := by
      congr 1
      exact_mod_cast flagCharacter_inner n (A \ S) (B \ T)
    _ = _ := by ring

/-- Once the descent-to-orbit correspondence is supplied, inclusion-exclusion
and Burnside give the squared character formula for the actual count g. -/
theorem g_character_norm_of_orbit_counts (n : ℕ)
    (h : ∀ S ∈ (altS n).powerset, ∀ T ∈ (altS n).powerset,
      jointSubsetCount n (altS n \ S) (altS n \ T) =
        flagOrbitCount n (altS n \ S) (altS n \ T)) :
    (g n : ℝ) * (n ! : ℝ) =
      ∑ w : Equiv.Perm (Fin n), descentCharacter n (altS n) w ^ 2 := by
  simp_rw [pow_two]
  rw [descentCharacter_inner, g_inclusion_exclusion, mul_comm]
  congr 1
  apply sum_congr rfl
  intro S hS
  apply sum_congr rfl
  intro T hT
  rw [h S hS T hT]

end Stanley.Alt
