import LeanProofs.Orbits516140.Basic

/-!
# A certified counter for linear extensions

`cnt D k S` removes a minimal element of `S` in every possible way, `k` times. Given a table
`D m` of the elements strictly below `m`, `cnt D (card α) univ` equals `e(α) = #LinExt α`.
The proof goes through words: a linear extension is the same as a listing of the elements,
each once, with no element listed after one strictly below it.
-/

namespace Orbits516140

variable {α : Type*} [Fintype α] [PartialOrder α] [DecidableEq α]

/-- Listings of the finset `S`, each element once, never an element after one below it. -/
def ListExt (S : Finset α) : Type _ :=
  {l : List α // l.Nodup ∧ l.toFinset = S ∧ l.Pairwise (fun a b => ¬ b < a)}

/-- Count by removal of a minimal element, `k` times. `D m` lists the elements below `m`. -/
def cnt (D : α → List α) : ℕ → Finset α → ℕ
  | 0, _ => 1
  | k + 1, S => ∑ m ∈ S.filter (fun m => ∀ x ∈ D m, x ∉ S), cnt D k (S.erase m)

set_option linter.unusedFintypeInType false in
instance (S : Finset α) : Finite (ListExt S) := by
  have : Finite {l : List α | l.length ≤ Fintype.card α} :=
    (List.finite_length_le (α := α) (n := Fintype.card α)).to_subtype
  exact Finite.of_injective
    (fun l : ListExt S => (⟨l.1, l.2.1.length_le_card⟩ :
      {l : List α | l.length ≤ Fintype.card α}))
    fun a b h => Subtype.ext (by have := congrArg Subtype.val h; exact this)

theorem cons_ok {D : α → List α} (hD : ∀ x m, x < m ↔ x ∈ D m) {S : Finset α} {m : α}
    (hm : m ∈ S.filter (fun m => ∀ x ∈ D m, x ∉ S)) {t : List α}
    (ht : t.Nodup ∧ t.toFinset = S.erase m ∧ t.Pairwise (fun a b => ¬ b < a)) :
    (m :: t).Nodup ∧ (m :: t).toFinset = S ∧ (m :: t).Pairwise (fun a b => ¬ b < a) := by
  obtain ⟨hnd, hS, hp⟩ := ht
  have hmS := (Finset.mem_filter.1 hm).1
  have hmin := (Finset.mem_filter.1 hm).2
  refine ⟨List.nodup_cons.2 ⟨fun h => ?_, hnd⟩, ?_, List.pairwise_cons.2 ⟨fun b hb hbm => ?_, hp⟩⟩
  · have : m ∈ t.toFinset := List.mem_toFinset.2 h
    rw [hS] at this; simp at this
  · rw [List.toFinset_cons, hS, Finset.insert_erase hmS]
  · have hb' : b ∈ S := by
      have : b ∈ t.toFinset := List.mem_toFinset.2 hb
      rw [hS] at this; exact Finset.mem_of_mem_erase this
    exact hmin b ((hD b m).1 hbm) hb'

/-- Prepend a minimal element of `S` to a listing of `S \ {m}`. -/
def consExt (D : α → List α) (hD : ∀ x m, x < m ↔ x ∈ D m) (S : Finset α)
    (p : Σ m : S.filter (fun m => ∀ x ∈ D m, x ∉ S), ListExt (S.erase m)) : ListExt S :=
  ⟨p.1.1 :: p.2.1, cons_ok hD p.1.2 p.2.2⟩

theorem consExt_bijective (D : α → List α) (hD : ∀ x m, x < m ↔ x ∈ D m) {S : Finset α}
    (hS0 : S.Nonempty) :
    Function.Bijective (consExt D hD S) := by
  constructor
  · rintro ⟨⟨m, hm⟩, ⟨t, ht⟩⟩ ⟨⟨m', hm'⟩, ⟨t', ht'⟩⟩ h
    have h' : m :: t = m' :: t' := congrArg Subtype.val h
    obtain ⟨rfl, rfl⟩ := List.cons.inj h'
    rfl
  · rintro ⟨l, hnd, hS, hp⟩
    cases l with
    | nil =>
      simp only [List.toFinset_nil] at hS
      exact absurd hS.symm hS0.ne_empty
    | cons m t =>
      have hmS : m ∈ S := by rw [← hS]; simp
      have hmin : ∀ x ∈ D m, x ∉ S := by
        intro x hx hxS
        have hxm : x < m := (hD x m).2 hx
        rw [← hS, List.mem_toFinset, List.mem_cons] at hxS
        rcases hxS with rfl | hxt
        · exact lt_irrefl _ hxm
        · exact (List.pairwise_cons.1 hp).1 x hxt hxm
      have hmt : m ∉ t := (List.nodup_cons.1 hnd).1
      refine ⟨⟨⟨m, Finset.mem_filter.2 ⟨hmS, hmin⟩⟩, ⟨t, (List.nodup_cons.1 hnd).2, ?_,
        (List.pairwise_cons.1 hp).2⟩⟩, rfl⟩
      change t.toFinset = S.erase m
      rw [← hS, List.toFinset_cons, Finset.erase_insert (by simpa using hmt)]

/-- `#ListExt S = cnt D (#S) S`. -/
theorem card_listExt (D : α → List α) (hD : ∀ x m, x < m ↔ x ∈ D m) :
    ∀ (k : ℕ) (S : Finset α), S.card = k → Nat.card (ListExt S) = cnt D k S
  | 0, S, h => by
    rw [Finset.card_eq_zero] at h
    subst h
    have : Unique (ListExt (∅ : Finset α)) :=
      { default := ⟨[], by simp⟩
        uniq := fun ⟨l, _, hS, _⟩ => Subtype.ext (by simpa using hS) }
    simp [cnt]
  | k + 1, S, h => by
    have hS0 : S.Nonempty := Finset.card_pos.1 (by omega)
    rw [← Nat.card_congr (Equiv.ofBijective _ (consExt_bijective D hD hS0)), Nat.card_sigma, cnt,
      ← Finset.sum_coe_sort (S.filter _) (fun m => cnt D k (S.erase m))]
    refine Fintype.sum_congr _ _ fun m => card_listExt D hD k _ ?_
    rw [Finset.card_erase_of_mem (Finset.mem_filter.1 m.2).1, h, Nat.add_sub_cancel]

/-- Linear extensions as listings: `σ ↦ [σ⁻¹ 0, σ⁻¹ 1, …]`. -/
def toList (σ : LinExt α) : ListExt (Finset.univ : Finset α) :=
  ⟨List.ofFn σ.1.symm, by
    refine ⟨List.nodup_ofFn.2 σ.1.symm.injective, ?_, List.pairwise_ofFn.2 fun i j hij h => ?_⟩
    · ext a; simp only [List.mem_toFinset, List.mem_ofFn, Finset.mem_univ, iff_true]
      exact ⟨σ.1 a, by simp⟩
    · have := σ.2 h
      simp only [Equiv.apply_symm_apply] at this
      exact lt_asymm hij this⟩

theorem toList_bijective : Function.Bijective (toList (α := α)) := by
  constructor
  · intro σ τ h
    have h' : List.ofFn σ.1.symm = List.ofFn τ.1.symm := congrArg Subtype.val h
    have := List.ofFn_injective h'
    exact Subtype.ext (Equiv.symm_bijective.injective (Equiv.coe_fn_injective this))
  · rintro ⟨l, hnd, hS, hp⟩
    have hmem : ∀ x, x ∈ l := fun x => by
      rw [← List.mem_toFinset, hS]; exact Finset.mem_univ x
    have hlen : l.length = Fintype.card α := by
      rw [← List.toFinset_card_of_nodup hnd, hS, Finset.card_univ]
    let e := hnd.getEquivOfForallMemList l hmem
    let σ : α ≃ Fin (Fintype.card α) := e.symm.trans (finCongr hlen)
    have hσ : ∀ i, σ.symm i = l.get (Fin.cast hlen.symm i) := fun i => rfl
    have hmono : StrictMono σ := by
      intro a b hab
      have ha : l.get (e.symm a) = a := e.apply_symm_apply a
      have hb : l.get (e.symm b) = b := e.apply_symm_apply b
      change Fin.cast hlen (e.symm a) < Fin.cast hlen (e.symm b)
      rw [Fin.lt_def, Fin.val_cast, Fin.val_cast]
      rcases lt_trichotomy (e.symm a).val (e.symm b).val with h | h | h
      · exact h
      · exact absurd (e.symm.injective (Fin.ext h)) hab.ne
      · have := List.pairwise_iff_get.1 hp (e.symm b) (e.symm a) h
        rw [ha, hb] at this
        exact absurd hab this
    refine ⟨⟨σ, hmono⟩, Subtype.ext ?_⟩
    change List.ofFn σ.symm = l
    apply List.ext_get (by simp [hlen])
    intro n h1 h2
    simp [hσ]

/-- `e(α) = cnt D (#α) univ` for any table `D` of strict down-sets. -/
theorem card_linExt_eq_cnt (D : α → List α) (hD : ∀ x m, x < m ↔ x ∈ D m) :
    Nat.card (LinExt α) = cnt D (Fintype.card α) Finset.univ := by
  rw [Nat.card_congr (Equiv.ofBijective _ toList_bijective)]
  exact card_listExt D hD _ _ Finset.card_univ

end Orbits516140
