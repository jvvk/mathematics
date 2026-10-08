/-
  Stanley, MathOverflow 486548. Part K. Descent pairs and orbits of flag pairs.

  A flag of type `A` is a labelling `f : Fin n → Fin (n+1)` with the fibre sizes of the block
  labelling `blk n A` (positions `p` and `p + 1` share a block iff `p ∉ A`). `Perm (Fin n)` acts by
  `σ • f = f ∘ σ⁻¹`. The main result `card_joint_eq_orbits`:

    #{w : D(w) ⊆ A, D(w⁻¹) ⊆ B} = #orbits of `Perm (Fin n)` on (flags of type A) × (flags of type B),

  via `w ↦ orbit of (blk A, blk B ∘ w)`. Surjectivity: in an orbit, a permutation with fewest
  inversions has `D(w) ⊆ A` and `D(w⁻¹) ⊆ B` (an adjacent swap inside a block stays in the orbit and
  removes an inversion). Injectivity: two such permutations in one orbit have the same value-block
  labelling, since monotone labellings of a set with equal fibre counts agree, and then agree
  because increasing maps onto a common image agree.
-/
import LeanProofs.Stanley.FlagCount

namespace Stanley.Alt

open Finset Equiv

/-! ### Fibres and flags -/

/-- Fibre size. -/
def fib {α β : Type*} [Fintype α] [DecidableEq β] (f : α → β) (j : β) : ℕ :=
  (univ.filter (fun p => f p = j)).card

theorem fib_comp {n : ℕ} {β : Type*} [DecidableEq β] (f : Fin n → β) (σ : Perm (Fin n)) (j : β) :
    fib (f ∘ σ) j = fib f j := by
  unfold fib
  rw [← Finset.card_map σ.toEmbedding]
  congr 1
  ext p
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
    Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact hq
  · intro hp; exact ⟨σ.symm p, by simpa using hp, by simp⟩

theorem block_le (A : Finset ℕ) (i : ℕ) : block A i ≤ i := by
  unfold block
  calc (A.filter (· < i)).card ≤ (range i).card :=
        Finset.card_le_card fun r hr => by simp only [mem_filter] at hr; simp [hr.2]
    _ = i := card_range i

/-- The block labelling of positions. -/
def blk (n : ℕ) (A : Finset ℕ) (p : Fin n) : Fin (n + 1) :=
  ⟨block A p, by have := block_le A p; omega⟩

theorem blk_val {n : ℕ} (A : Finset ℕ) (p : Fin n) : (blk n A p : ℕ) = block A p := rfl

theorem blk_mono {n : ℕ} (A : Finset ℕ) {p q : Fin n} (h : p ≤ q) : blk n A p ≤ blk n A q := by
  rw [Fin.le_iff_val_le_val, blk_val, blk_val]; exact block_monotone A h

/-- Flags of type `A`. -/
def Flag (n : ℕ) (A : Finset ℕ) : Type :=
  {f : Fin n → Fin (n + 1) // ∀ j, fib f j = fib (blk n A) j}

instance (n : ℕ) (A : Finset ℕ) : Fintype (Flag n A) := by unfold Flag; infer_instance

instance (n : ℕ) (A : Finset ℕ) : DecidableEq (Flag n A) := by unfold Flag; infer_instance

instance (n : ℕ) (A : Finset ℕ) : MulAction (Perm (Fin n)) (Flag n A) where
  smul σ f := ⟨f.1 ∘ ⇑σ⁻¹, fun j => by rw [fib_comp]; exact f.2 j⟩
  one_smul f := Subtype.ext (by funext p; rfl)
  mul_smul σ τ f := Subtype.ext (by funext p; rfl)

theorem smul_val {n : ℕ} {A : Finset ℕ} (σ : Perm (Fin n)) (f : Flag n A) :
    (σ • f).1 = f.1 ∘ ⇑σ⁻¹ := rfl

/-- The block labelling as a flag. -/
def canon (n : ℕ) (A : Finset ℕ) : Flag n A := ⟨blk n A, fun _ => rfl⟩

/-- The value-block labelling of positions pulled back by `w`. -/
def gflag (n : ℕ) (B : Finset ℕ) (w : Perm (Fin n)) : Flag n B :=
  ⟨blk n B ∘ w, fun j => fib_comp _ _ _⟩

/-- Every flag is a block labelling composed with a permutation. -/
theorem exists_perm_of_flag {n : ℕ} {A : Finset ℕ} (f : Flag n A) :
    ∃ σ : Perm (Fin n), f.1 = blk n A ∘ σ := by
  classical
  have hcard : ∀ j, Fintype.card {p // f.1 p = j} = Fintype.card {p // blk n A p = j} := by
    intro j
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact f.2 j
  let e : ∀ j, {p // f.1 p = j} ≃ {p // blk n A p = j} := fun j =>
    Fintype.equivOfCardEq (hcard j)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext p
  exact (Equiv.ofFiberEquiv_map e p).symm

/-! ### Inversions -/

/-- Inversion pairs. -/
def invs {n : ℕ} (w : Perm (Fin n)) : Finset (Fin n × Fin n) :=
  univ.filter (fun pq => pq.1 < pq.2 ∧ w pq.2 < w pq.1)

theorem mem_invs {n : ℕ} {w : Perm (Fin n)} {pq : Fin n × Fin n} :
    pq ∈ invs w ↔ pq.1 < pq.2 ∧ w pq.2 < w pq.1 := by simp [invs]

theorem card_invs_inv {n : ℕ} (w : Perm (Fin n)) : (invs w⁻¹).card = (invs w).card := by
  apply Finset.card_bij (fun pq _ => (w⁻¹ pq.2, w⁻¹ pq.1))
  · intro pq h
    rw [mem_invs] at h ⊢
    simp only [inv_inv]
    have e1 : w (w⁻¹ pq.1) = pq.1 := by simp
    have e2 : w (w⁻¹ pq.2) = pq.2 := by simp
    rw [e1, e2]; exact ⟨h.2, h.1⟩
  · intro a ha b hb h
    simp only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
    exact Prod.ext h.2 h.1
  · intro pq h
    rw [mem_invs] at h
    refine ⟨(w pq.2, w pq.1), ?_, by simp⟩
    rw [mem_invs]
    have e1 : w⁻¹ (w pq.1) = pq.1 := by simp
    have e2 : w⁻¹ (w pq.2) = pq.2 := by simp
    simp only [e1, e2]; exact ⟨h.2, h.1⟩

/-- An adjacent swap reverses the order of no pair except itself. -/
theorem swap_adj_lt {n : ℕ} {v v' x y : Fin n} (hv : (v' : ℕ) = v + 1)
    (h : swap v v' y < swap v v' x) : y < x ∨ (x = v ∧ y = v') := by
  rw [swap_apply_def, swap_apply_def] at h
  rw [Fin.lt_def] at h ⊢
  rw [Fin.ext_iff, Fin.ext_iff]
  split_ifs at h with h1 h2 h3 h4 h5 h6 <;> simp only [Fin.ext_iff] at * <;> omega

/-- Swapping two adjacent values that appear in the wrong order removes an inversion. -/
theorem card_invs_swap_left {n : ℕ} (w : Perm (Fin n)) {v v' : Fin n} (hv : (v' : ℕ) = v + 1)
    (hd : w⁻¹ v' < w⁻¹ v) : (invs (swap v v' * w)).card < (invs w).card := by
  have hsub : invs (swap v v' * w) ⊆ (invs w).erase (w⁻¹ v', w⁻¹ v) := by
    intro pq h
    rw [mem_invs] at h
    simp only [Perm.mul_apply] at h
    rcases swap_adj_lt hv h.2 with h2 | ⟨hx, hy⟩
    · rw [Finset.mem_erase]
      refine ⟨fun he => ?_, ?_⟩
      · rw [Prod.ext_iff] at he
        have e1 : w pq.1 = v' := by rw [he.1]; simp
        have e2 : w pq.2 = v := by rw [he.2]; simp
        have h3 := h.2
        rw [e1, e2, swap_apply_left, swap_apply_right, Fin.lt_def] at h3; omega
      · rw [mem_invs]; exact ⟨h.1, h2⟩
    · exfalso
      have e1 : pq.1 = w⁻¹ v := by rw [← hx]; simp
      have e2 : pq.2 = w⁻¹ v' := by rw [← hy]; simp
      have := h.1; rw [e1, e2] at this
      exact absurd hd (not_lt.mpr this.le)
  refine lt_of_le_of_lt (Finset.card_le_card hsub) ?_
  apply Finset.card_erase_lt_of_mem
  rw [mem_invs]
  have e1 : w (w⁻¹ v) = v := by simp
  have e2 : w (w⁻¹ v') = v' := by simp
  refine ⟨hd, ?_⟩
  simp only [e1, e2]; rw [Fin.lt_def]; omega

/-- Swapping two adjacent positions holding a descent removes an inversion. -/
theorem card_invs_swap_right {n : ℕ} (w : Perm (Fin n)) {i i' : Fin n} (hi : (i' : ℕ) = i + 1)
    (hd : w i' < w i) : (invs (w * swap i i')).card < (invs w).card := by
  have h1 : (w * swap i i')⁻¹ = swap i i' * w⁻¹ := by rw [mul_inv_rev, swap_inv]
  rw [← card_invs_inv (w * swap i i'), h1, ← card_invs_inv w]
  exact card_invs_swap_left w⁻¹ hi (by simpa using hd)

/-! ### Two uniqueness lemmas -/

theorem card_filter_le_eq {n : ℕ} (I : Finset (Fin n)) (g g' : Fin n → Fin (n + 1))
    (hfib : ∀ j, (I.filter (fun q => g q = j)).card = (I.filter (fun q => g' q = j)).card)
    (j : Fin (n + 1)) :
    (I.filter (fun q => g q ≤ j)).card = (I.filter (fun q => g' q ≤ j)).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := univ.filter (· ≤ j)),
    Finset.card_eq_sum_card_fiberwise (f := g') (t := univ.filter (· ≤ j))]
  · refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.filter_filter, Finset.filter_filter]
    have hv' : v ≤ j := by simpa using hv
    have e1 : I.filter (fun q => g q ≤ j ∧ g q = v) = I.filter (fun q => g q = v) :=
      Finset.filter_congr fun q _ => ⟨fun h => h.2, fun h => ⟨h ▸ hv', h⟩⟩
    have e2 : I.filter (fun q => g' q ≤ j ∧ g' q = v) = I.filter (fun q => g' q = v) :=
      Finset.filter_congr fun q _ => ⟨fun h => h.2, fun h => ⟨h ▸ hv', h⟩⟩
    rw [e1, e2]; exact hfib v
  · intro q hq; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩
  · intro q hq; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hq).2⟩

theorem not_lt_of_monotone_fib {n : ℕ} (I : Finset (Fin n)) (g g' : Fin n → Fin (n + 1))
    (hg : ∀ p ∈ I, ∀ q ∈ I, p ≤ q → g p ≤ g q) (hg' : ∀ p ∈ I, ∀ q ∈ I, p ≤ q → g' p ≤ g' q)
    (hfib : ∀ j, (I.filter (fun q => g q = j)).card = (I.filter (fun q => g' q = j)).card)
    {p : Fin n} (hp : p ∈ I) : ¬ g p < g' p := by
  intro hlt
  have hC := card_filter_le_eq I g g' hfib (g p)
  have h1 : I.filter (fun q => q ≤ p) ⊆ I.filter (fun q => g q ≤ g p) := fun q hq => by
    simp only [Finset.mem_filter] at hq ⊢; exact ⟨hq.1, hg q hq.1 p hp hq.2⟩
  have h2 : I.filter (fun q => g' q ≤ g p) ⊆ I.filter (fun q => q < p) := fun q hq => by
    simp only [Finset.mem_filter] at hq ⊢
    refine ⟨hq.1, lt_of_not_ge fun hpq => ?_⟩
    exact absurd (lt_of_lt_of_le hlt (hg' p hp q hq.1 hpq)) (not_lt.mpr hq.2)
  have h3 : (I.filter (fun q => q < p)).card < (I.filter (fun q => q ≤ p)).card := by
    apply Finset.card_lt_card
    refine ⟨fun q hq => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter] at hq ⊢; exact ⟨hq.1, hq.2.le⟩
    · have := hsub (Finset.mem_filter.mpr ⟨hp, le_rfl⟩)
      simp at this
  have := Finset.card_le_card h1
  have := Finset.card_le_card h2
  omega

/-- Monotone labellings of a set with equal fibre counts agree. -/
theorem eq_of_monotone_fib {n : ℕ} (I : Finset (Fin n)) (g g' : Fin n → Fin (n + 1))
    (hg : ∀ p ∈ I, ∀ q ∈ I, p ≤ q → g p ≤ g q) (hg' : ∀ p ∈ I, ∀ q ∈ I, p ≤ q → g' p ≤ g' q)
    (hfib : ∀ j, (I.filter (fun q => g q = j)).card = (I.filter (fun q => g' q = j)).card)
    {p : Fin n} (hp : p ∈ I) : g p = g' p :=
  le_antisymm (not_lt.mp (not_lt_of_monotone_fib I g' g hg' hg (fun j => (hfib j).symm) hp))
    (not_lt.mp (not_lt_of_monotone_fib I g g' hg hg' hfib hp))

theorem not_lt_of_strictMono_image {n : ℕ} (J : Finset (Fin n)) (h h' : Fin n → Fin n)
    (hm : ∀ x ∈ J, ∀ y ∈ J, x < y → h x < h y) (hm' : ∀ x ∈ J, ∀ y ∈ J, x < y → h' x < h' y)
    (himg : J.image h = J.image h') {x : Fin n} (hx : x ∈ J) : ¬ h x < h' x := by
  intro hlt
  have hinj : Set.InjOn h J := fun a ha b hb hab => by
    rcases lt_trichotomy a b with c | c | c
    · exact absurd hab (hm a ha b hb c).ne
    · exact c
    · exact absurd hab (hm b hb a ha c).ne'
  have hinj' : Set.InjOn h' J := fun a ha b hb hab => by
    rcases lt_trichotomy a b with c | c | c
    · exact absurd hab (hm' a ha b hb c).ne
    · exact c
    · exact absurd hab (hm' b hb a ha c).ne'
  have hc : ∀ (k : Fin n → Fin n), Set.InjOn k J →
      (J.filter (fun y => k y ≤ h x)).card = ((J.image k).filter (· ≤ h x)).card := by
    intro k hk
    rw [Finset.filter_image, Finset.card_image_of_injOn (hk.mono (fun y hy => (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).1))]
  have heq : (J.filter (fun y => h y ≤ h x)).card = (J.filter (fun y => h' y ≤ h x)).card := by
    rw [hc h hinj, hc h' hinj', himg]
  have h1 : J.filter (fun y => y ≤ x) ⊆ J.filter (fun y => h y ≤ h x) := fun y hy => by
    simp only [Finset.mem_filter] at hy ⊢
    refine ⟨hy.1, ?_⟩
    rcases eq_or_lt_of_le hy.2 with e | e
    · rw [e]
    · exact (hm y hy.1 x hx e).le
  have h2 : J.filter (fun y => h' y ≤ h x) ⊆ J.filter (fun y => y < x) := fun y hy => by
    simp only [Finset.mem_filter] at hy ⊢
    refine ⟨hy.1, lt_of_not_ge fun hxy => ?_⟩
    rcases eq_or_lt_of_le hxy with e | e
    · rw [← e] at hy; exact absurd hlt (not_lt.mpr hy.2)
    · exact absurd (lt_trans hlt (hm' x hx y hy.1 e)) (not_lt.mpr hy.2)
  have h3 : (J.filter (fun y => y < x)).card < (J.filter (fun y => y ≤ x)).card := by
    apply Finset.card_lt_card
    refine ⟨fun y hy => ?_, fun hsub => ?_⟩
    · simp only [Finset.mem_filter] at hy ⊢; exact ⟨hy.1, hy.2.le⟩
    · have := hsub (Finset.mem_filter.mpr ⟨hx, le_rfl⟩)
      simp at this
  have := Finset.card_le_card h1
  have := Finset.card_le_card h2
  omega

/-- Strictly increasing maps of a set with a common image agree. -/
theorem eq_of_strictMono_image {n : ℕ} (J : Finset (Fin n)) (h h' : Fin n → Fin n)
    (hm : ∀ x ∈ J, ∀ y ∈ J, x < y → h x < h y) (hm' : ∀ x ∈ J, ∀ y ∈ J, x < y → h' x < h' y)
    (himg : J.image h = J.image h') {x : Fin n} (hx : x ∈ J) : h x = h' x :=
  le_antisymm (not_lt.mp (not_lt_of_strictMono_image J h' h hm' hm himg.symm hx))
    (not_lt.mp (not_lt_of_strictMono_image J h h' hm hm' himg hx))

/-! ### Descent pairs and orbits -/

/-- Orbits of pairs of flags. -/
abbrev FQ (n : ℕ) (A B : Finset ℕ) :=
  MulAction.orbitRel.Quotient (Perm (Fin n)) (Flag n A × Flag n B)

/-- The orbit attached to a permutation. -/
def orbOf {n : ℕ} (A B : Finset ℕ) (w : Perm (Fin n)) : FQ n A B :=
  Quotient.mk (MulAction.orbitRel _ _) (canon n A, gflag n B w)

theorem mk_smul {n : ℕ} {A B : Finset ℕ} (σ : Perm (Fin n)) (x : Flag n A × Flag n B) :
    Quotient.mk (MulAction.orbitRel (Perm (Fin n)) (Flag n A × Flag n B)) (σ • x) =
      Quotient.mk (MulAction.orbitRel _ _) x :=
  Quotient.sound (MulAction.mem_orbit x σ)

/-- Swapping two positions of one block preserves the block labelling. -/
theorem blk_swap {n : ℕ} (A : Finset ℕ) {a a' : Fin n} (ha : (a' : ℕ) = a + 1)
    (hA : (a : ℕ) ∉ A) (p : Fin n) : blk n A (swap a a' p) = blk n A p := by
  have hb : block A a' = block A a := by rw [ha]; exact (block_succ_eq_iff A a).mpr hA
  rw [swap_apply_def]
  split_ifs with h1 h2
  · subst h1; exact Fin.ext (by rw [blk_val, blk_val, hb])
  · subst h2; exact Fin.ext (by rw [blk_val, blk_val, hb])
  · rfl

theorem mem_descP {n : ℕ} {w : Perm (Fin n)} {i : ℕ} :
    i ∈ descP w ↔ ∃ h : i + 1 < n, w ⟨i + 1, h⟩ < w ⟨i, by omega⟩ := by
  simp only [descP, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨h, hlt⟩; exact ⟨by omega, h, hlt⟩

/-- **Descent pairs and orbits.** `#{w : D(w) ⊆ A, D(w⁻¹) ⊆ B}` equals the number of orbits of
`Perm (Fin n)` on pairs of flags of types `A` and `B`. -/
theorem card_joint_eq_orbits (n : ℕ) (A B : Finset ℕ) :
    jointSubsetCount n A B = Nat.card (FQ n A B) := by
  classical
  have hW : jointSubsetCount n A B =
      Nat.card {w : Perm (Fin n) // descP w ⊆ A ∧ descP w⁻¹ ⊆ B} := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; rfl
  rw [hW]
  apply Nat.card_eq_of_bijective (fun w => orbOf A B w.1)
  constructor
  · -- injectivity
    rintro ⟨w, hwA, hwB⟩ ⟨w', hw'A, hw'B⟩ heq
    simp only [orbOf] at heq
    rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at heq
    obtain ⟨σ, hσ⟩ := heq
    have h1 : ∀ p, blk n A (σ⁻¹ p) = blk n A p := fun p =>
      congrFun (congrArg (fun x : Flag n A × Flag n B => x.1.1) hσ) p
    have h2 : ∀ p, blk n B (w' (σ⁻¹ p)) = blk n B (w p) := fun p =>
      congrFun (congrArg (fun x : Flag n A × Flag n B => x.2.1) hσ) p
    -- the value-block labellings agree
    have hg : ∀ p, blk n B (w p) = blk n B (w' p) := by
      intro p
      set I := univ.filter (fun q => blk n A q = blk n A p)
      have hmono : ∀ (v : Perm (Fin n)), descP v ⊆ A →
          ∀ a ∈ I, ∀ b ∈ I, a ≤ b → (blk n B ∘ v) a ≤ (blk n B ∘ v) b := by
        intro v hv a ha b hb hab
        simp only [I, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        rcases eq_or_lt_of_le hab with e | e
        · rw [e]
        · have hbl : block A a = block A b := by
            rw [← blk_val, ← blk_val, ha, hb]
          exact blk_mono B ((descP_subset_iff_blocks v A).mp hv a b hbl e).le
      have hfib : ∀ j, (I.filter (fun q => (blk n B ∘ w) q = j)).card =
          (I.filter (fun q => (blk n B ∘ w') q = j)).card := by
        intro j
        apply Finset.card_bij (fun q _ => σ⁻¹ q)
        · intro q hq
          simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hq ⊢
          exact ⟨by rw [h1, hq.1], by rw [h2, hq.2]⟩
        · intro a _ b _ hab; exact σ⁻¹.injective hab
        · intro q hq
          simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply] at hq
          refine ⟨σ q, ?_, by simp⟩
          have e1 : σ⁻¹ (σ q) = q := by simp
          simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
          refine ⟨?_, ?_⟩
          · rw [← h1 (σ q), e1, hq.1]
          · rw [← h2 (σ q), e1, hq.2]
      exact eq_of_monotone_fib I (blk n B ∘ w) (blk n B ∘ w') (hmono w hwA) (hmono w' hw'A) hfib
        (by simp [I])
    -- hence the permutations agree
    have hinv : w⁻¹ = w'⁻¹ := by
      ext v
      congr 1
      set J := univ.filter (fun x => blk n B x = blk n B v)
      have hsm : ∀ (u : Perm (Fin n)), descP u⁻¹ ⊆ B →
          ∀ a ∈ J, ∀ b ∈ J, a < b → u⁻¹ a < u⁻¹ b := by
        intro u hu a ha b hb hab
        simp only [J, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        have hbl : block B a = block B b := by rw [← blk_val, ← blk_val, ha, hb]
        exact (descP_subset_iff_blocks u⁻¹ B).mp hu a b hbl hab
      have himg : ∀ (u : Perm (Fin n)),
          J.image ⇑u⁻¹ = univ.filter (fun p => blk n B (u p) = blk n B v) := by
        intro u
        ext p
        simp only [J, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨x, hx, rfl⟩; simpa using hx
        · intro hp; exact ⟨u p, hp, by simp⟩
      have hsame : J.image ⇑w⁻¹ = J.image ⇑w'⁻¹ := by
        rw [himg, himg]
        exact Finset.filter_congr fun p _ => by rw [hg p]
      exact eq_of_strictMono_image J ⇑w⁻¹ ⇑w'⁻¹ (hsm w hwB) (hsm w' hw'B) hsame (by simp [J])
    exact Subtype.ext (inv_inj.mp hinv)
  · -- surjectivity: a permutation with fewest inversions in the orbit
    intro q
    induction q using Quotient.inductionOn with
    | h x =>
    obtain ⟨f1, f2⟩ := x
    obtain ⟨σ1, hσ1⟩ := exists_perm_of_flag f1
    have hx1 : σ1 • f1 = canon n A := Subtype.ext (by
      funext p; rw [smul_val]; simp [hσ1, canon])
    obtain ⟨π, hπ⟩ := exists_perm_of_flag (σ1 • f2)
    have hgπ : σ1 • f2 = gflag n B π := Subtype.ext hπ
    have hq : orbOf A B π = Quotient.mk (MulAction.orbitRel _ _) (f1, f2) := by
      unfold orbOf; rw [← hx1, ← hgπ, ← Prod.smul_mk, mk_smul]
    set D := univ.filter (fun w : Perm (Fin n) => orbOf A B w = orbOf A B π)
    obtain ⟨w, hwD, hmin⟩ := D.exists_min_image (fun w => (invs w).card)
      ⟨π, by simp [D]⟩
    have hw : orbOf A B w = orbOf A B π := (Finset.mem_filter.mp hwD).2
    refine ⟨⟨w, ?_, ?_⟩, by simp only; rw [hw, hq]⟩
    · intro i hi
      by_contra hA
      obtain ⟨hi1, hd⟩ := mem_descP.mp hi
      set a : Fin n := ⟨i, by omega⟩
      set a' : Fin n := ⟨i + 1, hi1⟩
      have haa : (a' : ℕ) = a + 1 := rfl
      have hstay : orbOf A B (w * swap a a') = orbOf A B w := by
        have e : swap a a' • (canon n A, gflag n B w) = (canon n A, gflag n B (w * swap a a')) := by
          rw [Prod.smul_mk]
          congr 1
          exact Subtype.ext (by funext p; rw [smul_val, swap_inv]; exact blk_swap A haa hA p)
        unfold orbOf; rw [← e, mk_smul]
      have hmem : w * swap a a' ∈ D := by simp [D, hstay, hw]
      have := hmin _ hmem
      exact absurd this (not_le.mpr (card_invs_swap_right w haa hd))
    · intro i hi
      by_contra hB
      obtain ⟨hi1, hd⟩ := mem_descP.mp hi
      set b : Fin n := ⟨i, by omega⟩
      set b' : Fin n := ⟨i + 1, hi1⟩
      have hbb : (b' : ℕ) = b + 1 := rfl
      have hstay : orbOf A B (swap b b' * w) = orbOf A B w := by
        have e : gflag n B (swap b b' * w) = gflag n B w :=
          Subtype.ext (by funext p; exact blk_swap B hbb hB (w p))
        unfold orbOf; rw [e]
      have hmem : swap b b' * w ∈ D := by simp [D, hstay, hw]
      have := hmin _ hmem
      exact absurd this (not_le.mpr (card_invs_swap_left w hbb hd))

end Stanley.Alt
