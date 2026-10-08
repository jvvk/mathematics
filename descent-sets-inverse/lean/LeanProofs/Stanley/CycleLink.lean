/-
  Stanley, MathOverflow 486548. Part N. From flags of type `A ⊆ alt` to surjective labellings with
  odd partial sums.

  For weighted atoms (`c a ≥ 1`, total `n`), a labelling `h : κ → Fin (n+1)` whose weighted fibre
  sizes are those of the block labelling of `A ⊆ altS n` is the same thing as a surjective labelling
  onto `{0, …, |A|}` with odd partial weights below the top label; `A` is recovered as the set of
  partial weights minus one. Hence (`signed_fits_eq`)

    Σ_{A ⊆ alt} (-1)^|alt \ A| #{h fitting A} = (-1)^|alt| Φ c.
-/
import LeanProofs.Stanley.Atoms
import LeanProofs.Stanley.Fill

namespace Stanley.Alt

open Finset

/-! ### Cumulative counts of the block labelling -/

theorem block_eq_rk (A : Finset ℕ) (i : ℕ) : block A i = Fill.rk A i := rfl

/-- Positions in blocks `≤ rk A a` are exactly the positions `≤ a`. -/
theorem card_block_le_rk {n : ℕ} {A : Finset ℕ} (hA : A ⊆ range (n - 1)) {a : ℕ} (ha : a ∈ A) :
    (univ.filter (fun p : Fin n => block A p ≤ Fill.rk A a)).card = a + 1 := by
  have han : a < n := by have := Finset.mem_range.mp (hA ha); omega
  rw [← Finset.card_map Fin.valEmbedding, ← Finset.card_range (a + 1)]
  congr 1
  ext i
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨p, hp, rfl⟩
    by_contra hlt
    have : Fill.rk A a < Fill.rk A p := Fill.rk_lt_rk ha (by omega)
    rw [block_eq_rk] at hp; omega
  · intro hi
    refine ⟨⟨i, by omega⟩, ?_, rfl⟩
    rw [block_eq_rk]; exact Fill.rk_mono A (by simp only; omega)

/-- Above the last block every position is counted. -/
theorem card_block_le_top {n : ℕ} (A : Finset ℕ) {j : ℕ} (hj : A.card ≤ j) :
    (univ.filter (fun p : Fin n => block A p ≤ j)).card = n := by
  have : univ.filter (fun p : Fin n => block A p ≤ j) = univ :=
    Finset.filter_true_of_mem (fun p _ => (Finset.card_le_card (Finset.filter_subset _ _)).trans hj)
  rw [this, Finset.card_univ, Fintype.card_fin]

/-! ### Fibres versus cumulative sums -/

section Cum

variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}

/-- Weighted cumulative count. -/
def cumW (u : X → Fin (n + 1)) (w : X → ℕ) (j : ℕ) : ℕ :=
  ∑ x ∈ univ.filter (fun x => (u x : ℕ) ≤ j), w x

/-- Weighted fibre. -/
def fibW (u : X → Fin (n + 1)) (w : X → ℕ) (j : Fin (n + 1)) : ℕ :=
  ∑ x ∈ univ.filter (fun x => u x = j), w x

theorem cumW_eq_sum_fibW (u : X → Fin (n + 1)) (w : X → ℕ) (j : ℕ) :
    cumW u w j = ∑ j' ∈ univ.filter (fun j' : Fin (n + 1) => (j' : ℕ) ≤ j), fibW u w j' := by
  unfold cumW fibW
  rw [← Finset.sum_fiberwise_of_maps_to (g := u) (t := univ.filter (fun j' : Fin (n + 1) => (j' : ℕ) ≤ j))]
  · refine Finset.sum_congr rfl fun j' hj' => ?_
    have hj'' : (j' : ℕ) ≤ j := (Finset.mem_filter.mp hj').2
    rw [Finset.filter_filter]
    congr 1
    exact Finset.filter_congr fun x _ => ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hj'', h⟩⟩
  · intro x hx; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩

theorem cumW_succ (u : X → Fin (n + 1)) (w : X → ℕ) (j : ℕ) (hj : j + 1 < n + 1) :
    cumW u w (j + 1) = cumW u w j + fibW u w ⟨j + 1, hj⟩ := by
  unfold cumW fibW
  rw [← Finset.sum_union]
  · congr 1; ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Fin.ext_iff]
    omega
  · rw [Finset.disjoint_left]; intro x h1 h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff] at h1 h2; omega

theorem cumW_zero (u : X → Fin (n + 1)) (w : X → ℕ) : cumW u w 0 = fibW u w 0 := by
  unfold cumW fibW; congr 1; ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff, Fin.val_zero]; omega

theorem fibW_eq_iff {Y : Type*} [Fintype Y] [DecidableEq Y] (u : X → Fin (n + 1)) (w : X → ℕ)
    (v : Y → Fin (n + 1)) (w' : Y → ℕ) :
    (∀ j, fibW u w j = fibW v w' j) ↔ (∀ j, cumW u w j = cumW v w' j) := by
  constructor
  · intro h j; rw [cumW_eq_sum_fibW, cumW_eq_sum_fibW]; exact Finset.sum_congr rfl fun j' _ => h j'
  · intro h j
    rcases j with ⟨j, hj⟩
    rcases j with _ | j
    · have := h 0; rw [cumW_zero, cumW_zero] at this; exact this
    · have h1 := h (j + 1); have h0 := h j
      rw [cumW_succ u w j hj, cumW_succ v w' j hj] at h1; omega

end Cum

theorem fib_eq_fibW {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ} (u : X → Fin (n + 1)) (j : Fin (n + 1)) :
    fib u j = fibW u (fun _ => 1) j := by
  unfold fib fibW; rw [Finset.card_eq_sum_ones]

theorem cumW_blk {n : ℕ} (A : Finset ℕ) (j : ℕ) :
    cumW (blk n A) (fun _ => 1) j = (univ.filter (fun p : Fin n => block A p ≤ j)).card := by
  unfold cumW; rw [Finset.card_eq_sum_ones]; rfl

/-! ### Fitting labellings -/

section Fit

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (c : κ → ℕ)

/-- `h` has the weighted fibre sizes of the block labelling of `A`. -/
def Fits {n : ℕ} (h : κ → Fin (n + 1)) (A : Finset ℕ) : Prop :=
  ∀ j, fibW h c j = fib (blk n A) j

/-- Surjective onto `{0, …, k}` with odd partial weights below `k`. -/
def Valid {n : ℕ} (h : κ → Fin (n + 1)) (k : ℕ) : Prop :=
  (∀ a, (h a : ℕ) ≤ k) ∧ (∀ j ≤ k, ∃ a, (h a : ℕ) = j) ∧ ∀ t < k, Odd (cumW h c t)

instance {n : ℕ} (h : κ → Fin (n + 1)) (A : Finset ℕ) : Decidable (Fits c h A) := by
  unfold Fits; infer_instance

instance {n : ℕ} (h : κ → Fin (n + 1)) (k : ℕ) : Decidable (Valid c h k) := by
  unfold Valid; infer_instance

variable {c}

theorem fits_iff_cum {n : ℕ} (h : κ → Fin (n + 1)) (A : Finset ℕ) :
    Fits c h A ↔ ∀ j, cumW h c j = (univ.filter (fun p : Fin n => block A p ≤ j)).card := by
  unfold Fits
  simp_rw [fib_eq_fibW, ← cumW_blk]
  exact fibW_eq_iff h c (blk n A) (fun _ => 1)

theorem cumW_le_total {n : ℕ} (h : κ → Fin (n + 1)) (j : ℕ) : cumW h c j ≤ ∑ a, c a :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem cumW_eq_total {n : ℕ} (h : κ → Fin (n + 1)) {j : ℕ} (hj : ∀ a, (h a : ℕ) ≤ j) :
    cumW h c j = ∑ a, c a := by
  unfold cumW; rw [Finset.filter_true_of_mem fun a _ => hj a]

/-- With positive weights, a full cumulative sum includes every atom. -/
theorem le_of_cumW_eq_total (hc : ∀ a, 1 ≤ c a) {n : ℕ} (h : κ → Fin (n + 1)) {j : ℕ}
    (hj : cumW h c j = ∑ a, c a) (a : κ) : (h a : ℕ) ≤ j := by
  by_contra hlt
  have : cumW h c j < ∑ a, c a := by
    unfold cumW
    exact Finset.sum_lt_sum_of_subset (Finset.filter_subset _ univ) (Finset.mem_univ a)
      (by rw [Finset.mem_filter]; intro hm; exact hlt hm.2) (by have := hc a; omega)
      (fun _ _ _ => Nat.zero_le _)
  omega

/-- A strict increase of the cumulative sum at `j + 1` exhibits an atom labelled `j + 1`. -/
theorem exists_of_cumW_lt {n : ℕ} (h : κ → Fin (n + 1)) {j : ℕ} (hj : j + 1 < n + 1)
    (hlt : cumW h c j < cumW h c (j + 1)) : ∃ a, (h a : ℕ) = j + 1 := by
  rw [cumW_succ h c j hj] at hlt
  have : 0 < fibW h c ⟨j + 1, hj⟩ := by omega
  obtain ⟨a, ha, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.pos_iff_ne_zero.mp this)
  exact ⟨a, by have := (Finset.mem_filter.mp ha).2; rw [this]⟩

theorem exists_of_cumW_pos {n : ℕ} (h : κ → Fin (n + 1)) (hpos : 0 < cumW h c 0) :
    ∃ a, (h a : ℕ) = 0 := by
  rw [cumW_zero] at hpos
  obtain ⟨a, ha, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
  exact ⟨a, by have := (Finset.mem_filter.mp ha).2; rw [this]; rfl⟩

/-- Labels absent at `j + 1` leave the cumulative sum unchanged. -/
theorem cumW_succ_of_absent {n : ℕ} (h : κ → Fin (n + 1)) {j : ℕ} (hj : j + 1 < n + 1)
    (habs : ∀ a, (h a : ℕ) ≠ j + 1) : cumW h c (j + 1) = cumW h c j := by
  rw [cumW_succ h c j hj]
  have : fibW h c ⟨j + 1, hj⟩ = 0 := by
    unfold fibW; rw [Finset.sum_eq_zero]; intro a ha
    exact absurd (congrArg Fin.val (Finset.mem_filter.mp ha).2) (habs a)
  omega

end Fit

section Fit2

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {c : κ → ℕ}

theorem altS_sub (n : ℕ) : altS n ⊆ range (n - 1) := Finset.filter_subset _ _

theorem fibW_pos_of_label (hc : ∀ a, 1 ≤ c a) {n : ℕ} (h : κ → Fin (n + 1)) {a : κ} {j : Fin (n + 1)}
    (ha : h a = j) : 1 ≤ fibW h c j := by
  unfold fibW
  exact (hc a).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩))

theorem fits_valid (hc : ∀ a, 1 ≤ c a) {n : ℕ} (hn : n = ∑ a, c a) (hn1 : 1 ≤ n)
    {h : κ → Fin (n + 1)} {A : Finset ℕ} (hA : A ⊆ altS n) (hf : Fits c h A) :
    Valid c h A.card ∧ A = (range A.card).image (fun t => cumW h c t - 1) := by
  have hcum := (fits_iff_cum h A).mp hf
  have hAr : A ⊆ range (n - 1) := hA.trans (altS_sub n)
  have hval : ∀ a ∈ A, cumW h c (Fill.rk A a) = a + 1 := fun a ha => by
    rw [hcum]; exact card_block_le_rk hAr ha
  have htop : ∀ j, A.card ≤ j → cumW h c j = n := fun j hj => by
    rw [hcum, card_block_le_top A hj]
  have hAn : A.card ≤ n - 1 := by have := Finset.card_le_card hAr; simpa using this
  have hlt_n : ∀ a ∈ A, a + 1 < n := fun a ha => by
    have := Finset.mem_range.mp (hAr ha); omega
  refine ⟨⟨fun a => le_of_cumW_eq_total hc h (by rw [htop _ le_rfl, hn]) a, ?_, ?_⟩, ?_⟩
  · intro j hj
    rcases j with _ | j'
    · apply exists_of_cumW_pos h
      rcases Nat.eq_zero_or_pos A.card with h0 | h0
      · rw [htop 0 (by omega)]; omega
      · obtain ⟨a0, ha0, hr0⟩ := Fill.rk_surj h0
        rw [← hr0, hval a0 ha0]; omega
    · apply exists_of_cumW_lt h (by omega)
      obtain ⟨a, ha, hra⟩ := Fill.rk_surj (show j' < A.card by omega)
      have e1 : cumW h c j' = a + 1 := by rw [← hra]; exact hval a ha
      rw [e1]
      rcases Nat.lt_or_ge (j' + 1) A.card with h1 | h1
      · obtain ⟨a', ha', hra'⟩ := Fill.rk_surj h1
        have e2 : cumW h c (j' + 1) = a' + 1 := by rw [← hra']; exact hval a' ha'
        rw [e2]
        have : a < a' := Fill.lt_of_rk_lt (Y := A) (by rw [hra, hra']; omega)
        omega
      · rw [htop _ h1]; exact hlt_n a ha
  · intro t ht
    obtain ⟨a, ha, hra⟩ := Fill.rk_surj ht
    rw [← hra, hval a ha]
    have he : Even a := (Finset.mem_filter.mp (hA ha)).2
    exact he.add_one
  · ext a
    simp only [Finset.mem_image, Finset.mem_range]
    constructor
    · intro ha; exact ⟨Fill.rk A a, Fill.rk_lt_card ha, by rw [hval a ha]; omega⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨a', ha', hra'⟩ := Fill.rk_surj ht
      rw [← hra', hval a' ha']; simpa using ha'

theorem cumW_mono {n : ℕ} (h : κ → Fin (n + 1)) {t t' : ℕ} (htt : t ≤ t') :
    cumW h c t ≤ cumW h c t' :=
  Finset.sum_le_sum_of_subset (fun a ha => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2.trans htt⟩)

theorem cumW_strict (hc : ∀ a, 1 ≤ c a) {n k : ℕ} {h : κ → Fin (n + 1)} (hv : Valid c h k)
    (hkn : k ≤ n) : ∀ t t', t < t' → t' ≤ k → cumW h c t < cumW h c t' := by
  intro t t' htt' ht'k
  induction t', htt' using Nat.le_induction with
  | base =>
    obtain ⟨a, ha⟩ := hv.2.1 (t + 1) ht'k
    rw [cumW_succ h c t (by omega)]
    have := fibW_pos_of_label hc h (j := ⟨t + 1, by omega⟩) (Fin.ext ha)
    omega
  | succ t'' _ ih =>
    have := ih (by omega)
    obtain ⟨a, ha⟩ := hv.2.1 (t'' + 1) ht'k
    rw [cumW_succ h c t'' (by omega)]
    have := fibW_pos_of_label hc h (j := ⟨t'' + 1, by omega⟩) (Fin.ext ha)
    omega

theorem valid_fits (hc : ∀ a, 1 ≤ c a) {n : ℕ} (hn : n = ∑ a, c a) {h : κ → Fin (n + 1)} {k : ℕ}
    (hv : Valid c h k) (hkn : k ≤ n) :
    (range k).image (fun t => cumW h c t - 1) ⊆ altS n ∧
      ((range k).image (fun t => cumW h c t - 1)).card = k ∧
      Fits c h ((range k).image (fun t => cumW h c t - 1)) := by
  set f : ℕ → ℕ := fun t => cumW h c t - 1 with hfdef
  have hall : ∀ j, k ≤ j → cumW h c j = n := fun j hj => by
    rw [cumW_eq_total h (fun a => (hv.1 a).trans hj), hn]
  have hpos : 1 ≤ cumW h c 0 := by
    obtain ⟨a, ha⟩ := hv.2.1 0 (Nat.zero_le _)
    rw [cumW_zero]; exact fibW_pos_of_label hc h (j := 0) (Fin.ext ha)
  have hst := cumW_strict hc hv hkn
  have hge1 : ∀ t, 1 ≤ cumW h c t := fun t => hpos.trans (cumW_mono h (Nat.zero_le t))
  have hlt : ∀ t < k, cumW h c t < n := fun t ht => by
    have := hall k le_rfl; have := hst t k ht le_rfl; omega
  have hfmono : ∀ t t', t < t' → t' < k → f t < f t' := fun t t' h1 h2 => by
    simp only [hfdef]; have := hst t t' h1 h2.le; have := hge1 t; omega
  have hinj : Set.InjOn f (range k) := fun t ht t' ht' he => by
    simp only [Finset.coe_range, Set.mem_Iio] at ht ht'
    rcases lt_trichotomy t t' with c1 | c1 | c1
    · exact absurd he (hfmono t t' c1 ht').ne
    · exact c1
    · exact absurd he (hfmono t' t c1 ht).ne'
  set A := (range k).image f
  have hcard : A.card = k := by rw [Finset.card_image_of_injOn hinj, card_range]
  have hsub : A ⊆ altS n := by
    intro a ha
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
    have htk := Finset.mem_range.mp ht
    have hodd := hv.2.2 t htk
    have := hlt t htk; have := hge1 t
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by simp only [hfdef]; omega), ?_⟩
    obtain ⟨r, hr⟩ := hodd
    exact ⟨r, by simp only [hfdef]; omega⟩
  refine ⟨hsub, hcard, (fits_iff_cum h A).mpr fun j => ?_⟩
  rcases Nat.lt_or_ge j k with hjk | hjk
  · have hfj : f j ∈ A := Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hjk, rfl⟩
    have hrk : Fill.rk A (f j) = j := by
      unfold Fill.rk
      rw [Finset.filter_image, Finset.card_image_of_injOn (hinj.mono (fun t ht =>
        (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).1))]
      have : (range k).filter (fun t => f t < f j) = range j := by
        ext t; simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨htk, hft⟩
          by_contra hjt
          rcases eq_or_lt_of_le (not_lt.mp hjt) with e | e
          · rw [e] at hft; exact lt_irrefl _ hft
          · exact absurd hft (not_lt.mpr (hfmono j t e htk).le)
        · intro htj; exact ⟨by omega, hfmono t j htj hjk⟩
      rw [this, card_range]
    have := card_block_le_rk (n := n) (hsub.trans (altS_sub n)) hfj
    rw [hrk] at this; rw [this]; simp only [hfdef]; have := hge1 j; omega
  · rw [hall j hjk, card_block_le_top A (by omega)]

end Fit2

section Signed

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {c : κ → ℕ}

theorem valid_lt_card {n : ℕ} {h : κ → Fin (n + 1)} {k : ℕ} (hv : Valid c h k) :
    k < Fintype.card κ := by
  have hs : Function.Surjective (fun a => (⟨h a, by have := hv.1 a; omega⟩ : Fin (k + 1))) := by
    intro j; obtain ⟨a, ha⟩ := hv.2.1 j (by omega); exact ⟨a, Fin.ext ha⟩
  have := Fintype.card_le_of_surjective _ hs
  simp at this; omega

theorem valid_unique {n : ℕ} {h : κ → Fin (n + 1)} {k k' : ℕ} (hv : Valid c h k)
    (hv' : Valid c h k') : k = k' := by
  obtain ⟨a, ha⟩ := hv.2.1 k le_rfl
  obtain ⟨a', ha'⟩ := hv'.2.1 k' le_rfl
  have := hv'.1 a; have := hv.1 a'; omega

theorem card_le_total (hc : ∀ a, 1 ≤ c a) : Fintype.card κ ≤ ∑ a, c a := by
  calc Fintype.card κ = ∑ _a : κ, 1 := by simp
    _ ≤ ∑ a, c a := Finset.sum_le_sum fun a _ => hc a

theorem card_valid_eq_V {n k : ℕ} (hkn : k ≤ n) :
    (univ.filter (fun h : κ → Fin (n + 1) => Valid c h k)).card = (Atoms.V c k).card := by
  symm
  have hw : ∀ (g : κ → Fin (k + 1)) (t : ℕ),
      Atoms.wcum c g t = cumW (fun a => Fin.castLE (by omega : k + 1 ≤ n + 1) (g a)) c t := by
    intro g t; unfold Atoms.wcum cumW; rfl
  refine Finset.card_bij' (fun g _ => fun a => Fin.castLE (by omega : k + 1 ≤ n + 1) (g a))
    (fun h hh => fun a => ⟨h a, by have := (Finset.mem_filter.mp hh).2.1 a; omega⟩) ?_ ?_ ?_ ?_
  · intro g hg
    obtain ⟨hs, hodd⟩ := (Finset.mem_filter.mp hg).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun a => by simp; omega, fun j hj => ?_,
      fun t ht => by rw [← hw]; exact hodd t ht⟩
    obtain ⟨a, ha⟩ := hs ⟨j, by omega⟩
    exact ⟨a, by simp [ha]⟩
  · intro h hh
    obtain ⟨hle, hsurj, hodd⟩ := (Finset.mem_filter.mp hh).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_, fun t ht => ?_⟩
    · obtain ⟨a, ha⟩ := hsurj j (by omega); exact ⟨a, Fin.ext ha⟩
    · have e : Atoms.wcum c (fun a => (⟨h a, by have := hle a; omega⟩ : Fin (k + 1))) t =
          cumW h c t := rfl
      rw [e]; exact hodd t ht
  · intro g _; funext a; rfl
  · intro h _; funext a; rfl

/-- **Flags to Φ.** The signed count of labellings fitting the flag types `A ⊆ alt` is
`(-1)^|alt| Φ c`. -/
theorem signed_fits (hc : ∀ a, 1 ≤ c a) {n : ℕ} (hn : n = ∑ a, c a) (hn1 : 1 ≤ n) :
    (∑ A ∈ (altS n).powerset, (-1 : ℤ) ^ (altS n \ A).card *
      ((univ.filter (fun h : κ → Fin (n + 1) => Fits c h A)).card : ℤ)) =
      (-1 : ℤ) ^ (altS n).card * Atoms.Φ c := by
  have hκn : Fintype.card κ ≤ n := hn ▸ card_le_total hc
  have perH : ∀ h : κ → Fin (n + 1),
      (∑ A ∈ (altS n).powerset, (-1 : ℤ) ^ (altS n \ A).card * (if Fits c h A then 1 else 0)) =
        ∑ k ∈ range (Fintype.card κ), (-1 : ℤ) ^ (altS n).card *
          ((-1 : ℤ) ^ k * (if Valid c h k then 1 else 0)) := by
    intro h
    by_cases hex : ∃ k, Valid c h k
    · obtain ⟨k, hk⟩ := hex
      have hkκ := valid_lt_card hk
      obtain ⟨hsub, hcard, hfit⟩ := valid_fits hc hn hk (by omega)
      set A0 := (range k).image (fun t => cumW h c t - 1)
      rw [Finset.sum_eq_single A0, Finset.sum_eq_single k]
      · rw [if_pos hfit, if_pos hk, Finset.card_sdiff_of_subset hsub, hcard]
        have hk_le : k ≤ (altS n).card := hcard ▸ Finset.card_le_card hsub
        have : (-1 : ℤ) ^ (altS n).card = (-1) ^ ((altS n).card - k) * (-1) ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hk_le]
        rw [this, mul_one, mul_one, mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num
      · intro k' _ hk'
        rw [if_neg (fun hv => hk' (valid_unique hv hk)), mul_zero, mul_zero]
      · intro hk'; exact absurd (Finset.mem_range.mpr hkκ) hk'
      · intro A hA hne
        rw [if_neg, mul_zero]
        intro hf
        obtain ⟨hvA, hAeq⟩ := fits_valid hc hn hn1 (Finset.mem_powerset.mp hA) hf
        have := valid_unique hvA hk
        exact hne (by rw [hAeq, this])
      · intro hA0; exact absurd (Finset.mem_powerset.mpr hsub) hA0
    · push_neg at hex
      rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
      · intro k _; rw [if_neg (hex k)]; ring
      · intro A hA
        rw [if_neg, mul_zero]
        intro hf
        exact hex _ (fits_valid hc hn hn1 (Finset.mem_powerset.mp hA) hf).1
  have lhs : (∑ A ∈ (altS n).powerset, (-1 : ℤ) ^ (altS n \ A).card *
      ((univ.filter (fun h : κ → Fin (n + 1) => Fits c h A)).card : ℤ)) =
      ∑ h : κ → Fin (n + 1), ∑ A ∈ (altS n).powerset,
        (-1 : ℤ) ^ (altS n \ A).card * (if Fits c h A then 1 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> simp
  have rhs : (-1 : ℤ) ^ (altS n).card * Atoms.Φ c =
      ∑ h : κ → Fin (n + 1), ∑ k ∈ range (Fintype.card κ), (-1 : ℤ) ^ (altS n).card *
        ((-1 : ℤ) ^ k * (if Valid c h k then 1 else 0)) := by
    unfold Atoms.Φ
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
    rw [← card_valid_eq_V hkn, Finset.card_filter, Nat.cast_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs <;> simp
  rw [lhs, rhs]
  exact Finset.sum_congr rfl fun h _ => perH h

end Signed

end Stanley.Alt
