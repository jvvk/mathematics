/-
  Stanley, MathOverflow 486548. Part M. Signed counts of ordered set partitions with odd partial
  sums (the combinatorial core of Foulkes's evaluation of the alternating ribbon character).

  Atoms `a : κ` carry weights `c a`. `V c k` is the set of surjective labellings `h : κ → Fin (k+1)`
  whose partial weights `wcum c h t = Σ_{h a ≤ t} c a` are odd for every `t < k`, and
  `Φ c = Σ_k (-1)^k #V c k`. Main result (`Φ_option`): adding one atom of even weight multiplies
  `Φ` by `[Σ c even]` (when `κ` is nonempty). The new atom either shares a label with an old one
  (`k + 1` ways) or sits alone; alone, it may sit at labels `1, …, k-1`, and at the top label only
  when the old total is odd.
-/
import LeanProofs.Stanley.RibbonChar

namespace Stanley.Alt

namespace Atoms

open Finset

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Partial weight below label `t`. -/
def wcum (c : κ → ℕ) {k : ℕ} (h : κ → Fin (k + 1)) (t : ℕ) : ℕ :=
  ∑ a ∈ univ.filter (fun a => (h a : ℕ) ≤ t), c a

/-- Surjective labellings onto `{0, …, k}` with odd partial weights. -/
def V (c : κ → ℕ) (k : ℕ) : Finset (κ → Fin (k + 1)) :=
  univ.filter (fun h => Function.Surjective h ∧ ∀ t < k, Odd (wcum c h t))

/-- The signed count. -/
def Φ (c : κ → ℕ) : ℤ := ∑ k ∈ range (Fintype.card κ), (-1 : ℤ) ^ k * (V c k).card

theorem V_eq_empty (c : κ → ℕ) {k : ℕ} (hk : Fintype.card κ ≤ k) : V c k = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro h hh
  have hs := (Finset.mem_filter.mp hh).2.1
  have := Fintype.card_le_of_surjective h hs
  simp at this; omega

/-! ### One extra atom -/

/-- Weights on `Option κ`: the new atom `none` has weight `d`. -/
def ext (c : κ → ℕ) (d : ℕ) : Option κ → ℕ := fun o => o.elim d c

theorem wcum_option (c : κ → ℕ) (d : ℕ) {k : ℕ} (h' : Option κ → Fin (k + 1)) (t : ℕ) :
    wcum (ext c d) h' t = wcum c (h' ∘ some) t + if (h' none : ℕ) ≤ t then d else 0 := by
  unfold wcum
  rw [Finset.sum_filter, Finset.sum_filter, Fintype.sum_option]
  simp only [ext, Option.elim, Function.comp_apply]
  ring

theorem odd_wcum_ext (c : κ → ℕ) {d : ℕ} (hd : Even d) {k : ℕ} (h' : Option κ → Fin (k + 1))
    (t : ℕ) : Odd (wcum (ext c d) h' t) ↔ Odd (wcum c (h' ∘ some) t) := by
  rw [wcum_option]
  split_ifs
  · rw [Nat.odd_add]; constructor
    · intro h; exact h.mpr hd
    · intro h; exact ⟨fun _ => hd, fun _ => h⟩
  · simp

/-- The new atom shares its label: `(k+1) · #V c k` labellings. -/
theorem card_shared (c : κ → ℕ) {d : ℕ} (hd : Even d) (k : ℕ) :
    ((V (ext c d) k).filter (fun h' => ∃ a, h' (some a) = h' none)).card =
      (V c k).card * (k + 1) := by
  have hp : (V c k).card * (k + 1) = (V c k ×ˢ (univ : Finset (Fin (k + 1)))).card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]
  rw [hp]
  refine Finset.card_bij' (fun h' _ => (h' ∘ some, h' none))
    (fun p _ => fun o => o.elim p.2 p.1) ?_ ?_ ?_ ?_
  · intro h' hh
    simp only [V, Finset.mem_filter, Finset.mem_univ, true_and] at hh
    obtain ⟨⟨hs, hodd⟩, a0, ha0⟩ := hh
    simp only [V, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true]
    refine ⟨fun y => ?_, fun t ht => (odd_wcum_ext c hd h' t).mp (hodd t ht)⟩
    obtain ⟨o, ho⟩ := hs y
    cases o with
    | none => exact ⟨a0, by rw [Function.comp_apply, ha0, ho]⟩
    | some a => exact ⟨a, ho⟩
  · intro p hp
    simp only [V, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and,
      and_true] at hp
    obtain ⟨hs, hodd⟩ := hp
    simp only [V, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨fun y => ?_, fun t ht => ?_⟩, ?_⟩
    · obtain ⟨a, ha⟩ := hs y; exact ⟨some a, ha⟩
    · rw [odd_wcum_ext c hd]; exact hodd t ht
    · obtain ⟨a, ha⟩ := hs p.2; exact ⟨a, ha⟩
  · intro h' _; funext o; cases o <;> rfl
  · intro p _; rfl

/-- Insert a label `x`, shifting labels `≥ x` up. -/
def expand {k₀ : ℕ} (x : Fin (k₀ + 2)) (y : Fin (k₀ + 1)) : Fin (k₀ + 2) :=
  ⟨if (y : ℕ) < x then y else y + 1, by split_ifs <;> omega⟩

/-- Delete the label `x`, shifting labels `> x` down. -/
def compress {k₀ : ℕ} (x : Fin (k₀ + 2)) (z : Fin (k₀ + 2)) : Fin (k₀ + 1) :=
  ⟨if (z : ℕ) < x then z else z - 1, by have := z.2; have := x.2; split_ifs <;> omega⟩

theorem expand_val {k₀ : ℕ} (x : Fin (k₀ + 2)) (y : Fin (k₀ + 1)) :
    (expand x y : ℕ) = if (y : ℕ) < (x : ℕ) then (y : ℕ) else (y : ℕ) + 1 := rfl

theorem expand_ne {k₀ : ℕ} (x : Fin (k₀ + 2)) (y : Fin (k₀ + 1)) : expand x y ≠ x := by
  intro h; have := congrArg Fin.val h; simp only [expand] at this; split_ifs at this <;> omega

theorem expand_compress {k₀ : ℕ} {x z : Fin (k₀ + 2)} (h : z ≠ x) : expand x (compress x z) = z := by
  have h' : (z : ℕ) ≠ x := fun e => h (Fin.ext e)
  apply Fin.ext; simp only [expand, compress]; split_ifs <;> omega

theorem compress_expand {k₀ : ℕ} (x : Fin (k₀ + 2)) (y : Fin (k₀ + 1)) :
    compress x (expand x y) = y := by
  apply Fin.ext; simp only [expand, compress]; split_ifs <;> omega

/-- Partial weights after inserting the label `x`. -/
theorem wcum_expand (c : κ → ℕ) {k₀ : ℕ} (x : Fin (k₀ + 2)) (h : κ → Fin (k₀ + 1)) (t : ℕ) :
    wcum c (expand x ∘ h) t =
      if t < x then wcum c h t else ∑ a ∈ univ.filter (fun a => (h a : ℕ) + 1 ≤ t), c a := by
  unfold wcum
  split_ifs with ht
  · congr 1; apply Finset.filter_congr; intro a _
    simp only [Function.comp_apply, expand_val]; split_ifs <;> omega
  · congr 1; apply Finset.filter_congr; intro a _
    simp only [Function.comp_apply, expand_val]; split_ifs <;> omega

theorem wcum_top (c : κ → ℕ) {k : ℕ} (h : κ → Fin (k + 1)) : wcum c h k = ∑ a, c a := by
  unfold wcum; congr 1; ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    iff_true]; have := (h a).2; omega

theorem wcum_pred (c : κ → ℕ) {k : ℕ} (h : κ → Fin (k + 1)) {t : ℕ} (ht : 1 ≤ t) :
    ∑ a ∈ univ.filter (fun a => (h a : ℕ) + 1 ≤ t), c a = wcum c h (t - 1) := by
  unfold wcum; congr 1; ext a; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega

/-- Validity of a labelling with the new atom alone at label `x`. -/
theorem valid_alone_iff (c : κ → ℕ) {d : ℕ} (hd : Even d) {k₀ : ℕ} (x : Fin (k₀ + 2))
    (h : κ → Fin (k₀ + 1)) :
    (Function.Surjective (fun o => o.elim x (fun a => expand x (h a)) : Option κ → Fin (k₀ + 2)) ∧
      ∀ t < k₀ + 1, Odd (wcum (ext c d) (fun o => o.elim x (fun a => expand x (h a))) t)) ↔
    ((x : ℕ) ≠ 0 ∧ ((x : ℕ) = k₀ + 1 → Odd (∑ a, c a))) ∧
      (Function.Surjective h ∧ ∀ t < k₀, Odd (wcum c h t)) := by
  set h' : Option κ → Fin (k₀ + 2) := fun o => o.elim x (fun a => expand x (h a))
  have hsome : h' ∘ some = expand x ∘ h := rfl
  have hpar : ∀ t, Odd (wcum (ext c d) h' t) ↔ Odd (wcum c (expand x ∘ h) t) := fun t => by
    rw [odd_wcum_ext c hd, hsome]
  have hsurj : Function.Surjective h' ↔ Function.Surjective h := by
    constructor
    · intro hs y
      obtain ⟨o, ho⟩ := hs (expand x y)
      cases o with
      | none => exact absurd ho.symm (expand_ne x y)
      | some a =>
        refine ⟨a, ?_⟩
        have := congrArg (compress x) ho
        simpa [h', compress_expand] using this
    · intro hs z
      by_cases hz : z = x
      · exact ⟨none, hz.symm⟩
      · obtain ⟨a, ha⟩ := hs (compress x z)
        exact ⟨some a, by simp [h', ha, expand_compress hz]⟩
  rw [hsurj]
  simp_rw [hpar, wcum_expand]
  have hx := x.2
  constructor
  · rintro ⟨hs, hodd⟩
    have hx0 : (x : ℕ) ≠ 0 := by
      intro h0
      have := hodd 0 (by omega)
      rw [if_neg (by omega)] at this
      have he : univ.filter (fun a => (h a : ℕ) + 1 ≤ 0) = ∅ := by
        ext a; simp
      rw [he, Finset.sum_empty] at this
      exact absurd this (by decide)
    refine ⟨⟨hx0, fun htop => ?_⟩, hs, fun t ht => ?_⟩
    · have := hodd k₀ (by omega)
      rw [if_pos (by omega), wcum_top] at this; exact this
    · by_cases htx : t < x
      · have := hodd t (by omega); rwa [if_pos htx] at this
      · have := hodd (t + 1) (by omega)
        rw [if_neg (by omega), wcum_pred c h (by omega)] at this
        simpa using this
  · rintro ⟨⟨hx0, htop⟩, hs, hodd⟩
    refine ⟨hs, fun t ht => ?_⟩
    split_ifs with htx
    · by_cases htk : t < k₀
      · exact hodd t htk
      · have : t = k₀ := by omega
        rw [this, wcum_top]; exact htop (by omega)
    · rw [wcum_pred c h (by omega)]; exact hodd (t - 1) (by omega)

/-- The new atom alone: `(k₀ + [Σ c odd]) · #V c k₀` labellings at level `k₀ + 1`. -/
theorem card_alone (c : κ → ℕ) {d : ℕ} (hd : Even d) (k₀ : ℕ) :
    ((V (ext c d) (k₀ + 1)).filter (fun h' => ¬∃ a, h' (some a) = h' none)).card =
      (univ.filter (fun x : Fin (k₀ + 2) =>
        (x : ℕ) ≠ 0 ∧ ((x : ℕ) = k₀ + 1 → Odd (∑ a, c a)))).card * (V c k₀).card := by
  rw [← Finset.card_product]
  refine Finset.card_bij' (fun h' _ => (h' none, fun a => compress (h' none) (h' (some a))))
    (fun p _ => fun o => o.elim p.1 (fun a => expand p.1 (p.2 a))) ?_ ?_ ?_ ?_
  · intro h' hh
    simp only [V, Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hh
    obtain ⟨⟨hs, hodd⟩, hne⟩ := hh
    have hrecon : (fun o : Option κ => o.elim (h' none)
        (fun a => expand (h' none) (compress (h' none) (h' (some a))))) = h' := by
      funext o; cases o with
      | none => rfl
      | some a => exact expand_compress (hne a)
    have key := (valid_alone_iff c hd (h' none) (fun a => compress (h' none) (h' (some a)))).mp
      (by rw [hrecon]; exact ⟨hs, hodd⟩)
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact key.1
    · simp only [V, Finset.mem_filter, Finset.mem_univ, true_and]; exact key.2
  · intro p hp
    rw [Finset.mem_product, Finset.mem_filter, V, Finset.mem_filter] at hp
    have key := (valid_alone_iff c hd p.1 p.2).mpr ⟨hp.1.2, hp.2.2⟩
    simp only [V, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
    exact ⟨key, fun a => expand_ne p.1 (p.2 a)⟩
  · intro h' hh
    simp only [V, Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hh
    funext o; cases o with
    | none => rfl
    | some a => exact expand_compress (hh.2 a)
  · intro p _
    ext a
    · rfl
    · simp [compress_expand]

theorem card_allowed (k₀ : ℕ) (P : Prop) [Decidable P] :
    (univ.filter (fun x : Fin (k₀ + 2) => (x : ℕ) ≠ 0 ∧ ((x : ℕ) = k₀ + 1 → P))).card =
      k₀ + if P then 1 else 0 := by
  rw [← Finset.card_map Fin.valEmbedding]
  have : (univ.filter (fun x : Fin (k₀ + 2) => (x : ℕ) ≠ 0 ∧ ((x : ℕ) = k₀ + 1 → P))).map
      Fin.valEmbedding = (Finset.Ico 1 (k₀ + 1 + if P then 1 else 0)) := by
    ext i
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico]
    constructor
    · rintro ⟨x, ⟨hx0, hP⟩, rfl⟩
      have := x.2
      split_ifs with hp
      · omega
      · by_cases he : (x : ℕ) = k₀ + 1
        · exact absurd (hP he) hp
        · omega
    · intro hi
      refine ⟨⟨i, by split_ifs at hi <;> omega⟩, ⟨by simp only; omega, fun he => ?_⟩, rfl⟩
      simp only at he
      split_ifs at hi with hp
      · exact hp
      · omega
  rw [this, Nat.card_Ico]
  split_ifs <;> omega

theorem alg_telescope (v : ℕ → ℤ) (o : ℤ) (K : ℕ) (hv : v K = 0) :
    ∑ k ∈ range (K + 1), (-1 : ℤ) ^ k * (v k * ((k : ℤ) + 1) +
      if k = 0 then 0 else (((k - 1 : ℕ) : ℤ) + o) * v (k - 1)) =
    (1 - o) * ∑ k ∈ range K, (-1 : ℤ) ^ k * v k := by
  set T : ℕ → ℤ := fun k => if k = 0 then 0 else (((k - 1 : ℕ) : ℤ) + o) * v (k - 1) with hT
  have hsplit : ∑ k ∈ range (K + 1), (-1 : ℤ) ^ k * (v k * ((k : ℤ) + 1) + T k) =
      ∑ k ∈ range (K + 1), (-1 : ℤ) ^ k * (v k * ((k : ℤ) + 1)) +
        ∑ k ∈ range (K + 1), (-1 : ℤ) ^ k * T k := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit, Finset.sum_range_succ (fun k => (-1 : ℤ) ^ k * (v k * ((k : ℤ) + 1))), hv,
    Finset.sum_range_succ' (fun k => (-1 : ℤ) ^ k * T k)]
  simp only [hT]
  simp only [mul_zero, zero_mul, add_zero, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel,
    ↓reduceIte, mul_zero]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_succ]; push_cast; ring

/-- **One even atom.** `Φ (ext c d) = [Σ c even] · Φ c` for `κ` nonempty and `d` even. -/
theorem Φ_option (c : κ → ℕ) {d : ℕ} (hd : Even d) [Nonempty κ] :
    Φ (ext c d) = (if Even (∑ a, c a) then 1 else 0) * Φ c := by
  set K := Fintype.card κ
  set o : ℕ := if Odd (∑ a, c a) then 1 else 0 with ho
  have hsplit : ∀ k, ((V (ext c d) k).card : ℤ) =
      ((V c k).card * (k + 1) : ℕ) +
        (if k = 0 then 0 else (((k - 1) + o) * (V c (k - 1)).card : ℕ)) := by
    intro k
    rw [← Finset.card_filter_add_card_filter_not (s := V (ext c d) k)
      (p := fun h' => ∃ a, h' (some a) = h' none), card_shared c hd]
    rcases k with _ | k₀
    · simp only [↓reduceIte, Nat.cast_add, add_zero]
      have : (V (ext c d) 0).filter (fun h' => ¬∃ a, h' (some a) = h' none) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro h' _ hn
        obtain ⟨a⟩ := ‹Nonempty κ›
        exact hn ⟨a, Fin.ext (by have := (h' (some a)).2; have := (h' none).2; omega)⟩
      rw [this, Finset.card_empty, Nat.cast_zero, add_zero]
    · rw [card_alone c hd, card_allowed, ho]
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      rw [show k₀ + 1 - 1 = k₀ by omega]
      push_cast; ring
  have hcard : Fintype.card (Option κ) = K + 1 := Fintype.card_option
  unfold Φ
  rw [hcard]
  simp_rw [hsplit]
  have halg := alg_telescope (fun k => ((V c k).card : ℤ)) (o : ℤ) K
    (by simp only [V_eq_empty c (le_refl K), Finset.card_empty, Nat.cast_zero])
  have hterm : ∀ k ∈ range (K + 1), (-1 : ℤ) ^ k * ((((V c k).card * (k + 1) : ℕ) : ℤ) +
      (((if k = 0 then 0 else ((k - 1) + o) * (V c (k - 1)).card) : ℕ) : ℤ)) =
      (-1 : ℤ) ^ k * (((V c k).card : ℤ) * ((k : ℤ) + 1) +
        if k = 0 then 0 else (((k - 1 : ℕ) : ℤ) + o) * ((V c (k - 1)).card : ℤ)) := by
    intro k _; split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl hterm, halg]
  congr 1
  rw [ho]
  rcases Nat.even_or_odd (∑ a, c a) with he | ho'
  · rw [if_pos he, if_neg (Nat.not_odd_iff_even.mpr he)]; norm_num
  · rw [if_neg (Nat.not_even_iff_odd.mpr ho'), if_pos ho']; norm_num

end Atoms

end Stanley.Alt
