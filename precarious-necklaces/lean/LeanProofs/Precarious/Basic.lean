import Mathlib

/-!
# Precarious necklaces (MO 515996): the counting bound and the two-colour lemma

A necklace is a cyclic word; it is rotationally symmetric exactly when a (any) linear representative is a
proper power `v ^ r`, `r ≥ 2`. A necklace is *precarious* when it is not symmetric but deleting every bead of
any one colour leaves a symmetric necklace.

* `count_dvd_of_pow`: if `w` with colour `c` deleted is `U ^ r`, every other colour count is a multiple of `r`.
* `pow_of_pairs`: if every two-colour projection of `w` is a `q`-th power, so is `w`. The proof works on the
  prefix-count vectors of `w`, which form a monotone chain: a point lies on the chain as soon as each of its
  two-colour projections lies on the corresponding projected chain (`prefix_counts_of_pairs`).
* `prime_dvd_at_most_two`: in a precarious word, a prime divides the repeat count of at most two colours.

`Symm` is stated with powers; `Rotation.lean` proves this is the same as invariance under a non-identity
rotation (`symm_iff_rotate`), and that symmetry and deletion do not depend on the representative.
-/

set_option linter.unusedSectionVars false

namespace Precarious

open List

variable {α : Type*} [DecidableEq α]

/-- `w = v ^ r` as words. -/
def IsPow (w : List α) (r : ℕ) : Prop := ∃ v : List α, w = (replicate r v).flatten

/-- The necklace of `w` is rotationally symmetric: `w` is a proper power. -/
def Symm (w : List α) : Prop := ∃ r, 2 ≤ r ∧ IsPow w r

/-- Delete every bead of colour `c`. -/
def del (c : α) (w : List α) : List α := w.filter (fun z => z ≠ c)

/-- Keep only the beads of colours `x` and `y`. -/
def pair (x y : α) (w : List α) : List α := w.filter (fun z => z = x ∨ z = y)

/-- Precarious: not symmetric, at least two colours, and symmetric after deleting any one colour. -/
def IsPrecarious (w : List α) : Prop :=
  ¬ Symm w ∧ 2 ≤ w.toFinset.card ∧ ∀ c ∈ w, Symm (del c w)

lemma count_flatten_replicate (r : ℕ) (v : List α) (z : α) :
    ((replicate r v).flatten).count z = r * v.count z := by
  induction r with
  | zero => simp
  | succ r ih => simp [replicate_succ, flatten_cons, count_append, ih, Nat.succ_mul, add_comm]

lemma filter_flatten_replicate (p : α → Bool) (r : ℕ) (v : List α) :
    ((replicate r v).flatten).filter p = (replicate r (v.filter p)).flatten := by
  induction r with
  | zero => simp
  | succ r ih => simp [replicate_succ, flatten_cons, filter_append, ih]

lemma flatten_replicate_mul (q m : ℕ) (v : List α) :
    (replicate (q * m) v).flatten = (replicate q (replicate m v).flatten).flatten := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, ← replicate_append_replicate, flatten_append, ih, replicate_succ', flatten_append]
    simp

/-- **Counting.** Deleting `c` leaves `U ^ r`, so `r` divides the count of every other colour. -/
theorem count_dvd_of_pow {w : List α} {c x : α} {r : ℕ} (h : IsPow (del c w) r) (hx : x ≠ c) :
    r ∣ w.count x := by
  obtain ⟨v, hv⟩ := h
  have : (del c w).count x = w.count x := by
    simp [del, count_filter, hx]
  refine ⟨v.count x, ?_⟩
  rw [← this, hv, count_flatten_replicate]

/-! ### Prefix counts -/

lemma count_take_mono (w : List α) (z : α) {s t : ℕ} (h : s ≤ t) :
    (w.take s).count z ≤ (w.take t).count z := by
  have : w.take s <+: w.take t := by
    rw [show w.take s = (w.take t).take s by rw [take_take, Nat.min_eq_left h]]
    exact take_prefix _ _
  exact this.sublist.count_le z

/-- Every prefix of a filtered word is the filter of a prefix. -/
lemma prefix_filter (p : α → Bool) (w : List α) :
    ∀ j ≤ (w.filter p).length, ∃ t ≤ w.length, (w.filter p).take j = (w.take t).filter p := by
  induction w with
  | nil => intro j _; exact ⟨0, le_rfl, by simp⟩
  | cons a w ih =>
    intro j hj
    by_cases hj0 : j = 0
    · exact ⟨0, Nat.zero_le _, by simp [hj0]⟩
    by_cases ha : p a = true
    · have hj' : j - 1 ≤ (w.filter p).length := by
        simp [filter_cons, ha] at hj; omega
      obtain ⟨t, ht, he⟩ := ih (j - 1) hj'
      refine ⟨t + 1, by simp; omega, ?_⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at he
      simp [filter_cons, ha, take_succ_cons, he]
    · have hj' : j ≤ (w.filter p).length := by simpa [filter_cons, ha] using hj
      obtain ⟨t, ht, he⟩ := ih j hj'
      exact ⟨t + 1, by simp; omega, by simp [filter_cons, ha, take_succ_cons, he]⟩

/-- In `v ^ q`, moving a prefix end by `|v|` adds one copy of `v` to every count. -/
lemma count_take_pow_shift (q : ℕ) (v : List α) (z : α) {j : ℕ}
    (hj : j + v.length ≤ ((replicate q v).flatten).length) :
    (((replicate q v).flatten).take (j + v.length)).count z
      = (((replicate q v).flatten).take j).count z + v.count z := by
  cases q with
  | zero =>
    simp at hj; obtain ⟨rfl, rfl⟩ := hj; simp
  | succ q =>
    have e1 : (replicate (q + 1) v).flatten = v ++ (replicate q v).flatten := by
      simp [replicate_succ, flatten_cons]
    have e2 : (replicate (q + 1) v).flatten = (replicate q v).flatten ++ v := by
      rw [replicate_succ', flatten_append]; simp
    have hl : ((replicate q v).flatten).length = q * v.length := by simp [length_flatten]
    have hl' : ((replicate (q + 1) v).flatten).length = q * v.length + v.length := by
      rw [e2, length_append, hl]
    have hjq : j ≤ q * v.length := by rw [hl'] at hj; omega
    have L : (((replicate (q + 1) v).flatten).take (j + v.length)).count z
        = v.count z + (((replicate q v).flatten).take j).count z := by
      rw [e1, take_append, take_of_length_le (by omega), show j + v.length - v.length = j by omega,
        count_append]
    have R : (((replicate (q + 1) v).flatten).take j).count z = (((replicate q v).flatten).take j).count z := by
      rw [e2, take_append_of_le_length (by omega)]
    rw [L, R]; omega

/-- The prefix counts of `w` sum to the prefix length. -/
lemma sum_count_take (w : List α) (A : Finset α) (hA : ∀ z ∈ w, z ∈ A) (t : ℕ) :
    ∑ z ∈ A, (w.take t).count z = min t w.length := by
  rw [← length_take, ← List.sum_toFinset_count_eq_length]
  symm
  apply Finset.sum_subset
  · intro z hz; exact hA z (mem_of_mem_take (mem_toFinset.mp hz))
  · intro z _ hz; exact count_eq_zero.mpr (by simpa using hz)

lemma count_take_succ (w : List α) (z : α) {t : ℕ} (h : t < w.length) :
    (w.take (t + 1)).count z = (w.take t).count z + if w[t] = z then 1 else 0 := by
  rw [take_succ, getElem?_eq_getElem h, Option.toList_some, count_append, count_cons, count_nil]
  by_cases hz : w[t] = z <;> simp [hz]

/-- A word of length `q * B` with period `B` is the `q`-th power of its first `B` letters. -/
lemma pow_of_periodic (B : ℕ) : ∀ (q : ℕ) (w : List α), w.length = q * B →
    (∀ i (h : i + B < w.length), w[i + B] = w[i]'(by omega)) →
    w = (replicate q (w.take B)).flatten := by
  intro q
  induction q with
  | zero => intro w hw _; simp at hw; simp [hw]
  | succ q ih =>
    intro w hw hper
    have hBw : B ≤ w.length := by rw [hw, Nat.succ_mul]; omega
    have hdrop : (w.drop B).length = q * B := by rw [length_drop, hw, Nat.succ_mul]; omega
    have hper' : ∀ i (h : i + B < (w.drop B).length),
        (w.drop B)[i + B] = (w.drop B)[i]'(by omega) := by
      intro i h
      simp only [getElem_drop]
      have := hper (B + i) (by rw [length_drop] at h; omega)
      simpa [show B + (i + B) = B + i + B by omega] using this
    have hrest : w.drop B = (replicate q (w.take B)).flatten := by
      rcases Nat.eq_zero_or_pos q with hq0 | hq0
      · subst hq0
        simp only [replicate_zero, flatten_nil]
        exact drop_eq_nil_of_le (by rw [hw]; simp)
      · rw [ih (w.drop B) hdrop hper']
        congr 2
        apply List.ext_getElem
        · simp [length_take, length_drop]; rw [hw, Nat.succ_mul]
          have : B ≤ q * B := Nat.le_mul_of_pos_left B hq0
          omega
        · intro i h1 h2
          simp only [getElem_take, getElem_drop]
          have hi : i < B := by simp at h2; omega
          have := hper i (by rw [hw, Nat.succ_mul]; have : B ≤ q * B := Nat.le_mul_of_pos_left B hq0; omega)
          simpa [add_comm] using this
    calc w = w.take B ++ w.drop B := (take_append_drop B w).symm
      _ = (replicate (q + 1) (w.take B)).flatten := by rw [hrest, replicate_succ, flatten_cons]

/-- **Chain separation.** Prefix counts form a chain: a vector whose two-colour projections all occur as
prefix-count pairs, and whose total is at most `|w|`, is itself the prefix-count vector at that total. -/
lemma prefix_counts_of_pairs (w : List α) (A : Finset α) (hA : ∀ z ∈ w, z ∈ A) (p : α → ℕ)
    (hpair : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      ∃ t, (w.take t).count x = p x ∧ (w.take t).count y = p y)
    (ht : ∑ z ∈ A, p z ≤ w.length) :
    ∀ z ∈ A, (w.take (∑ z ∈ A, p z)).count z = p z := by
  set t := ∑ z ∈ A, p z
  have hsum : ∑ z ∈ A, (w.take t).count z = t := by
    have h1 : ∑ z ∈ A, (w.take t).count z = (w.take t).length := by
      rw [← List.sum_toFinset_count_eq_length]
      symm
      apply Finset.sum_subset
      · intro z hz; exact hA z (mem_of_mem_take (mem_toFinset.mp hz))
      · intro z _ hz; exact count_eq_zero.mpr (by simpa using hz)
    rw [h1, length_take]; omega
  by_contra hne
  push Not at hne
  obtain ⟨z, hzA, hz⟩ := hne
  -- some colour is over and some under its target
  have hover : ∃ x ∈ A, p x < (w.take t).count x := by
    by_contra h; push Not at h
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · have := Finset.sum_lt_sum h ⟨z, hzA, hlt⟩; omega
    · exact absurd (h z hzA) (by omega)
  have hunder : ∃ y ∈ A, (w.take t).count y < p y := by
    by_contra h; push Not at h
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · exact absurd (h z hzA) (by omega)
    · have := Finset.sum_lt_sum h ⟨z, hzA, hgt⟩; omega
  obtain ⟨x, hxA, hx⟩ := hover
  obtain ⟨y, hyA, hy⟩ := hunder
  have hxy : x ≠ y := by rintro rfl; omega
  obtain ⟨s, hsx, hsy⟩ := hpair x hxA y hyA hxy
  have hst : s < t := by
    by_contra h; push Not at h
    have := count_take_mono w x h; omega
  have := count_take_mono w y hst.le; omega

/-- **Pairs force the power.** If every two-colour projection of `w` is a `q`-th power (`q ≥ 1`), with at
least two colours, then `w` is a `q`-th power. -/
theorem pow_of_pairs (w : List α) (q : ℕ) (hq : 1 ≤ q) (h2 : 2 ≤ w.toFinset.card)
    (hpairs : ∀ x ∈ w, ∀ y ∈ w, x ≠ y → IsPow (pair x y w) q) : IsPow w q := by
  set A := w.toFinset with hAdef
  have hA : ∀ z ∈ w, z ∈ A := fun z hz => mem_toFinset.mpr hz
  have partner : ∀ x ∈ w, ∃ y ∈ w, y ≠ x := by
    intro x hx
    by_contra h
    push Not at h
    have hsub : A ⊆ {x} := by
      intro z hz; simp [h z (mem_toFinset.mp hz)]
    have := Finset.card_le_card hsub
    simp at this; omega
  have cpl : ∀ x y, (pair x y w).count x = w.count x := by intro x y; simp [pair, count_filter]
  have cpr : ∀ x y, (pair x y w).count y = w.count y := by intro x y; simp [pair, count_filter]
  have hdvd : ∀ x ∈ w, q ∣ w.count x := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := partner x hx
    obtain ⟨v, hv⟩ := hpairs x hx y hy hyx.symm
    exact ⟨v.count x, by rw [← cpl x y, hv, count_flatten_replicate]⟩
  set s : α → ℕ := fun z => w.count z / q with hsdef
  have hs : ∀ z ∈ w, w.count z = q * s z := fun z hz => (Nat.mul_div_cancel' (hdvd z hz)).symm
  set B := ∑ z ∈ A, s z with hBdef
  have hL : w.length = q * B := by
    rw [← List.sum_toFinset_count_eq_length, hBdef, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z hz => hs z (mem_toFinset.mp hz))
  have hBL : B ≤ w.length := by rw [hL]; exact Nat.le_mul_of_pos_left B hq
  set W := w ++ w with hWdef
  have hWlen : W.length = w.length + w.length := by simp [W]
  have hWA : ∀ z ∈ W, z ∈ A := by
    intro z hz; simp only [W, mem_append] at hz; rcases hz with h | h <;> exact hA z h
  have hWpair : ∀ x ∈ w, ∀ y ∈ w, x ≠ y → ∃ v : List α,
      pair x y W = (replicate (q + q) v).flatten ∧ pair x y w = (replicate q v).flatten ∧
      v.count x = s x ∧ v.count y = s y := by
    intro x hx y hy hxy
    obtain ⟨v, hv⟩ := hpairs x hx y hy hxy
    refine ⟨v, ?_, hv, ?_, ?_⟩
    · have : pair x y W = pair x y w ++ pair x y w := by simp [pair, W, filter_append]
      rw [this, hv, replicate_add, flatten_append]
    · have h := cpl x y
      rw [hv, count_flatten_replicate, hs x hx] at h
      exact Nat.eq_of_mul_eq_mul_left hq h
    · have h := cpr x y
      rw [hv, count_flatten_replicate, hs y hy] at h
      exact Nat.eq_of_mul_eq_mul_left hq h
  have takeW : ∀ t ≤ w.length, W.take t = w.take t := fun t ht => by
    simp only [W]; exact take_append_of_le_length ht
  -- the prefix-count vector of `W` shifts by `s` after `B` letters
  have shift : ∀ t ≤ w.length, ∀ z ∈ A, (W.take (t + B)).count z = (W.take t).count z + s z := by
    intro t ht
    set p : α → ℕ := fun z => (W.take t).count z + s z with hpdef
    have hsum : ∑ z ∈ A, p z = t + B := by
      simp only [hpdef, Finset.sum_add_distrib]
      rw [sum_count_take W A hWA t, hWlen, Nat.min_eq_left (by omega)]
    have key := prefix_counts_of_pairs W A hWA p ?_ (by rw [hsum, hWlen]; omega)
    · intro z hz
      have h := key z hz
      rw [hsum] at h
      exact h
    · intro x hxA y hyA hxy
      have hx : x ∈ w := mem_toFinset.mp hxA
      have hy : y ∈ w := mem_toFinset.mp hyA
      obtain ⟨v, hvW, hvw, hvx, hvy⟩ := hWpair x hx y hy hxy
      set f : α → Bool := fun z => decide (z = x ∨ z = y) with hfdef
      have hPW : pair x y W = W.filter f := rfl
      set j := ((W.take t).filter f).length with hjdef
      have hpre : (W.filter f).take j = (W.take t).filter f := by
        have h : (W.take t).filter f <+: W.filter f := (take_prefix t W).filter f
        exact (prefix_iff_eq_take.mp h).symm
      have hj1 : j ≤ (pair x y w).length := by
        rw [hjdef, takeW t ht]
        exact ((take_sublist t w).filter f).length_le
      have hlenw : (pair x y w).length = q * v.length := by rw [hvw]; simp [length_flatten]
      have hlenW : (W.filter f).length = (q + q) * v.length := by
        rw [← hPW, hvW]; simp [length_flatten]
      have hjv : j + v.length ≤ (W.filter f).length := by
        rw [hlenW]; rw [hlenw] at hj1
        have : v.length ≤ q * v.length := Nat.le_mul_of_pos_left _ hq
        nlinarith
      obtain ⟨t', _, he⟩ := prefix_filter f W (j + v.length) hjv
      have hsh : ∀ z, ((W.filter f).take (j + v.length)).count z
          = ((W.filter f).take j).count z + v.count z := by
        intro z
        have h := count_take_pow_shift (q + q) v z (by rw [← hvW, hPW]; exact hjv)
        rw [← hvW, hPW] at h; exact h
      have cf : ∀ (u : List α) (z : α), (z = x ∨ z = y) → (u.filter f).count z = u.count z := by
        intro u z hz; simp [hfdef, count_filter, hz]
      refine ⟨t', ?_, ?_⟩
      · have h := hsh x
        rw [he, hpre, cf _ x (Or.inl rfl), cf _ x (Or.inl rfl), hvx] at h
        exact h
      · have h := hsh y
        rw [he, hpre, cf _ y (Or.inr rfl), cf _ y (Or.inr rfl), hvy] at h
        exact h
  -- period `B`
  have hper : ∀ i (h : i + B < w.length), w[i + B] = w[i]'(by omega) := by
    intro i h
    have hi : i < w.length := by omega
    have hz : w[i] ∈ A := hA _ (getElem_mem hi)
    have e1 := shift (i + 1) (by omega) _ hz
    have e0 := shift i (by omega) _ hz
    have hiW : i < W.length := by omega
    have hiBW : i + B < W.length := by omega
    have s1 := count_take_succ W w[i] hiW
    have s2 := count_take_succ W w[i] hiBW
    have gW : W[i] = w[i] := by simp only [W]; exact getElem_append_left hi
    have gWB : W[i + B] = w[i + B] := by simp only [W]; exact getElem_append_left h
    rw [show i + 1 + B = i + B + 1 by omega] at e1
    rw [s2, s1, gW, gWB, e0] at e1
    by_contra hne
    simp [hne] at e1
  exact ⟨w.take B, pow_of_periodic B q w hL hper⟩

/-- **Lemma.** In a precarious word, a prime `q` divides the repeat counts of at most two colours. -/
theorem prime_dvd_at_most_two (w : List α) (hw : IsPrecarious w) (r : α → ℕ)
    (hr : ∀ c ∈ w, IsPow (del c w) (r c)) (q : ℕ) (hq : q.Prime) :
    ((w.toFinset).filter (fun c => q ∣ r c)).card ≤ 2 := by
  by_contra hcard
  push Not at hcard
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hcard
  simp only [Finset.mem_filter, mem_toFinset] at ha hb hc
  -- every pair of colours misses one of `a, b, c`
  have third : ∀ x y : α, ∃ u, (u = a ∨ u = b ∨ u = c) ∧ u ≠ x ∧ u ≠ y := by
    intro x y
    by_cases h1 : a ≠ x ∧ a ≠ y
    · exact ⟨a, Or.inl rfl, h1⟩
    by_cases h2 : b ≠ x ∧ b ≠ y
    · exact ⟨b, Or.inr (Or.inl rfl), h2⟩
    refine ⟨c, Or.inr (Or.inr rfl), ?_⟩
    push Not at h1 h2
    constructor <;> intro h <;> subst h <;> grind
  have hpow : IsPow w q := by
    apply pow_of_pairs w q hq.one_lt.le hw.2.1
    intro x _ y _ _
    obtain ⟨u, hu, hux, huy⟩ := third x y
    have huw : u ∈ w ∧ q ∣ r u := by rcases hu with rfl | rfl | rfl <;> assumption
    obtain ⟨U, hU⟩ := hr u huw.1
    obtain ⟨m, hm⟩ := huw.2
    have hsame : pair x y (del u w) = pair x y w := by
      simp only [pair, del, filter_filter]
      apply filter_congr
      intro z _
      by_cases hz : z = x ∨ z = y
      · have : z ≠ u := by rcases hz with rfl | rfl <;> [exact Ne.symm hux; exact Ne.symm huy]
        simp [hz, this]
      · simp [hz]
    refine ⟨((replicate m U).flatten).filter (fun z => z = x ∨ z = y), ?_⟩
    rw [← hsame, pair, hU, hm, flatten_replicate_mul, filter_flatten_replicate]
  exact hw.1 ⟨q, hq.two_le, hpow⟩

end Precarious
