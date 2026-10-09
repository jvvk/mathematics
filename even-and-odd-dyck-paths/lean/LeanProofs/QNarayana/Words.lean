import Mathlib

/-!
# MO 501839, Steps 1-2: two-coloured Motzkin words and the sign-reversing involution

A word over `{u, d, a, b}` (up, down, two level letters). Letter `x` at position `p` (from 1) has sign
`(-1)^p` if it is `u` or `d`, and `1` otherwise. The weight `wt2` counts `u` and `d` once and `b` twice.

The involution acts on blocks of two letters (positions `2i-1, 2i`). Each block has at most one partner:
a block with exactly one level letter is partnered with its swap, `ud` with `ba`, and `du` with `ab` when the
height before the block is at least 1. The involution replaces the first block that has a partner. Unpartnered
blocks are `uu, dd, aa, bb` and `ab` at height 0; those words are the fixed points, all of sign `+1`.
-/

namespace QNarayana

inductive L | u | d | a | b
  deriving DecidableEq, Repr

open L

def allL : Finset L := {u, d, a, b}

lemma mem_allL (x : L) : x ∈ allL := by cases x <;> simp [allL]

def Δ : L → ℤ
  | u => 1
  | d => -1
  | _ => 0

def lv : L → Bool
  | a => true
  | b => true
  | _ => false

def w2 : L → ℕ
  | u => 1
  | d => 1
  | a => 0
  | b => 2

def sw : L → L
  | u => d
  | d => u
  | x => x

/-- The mirror image: read backwards, exchanging up and down. -/
def mirror (w : List L) : List L := (w.map sw).reverse

/-- The path from height `h` stays at height `≥ 0` and ends at height `e`. -/
def okTo : ℤ → ℤ → List L → Bool
  | h, e, [] => h == e
  | h, e, x :: w => decide (0 ≤ h + Δ x) && okTo (h + Δ x) e w

def sgnFrom : ℕ → List L → ℤ
  | _, [] => 1
  | p, x :: w => (if lv x then 1 else (-1) ^ p) * sgnFrom (p + 1) w

def wt2 : List L → ℕ
  | [] => 0
  | x :: w => w2 x + wt2 w

def words : ℕ → Finset (List L)
  | 0 => {[]}
  | m + 1 => allL.biUnion (fun x => (words m).image (x :: ·))

lemma mem_words {m : ℕ} {w : List L} : w ∈ words m ↔ w.length = m := by
  induction m generalizing w with
  | zero => cases w <;> simp [words]
  | succ m ih =>
    cases w with
    | nil => simp [words]
    | cons x w => simp [words, ih, mem_allL]

/-- Motzkin words of length `m` and weight `j`. -/
def Mot (m j : ℕ) : Finset (List L) := (words m).filter (fun w => okTo 0 0 w = true ∧ wt2 w = j)

/-! ### Basic lemmas -/

lemma sgnFrom_add_two : ∀ (w : List L) (p : ℕ), sgnFrom (p + 2) w = sgnFrom p w
  | [], _ => rfl
  | x :: w, p => by
    have := sgnFrom_add_two w (p + 1)
    simp only [sgnFrom, show p + 1 + 2 = p + 2 + 1 by omega] at this ⊢
    rw [this, pow_add, neg_one_sq, mul_one]

lemma sgnFrom_block (p : ℕ) (x y : L) (w : List L) :
    sgnFrom p (x :: y :: w) =
      (if lv x then 1 else (-1) ^ p) * (if lv y then 1 else (-1) ^ (p + 1)) * sgnFrom p w := by
  simp only [sgnFrom, show p + 1 + 1 = p + 2 by omega, sgnFrom_add_two]; ring

lemma okTo_block (h e : ℤ) (x y : L) (w : List L) :
    okTo h e (x :: y :: w) =
      (decide (0 ≤ h + Δ x) && decide (0 ≤ h + Δ x + Δ y) && okTo (h + Δ x + Δ y) e w) := by
  simp [okTo, Bool.and_assoc]


/-! ### The involution -/

/-- The partner of a block at height `h`, if it has one. -/
def partner (h : ℤ) : L → L → Option (L × L)
  | u, a => some (a, u)
  | a, u => some (u, a)
  | u, b => some (b, u)
  | b, u => some (u, b)
  | d, a => some (a, d)
  | a, d => some (d, a)
  | d, b => some (b, d)
  | b, d => some (d, b)
  | u, d => some (b, a)
  | b, a => some (u, d)
  | d, u => if 1 ≤ h then some (a, b) else none
  | a, b => if 1 ≤ h then some (d, u) else none
  | _, _ => none

/-- Replace the first block that has a partner. -/
def ι : ℤ → List L → List L
  | _, [] => []
  | _, [x] => [x]
  | h, x :: y :: w =>
    match partner h x y with
    | some q => q.1 :: q.2 :: w
    | none => x :: y :: ι (h + Δ x + Δ y) w

/-- Sign of a block at positions `p, p + 1`. -/
def bsg (p : ℕ) (x y : L) : ℤ := (if lv x then 1 else (-1) ^ p) * (if lv y then 1 else (-1) ^ (p + 1))

lemma sgnFrom_cons_cons (p : ℕ) (x y : L) (w : List L) : sgnFrom p (x :: y :: w) = bsg p x y * sgnFrom p w :=
  sgnFrom_block p x y w

lemma neg_one_pow_mul_succ (p : ℕ) : (-1 : ℤ) ^ p * (-1) ^ (p + 1) = -1 := by
  rw [← pow_add]; exact Odd.neg_one_pow ⟨p, by ring⟩

/-- A partner has the same weight and height change, is legal where the block is, has the opposite sign, and
has the block as its own partner. -/
lemma partner_facts {h : ℤ} {x y x' y' : L} (hs : partner h x y = some (x', y')) :
    partner h x' y' = some (x, y) ∧ w2 x' + w2 y' = w2 x + w2 y ∧ Δ x' + Δ y' = Δ x + Δ y ∧
      (0 ≤ h → 0 ≤ h + Δ x → 0 ≤ h + Δ x + Δ y → 0 ≤ h + Δ x' ∧ 0 ≤ h + Δ x' + Δ y') ∧
      ∀ p, bsg p x' y' = - bsg p x y := by
  have key : ∀ p, bsg p x' y' = - bsg p x y := by
    intro p
    have hss : (-1 : ℤ) ^ p * (-1) ^ p = 1 := by rw [← mul_pow]; simp
    revert hs
    cases x <;> cases y <;> by_cases hh : 1 ≤ h <;> simp [partner, hh] <;> rintro rfl rfl <;>
      simp [bsg, lv, pow_succ] <;> linarith
  refine ⟨?_, ?_, ?_, ?_, key⟩ <;> revert hs <;>
    cases x <;> cases y <;> by_cases hh : 1 ≤ h <;> simp [partner, hh] <;> rintro rfl rfl <;>
    simp [partner, hh, w2, Δ] <;> omega

lemma partner_ne {h : ℤ} {x y : L} : partner h x y ≠ some (x, y) := by
  cases x <;> cases y <;> by_cases hh : 1 ≤ h <;> simp [partner, hh]

theorem ι_ι : ∀ (h : ℤ) (w : List L), ι h (ι h w) = w
  | _, [] => rfl
  | _, [_] => rfl
  | h, x :: y :: w => by
    rcases hs : partner h x y with _ | ⟨x', y'⟩
    · simp [ι, hs, ι_ι _ w]
    · simp [ι, hs, (partner_facts hs).1]

theorem length_ι : ∀ (h : ℤ) (w : List L), (ι h w).length = w.length
  | _, [] => rfl
  | _, [_] => rfl
  | h, x :: y :: w => by
    rcases hs : partner h x y with _ | ⟨x', y'⟩
    · simp [ι, hs, length_ι _ w]
    · simp [ι, hs]

theorem wt2_ι : ∀ (h : ℤ) (w : List L), wt2 (ι h w) = wt2 w
  | _, [] => rfl
  | _, [_] => rfl
  | h, x :: y :: w => by
    rcases hs : partner h x y with _ | ⟨x', y'⟩
    · simp [ι, hs, wt2, wt2_ι _ w]
    · have := (partner_facts hs).2.1
      simp only [ι, hs, wt2]; omega

theorem okTo_ι : ∀ (h : ℤ) (w : List L) (e : ℤ), 0 ≤ h → okTo h e w = true → okTo h e (ι h w) = true
  | _, [], _, _, hw => hw
  | _, [_], _, _, hw => hw
  | h, x :: y :: w, e, h0, hw => by
    rw [okTo_block] at hw
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hw
    rcases hs : partner h x y with _ | ⟨x', y'⟩
    · simp only [ι, hs]
      rw [okTo_block]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hw.1.1, hw.1.2⟩, okTo_ι _ w e hw.1.2 hw.2⟩
    · obtain ⟨-, -, hΔ, hpos, -⟩ := partner_facts hs
      simp only [ι, hs]
      rw [okTo_block]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      obtain ⟨p1, p2⟩ := hpos h0 hw.1.1 hw.1.2
      refine ⟨⟨p1, p2⟩, ?_⟩
      rw [add_assoc, hΔ, ← add_assoc]; exact hw.2

theorem sgn_ι : ∀ (h : ℤ) (w : List L) (p : ℕ), ι h w ≠ w → sgnFrom p (ι h w) = - sgnFrom p w
  | _, [], _, hne => absurd rfl hne
  | _, [_], _, hne => absurd rfl hne
  | h, x :: y :: w, p, hne => by
    rcases hs : partner h x y with _ | ⟨x', y'⟩
    · simp only [ι, hs] at hne ⊢
      have hw : ι (h + Δ x + Δ y) w ≠ w := fun e => hne (by rw [e])
      rw [sgnFrom_cons_cons, sgnFrom_cons_cons, sgn_ι _ w p hw]; ring
    · simp only [ι, hs]
      rw [sgnFrom_cons_cons, sgnFrom_cons_cons, (partner_facts hs).2.2.2.2 p]; ring

theorem ι_mem {m j : ℕ} {w : List L} (hw : w ∈ Mot m j) : ι 0 w ∈ Mot m j := by
  simp only [Mot, Finset.mem_filter, mem_words] at hw ⊢
  obtain ⟨hl, hok, hwt⟩ := hw
  exact ⟨by rw [length_ι, hl], okTo_ι 0 w 0 le_rfl hok, by rw [wt2_ι, hwt]⟩

/-! ### Fixed points -/

/-- Blocks without a partner (in a legal word). -/
def blockOK (h : ℤ) : L → L → Bool
  | u, u => decide (0 ≤ h)
  | d, d => decide (2 ≤ h)
  | a, a => decide (0 ≤ h)
  | b, b => decide (0 ≤ h)
  | a, b => h == 0
  | _, _ => false

/-- Shape of the fixed points: unpartnered blocks, then possibly one level letter, ending at height 0. -/
def F : ℤ → List L → Bool
  | h, [] => h == 0
  | h, [x] => lv x && h == 0
  | h, x :: y :: w => blockOK h x y && F (h + Δ x + Δ y) w

theorem fix_to_F : ∀ (w : List L) (h : ℤ) (t : ℕ), h = 2 * t → ι h w = w → okTo h 0 w = true → F h w = true
  | [], h, t, ht, _, hok => by simpa [okTo, F] using hok
  | [x], h, t, ht, _, hok => by
    simp only [okTo, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    have hd : Δ x = -1 ∨ Δ x = 0 ∨ Δ x = 1 := by cases x <;> simp [Δ]
    have : Δ x = 0 ∧ h = 0 := by omega
    cases x <;> simp_all [F, lv, Δ]
  | x :: y :: w, h, t, ht, h1, hok => by
    rw [okTo_block] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hp1, hp2⟩, hrest⟩ := hok
    rcases hs : partner h x y with _ | ⟨x', y'⟩
    · simp only [ι, hs, List.cons.injEq, true_and] at h1
      have IH : ∀ t' : ℕ, h + Δ x + Δ y = 2 * t' → F (h + Δ x + Δ y) w = true :=
        fun t' ht' => fix_to_F w _ t' ht' h1 hrest
      simp only [F, Bool.and_eq_true]
      cases x <;> cases y <;> simp [partner, Δ, blockOK] at hs hp1 hp2 IH ⊢
      all_goals first
        | omega
        | exact ⟨by omega, IH (t + 1) (by omega)⟩
        | exact ⟨by omega, IH (t - 1) (by omega)⟩
        | exact ⟨by omega, IH t (by omega)⟩
    · simp only [ι, hs, List.cons.injEq] at h1
      obtain ⟨rfl, rfl, -⟩ := h1
      exact absurd hs partner_ne

theorem F_to_fix : ∀ (w : List L) (h : ℤ), F h w = true → ι h w = w ∧ okTo h 0 w = true ∧ 0 ≤ h
  | [], h, hF => by simp_all [F, okTo, ι]
  | [x], h, hF => by
    simp only [F, Bool.and_eq_true, beq_iff_eq] at hF
    obtain ⟨hl, rfl⟩ := hF
    cases x <;> simp_all [lv, ι, okTo, Δ]
  | x :: y :: w, h, hF => by
    simp only [F, Bool.and_eq_true] at hF
    obtain ⟨hb, hw⟩ := hF
    obtain ⟨i1, iok, ih0⟩ := F_to_fix w _ hw
    cases x <;> cases y <;> simp [blockOK] at hb <;>
      simp_all [ι, partner, okTo_block, Δ] <;> first | omega | exact decide_eq_true (by omega)

theorem sgn_F : ∀ (w : List L) (h : ℤ) (t : ℕ) (p : ℕ), h = 2 * t → F h w = true → sgnFrom p w = (-1) ^ t
  | [], h, t, _, ht, hF => by
    simp only [F, beq_iff_eq] at hF
    have : t = 0 := by omega
    subst this; simp [sgnFrom]
  | [x], h, t, p, ht, hF => by
    simp only [F, Bool.and_eq_true, beq_iff_eq] at hF
    have : t = 0 := by omega
    subst this
    cases x <;> simp_all [lv, sgnFrom]
  | x :: y :: w, h, t, p, ht, hF => by
    simp only [F, Bool.and_eq_true] at hF
    obtain ⟨hb, hw⟩ := hF
    rw [sgnFrom_cons_cons]
    have IH : ∀ t' : ℕ, h + Δ x + Δ y = 2 * t' → sgnFrom p w = (-1) ^ t' :=
      fun t' ht' => sgn_F w _ t' p ht' hw
    cases x <;> cases y <;> simp [blockOK] at hb <;> simp only [Δ] at IH <;>
      simp only [bsg, lv, Bool.false_eq_true, ite_false, ite_true]
    all_goals first
      | (rw [neg_one_pow_mul_succ, IH (t + 1) (by omega), pow_succ]; ring)
      | (obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
         rw [neg_one_pow_mul_succ, IH s (by omega), pow_succ]; ring)
      | (rw [IH t (by omega)]; ring)

/-! ### Step 2: the signed sum is the number of fixed points -/

def Fix (m j : ℕ) : Finset (List L) := (Mot m j).filter (fun w => ι 0 w = w)

theorem mem_Fix {m j : ℕ} {w : List L} : w ∈ Fix m j ↔ w.length = m ∧ F 0 w = true ∧ wt2 w = j := by
  simp only [Fix, Mot, Finset.mem_filter, mem_words]
  constructor
  · rintro ⟨⟨hl, hok, hwt⟩, hfix⟩
    exact ⟨hl, fix_to_F w 0 0 rfl hfix hok, hwt⟩
  · rintro ⟨hl, hF, hwt⟩
    obtain ⟨hfix, hok, -⟩ := F_to_fix w 0 hF
    exact ⟨⟨hl, hok, hwt⟩, hfix⟩

theorem signed_sum_eq_card_fix (m j : ℕ) : ∑ w ∈ Mot m j, sgnFrom 1 w = (Fix m j).card := by
  rw [← Finset.sum_filter_add_sum_filter_not (Mot m j) (fun w => ι 0 w = w)]
  have h0 : ∑ w ∈ (Mot m j).filter (fun w => ¬ ι 0 w = w), sgnFrom 1 w = 0 := by
    refine Finset.sum_involution (fun w _ => ι 0 w) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter] at hw
      rw [sgn_ι 0 w 1 hw.2]; ring
    · intro w hw _
      exact (Finset.mem_filter.1 hw).2
    · intro w hw
      simp only [Finset.mem_filter] at hw ⊢
      exact ⟨ι_mem hw.1, by rw [ι_ι]; exact fun e => hw.2 e.symm⟩
    · intro w _; exact ι_ι 0 w
  have h1 : ∑ w ∈ Fix m j, sgnFrom 1 w = ((Fix m j).card : ℤ) := by
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    rw [sgn_F w 0 0 1 rfl (mem_Fix.1 hw).2.1]; simp
  rw [h0, add_zero]; exact h1

end QNarayana
