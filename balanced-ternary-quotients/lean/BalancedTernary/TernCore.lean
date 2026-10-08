/-
  Shared core for the balanced-ternary quotient families (Guy F31, Selfridge–Lacampagne).

  B = positive integers whose balanced-ternary digits are all nonzero.  `ZF m` says m has a
  balanced-ternary representation with every digit ±1 (m may be negative).

  `not_BB_of_inv`: if a set S of carries contains 0, is closed under the carry map of
  "multiply by n", stays above 2 - n, and no move with digit d = +1 lands on a positive
  zero-free carry, then n ∉ B/B.

  `not_BB_of_cert`: the same for a concrete finite carry list, checked by a Boolean function
  whose soundness is proved here, so a concrete instance is closed by `decide`.

  Core Lean only.
-/

namespace Tern

inductive ZF : Int → Prop
  | one : ZF 1
  | negOne : ZF (-1)
  | step {q c : Int} : ZF q → (c = 1 ∨ c = -1) → ZF (3 * q + c)

theorem ZF.mod3 {m : Int} (h : ZF m) : m % 3 ≠ 0 := by
  cases h with
  | one => decide
  | negOne => decide
  | step _ hc => rcases hc with rfl | rfl <;> omega

theorem ZF.ne_zero {m : Int} (h : ZF m) : m ≠ 0 := by
  have := h.mod3; omega

theorem ZF.peel {M q c : Int} (h : ZF M) (hM : M = 3 * q + c) (hc : c = 1 ∨ c = -1) :
    q = 0 ∨ ZF q := by
  cases h with
  | one => left; omega
  | negOne => left; omega
  | @step q' c' hq' hc' =>
    right
    have : q = q' := by rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl <;> omega
    subst this; exact hq'

theorem ZF.peel_auto {M : Int} (h : ZF M) :
    ∃ q c, (c = 1 ∨ c = -1) ∧ M = 3 * q + c ∧ (q = 0 ∨ ZF q) := by
  cases h with
  | one => exact ⟨0, 1, .inl rfl, by decide, .inl rfl⟩
  | negOne => exact ⟨0, -1, .inr rfl, by decide, .inl rfl⟩
  | @step q c hq hc => exact ⟨q, c, hc, rfl, .inr hq⟩

/-- One peeling step with the digit named explicitly. -/
theorem ZF.down {M : Int} (q c : Int) (h : ZF M) (hM : M = 3 * q + c) (hc : c = 1 ∨ c = -1)
    (hq : q ≠ 0) : ZF q := by
  rcases h.peel hM hc with h0 | h1
  · exact absurd h0 hq
  · exact h1

theorem pow3_pos (i : Nat) : (0 : Int) < 3 ^ i := Int.pow_pos (by decide)

/-- Powers of three as omega atoms: 3^x = 3 · 3^y when x = y + 1. -/
theorem p3 (x y : Nat) (h : x = y + 1) : (3 : Int) ^ x = 3 * 3 ^ y := by
  subst h; rw [Int.pow_succ, Int.mul_comm]

theorem pow3_mono (x y : Nat) (h : x ≤ y) : (3 : Int) ^ x ≤ 3 ^ y := by
  induction y with
  | zero => rw [Nat.le_zero.mp h]; exact Int.le_refl _
  | succ y ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | hl
    · exact Int.le_refl _
    · have := ih (by omega); rw [p3 (y + 1) y rfl]; have := pow3_pos y; omega

/-- 3^t · 3^x ≤ 3^y when x + t ≤ y, with 3^t given as a numeral c. -/
theorem pow3_le_mul (x y t : Nat) (c : Int) (hc : (3 : Int) ^ t = c) (h : x + t ≤ y) :
    c * 3 ^ x ≤ 3 ^ y := by
  rw [← hc, ← Int.pow_add, Nat.add_comm]; exact pow3_mono _ _ h

/-- 3^t ≤ 3^y when t ≤ y, with 3^t given as a numeral c. -/
theorem pow3_ge (y t : Nat) (c : Int) (hc : (3 : Int) ^ t = c) (h : t ≤ y) : c ≤ 3 ^ y := by
  rw [← hc]; exact pow3_mono _ _ h

/-- 3^x ≤ 3^s · 3^y when x ≤ y + s, with 3^s given as a numeral c. -/
theorem pow3_le_shift (x y s : Nat) (c : Int) (hc : (3 : Int) ^ s = c) (h : x ≤ y + s) :
    (3 : Int) ^ x ≤ c * 3 ^ y := by
  rw [← hc, ← Int.pow_add, Nat.add_comm]; exact pow3_mono _ _ (by omega)

theorem mul_ge_self {n q : Int} (hn : 0 ≤ n) (hq : 1 ≤ q) : n ≤ n * q := by
  have : n * q = n + n * (q - 1) := by
    rw [Int.mul_sub, Int.mul_one]; omega
  have : 0 ≤ n * (q - 1) := Int.mul_nonneg hn (by omega)
  omega

/-! ### The invariant theorem -/

theorem not_BB_of_inv (n : Int) (S : Int → Prop) (h0 : S 0)
    (hstep : ∀ r r' d c, S r → (d = 1 ∨ d = -1) → (c = 1 ∨ c = -1) →
      r + n * d = 3 * r' + c → S r')
    (hbound : ∀ r, S r → 2 - n ≤ r)
    (hacc : ∀ r r' c, S r → (c = 1 ∨ c = -1) → r + n = 3 * r' + c → 0 < r' → ¬ ZF r') :
    ¬ ∃ m N : Int, 0 < m ∧ ZF m ∧ 0 < N ∧ ZF N ∧ N = n * m := by
  have hn : 2 ≤ n := by have := hbound 0 h0; omega
  have key : ∀ m : Int, ZF m → 0 < m → ∀ r, S r → ¬ ZF (n * m + r) := by
    intro m hm
    induction hm with
    | one =>
      intro _ r hr h
      rw [Int.mul_one] at h
      obtain ⟨Q, c, hc, hQ, hQz⟩ := h.peel_auto
      have hb := hbound r hr
      have hQpos : 0 < Q := by rcases hc with rfl | rfl <;> omega
      rcases hQz with h0 | hZ
      · omega
      · exact hacc r Q c hr hc (by omega) hQpos hZ
    | negOne => intro h; omega
    | @step q c hq hc ih =>
      intro hpos r hr h
      have hq0 := hq.ne_zero
      have hqpos : 0 < q := by rcases hc with rfl | rfl <;> omega
      have hexp : n * (3 * q + c) + r = 3 * (n * q) + (n * c + r) := by
        rw [Int.mul_add, Int.mul_left_comm]; omega
      rw [hexp] at h
      obtain ⟨Q, c', hc', hQ, hQz⟩ := h.peel_auto
      have hS : S (Q - n * q) := hstep r _ c c' hr hc hc' (by omega)
      have hb := hbound _ hS
      have hnq := mul_ge_self (n := n) (q := q) (by omega) (by omega)
      rcases hQz with h0 | hZ
      · omega
      · apply ih hqpos (Q - n * q) hS
        rw [show n * q + (Q - n * q) = Q by omega]
        exact hZ
  rintro ⟨m, N, hm, hZm, _, hZN, rfl⟩
  exact key m hZm hm 0 h0 (by rw [Int.add_zero]; exact hZN)

/-! ### Concrete certificates checked by evaluation -/

/-- Balanced residue of v modulo 3. -/
def bal (v : Int) : Int := if v % 3 = 1 then 1 else if v % 3 = 2 then -1 else 0

theorem bal_eq {v r c : Int} (hv : v = 3 * r + c) (hc : c = 1 ∨ c = -1) : bal v = c := by
  unfold bal; rcases hc with rfl | rfl <;> split <;> (try split) <;> omega

/-- Decides zero-freeness with fuel. -/
def zfb : Nat → Int → Bool
  | 0, _ => false
  | f + 1, m => if m = 1 ∨ m = -1 then true else if m % 3 = 0 then false else zfb f ((m - bal m) / 3)

theorem zfb_of_ZF {m : Int} (h : ZF m) : ∀ f : Nat, m.natAbs ≤ f → zfb f m = true := by
  induction h with
  | one => intro f hf; cases f with
    | zero => simp at hf
    | succ f => simp [zfb]
  | negOne => intro f hf; cases f with
    | zero => simp at hf
    | succ f => simp [zfb]
  | @step q c hq hc ih =>
    intro f hf
    have hq0 := hq.ne_zero
    cases f with
    | zero => rcases hc with rfl | rfl <;> omega
    | succ f =>
      have hb : bal (3 * q + c) = c := bal_eq rfl hc
      have hne : ¬ (3 * q + c = 1 ∨ 3 * q + c = -1) := by rcases hc with rfl | rfl <;> omega
      have hm3 : ¬ (3 * q + c) % 3 = 0 := by rcases hc with rfl | rfl <;> omega
      simp only [zfb, hne, hm3, ite_false, hb]
      rw [show (3 * q + c - c) / 3 = q by omega]
      exact ih f (by rcases hc with rfl | rfl <;> omega)

theorem not_ZF_of_zfb {m : Int} (h : zfb m.natAbs m = false) : ¬ ZF m := by
  intro hz; have := zfb_of_ZF hz m.natAbs (Nat.le_refl _); rw [this] at h; exact Bool.noConfusion h

/-- The move from carry r with multiplier digit d, or `none` if the product digit is 0. -/
def move (n r d : Int) : Option Int :=
  let v := r + n * d
  if bal v = 0 then none else some ((v - bal v) / 3)

def okMove (n : Int) (L : List Int) (r d : Int) : Bool :=
  match move n r d with
  | none => true
  | some r' => L.contains r' && (d == -1 || decide (r' ≤ 0) || !zfb r'.natAbs r')

def certB (n : Int) (L : List Int) : Bool :=
  L.contains 0 && L.all (fun r => decide (2 - n ≤ r) && okMove n L r 1 && okMove n L r (-1))

theorem move_eq {n r r' d c : Int} (hc : c = 1 ∨ c = -1) (hv : r + n * d = 3 * r' + c) :
    move n r d = some r' := by
  have hb := bal_eq hv hc
  unfold move
  simp only [hb]
  rw [if_neg (show ¬ c = 0 by rcases hc with rfl | rfl <;> decide)]
  congr 1; omega

theorem not_BB_of_cert (n : Int) (L : List Int) (h : certB n L = true) :
    ¬ ∃ m N : Int, 0 < m ∧ ZF m ∧ 0 < N ∧ ZF N ∧ N = n * m := by
  simp only [certB, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h0, hall⟩ := h
  have hok : ∀ r ∈ L, ∀ d, (d = 1 ∨ d = -1) → okMove n L r d = true := by
    intro r hr d hd
    have := hall r hr
    rcases hd with rfl | rfl
    · exact this.1.2
    · exact this.2
  apply not_BB_of_inv n (fun r => r ∈ L)
  · simpa using h0
  · intro r r' d c hr hd hc hv
    have := hok r hr d hd
    simp only [okMove, move_eq hc hv, Bool.and_eq_true] at this
    simpa using this.1
  · intro r hr; exact of_decide_eq_true (hall r hr).1.1
  · intro r r' c hr hc hv hpos
    have := hok r hr 1 (.inl rfl)
    have hm : move n r 1 = some r' := move_eq (n := n) (r := r) (r' := r') (d := 1) hc (by omega)
    simp only [okMove, hm, Bool.and_eq_true] at this
    have h2 := this.2
    have hne : decide (r' ≤ 0) = false := by simp; omega
    simp only [hne, Bool.or_false] at h2
    have h3 : zfb r'.natAbs r' = false := by simpa using h2
    exact not_ZF_of_zfb h3

end Tern
