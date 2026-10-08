/-
  Infinitely many exceptions to the Selfridge–Lacampagne conjecture.

  B = positive integers whose balanced-ternary digits are all nonzero.
  Theorem: for every k ≥ 5 and every m ∈ B, (4·3^k + 5)·m ∉ B.
  Hence 4·3^k + 5 ∉ B/B for all k ≥ 5.

  Plain Lean 4 (core only); every arithmetic step is discharged by `omega`
  with the powers 3^k, 3^i treated as atoms tied by explicit equations.
-/

/-- `ZF m`: m has a balanced-ternary representation with every digit in {1, -1}
    (m may be negative). B = {m | 0 < m ∧ ZF m}. -/
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

/-- Peeling the lowest digit: the digit is forced by m mod 3, and the rest is 0 or zero-free. -/
theorem ZF.peel {M q c : Int} (h : ZF M) (hM : M = 3 * q + c) (hc : c = 1 ∨ c = -1) :
    q = 0 ∨ ZF q := by
  cases h with
  | one => left; omega
  | negOne => left; omega
  | @step q' c' hq' hc' =>
    right
    have : q = q' := by rcases hc with rfl | rfl <;> rcases hc' with rfl | rfl <;> omega
    subst this; exact hq'

/-- A positive zero-free number is 1, or 3q + c with q positive and zero-free. -/
theorem ZF.pos_cases {m : Int} (h : ZF m) (hm : 0 < m) :
    m = 1 ∨ ∃ q c, ZF q ∧ 0 < q ∧ (c = 1 ∨ c = -1) ∧ m = 3 * q + c := by
  cases h with
  | one => left; rfl
  | negOne => omega
  | @step q c hq hc =>
    right; refine ⟨q, c, hq, ?_, hc, rfl⟩
    have := hq.ne_zero; rcases hc with rfl | rfl <;> omega

/-- The carry set S_k, with c = 2·3^k + 2 = (n - 1)/2 and n = 4·3^k + 5. -/
inductive InS (k : Nat) : Int → Prop
  | zero : InS k 0
  | cpos : InS k (2 * 3 ^ k + 2)
  | cneg : InS k (-(2 * 3 ^ k + 2))
  | t2pos (i : Nat) : i < k → InS k (2 * 3 ^ k + 2 - 2 * 3 ^ i)
  | t2neg (i : Nat) : i < k → InS k (-(2 * 3 ^ k + 2 - 2 * 3 ^ i))
  | t4pos (i : Nat) : i < k → InS k (2 * 3 ^ k + 2 - 4 * 3 ^ i)
  | t4neg (i : Nat) : i < k → InS k (-(2 * 3 ^ k + 2 - 4 * 3 ^ i))

theorem pow3_pos (i : Nat) : (0 : Int) < 3 ^ i := Int.pow_pos (by decide)

theorem pow3_succ (i : Nat) : (3 : Int) ^ (i + 1) = 3 * 3 ^ i := by
  rw [Int.pow_succ, Int.mul_comm]

theorem pow3_mono (i t : Nat) : (3 : Int) ^ i ≤ 3 ^ (i + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show i + (t + 1) = (i + t) + 1 by omega, pow3_succ]
    have := pow3_pos (i + t); omega

theorem pow3_le {i k : Nat} (h : i < k) : (3 : Int) ^ i ≤ 3 ^ (k - 1) := by
  have := pow3_mono i (k - 1 - i)
  rwa [show i + (k - 1 - i) = k - 1 by omega] at this

theorem pow3_top {k : Nat} (hk : 1 ≤ k) : (3 : Int) ^ k = 3 * 3 ^ (k - 1) := by
  have : k = (k - 1) + 1 := by omega
  rw [this, pow3_succ]; simp

/-- Every element of S_k lies strictly between -n and n (in fact |r| ≤ c). -/
theorem InS.bound {k : Nat} (hk5 : 1 ≤ k) {r : Int} (h : InS k r) : -(2 * 3 ^ k + 2) ≤ r := by
  have hk := pow3_pos k
  cases h with
  | zero => omega
  | cpos => omega
  | cneg => omega
  | t2pos i hi => have := pow3_le hi; have := pow3_pos i; have := pow3_top (k := k) (by omega); omega
  | t2neg i hi => have := pow3_pos i; omega
  | t4pos i hi =>
      have := pow3_le hi; have := pow3_pos i; have := pow3_top (k := k) hk5; omega
  | t4neg i hi => have := pow3_pos i; omega

/-- Closure of S_k under one carry step: from carry r and digit d = ±1 of m, if the product
    digit c = ±1 satisfies r + n·d = 3·r' + c, then r' ∈ S_k.  (If r + n·d ≡ 0 mod 3 the
    product digit would be 0, which is excluded separately.) -/
theorem InS.step {k : Nat} (hk : 5 ≤ k) {r r' d c : Int} (hr : InS k r)
    (hd : d = 1 ∨ d = -1) (hc : c = 1 ∨ c = -1)
    (hv : r + (4 * 3 ^ k + 5) * d = 3 * r' + c) : InS k r' := by
  have hkx : (3 : Int) ^ k = 3 * 3 ^ (k - 1) := by
    have : k = (k - 1) + 1 := by omega
    rw [this, pow3_succ]; simp
  have hk1 : k - 1 < k := by omega
  rcases hd with rfl | rfl <;> rcases hc with rfl | rfl <;>
  cases hr with
  | zero => first
      | (have : r' = 2 * 3 ^ k + 2 - 2 * 3 ^ (k - 1) := by omega
         rw [this]; exact .t2pos _ hk1)
      | (have : r' = -(2 * 3 ^ k + 2 - 2 * 3 ^ (k - 1)) := by omega
         rw [this]; exact .t2neg _ hk1)
      | omega
  | cpos => first
      | (have : r' = 2 * 3 ^ k + 2 := by omega
         rw [this]; exact .cpos)
      | omega
  | cneg => first
      | (have : r' = -(2 * 3 ^ k + 2) := by omega
         rw [this]; exact .cneg)
      | omega
  | t2pos i hi =>
      cases i with
      | zero => first
          | (have : r' = 2 * 3 ^ k + 2 := by simp at hv; omega
             rw [this]; exact .cpos)
          | (have : r' = -(2 * 3 ^ k + 2 - 4 * 3 ^ (k - 1)) := by simp at hv; omega
             rw [this]; exact .t4neg _ hk1)
          | (simp at hv; omega)
      | succ j =>
          rw [pow3_succ] at hv
          first
          | (have : r' = 2 * 3 ^ k + 2 - 2 * 3 ^ j := by omega
             rw [this]; exact .t2pos _ (by omega))
          | omega
  | t2neg i hi =>
      cases i with
      | zero => first
          | (have : r' = 2 * 3 ^ k + 2 - 4 * 3 ^ (k - 1) := by simp at hv; omega
             rw [this]; exact .t4pos _ hk1)
          | (have : r' = -(2 * 3 ^ k + 2) := by simp at hv; omega
             rw [this]; exact .cneg)
          | (simp at hv; omega)
      | succ j =>
          rw [pow3_succ] at hv
          first
          | (have : r' = -(2 * 3 ^ k + 2 - 2 * 3 ^ j) := by omega
             rw [this]; exact .t2neg _ (by omega))
          | omega
  | t4pos i hi =>
      cases i with
      | zero => first
          | (have : r' = -(2 * 3 ^ k + 2 - 4 * 3 ^ (k - 1)) := by simp at hv; omega
             rw [this]; exact .t4neg _ hk1)
          | (simp at hv; omega)
      | succ j =>
          rw [pow3_succ] at hv
          first
          | (have : r' = 2 * 3 ^ k + 2 - 4 * 3 ^ j := by omega
             rw [this]; exact .t4pos _ (by omega))
          | omega
  | t4neg i hi =>
      cases i with
      | zero => first
          | (have : r' = 2 * 3 ^ k + 2 - 4 * 3 ^ (k - 1) := by simp at hv; omega
             rw [this]; exact .t4pos _ hk1)
          | (simp at hv; omega)
      | succ j =>
          rw [pow3_succ] at hv
          first
          | (have : r' = -(2 * 3 ^ k + 2 - 4 * 3 ^ j) := by omega
             rw [this]; exact .t4neg _ (by omega))
          | omega

/-! ### No positive carry in S_k is zero-free (the "zero digit" lemma) -/

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

/-- Powers of 3 below 3^k, as atoms: 3^k = 3^5 · 3^(k-5). -/
theorem pows (k : Nat) (hk : 5 ≤ k) :
    (3:Int)^k = 3 * 3^(k-1) ∧ (3:Int)^(k-1) = 3 * 3^(k-2) ∧ (3:Int)^(k-2) = 3 * 3^(k-3) ∧
    (3:Int)^(k-3) = 3 * 3^(k-4) ∧ (3:Int)^(k-4) = 3 * 3^(k-5) ∧ (0:Int) < 3^(k-5) := by
  refine ⟨pow3_top (by omega), ?_, ?_, ?_, ?_, pow3_pos _⟩
  · have := pow3_top (k := k - 1) (by omega); rwa [show k - 1 - 1 = k - 2 by omega] at this
  · have := pow3_top (k := k - 2) (by omega); rwa [show k - 2 - 1 = k - 3 by omega] at this
  · have := pow3_top (k := k - 3) (by omega); rwa [show k - 3 - 1 = k - 4 by omega] at this
  · have := pow3_top (k := k - 4) (by omega); rwa [show k - 4 - 1 = k - 5 by omega] at this

theorem nzf_c {k : Nat} (hk : 5 ≤ k) : ¬ ZF (2 * 3 ^ k + 2) := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pows k hk
  have a := ZF.down (2 * 3^(k-1) + 1) (-1) h (by omega) (by simp) (by omega)
  have b := ZF.down (2 * 3^(k-2)) 1 a (by omega) (by simp) (by omega)
  exact b.mod3 (by omega)

theorem nzf_t {k j : Nat} (hk : 5 ≤ k) (hj : j < k) (t : Int) (ht : t = 2 ∨ t = 4) :
    ¬ ZF (2 * 3 ^ k + 2 - t * 3 ^ j) := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pows k hk
  match j, hj, h with
  | 0, _, h =>
    simp at h
    rcases ht with rfl | rfl
    · exact h.mod3 (by omega)
    · have a := ZF.down (2 * 3^(k-1) - 1) 1 h (by omega) (by simp) (by omega)
      have b := ZF.down (2 * 3^(k-2)) (-1) a (by omega) (by simp) (by omega)
      exact b.mod3 (by omega)
  | 1, _, h =>
    simp at h
    rcases ht with rfl | rfl
    · have a := ZF.down (2 * 3^(k-1) - 1) (-1) h (by omega) (by simp) (by omega)
      have b := ZF.down (2 * 3^(k-2)) (-1) a (by omega) (by simp) (by omega)
      exact b.mod3 (by omega)
    · have a := ZF.down (2 * 3^(k-1) - 3) (-1) h (by omega) (by simp) (by omega)
      exact a.mod3 (by omega)
  | 2, _, h =>
    have e : (3:Int)^2 = 9 := by decide
    rw [e] at h
    rcases ht with rfl | rfl
    · have a := ZF.down (2 * 3^(k-1) - 5) (-1) h (by omega) (by simp) (by omega)
      have b := ZF.down (2 * 3^(k-2) - 2) 1 a (by omega) (by simp) (by omega)
      have c := ZF.down (2 * 3^(k-3) - 1) 1 b (by omega) (by simp) (by omega)
      have d := ZF.down (2 * 3^(k-4)) (-1) c (by omega) (by simp) (by omega)
      exact d.mod3 (by omega)
    · have a := ZF.down (2 * 3^(k-1) - 11) (-1) h (by omega) (by simp) (by omega)
      have b := ZF.down (2 * 3^(k-2) - 4) 1 a (by omega) (by simp) (by omega)
      have c := ZF.down (2 * 3^(k-3) - 1) (-1) b (by omega) (by simp) (by omega)
      have d := ZF.down (2 * 3^(k-4)) (-1) c (by omega) (by simp) (by omega)
      exact d.mod3 (by omega)
  | j + 3, hj, h =>
    have ej : (3:Int)^(j+3) = 27 * 3^j := by
      rw [pow3_succ, pow3_succ, pow3_succ]; omega
    have hle := pow3_le hj
    rw [ej] at h hle
    have a := ZF.down (2 * 3^(k-1) + 1 - 9 * t * 3^j) (-1) h (by rcases ht with rfl | rfl <;> omega)
      (by simp) (by rcases ht with rfl | rfl <;> omega)
    have b := ZF.down (2 * 3^(k-2) - 3 * t * 3^j) 1 a (by rcases ht with rfl | rfl <;> omega)
      (by simp) (by rcases ht with rfl | rfl <;> omega)
    exact b.mod3 (by rcases ht with rfl | rfl <;> omega)

/-- No positive element of S_k is zero-free. -/
theorem InS.not_zf {k : Nat} (hk : 5 ≤ k) {r : Int} (hr : InS k r) (hpos : 0 < r) : ¬ ZF r := by
  have := pow3_top (k := k) (by omega)
  cases hr with
  | zero => omega
  | cpos => exact nzf_c hk
  | cneg => have := pow3_pos k; omega
  | t2pos j hj => exact nzf_t hk hj 2 (.inl rfl)
  | t2neg j hj => have := pow3_le hj; have := pow3_pos k; omega
  | t4pos j hj => exact nzf_t hk hj 4 (.inr rfl)
  | t4neg j hj => have := pow3_le hj; have := pow3_pos j; omega

/-! ### Main theorem -/

theorem mul_ge_self {n q : Int} (hn : 0 ≤ n) (hq : 1 ≤ q) : n ≤ n * q := by
  have : n * q = n + n * (q - 1) := by
    rw [Int.mul_sub, Int.mul_one]; omega
  have : 0 ≤ n * (q - 1) := Int.mul_nonneg hn (by omega)
  omega

/-- For every zero-free m > 0 and carry r ∈ S_k, n·m + r is not zero-free. -/
theorem key {k : Nat} (hk : 5 ≤ k) :
    ∀ m : Int, ZF m → 0 < m → ∀ r, InS k r → ¬ ZF ((4 * 3 ^ k + 5) * m + r) := by
  intro m hm
  have h3 := pow3_top (k := k) (by omega)
  have hkpos := pow3_pos k
  induction hm with
  | one =>
    intro _ r hr h
    rw [Int.mul_one] at h
    obtain ⟨Q, c, hc, hQ, hQz⟩ := h.peel_auto
    have hS : InS k Q := InS.step hk hr (.inl rfl) hc (by rw [Int.mul_one]; omega)
    have hb := hr.bound (by omega)
    have hQpos : 0 < Q := by rcases hc with rfl | rfl <;> omega
    rcases hQz with h0 | hZ
    · omega
    · exact hS.not_zf hk hQpos hZ
  | negOne => intro h; omega
  | @step q c hq hc ih =>
    intro hpos r hr h
    have hq0 := hq.ne_zero
    have hqpos : 0 < q := by rcases hc with rfl | rfl <;> omega
    have hexp : (4 * 3 ^ k + 5) * (3 * q + c) + r = 3 * ((4 * 3 ^ k + 5) * q) + ((4 * 3 ^ k + 5) * c + r) := by
      rw [Int.mul_add, Int.mul_left_comm]; omega
    rw [hexp] at h
    obtain ⟨Q, c', hc', hQ, hQz⟩ := h.peel_auto
    -- r' = Q - n q is the next carry
    have hS : InS k (Q - (4 * 3 ^ k + 5) * q) :=
      InS.step hk hr hc hc' (by omega)
    have hb := hS.bound (by omega)
    have hnq := mul_ge_self (n := 4 * 3 ^ k + 5) (q := q) (by omega) (by omega)
    rcases hQz with h0 | hZ
    · omega
    · apply ih hqpos (Q - (4 * 3 ^ k + 5) * q) hS
      rw [show (4 * 3 ^ k + 5) * q + (Q - (4 * 3 ^ k + 5) * q) = Q by omega]
      exact hZ

/-- **Theorem.** For every k ≥ 5, 4·3^k + 5 is not a quotient of two positive integers whose
    balanced-ternary digits are all nonzero. -/
theorem four_pow_plus_five_not_in_BB (k : Nat) (hk : 5 ≤ k) :
    ¬ ∃ m N : Int, 0 < m ∧ ZF m ∧ 0 < N ∧ ZF N ∧ N = (4 * 3 ^ k + 5) * m := by
  rintro ⟨m, N, hm, hZm, _, hZN, rfl⟩
  exact key hk m hZm hm 0 .zero (by rw [Int.add_zero]; exact hZN)

/-- Consequence: infinitely many n ≢ 0 (mod 3) lie outside B/B. -/
theorem infinitely_many_exceptions :
    ∀ K : Nat, ∃ n : Int, n > K ∧ n % 3 ≠ 0 ∧
      ¬ ∃ m N : Int, 0 < m ∧ ZF m ∧ 0 < N ∧ ZF N ∧ N = n * m := by
  intro K
  refine ⟨4 * 3 ^ (K + 5) + 5, ?_, ?_, four_pow_plus_five_not_in_BB (K + 5) (by omega)⟩
  · have := pow3_mono 0 (K + 5); have : (K : Int) + 5 < 3 ^ (K + 5) := by
      have key : ∀ t : Nat, (t : Int) < 3 ^ t := by
        intro t; induction t with
        | zero => decide
        | succ t ih => rw [pow3_succ]; omega
      exact_mod_cast key (K + 5)
    omega
  · have := pow3_top (k := K + 5) (by omega); omega
