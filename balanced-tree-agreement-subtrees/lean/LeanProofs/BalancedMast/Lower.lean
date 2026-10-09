import LeanProofs.BalancedMast.Balanced

/-!
# The lower bound: the one-level induction (Section 5 of the note)

For balanced phylogenetic `S, T` of heights `h₁, h₂` sharing `t` labels,
`t^a 2^(-c(h₁+h₂)) ≤ mast(S, T)` whenever the inequality `Φ_{a,c} ≥ 1` of Lemma 5.1 holds on the
simplex (`CertOne a c`). Putting `h₁ = h₂ = m` gives `M(2^m) ≥ 2^(m(a-2c))`.
-/

namespace BalancedMast

open Tree

/-- `Φ_{a,c}(x)`: the six cases of the recursion, read on the overlap fractions
`x₁ = S_L ∩ T_L`, `x₂ = S_L ∩ T_R`, `x₃ = S_R ∩ T_L`, `x₄ = S_R ∩ T_R`. -/
noncomputable def Phi (a c x₁ x₂ x₃ x₄ : ℝ) : ℝ :=
  max (max ((4 : ℝ) ^ c * (x₁ ^ a + x₄ ^ a)) ((4 : ℝ) ^ c * (x₂ ^ a + x₃ ^ a)))
    (max (max ((2 : ℝ) ^ c * (x₁ + x₂) ^ a) ((2 : ℝ) ^ c * (x₃ + x₄) ^ a))
      (max ((2 : ℝ) ^ c * (x₁ + x₃) ^ a) ((2 : ℝ) ^ c * (x₂ + x₄) ^ a)))

/-- The inequality of Lemma 5.1: `Φ_{a,c} ≥ 1` on the simplex. -/
def CertOne (a c : ℝ) : Prop :=
  ∀ x₁ x₂ x₃ x₄ : ℝ, 0 ≤ x₁ → 0 ≤ x₂ → 0 ≤ x₃ → 0 ≤ x₄ → x₁ + x₂ + x₃ + x₄ = 1 →
    1 ≤ Phi a c x₁ x₂ x₃ x₄

lemma Phi_nonneg {a c x₁ x₂ x₃ x₄ : ℝ} (h₁ : 0 ≤ x₁) (h₄ : 0 ≤ x₄) : 0 ≤ Phi a c x₁ x₂ x₃ x₄ :=
  le_max_of_le_left (le_max_of_le_left (by positivity))

/-- `Φ` is homogeneous of degree `a`. -/
lemma Phi_smul {a c t x₁ x₂ x₃ x₄ : ℝ} (ht : 0 ≤ t) (h₁ : 0 ≤ x₁) (h₂ : 0 ≤ x₂) (h₃ : 0 ≤ x₃)
    (h₄ : 0 ≤ x₄) : Phi a c (t * x₁) (t * x₂) (t * x₃) (t * x₄) = t ^ a * Phi a c x₁ x₂ x₃ x₄ := by
  have e : ∀ u, 0 ≤ u → (t * u) ^ a = t ^ a * u ^ a := fun u hu => Real.mul_rpow ht hu
  have hta : 0 ≤ t ^ a := Real.rpow_nonneg ht a
  simp only [Phi, ← mul_add, e _ h₁, e _ h₂, e _ h₃, e _ h₄, e _ (add_nonneg h₁ h₂),
    e _ (add_nonneg h₃ h₄), e _ (add_nonneg h₁ h₃), e _ (add_nonneg h₂ h₄)]
  simp only [mul_left_comm _ (t ^ a), ← mul_max_of_nonneg _ _ hta]

/-- Lemma 5.1, scaled: `(n₁+n₂+n₃+n₄)^a ≤ Φ(n)` for all nonnegative `n`. -/
lemma CertOne.scaled {a c : ℝ} (ha : 0 < a) (h : CertOne a c) {n₁ n₂ n₃ n₄ : ℝ} (h₁ : 0 ≤ n₁)
    (h₂ : 0 ≤ n₂) (h₃ : 0 ≤ n₃) (h₄ : 0 ≤ n₄) :
    (n₁ + n₂ + n₃ + n₄) ^ a ≤ Phi a c n₁ n₂ n₃ n₄ := by
  set t := n₁ + n₂ + n₃ + n₄
  rcases (show 0 ≤ t by positivity).eq_or_lt with ht | ht
  · rw [← ht, Real.zero_rpow ha.ne']; exact Phi_nonneg h₁ h₄
  · have hx := h (n₁ / t) (n₂ / t) (n₃ / t) (n₄ / t) (by positivity) (by positivity)
      (by positivity) (by positivity) (by rw [← add_div, ← add_div, ← add_div]; exact div_self ht.ne')
    have := Phi_smul (a := a) (c := c) ht.le (div_nonneg h₁ ht.le) (div_nonneg h₂ ht.le)
      (div_nonneg h₃ ht.le) (div_nonneg h₄ ht.le)
    simp only [mul_div_cancel₀ _ ht.ne'] at this
    rw [this]
    exact le_mul_of_one_le_right (Real.rpow_nonneg ht.le a) hx

variable {α : Type*} [DecidableEq α]

lemma Bal.eq_leaf {S : Tree α} (h : Bal 0 S) : ∃ x, S = Tree.leaf x := by
  cases h; exact ⟨_, rfl⟩

lemma Bal.eq_node {h : ℕ} {S : Tree α} (hS : Bal (h + 1) S) :
    ∃ l r, S = Tree.node l r ∧ Bal h l ∧ Bal h r := by
  cases hS; exact ⟨_, _, rfl, ‹_›, ‹_›⟩

/-- The shared labels of `S` and `T`, as a real number. -/
noncomputable def tt (S T : Tree α) : ℝ := ((S.L ∩ T.L).card : ℝ)

lemma tt_node_left (l r T : Tree α) (h : (node l r).Phylo) : tt (node l r) T = tt l T + tt r T := by
  simp only [tt, L_node, Finset.union_inter_distrib_right]
  rw [Finset.card_union_of_disjoint]
  · push_cast; ring
  · exact Finset.disjoint_of_subset_left Finset.inter_subset_left
      (Finset.disjoint_of_subset_right Finset.inter_subset_left (phylo_node.1 h).2.2)

lemma tt_node_right (S l r : Tree α) (h : (node l r).Phylo) :
    tt S (node l r) = tt S l + tt S r := by
  have e : ∀ U V : Tree α, tt U V = tt V U := fun U V => by simp [tt, Finset.inter_comm]
  rw [e, tt_node_left _ _ _ h, e l, e r]

lemma tt_nonneg (S T : Tree α) : 0 ≤ tt S T := Nat.cast_nonneg _

lemma two_rpow_shift (c x k : ℝ) :
    (2 : ℝ) ^ (-(c * x)) = (2 : ℝ) ^ (-(c * (x + k))) * (2 : ℝ) ^ (c * k) := by
  rw [← Real.rpow_add (by norm_num)]; ring_nf

lemma four_rpow (c : ℝ) : (2 : ℝ) ^ (c * 2) = (4 : ℝ) ^ c := by
  rw [mul_comm, Real.rpow_mul (by norm_num)]; norm_num

/-- **The one-level induction** (the proof of `M(n) ≥ n^0.235`, for any `(a, c)` with
`CertOne a c`). -/
theorem ansatz_one {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hcert : CertOne a c) :
    ∀ n h₁ h₂ (S T : Tree α), h₁ + h₂ = n → Bal h₁ S → Bal h₂ T → S.Phylo → T.Phylo →
      tt S T ^ a * (2 : ℝ) ^ (-(c * ((h₁ : ℝ) + h₂))) ≤ mast S T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro h₁ h₂ S T hn hS hT pS pT
  have hK1 : (2 : ℝ) ^ (-(c * ((h₁ : ℝ) + h₂))) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (by have : (0 : ℝ) ≤ c * ((h₁ : ℝ) + h₂) := by positivity
          linarith)
  -- a leaf shares at most one label
  have base : ∀ x, (S = leaf x ∨ T = leaf x) →
      tt S T ^ a * (2 : ℝ) ^ (-(c * ((h₁ : ℝ) + h₂))) ≤ mast S T := by
    intro x hx
    have hle : (S.L ∩ T.L).card ≤ 1 := by
      rcases hx with rfl | rfl
      · exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
      · exact (Finset.card_le_card Finset.inter_subset_right).trans (by simp)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h0 | h1
    · simp [tt, h0, Real.zero_rpow ha.ne']
    · have := one_le_mast (Finset.card_pos.1 (by omega : 0 < (S.L ∩ T.L).card))
      rw [tt, h1]; push_cast; rw [Real.one_rpow, one_mul]
      exact hK1.trans (by exact_mod_cast this)
  rcases Nat.eq_zero_or_pos h₁ with e₁ | e₁
  · subst e₁; obtain ⟨x, rfl⟩ := hS.eq_leaf; exact base x (Or.inl rfl)
  rcases Nat.eq_zero_or_pos h₂ with e₂ | e₂
  · subst e₂; obtain ⟨x, rfl⟩ := hT.eq_leaf; exact base x (Or.inr rfl)
  obtain ⟨k₁, rfl⟩ : ∃ k, h₁ = k + 1 := ⟨h₁ - 1, by omega⟩
  obtain ⟨k₂, rfl⟩ : ∃ k, h₂ = k + 1 := ⟨h₂ - 1, by omega⟩
  obtain ⟨l, r, rfl, hl, hr⟩ := hS.eq_node
  obtain ⟨l', r', rfl, hl', hr'⟩ := hT.eq_node
  obtain ⟨pl, pr, _⟩ := phylo_node.1 pS
  obtain ⟨pl', pr', _⟩ := phylo_node.1 pT
  -- the induction hypothesis on the smaller pairs that occur
  have IH : ∀ {g₁ g₂} {U V : Tree α}, g₁ + g₂ < n → Bal g₁ U → Bal g₂ V → U.Phylo → V.Phylo →
      tt U V ^ a * (2 : ℝ) ^ (-(c * ((g₁ : ℝ) + g₂))) ≤ mast U V :=
    fun hlt hU hV pU pV => ih _ hlt _ _ _ _ rfl hU hV pU pV
  set K := (2 : ℝ) ^ (-(c * (((k₁ + 1 : ℕ) : ℝ) + ((k₂ + 1 : ℕ) : ℝ))))
  have w2 : (2 : ℝ) ^ (-(c * ((k₁ : ℝ) + k₂))) = K * (4 : ℝ) ^ c := by
    rw [two_rpow_shift c _ 2, ← four_rpow]; congr 3; push_cast; ring
  have wS : (2 : ℝ) ^ (-(c * ((k₁ : ℝ) + ((k₂ + 1 : ℕ) : ℝ)))) = K * (2 : ℝ) ^ c := by
    rw [two_rpow_shift c _ 1, mul_one]; congr 3; push_cast; ring
  have wT : (2 : ℝ) ^ (-(c * (((k₁ + 1 : ℕ) : ℝ) + k₂))) = K * (2 : ℝ) ^ c := by
    rw [two_rpow_shift c _ 1, mul_one]; congr 3; push_cast; ring
  -- the six cases of the recursion
  set n₁ := tt l l'; set n₂ := tt l r'; set n₃ := tt r l'; set n₄ := tt r r'
  have q₁ := IH (by omega) hl hl' pl pl'
  have q₂ := IH (by omega) hl hr' pl pr'
  have q₃ := IH (by omega) hr hl' pr pl'
  have q₄ := IH (by omega) hr hr' pr pr'
  have qL := IH (by omega) hl (Bal.node hl' hr') pl pT
  have qR := IH (by omega) hr (Bal.node hl' hr') pr pT
  have qL' := IH (by omega) (Bal.node hl hr) hl' pS pl'
  have qR' := IH (by omega) (Bal.node hl hr) hr' pS pr'
  rw [w2] at q₁ q₂ q₃ q₄
  rw [wS] at qL qR
  rw [wT] at qL' qR'
  rw [tt_node_right _ _ _ pT] at qL qR
  rw [tt_node_left _ _ _ pS] at qL' qR'
  have m₁ := mast_node_node pS pT
  have m₂ := mast_node_cross pS pT
  have m₃ := mast_node_left (T := node l' r') pS
  have m₄ := mast_node_right (T := node l' r') pS
  have m₅ : mast (node l r) l' ≤ mast (node l r) (node l' r') := by
    rw [mast_comm, mast_comm (node l r)]; exact mast_node_left pT
  have m₆ : mast (node l r) r' ≤ mast (node l r) (node l' r') := by
    rw [mast_comm, mast_comm (node l r)]; exact mast_node_right pT
  have hKnn : 0 ≤ K := Real.rpow_nonneg (by norm_num) _
  have hPhi : K * Phi a c n₁ n₂ n₃ n₄ ≤ mast (node l r) (node l' r') := by
    simp only [Phi, mul_max_of_nonneg _ _ hKnn]
    refine max_le (max_le ?_ ?_) (max_le (max_le ?_ ?_) (max_le ?_ ?_))
    · exact le_trans (le_of_eq (by ring)) ((add_le_add q₁ q₄).trans (by exact_mod_cast m₁))
    · exact le_trans (le_of_eq (by ring)) ((add_le_add q₂ q₃).trans (by exact_mod_cast m₂))
    · exact le_trans (le_of_eq (by ring)) (qL.trans (by exact_mod_cast m₃))
    · exact le_trans (le_of_eq (by ring)) (qR.trans (by exact_mod_cast m₄))
    · exact le_trans (le_of_eq (by ring)) (qL'.trans (by exact_mod_cast m₅))
    · exact le_trans (le_of_eq (by ring)) (qR'.trans (by exact_mod_cast m₆))
  have htot : tt (node l r) (node l' r') = n₁ + n₂ + n₃ + n₄ := by
    rw [tt_node_left _ _ _ pS, tt_node_right _ _ _ pT, tt_node_right _ _ _ pT]; ring
  calc tt (node l r) (node l' r') ^ a * K = (n₁ + n₂ + n₃ + n₄) ^ a * K := by rw [htot]
    _ ≤ Phi a c n₁ n₂ n₃ n₄ * K :=
        mul_le_mul_of_nonneg_right (hcert.scaled ha (tt_nonneg _ _) (tt_nonneg _ _)
          (tt_nonneg _ _) (tt_nonneg _ _)) hKnn
    _ = K * Phi a c n₁ n₂ n₃ n₄ := mul_comm _ _
    _ ≤ _ := hPhi

/-- `M(2^m) ≥ 2^(m(a - 2c))` from the one-level inequality. -/
theorem M_lower_of_certOne {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (hcert : CertOne a c) (m : ℕ) :
    (2 : ℝ) ^ ((m : ℝ) * (a - 2 * c)) ≤ M m := by
  obtain ⟨S, T, hS, hT, pS, pT, hL, hm⟩ := M_mem m
  have := ansatz_one ha hc hcert _ m m S T rfl hS hT pS pT
  rw [← hm]
  have ht : tt S T = (2 : ℝ) ^ (m : ℝ) := by
    rw [tt, ← hL, Finset.inter_self, hS.card_L pS, Real.rpow_natCast]; push_cast; ring
  rw [ht, ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)] at this
  convert this using 2; ring

end BalancedMast
