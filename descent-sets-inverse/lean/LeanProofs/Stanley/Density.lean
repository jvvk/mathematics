/-
  Stanley, MathOverflow 486548. Part H. Theorem 1 of the paper: almost every pair occurs,
  `1 - f(n) / 4^(n-1) ≤ 6 e^(-n/20000)` for every `n ≥ 1`.

  Subsets of `{0, …, N-1}` (`N = n - 1`) are points `ω` of the cube `Fin N → Bool` with the uniform
  product law. Three statistics control Corollary 3.3: the size `|X|`, the count `A(X)` of
  non-breaks below `m - 1`, and the count `G(X)` of breaks `x ≥ m + 1` with `x - 1` not a break
  (`m = ⌊n/2⌋`). Each is Lipschitz in Hamming distance (constants `1, 1, 2`), so McDiarmid's
  bounded-difference inequality (vendored from github.com/openai/math, Apache 2.0) bounds the
  probability that it strays from its mean. A point is *good* when all three are near their means;
  pairs of good points occur (`good_pair`), and the bad points are exponentially rare.
-/
import LeanProofs.Stanley.Fill
import LeanProofs.Vendor.OAI.NumberTheory.JointDickman.Probability.FiniteMcDiarmidDischarge

namespace Stanley

namespace Density

open Finset OAI.JointDickman OAI.JointDickman.PublishedInputs

/-! ### The uniform cube -/

section Cube

variable {N : ℕ}

/-- The fair coin at every site. -/
noncomputable def unif (N : ℕ) : Fin N → Bool → ℝ := fun _ _ => 1 / 2

theorem unif_nonneg : ∀ (i : Fin N) (a : Bool), 0 ≤ unif N i a := fun _ _ => by
  unfold unif; norm_num

theorem unif_sum : ∀ i : Fin N, ∑ a, unif N i a = 1 := fun _ => by
  simp [unif]

theorem mass_eq (ω : Fin N → Bool) : siteProductMass (unif N) ω = (1 / 2) ^ N := by
  simp [siteProductMass, unif]

theorem prob_eq (E : (Fin N → Bool) → Prop) [DecidablePred E] :
    finiteProbability (siteProductMass (unif N)) E = ((univ.filter E).card : ℝ) * (1 / 2) ^ N := by
  unfold finiteProbability
  simp only [mass_eq]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

theorem expect_eq (f : (Fin N → Bool) → ℝ) :
    finiteExpectation (siteProductMass (unif N)) f = (∑ ω, f ω) * (1 / 2) ^ N := by
  unfold finiteExpectation
  simp only [mass_eq]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **McDiarmid's inequality on the fair cube**, as a count. -/
theorem tail (f : (Fin N → Bool) → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hlip : ∀ x y, |f x - f y| ≤ c * hammingDist x y) {a : ℝ} (ha : 0 < a) :
    ((univ.filter (fun ω => a < f ω - (∑ ω', f ω') * (1 / 2) ^ N)).card : ℝ) ≤
      2 ^ N * Real.exp (-2 * a ^ 2 / (N * c ^ 2)) := by
  have h := finiteMcDiarmidInput (A := Bool) N (unif N) unif_nonneg unif_sum f c hc hlip a ha
  rw [prob_eq, expect_eq, Fintype.card_fin] at h
  have h2 : (0 : ℝ) < (1 / 2) ^ N := by positivity
  have h3 : (2 : ℝ) ^ N * (1 / 2) ^ N = 1 := by rw [← mul_pow]; norm_num
  calc _ = ((univ.filter (fun ω => a < f ω - (∑ ω', f ω') * (1 / 2) ^ N)).card : ℝ) *
          (1 / 2) ^ N * 2 ^ N := by rw [mul_assoc, mul_comm ((1 / 2 : ℝ) ^ N), h3, mul_one]
    _ ≤ Real.exp (-2 * a ^ 2 / (N * c ^ 2)) * 2 ^ N :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := mul_comm _ _

/-! ### Counting with coordinate flips -/

/-- Flip coordinate `j`. -/
def flipAt (j : Fin N) (ω : Fin N → Bool) : Fin N → Bool := Function.update ω j (!(ω j))

theorem flipAt_flipAt (j : Fin N) (ω : Fin N → Bool) : flipAt j (flipAt j ω) = ω := by
  funext i; unfold flipAt
  by_cases h : i = j
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem flipAt_self (j : Fin N) (ω : Fin N → Bool) : flipAt j ω j = !(ω j) := by
  simp [flipAt]

theorem flipAt_ne {j k : Fin N} (h : k ≠ j) (ω : Fin N → Bool) : flipAt j ω k = ω k := by
  simp [flipAt, Function.update_of_ne h]

theorem card_flip (j : Fin N) (P : (Fin N → Bool) → Prop) [DecidablePred P] :
    (univ.filter P).card = (univ.filter (fun ω => P (flipAt j ω))).card := by
  apply Finset.card_bij' (fun ω _ => flipAt j ω) (fun ω _ => flipAt j ω)
  · intro ω hω; simpa [flipAt_flipAt] using hω
  · intro ω hω; simpa using hω
  · intro ω _; exact flipAt_flipAt j ω
  · intro ω _; exact flipAt_flipAt j ω

theorem card_coord (j : Fin N) (a : Bool) :
    ((univ.filter (fun ω : Fin N → Bool => ω j = a)).card : ℝ) = 2 ^ N / 2 := by
  have h1 := card_flip j (fun ω : Fin N → Bool => ω j = a)
  simp only [flipAt_self] at h1
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset (Fin N → Bool))) (p := fun ω => ω j = a)
  have h3 : (univ.filter (fun ω : Fin N → Bool => ¬ω j = a)) =
      univ.filter (fun ω : Fin N → Bool => (!ω j) = a) := by
    ext ω; cases a <;> cases h : ω j <;> simp [h]
  rw [h3, ← h1, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at h2
  have : ((univ.filter (fun ω : Fin N → Bool => ω j = a)).card : ℝ) * 2 = 2 ^ N := by
    exact_mod_cast (by omega : (univ.filter (fun ω : Fin N → Bool => ω j = a)).card * 2 = 2 ^ N)
  linarith

theorem card_coord2 {j k : Fin N} (hjk : j ≠ k) (a b : Bool) :
    ((univ.filter (fun ω : Fin N → Bool => ω j = a ∧ ω k = b)).card : ℝ) = 2 ^ N / 4 := by
  -- flipping `j` exchanges the classes `(a, b)` and `(!a, b)`
  have h1 := card_flip j (fun ω : Fin N → Bool => ω j = a ∧ ω k = b)
  simp only [flipAt_self, flipAt_ne (Ne.symm hjk)] at h1
  have hsplit : (univ.filter (fun ω : Fin N → Bool => ω k = b)).card =
      (univ.filter (fun ω : Fin N → Bool => ω j = a ∧ ω k = b)).card +
      (univ.filter (fun ω : Fin N → Bool => (!ω j) = a ∧ ω k = b)).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1; ext ω; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      cases a <;> cases ω j <;> simp
    · rw [Finset.disjoint_left]; intro ω h h'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h h'
      rw [h.1] at h'; cases a <;> simp at h'
  have hk := card_coord k b
  rw [hsplit, ← h1] at hk
  push_cast at hk
  linarith

end Cube

/-! ### The three statistics -/

section Stats

variable {N : ℕ}

/-- `1` or `0`. -/
noncomputable def ind (P : Prop) [Decidable P] : ℝ := if P then 1 else 0

theorem ind_nonneg (P : Prop) [Decidable P] : 0 ≤ ind P := by unfold ind; split_ifs <;> norm_num

theorem sum_ind (P : (Fin N → Bool) → Prop) [DecidablePred P] :
    ∑ ω, ind (P ω) = ((univ.filter P).card : ℝ) := by
  unfold ind; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]; simp

theorem sum_ind_fin (P : Fin N → Prop) [DecidablePred P] :
    ∑ i, ind (P i) = ((univ.filter P).card : ℝ) := by
  unfold ind; rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]; simp

/-- The predecessor index (only used at `i ≥ 1`). -/
def prev (i : Fin N) : Fin N := ⟨i.1 - 1, by omega⟩

/-- `|X|`. -/
noncomputable def sz (ω : Fin N → Bool) : ℝ := ∑ i, ind (ω i = true)

/-- `A(X)`: non-breaks below `m - 1`. -/
noncomputable def stA (m : ℕ) (ω : Fin N → Bool) : ℝ := ∑ i, ind (i.1 < m - 1 ∧ ω i = false)

/-- `G(X)`: breaks `x ≥ m + 1` with `x - 1` not a break. -/
noncomputable def stG (m : ℕ) (ω : Fin N → Bool) : ℝ :=
  ∑ i, ind (m + 1 ≤ i.1 ∧ ω i = true ∧ ω (prev i) = false)

theorem sum_sz : ∑ ω : Fin N → Bool, sz ω = N * (2 ^ N / 2) := by
  unfold sz
  rw [Finset.sum_comm]
  simp_rw [sum_ind (fun ω : Fin N → Bool => _ = true), card_coord]
  simp

theorem sum_stA (m : ℕ) : ∑ ω : Fin N → Bool, stA m ω =
    ((univ.filter (fun i : Fin N => i.1 < m - 1)).card : ℝ) * (2 ^ N / 2) := by
  unfold stA
  rw [Finset.sum_comm]
  have : ∀ i : Fin N, ∑ ω : Fin N → Bool, ind (i.1 < m - 1 ∧ ω i = false) =
      ind (i.1 < m - 1) * (2 ^ N / 2) := by
    intro i
    by_cases hi : i.1 < m - 1
    · simp only [hi, true_and]; rw [sum_ind (fun ω : Fin N → Bool => ω i = false), card_coord]
      simp [ind]
    · simp [hi, ind]
  simp_rw [this, ← Finset.sum_mul, sum_ind_fin]

theorem sum_stG (m : ℕ) : ∑ ω : Fin N → Bool, stG m ω =
    ((univ.filter (fun i : Fin N => m + 1 ≤ i.1)).card : ℝ) * (2 ^ N / 4) := by
  unfold stG
  rw [Finset.sum_comm]
  have : ∀ i : Fin N, ∑ ω : Fin N → Bool, ind (m + 1 ≤ i.1 ∧ ω i = true ∧ ω (prev i) = false) =
      ind (m + 1 ≤ i.1) * (2 ^ N / 4) := by
    intro i
    by_cases hi : m + 1 ≤ i.1
    · simp only [hi, true_and]
      rw [sum_ind (fun ω : Fin N → Bool => ω i = true ∧ ω (prev i) = false),
        card_coord2 (fun h => by have := congrArg Fin.val h; simp [prev] at this; omega)]
      simp [ind]
    · simp [hi, ind]
  simp_rw [this, ← Finset.sum_mul, sum_ind_fin]

theorem ind_sub_le {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : |ind P - ind Q| = 0 := by
  simp [ind, h]

theorem hamming_eq (x y : Fin N → Bool) :
    (hammingDist x y : ℝ) = ∑ i, ind (x i ≠ y i) := by
  rw [sum_ind_fin]; rfl

theorem abs_ind_coord (x y : Fin N → Bool) (i : Fin N) (P : Fin N → Bool → Prop)
    [∀ i b, Decidable (P i b)] : |ind (P i (x i)) - ind (P i (y i))| ≤ ind (x i ≠ y i) := by
  by_cases h : x i = y i
  · rw [h]; simp [ind]
  · unfold ind; split_ifs <;> norm_num

theorem sz_lip (x y : Fin N → Bool) : |sz x - sz y| ≤ 1 * hammingDist x y := by
  rw [one_mul, hamming_eq]; unfold sz
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
    abs_ind_coord x y i (fun _ b => b = true))

theorem stA_lip (m : ℕ) (x y : Fin N → Bool) : |stA m x - stA m y| ≤ 1 * hammingDist x y := by
  rw [one_mul, hamming_eq]; unfold stA
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
    abs_ind_coord x y i (fun i b => i.1 < m - 1 ∧ b = false))

theorem stG_lip (m : ℕ) (x y : Fin N → Bool) : |stG m x - stG m y| ≤ 2 * hammingDist x y := by
  unfold stG
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ i : Fin N,
      |ind (m + 1 ≤ i.1 ∧ x i = true ∧ x (prev i) = false) -
        ind (m + 1 ≤ i.1 ∧ y i = true ∧ y (prev i) = false)| ≤
      ind (x i ≠ y i) + ind (m + 1 ≤ i.1 ∧ x (prev i) ≠ y (prev i)) := by
    intro i
    by_cases h1 : x i = y i <;> by_cases h2 : x (prev i) = y (prev i) <;>
      by_cases hm : m + 1 ≤ i.1 <;> simp only [ind, h1, h2, hm, true_and, false_and, ne_eq,
        not_true_eq_false, not_false_eq_true, if_true, if_false] <;>
      (try split_ifs) <;> norm_num
  have hprev : ∑ i : Fin N, ind (m + 1 ≤ i.1 ∧ x (prev i) ≠ y (prev i)) ≤
      ∑ i : Fin N, ind (x i ≠ y i) := by
    rw [sum_ind_fin, sum_ind_fin]
    exact_mod_cast Finset.card_le_card_of_injOn prev
      (fun i hi => by
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
        exact hi.2)
      (fun i hi j hj h => by
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi hj
        have := congrArg Fin.val h; simp [prev] at this; exact Fin.ext (by omega))
  calc _ ≤ ∑ i, |ind (m + 1 ≤ i.1 ∧ x i = true ∧ x (prev i) = false) -
        ind (m + 1 ≤ i.1 ∧ y i = true ∧ y (prev i) = false)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (ind (x i ≠ y i) + ind (m + 1 ≤ i.1 ∧ x (prev i) ≠ y (prev i))) :=
        Finset.sum_le_sum fun i _ => hterm i
    _ ≤ 2 * hammingDist x y := by
        rw [Finset.sum_add_distrib, hamming_eq]; linarith

end Stats

/-! ### From cube points to break sets -/

section Sets

open Fill

variable {N : ℕ}

/-- The break set of a cube point. -/
def toSet (ω : Fin N → Bool) : Finset ℕ :=
  (univ.filter (fun i : Fin N => ω i = true)).map Fin.valEmbedding

theorem mem_toSet {ω : Fin N → Bool} {x : ℕ} : x ∈ toSet ω ↔ ∃ h : x < N, ω ⟨x, h⟩ = true := by
  simp only [toSet, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Fin.valEmbedding_apply]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i.2, hi⟩
  · rintro ⟨h, hx⟩; exact ⟨⟨x, h⟩, hx, rfl⟩

theorem toSet_sub (ω : Fin N → Bool) : toSet ω ⊆ range N := fun x hx =>
  Finset.mem_range.mpr (mem_toSet.mp hx).1

theorem toSet_injective : Function.Injective (toSet (N := N)) := by
  intro ω ω' h
  funext i
  have h1 : i.1 ∈ toSet ω ↔ i.1 ∈ toSet ω' := by rw [h]
  simp only [mem_toSet, i.2, exists_true_left, Fin.eta] at h1
  cases hω : ω i <;> cases hω' : ω' i <;> simp_all

theorem card_toSet (ω : Fin N → Bool) : ((toSet ω).card : ℝ) = sz ω := by
  unfold sz; rw [sum_ind_fin, toSet, Finset.card_map]

/-- `A(X)` as a finset count. -/
def setA (m : ℕ) (X : Finset ℕ) : Finset ℕ := (range (m - 1)).filter (· ∉ X)

theorem card_setA {m : ℕ} (hm : m - 1 ≤ N) (ω : Fin N → Bool) :
    ((setA m (toSet ω)).card : ℝ) = stA m ω := by
  unfold stA; rw [sum_ind_fin]
  congr 1
  apply Finset.card_bij (fun x hx => (⟨x, by
      simp only [setA, Finset.mem_filter, Finset.mem_range] at hx; omega⟩ : Fin N))
  · intro x hx
    simp only [setA, Finset.mem_filter, Finset.mem_range, mem_toSet, not_exists] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hx.1, ?_⟩
    have := hx.2 (by omega)
    simpa using this
  · intro a _ b _ h; simpa using h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨i.1, ?_, rfl⟩
    simp only [setA, Finset.mem_filter, Finset.mem_range, mem_toSet, not_exists]
    exact ⟨hi.1, fun h => by simp [hi.2]⟩

/-- `G(X)`: breaks `x ≥ m + 1` (below `N`) with `x - 1` not a break. -/
def setG (N m : ℕ) (X : Finset ℕ) : Finset ℕ :=
  (range N).filter (fun x => m + 1 ≤ x ∧ x ∈ X ∧ x - 1 ∉ X)

theorem card_setG (m : ℕ) (ω : Fin N → Bool) :
    ((setG N m (toSet ω)).card : ℝ) = stG m ω := by
  unfold stG; rw [sum_ind_fin]
  congr 1
  apply Finset.card_bij (fun x hx => (⟨x, by
      simp only [setG, Finset.mem_filter, Finset.mem_range] at hx; omega⟩ : Fin N))
  · intro x hx
    simp only [setG, Finset.mem_filter, Finset.mem_range, mem_toSet, not_exists] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨hxN, hm, ⟨_, hx⟩, hx1⟩ := hx
    refine ⟨hm, hx, ?_⟩
    have := hx1 (by omega)
    simpa [prev] using this
  · intro a _ b _ h; simpa using h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine ⟨i.1, ?_, rfl⟩
    simp only [setG, Finset.mem_filter, Finset.mem_range, mem_toSet, not_exists]
    refine ⟨i.2, hi.1, ⟨i.2, hi.2.1⟩, fun h => ?_⟩
    have := hi.2.2; simp only [prev] at this; simp [this]

/-! ### The two counts `G - 2` and `G - 1` -/

theorem card_low_rk (G : Finset ℕ) : (G.filter (fun x => rk G x < 2)).card ≤ 2 := by
  have h : G.filter (fun x => rk G x < 2) =
      G.filter (fun x => rk G x = 0) ∪ G.filter (fun x => rk G x = 1) := by
    rw [← Finset.filter_or]; exact Finset.filter_congr (fun x _ => by omega)
  rw [h]
  refine (Finset.card_union_le _ _).trans ?_
  rw [card_rk_eq, card_rk_eq]
  split_ifs <;> omega

theorem setG_sub {N m : ℕ} {X : Finset ℕ} : setG N m X ⊆ X := fun x hx => by
  simp only [setG, Finset.mem_filter] at hx; exact hx.2.2.1

theorem rk_setG_le {N m : ℕ} {X : Finset ℕ} (x : ℕ) : rk (setG N m X) x ≤ rk X x :=
  Finset.card_le_card fun y hy => by
    simp only [Finset.mem_filter] at hy ⊢; exact ⟨setG_sub hy.1, hy.2⟩

/-- Paper, proof of Theorem 1, second bullet: `Σ_late (|R| - 1) ≥ G(X) - 2`. -/
theorem setG_le_exC {n m : ℕ} {X : Finset ℕ} :
    (setG (n - 1) m X).card ≤ (exC n m X).card + 2 := by
  set G := setG (n - 1) m X
  have hsub : G.filter (fun x => 2 ≤ rk G x) ⊆ exC n m X := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have hxG := hx.1
    simp only [G, setG, Finset.mem_filter, Finset.mem_range] at hxG
    obtain ⟨hxN, hm, hxX, hx1⟩ := hxG
    rw [mem_exC]
    refine ⟨by omega, by omega, hx1, le_trans hx.2 (rk_setG_le x), ?_⟩
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < (G.filter (· < x)).card by
      have := hx.2; unfold rk at this; omega)
    rw [Finset.mem_filter] at hy
    have hyG := hy.1
    simp only [G, setG, Finset.mem_filter] at hyG
    exact ⟨y, hyG.2.2.1, by omega, hy.2⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_filter_add_card_filter_not (s := G) (p := fun x => 2 ≤ rk G x)
  have h3 := card_low_rk G
  have h4 : G.filter (fun x => ¬ 2 ≤ rk G x) = G.filter (fun x => rk G x < 2) :=
    Finset.filter_congr (fun x _ => by omega)
  rw [h4] at h2
  omega

/-- Paper, proof of Theorem 1, first bullet: `≥ G(X) - 1` late runs follow a run of length `≥ 2`. -/
theorem setG_le_tsG {n m : ℕ} {X : Finset ℕ} :
    (setG (n - 1) m X).card ≤ (tsG n m X).card + 1 := by
  set G := setG (n - 1) m X
  have hsub : (G.filter (fun x => 1 ≤ rk G x)).image (· + 1) ⊆ tsG n m X := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq
    rw [Finset.mem_filter] at hx
    have hxG := hx.1
    simp only [G, setG, Finset.mem_filter, Finset.mem_range] at hxG
    obtain ⟨hxN, hm, hxX, hx1⟩ := hxG
    rw [mem_tsG, rk_succ_of_mem hxX]
    have := le_trans hx.2 (rk_setG_le (N := n - 1) (m := m) x)
    exact ⟨by omega, by omega, by simpa using hxX, by simpa using hx1, by omega, by omega⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (add_left_injective 1)] at h1
  have h2 := Finset.card_filter_add_card_filter_not (s := G) (p := fun x => 1 ≤ rk G x)
  have h3 : (G.filter (fun x => ¬ 1 ≤ rk G x)).card ≤ 1 := by
    have : G.filter (fun x => ¬ 1 ≤ rk G x) = G.filter (fun x => rk G x = 0) :=
      Finset.filter_congr (fun x _ => by omega)
    rw [this, card_rk_eq]; split_ifs <;> omega
  omega

end Sets

/-! ### Good pairs occur -/

theorem pairs_symm {n : ℕ} {S T : Finset ℕ} (h : (S, T) ∈ pairs n) : (T, S) ∈ pairs n := by
  obtain ⟨σ, _, hσ⟩ := Finset.mem_image.mp h
  refine Finset.mem_image.mpr ⟨σ⁻¹, Finset.mem_univ _, ?_⟩
  simp only [inv_inv]
  simp only [Prod.mk.injEq] at hσ ⊢
  exact ⟨hσ.2, hσ.1⟩

/-- The three conditions on a break set, with `m = ⌊n/2⌋`. -/
def GoodSet (n : ℕ) (X : Finset ℕ) : Prop :=
  |(X.card : ℝ) - ((n - 1 : ℕ) : ℝ) / 2| ≤ n / 200 ∧
  (n : ℝ) / 5 ≤ (setA (n / 2) X).card ∧ (n : ℝ) / 10 + 2 ≤ (setG (n - 1) (n / 2) X).card

theorem good_pair_lt {n : ℕ} (hn : 200 ≤ n) {S T : Finset ℕ} (hS : S ⊆ range (n - 1))
    (hT : T ⊆ range (n - 1)) (gS : GoodSet n S) (gT : GoodSet n T) (hlt : S.card < T.card) :
    (S, T) ∈ pairs n := by
  obtain ⟨hsS, hAS, hGS⟩ := gS
  obtain ⟨hsT, hAT, hGT⟩ := gT
  have hn' : (200 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : (((n - 1 : ℕ)) : ℝ) = n - 1 := by push_cast [show 1 ≤ n by omega]; ring
  rw [hN] at hsS hsT
  have hd : ((T.card - S.card : ℕ) : ℝ) = T.card - S.card := by
    push_cast [Nat.cast_sub hlt.le]; ring
  have hdiff : ((T.card - S.card : ℕ) : ℝ) ≤ n / 100 := by
    rw [hd]
    have := (abs_le.mp hsS).1; have := (abs_le.mp hsT).2; linarith
  have hC := setG_le_exC (n := n) (m := n / 2) (X := S)
  have hG := setG_le_tsG (n := n) (m := n / 2) (X := T)
  apply Fill.pair_of_fillings (m := n / 2) hS hT
  · have : (1 : ℝ) ≤ S.card := by have := (abs_le.mp hsS).1; linarith
    exact_mod_cast this
  · exact hlt
  · have : ((T.card - S.card : ℕ) : ℝ) + 1 ≤ (setA (n / 2) S).card := by linarith
    exact_mod_cast this
  · have : ((T.card - S.card : ℕ) : ℝ) + 1 ≤ (setA (n / 2) T).card := by linarith
    exact_mod_cast this
  · have hC' : ((setG (n - 1) (n / 2) S).card : ℝ) ≤ (Fill.exC n (n / 2) S).card + 2 := by
      exact_mod_cast hC
    have : ((T.card - S.card : ℕ) : ℝ) ≤ (Fill.exC n (n / 2) S).card := by linarith
    exact_mod_cast this
  · have hG' : ((setG (n - 1) (n / 2) T).card : ℝ) ≤ (Fill.tsG n (n / 2) T).card + 1 := by
      exact_mod_cast hG
    have : ((T.card - S.card : ℕ) : ℝ) ≤ (Fill.tsG n (n / 2) T).card := by linarith
    exact_mod_cast this

/-- **Two good break sets form an occurring pair** (for `n ≥ 200`). -/
theorem good_pair {n : ℕ} (hn : 200 ≤ n) {S T : Finset ℕ} (hS : S ⊆ range (n - 1))
    (hT : T ⊆ range (n - 1)) (gS : GoodSet n S) (gT : GoodSet n T) : (S, T) ∈ pairs n := by
  rcases lt_trichotomy S.card T.card with h | h | h
  · exact good_pair_lt hn hS hT gS gT h
  · exact mem_pairs hS hT h
  · exact pairs_symm (good_pair_lt hn hT hS gT gS h)

/-! ### Counting the bad points -/

section Bad

variable {N : ℕ}

theorem card_cube : ((univ : Finset (Fin N → Bool)).card : ℝ) = 2 ^ N := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]; push_cast; ring

theorem cntLt_le (k : ℕ) : (univ.filter (fun i : Fin N => i.1 < k)).card ≤ k := by
  have := Finset.card_le_card_of_injOn (fun i : Fin N => i.1)
    (s := univ.filter (fun i : Fin N => i.1 < k)) (t := range k)
    (fun i hi => by
      have h := Finset.mem_coe.mp hi
      rw [Finset.mem_filter] at h
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr h.2))
    (fun i _ j _ h => Fin.ext h)
  rwa [Finset.card_range] at this

theorem le_cntLt {k : ℕ} (hk : k ≤ N) : k ≤ (univ.filter (fun i : Fin N => i.1 < k)).card := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · omega
  have := Finset.card_le_card_of_injOn (fun x : ℕ => (⟨min x (N - 1),
      lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hN one_pos)⟩ : Fin N))
    (s := range k) (t := univ.filter (fun i : Fin N => i.1 < k))
    (fun x hx => by
      have h := Finset.mem_range.mp (Finset.mem_coe.mp hx)
      exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        show min x (N - 1) < k by omega⟩))
    (fun x hx y hy h => by
      have hx' := Finset.mem_range.mp (Finset.mem_coe.mp hx)
      have hy' := Finset.mem_range.mp (Finset.mem_coe.mp hy)
      have := congrArg Fin.val h; simp only at this; omega)
  rwa [Finset.card_range] at this

theorem cntGe (k : ℕ) : N - k ≤ (univ.filter (fun i : Fin N => k ≤ i.1)).card := by
  have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin N)))
    (p := fun i : Fin N => i.1 < k)
  have h2 : (univ : Finset (Fin N)).filter (fun i => ¬ i.1 < k) = univ.filter (fun i => k ≤ i.1) :=
    Finset.filter_congr (fun i _ => by omega)
  rw [h2, Finset.card_univ, Fintype.card_fin] at h
  have := cntLt_le (N := N) k
  omega

/-- McDiarmid in the form used: a deviation of at least `lo` costs `e^(-n/k)`. -/
theorem tail_n (f : (Fin N → Bool) → ℝ) {c : ℝ} (hc : 0 < c)
    (hlip : ∀ x y, |f x - f y| ≤ c * hammingDist x y) {n a lo k : ℝ} (hk : 0 < k) (hlo : 0 < lo)
    (hle : lo ≤ a) (hN : 0 < (N : ℝ)) (hkey : n * N * c ^ 2 ≤ 2 * k * lo ^ 2) :
    ((univ.filter (fun ω => a < f ω - (∑ ω', f ω') * (1 / 2) ^ N)).card : ℝ) ≤
      2 ^ N * Real.exp (-n / k) := by
  refine (tail f hc.le hlip (by linarith)).trans ?_
  gcongr 2 ^ N * ?_
  apply Real.exp_le_exp.mpr
  have hpos : 0 < (N : ℝ) * c ^ 2 := by positivity
  have : lo ^ 2 ≤ a ^ 2 := by nlinarith
  have h2 : n / k ≤ 2 * a ^ 2 / (N * c ^ 2) := by
    rw [div_le_div_iff₀ hk hpos]; nlinarith
  have h3 : -2 * a ^ 2 / (N * c ^ 2) = -(2 * a ^ 2 / (N * c ^ 2)) := by ring
  rw [h3]; linarith [show -n / k = -(n / k) by ring]

theorem half_pow : (2 : ℝ) ^ N / 2 * (1 / 2) ^ N = 1 / 2 := by
  rw [div_mul_eq_mul_div, ← mul_pow]; norm_num

theorem quarter_pow : (2 : ℝ) ^ N / 4 * (1 / 2) ^ N = 1 / 4 := by
  rw [div_mul_eq_mul_div, ← mul_pow]; norm_num

end Bad

/-- A good cube point. -/
def GoodPt (n : ℕ) (ω : Fin (n - 1) → Bool) : Prop := GoodSet n (toSet ω)

noncomputable instance (n : ℕ) : DecidablePred (GoodPt n) := fun _ => Classical.dec _

/-- The two fast tails fit under one slow one: `e^(-n/800) + e^(-n/12800) ≤ e^(-n/20000)`
once `n ≥ 6000`. -/
theorem exp_absorb {n : ℝ} (hn : 6000 ≤ n) :
    Real.exp (-n / 800) + Real.exp (-n / 12800) ≤ Real.exp (-n / 20000) := by
  set a := 3 * n / 2500
  set b := 9 * n / 320000
  have hu : Real.exp (-n / 800) = Real.exp (-n / 20000) * Real.exp (-a) := by
    rw [← Real.exp_add]; congr 1; simp only [a]; ring
  have hv : Real.exp (-n / 12800) = Real.exp (-n / 20000) * Real.exp (-b) := by
    rw [← Real.exp_add]; congr 1; simp only [b]; ring
  have inv_le (x : ℝ) (hx : 0 ≤ x) : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp x])
  have ha : 0 ≤ a := by simp only [a]; linarith
  have hb : 0 ≤ b := by simp only [b]; linarith
  have hab : 1 ≤ a * b := by simp only [a, b]; nlinarith
  have hsum : 1 / (1 + a) + 1 / (1 + b) ≤ 1 := by
    rw [div_add_div _ _ (by linarith) (by linarith), div_le_one (by positivity)]; nlinarith
  rw [hu, hv, ← mul_add]
  have := Real.exp_pos (-n / 20000)
  nlinarith [inv_le a ha, inv_le b hb]

theorem card_bad {n : ℕ} (hn6 : 6000 ≤ n) :
    ((univ.filter (fun ω : Fin (n - 1) → Bool => ¬ GoodPt n ω)).card : ℝ) ≤
      3 * (2 ^ (n - 1) * Real.exp (-(n : ℝ) / 20000)) := by
  have hn : 200 ≤ n := by omega
  set N := n - 1 with hNdef
  set m := n / 2 with hm
  have hn' : (200 : ℝ) ≤ n := by exact_mod_cast hn
  have hNr : (N : ℝ) = n - 1 := by rw [hNdef]; push_cast [show 1 ≤ n by omega]; ring
  have hNpos : (0 : ℝ) < N := by rw [hNr]; linarith
  have hm2 : (n : ℝ) - 1 ≤ 2 * (m : ℝ) := by
    have : n ≤ 2 * m + 1 := by omega
    have : (n : ℝ) ≤ 2 * m + 1 := by exact_mod_cast this
    linarith
  have hm3 : 2 * (m : ℝ) ≤ n := by
    have : 2 * m ≤ n := by omega
    exact_mod_cast this
  -- the means
  have mz : (∑ ω : Fin N → Bool, sz ω) * (1 / 2) ^ N = N / 2 := by
    rw [sum_sz, mul_assoc, half_pow]; ring
  have mA : (m : ℝ) - 1 ≤ 2 * ((∑ ω : Fin N → Bool, stA m ω) * (1 / 2) ^ N) := by
    rw [sum_stA, mul_assoc, half_pow]
    have := le_cntLt (N := N) (k := m - 1) (by omega)
    have h' : ((m - 1 : ℕ) : ℝ) ≤ (univ.filter (fun i : Fin N => i.1 < m - 1)).card := by
      exact_mod_cast this
    have : ((m - 1 : ℕ) : ℝ) ≥ m - 1 := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h]; simp
      · push_cast [Nat.cast_sub h]; linarith
    linarith
  have mG : (N : ℝ) - m - 1 ≤ 4 * ((∑ ω : Fin N → Bool, stG m ω) * (1 / 2) ^ N) := by
    rw [sum_stG, mul_assoc, quarter_pow]
    have := cntGe (N := N) (m + 1)
    have h' : ((N - (m + 1) : ℕ) : ℝ) ≤ (univ.filter (fun i : Fin N => m + 1 ≤ i.1)).card := by
      exact_mod_cast this
    have : ((N - (m + 1) : ℕ) : ℝ) ≥ N - m - 1 := by
      by_cases h : m + 1 ≤ N
      · push_cast [Nat.cast_sub h]; linarith
      · have : (N : ℝ) < m + 1 := by exact_mod_cast (not_le.mp h)
        have : (0 : ℝ) ≤ ((N - (m + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
    linarith
  -- bad points lie in one of four tail events
  set E1 := univ.filter (fun ω : Fin N → Bool =>
    (n : ℝ) / 200 < sz ω - (∑ ω', sz ω') * (1 / 2) ^ N)
  set E2 := univ.filter (fun ω : Fin N → Bool =>
    (n : ℝ) / 200 < (fun ω => -sz ω) ω - (∑ ω', (fun ω => -sz ω) ω') * (1 / 2) ^ N)
  set aA := (∑ ω : Fin N → Bool, stA m ω) * (1 / 2) ^ N - n / 5
  set E3 := univ.filter (fun ω : Fin N → Bool =>
    aA < (fun ω => -stA m ω) ω - (∑ ω', (fun ω => -stA m ω) ω') * (1 / 2) ^ N)
  set aG := (∑ ω : Fin N → Bool, stG m ω) * (1 / 2) ^ N - (n / 10 + 2)
  set E4 := univ.filter (fun ω : Fin N → Bool =>
    aG < (fun ω => -stG m ω) ω - (∑ ω', (fun ω => -stG m ω) ω') * (1 / 2) ^ N)
  have hsub : univ.filter (fun ω : Fin N → Bool => ¬ GoodPt n ω) ⊆ E1 ∪ E2 ∪ E3 ∪ E4 := by
    intro ω hω0
    have hω : ¬ GoodPt n ω := (Finset.mem_filter.mp hω0).2
    unfold GoodPt GoodSet at hω
    rw [card_toSet, card_setA (by omega), card_setG] at hω
    simp only [E1, E2, E3, E4, aA, aG, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.sum_neg_distrib, neg_mul]
    rw [mz]
    have hNN : ((n - 1 : ℕ) : ℝ) = N := rfl
    rw [hNN] at hω
    by_contra hc
    push_neg at hc
    apply hω
    refine ⟨abs_le.mpr ⟨by linarith [hc.1.1.2], by linarith [hc.1.1.1]⟩, ?_, ?_⟩
    · linarith [hc.1.2]
    · linarith [hc.2]
  have hz := tail_n (n := n) (lo := n / 200) (k := 20000) sz one_pos sz_lip (by norm_num) (by positivity) le_rfl hNpos
    (by rw [hNr]; nlinarith)
  have hz' := tail_n (n := n) (lo := n / 200) (fun ω => -sz ω) one_pos
    (k := 20000) (fun x y => by rw [show -sz x - -sz y = -(sz x - sz y) by ring, abs_neg]; exact sz_lip x y)
    (by norm_num) (by positivity) le_rfl hNpos (by rw [hNr]; nlinarith)
  have hA := tail_n (n := n) (lo := n / 40) (a := aA) (k := 800) (fun ω => -stA m ω) one_pos
    (fun x y => by
      rw [show -stA m x - -stA m y = -(stA m x - stA m y) by ring, abs_neg]; exact stA_lip m x y)
    (by norm_num) (by positivity) (by simp only [aA]; linarith) hNpos (by rw [hNr]; nlinarith)
  have hG := tail_n (n := n) (lo := n / 80) (a := aG) (k := 12800) (fun ω => -stG m ω) two_pos
    (fun x y => by
      rw [show -stG m x - -stG m y = -(stG m x - stG m y) by ring, abs_neg]; exact stG_lip m x y)
    (by norm_num) (by positivity) (by simp only [aG]; rw [hNr] at mG; linarith) hNpos (by rw [hNr]; nlinarith)
  calc ((univ.filter (fun ω : Fin N → Bool => ¬ GoodPt n ω)).card : ℝ)
      ≤ ((E1 ∪ E2 ∪ E3 ∪ E4).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ (E1.card : ℝ) + E2.card + E3.card + E4.card := by
        have h1 := Finset.card_union_le (E1 ∪ E2 ∪ E3) E4
        have h2 := Finset.card_union_le (E1 ∪ E2) E3
        have h3 := Finset.card_union_le E1 E2
        have : (E1 ∪ E2 ∪ E3 ∪ E4).card ≤ E1.card + E2.card + E3.card + E4.card := by omega
        exact_mod_cast this
    _ ≤ 3 * (2 ^ N * Real.exp (-(n : ℝ) / 20000)) := by
        have habs := exp_absorb (n := (n : ℝ)) (by exact_mod_cast hn6)
        have hP : (0 : ℝ) < 2 ^ N := by positivity
        have := mul_le_mul_of_nonneg_left habs hP.le
        simp only [E1, E2, E3, E4]; nlinarith

/-! ### Theorem 1 -/

/-- **Theorem 1 of the paper.** For every `n ≥ 1`, `4^(n-1) - f(n) ≤ 6 e^(-n/20000) 4^(n-1)`:
almost every pair of subsets of `{1, …, n-1}` is `(D(w), D(w⁻¹))` for some `w ∈ S_n`. -/
theorem density {n : ℕ} (hn : 1 ≤ n) :
    (4 : ℝ) ^ (n - 1) - f n ≤ 6 * Real.exp (-(n : ℝ) / 20000) * 4 ^ (n - 1) := by
  have h4 : (0 : ℝ) < 4 ^ (n - 1) := by positivity
  by_cases hsmall : n < 6000
  · have hf : (0 : ℝ) ≤ f n := Nat.cast_nonneg _
    have he : (1 : ℝ) / 6 ≤ Real.exp (-(n : ℝ) / 20000) := by
      have := Real.add_one_le_exp (-(n : ℝ) / 20000)
      have : (n : ℝ) < 6000 := by exact_mod_cast hsmall
      linarith
    nlinarith
  · push_neg at hsmall
    set N := n - 1
    set good := univ.filter (fun ω : Fin N → Bool => GoodPt n ω)
    set bad := univ.filter (fun ω : Fin N → Bool => ¬ GoodPt n ω)
    have hgb : (good.card : ℝ) + bad.card = 2 ^ N := by
      rw [← card_cube]
      exact_mod_cast Finset.card_filter_add_card_filter_not (s := univ) (p := GoodPt n)
    -- good × good injects into the occurring pairs
    have hf : (good.card : ℝ) * good.card ≤ f n := by
      have := Finset.card_le_card_of_injOn (fun q : (Fin N → Bool) × (Fin N → Bool) =>
          (toSet q.1, toSet q.2)) (s := good ×ˢ good) (t := pairs n)
        (fun q hq => by
          simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, good, Finset.mem_filter,
            Finset.mem_univ, true_and] at hq
          exact good_pair (by omega) (toSet_sub q.1) (toSet_sub q.2) hq.1 hq.2)
        (fun q _ q' _ h => by
          simp only [Prod.mk.injEq] at h
          exact Prod.ext (toSet_injective h.1) (toSet_injective h.2))
      rw [Finset.card_product] at this
      unfold f; exact_mod_cast this
    have hb := card_bad hsmall
    have h4N : (4 : ℝ) ^ (n - 1) = 2 ^ N * 2 ^ N := by
      show (4 : ℝ) ^ N = 2 ^ N * 2 ^ N
      rw [← mul_pow]; norm_num
    have hbn : (0 : ℝ) ≤ bad.card := Nat.cast_nonneg _
    have hP : (0 : ℝ) < 2 ^ N := by positivity
    rw [h4N]
    have hgood : (good.card : ℝ) = 2 ^ N - bad.card := by linarith
    rw [hgood] at hf
    nlinarith [mul_le_mul_of_nonneg_left hb hP.le]

/-- Theorem 1 as stated in the paper: `1 - f(n)/4^(n-1) ≤ C e^(-cn)` with `C = 6`, `c = 1/20000`. -/
theorem density_ratio {n : ℕ} (hn : 1 ≤ n) :
    1 - (f n : ℝ) / 4 ^ (n - 1) ≤ 6 * Real.exp (-(n : ℝ) / 20000) := by
  have h4 : (0 : ℝ) < 4 ^ (n - 1) := by positivity
  have := density hn
  rw [one_sub_div h4.ne', div_le_iff₀ h4]
  linarith

end Density

end Stanley
