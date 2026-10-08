/-
  Stanley, MathOverflow 486548. Theorem 1 with a better rate:
  `1 - f(n)/4^(n-1) ≤ 6 e^(-n/150)` for every `n ≥ 1`.

  Same construction as `Density` (Lemmas 3.1, 3.2 via `Fill.pair_of_fillings`), two changes in the
  probability:
  * the sizes enter only through the difference `|S| - |T|`, a function of `2(n-1)` fair bits
    (`diffCount`), instead of two separate deviations;
  * `G(X)` is controlled through the number of membership changes in the late window, which is at
    most `2 G(X) + 1` (`card_chg_le`). The change map `dmap` is a bijection of the cube, so the
    number of changes has the law of a count of fair bits (`chgCount`).
-/
import LeanProofs.Stanley.Density

namespace Stanley

namespace DensitySharp

open Finset Density

/-! ### Rises, falls and changes of a set in `[m+1, K)` -/

/-- Rises: `x ∈ X`, `x - 1 ∉ X`. -/
def ups (m K : ℕ) (X : Finset ℕ) : Finset ℕ := (Ico (m + 1) K).filter (fun x => x ∈ X ∧ x - 1 ∉ X)

/-- Falls: `x ∉ X`, `x - 1 ∈ X`. -/
def downs (m K : ℕ) (X : Finset ℕ) : Finset ℕ :=
  (Ico (m + 1) K).filter (fun x => x ∉ X ∧ x - 1 ∈ X)

/-- Changes of membership. -/
def chg (m K : ℕ) (X : Finset ℕ) : Finset ℕ :=
  (Ico (m + 1) K).filter (fun x => ¬ ((x ∈ X) ↔ (x - 1 ∈ X)))

theorem ups_sub_downs (m : ℕ) (X : Finset ℕ) : ∀ K, m + 1 ≤ K →
    ((ups m K X).card : ℤ) - (downs m K X).card =
      (if K - 1 ∈ X then 1 else 0) - (if m ∈ X then 1 else 0) := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => simp [ups, downs]
  | succ K hK ih =>
    have hI : Ico (m + 1) (K + 1) = insert K (Ico (m + 1) K) := by
      ext x; simp only [mem_Ico, mem_insert]; omega
    have hnot : K ∉ Ico (m + 1) K := by simp
    simp only [ups, downs, hI, filter_insert] at ih ⊢
    have hK1 : K + 1 - 1 = K := by omega
    rw [hK1]
    by_cases ha : K ∈ X <;> by_cases hb : K - 1 ∈ X <;>
      simp only [ha, hb, not_true_eq_false, not_false_eq_true, and_true, and_false, true_and,
        false_and, if_true, if_false] at ih ⊢ <;>
      first
        | (rw [card_insert_of_notMem (fun h => hnot (mem_filter.mp h).1)]; push_cast; linarith)
        | linarith

theorem card_chg (m K : ℕ) (X : Finset ℕ) :
    (chg m K X).card = (ups m K X).card + (downs m K X).card := by
  have he : chg m K X = ups m K X ∪ downs m K X := by
    ext x; simp only [chg, ups, downs, mem_filter, mem_union]; tauto
  have hd : Disjoint (ups m K X) (downs m K X) := by
    rw [disjoint_left]; intro x h1 h2
    exact (mem_filter.mp h2).2.1 (mem_filter.mp h1).2.1
  rw [he, card_union_of_disjoint hd]

/-- At most `2 G + 1` changes. -/
theorem card_chg_le (m K : ℕ) (X : Finset ℕ) :
    (chg m K X).card ≤ 2 * (ups m K X).card + 1 := by
  rw [card_chg]
  by_cases hK : m + 1 ≤ K
  · have := ups_sub_downs m X K hK
    split_ifs at this <;> omega
  · have : ups m K X = ∅ := by
      ext x; simp only [ups, mem_filter, mem_Ico, notMem_empty, iff_false]; omega
    have h2 : downs m K X = ∅ := by
      ext x; simp only [downs, mem_filter, mem_Ico, notMem_empty, iff_false]; omega
    simp [this, h2]

theorem setG_eq_ups (N m : ℕ) (X : Finset ℕ) : setG N m X = ups m N X := by
  ext x; simp only [setG, ups, mem_filter, mem_range, mem_Ico]; tauto

/-! ### The change map is a bijection of the cube -/

section Cube

variable {N : ℕ}

/-- Replace each late bit by its change from the previous bit. -/
def dmap (m : ℕ) (ω : Fin N → Bool) : Fin N → Bool :=
  fun i => if m + 1 ≤ i.1 then xor (ω i) (ω (prev i)) else ω i

theorem dmap_injective (m : ℕ) : Function.Injective (dmap (N := N) m) := by
  intro ω ω' h
  funext ⟨k, hk⟩
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hd := congrFun h ⟨k, hk⟩
    simp only [dmap] at hd
    split_ifs at hd with hm
    · have hp : ω (prev ⟨k, hk⟩) = ω' (prev ⟨k, hk⟩) := ih (k - 1) (by omega) (by omega)
      rw [hp] at hd
      simpa using hd
    · exact hd

theorem card_dmap (m : ℕ) (P : (Fin N → Bool) → Prop) [DecidablePred P] :
    (univ.filter (fun ω => P (dmap m ω))).card = (univ.filter P).card := by
  have hbij : Function.Bijective (dmap (N := N) m) :=
    (Finite.injective_iff_bijective).mp (dmap_injective m)
  apply card_bij (fun ω _ => dmap m ω)
  · intro ω hω; simpa using hω
  · intro a _ b _ h; exact dmap_injective m h
  · intro δ hδ
    obtain ⟨ω, rfl⟩ := hbij.2 δ
    exact ⟨ω, by simpa using hδ, rfl⟩

/-- Ones in the late window. -/
noncomputable def wcount (m : ℕ) (δ : Fin N → Bool) : ℝ := ∑ i, ind (m + 1 ≤ i.1 ∧ δ i = true)

theorem sum_wcount (m : ℕ) : ∑ δ : Fin N → Bool, wcount m δ =
    ((univ.filter (fun i : Fin N => m + 1 ≤ i.1)).card : ℝ) * (2 ^ N / 2) := by
  unfold wcount
  rw [Finset.sum_comm]
  have : ∀ i : Fin N, ∑ δ : Fin N → Bool, ind (m + 1 ≤ i.1 ∧ δ i = true) =
      ind (m + 1 ≤ i.1) * (2 ^ N / 2) := by
    intro i
    by_cases hi : m + 1 ≤ i.1
    · simp only [hi, true_and]; rw [sum_ind (fun δ : Fin N → Bool => δ i = true), card_coord]
      simp [ind]
    · simp [hi, ind]
  simp_rw [this, ← Finset.sum_mul, sum_ind_fin]

theorem wcount_lip (m : ℕ) (x y : Fin N → Bool) :
    |wcount m x - wcount m y| ≤ 1 * hammingDist x y := by
  rw [one_mul, hamming_eq]; unfold wcount
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
    abs_ind_coord x y i (fun i b => m + 1 ≤ i.1 ∧ b = true))

/-- The changes of `toSet ω` are the late ones of `dmap ω`. -/
theorem card_chg_toSet (m : ℕ) (ω : Fin N → Bool) :
    ((chg m N (toSet ω)).card : ℝ) = wcount m (dmap m ω) := by
  unfold wcount; rw [sum_ind_fin]
  congr 1
  apply Finset.card_bij (fun x hx => (⟨x, by
      simp only [chg, Finset.mem_filter, Finset.mem_Ico] at hx; omega⟩ : Fin N))
  · intro x hx
    simp only [chg, Finset.mem_filter, Finset.mem_Ico, mem_toSet] at hx
    obtain ⟨⟨hm, hxN⟩, hc⟩ := hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm, ?_⟩
    simp only [dmap]
    rw [if_pos hm]
    have hp : prev (⟨x, hxN⟩ : Fin N) = ⟨x - 1, by omega⟩ := rfl
    rw [hp]
    have e1 : (∃ h : x < N, ω ⟨x, h⟩ = true) ↔ ω ⟨x, hxN⟩ = true :=
      ⟨fun ⟨_, h⟩ => h, fun h => ⟨hxN, h⟩⟩
    have e2 : (∃ h : x - 1 < N, ω ⟨x - 1, h⟩ = true) ↔ ω ⟨x - 1, by omega⟩ = true :=
      ⟨fun ⟨_, h⟩ => h, fun h => ⟨by omega, h⟩⟩
    rw [e1, e2] at hc
    revert hc
    cases ω ⟨x, hxN⟩ <;> cases ω ⟨x - 1, by omega⟩ <;> simp
  · intro a _ b _ h; simpa using h
  · intro i hi
    obtain ⟨hm, hx⟩ := (Finset.mem_filter.mp hi).2
    simp only [dmap] at hx
    rw [if_pos hm] at hx
    refine ⟨i.1, ?_, rfl⟩
    simp only [chg, Finset.mem_filter, Finset.mem_Ico, mem_toSet]
    refine ⟨⟨hm, i.2⟩, ?_⟩
    have hp : prev i = ⟨i.1 - 1, by omega⟩ := rfl
    rw [hp] at hx
    have e1 : (∃ h : i.1 < N, ω ⟨i.1, h⟩ = true) ↔ ω i = true :=
      ⟨fun ⟨_, h⟩ => h, fun h => ⟨i.2, h⟩⟩
    have e2 : (∃ h : i.1 - 1 < N, ω ⟨i.1 - 1, h⟩ = true) ↔ ω ⟨i.1 - 1, by omega⟩ = true :=
      ⟨fun ⟨_, h⟩ => h, fun h => ⟨by omega, h⟩⟩
    rw [e1, e2]
    revert hx
    cases ω i <;> cases ω ⟨i.1 - 1, by omega⟩ <;> simp

/-! ### The size difference on the doubled cube -/

/-- `|S| - |T|` as a function of `2N` bits. -/
noncomputable def dsz (ω : Fin (N + N) → Bool) : ℝ :=
  ∑ i : Fin N, ind (ω (Fin.castAdd N i) = true) - ∑ i : Fin N, ind (ω (Fin.natAdd N i) = true)

theorem dsz_append (ω₁ ω₂ : Fin N → Bool) : dsz (Fin.append ω₁ ω₂) = sz ω₁ - sz ω₂ := by
  simp only [dsz, sz, Fin.append_left, Fin.append_right]

theorem dsz_lip (x y : Fin (N + N) → Bool) : |dsz x - dsz y| ≤ 1 * hammingDist x y := by
  rw [one_mul, hamming_eq, Fin.sum_univ_add]
  unfold dsz
  have h1 := Finset.abs_sum_le_sum_abs (fun i : Fin N =>
    ind (x (Fin.castAdd N i) = true) - ind (y (Fin.castAdd N i) = true)) univ
  have h2 := Finset.abs_sum_le_sum_abs (fun i : Fin N =>
    ind (x (Fin.natAdd N i) = true) - ind (y (Fin.natAdd N i) = true)) univ
  have h3 : ∑ i : Fin N, |ind (x (Fin.castAdd N i) = true) - ind (y (Fin.castAdd N i) = true)| ≤
      ∑ i : Fin N, ind (x (Fin.castAdd N i) ≠ y (Fin.castAdd N i)) :=
    Finset.sum_le_sum fun i _ => abs_ind_coord x y (Fin.castAdd N i) (fun _ b => b = true)
  have h4 : ∑ i : Fin N, |ind (x (Fin.natAdd N i) = true) - ind (y (Fin.natAdd N i) = true)| ≤
      ∑ i : Fin N, ind (x (Fin.natAdd N i) ≠ y (Fin.natAdd N i)) :=
    Finset.sum_le_sum fun i _ => abs_ind_coord x y (Fin.natAdd N i) (fun _ b => b = true)
  rw [Finset.sum_sub_distrib] at h1 h2
  have := abs_sub (∑ i : Fin N, ind (x (Fin.castAdd N i) = true) -
      ∑ i : Fin N, ind (y (Fin.castAdd N i) = true))
    (∑ i : Fin N, ind (x (Fin.natAdd N i) = true) - ∑ i : Fin N, ind (y (Fin.natAdd N i) = true))
  calc _ = |(∑ i : Fin N, ind (x (Fin.castAdd N i) = true) -
          ∑ i : Fin N, ind (y (Fin.castAdd N i) = true)) -
        (∑ i : Fin N, ind (x (Fin.natAdd N i) = true) -
          ∑ i : Fin N, ind (y (Fin.natAdd N i) = true))| := by ring_nf
    _ ≤ _ := by linarith

theorem sum_dsz : ∑ ω : Fin (N + N) → Bool, dsz ω = 0 := by
  have hc : ∀ j : Fin (N + N), ∑ ω : Fin (N + N) → Bool, ind (ω j = true) = 2 ^ (N + N) / 2 := by
    intro j; rw [sum_ind (fun ω : Fin (N + N) → Bool => ω j = true), card_coord]
  have h1 : ∑ ω : Fin (N + N) → Bool, ∑ i : Fin N, ind (ω (Fin.castAdd N i) = true) =
      N * (2 ^ (N + N) / 2) := by
    rw [Finset.sum_comm]; simp [hc]
  have h2 : ∑ ω : Fin (N + N) → Bool, ∑ i : Fin N, ind (ω (Fin.natAdd N i) = true) =
      N * (2 ^ (N + N) / 2) := by
    rw [Finset.sum_comm]; simp [hc]
  unfold dsz
  rw [Finset.sum_sub_distrib, h1, h2, sub_self]

/-- **The size difference is concentrated.** -/
theorem diffCount {n : ℕ} (hn : 2 ≤ n) (hN : N = n - 1) :
    ((univ.filter (fun q : (Fin N → Bool) × (Fin N → Bool) =>
      (n : ℝ) / 12 < sz q.1 - sz q.2)).card : ℝ) ≤ 4 ^ N * Real.exp (-(n : ℝ) / 150) := by
  have hNr : (N : ℝ) = n - 1 := by rw [hN]; push_cast [show 1 ≤ n by omega]; ring
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hinj := Finset.card_le_card_of_injOn (fun q : (Fin N → Bool) × (Fin N → Bool) =>
      Fin.append q.1 q.2)
    (s := univ.filter (fun q : (Fin N → Bool) × (Fin N → Bool) => (n : ℝ) / 12 < sz q.1 - sz q.2))
    (t := univ.filter (fun ω : Fin (N + N) → Bool =>
      (n : ℝ) / 12 < dsz ω - (∑ ω' : Fin (N + N) → Bool, dsz ω') * (1 / 2) ^ (N + N)))
    (fun q hq => by
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hq ⊢
      rw [sum_dsz (N := N), zero_mul, sub_zero, dsz_append]; exact hq)
    (fun q _ q' _ h => by
      have h1 := congrArg (fun ω => fun i => ω (Fin.castAdd N i)) h
      have h2 := congrArg (fun ω => fun i => ω (Fin.natAdd N i)) h
      simp only [Fin.append_left, Fin.append_right] at h1 h2
      exact Prod.ext h1 h2)
  have ht := tail_n (N := N + N) (n := n) (lo := n / 12) (a := n / 12) (k := 150) dsz one_pos
    dsz_lip (by norm_num) (by positivity) le_rfl (by push_cast; rw [hNr]; linarith)
    (by push_cast; rw [hNr]; nlinarith)
  have h4 : (2 : ℝ) ^ (N + N) = 4 ^ N := by rw [pow_add, ← mul_pow]; norm_num
  rw [h4] at ht
  calc _ ≤ _ := by exact_mod_cast hinj
    _ ≤ _ := ht

end Cube

/-! ### Good sets and good pairs -/

/-- The two conditions on a break set, with `m = ⌊n/2⌋`. -/
def GoodSet (n : ℕ) (X : Finset ℕ) : Prop :=
  (n : ℝ) / 12 + 1 ≤ (setA (n / 2) X).card ∧ (n : ℝ) / 12 + 2 ≤ (setG (n - 1) (n / 2) X).card

theorem good_pair_lt {n : ℕ} {S T : Finset ℕ} (hS : S ⊆ range (n - 1))
    (hT : T ⊆ range (n - 1)) (gS : GoodSet n S) (gT : GoodSet n T)
    (hdiff : (T.card : ℝ) - S.card ≤ n / 12) (hlt : S.card < T.card) :
    (S, T) ∈ pairs n := by
  obtain ⟨hAS, hGS⟩ := gS
  obtain ⟨hAT, hGT⟩ := gT
  have hd : ((T.card - S.card : ℕ) : ℝ) = T.card - S.card := by
    push_cast [Nat.cast_sub hlt.le]; ring
  have hC := setG_le_exC (n := n) (m := n / 2) (X := S)
  have hG := setG_le_tsG (n := n) (m := n / 2) (X := T)
  have hsub : ((setG (n - 1) (n / 2) S).card : ℝ) ≤ S.card := by
    exact_mod_cast card_le_card setG_sub
  apply Fill.pair_of_fillings (m := n / 2) hS hT
  · have : (1 : ℝ) ≤ S.card := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    exact_mod_cast this
  · exact hlt
  · have : ((T.card - S.card : ℕ) : ℝ) + 1 ≤ (setA (n / 2) S).card := by rw [hd]; linarith
    exact_mod_cast this
  · have : ((T.card - S.card : ℕ) : ℝ) + 1 ≤ (setA (n / 2) T).card := by rw [hd]; linarith
    exact_mod_cast this
  · have hC' : ((setG (n - 1) (n / 2) S).card : ℝ) ≤ (Fill.exC n (n / 2) S).card + 2 := by
      exact_mod_cast hC
    have : ((T.card - S.card : ℕ) : ℝ) ≤ (Fill.exC n (n / 2) S).card := by rw [hd]; linarith
    exact_mod_cast this
  · have hG' : ((setG (n - 1) (n / 2) T).card : ℝ) ≤ (Fill.tsG n (n / 2) T).card + 1 := by
      exact_mod_cast hG
    have : ((T.card - S.card : ℕ) : ℝ) ≤ (Fill.tsG n (n / 2) T).card := by rw [hd]; linarith
    exact_mod_cast this

/-- **Two good sets of close sizes form an occurring pair.** -/
theorem good_pair {n : ℕ} {S T : Finset ℕ} (hS : S ⊆ range (n - 1))
    (hT : T ⊆ range (n - 1)) (gS : GoodSet n S) (gT : GoodSet n T)
    (hdiff : |(S.card : ℝ) - T.card| ≤ n / 12) : (S, T) ∈ pairs n := by
  rcases lt_trichotomy S.card T.card with h | h | h
  · exact good_pair_lt hS hT gS gT (by have := (abs_le.mp hdiff).1; linarith) h
  · exact mem_pairs hS hT h
  · exact pairs_symm (good_pair_lt hT hS gT gS (by have := (abs_le.mp hdiff).2; linarith) h)

/-- A good cube point. -/
def GoodPt (n : ℕ) (ω : Fin (n - 1) → Bool) : Prop := GoodSet n (toSet ω)

noncomputable instance (n : ℕ) : DecidablePred (GoodPt n) := fun _ => Classical.dec _

/-! ### Counting -/

theorem card_bad {n : ℕ} (hn : 240 ≤ n) :
    ((univ.filter (fun ω : Fin (n - 1) → Bool => ¬ GoodPt n ω)).card : ℝ) ≤
      2 * (2 ^ (n - 1) * Real.exp (-(n : ℝ) / 150)) := by
  set N := n - 1 with hNdef
  set m := n / 2 with hm
  have hn' : (240 : ℝ) ≤ n := by exact_mod_cast hn
  have hNr : (N : ℝ) = n - 1 := by rw [hNdef]; push_cast [show 1 ≤ n by omega]; ring
  have hNpos : (0 : ℝ) < N := by rw [hNr]; linarith
  have hm2 : (n : ℝ) - 1 ≤ 2 * (m : ℝ) := by
    have : n ≤ 2 * m + 1 := by omega
    have : (n : ℝ) ≤ 2 * m + 1 := by exact_mod_cast this
    linarith
  have hm3 : 2 * (m : ℝ) ≤ n := by
    have : 2 * m ≤ n := by omega
    exact_mod_cast this
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
  have mW : (N : ℝ) - m - 1 ≤ 2 * ((∑ δ : Fin N → Bool, wcount m δ) * (1 / 2) ^ N) := by
    rw [sum_wcount, mul_assoc, half_pow]
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
  set aA := (∑ ω : Fin N → Bool, stA m ω) * (1 / 2) ^ N - (n / 12 + 1)
  set E1 := univ.filter (fun ω : Fin N → Bool =>
    aA < (fun ω => -stA m ω) ω - (∑ ω', (fun ω => -stA m ω) ω') * (1 / 2) ^ N)
  set aW := (∑ δ : Fin N → Bool, wcount m δ) * (1 / 2) ^ N - (n / 6 + 5)
  set PW : (Fin N → Bool) → Prop := fun δ =>
    aW < (fun δ => -wcount m δ) δ - (∑ δ', (fun δ => -wcount m δ) δ') * (1 / 2) ^ N
  set E2 := univ.filter (fun ω : Fin N → Bool => PW (dmap m ω))
  have hsub : univ.filter (fun ω : Fin N → Bool => ¬ GoodPt n ω) ⊆ E1 ∪ E2 := by
    intro ω hω0
    have hω : ¬ GoodPt n ω := (Finset.mem_filter.mp hω0).2
    unfold GoodPt GoodSet at hω
    rw [card_setA (by omega), ← hm] at hω
    simp only [E1, E2, PW, aA, aW, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.sum_neg_distrib, neg_mul]
    by_contra hc
    push Not at hc
    apply hω
    obtain ⟨hc1, hc2⟩ := hc
    generalize (∑ x : Fin N → Bool, stA m x) * (1 / 2) ^ N = MA at hc1
    generalize (∑ x : Fin N → Bool, wcount m x) * (1 / 2) ^ N = MW at hc2
    refine ⟨by linarith, ?_⟩
    have hchg : ((chg m N (toSet ω)).card : ℝ) ≤ 2 * (setG (n - 1) m (toSet ω)).card + 1 := by
      rw [setG_eq_ups]; exact_mod_cast card_chg_le m N (toSet ω)
    rw [card_chg_toSet] at hchg
    linarith
  have hA := tail_n (n := n) (lo := n / 6 - 7 / 4) (a := aA) (k := 150) (fun ω => -stA m ω)
    one_pos
    (fun x y => by
      rw [show -stA m x - -stA m y = -(stA m x - stA m y) by ring, abs_neg]; exact stA_lip m x y)
    (by norm_num) (by linarith) (by simp only [aA]; linarith) hNpos (by rw [hNr]; nlinarith)
  have hWlo : (0 : ℝ) < n / 12 - 6 := by linarith
  have hWa : (n : ℝ) / 12 - 6 ≤ aW := by
    have h1 := mW; rw [hNr] at h1
    simp only [aW]; linarith
  have hWkey : (n : ℝ) * N * 1 ^ 2 ≤ 2 * 150 * (n / 12 - 6) ^ 2 := by
    rw [hNr]; nlinarith [mul_nonneg (sub_nonneg.mpr hn') (sub_nonneg.mpr hn')]
  have hW := tail_n (n := n) (lo := n / 12 - 6) (a := aW) (k := 150) (fun δ => -wcount m δ)
    one_pos
    (fun x y => by
      rw [show -wcount m x - -wcount m y = -(wcount m x - wcount m y) by ring, abs_neg]
      exact wcount_lip m x y)
    (by norm_num) hWlo hWa hNpos hWkey
  have hE2 : (E2.card : ℝ) = (univ.filter PW).card := by
    exact_mod_cast card_dmap m PW
  calc ((univ.filter (fun ω : Fin N → Bool => ¬ GoodPt n ω)).card : ℝ)
      ≤ ((E1 ∪ E2).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
    _ ≤ (E1.card : ℝ) + E2.card := by exact_mod_cast Finset.card_union_le E1 E2
    _ ≤ 2 * (2 ^ N * Real.exp (-(n : ℝ) / 150)) := by
        rw [hE2]; simp only [E1, PW] at hA hW ⊢; linarith

/-! ### Theorem 1 with rate `1/150` -/

theorem small_case {n : ℕ} (h : n < 240) : (1 : ℝ) / 6 ≤ Real.exp (-(n : ℝ) / 150) := by
  have h1 : (0.8 : ℝ) ≤ Real.exp (-0.2) := by
    have := Real.add_one_le_exp (-0.2 : ℝ); linarith
  have h2 : Real.exp (-0.2) ^ 8 ≤ Real.exp (-(n : ℝ) / 150) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : (n : ℝ) < 240 := by exact_mod_cast h
    norm_num; linarith
  have h3 : (0.8 : ℝ) ^ 8 ≤ Real.exp (-0.2) ^ 8 := pow_le_pow_left₀ (by norm_num) h1 8
  have h4 : (1 : ℝ) / 6 ≤ 0.8 ^ 8 := by norm_num
  linarith

/-- **Theorem 1, rate `1/150`.** For every `n ≥ 1`, `4^(n-1) - f(n) ≤ 6 e^(-n/150) 4^(n-1)`. -/
theorem density {n : ℕ} (hn : 1 ≤ n) :
    (4 : ℝ) ^ (n - 1) - f n ≤ 6 * Real.exp (-(n : ℝ) / 150) * 4 ^ (n - 1) := by
  have h4 : (0 : ℝ) < 4 ^ (n - 1) := by positivity
  by_cases hsmall : n < 240
  · have hf : (0 : ℝ) ≤ f n := Nat.cast_nonneg _
    have he := small_case hsmall
    nlinarith
  · push Not at hsmall
    set N := n - 1 with hNdef
    set e := Real.exp (-(n : ℝ) / 150)
    set C := (univ : Finset ((Fin N → Bool) × (Fin N → Bool)))
    set good := C.filter (fun q => GoodPt n q.1 ∧ GoodPt n q.2 ∧ |sz q.1 - sz q.2| ≤ n / 12)
    set bad := univ.filter (fun ω : Fin N → Bool => ¬ GoodPt n ω)
    set D1 := C.filter (fun q => (n : ℝ) / 12 < sz q.1 - sz q.2)
    set D2 := C.filter (fun q => (n : ℝ) / 12 < sz q.2 - sz q.1)
    -- good pairs inject into the occurring pairs
    have hf : (good.card : ℝ) ≤ f n := by
      have := Finset.card_le_card_of_injOn (fun q : (Fin N → Bool) × (Fin N → Bool) =>
          (toSet q.1, toSet q.2)) (s := good) (t := pairs n)
        (fun q hq => by
          simp only [coe_filter, Set.mem_setOf_eq, good, C, mem_univ, true_and] at hq
          obtain ⟨g1, g2, hd⟩ := hq
          refine good_pair (toSet_sub q.1) (toSet_sub q.2) g1 g2 ?_
          rw [card_toSet, card_toSet]; exact hd)
        (fun q _ q' _ h => by
          simp only [Prod.mk.injEq] at h
          exact Prod.ext (toSet_injective h.1) (toSet_injective h.2))
      unfold f; exact_mod_cast this
    -- the complement of `good` is small
    have hcov : C ⊆ good ∪ (bad ×ˢ univ ∪ (univ ×ˢ bad ∪ (D1 ∪ D2))) := by
      intro q _
      simp only [good, bad, D1, D2, C, mem_union, mem_filter, mem_product, mem_univ, true_and,
        and_true]
      by_cases g1 : GoodPt n q.1
      · by_cases g2 : GoodPt n q.2
        · by_cases hd : |sz q.1 - sz q.2| ≤ n / 12
          · exact Or.inl ⟨g1, g2, hd⟩
          · right; right; right
            rcases lt_abs.mp (not_le.mp hd) with h | h
            · exact Or.inl h
            · exact Or.inr (by linarith)
        · exact Or.inr (Or.inr (Or.inl g2))
      · exact Or.inr (Or.inl g1)
    have hCc : (C.card : ℝ) = 4 ^ N := by
      simp only [C, card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin]
      push_cast; rw [← mul_pow]; norm_num
    have hD1 := diffCount (N := N) (n := n) (by omega) rfl
    have hD2 : (D2.card : ℝ) = D1.card := by
      have : D2.card = D1.card := by
        apply card_bij (fun q _ => (q.2, q.1))
        · intro q hq; simp only [D1, D2, C, mem_filter, mem_univ, true_and] at hq ⊢; exact hq
        · intro a _ b _ h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
        · intro q hq
          refine ⟨(q.2, q.1), ?_, rfl⟩
          simp only [D1, D2, C, mem_filter, mem_univ, true_and] at hq ⊢
          exact hq
      exact_mod_cast this
    have hb := card_bad hsmall
    have hbadprod : ((bad ×ˢ (univ : Finset (Fin N → Bool))).card : ℝ) = bad.card * 2 ^ N := by
      rw [card_product]; push_cast; rw [card_cube]
    have hbadprod' : (((univ : Finset (Fin N → Bool)) ×ˢ bad).card : ℝ) = 2 ^ N * bad.card := by
      rw [card_product]; push_cast; rw [card_cube]
    have hsum : (C.card : ℝ) ≤ good.card + (bad.card * 2 ^ N + (2 ^ N * bad.card +
        (D1.card + D2.card))) := by
      have h := card_le_card hcov
      have h1 := card_union_le good (bad ×ˢ univ ∪ (univ ×ˢ bad ∪ (D1 ∪ D2)))
      have h2 := card_union_le (bad ×ˢ (univ : Finset (Fin N → Bool))) (univ ×ˢ bad ∪ (D1 ∪ D2))
      have h3 := card_union_le ((univ : Finset (Fin N → Bool)) ×ˢ bad) (D1 ∪ D2)
      have h4 := card_union_le D1 D2
      have : C.card ≤ good.card + ((bad ×ˢ (univ : Finset (Fin N → Bool))).card +
          (((univ : Finset (Fin N → Bool)) ×ˢ bad).card + (D1.card + D2.card))) := by omega
      have h' : ((C.card : ℕ) : ℝ) ≤ ((good.card + ((bad ×ˢ (univ : Finset (Fin N → Bool))).card +
          (((univ : Finset (Fin N → Bool)) ×ˢ bad).card + (D1.card + D2.card))) : ℕ) : ℝ) := by
        exact_mod_cast this
      push_cast at h'
      rw [hbadprod, hbadprod'] at h'
      exact h'
    have h4N : (4 : ℝ) ^ N = 2 ^ N * 2 ^ N := by rw [← mul_pow]; norm_num
    have hP : (0 : ℝ) < 2 ^ N := by positivity
    have hbn : (0 : ℝ) ≤ bad.card := Nat.cast_nonneg _
    rw [hCc] at hsum
    show (4 : ℝ) ^ N - f n ≤ 6 * e * 4 ^ N
    have hbb : (bad.card : ℝ) * 2 ^ N ≤ 2 * (2 ^ N * e) * 2 ^ N :=
      mul_le_mul_of_nonneg_right hb hP.le
    rw [h4N] at hsum hD1 ⊢
    nlinarith

/-- **Theorem 1 with rate `1/150`:** `1 - f(n)/4^(n-1) ≤ 6 e^(-n/150)` for every `n ≥ 1`. -/
theorem density_ratio {n : ℕ} (hn : 1 ≤ n) :
    1 - (f n : ℝ) / 4 ^ (n - 1) ≤ 6 * Real.exp (-(n : ℝ) / 150) := by
  have h4 : (0 : ℝ) < 4 ^ (n - 1) := by positivity
  have := density hn
  rw [one_sub_div h4.ne', div_le_iff₀ h4]
  linarith

end DensitySharp

end Stanley
