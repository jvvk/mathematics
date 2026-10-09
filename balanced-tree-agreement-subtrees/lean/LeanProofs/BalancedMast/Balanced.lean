import LeanProofs.BalancedMast.Subst

/-!
# Balanced trees, `M(2^m)`, submultiplicativity and the exponent (Theorem 1.1(1))

`Bal h S`: every leaf of `S` is at depth `h`, so `S` has `2^h` leaves.
`M h` is the least `mast S T` over balanced phylogenetic `S, T` of height `h` on one label set
(labels in `ℕ`), that is, `M(2^h)` in the note.
-/

open Filter Topology

namespace BalancedMast

open Tree

/-- `S` is balanced of height `h`. -/
inductive Bal {α : Type*} : ℕ → Tree α → Prop
  | leaf (a : α) : Bal 0 (Tree.leaf a)
  | node {h : ℕ} {l r : Tree α} : Bal h l → Bal h r → Bal (h + 1) (Tree.node l r)

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

lemma Bal.length_labels {h : ℕ} {S : Tree α} (hS : Bal h S) : S.labels.length = 2 ^ h := by
  induction hS with
  | leaf a => simp [labels]
  | node _ _ ihl ihr => simp [labels, ihl, ihr, pow_succ, mul_two]

lemma Bal.card_L {h : ℕ} {S : Tree α} (hS : Bal h S) (hp : S.Phylo) : S.L.card = 2 ^ h := by
  rw [L, List.toFinset_card_of_nodup hp, hS.length_labels]

lemma Bal.bind {h k : ℕ} {S : Tree α} {A : α → Tree β} (hS : Bal h S)
    (hA : ∀ z ∈ S.L, Bal k (A z)) : Bal (h + k) (S.bind A) := by
  induction hS with
  | leaf a => simpa [Tree.bind] using hA a (by simp)
  | @node h l r _ _ ihl ihr =>
    have := Bal.node (ihl fun z hz => hA z (by simp [hz])) (ihr fun z hz => hA z (by simp [hz]))
    rwa [show h + k + 1 = h + 1 + k by omega] at this

/-! ## Relabelling -/

lemma mem_L_map {f : α → β} {S : Tree α} {x : β} : x ∈ (S.map f).L ↔ ∃ z ∈ S.L, f z = x := by
  simp [Tree.map, mem_L_bind, eq_comm]

lemma blocksDisjoint_map {f : α → β} {S : Tree α} (hf : Set.InjOn f S.L) :
    S.BlocksDisjoint fun z => leaf (f z) := by
  intro z hz z' hz' hne
  simpa using fun h => hne (hf hz hz' h)

lemma Bal.map {h : ℕ} {S : Tree α} (hS : Bal h S) (f : α → β) : Bal h (S.map f) := by
  rw [Tree.map]
  simpa using hS.bind (k := 0) (A := fun z => Tree.leaf (f z)) fun z _ => Bal.leaf (f z)

lemma phylo_map {f : α → β} {S : Tree α} (hf : Set.InjOn f S.L) (hS : S.Phylo) :
    (S.map f).Phylo :=
  phylo_bind hS (fun _ _ => by simp [Phylo, labels]) (blocksDisjoint_map hf)

/-- Relabelling preserves triples of distinct labels. -/
lemma displays_map {f : α → β} {S : Tree α} (hf : Set.InjOn f S.L) {x y z : α} (hx : x ∈ S.L)
    (hy : y ∈ S.L) (hz : z ∈ S.L) (hxy : x ≠ y) :
    (S.map f).Displays (f x) (f y) (f z) ↔ S.Displays x y z :=
  displays_bind_skeleton (blocksDisjoint_map hf) hx hy hz hxy (by simp) (by simp) (by simp)

/-- Relabelling by an injective map does not increase `mast`. -/
lemma mast_map_le {f : α → β} {S T : Tree α} (hf : Set.InjOn f S.L) (hL : S.L = T.L) :
    mast (S.map f) (T.map f) ≤ mast S T := by
  rw [Tree.map, Tree.map]
  simpa using mast_bind_le (A := fun z => leaf (f z)) (B := fun z => leaf (f z)) hL
    (blocksDisjoint_map hf) (fun _ _ => rfl) (K := 1)
    (fun z _ => (mast_le_card_inter _ _).trans (by simp))

/-! ## The standard balanced tree -/

/-- The balanced tree of height `h` with labels `o, o+1, …, o+2^h-1` from left to right. -/
def std : ℕ → ℕ → Tree ℕ
  | 0, o => leaf o
  | h + 1, o => node (std h o) (std h (o + 2 ^ h))

lemma labels_std (h o : ℕ) : (std h o).labels = List.range' o (2 ^ h) := by
  induction h generalizing o with
  | zero => simp [std, labels]
  | succ h ih => simp [std, labels, ih, pow_succ, mul_two]

lemma bal_std (h o : ℕ) : Bal h (std h o) := by
  induction h generalizing o with
  | zero => exact Bal.leaf o
  | succ h ih => exact Bal.node (ih _) (ih _)

lemma phylo_std (h o : ℕ) : (std h o).Phylo := by
  rw [Phylo, labels_std]; exact List.nodup_range'

lemma mem_L_std {h o x : ℕ} : x ∈ (std h o).L ↔ o ≤ x ∧ x < o + 2 ^ h := by
  rw [mem_L, labels_std, List.mem_range'_1]

/-! ## `M` -/

/-- The values of `mast` over pairs of balanced phylogenetic trees of height `h` on a common
label set. -/
def Pairs (h : ℕ) : Set ℕ :=
  {m | ∃ S T : Tree ℕ, Bal h S ∧ Bal h T ∧ S.Phylo ∧ T.Phylo ∧ S.L = T.L ∧ mast S T = m}

/-- `M h` is `M(2^h)` of the note. -/
noncomputable def M (h : ℕ) : ℕ := sInf (Pairs h)

lemma pairs_nonempty (h : ℕ) : (Pairs h).Nonempty :=
  ⟨_, std h 0, std h 0, bal_std h 0, bal_std h 0, phylo_std h 0, phylo_std h 0, rfl, rfl⟩

lemma M_mem (h : ℕ) : M h ∈ Pairs h := Nat.sInf_mem (pairs_nonempty h)

lemma M_le {h : ℕ} {S T : Tree ℕ} (hS : Bal h S) (hT : Bal h T) (pS : S.Phylo) (pT : T.Phylo)
    (hL : S.L = T.L) : M h ≤ mast S T :=
  Nat.sInf_le ⟨S, T, hS, hT, pS, pT, hL, rfl⟩

lemma one_le_mast {S T : Tree α} (h : (S.L ∩ T.L).Nonempty) : 1 ≤ mast S T := by
  obtain ⟨x, hx⟩ := h
  simpa using le_mast (agree_of_card_le_two (S := S) (T := T) (Y := {x})
    (Finset.singleton_subset_iff.2 hx) (by simp))

lemma one_le_M (h : ℕ) : 1 ≤ M h := by
  obtain ⟨S, T, _, _, _, _, hL, hm⟩ := M_mem h
  rw [← hm]; apply one_le_mast; rw [← hL, Finset.inter_self]; exact S.L_nonempty

lemma M_le_two_pow (h : ℕ) : M h ≤ 2 ^ h := by
  refine (M_le (bal_std h 0) (bal_std h 0) (phylo_std h 0) (phylo_std h 0) rfl).trans ?_
  refine (mast_le_card_inter _ _).trans ?_
  rw [Finset.inter_self, (bal_std h 0).card_L (phylo_std h 0)]

/-- **Corollary 3.2.** `M(2^(h+k)) ≤ M(2^h) M(2^k)`. -/
theorem M_add_le (h k : ℕ) : M (h + k) ≤ M h * M k := by
  obtain ⟨S, T, hS, hT, pS, pT, hL, hm⟩ := M_mem h
  obtain ⟨A₀, B₀, hA₀, hB₀, pA₀, pB₀, hL₀, hm₀⟩ := M_mem k
  set A : ℕ → Tree ℕ := fun z => A₀.map (Nat.pair z)
  set B : ℕ → Tree ℕ := fun z => B₀.map (Nat.pair z)
  have inj : ∀ z, Function.Injective (Nat.pair z) := fun z x y hxy => by
    simpa using congrArg (fun n => (Nat.unpair n).2) hxy
  have hAB : ∀ z, (A z).L = (B z).L := fun z => by
    ext x; simp only [A, B, mem_L_map, hL₀]
  have hdA : ∀ U : Tree ℕ, U.BlocksDisjoint A := by
    intro U z _ z' _ hne
    refine Finset.disjoint_left.2 fun x hx hx' => hne ?_
    obtain ⟨y, _, rfl⟩ := mem_L_map.1 hx
    obtain ⟨y', _, hy'⟩ := mem_L_map.1 hx'
    simpa using congrArg (fun n => (Nat.unpair n).1) hy'.symm
  have hdB : ∀ U : Tree ℕ, U.BlocksDisjoint B := by
    intro U z hz z' hz' hne; rw [← hAB, ← hAB]; exact hdA U z hz z' hz' hne
  have hLb : (S.bind A).L = (T.bind B).L := by
    ext x; simp only [mem_L_bind, hL, hAB]
  refine (M_le (hS.bind fun z _ => hA₀.map _) (hT.bind fun z _ => hB₀.map _)
    (phylo_bind pS (fun z _ => phylo_map (inj z).injOn pA₀) (hdA S))
    (phylo_bind pT (fun z _ => phylo_map (inj z).injOn pB₀) (hdB T)) hLb).trans ?_
  rw [← hm, ← hm₀]
  exact mast_bind_le hL (hdA S) (fun z _ => hAB z) fun z _ => mast_map_le (inj z).injOn hL₀

/-! ## The exponent exists (Fekete) -/

/-- `log₂ M(2^m)`. -/
noncomputable def u (m : ℕ) : ℝ := Real.logb 2 (M m)

lemma M_pos (m : ℕ) : (0 : ℝ) < M m := by
  have := one_le_M m; positivity

lemma u_nonneg (m : ℕ) : 0 ≤ u m :=
  Real.logb_nonneg (by norm_num) (by exact_mod_cast one_le_M m)

lemma u_subadditive : Subadditive u := by
  intro m n
  unfold u
  rw [← Real.logb_mul (M_pos m).ne' (M_pos n).ne']
  exact Real.logb_le_logb_of_le (by norm_num) (M_pos _) (by exact_mod_cast M_add_le m n)

lemma u_bddBelow : BddBelow (Set.range fun n : ℕ => u n / n) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (u_nonneg n) (Nat.cast_nonneg n)⟩

/-- The exponent `β = inf_{m ≥ 1} log₂ M(2^m) / m`. -/
noncomputable def beta : ℝ := sInf ((fun m : ℕ => u m / m) '' Set.Ici 1)

lemma beta_eq_lim : beta = u_subadditive.lim := by
  rw [Subadditive.lim]; rfl

/-- **Theorem 1.1(1).** `log₂ M(2^m) / m → β`. -/
theorem tendsto_beta : Tendsto (fun m : ℕ => Real.logb 2 (M m) / m) atTop (𝓝 beta) := by
  rw [beta_eq_lim]; exact u_subadditive.tendsto_lim u_bddBelow

lemma beta_le (m : ℕ) (hm : m ≠ 0) : beta ≤ Real.logb 2 (M m) / m := by
  rw [beta_eq_lim]; exact u_subadditive.lim_le_div u_bddBelow hm

/-! ## From one example to every `n` (Theorem 1.1(2), given `M(2^11) ≤ 2^5`) -/

lemma M_mul_le (h k : ℕ) : M (h * k) ≤ M h ^ k := by
  induction k with
  | zero => simpa using M_le_two_pow 0
  | succ k ih =>
    calc M (h * (k + 1)) = M (h * k + h) := by rw [Nat.mul_succ]
      _ ≤ M (h * k) * M h := M_add_le _ _
      _ ≤ M h ^ k * M h := Nat.mul_le_mul_right _ ih
      _ = M h ^ (k + 1) := (pow_succ _ _).symm

theorem M_le_of_M11 (h11 : M 11 ≤ 2 ^ 5) (m : ℕ) :
    (M m : ℝ) ≤ 2 ^ 10 * (2 : ℝ) ^ ((5 : ℝ) * m / 11) := by
  set j := m / 11
  set r := m % 11
  have hm : m = 11 * j + r := (Nat.div_add_mod m 11).symm
  have hr : r < 11 := Nat.mod_lt _ (by norm_num)
  have hN : M m ≤ 2 ^ (5 * j + r) := by
    calc M m = M (11 * j + r) := by rw [← hm]
      _ ≤ M (11 * j) * M r := M_add_le _ _
      _ ≤ (2 ^ 5) ^ j * 2 ^ r :=
        Nat.mul_le_mul ((M_mul_le 11 j).trans (Nat.pow_le_pow_left h11 j)) (M_le_two_pow r)
      _ = 2 ^ (5 * j + r) := by rw [← pow_mul, ← pow_add]
  have hR : ((5 * j + r : ℕ) : ℝ) ≤ 10 + 5 * m / 11 := by
    have : (r : ℝ) ≤ 10 := by exact_mod_cast Nat.lt_succ_iff.1 hr
    rw [hm]; push_cast; linarith
  calc (M m : ℝ) ≤ ((2 ^ (5 * j + r) : ℕ) : ℝ) := by exact_mod_cast hN
    _ = (2 : ℝ) ^ (((5 * j + r : ℕ)) : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
    _ ≤ (2 : ℝ) ^ ((10 : ℝ) + 5 * m / 11) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hR
    _ = 2 ^ 10 * (2 : ℝ) ^ ((5 : ℝ) * m / 11) := by
      rw [Real.rpow_add (by norm_num)]; norm_num

theorem beta_le_of_M11 (h11 : M 11 ≤ 2 ^ 5) : beta ≤ 5 / 11 := by
  refine (beta_le 11 (by norm_num)).trans ?_
  have : Real.logb 2 (M 11) ≤ Real.logb 2 ((2 : ℝ) ^ 5) :=
    Real.logb_le_logb_of_le (by norm_num) (M_pos 11) (by exact_mod_cast h11)
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
  push_cast at this ⊢
  linarith

end BalancedMast
