import LeanProofs.LatinRank.Factor

/-!
# Latin squares of small rank: the lower bound (Theorem 1)

A Latin square of order `n` is stored with symbols `0, …, n-1`; its real matrix `V L` has the entries
`1, …, n` of the question, and `C L = 2 V L - (n+1)` has entries `-(n-1), -(n-3), …, n-1`.
* `rank_bound`: `3 (n - 1) ≤ (n + 1) (rank V - 1)`;
* `rank_bound_strict`: strict when `n ≥ 3` is odd;
* `four_le_rank`: `rank V ≥ 4` for `n ≥ 5`, and `three_le_rank`: `rank V ≥ 3` for `n = 4`.

The subspace used is `W ∩ 1ᗮ`, `W` the column space of `V`: it contains every column of `C` and has
dimension `rank V - 1`, so the factorisation of `Factor.lean` applies to `C` with `d = rank V - 1`.
-/

open Module

namespace LatinRank

variable {n : ℕ}

local notation "E" n => EuclideanSpace ℝ (Fin n)

/-- A Latin square of order `n` on the symbols `0, …, n - 1`. -/
def IsLatin (L : Matrix (Fin n) (Fin n) (Fin n)) : Prop :=
  (∀ i, Function.Bijective (L i)) ∧ ∀ j, Function.Bijective fun i => L i j

/-- The real matrix with entries `1, …, n`. -/
def V (L : Matrix (Fin n) (Fin n) (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ((L i j : ℕ) : ℝ) + 1

/-- The centred matrix `2 V - (n + 1)`. -/
def C (L : Matrix (Fin n) (Fin n) (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => 2 * ((L i j : ℕ) : ℝ) - (n - 1)

/-- The all-ones vector. -/
noncomputable def one : E n := WithLp.toLp 2 (fun _ => 1)

lemma sum_bij {f : Fin n → Fin n} (hf : f.Bijective) (g : Fin n → ℝ) :
    ∑ i, g (f i) = ∑ k, g k :=
  Equiv.sum_comp (Equiv.ofBijective f hf) g

lemma sum_id_range (n : ℕ) : ∑ k ∈ Finset.range n, (k : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_sq_range (n : ℕ) :
    ∑ k ∈ Finset.range n, (k : ℝ) ^ 2 = n * (n - 1) * (2 * n - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

lemma sum_val (n : ℕ) : ∑ k : Fin n, ((k : ℕ) : ℝ) = n * (n - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (k : ℝ)), sum_id_range]

lemma sum_val_sq (n : ℕ) : ∑ k : Fin n, ((k : ℕ) : ℝ) ^ 2 = n * (n - 1) * (2 * n - 1) / 6 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (k : ℝ) ^ 2), sum_sq_range]

lemma sum_centre (n : ℕ) : ∑ k : Fin n, (2 * ((k : ℕ) : ℝ) - (n - 1)) = 0 := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_val]; simp; ring

lemma sum_centre_sq (n : ℕ) :
    ∑ k : Fin n, (2 * ((k : ℕ) : ℝ) - (n - 1)) ^ 2 = (n : ℝ) * ((n : ℝ) ^ 2 - 1) / 3 := by
  have e : ∀ k : Fin n, (2 * ((k : ℕ) : ℝ) - (n - 1)) ^ 2 =
      4 * ((k : ℕ) : ℝ) ^ 2 - 4 * (n - 1) * ((k : ℕ) : ℝ) + (n - 1) ^ 2 := fun k => by ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_val, sum_val_sq]
  simp; ring

variable {L : Matrix (Fin n) (Fin n) (Fin n)}

lemma col_sum_C (hL : IsLatin L) (j : Fin n) : ∑ i, C L i j = 0 := by
  simpa [C] using (sum_bij (hL.2 j) fun k => 2 * ((k : ℕ) : ℝ) - (n - 1)).trans (sum_centre n)

lemma col_sq_C (hL : IsLatin L) (j : Fin n) : ∑ i, C L i j ^ 2 = n * (n ^ 2 - 1) / 3 := by
  simpa [C] using
    (sum_bij (hL.2 j) fun k => (2 * ((k : ℕ) : ℝ) - (n - 1)) ^ 2).trans (sum_centre_sq n)

lemma row_sum_V (hL : IsLatin L) (i : Fin n) : ∑ j, V L i j = n * (n + 1) / 2 := by
  have := sum_bij (hL.1 i) fun k => ((k : ℕ) : ℝ) + 1
  simp only [V] at this ⊢
  rw [this, Finset.sum_add_distrib, sum_val]; simp; ring

/-- The column space of `V`, in `ℝⁿ`. -/
noncomputable def W (L : Matrix (Fin n) (Fin n) (Fin n)) : Submodule ℝ (E n) :=
  Submodule.span ℝ (Set.range (col (V L)))

lemma rank_eq_finrank_W : (V L).rank = finrank ℝ (W L) := by
  rw [Matrix.rank_eq_finrank_span_cols]
  let e := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm
  have : W L = (Submodule.span ℝ (Set.range (V L).col)).map e.toLinearMap := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  rw [this, LinearEquiv.finrank_map_eq]

lemma one_mem_W (hn : 0 < n) (hL : IsLatin L) : (one : E n) ∈ W L := by
  have hs : (∑ j, col (V L) j) = ((n : ℝ) * (n + 1) / 2) • (one : E n) := by
    ext i; simp [one, col, row_sum_V hL i, WithLp.ofLp_sum]
  have hmem : (∑ j, col (V L) j) ∈ W L :=
    Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨j, rfl⟩
  rw [hs] at hmem
  have hc : ((n : ℝ) * (n + 1) / 2) ≠ 0 := by positivity
  exact (Submodule.smul_mem_iff _ hc).1 hmem

lemma col_C_mem_W (hn : 0 < n) (hL : IsLatin L) (j : Fin n) : col (C L) j ∈ W L := by
  have : col (C L) j = (2 : ℝ) • col (V L) j - ((n : ℝ) + 1) • (one : E n) := by
    ext i; simp [col, C, V, one]; ring
  rw [this]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
    (Submodule.smul_mem _ _ (one_mem_W hn hL))

lemma col_C_orth (hL : IsLatin L) (j : Fin n) :
    col (C L) j ∈ (Submodule.span ℝ {(one : E n)})ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, PiLp.inner_apply]
  simpa [one, col] using col_sum_C hL j

/-- The subspace `W ∩ 1ᗮ`, of dimension `rank V - 1`. -/
noncomputable def K (L : Matrix (Fin n) (Fin n) (Fin n)) : Submodule ℝ (E n) :=
  (Submodule.span ℝ {(one : E n)})ᗮ ⊓ W L

lemma finrank_K (hn : 0 < n) (hL : IsLatin L) : finrank ℝ (K L) + 1 = (V L).rank := by
  have hle : Submodule.span ℝ {(one : E n)} ≤ W L :=
    (Submodule.span_singleton_le_iff_mem _ _).2 (one_mem_W hn hL)
  have h1 : (one : E n) ≠ 0 := by
    intro h
    have := congrArg (fun v : E n => v ⟨0, hn⟩) h
    simp [one] at this
  have := Submodule.finrank_add_inf_finrank_orthogonal hle
  rw [finrank_span_singleton h1] at this
  rw [rank_eq_finrank_W, ← this, K, add_comm]

/-- The value `n - 1` of `C` occurs in every row. -/
lemma exists_top (hn : 0 < n) (hL : IsLatin L) (i : Fin n) : ∃ j, C L i j = n - 1 := by
  obtain ⟨j, hj⟩ := (hL.1 i).2 ⟨n - 1, by omega⟩
  refine ⟨j, ?_⟩
  simp only [C, hj]
  rw [Nat.cast_sub (by omega)]; push_cast; ring

/-- The value `-(n - 1)` of `C` occurs in every row. -/
lemma exists_bot (hn : 0 < n) (hL : IsLatin L) (i : Fin n) : ∃ j, C L i j = -(n - 1) := by
  obtain ⟨j, hj⟩ := (hL.1 i).2 ⟨0, hn⟩
  exact ⟨j, by simp [C, hj]⟩

/-- The two estimates of the proof, for `d = rank V - 1`. -/
lemma core (hn : 0 < n) (hL : IsLatin L) :
    ∃ (x y : Fin n → E (finrank ℝ (K L))),
      (∀ i j, C L i j = inner ℝ (x i) (y j)) ∧
      ∑ i, ‖x i‖ ^ 2 = finrank ℝ (K L) ∧
      ∀ j, ‖y j‖ ^ 2 = n * (n ^ 2 - 1) / 3 := by
  obtain ⟨x, y, h1, h2, h3⟩ := factor (C L) (K L)
    (fun j => ⟨col_C_orth hL j, col_C_mem_W hn hL j⟩)
  exact ⟨x, y, h1, h2, fun j => (h3 j).trans (col_sq_C hL j)⟩

/-- Each row's top entry: `(n - 1)² ≤ ‖xᵢ‖² S₂`. -/
lemma row_le {d : ℕ} {x y : Fin n → E d} (hn : 0 < n) (hL : IsLatin L)
    (h1 : ∀ i j, C L i j = inner ℝ (x i) (y j)) (h3 : ∀ j, ‖y j‖ ^ 2 = n * (n ^ 2 - 1) / 3)
    (i : Fin n) : ((n : ℝ) - 1) ^ 2 ≤ ‖x i‖ ^ 2 * (n * (n ^ 2 - 1) / 3) := by
  obtain ⟨j, hj⟩ := exists_top hn hL i
  rw [← h3 j, ← mul_pow, ← hj, h1]
  exact sq_le_sq' (by linarith [abs_le.1 (abs_real_inner_le_norm (x i) (y j))])
    (real_inner_le_norm _ _)

/-- Theorem 1 (the inequality): `3 (n - 1) ≤ (n + 1) (rank V - 1)`. -/
theorem rank_bound (hn : 0 < n) (hL : IsLatin L) :
    3 * ((n : ℝ) - 1) ≤ (n + 1) * finrank ℝ (K L) := by
  obtain ⟨x, y, h1, h2, h3⟩ := core hn hL
  have hsum : (n : ℝ) * ((n : ℝ) - 1) ^ 2 ≤ finrank ℝ (K L) * (n * (n ^ 2 - 1) / 3) := by
    have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => row_le hn hL h1 h3 i
    rw [← Finset.sum_mul, h2] at this
    simpa using this
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rcases eq_or_lt_of_le hn1 with h | h
  · rw [← h]; norm_num
  · have hpos : 0 < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
    nlinarith

/-- Theorem 1 (strictness): for odd `n ≥ 3` the inequality is strict. -/
theorem rank_bound_strict (hn : 3 ≤ n) (hodd : Odd n) (hL : IsLatin L) :
    3 * ((n : ℝ) - 1) < (n + 1) * finrank ℝ (K L) := by
  have hn0 : 0 < n := by omega
  refine lt_of_le_of_ne (rank_bound hn0 hL) fun heq => ?_
  obtain ⟨x, y, h1, h2, h3⟩ := core hn0 hL
  set S : ℝ := n * (n ^ 2 - 1) / 3 with hS
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hSpos : 0 < S := by rw [hS]; nlinarith
  -- every row estimate is an equality
  have htight : ∀ i, ‖x i‖ ^ 2 * S = ((n : ℝ) - 1) ^ 2 := by
    have hle := fun i => row_le hn0 hL h1 h3 i
    have htot : ∑ i, (‖x i‖ ^ 2 * S - ((n : ℝ) - 1) ^ 2) = 0 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, h2]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [hS]
      have : (finrank ℝ (K L) : ℝ) = 3 * ((n : ℝ) - 1) / (n + 1) := by
        field_simp; linarith
      rw [this]; field_simp; ring
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sub_nonneg.2 (hle i)).1 htot i
      (Finset.mem_univ _)
    rw [← hS] at this
    linarith
  -- row 0: the top and bottom entries force two opposite columns
  let i₀ : Fin n := ⟨0, hn0⟩
  obtain ⟨j, hj⟩ := exists_top hn0 hL i₀
  obtain ⟨j', hj'⟩ := exists_bot hn0 hL i₀
  have hy : ∀ k, ‖y k‖ = Real.sqrt S := fun k => by
    rw [← Real.sqrt_sq (norm_nonneg _), h3 k]
  have hxS : ‖x i₀‖ * Real.sqrt S = (n : ℝ) - 1 := by
    have := htight i₀
    have h0 : 0 ≤ ‖x i₀‖ * Real.sqrt S := by positivity
    have hsq : (‖x i₀‖ * Real.sqrt S) ^ 2 = ((n : ℝ) - 1) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hSpos.le, this]
    nlinarith [sq_nonneg (‖x i₀‖ * Real.sqrt S - ((n : ℝ) - 1)),
      sq_nonneg (‖x i₀‖ * Real.sqrt S + ((n : ℝ) - 1))]
  have hsqrt : 0 < Real.sqrt S := Real.sqrt_pos.2 hSpos
  have hx0 : 0 < ‖x i₀‖ := by
    by_contra h
    have : ‖x i₀‖ = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
    rw [this, zero_mul] at hxS; linarith
  have e1 : inner ℝ (x i₀) (y j) = ‖x i₀‖ * ‖y j‖ := by rw [← h1, hj, hy, hxS]
  have e2 : inner ℝ (x i₀) (-y j') = ‖x i₀‖ * ‖-y j'‖ := by
    rw [inner_neg_right, ← h1, hj', norm_neg, hy, hxS]; ring
  have f1 := inner_eq_norm_mul_iff_real.1 e1
  have f2 := inner_eq_norm_mul_iff_real.1 e2
  rw [norm_neg, hy] at f2
  rw [hy] at f1
  have hyy : y j = -y j' := by
    have := f1.symm.trans f2
    exact smul_right_injective _ hx0.ne' this
  -- so column `j'` is the negative of column `j`
  have hcol : ∀ k, C L k j' = -C L k j := fun k => by
    rw [h1, h1, hyy, inner_neg_right, neg_neg]
  -- the zero entry of column `j` meets the zero entry of column `j'` in the same row
  obtain ⟨m, hm⟩ := hodd
  obtain ⟨k, hk⟩ := (hL.2 j).2 ⟨m, by omega⟩
  have hk0 : C L k j = 0 := by
    simp only [C] at hk ⊢
    rw [hk]; push_cast [hm]; ring
  have hk0' : C L k j' = 0 := by rw [hcol, hk0, neg_zero]
  have hkj : L k j' = L k j := by
    apply Fin.ext
    have a : 2 * ((L k j' : ℕ) : ℝ) = n - 1 := by simp only [C] at hk0'; linarith
    have b : 2 * ((L k j : ℕ) : ℝ) = n - 1 := by simp only [C] at hk0; linarith
    exact_mod_cast (by linarith : ((L k j' : ℕ) : ℝ) = ((L k j : ℕ) : ℝ))
  have hjj : j' = j := (hL.1 k).1 hkj
  rw [hjj, hj] at hj'
  linarith

/-- `rank V ≥ 4` for every Latin square of order `n ≥ 5`. -/
theorem four_le_rank (hn : 5 ≤ n) (hL : IsLatin L) : 4 ≤ (V L).rank := by
  rw [← finrank_K (by omega) hL]
  suffices 3 ≤ finrank ℝ (K L) by omega
  by_contra h
  have hd : (finrank ℝ (K L) : ℝ) ≤ 2 := by exact_mod_cast (by omega : finrank ℝ (K L) ≤ 2)
  have hn5 : (5 : ℝ) ≤ n := by exact_mod_cast hn
  rcases Nat.even_or_odd n with he | ho
  · have := rank_bound (by omega) hL
    have h6 : 6 ≤ n := by obtain ⟨k, rfl⟩ := he; omega
    have hn6 : (6 : ℝ) ≤ n := by exact_mod_cast h6
    nlinarith
  · have := rank_bound_strict (by omega) ho hL
    nlinarith

/-- `rank V ≥ 3` for every Latin square of order `4`. -/
theorem three_le_rank (hn : n = 4) (hL : IsLatin L) : 3 ≤ (V L).rank := by
  subst hn
  rw [← finrank_K (by norm_num) hL]
  have := rank_bound (by norm_num) hL
  suffices 2 ≤ finrank ℝ (K L) by omega
  by_contra h
  have hd : (finrank ℝ (K L) : ℝ) ≤ 1 := by exact_mod_cast (by omega : finrank ℝ (K L) ≤ 1)
  push_cast at this
  linarith

end LatinRank
