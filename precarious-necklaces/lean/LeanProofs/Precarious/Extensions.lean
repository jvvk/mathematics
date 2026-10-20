import LeanProofs.Precarious.Construct
import LeanProofs.Precarious.Framework

/-!
# Precarious necklaces (MO 515996): extensions

* `even_every_deletion`, `odd_every_deletion`: deleting *any* nonempty set of colours from the constructions
  leaves a symmetric necklace, so asking for every deletion (not just single colours) does not change the
  minimum `a k`.
* `extWord m n`: the even word with `n` extra colours fixed at the end of every block. Keeping fewer than `2m`
  colours always misses a pair colour, so `extWord` keeps any `s < 2m` colours symmetric (`extWord_keepPrec`).
  With `m = 2`: `keep_three_exact`, keeping any three of `k ≥ 4` colours, the minimum length is `6k`.
* `twoWord n`: `AABBACABBAABCB` with `n` extra colours inserted, as a cluster, after its 1st and 8th letters.
  Every two-colour sub-necklace is symmetric: `keep_two_exact`, with `k ≥ 3` colours the minimum is `2k + 8`.

Removing a set that meets pair `i` leaves pair `i` with a pattern that no longer depends on the block, so the
blocks repeat with period `p_m# / p_i`, as in `even_spec`.
-/

set_option linter.unusedSectionVars false

namespace Precarious

open List

/-- Once a colour of pair `i` is removed, what is left of the pair does not depend on the block. -/
lemma filter_pairBlk_indep {β : Type*} (f : β → Bool) (x y : β) (hf : f x = false ∨ f y = false)
    (p j j' : ℕ) : (pairBlk p j x y).filter f = (pairBlk p j' x y).filter f := by
  unfold pairBlk
  rcases hf with h | h <;> split_ifs <;> simp [filter_cons, h]

/-- Blocks agree after a shift by `D` once a colour of pair `i` is removed and the other primes divide `D`. -/
lemma filter_block_shift {m : ℕ} (f : Fin m × Bool → Bool) (i : Fin m)
    (hf : f (i, false) = false ∨ f (i, true) = false) (j D : ℕ)
    (hD : ∀ l : Fin m, l ≠ i → pp l ∣ D) : (block m (j + D)).filter f = (block m j).filter f := by
  unfold block
  simp only [filter_flatMap]
  apply flatMap_congr
  intro l _
  by_cases hli : l = i
  · subst hli; exact filter_pairBlk_indep f _ _ hf _ _ _
  · have : pairBlk (pp l) (j + D) (l, false) (l, true) = pairBlk (pp l) j (l, false) (l, true) := by
      unfold pairBlk
      simp only [Nat.dvd_add_left (hD l hli)]
    rw [this]

/-- **Every deletion, even case.** -/
theorem even_every_deletion (m : ℕ) (J : Finset (Fin m × Bool)) (hJ : J.Nonempty) :
    Symm ((evenWord m).filter (fun z => z ∉ J)) := by
  obtain ⟨⟨i, b⟩, hib⟩ := hJ
  set f : Fin m × Bool → Bool := fun z => decide (z ∉ J) with hfdef
  have hf : f (i, false) = false ∨ f (i, true) = false := by
    cases b
    · left; simp [hfdef, hib]
    · right; simp [hfdef, hib]
  refine ⟨pp i, (pp_prime i).two_le, (range (prOff m i)).flatMap (fun j => (block m j).filter f), ?_⟩
  have h1 : (evenWord m).filter (fun z => z ∉ J) = (range (pr m)).flatMap (fun j => (block m j).filter f) := by
    unfold evenWord; rw [filter_flatMap]
  rw [h1, pr_eq_mul m i i.isLt]
  apply flatMap_range_periodic
  intro j
  exact filter_block_shift f i hf j _ (fun l hli => pp_dvd_prOff l.isLt (fun h => hli (Fin.ext h)))

/-- **Every deletion, odd case.** -/
theorem odd_every_deletion (m : ℕ) (J : Finset (Option (Fin m × Bool))) (hJ : J.Nonempty) :
    Symm ((oddWord m).filter (fun z => z ∉ J)) := by
  by_cases hpair : ∃ i b, some (i, b) ∈ J
  · -- `J` meets pair `i`: the groups repeat with period `prOff m i`
    obtain ⟨i, b, hib⟩ := hpair
    set f : Option (Fin m × Bool) → Bool := fun z => decide (z ∉ J) with hfdef
    set g : Fin m × Bool → Bool := fun z => f (some z) with hgdef
    have hg : g (i, false) = false ∨ g (i, true) = false := by
      cases b
      · left; simp [hgdef, hfdef, hib]
      · right; simp [hgdef, hfdef, hib]
    refine ⟨pp i, (pp_prime i).two_le, (range (prOff m i)).flatMap (fun G => (group m G).filter f), ?_⟩
    have h1 : (oddWord m).filter (fun z => z ∉ J) = (range (pr m)).flatMap (fun G => (group m G).filter f) := by
      unfold oddWord; rw [filter_flatMap]
    rw [h1, pr_eq_mul m i i.isLt]
    apply flatMap_range_periodic
    intro G
    have hsh : ∀ t, ((block m ((G + prOff m i) * pp m + t)).filter g) = (block m (G * pp m + t)).filter g := by
      intro t
      rw [show (G + prOff m i) * pp m + t = G * pp m + t + prOff m i * pp m by ring]
      exact filter_block_shift g i hg (G * pp m + t) (prOff m i * pp m)
        (fun l hli => Dvd.dvd.mul_right (pp_dvd_prOff l.isLt (fun h => hli (Fin.ext h))) _)
    have hc : f ∘ some = g := rfl
    unfold group
    simp only [filter_cons, filter_flatMap, filter_map, hc]
    split_ifs
    · congr 1
      exact flatMap_congr (fun t _ => by rw [hsh t])
    · exact flatMap_congr (fun t _ => by rw [hsh t])
  · -- `J` is `{none}`: the blocks repeat with period `pr m`
    push Not at hpair
    have hJn : J = {none} := by
      obtain ⟨z, hz⟩ := hJ
      ext c
      rcases c with _ | ⟨i, b⟩
      · simp only [Finset.mem_singleton, iff_true]
        rcases z with _ | ⟨i, b⟩
        · exact hz
        · exact absurd hz (hpair i b)
      · simp [hpair i b]
    subst hJn
    have : (oddWord m).filter (fun z => z ∉ ({none} : Finset (Option (Fin m × Bool)))) = del none (oddWord m) := by
      unfold del; congr 1; funext z; simp
    rw [this]
    refine ⟨pp m, (pp_prime m).two_le, (range (pr m)).flatMap (fun j => (block m j).map some), ?_⟩
    have hdel : del none (oddWord m) = (range (pr m * pp m)).flatMap (fun j => (block m j).map some) := by
      rw [← flatMap_range_groups]
      unfold oddWord del
      rw [filter_flatMap]
      apply flatMap_congr
      intro G _
      unfold group
      rw [filter_cons_of_neg (by simp), filter_flatMap]
      apply flatMap_congr
      intro t _
      rw [filter_map_some _ (fun z => z ≠ none)]
      simp
    rw [hdel, mul_comm]
    apply flatMap_range_periodic
    intro j; rw [block_shift_pr]

/-! ### Extra fixed colours -/

lemma filterMap_flatten_replicate {β γ : Type*} (f : β → Option γ) (r : ℕ) (v : List β) :
    ((replicate r v).flatten).filterMap f = (replicate r (v.filterMap f)).flatten := by
  induction r with
  | zero => simp
  | succ r ih => simp [replicate_succ, flatten_cons, filterMap_append, ih]

lemma filterMap_flatMap {β γ δ : Type*} (f : γ → Option δ) (g : β → List γ) (l : List β) :
    (l.flatMap g).filterMap f = l.flatMap (fun a => (g a).filterMap f) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [flatMap_cons, filterMap_append, ih]

/-- The even word with `n` extra colours at the end of every block. -/
noncomputable def extWord (m n : ℕ) : List (Fin m × Bool ⊕ Fin n) :=
  (range (pr m)).flatMap (fun j => (block m j).map Sum.inl ++ (finRange n).map Sum.inr)

lemma extWord_left (m n : ℕ) : (extWord m n).filterMap Sum.getLeft? = evenWord m := by
  unfold extWord evenWord
  rw [filterMap_flatMap]
  apply flatMap_congr
  intro j _
  rw [filterMap_append, filterMap_map, filterMap_map]
  simp [Function.comp_def]

theorem extWord_not_symm (m n : ℕ) (hm : 1 ≤ m) : ¬ Symm (extWord m n) := by
  rintro ⟨r, hr, v, hv⟩
  apply (even_spec m hm).1.1
  refine ⟨r, hr, v.filterMap Sum.getLeft?, ?_⟩
  rw [← extWord_left m n, hv, filterMap_flatten_replicate]

/-- Keeping a set that misses a colour of pair `i` leaves a `p_i`-th power. -/
theorem extWord_keep (m n : ℕ) (S : Finset (Fin m × Bool ⊕ Fin n)) (i : Fin m) (b : Bool)
    (hS : Sum.inl (i, b) ∉ S) : Symm (keep S (extWord m n)) := by
  set f : Fin m × Bool ⊕ Fin n → Bool := fun z => decide (z ∈ S) with hfdef
  set g : Fin m × Bool → Bool := fun z => f (Sum.inl z) with hgdef
  have hg : g (i, false) = false ∨ g (i, true) = false := by
    cases b
    · left; simp [hgdef, hfdef, hS]
    · right; simp [hgdef, hfdef, hS]
  set E := ((finRange n).map Sum.inr).filter f
  refine ⟨pp i, (pp_prime i).two_le,
    (range (prOff m i)).flatMap (fun j => ((block m j).filter g).map Sum.inl ++ E), ?_⟩
  have h1 : keep S (extWord m n) = (range (pr m)).flatMap (fun j => ((block m j).filter g).map Sum.inl ++ E) := by
    unfold keep extWord
    rw [filter_flatMap]
    apply flatMap_congr
    intro j _
    rw [filter_append, filter_map]
    rfl
  rw [h1, pr_eq_mul m i i.isLt]
  apply flatMap_range_periodic
  intro j
  rw [filter_block_shift g i hg j _ (fun l hli => pp_dvd_prOff l.isLt (fun h => hli (Fin.ext h)))]

lemma extWord_mem (m n : ℕ) (_hm : 1 ≤ m) (z : Fin m × Bool ⊕ Fin n) : z ∈ extWord m n := by
  unfold extWord
  refine mem_flatMap.mpr ⟨0, mem_range.mpr (pr_pos m), ?_⟩
  rcases z with ⟨i, b⟩ | e
  · refine mem_append_left _ (mem_map.mpr ⟨(i, b), ?_, rfl⟩)
    unfold block
    refine mem_flatMap.mpr ⟨i, mem_finRange i, ?_⟩
    cases b <;> simp [pairBlk]
  · exact mem_append_right _ (mem_map.mpr ⟨e, mem_finRange e, rfl⟩)

theorem extWord_card (m n : ℕ) (hm : 1 ≤ m) : (extWord m n).toFinset.card = 2 * m + n := by
  have : (extWord m n).toFinset = Finset.univ :=
    Finset.eq_univ_of_forall (fun z => mem_toFinset.mpr (extWord_mem m n hm z))
  rw [this, Finset.card_univ, Fintype.card_sum, Fintype.card_prod]
  simp [mul_comm]

theorem extWord_length (m n : ℕ) : (extWord m n).length = (2 * m + n) * pr m := by
  simp [extWord, length_flatMap, block_length, mul_comm]

/-- Keeping fewer than `2m` colours of `extWord` always leaves a symmetric necklace. -/
theorem extWord_keepPrec (m n s : ℕ) (hm : 1 ≤ m) (hs : s < 2 * m) : KeepPrec s (extWord m n) := by
  refine ⟨extWord_not_symm m n hm, fun S _ hSs => ?_⟩
  -- `S` misses a pair colour
  by_cases hall : ∀ ib : Fin m × Bool, Sum.inl ib ∈ S
  · exfalso
    have hsub : (Finset.univ : Finset (Fin m × Bool)).map ⟨Sum.inl, Sum.inl_injective⟩ ⊆ S := by
      intro z hz
      obtain ⟨ib, _, rfl⟩ := Finset.mem_map.mp hz
      exact hall ib
    have := Finset.card_le_card hsub
    rw [Finset.card_map, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at this
    omega
  · push Not at hall
    obtain ⟨⟨i, b⟩, hib⟩ := hall
    exact extWord_keep m n S i b hib

/-- **Keeping three colours.** For `k ≥ 4` the minimum length is exactly `6k`. -/
theorem keep_three_exact (k : ℕ) (hk : 4 ≤ k) :
    (∀ {α : Type} [DecidableEq α] (w : List α), KeepPrec 3 w → w.toFinset.card = k → 6 * k ≤ w.length) ∧
    ∃ (β : Type) (_ : DecidableEq β) (w : List β),
      KeepPrec 3 w ∧ w.toFinset.card = k ∧ w.length = 6 * k := by
  refine ⟨fun w hw hc => hc ▸ keep_three_bound 3 le_rfl w hw (by omega), ?_⟩
  have hpr2 : pr 2 = 6 := by
    simp [pr, Finset.prod_range_succ, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
  refine ⟨_, inferInstance, extWord 2 (k - 4), extWord_keepPrec 2 (k - 4) 3 (by norm_num) (by norm_num),
    by rw [extWord_card 2 (k - 4) (by norm_num)]; omega, ?_⟩
  rw [extWord_length, hpr2]; omega

/-! ### Keeping two colours -/

/-- `AABBACABBAABCB`, split as first letter, next seven, last six. -/
def W0 : List (Fin 3) := [0]
def WM : List (Fin 3) := [0, 1, 1, 0, 2, 0, 1]
def WR : List (Fin 3) := [1, 0, 0, 1, 2, 1]

lemma symm_map {β γ : Type*} (f : β → γ) {u : List β} (h : Symm u) : Symm (u.map f) := by
  obtain ⟨r, hr, v, hv⟩ := h
  exact ⟨r, hr, v.map f, by rw [hv, map_flatten, map_replicate]⟩

lemma W_not_symm : ¬ Symm (W0 ++ WM ++ WR) := by
  rintro ⟨r, hr, v, hv⟩
  have hl : 14 = r * v.length := by
    have := congrArg length hv
    rw [length_flatten_replicate] at this
    simpa [W0, WM, WR] using this
  have hv' : v = (W0 ++ WM ++ WR).take v.length := by
    rw [hv]
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    simp [replicate_succ, flatten_cons]
  have hv2 : W0 ++ WM ++ WR = (replicate r ((W0 ++ WM ++ WR).take v.length)).flatten := by
    rw [← hv']; exact hv
  generalize v.length = L at hl hv2
  have hL : 1 ≤ L := by rcases Nat.eq_zero_or_pos L with h | h <;> [subst h; skip] <;> omega
  have hr14 : r ≤ 14 := by nlinarith
  interval_cases r <;> first
    | omega
    | (have h3 : L = 7 ∨ L = 2 ∨ L = 1 := by omega
       rcases h3 with rfl | rfl | rfl <;> first | omega | exact absurd hv2 (by decide))

lemma W_pairs (a b : Fin 3) (hab : a ≠ b) :
    Symm ((W0 ++ WM ++ WR).filter (fun c => decide (c = a ∨ c = b))) := by
  fin_cases a <;> fin_cases b
  all_goals first
    | exact absurd rfl hab
    | exact ⟨3, by norm_num, [0, 0, 1, 1], by decide⟩
    | exact ⟨2, le_rfl, [0, 0, 0, 2], by decide⟩
    | exact ⟨2, le_rfl, [1, 1, 2, 1], by decide⟩
    | exact ⟨3, by norm_num, [1, 1, 0, 0], by decide⟩
    | exact ⟨2, le_rfl, [2, 0, 0, 0], by decide⟩
    | exact ⟨2, le_rfl, [1, 1, 2, 1], by decide⟩
    | exact ⟨2, le_rfl, [2, 1, 1, 1], by decide⟩
    | exact ⟨2, le_rfl, [0, 0, 0, 2], by decide⟩
    | exact ⟨2, le_rfl, [1, 2, 1, 1], by decide⟩

/-- The `2k + 8` word for `k = 3 + n` colours. -/
def twoWord (n : ℕ) : List (Fin 3 ⊕ Fin n) :=
  W0.map Sum.inl ++ (finRange n).map Sum.inr ++ WM.map Sum.inl ++ (finRange n).map Sum.inr ++ WR.map Sum.inl

lemma twoWord_left (n : ℕ) : (twoWord n).filterMap Sum.getLeft? = W0 ++ WM ++ WR := by
  simp [twoWord, filterMap_append, filterMap_map, Function.comp_def]

lemma filter_finRange_eq (n : ℕ) (e : Fin n) : (finRange n).filter (fun z => decide (z = e)) = [e] := by
  rw [List.filter_eq, count_eq_one_of_mem (nodup_finRange n) (mem_finRange e)]
  rfl

theorem twoWord_keepPrec (n : ℕ) : KeepPrec 2 (twoWord n) := by
  refine ⟨?_, fun S _ hS => ?_⟩
  · rintro ⟨r, hr, v, hv⟩
    exact W_not_symm ⟨r, hr, v.filterMap Sum.getLeft?, by
      rw [← twoWord_left n, hv, filterMap_flatten_replicate]⟩
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hS
  -- the inserted cluster, kept
  have hE : ∀ (T : Finset (Fin 3 ⊕ Fin n)), ((finRange n).map Sum.inr).filter (fun z => decide (z ∈ T))
      = ((finRange n).filter (fun e => decide (Sum.inr e ∈ T))).map Sum.inr := by
    intro T; rw [filter_map]; rfl
  have hWpart : ∀ (T : Finset (Fin 3 ⊕ Fin n)) (U : List (Fin 3)), (U.map Sum.inl).filter (fun z => decide (z ∈ T))
      = (U.filter (fun c => decide (Sum.inl c ∈ T))).map Sum.inl := by
    intro T U; rw [filter_map]; rfl
  have hsplit : ∀ T : Finset (Fin 3 ⊕ Fin n), keep T (twoWord n) =
      (W0.filter (fun c => decide (Sum.inl c ∈ T))).map Sum.inl ++
      ((finRange n).filter (fun e => decide (Sum.inr e ∈ T))).map Sum.inr ++
      (WM.filter (fun c => decide (Sum.inl c ∈ T))).map Sum.inl ++
      ((finRange n).filter (fun e => decide (Sum.inr e ∈ T))).map Sum.inr ++
      (WR.filter (fun c => decide (Sum.inl c ∈ T))).map Sum.inl := by
    intro T
    simp only [keep, twoWord, filter_append, hE, hWpart]
  -- the four shapes of a kept pair
  have case_ll : ∀ a b : Fin 3, a ≠ b → Symm (keep {Sum.inl a, Sum.inl b} (twoWord n)) := by
    intro a b hab
    rw [hsplit]
    have h0 : ∀ e : Fin n, decide (Sum.inr e ∈ ({Sum.inl a, Sum.inl b} : Finset (Fin 3 ⊕ Fin n))) = false := by
      intro e; simp
    simp only [h0, filter_false, map_nil, append_nil]
    have hc : ∀ c : Fin 3, decide (Sum.inl c ∈ ({Sum.inl a, Sum.inl b} : Finset (Fin 3 ⊕ Fin n)))
        = decide (c = a ∨ c = b) := by intro c; simp
    simp only [hc, ← map_append, ← filter_append]
    exact symm_map _ (W_pairs a b hab)
  have case_lr : ∀ (a : Fin 3) (e : Fin n), Symm (keep {Sum.inl a, Sum.inr e} (twoWord n)) := by
    intro a e
    rw [hsplit]
    have hr : ∀ f : Fin n, decide (Sum.inr f ∈ ({Sum.inl a, Sum.inr e} : Finset (Fin 3 ⊕ Fin n)))
        = decide (f = e) := by intro f; simp
    have hc : ∀ c : Fin 3, decide (Sum.inl c ∈ ({Sum.inl a, Sum.inr e} : Finset (Fin 3 ⊕ Fin n)))
        = decide (c = a) := by intro c; simp
    simp only [hr, hc, filter_finRange_eq]
    fin_cases a
    · exact ⟨2, le_rfl, [Sum.inl 0, Sum.inr e, Sum.inl 0, Sum.inl 0], by simp [W0, WM, WR]⟩
    · exact ⟨2, le_rfl, [Sum.inr e, Sum.inl 1, Sum.inl 1, Sum.inl 1], by simp [W0, WM, WR]⟩
    · exact ⟨2, le_rfl, [Sum.inr e, Sum.inl 2], by simp [W0, WM, WR]⟩
  have case_rr : ∀ e f : Fin n, Symm (keep {Sum.inr e, Sum.inr f} (twoWord n)) := by
    intro e f
    rw [hsplit]
    have hc : ∀ c : Fin 3, decide (Sum.inl c ∈ ({Sum.inr e, Sum.inr f} : Finset (Fin 3 ⊕ Fin n))) = false := by
      intro c; simp
    simp only [hc, filter_false, map_nil, nil_append, append_nil]
    exact ⟨2, le_rfl, ((finRange n).filter (fun g => decide (Sum.inr g ∈
      ({Sum.inr e, Sum.inr f} : Finset (Fin 3 ⊕ Fin n))))).map Sum.inr,
      by simp only [replicate_succ, replicate_zero, flatten_cons, flatten_nil, List.append_nil]⟩
  rcases x with a | e <;> rcases y with b | f
  · exact case_ll a b (fun h => hxy (h ▸ rfl))
  · exact case_lr a f
  · rw [Finset.pair_comm]; exact case_lr b e
  · exact case_rr e f

theorem twoWord_card (n : ℕ) : (twoWord n).toFinset.card = 3 + n := by
  have : (twoWord n).toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro z
    rw [mem_toFinset]
    rcases z with c | e
    · fin_cases c <;> simp [twoWord, W0, WM]
    · simp [twoWord, mem_finRange]
  rw [this, Finset.card_univ, Fintype.card_sum]
  simp

theorem twoWord_length (n : ℕ) : (twoWord n).length = 2 * (3 + n) + 8 := by
  simp [twoWord, W0, WM, WR]; omega

/-- **Keeping two colours.** For `k ≥ 3` the minimum length is exactly `2k + 8`. -/
theorem keep_two_exact (k : ℕ) (hk : 3 ≤ k) :
    (∀ {α : Type} [DecidableEq α] (w : List α), KeepPrec 2 w → w.toFinset.card = k → 2 * k + 8 ≤ w.length) ∧
    ∃ (β : Type) (_ : DecidableEq β) (w : List β),
      KeepPrec 2 w ∧ w.toFinset.card = k ∧ w.length = 2 * k + 8 := by
  refine ⟨fun w hw hc => hc ▸ keep_two_bound w hw (by omega), ?_⟩
  refine ⟨_, inferInstance, twoWord (k - 3), twoWord_keepPrec _, by rw [twoWord_card]; omega, ?_⟩
  rw [twoWord_length]; omega

end Precarious
