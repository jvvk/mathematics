import LeanProofs.Precarious.Bound

/-!
# Precarious necklaces (MO 515996): the constructions

Colours come in pairs `(i, false), (i, true)`, `i < m`, and pair `i` is given the prime `p_i`. Block `j`
lists the pairs in order, pair `i` as `(i,false)(i,true)` when `p_i ∣ j` and reversed otherwise.

* `evenWord m`: blocks `j < p_m#`; precarious with `2m` colours and length `2m · p_m#` (`even_spec`).
* `oddWord m`: a new colour `none` before each run of `q = p_m` blocks, blocks `j < p_m# · q`; precarious with
  `2m + 1` colours and length `p_m# (2m q + 1)` (`odd_spec`).

Deleting a colour of pair `i` leaves a word whose blocks repeat with period `p_m# / p_i`, a `p_i`-th power.
Neither word is a power: a prime `p` dividing the exponent divides a colour count, so `p = p_i` for some `i`,
and then the projection onto pair `i` would repeat after `N / p_i` blocks, which `pairs_not_pow` rules out
because `p_i` does not divide the product of the other primes.
-/

set_option linter.unusedSectionVars false

namespace Precarious

open List

/-- The `i`-th prime. -/
noncomputable abbrev pp (i : ℕ) : ℕ := Nat.nth Nat.Prime i

lemma pp_prime (i : ℕ) : (pp i).Prime := Nat.prime_nth_prime i

lemma pp_inj {i l : ℕ} (h : pp i = pp l) : i = l := Nat.nth_injective Nat.infinite_setOfPred_prime h

/-- Pair `x y` in block `j`, for the prime `p`. -/
def pairBlk {β : Type*} (p j : ℕ) (x y : β) : List β := if p ∣ j then [x, y] else [y, x]

lemma pairBlk_length {β : Type*} (p j : ℕ) (x y : β) : (pairBlk p j x y).length = 2 := by
  unfold pairBlk; split_ifs <;> rfl

/-- Block `j`: every pair once. -/
noncomputable def block (m j : ℕ) : List (Fin m × Bool) :=
  (finRange m).flatMap (fun i : Fin m => pairBlk (pp i) j (i, false) (i, true))

noncomputable def evenWord (m : ℕ) : List (Fin m × Bool) := (range (pr m)).flatMap (block m)

/-! ### Lemmas on lists -/

/-- A block function with period `Q` gives a power. -/
lemma flatMap_range_periodic {β : Type*} (f : ℕ → List β) (Q : ℕ) (hf : ∀ j, f (j + Q) = f j) :
    ∀ n, (range (n * Q)).flatMap f = (replicate n ((range Q).flatMap f)).flatten := by
  have hshift : ∀ n j, f (n * Q + j) = f j := by
    intro n; induction n with
    | zero => simp
    | succ n ih => intro j; rw [Nat.succ_mul, show n * Q + Q + j = (n * Q + j) + Q by omega, hf, ih]
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, range_add, flatMap_append, ih, replicate_succ', flatten_append, flatten_singleton]
    congr 1
    rw [flatMap_map]
    exact flatMap_congr (fun j _ => hshift n j)

/-- `l.flatMap (if · = i then X else [])` is `X` when `i` occurs once. -/
lemma flatMap_ite_single {γ β : Type*} [DecidableEq γ] (X : List β) (i : γ) :
    ∀ l : List γ, l.Nodup → i ∈ l → l.flatMap (fun a => if a = i then X else []) = X := by
  intro l
  induction l with
  | nil => intro _ h; simp at h
  | cons a l ih =>
    intro hnd hi
    rw [flatMap_cons]
    have hnd' := (nodup_cons.mp hnd)
    by_cases ha : a = i
    · subst ha
      have : l.flatMap (fun b => if b = a then X else []) = [] := by
        rw [flatMap_eq_nil_iff]
        intro b hb; have : b ≠ a := fun h => hnd'.1 (h ▸ hb); simp [this]
      simp [this]
    · have hil : i ∈ l := by simpa [Ne.symm ha] using hi
      simp [ha, ih hnd'.2 hil]

/-- Dropping `M` blocks of length 2. -/
lemma drop_flatMap_two {γ β : Type*} (f : γ → List β) (hf : ∀ a, (f a).length = 2) :
    ∀ (M : ℕ) (l : List γ), (l.flatMap f).drop (2 * M) = (l.drop M).flatMap f := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
    intro l
    cases l with
    | nil => simp
    | cons a l =>
      rw [flatMap_cons, show 2 * (M + 1) = (f a).length + 2 * M by rw [hf]; ring, ← drop_drop,
        drop_left, ih, drop_succ_cons]

/-- **No power.** If the pair pattern over `N` blocks is a `p`-th power then `p ∣ N / p`. -/
lemma pairs_not_pow {β : Type*} (p N : ℕ) (hp : 2 ≤ p) (x y : β) (hxy : x ≠ y) (hN : p ∣ N)
    (v : List β) (h : (range N).flatMap (fun j => pairBlk p j x y) = (replicate p v).flatten) :
    p ∣ N / p := by
  obtain ⟨M, rfl⟩ := hN
  rw [Nat.mul_div_cancel_left M (by omega)]
  rcases Nat.eq_zero_or_pos M with hM | hM
  · simp [hM]
  have hlen : 2 * (p * M) = p * v.length := by
    have := congrArg length h
    rw [length_flatMap, length_flatten] at this
    simp [pairBlk_length] at this
    simpa [Nat.mul_comm] using this
  have hv : v.length = 2 * M := by
    have : p * v.length = p * (2 * M) := by rw [← hlen]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  -- the first letter, and the first letter after `M` blocks
  have h0 : ((range (p * M)).flatMap (fun j => pairBlk p j x y)).head? = some x := by
    obtain ⟨n, hn⟩ : ∃ n, p * M = n + 1 := ⟨p * M - 1, by have : 1 ≤ p * M := Nat.one_le_iff_ne_zero.mpr (by positivity); omega⟩
    rw [hn, range_succ_eq_map, flatMap_cons]
    simp [pairBlk]
  have hM' : ((range (p * M)).flatMap (fun j => pairBlk p j x y)).drop (2 * M) =
      (range' M (p * M - M)).flatMap (fun j => pairBlk p j x y) := by
    rw [drop_flatMap_two _ (fun j => pairBlk_length p j x y), range_eq_range', drop_range']
    simp
  have hMhead : (((range (p * M)).flatMap (fun j => pairBlk p j x y)).drop (2 * M)).head?
      = some (if p ∣ M then x else y) := by
    rw [hM']
    obtain ⟨n, hn⟩ : ∃ n, p * M - M = n + 1 := ⟨p * M - M - 1, by
      have : 2 * M ≤ p * M := Nat.mul_le_mul_right M hp; omega⟩
    rw [hn, range'_succ, flatMap_cons]
    unfold pairBlk; split_ifs <;> simp
  -- in a `p`-th power, the letter after `|v|` repeats the first
  have hpow : (((replicate p v).flatten).drop (2 * M)).head? = ((replicate p v).flatten).head? := by
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
    rw [← hv, replicate_succ, flatten_cons, drop_left, replicate_succ, flatten_cons, head?_append,
      head?_append]
    have : v ≠ [] := by intro hv0; rw [hv0] at hv; simp at hv; omega
    obtain ⟨a, v', rfl⟩ := exists_cons_of_ne_nil this
    simp
  rw [h] at h0 hMhead
  rw [hpow, h0] at hMhead
  by_contra hnd
  simp [hnd] at hMhead
  exact hxy hMhead

/-! ### Primes -/

/-- The product of the first `m` primes other than the `i`-th. -/
noncomputable def prOff (m i : ℕ) : ℕ := ∏ l ∈ (Finset.range m).erase i, pp l

lemma pr_eq_mul (m i : ℕ) (hi : i < m) : pr m = pp i * prOff m i := by
  unfold pr prOff
  exact (Finset.mul_prod_erase _ _ (Finset.mem_range.mpr hi)).symm

lemma pp_dvd_prOff {m i l : ℕ} (hl : l < m) (hli : l ≠ i) : pp l ∣ prOff m i :=
  Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hli, Finset.mem_range.mpr hl⟩)

lemma not_pp_dvd_prOff (m i : ℕ) : ¬ pp i ∣ prOff m i := by
  intro h
  obtain ⟨l, hl, hdvd⟩ := ((pp_prime i).prime.dvd_finsetProd_iff _).mp h
  have := (Nat.prime_dvd_prime_iff_eq (pp_prime i) (pp_prime l)).mp hdvd
  exact (Finset.mem_erase.mp hl).1 (pp_inj this).symm

lemma pp_dvd_pr {m l : ℕ} (hl : l < m) : pp l ∣ pr m :=
  Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hl)

lemma prime_dvd_pr {p m : ℕ} (hp : p.Prime) (h : p ∣ pr m) : ∃ i < m, p = pp i := by
  obtain ⟨i, hi, hdvd⟩ := (hp.prime.dvd_finsetProd_iff _).mp h
  exact ⟨i, Finset.mem_range.mp hi, (Nat.prime_dvd_prime_iff_eq hp (pp_prime i)).mp hdvd⟩

/-! ### Blocks -/

lemma length_flatten_replicate {β : Type*} (r : ℕ) (v : List β) :
    ((replicate r v).flatten).length = r * v.length := by
  induction r with
  | zero => simp
  | succ r ih => simp [replicate_succ, flatten_cons, ih, Nat.succ_mul, add_comm]

lemma block_length (m j : ℕ) : (block m j).length = 2 * m := by
  simp [block, length_flatMap, pairBlk_length, mul_comm]

lemma pairBlk_ne {m : ℕ} (i l : Fin m) (hli : l ≠ i) (p j : ℕ) (b : Bool) :
    del (i, b) (pairBlk p j (l, false) (l, true)) = pairBlk p j (l, false) (l, true) := by
  unfold pairBlk del; split_ifs <;> simp [hli]

lemma del_pairBlk_self {m : ℕ} (i : Fin m) (p j : ℕ) (b : Bool) :
    del (i, b) (pairBlk p j (i, false) (i, true)) = [(i, !b)] := by
  unfold pairBlk del; cases b <;> split_ifs <;> simp

/-- Deleting a colour of pair `i`: blocks agree after a shift by any `D` that the other primes divide. -/
lemma del_block_shift {m : ℕ} (i : Fin m) (b : Bool) (j D : ℕ)
    (hD : ∀ l : Fin m, l ≠ i → pp l ∣ D) : del (i, b) (block m (j + D)) = del (i, b) (block m j) := by
  unfold block
  simp only [del, filter_flatMap]
  apply flatMap_congr
  intro l _
  by_cases hli : l = i
  · rw [hli]
    have h1 := del_pairBlk_self i (pp i) (j + D) b
    have h2 := del_pairBlk_self i (pp i) j b
    simp only [del] at h1 h2; rw [h1, h2]
  · have : pairBlk (pp l) (j + D) (l, false) (l, true) = pairBlk (pp l) j (l, false) (l, true) := by
      unfold pairBlk
      simp only [Nat.dvd_add_left (hD l hli)]
    rw [this]

/-- Projection of a block onto pair `i`. -/
lemma pair_block {m : ℕ} (i : Fin m) (j : ℕ) :
    pair (i, false) (i, true) (block m j) = pairBlk (pp i) j (i, false) (i, true) := by
  unfold block pair
  rw [filter_flatMap]
  have : ∀ l ∈ finRange m, (pairBlk (pp l) j (l, false) (l, true)).filter
      (fun z => decide (z = (i, false) ∨ z = (i, true)))
      = if l = i then pairBlk (pp i) j (i, false) (i, true) else [] := by
    intro l _
    by_cases hli : l = i
    · subst hli; unfold pairBlk; split_ifs <;> simp_all
    · unfold pairBlk; split_ifs <;> simp_all
  rw [flatMap_congr this]
  exact flatMap_ite_single _ i _ (nodup_finRange m) (mem_finRange i)

/-! ### The even word -/

theorem even_spec (m : ℕ) (hm : 1 ≤ m) :
    IsPrecarious (evenWord m) ∧ (evenWord m).toFinset.card = 2 * m ∧
      (evenWord m).length = 2 * m * pr m := by
  have hP : 0 < pr m := pr_pos m
  have hmem : ∀ c : Fin m × Bool, c ∈ evenWord m := by
    rintro ⟨i, b⟩
    unfold evenWord
    refine mem_flatMap.mpr ⟨0, mem_range.mpr hP, ?_⟩
    unfold block
    refine mem_flatMap.mpr ⟨i, mem_finRange i, ?_⟩
    cases b <;> simp [pairBlk]
  have hcard : (evenWord m).toFinset.card = 2 * m := by
    have : (evenWord m).toFinset = Finset.univ := Finset.eq_univ_of_forall (fun c => mem_toFinset.mpr (hmem c))
    rw [this, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, mul_comm]
  have hlen : (evenWord m).length = 2 * m * pr m := by
    simp [evenWord, length_flatMap, block_length, mul_comm]
  refine ⟨⟨?_, by omega, ?_⟩, hcard, hlen⟩
  · -- not a power
    rintro ⟨r, hr, v, hv⟩
    have i0 : (0 : ℕ) < m := hm
    let i : Fin m := ⟨0, i0⟩
    have hproj : pair (i, false) (i, true) (evenWord m)
        = (range (pr m)).flatMap (fun j => pairBlk (pp i) j (i, false) (i, true)) := by
      unfold evenWord pair; rw [filter_flatMap]
      exact flatMap_congr (fun j _ => pair_block i j)
    -- `r` divides the length `2 · pr m` of the projection, so a prime factor of `r` divides `pr m`
    have hlenproj : (pair (i, false) (i, true) (evenWord m)).length = 2 * pr m := by
      rw [hproj, length_flatMap]; simp [pairBlk_length, mul_comm]
    have hrd : r ∣ 2 * pr m := by
      rw [← hlenproj, pair, hv, filter_flatten_replicate, length_flatten_replicate]
      exact Dvd.intro _ rfl
    obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd (show r ≠ 1 by omega)
    have hpP : p ∣ pr m := by
      rcases (Nat.Prime.dvd_mul hp).mp (hpr.trans hrd) with h2 | h2
      · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
        subst this
        simpa [pp, Nat.nth_prime_zero_eq_two] using pp_dvd_pr (m := m) (l := 0) hm
      · exact h2
    obtain ⟨i', hi', rfl⟩ := prime_dvd_pr hp hpP
    let c : Fin m := ⟨i', hi'⟩
    obtain ⟨s, rfl⟩ := hpr
    have hproj' : pair (c, false) (c, true) (evenWord m)
        = (range (pr m)).flatMap (fun j => pairBlk (pp c) j (c, false) (c, true)) := by
      unfold evenWord pair; rw [filter_flatMap]
      exact flatMap_congr (fun j _ => pair_block c j)
    have hpowc : (range (pr m)).flatMap (fun j => pairBlk (pp c) j (c, false) (c, true))
        = (replicate (pp i') (((replicate s v).flatten).filter (fun z => z = (c, false) ∨ z = (c, true)))).flatten := by
      rw [← hproj', pair, hv, flatten_replicate_mul, filter_flatten_replicate]
    have := pairs_not_pow (pp i') (pr m) hp.two_le (c, false) (c, true) (by simp) (pp_dvd_pr hi') _ hpowc
    rw [pr_eq_mul m i' hi', Nat.mul_div_cancel_left _ hp.pos] at this
    exact not_pp_dvd_prOff m i' this
  · -- every deletion is a power
    rintro ⟨i, b⟩ _
    refine ⟨pp i, (pp_prime i).two_le, (range (prOff m i)).flatMap (fun j => del (i, b) (block m j)), ?_⟩
    have hdel : del (i, b) (evenWord m) = (range (pr m)).flatMap (fun j => del (i, b) (block m j)) := by
      unfold evenWord; simp only [del, filter_flatMap]
    rw [hdel, pr_eq_mul m i i.isLt]
    apply flatMap_range_periodic
    intro j
    exact del_block_shift i b j _ (fun l hli => pp_dvd_prOff l.isLt (fun h => hli (Fin.ext h)))

/-! ### The odd word -/

/-- Group `g`: the new colour `none`, then blocks `g q, …, g q + q - 1`, `q = p_m`. -/
noncomputable def group (m g : ℕ) : List (Option (Fin m × Bool)) :=
  none :: (range (pp m)).flatMap (fun t => (block m (g * pp m + t)).map some)

noncomputable def oddWord (m : ℕ) : List (Option (Fin m × Bool)) := (range (pr m)).flatMap (group m)

/-- Runs of `q` consecutive blocks, `n` times, are the first `n q` blocks. -/
lemma flatMap_range_groups {β : Type*} (f : ℕ → List β) (q : ℕ) :
    ∀ n, (range n).flatMap (fun g => (range q).flatMap (fun t => f (g * q + t))) = (range (n * q)).flatMap f := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [range_succ, flatMap_append, ih, Nat.succ_mul, range_add, flatMap_append, flatMap_map]
    simp

lemma map_some_pairBlk {β : Type*} (p j : ℕ) (x y : β) :
    (pairBlk p j x y).map some = pairBlk p j (some x) (some y) := by
  unfold pairBlk; split_ifs <;> simp

lemma filter_map_some {β : Type*} [DecidableEq β] (l : List β) (P : Option β → Prop) [DecidablePred P] :
    (l.map some).filter (fun z => decide (P z)) = (l.filter (fun z => decide (P (some z)))).map some := by
  rw [filter_map]; rfl

lemma block_shift_pr (m j : ℕ) : block m (j + pr m) = block m j := by
  unfold block
  apply flatMap_congr
  intro l _
  unfold pairBlk
  simp only [Nat.dvd_add_left (pp_dvd_pr l.isLt)]

theorem odd_spec (m : ℕ) (hm : 1 ≤ m) :
    IsPrecarious (oddWord m) ∧ (oddWord m).toFinset.card = 2 * m + 1 ∧
      (oddWord m).length = pr m * (2 * m * pp m + 1) := by
  have hP : 0 < pr m := pr_pos m
  have hq : 0 < pp m := (pp_prime m).pos
  have hmem : ∀ c : Option (Fin m × Bool), c ∈ oddWord m := by
    intro c
    unfold oddWord
    refine mem_flatMap.mpr ⟨0, mem_range.mpr hP, ?_⟩
    unfold group
    rcases c with _ | ⟨i, b⟩
    · simp
    · refine mem_cons_of_mem _ (mem_flatMap.mpr ⟨0, mem_range.mpr hq, ?_⟩)
      refine mem_map.mpr ⟨(i, b), ?_, rfl⟩
      unfold block
      refine mem_flatMap.mpr ⟨i, mem_finRange i, ?_⟩
      cases b <;> simp [pairBlk]
  have hcard : (oddWord m).toFinset.card = 2 * m + 1 := by
    have : (oddWord m).toFinset = Finset.univ :=
      Finset.eq_univ_of_forall (fun c => mem_toFinset.mpr (hmem c))
    rw [this, Finset.card_univ, Fintype.card_option, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, mul_comm]
  have hlen : (oddWord m).length = pr m * (2 * m * pp m + 1) := by
    simp [oddWord, group, length_flatMap, block_length]
    ring_nf
    simp
  refine ⟨⟨?_, by omega, ?_⟩, hcard, hlen⟩
  · -- not a power
    rintro ⟨r, hr, v, hv⟩
    -- the `none` beads: one per group
    have hnone : ((oddWord m).filter (fun z => decide (z = none))).length = pr m := by
      unfold oddWord
      rw [filter_flatMap, length_flatMap]
      have : ∀ g, ((group m g).filter (fun z => decide (z = none))).length = 1 := by
        intro g
        unfold group
        rw [filter_cons_of_pos (by simp), filter_flatMap]
        simp [filter_map, Function.comp_def]
      simp [this]
    have hrd : r ∣ pr m := by
      rw [← hnone, hv, filter_flatten_replicate, length_flatten_replicate]
      exact Dvd.intro _ rfl
    obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd (show r ≠ 1 by omega)
    obtain ⟨i', hi', rfl⟩ := prime_dvd_pr hp (hpr.trans hrd)
    let c : Fin m := ⟨i', hi'⟩
    obtain ⟨s, rfl⟩ := hpr
    have hproj : pair (some (c, false)) (some (c, true)) (oddWord m)
        = (range (pr m * pp m)).flatMap (fun j => pairBlk (pp c) j (some (c, false)) (some (c, true))) := by
      rw [← flatMap_range_groups]
      unfold oddWord pair
      rw [filter_flatMap]
      apply flatMap_congr
      intro g _
      unfold group
      rw [filter_cons_of_neg (by simp), filter_flatMap]
      apply flatMap_congr
      intro t _
      rw [filter_map_some (block m (g * pp m + t)) (fun z => z = some (c, false) ∨ z = some (c, true))]
      have := pair_block c (g * pp m + t)
      simp only [pair] at this
      simp only [Option.some.injEq]
      rw [this, map_some_pairBlk]
    have hpowc : (range (pr m * pp m)).flatMap (fun j => pairBlk (pp c) j (some (c, false)) (some (c, true)))
        = (replicate (pp i') (((replicate s v).flatten).filter
            (fun z => z = some (c, false) ∨ z = some (c, true)))).flatten := by
      rw [← hproj, pair, hv, flatten_replicate_mul, filter_flatten_replicate]
    have := pairs_not_pow (pp i') (pr m * pp m) hp.two_le _ _ (by simp)
      (Dvd.dvd.mul_right (pp_dvd_pr hi') _) _ hpowc
    rw [pr_eq_mul m i' hi', mul_assoc, Nat.mul_div_cancel_left _ hp.pos] at this
    rcases (Nat.Prime.dvd_mul hp).mp this with h | h
    · exact not_pp_dvd_prOff m i' h
    · have := (Nat.prime_dvd_prime_iff_eq hp (pp_prime m)).mp h
      exact absurd (pp_inj this) (by omega)
  · -- every deletion is a power
    rintro (_ | ⟨i, b⟩) _
    · -- delete `none`: the blocks repeat with period `pr m`
      refine ⟨pp m, (pp_prime m).two_le, (range (pr m)).flatMap (fun j => (block m j).map some), ?_⟩
      have hdel : del none (oddWord m) = (range (pr m * pp m)).flatMap (fun j => (block m j).map some) := by
        rw [← flatMap_range_groups]
        unfold oddWord del
        rw [filter_flatMap]
        apply flatMap_congr
        intro g _
        unfold group
        rw [filter_cons_of_neg (by simp), filter_flatMap]
        apply flatMap_congr
        intro t _
        rw [filter_map_some _ (fun z => z ≠ none)]
        simp
      rw [hdel, mul_comm]
      apply flatMap_range_periodic
      intro j; rw [block_shift_pr]
    · -- delete a colour of pair `i`: groups repeat with period `prOff m i`
      refine ⟨pp i, (pp_prime i).two_le,
        (range (prOff m i)).flatMap (fun g => del (some (i, b)) (group m g)), ?_⟩
      have hdel : del (some (i, b)) (oddWord m)
          = (range (pr m)).flatMap (fun g => del (some (i, b)) (group m g)) := by
        unfold oddWord; simp only [del, filter_flatMap]
      rw [hdel, pr_eq_mul m i i.isLt]
      apply flatMap_range_periodic
      intro g
      unfold group del
      rw [filter_cons_of_pos (by simp), filter_cons_of_pos (by simp), filter_flatMap, filter_flatMap]
      congr 1
      apply flatMap_congr
      intro t _
      rw [filter_map_some _ (fun z => z ≠ some (i, b)), filter_map_some _ (fun z => z ≠ some (i, b))]
      have hsh := del_block_shift i b (g * pp m + t) (prOff m i * pp m)
        (fun l hli => Dvd.dvd.mul_right (pp_dvd_prOff l.isLt (fun h => hli (Fin.ext h))) _)
      simp only [del] at hsh
      simp only [ne_eq, Option.some.injEq]
      rw [show (g + prOff m i) * pp m + t = g * pp m + t + prOff m i * pp m by ring, hsh]

/-! ### The theorem -/

/-- **MO 515996.** For `k ≥ 2` colours the shortest precarious necklace has length `a k`. -/
theorem precarious_min (k : ℕ) (hk : 2 ≤ k) :
    (∀ {α : Type} [DecidableEq α] (w : List α), IsPrecarious w → w.toFinset.card = k → a k ≤ w.length) ∧
    ∃ (β : Type) (_ : DecidableEq β) (w : List β),
      IsPrecarious w ∧ w.toFinset.card = k ∧ w.length = a k := by
  refine ⟨fun w hw hc => hc ▸ lower_bound w hw, ?_⟩
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := even_spec m (by omega)
    refine ⟨_, inferInstance, evenWord m, h1, by rw [h2]; ring, ?_⟩
    rw [h3, a, if_pos (by omega), show (m + m) / 2 = m by omega]; ring
  · obtain ⟨h1, h2, h3⟩ := odd_spec m (by omega)
    refine ⟨_, inferInstance, oddWord m, h1, h2, ?_⟩
    rw [h3, a, if_neg (by omega), show (2 * m + 1) / 2 = m by omega, show 2 * m + 1 - 1 = 2 * m by omega]

end Precarious
