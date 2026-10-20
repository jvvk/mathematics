import LeanProofs.Precarious.Closed
import LeanProofs.Precarious.Extensions

/-!
# Precarious necklaces (MO 515996): the closed form, constructions and the theorem

* Odd `s = 2h + 1`: `extWord (h + 1) (k - 2h - 2)` (pair rhythms plus fixed colours), from `Extensions`.
* Even `s = 2h`: `clusterWord h n`: `h` pair rhythms over `p_h# · p_{h+1}` blocks, with a cluster of `n` new
  colours before each group of `p_{h+1}` blocks. A kept set of size `2h` either misses a pair colour (the
  groups repeat with period `p_h# / p_i`) or is exactly the pair colours (the blocks repeat with period `p_h#`).

`keep_exact`: for `1 ≤ s < k`, the minimum length of a necklace with `k` colours that is not symmetric but
becomes symmetric on keeping any `s` colours is `s · p_{⌊s/2⌋+1}# + (k - s) · p_{⌈s/2⌉}#`.
-/

set_option linter.unusedSectionVars false

namespace Precarious

open List

/-- Group `g`: the cluster, then blocks `g q, …, g q + q - 1`, `q = p_h`. -/
noncomputable def cgroup (h n g : ℕ) : List (Fin h × Bool ⊕ Fin n) :=
  (finRange n).map Sum.inr ++ (range (pp h)).flatMap (fun t => (block h (g * pp h + t)).map Sum.inl)

noncomputable def clusterWord (h n : ℕ) : List (Fin h × Bool ⊕ Fin n) := (range (pr h)).flatMap (cgroup h n)

lemma clusterWord_length (h n : ℕ) : (clusterWord h n).length = 2 * h * pr (h + 1) + n * pr h := by
  simp [clusterWord, cgroup, length_flatMap, block_length, pr_succ]
  ring

lemma clusterWord_card (h n : ℕ) : (clusterWord h n).toFinset.card = 2 * h + n := by
  have hP : 0 < pr h := pr_pos h
  have hq : 0 < pp h := (pp_prime h).pos
  have : (clusterWord h n).toFinset = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro z
    rw [mem_toFinset]
    unfold clusterWord
    refine mem_flatMap.mpr ⟨0, mem_range.mpr hP, ?_⟩
    unfold cgroup
    rcases z with ⟨i, b⟩ | e
    · refine mem_append_right _ (mem_flatMap.mpr ⟨0, mem_range.mpr hq, mem_map.mpr ⟨(i, b), ?_, rfl⟩⟩)
      unfold block
      refine mem_flatMap.mpr ⟨i, mem_finRange i, ?_⟩
      cases b <;> simp [pairBlk]
    · exact mem_append_left _ (mem_map.mpr ⟨e, mem_finRange e, rfl⟩)
  rw [this, Finset.card_univ, Fintype.card_sum, Fintype.card_prod]
  simp [mul_comm]

/-- Keeping a set that misses a colour of pair `i`: the groups repeat with period `prOff h i`. -/
lemma clusterWord_keep_miss (h n : ℕ) (S : Finset (Fin h × Bool ⊕ Fin n)) (i : Fin h) (b : Bool)
    (hS : Sum.inl (i, b) ∉ S) : Symm (keep S (clusterWord h n)) := by
  set f : Fin h × Bool ⊕ Fin n → Bool := fun z => decide (z ∈ S) with hfdef
  set g : Fin h × Bool → Bool := fun z => f (Sum.inl z) with hgdef
  have hg : g (i, false) = false ∨ g (i, true) = false := by
    cases b
    · left; simp [hgdef, hfdef, hS]
    · right; simp [hgdef, hfdef, hS]
  refine ⟨pp i, (pp_prime i).two_le, (range (prOff h i)).flatMap (fun G => (cgroup h n G).filter f), ?_⟩
  have h1 : keep S (clusterWord h n) = (range (pr h)).flatMap (fun G => (cgroup h n G).filter f) := by
    unfold keep clusterWord; rw [filter_flatMap]
  rw [h1, pr_eq_mul h i i.isLt]
  apply flatMap_range_periodic
  intro G
  have hsh : ∀ t, ((block h ((G + prOff h i) * pp h + t)).filter g) = (block h (G * pp h + t)).filter g := by
    intro t
    rw [show (G + prOff h i) * pp h + t = G * pp h + t + prOff h i * pp h by ring]
    exact filter_block_shift g i hg (G * pp h + t) (prOff h i * pp h)
      (fun l hli => Dvd.dvd.mul_right (pp_dvd_prOff l.isLt (fun h' => hli (Fin.ext h'))) _)
  have hc : f ∘ Sum.inl = g := rfl
  unfold cgroup
  simp only [filter_append, filter_flatMap, filter_map, hc]
  congr 1
  exact flatMap_congr (fun t _ => by rw [hsh t])

/-- Keeping exactly the pair colours: the blocks repeat with period `pr h`. -/
lemma clusterWord_keep_pairs (h n : ℕ) (S : Finset (Fin h × Bool ⊕ Fin n))
    (hS : ∀ e : Fin n, Sum.inr e ∉ S) (hS' : ∀ ib : Fin h × Bool, Sum.inl ib ∈ S) :
    Symm (keep S (clusterWord h n)) := by
  refine ⟨pp h, (pp_prime h).two_le, (range (pr h)).flatMap (fun j => (block h j).map Sum.inl), ?_⟩
  have h1 : keep S (clusterWord h n) = (range (pr h * pp h)).flatMap (fun j => (block h j).map Sum.inl) := by
    rw [← flatMap_range_groups]
    unfold keep clusterWord
    rw [filter_flatMap]
    apply flatMap_congr
    intro G _
    unfold cgroup
    rw [filter_append, filter_flatMap]
    have hE : ((finRange n).map Sum.inr).filter (fun z => decide (z ∈ S)) = [] := by
      rw [filter_map]; simp [Function.comp_def, hS]
    rw [hE, nil_append]
    apply flatMap_congr
    intro t _
    rw [filter_map]
    have : (fun z => decide (z ∈ S)) ∘ (Sum.inl : Fin h × Bool → Fin h × Bool ⊕ Fin n) = fun _ => true := by
      funext z; simp [hS' z]
    rw [this, filter_true]
  rw [h1, mul_comm]
  apply flatMap_range_periodic
  intro j; rw [block_shift_pr]

theorem clusterWord_not_symm (h n : ℕ) (hh : 1 ≤ h) (hn : 1 ≤ n) : ¬ Symm (clusterWord h n) := by
  rintro ⟨r, hr, v, hv⟩
  set e0 : Fin n := ⟨0, hn⟩
  -- one bead of `e0` per group
  have hcl : ((clusterWord h n).filter (fun z => decide (z = Sum.inr e0))).length = pr h := by
    unfold clusterWord
    rw [filter_flatMap, length_flatMap]
    have : ∀ G, ((cgroup h n G).filter (fun z => decide (z = Sum.inr e0))).length = 1 := by
      intro G
      unfold cgroup
      have h1 : (fun z => decide (z = Sum.inr e0)) ∘ (Sum.inr : Fin n → Fin h × Bool ⊕ Fin n)
          = fun z => decide (z = e0) := by funext z; simp
      rw [filter_append, filter_flatMap, filter_map, h1, filter_finRange_eq]
      simp [filter_map, Function.comp_def]
    simp [this]
  have hrd : r ∣ pr h := by
    rw [← hcl, hv, filter_flatten_replicate, length_flatten_replicate]
    exact Dvd.intro _ rfl
  obtain ⟨p, hp, hpr⟩ := Nat.exists_prime_and_dvd (show r ≠ 1 by omega)
  obtain ⟨i', hi', rfl⟩ := prime_dvd_pr hp (hpr.trans hrd)
  let c : Fin h := ⟨i', hi'⟩
  obtain ⟨s, rfl⟩ := hpr
  have hproj : pair (Sum.inl (c, false)) (Sum.inl (c, true)) (clusterWord h n)
      = (range (pr h * pp h)).flatMap
          (fun j => pairBlk (pp c) j (Sum.inl (c, false) : Fin h × Bool ⊕ Fin n) (Sum.inl (c, true))) := by
    rw [← flatMap_range_groups]
    unfold clusterWord pair
    rw [filter_flatMap]
    apply flatMap_congr
    intro G _
    unfold cgroup
    rw [filter_append, filter_flatMap]
    have hE : ((finRange n).map Sum.inr).filter
        (fun z => decide (z = (Sum.inl (c, false) : Fin h × Bool ⊕ Fin n) ∨ z = Sum.inl (c, true))) = [] := by
      rw [filter_map]; simp [Function.comp_def]
    rw [hE, nil_append]
    apply flatMap_congr
    intro t _
    rw [filter_map]
    have hpb := pair_block c (G * pp h + t)
    simp only [pair] at hpb
    have : (fun z => decide (z = (Sum.inl (c, false) : Fin h × Bool ⊕ Fin n) ∨ z = Sum.inl (c, true))) ∘ Sum.inl
        = fun z => decide (z = (c, false) ∨ z = (c, true)) := by funext z; simp
    rw [this, hpb]
    unfold pairBlk; split_ifs <;> simp
  have hpowc : (range (pr h * pp h)).flatMap
      (fun j => pairBlk (pp c) j (Sum.inl (c, false) : Fin h × Bool ⊕ Fin n) (Sum.inl (c, true)))
      = (replicate (pp i') (((replicate s v).flatten).filter
          (fun z => z = Sum.inl (c, false) ∨ z = Sum.inl (c, true)))).flatten := by
    rw [← hproj, pair, hv, flatten_replicate_mul, filter_flatten_replicate]
  have := pairs_not_pow (pp i') (pr h * pp h) hp.two_le _ _ (by simp)
    (Dvd.dvd.mul_right (pp_dvd_pr hi') _) _ hpowc
  rw [pr_eq_mul h i' hi', mul_assoc, Nat.mul_div_cancel_left _ hp.pos] at this
  rcases (Nat.Prime.dvd_mul hp).mp this with hd | hd
  · exact not_pp_dvd_prOff h i' hd
  · have := (Nat.prime_dvd_prime_iff_eq hp (pp_prime h)).mp hd
    exact absurd (pp_inj this) (by omega)

theorem clusterWord_keepPrec (h n : ℕ) (hh : 1 ≤ h) (hn : 1 ≤ n) : KeepPrec (2 * h) (clusterWord h n) := by
  refine ⟨clusterWord_not_symm h n hh hn, fun S _ hSs => ?_⟩
  by_cases hall : ∀ ib : Fin h × Bool, Sum.inl ib ∈ S
  · apply clusterWord_keep_pairs h n S _ hall
    intro e he
    have hsub : insert (Sum.inr e) ((Finset.univ : Finset (Fin h × Bool)).map ⟨Sum.inl, Sum.inl_injective⟩) ⊆ S := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact he
      · obtain ⟨ib, _, rfl⟩ := Finset.mem_map.mp hz; exact hall ib
    have := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_map, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_bool] at this
    omega
  · push Not at hall
    obtain ⟨⟨i, b⟩, hib⟩ := hall
    exact clusterWord_keep_miss h n S i b hib

/-- **The closed form.** For `1 ≤ s < k`: keeping any `s` of `k` colours symmetric needs, and can be done
with, exactly `s · p_{⌊s/2⌋+1}# + (k - s) · p_{⌈s/2⌉}#` beads. -/
theorem keep_exact (k s : ℕ) (hs : 1 ≤ s) (hsk : s < k) :
    (∀ {α : Type} [DecidableEq α] (w : List α), KeepPrec s w → w.toFinset.card = k →
        closedForm k s ≤ w.length) ∧
    ∃ (β : Type) (_ : DecidableEq β) (w : List β),
      KeepPrec s w ∧ w.toFinset.card = k ∧ w.length = closedForm k s := by
  refine ⟨fun w hw hc => hc ▸ keep_general_bound s hs w hw (by omega), ?_⟩
  rcases Nat.even_or_odd s with ⟨h, rfl⟩ | ⟨h, rfl⟩
  · -- even: the cluster word
    refine ⟨_, inferInstance, clusterWord h (k - (h + h)), ?_, ?_, ?_⟩
    · have := clusterWord_keepPrec h (k - (h + h)) (by omega) (by omega)
      rwa [show 2 * h = h + h by ring] at this
    · rw [clusterWord_card]; omega
    · rw [clusterWord_length, closedForm, show (h + h) / 2 + 1 = h + 1 by omega,
        show (h + h + 1) / 2 = h by omega]
      ring_nf
  · -- odd: pair rhythms plus fixed colours
    refine ⟨_, inferInstance, extWord (h + 1) (k - (2 * h + 2)), ?_, ?_, ?_⟩
    · exact extWord_keepPrec (h + 1) _ (2 * h + 1) (by omega) (by omega)
    · rw [extWord_card (h + 1) _ (by omega)]; omega
    · rw [extWord_length, closedForm, show (2 * h + 1) / 2 + 1 = h + 1 by omega,
        show (2 * h + 1 + 1) / 2 = h + 1 by omega, ← add_mul]
      congr 1; omega

/-- At `s = k - 1` (delete one colour) the closed form is the original `a k`. -/
lemma closedForm_top (k : ℕ) (hk : 2 ≤ k) : closedForm k (k - 1) = a k := by
  unfold closedForm a
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [if_pos (by omega), show (m + m - 1) / 2 + 1 = m by omega, show (m + m - 1 + 1) / 2 = m by omega,
      show (m + m) / 2 = m by omega, show m + m - (m + m - 1) = 1 by omega]
    have : m + m - 1 + 1 = m + m := by omega
    nlinarith [this]
  · rw [if_neg (by omega), show (2 * m + 1 - 1) / 2 + 1 = m + 1 by omega,
      show (2 * m + 1 - 1 + 1) / 2 = m by omega, show (2 * m + 1) / 2 = m by omega,
      show 2 * m + 1 - (2 * m + 1 - 1) = 1 by omega, show 2 * m + 1 - 1 = 2 * m by omega, pr_succ]
    ring

end Precarious

namespace Precarious

open List

variable {α : Type*} [DecidableEq α]

lemma keep_erase_eq_del (w : List α) (c : α) : keep (w.toFinset.erase c) w = del c w := by
  unfold keep del
  apply List.filter_congr
  intro z hz
  simp [Finset.mem_erase, List.mem_toFinset.mpr hz]

/-- The original question is the case `s = k - 1`: deleting one colour is keeping the other `k - 1`. -/
theorem isPrecarious_iff_keepPrec (w : List α) (h2 : 2 ≤ w.toFinset.card) :
    IsPrecarious w ↔ KeepPrec (w.toFinset.card - 1) w := by
  constructor
  · rintro ⟨hns, -, hdel⟩
    refine ⟨hns, fun S hSC hSs => ?_⟩
    -- `S` is everything but one colour `c`
    obtain ⟨c, hcC, hcS⟩ : ∃ c ∈ w.toFinset, c ∉ S := by
      by_contra h; push Not at h
      have := Finset.card_le_card (fun z hz => h z hz : w.toFinset ⊆ S); omega
    have hS : S = w.toFinset.erase c := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz; exact Finset.mem_erase.mpr ⟨fun h => hcS (h ▸ hz), hSC hz⟩
      · rw [Finset.card_erase_of_mem hcC, hSs]
    rw [hS, keep_erase_eq_del]
    exact hdel c (List.mem_toFinset.mp hcC)
  · rintro ⟨hns, hkeep⟩
    refine ⟨hns, h2, fun c hc => ?_⟩
    rw [← keep_erase_eq_del]
    exact hkeep _ (Finset.erase_subset _ _) (by rw [Finset.card_erase_of_mem (List.mem_toFinset.mpr hc)])

end Precarious
