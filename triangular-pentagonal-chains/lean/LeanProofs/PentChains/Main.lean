import LeanProofs.PentChains.Layouts
import LeanProofs.PentChains.SmallCases

/-!
# Pentagonal chains and necklaces for every admissible `n` (a Berlekamp-Guy conjecture)

* `good_all`: from the base hypothesis (chains `Good N` for `60 ≤ N ≤ 2965`, verified by computer in
  pentagonal-sum-chains/verify/recheck/recheck.py), every `N ≥ 60` has a `Good` chain: `N = 49 n + r`,
  `26 ≤ r ≤ 74`, `step` with `layout r (n % 2)`.
* `berlekamp_guy`: pentagonal chains for every `n ≥ 4`; necklaces for every `n ≥ 9`.
  (Nonexistence for `n = 2, 3` and necklaces `3 ≤ n ≤ 8`: exhaustive search in Python.)
-/

namespace PentChains

/-- The computer-verified base: a `Good` chain for every `60 ≤ N ≤ 2965`. -/
def BaseHyp : Prop := ∀ N, 60 ≤ N → N ≤ 2965 → ∃ l, Good N l

theorem good_all (base : BaseHyp) : ∀ N, 60 ≤ N → ∃ l, Good N l := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    by_cases hb : N ≤ 2965
    · exact base N hN hb
    · push_neg at hb
      obtain ⟨s, hs⟩ := ih ((N - 26) / 49) (by omega) (by omega)
      obtain ⟨t, ht⟩ := ih ((N - 26) / 49 + 1) (by omega) (by omega)
      have hv := layout_valid (N - 49 * ((N - 26) / 49)) ((N - 26) / 49 % 2) (by omega) (by omega)
        (Nat.mod_lt _ (by norm_num))
      have hg := step (by omega) hs ht hv
      have hN' : 49 * ((N - 26) / 49) + (N - 49 * ((N - 26) / 49)) = N := by omega
      exact ⟨_, hN' ▸ hg⟩

theorem triChain_of_good {N : ℕ} {l : List ℤ} (h : Good N l) : TriChain N l :=
  ⟨h.nodup, mem_iff_of_nodup h.nodup h.len h.range, h.chain.imp fun _ _ hab => hab.1⟩

theorem triNecklace_of_good {N : ℕ} {l : List ℤ} (h : Good N l) : TriNecklace N l := by
  refine ⟨triChain_of_good h, 3, bEnd N, h.head, h.last, ?_⟩
  unfold bEnd; split_ifs
  · exact ⟨2, by norm_num⟩
  · exact ⟨4, by norm_num⟩

/-- **Berlekamp-Guy, pentagonal case.** Chains with generalized pentagonal adjacent sums exist for all `n ≥ 4`;
necklaces for all `n ≥ 9`. Conditional on the computer-verified base `BaseHyp`. -/
theorem berlekamp_guy (base : BaseHyp) :
    (∀ N, 4 ≤ N → ∃ l, TriChain N l) ∧ (∀ N, 9 ≤ N → ∃ l, TriNecklace N l) := by
  refine ⟨fun N hN => ?_, fun N h1 => ?_⟩
  · by_cases h : N ≤ 59
    · exact small_chains N hN h
    · obtain ⟨l, hl⟩ := good_all base N (by omega); exact ⟨l, triChain_of_good hl⟩
  · by_cases h : N ≤ 59
    · exact small_necklaces N h1 h
    · obtain ⟨l, hl⟩ := good_all base N (by omega); exact ⟨l, triNecklace_of_good hl⟩

end PentChains
