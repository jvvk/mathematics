import LeanProofs.TriChains.Layouts
import LeanProofs.TriChains.SmallCases

/-!
# Triangular chains and necklaces for every admissible `n`

* `good_all`: from the base hypothesis (chains `Good N` for `54 ≤ N ≤ 2673`, verified by computer in
  `verify/recheck/recheck.py`), every `N ≥ 54` has a `Good` chain: write `N = 49 n + r`, `28 ≤ r ≤ 76`,
  and apply `step` with `layout r (n % 2)` to the chains for `n` and `n + 1`.
* `berlekamp_guy`: chains for `n = 2` and every `n ≥ 9`; necklaces for every `n ≥ 12`, `n ≠ 14`.
  (Nonexistence for the remaining `n` is an exhaustive search, done in Python: `verify/small_cases.py`.)
-/

namespace TriChains

/-- The computer-verified base: a `Good` chain for every `54 ≤ N ≤ 2673`. -/
def BaseHyp : Prop := ∀ N, 54 ≤ N → N ≤ 2673 → ∃ l, Good N l

theorem good_all (base : BaseHyp) : ∀ N, 54 ≤ N → ∃ l, Good N l := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN
    by_cases hb : N ≤ 2673
    · exact base N hN hb
    · push_neg at hb
      obtain ⟨s, hs⟩ := ih ((N - 28) / 49) (by omega) (by omega)
      obtain ⟨t, ht⟩ := ih ((N - 28) / 49 + 1) (by omega) (by omega)
      have hv := layout_valid (N - 49 * ((N - 28) / 49)) ((N - 28) / 49 % 2) (by omega) (by omega)
        (Nat.mod_lt _ (by norm_num))
      have hg := step (by omega) hs ht hv
      have hN' : 49 * ((N - 28) / 49) + (N - 49 * ((N - 28) / 49)) = N := by omega
      exact ⟨_, hN' ▸ hg⟩

theorem triChain_of_good {N : ℕ} {l : List ℤ} (h : Good N l) : TriChain N l :=
  ⟨h.nodup, mem_iff_of_nodup h.nodup h.len h.range, h.chain.imp fun _ _ hab => hab.1⟩

theorem triNecklace_of_good {N : ℕ} {l : List ℤ} (h : Good N l) : TriNecklace N l := by
  refine ⟨triChain_of_good h, 1, bEnd N, h.head, h.last, ?_⟩
  unfold bEnd; split_ifs
  · exact ⟨2, by norm_num⟩
  · exact ⟨4, by norm_num⟩

/-- **Berlekamp-Guy.** Triangular chains exist for `n = 2` and all `n ≥ 9`; triangular necklaces exist for
all `n ≥ 12` except `n = 14`. Conditional on the computer-verified base `BaseHyp`. -/
theorem berlekamp_guy (base : BaseHyp) :
    (∀ N, (N = 2 ∨ 9 ≤ N) → ∃ l, TriChain N l) ∧ (∀ N, 12 ≤ N → N ≠ 14 → ∃ l, TriNecklace N l) := by
  refine ⟨fun N hN => ?_, fun N h1 h2 => ?_⟩
  · by_cases h : N ≤ 53
    · exact small_chains N (by omega)
    · obtain ⟨l, hl⟩ := good_all base N (by omega); exact ⟨l, triChain_of_good hl⟩
  · by_cases h : N ≤ 53
    · exact small_necklaces N h1 h h2
    · obtain ⟨l, hl⟩ := good_all base N (by omega); exact ⟨l, triNecklace_of_good hl⟩

end TriChains
