import Mathlib

/-!
# Lemma 4.2 (pruning), on the reduced tree

Contract every segment of a tree to a single edge. The result `K` is a finite tree with no vertex of degree `2`;
its edges are the segments, an edge is *pendant* when one end has degree `1`, and `len e` is the segment's length.
For `D = (L, p, h, …, h)` at most two segments have length other than `h`.

Lemma 4.2 of the note: if some non-pendant segment has length `h`, then some non-pendant segment of length `h` is
adjacent to a pendant segment. The proof is the note's: take a component of the graph `J` of non-pendant
`h`-segments, take two leaves `u ≠ v` of it (a finite tree), and count. Each leaf has degree at least `3`, so it meets at
least two segments outside `J`; if neither carries a pendant segment these are all non-pendant of length `≠ h`.
Two at `u` and one at `v` not ending at `u` are three distinct such segments, but there are at most two.
Only acyclicity of `K` is used.
-/

namespace Remoteness.Prune

open SimpleGraph Finset

variable {V : Type*} [Fintype V] (K : SimpleGraph V) [DecidableRel K.Adj]

/-- **Lemma 4.2.** -/
theorem prune (hK : K.IsAcyclic) (len : Sym2 V → ℕ) (h : ℕ) (hdeg : ∀ v, K.degree v ≠ 2)
    (hspec : #(K.edgeFinset.filter (fun e => len e ≠ h)) ≤ 2)
    (u₀ v₀ : V) (h₀ : K.Adj u₀ v₀) (hu₀ : K.degree u₀ ≠ 1) (hv₀ : K.degree v₀ ≠ 1)
    (hl₀ : len s(u₀, v₀) = h) :
    ∃ a b c, K.Adj a b ∧ K.degree a ≠ 1 ∧ K.degree b ≠ 1 ∧ len s(a, b) = h ∧
      K.Adj b c ∧ K.degree c = 1 := by
  classical
  by_contra hno
  push Not at hno
  -- `J`: the non-pendant segments of length `h`
  let J : SimpleGraph V :=
    { Adj := fun a b => K.Adj a b ∧ K.degree a ≠ 1 ∧ K.degree b ≠ 1 ∧ len s(a, b) = h
      symm := ⟨fun a b hab => ⟨hab.1.symm, hab.2.2.1, hab.2.1, by rw [Sym2.eq_swap]; exact hab.2.2.2⟩⟩
      loopless := ⟨fun a ha => K.irrefl ha.1⟩ }
  have hJK : J ≤ K := fun a b hab => hab.1
  set S := K.edgeFinset.filter (fun e => len e ≠ h)
  -- a leaf `w` of `J` meets two segments of `S`
  have key : ∀ w, J.degree w = 1 → ∃ x₁ x₂, x₁ ≠ w ∧ x₂ ≠ w ∧ x₁ ≠ x₂ ∧ s(w, x₁) ∈ S ∧ s(w, x₂) ∈ S := by
    intro w hw
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp ((J.card_neighborFinset_eq_degree w).trans hw)
    have hyJ : J.Adj w y := (J.mem_neighborFinset w y).mp (hy ▸ Finset.mem_singleton_self y)
    have hwK : 3 ≤ K.degree w := by
      have h1 := hyJ.2.1
      have h2 := hdeg w
      have h0 : 0 < K.degree w := K.degree_pos_iff_exists_adj w |>.mpr ⟨y, hyJ.1⟩
      omega
    have hsub : J.neighborFinset w ⊆ K.neighborFinset w := fun x hx => by
      simp only [mem_neighborFinset] at hx ⊢; exact hx.1
    have hcard : 2 ≤ #(K.neighborFinset w \ J.neighborFinset w) := by
      rw [card_sdiff_of_subset hsub, card_neighborFinset_eq_degree, card_neighborFinset_eq_degree]; omega
    obtain ⟨x₁, hx₁, x₂, hx₂, hne⟩ := Finset.one_lt_card.mp hcard
    have hin : ∀ x ∈ K.neighborFinset w \ J.neighborFinset w, x ≠ w ∧ s(w, x) ∈ S := by
      intro x hx
      simp only [mem_sdiff, mem_neighborFinset] at hx
      obtain ⟨hKx, hJx⟩ := hx
      refine ⟨(K.ne_of_adj hKx).symm, ?_⟩
      simp only [S, mem_filter, mem_edgeFinset, mem_edgeSet]
      refine ⟨hKx, fun hlen => hJx ⟨hKx, hyJ.2.1, ?_, hlen⟩⟩
      exact hno y w x hyJ.1.symm hyJ.2.2.1 hyJ.2.1 (by rw [Sym2.eq_swap]; exact hyJ.2.2.2) hKx
    exact ⟨x₁, x₂, (hin x₁ hx₁).1, (hin x₂ hx₂).1, hne, (hin x₁ hx₁).2, (hin x₂ hx₂).2⟩
  -- two leaves of the component of `J` through the segment `u₀ v₀`
  let c := J.connectedComponentMk u₀
  have hJ₀ : J.Adj u₀ v₀ := ⟨h₀, hu₀, hv₀, hl₀⟩
  have htree := (hK.anti hJK).isTree_connectedComponent c
  have : Nontrivial c.supp :=
    ⟨⟨⟨u₀, rfl⟩, ⟨v₀, (ConnectedComponent.connectedComponentMk_eq_of_adj hJ₀).symm⟩, by
      simp [Subtype.ext_iff, K.ne_of_adj h₀]⟩⟩
  obtain ⟨u, v, huv, hu, hv⟩ := htree.exists_ne_and_degree_eq_one
  have hdegJ : ∀ w : c.supp, c.toSimpleGraph.degree w = 1 → J.degree w = 1 := by
    intro w hw
    have e := degree_induce_of_neighborSet_subset (G := J) (s := c.supp) (v := w)
      (fun x (hx : J.Adj w x) => (c.mem_supp_congr_adj hx).mp w.2)
    rw [← e]; convert hw; rfl
  obtain ⟨x₁, x₂, hx₁, hx₂, hx, hS₁, hS₂⟩ := key u (hdegJ u hu)
  obtain ⟨y₁, y₂, -, -, hy, hT₁, hT₂⟩ := key v (hdegJ v hv)
  have huv' : (u : V) ≠ v := fun e => huv (Subtype.ext e)
  -- one of `v`'s segments does not end at `u`
  obtain ⟨y, hyu, hT⟩ : ∃ y, y ≠ (u : V) ∧ s((v : V), y) ∈ S := by
    by_cases h1 : y₁ = u
    · exact ⟨y₂, fun e => hy (h1.trans e.symm), hT₂⟩
    · exact ⟨y₁, h1, hT₁⟩
  have h3 : 2 < #S := Finset.two_lt_card.mpr
    ⟨_, hS₁, _, hS₂, _, hT, by simp; grind, by simp; grind,
      by simp; grind⟩
  omega

end Remoteness.Prune
