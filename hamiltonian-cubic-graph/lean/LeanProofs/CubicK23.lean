import Mathlib

/-!
# A Hamiltonian, non-bipartite cubic graph with no cycle of length `n - 1`

MathOverflow question 263706 asks for a non-bipartite Hamiltonian cubic graph on `n` vertices with
no cycle of length `n - 1`. Take `K₄` and replace each vertex `v` by a copy `X_v` of `K_{2,3}`,
attaching the three edges of `K₄` at `v` to the three vertices of the larger class of `X_v`.

Vertices are pairs `(v, i)` with `v : Fin 4` the block and `i : Fin 5` the position: positions
`0, 1` form the inner class of `K_{2,3}`, positions `2, 3, 4` the attachment class. The attachment
`(v, 2 + j)` is joined to the attachment `(v + j + 1, 4 - j)` of another block.

Main results:
* `cubic`: every vertex has degree three;
* `hamiltonian`: an explicit cycle through all twenty vertices;
* `not_bipartite`: the graph is not 2-colourable (an explicit 9-cycle);
* `no_cycle_nineteen`: there is no cycle of length nineteen.

The proof of the last follows the counting argument: in the block containing the vertex the cycle
misses, the four other vertices have degree two in the cycle, so twice the number of cycle edges
inside the block plus the number leaving it is eight. Every inner edge meets exactly one inner
vertex, and the inner vertices have all their cycle edges inside the block. If the missing vertex is
inner this forces four cycle edges to leave through three attachments, which is impossible; if it is
an attachment, no cycle edge leaves the block, and the cycle is trapped among five vertices.
-/

namespace CubicK23

abbrev V := Fin 4 × Fin 5

/-- The attachment `(v, 2 + j)` is joined to `(v + j + 1, 4 - j)`. -/
def partner (x : V) : V :=
  (x.1 + ⟨(x.2.val + 3) % 4, Nat.mod_lt _ (by norm_num)⟩, ⟨(6 - x.2.val) % 5, Nat.mod_lt _ (by norm_num)⟩)

/-- Adjacency: inner to attachment inside a block, or an attachment to its partner. -/
def adjB (x y : V) : Bool :=
  (x.1 == y.1 && (decide (x.2.val < 2) != decide (y.2.val < 2))) ||
    (decide (2 ≤ x.2.val) && decide (2 ≤ y.2.val) && y == partner x)

theorem adjB_symm : ∀ x y : V, adjB x y = true → adjB y x = true := by decide

theorem adjB_irrefl : ∀ x : V, adjB x x = false := by decide

def G : SimpleGraph V where
  Adj x y := adjB x y = true
  symm := ⟨fun x y h => adjB_symm x y h⟩
  loopless := ⟨fun x h => by simp [adjB_irrefl x] at h⟩

instance : DecidableRel G.Adj := fun x y => inferInstanceAs (Decidable (adjB x y = true))

theorem card_V : Fintype.card V = 20 := by decide

/-- Every vertex has degree three. -/
theorem cubic : ∀ x : V, G.degree x = 3 := by decide +kernel

/-! ## Hamiltonian, and not bipartite -/

/-- A cyclic list of vertices whose consecutive entries (and last and first) are adjacent. -/
def IsCycleList (l : List V) : Prop :=
  l.Nodup ∧ 3 ≤ l.length ∧ ∀ p ∈ l.zip (l.rotate 1), G.Adj p.1 p.2

instance (l : List V) : Decidable (IsCycleList l) := by unfold IsCycleList; infer_instance

/-- Follow the Hamiltonian cycle `0, 1, 2, 3` of `K₄`, crossing each block by a Hamiltonian path
between two attachments. -/
def hamCycle : List V :=
  (List.finRange 4).flatMap fun v => [(v, 4), (v, 0), (v, 3), (v, 1), (v, 2)]

theorem hamiltonian : IsCycleList hamCycle ∧ hamCycle.length = 20 := by decide +kernel

/-- A triangle of `K₄` becomes a 9-cycle: three paths of length two and three partner edges. -/
def oddCycle : List V := [(0, 3), (0, 0), (0, 2), (1, 4), (1, 0), (1, 2), (2, 4), (2, 0), (2, 3)]

theorem oddCycle_isCycle : IsCycleList oddCycle ∧ oddCycle.length = 9 := by decide +kernel

/-- The graph is not bipartite. -/
theorem not_bipartite : ¬ G.Colorable 2 := by
  rintro ⟨c⟩
  have h : ∀ x y : V, G.Adj x y → c x ≠ c y := fun x y hxy => c.valid hxy
  have key : ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 : Fin 2,
      a0 ≠ a1 → a1 ≠ a2 → a2 ≠ a3 → a3 ≠ a4 → a4 ≠ a5 → a5 ≠ a6 → a6 ≠ a7 → a7 ≠ a8 → a8 ≠ a0 →
      False := by
    intro a0 a1 a2 a3 a4 a5 a6 a7 a8 h0 h1 h2 h3 h4 h5 h6 h7 h8
    simp only [ne_eq, Fin.ext_iff] at h0 h1 h2 h3 h4 h5 h6 h7 h8
    have := a0.isLt; have := a1.isLt; have := a2.isLt; have := a3.isLt; have := a4.isLt
    have := a5.isLt; have := a6.isLt; have := a7.isLt; have := a8.isLt
    omega
  exact key _ _ _ _ _ _ _ _ _ (h (0, 3) (0, 0) (by decide)) (h (0, 0) (0, 2) (by decide))
    (h (0, 2) (1, 4) (by decide)) (h (1, 4) (1, 0) (by decide)) (h (1, 0) (1, 2) (by decide))
    (h (1, 2) (2, 4) (by decide)) (h (2, 4) (2, 0) (by decide)) (h (2, 0) (2, 3) (by decide))
    (h (2, 3) (0, 3) (by decide))

/-! ## No cycle of length nineteen -/

/-- Neighbourhoods of the inner vertices: the three attachments of their block. -/
theorem adj_inner (w : Fin 4) (i : Fin 5) (hi : i.val < 2) (y : V) (h : G.Adj (w, i) y) :
    y = (w, 2) ∨ y = (w, 3) ∨ y = (w, 4) := by
  revert w i y; decide +kernel

/-- Neighbourhoods of the attachments: the two inner vertices of their block and the partner. -/
theorem adj_attach (w : Fin 4) (j : Fin 5) (hj : 2 ≤ j.val) (y : V) (h : G.Adj (w, j) y) :
    y = (w, 0) ∨ y = (w, 1) ∨ y = partner (w, j) := by
  revert w j y; decide +kernel

theorem partner_block_ne (w : Fin 4) (j : Fin 5) (hj : 2 ≤ j.val) : (partner (w, j)).1 ≠ w := by
  revert w j; decide +kernel

section Count

open Classical

variable (H : G.Subgraph)

/-- `a x y` is `1` if `x y` is an edge of `H`, else `0`. -/
noncomputable def a (x y : V) : ℕ := if H.Adj x y then 1 else 0

theorem a_le_one (x y : V) : a H x y ≤ 1 := by unfold a; split_ifs <;> simp

theorem a_symm (x y : V) : a H x y = a H y x := by
  unfold a; by_cases h : H.Adj x y
  · simp [h, h.symm]
  · have h' : ¬ H.Adj y x := fun h' => h h'.symm
    simp [h, h']

/-- The degree of `x` in `H`, counted over a set containing all its neighbours in `G`. -/
theorem card_filter_eq_sum (x : V) (N : Finset V) (hN : ∀ y, G.Adj x y → y ∈ N) :
    (Finset.univ.filter (H.Adj x)).card = ∑ y ∈ N, a H x y := by
  rw [Finset.card_filter]
  refine (Finset.sum_subset (Finset.subset_univ N) ?_).symm
  intro y _ hy
  have : ¬ H.Adj x y := fun h => hy (hN y (H.adj_sub h))
  simp [this]

end Count

theorem block_card : ∀ w : Fin 4, (Finset.univ.filter (fun x : V => x.1 = w)).card = 5 := by
  decide +kernel

open Classical in
/-- There is no cycle of length nineteen. -/
theorem no_cycle_nineteen {u : V} (p : G.Walk u u) (hp : p.IsCycle) : p.length ≠ 19 := by
  intro hlen
  set H := p.toSubgraph with hH
  -- degrees in the cycle
  have hdeg2 : ∀ x ∈ p.support, (Finset.univ.filter (H.Adj x)).card = 2 := by
    intro x hx
    rw [← hp.ncard_neighborSet_toSubgraph_eq_two hx, ← Set.ncard_coe_finset]
    congr 1
    ext y
    simp [hH, SimpleGraph.Subgraph.mem_neighborSet]
  have hnot : ∀ x, x ∉ p.support → ∀ y, ¬ H.Adj x y := by
    intro x hx y h
    exact hx ((p.mem_verts_toSubgraph).1 (H.edge_vert h))
  -- the cycle visits nineteen distinct vertices
  have hnil : ¬ p.Nil := fun h => by simp [SimpleGraph.Walk.length_eq_zero_iff.mpr h] at hlen
  have hsupp : p.support.toFinset = p.support.tail.toFinset := by
    ext x
    rw [List.mem_toFinset, List.mem_toFinset, ← p.cons_tail_support]
    simp only [List.mem_cons, List.tail_cons]
    constructor
    · rintro (rfl | h)
      · exact SimpleGraph.Walk.end_mem_tail_support hnil
      · exact h
    · exact Or.inr
  have hcard : p.support.toFinset.card = 19 := by
    rw [hsupp, List.toFinset_card_of_nodup hp.support_nodup, List.length_tail,
      SimpleGraph.Walk.length_support, hlen]
  -- the missing vertex
  obtain ⟨m, hm⟩ : ∃ m : V, m ∉ p.support := by
    by_contra! h
    have : p.support.toFinset = Finset.univ := by
      ext x; simp [h x]
    have := congrArg Finset.card this
    rw [hcard, Finset.card_univ, card_V] at this
    norm_num at this
  have honly : ∀ x : V, x ≠ m → x ∈ p.support := by
    intro x hx
    by_contra hxs
    have hsub : p.support.toFinset ⊆ (Finset.univ.erase m).erase x := by
      intro y hy
      rw [List.mem_toFinset] at hy
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact ⟨fun h => hxs (h ▸ hy), fun h => hm (h ▸ hy)⟩
    have := Finset.card_le_card hsub
    rw [hcard, Finset.card_erase_of_mem (by simp [hx]), Finset.card_erase_of_mem (by simp),
      Finset.card_univ, card_V] at this
    norm_num at this
  -- degrees of the five vertices of the block of `m`
  obtain ⟨w, k⟩ := m
  have hdeg : ∀ i : Fin 5, (Finset.univ.filter (H.Adj (w, i))).card = if i = k then 0 else 2 := by
    intro i
    split_ifs with hik
    · subst hik
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun y _ => hnot _ hm y
    · exact hdeg2 _ (honly _ (by simp [hik]))
  -- write each degree as a sum of edge indicators
  have hin : ∀ i : Fin 5, i.val < 2 →
      (Finset.univ.filter (H.Adj (w, i))).card = a H (w, i) (w, 2) + a H (w, i) (w, 3) + a H (w, i) (w, 4) := by
    intro i hi
    rw [card_filter_eq_sum H (w, i) {(w, 2), (w, 3), (w, 4)}]
    · rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton, add_assoc]
    · intro y hy
      rcases adj_inner w i hi y hy with rfl | rfl | rfl <;> simp
  have hat : ∀ j : Fin 5, 2 ≤ j.val →
      (Finset.univ.filter (H.Adj (w, j))).card =
        a H (w, j) (w, 0) + a H (w, j) (w, 1) + a H (w, j) (partner (w, j)) := by
    intro j hj
    have hp1 : partner (w, j) ≠ (w, 0) := fun h => partner_block_ne w j hj (by rw [h])
    have hp2 : partner (w, j) ≠ (w, 1) := fun h => partner_block_ne w j hj (by rw [h])
    rw [card_filter_eq_sum H (w, j) {(w, 0), (w, 1), partner (w, j)}]
    · rw [Finset.sum_insert (by simp [hp1.symm]), Finset.sum_insert (by simp [hp2.symm]),
        Finset.sum_singleton, add_assoc]
    · intro y hy
      rcases adj_attach w j hj y hy with rfl | rfl | rfl <;> simp
  -- the counting argument
  have d0 := hdeg 0; have d1 := hdeg 1; have d2 := hdeg 2; have d3 := hdeg 3; have d4 := hdeg 4
  rw [hin 0 (by decide)] at d0
  rw [hin 1 (by decide)] at d1
  rw [hat 2 (by decide)] at d2
  rw [hat 3 (by decide)] at d3
  rw [hat 4 (by decide)] at d4
  rw [a_symm H (w, 2) (w, 0), a_symm H (w, 2) (w, 1)] at d2
  rw [a_symm H (w, 3) (w, 0), a_symm H (w, 3) (w, 1)] at d3
  rw [a_symm H (w, 4) (w, 0), a_symm H (w, 4) (w, 1)] at d4
  have b02 := a_le_one H (w, 0) (w, 2); have b03 := a_le_one H (w, 0) (w, 3)
  have b04 := a_le_one H (w, 0) (w, 4); have b12 := a_le_one H (w, 1) (w, 2)
  have b13 := a_le_one H (w, 1) (w, 3); have b14 := a_le_one H (w, 1) (w, 4)
  have f2 := a_le_one H (w, 2) (partner (w, 2)); have f3 := a_le_one H (w, 3) (partner (w, 3))
  have f4 := a_le_one H (w, 4) (partner (w, 4))
  -- an inner missing vertex is impossible; an attachment one leaves no edge out of the block
  have hout : a H (w, 2) (partner (w, 2)) = 0 ∧ a H (w, 3) (partner (w, 3)) = 0 ∧
      a H (w, 4) (partner (w, 4)) = 0 := by
    fin_cases k <;> simp at d0 d1 d2 d3 d4 <;> omega
  -- no edge of the cycle leaves block `w`
  have hclosed : ∀ x y : V, x.1 = w → H.Adj x y → y.1 = w := by
    rintro ⟨xw, i⟩ y hx hxy
    simp only at hx
    subst hx
    by_cases hi : i.val < 2
    · rcases adj_inner xw i hi y (H.adj_sub hxy) with rfl | rfl | rfl <;> rfl
    · have hj : 2 ≤ i.val := by omega
      rcases adj_attach xw i hj y (H.adj_sub hxy) with rfl | rfl | rfl
      · rfl
      · rfl
      · exfalso
        have : a H (xw, i) (partner (xw, i)) = 1 := by simp [a, hxy]
        fin_cases i <;> simp_all
  -- so the whole cycle lies in block `w`
  obtain ⟨j0, hj0, hj0le⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
    (honly (w, if k = 0 then 1 else 0) (by split_ifs with h <;> simp [Prod.ext_iff] <;> omega))
  have hfwd : ∀ s : ℕ, (p.getVert s).1 = w → ∀ t, s + t ≤ p.length → (p.getVert (s + t)).1 = w := by
    intro s hs t
    induction t with
    | zero => intro _; simpa using hs
    | succ t ih =>
      intro hst
      have h1 := ih (by omega)
      exact hclosed _ _ h1 (p.toSubgraph_adj_getVert (by omega))
  have hu : u.1 = w := by
    have := hfwd j0 (by rw [hj0]) (p.length - j0) (by omega)
    rwa [show j0 + (p.length - j0) = p.length by omega, p.getVert_length] at this
  have hall : ∀ x ∈ p.support, x.1 = w := by
    intro x hx
    obtain ⟨n, rfl, hn⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    have := hfwd 0 (by rw [p.getVert_zero]; exact hu) n (by omega)
    simpa using this
  have hsub : p.support.toFinset ⊆ Finset.univ.filter (fun x : V => x.1 = w) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hall x (List.mem_toFinset.mp hx)
  have h5 := block_card w
  have := Finset.card_le_card hsub
  omega

end CubicK23
