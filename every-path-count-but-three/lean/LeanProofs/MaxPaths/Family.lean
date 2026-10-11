import LeanProofs.MaxPaths.Paths

/-!
# The graphs `G_a` and the affine lemma

`G_a` is a base graph on `Fin h` (edge list `E`) plus `a` new vertices, each joined to `x` and `y`
only. **Affine lemma** (`affine`): for endpoints that are images of `s, t` in `G_b`, where every new
vertex of `G_b` is `s` or `t`, the number of paths in `G_a` is `N_b(s,t) + (a - b) T(s,t)`, where
`T(s,t)` counts the paths of `G_{b+1}` through its last new vertex (`N_succ`: `N_{b+1} = N_b + T`).
-/

namespace MaxPaths

-- `Fin h ⊕ Fin a` has a derived `BEq` with no `LawfulBEq`; use the one from `DecidableEq`.
attribute [local instance high] instBEqOfDecidableEq

variable (h : ℕ) (E : List (ℕ × ℕ)) (x y : ℕ)

/-- Adjacency of `G_a`. -/
def gadj (a : ℕ) : Fin h ⊕ Fin a → Fin h ⊕ Fin a → Bool
  | .inl i, .inl j => (i.val, j.val) ∈ E || (j.val, i.val) ∈ E
  | .inl i, .inr _ => i.val == x || i.val == y
  | .inr _, .inl j => j.val == x || j.val == y
  | .inr _, .inr _ => false

/-- The vertices of `G_a`, listed once each. -/
def verts (a : ℕ) : List (Fin h ⊕ Fin a) :=
  (List.finRange h).map .inl ++ (List.finRange a).map .inr

lemma mem_verts (a : ℕ) (w : Fin h ⊕ Fin a) : w ∈ verts h a := by
  cases w <;> simp [verts]

lemma nodup_verts (a : ℕ) : (verts h a).Nodup := by
  simp only [verts, List.nodup_append]
  refine ⟨(List.nodup_finRange h).map Sum.inl_injective,
    (List.nodup_finRange a).map Sum.inr_injective, ?_⟩
  simp

/-- Number of simple paths from `u` to `v` in `G_a`. -/
def N (a : ℕ) (u v : Fin h ⊕ Fin a) : ℕ := (paths (verts h a) (gadj h E x y a) u v).card

/-- The copy of `G_b` inside `G_a` given by `g : Fin b → Fin a`. -/
def emb {a b : ℕ} (g : Fin b → Fin a) : Fin h ⊕ Fin b → Fin h ⊕ Fin a := Sum.map id g

lemma emb_adj {a b : ℕ} (g : Fin b → Fin a) (s t : Fin h ⊕ Fin b) :
    gadj h E x y a (emb h g s) (emb h g t) = gadj h E x y b s t := by
  cases s <;> cases t <;> rfl

lemma emb_inj {a b : ℕ} {g : Fin b → Fin a} (hg : Function.Injective g) :
    Function.Injective (emb h g) :=
  Function.Injective.sumMap Function.injective_id hg

/-- `T(s,t)`: paths of `G_{b+1}` (endpoints copied by `castSucc`) through the last new vertex. -/
def T (b : ℕ) (s t : Fin h ⊕ Fin b) : ℕ :=
  ((paths (verts h (b + 1)) (gadj h E x y (b + 1)) (emb h Fin.castSucc s) (emb h Fin.castSucc t)).filter
    fun l : List (Fin h ⊕ Fin (b + 1)) => Sum.inr (Fin.last b) ∈ l).card

/-- A new vertex has neighbours `x` and `y` only. -/
lemma new_nbrs {a : ℕ} (hx : x < h) (hy : y < h) (k : Fin a) (w : Fin h ⊕ Fin a)
    (hw : gadj h E x y a w (.inr k) = true ∨ gadj h E x y a (.inr k) w = true) :
    w = .inl ⟨x, hx⟩ ∨ w = .inl ⟨y, hy⟩ := by
  rcases w with i | j
  · simp only [gadj, Bool.or_eq_true, beq_iff_eq, or_self] at hw
    rcases hw with h1 | h1
    · left; exact congrArg _ (Fin.ext h1)
    · right; exact congrArg _ (Fin.ext h1)
  · simp [gadj] at hw

variable {h E x y}

/-- **The affine lemma.** -/
theorem affine (hx : x < h) (hy : y < h) {a b : ℕ} (g : Fin b → Fin a) (hg : Function.Injective g)
    (s t : Fin h ⊕ Fin b) (hall : ∀ k : Fin b, Sum.inr k = s ∨ Sum.inr k = t) :
    N h E x y a (emb h g s) (emb h g t) = N h E x y b s t + (a - b) * T h E x y b s t := by
  set P := paths (verts h a) (gadj h E x y a) (emb h g s) (emb h g t) with hP
  set Z : Finset (Fin a) := Finset.univ.filter fun k => ∀ j, g j ≠ k with hZ
  have hZcard : Z.card = a - b := by
    have : Z = Finset.univ \ Finset.univ.image g := by
      ext k; simp [hZ]
    rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  -- a new vertex outside the copy is never an endpoint
  have hend : ∀ k ∈ Z, ∀ r : Fin h ⊕ Fin b, emb h g r ≠ Sum.inr k := by
    intro k hk r hr
    rcases r with i | j
    · simp [emb] at hr
    · simp only [emb, Sum.map_inr, Sum.inr.injEq] at hr
      exact (Finset.mem_filter.1 hk).2 j hr
  have huniq : ∀ l ∈ P, ∀ k ∈ Z, ∀ k' ∈ Z, (Sum.inr k : Fin h ⊕ Fin a) ∈ l → Sum.inr k' ∈ l → k = k' := by
    intro l hl k hk k' hk' m m'
    obtain ⟨hu, hv, hn, hc⟩ := (mem_paths _ _ (mem_verts h a)).1 hl
    have := at_most_one (gadj h E x y a) (.inl ⟨x, hx⟩) (.inl ⟨y, hy⟩) hn hc
      (new_nbrs h E x y hx hy k) (new_nbrs h E x y hx hy k') m m'
      (by rw [hv]; simpa using hend k hk t) (by rw [hu]; simpa using hend k hk s)
      (by rw [hv]; simpa using hend k' hk' t) (by rw [hu]; simpa using hend k' hk' s)
    exact Sum.inr_injective this
  rw [N]
  refine (card_decomp P Z (Sum.inr : Fin a → Fin h ⊕ Fin a) huniq).trans ?_
  congr 1
  · -- paths avoiding the other new vertices are the paths of `G_b`
    have := card_pullback (verts h a) (gadj h E x y a) (verts h b) (gadj h E x y b) (mem_verts h b)
      (mem_verts h a) (emb h g) (emb_inj h hg) (emb_adj h E x y g) (fun _ => True) s t
    simp only [Finset.filter_true, and_true] at this
    rw [N, this]
    apply congrArg Finset.card
    ext l
    simp only [Finset.mem_filter]
    refine and_congr_right fun hl => ?_
    constructor
    · intro hno w hw
      rcases w with i | k
      · exact List.mem_map.2 ⟨.inl i, mem_verts h b _, rfl⟩
      · by_cases hk : k ∈ Z
        · exact absurd hw (hno k hk)
        · simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hk
          obtain ⟨j, rfl⟩ := hk
          exact List.mem_map.2 ⟨.inr j, mem_verts h b _, rfl⟩
    · intro hall' k hk hm
      obtain ⟨r, -, hr⟩ := List.mem_map.1 (hall' _ hm)
      exact hend k hk r hr
  · -- each new vertex outside the copy contributes `T`
    rw [Finset.sum_const_nat (m := T h E x y b s t), hZcard]
    intro k hk
    have hkZ := (Finset.mem_filter.1 hk).2
    set g' : Fin (b + 1) → Fin a := Fin.lastCases k g with hg'
    have hg'inj : Function.Injective g' := by
      intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rfl
        | cast j => simp only [hg', Fin.lastCases_last, Fin.lastCases_castSucc] at hij
                    exact absurd hij.symm (hkZ j)
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp only [hg', Fin.lastCases_last, Fin.lastCases_castSucc] at hij
                  exact absurd hij (hkZ i)
        | cast j => simp only [hg', Fin.lastCases_castSucc] at hij
                    rw [hg hij]
    have hcomp : ∀ r, emb h g' (emb h Fin.castSucc r) = emb h g r := by
      intro r; cases r <;> simp [emb, hg', Fin.lastCases_castSucc]
    have hpb := card_pullback (verts h a) (gadj h E x y a) (verts h (b + 1)) (gadj h E x y (b + 1))
      (mem_verts h (b + 1)) (mem_verts h a) (emb h g') (emb_inj h hg'inj) (emb_adj h E x y g')
      (fun l => (Sum.inr k : Fin h ⊕ Fin a) ∈ l) (emb h Fin.castSucc s) (emb h Fin.castSucc t)
    rw [hcomp, hcomp] at hpb
    have hlast : emb h g' (Sum.inr (Fin.last b)) = Sum.inr k := by simp [emb, hg']
    rw [T]
    symm
    convert hpb using 1
    · apply congrArg Finset.card
      ext l'
      simp only [Finset.mem_filter]
      refine and_congr_right fun _ => ⟨fun hm => List.mem_map.2 ⟨_, hm, hlast⟩, fun hm => ?_⟩
      obtain ⟨r, hr, he⟩ := List.mem_map.1 hm
      rw [← hlast] at he
      rwa [← emb_inj h hg'inj he]
    · apply congrArg Finset.card
      ext l
      simp only [Finset.mem_filter]
      refine and_congr_right fun hl => ⟨fun hm => ⟨fun w hw => ?_, hm⟩, fun hm => hm.2⟩
      rcases w with i | k''
      · exact List.mem_map.2 ⟨.inl i, mem_verts h _ _, rfl⟩
      · by_cases hz : k'' ∈ Z
        · have := huniq l hl k hk k'' hz hm hw
          subst this
          exact List.mem_map.2 ⟨_, mem_verts h _ _, hlast⟩
        · simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hz
          obtain ⟨j, rfl⟩ := hz
          exact List.mem_map.2 ⟨.inr (Fin.castSucc j), mem_verts h _ _, by simp [emb, hg']⟩

theorem N_succ (hx : x < h) (hy : y < h) {b : ℕ} (s t : Fin h ⊕ Fin b)
    (hall : ∀ k : Fin b, Sum.inr k = s ∨ Sum.inr k = t) :
    N h E x y (b + 1) (emb h Fin.castSucc s) (emb h Fin.castSucc t)
      = N h E x y b s t + T h E x y b s t := by
  rw [affine hx hy Fin.castSucc (Fin.castSucc_injective b) s t hall]; simp

lemma N_eq_countFast (a : ℕ) (u v : Fin h ⊕ Fin a) :
    N h E x y a u v = countFast (verts h a) (gadj h E x y a) u v :=
  (countFast_eq _ _ (nodup_verts h a) u v).symm

end MaxPaths
