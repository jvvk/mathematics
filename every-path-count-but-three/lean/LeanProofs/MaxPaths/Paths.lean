import Mathlib

/-!
# Simple paths as lists, and an exhaustive generator

A simple path from `u` to `v` is a list of distinct vertices, consecutive ones adjacent, whose last
entry is `u` and first entry is `v` (lists are built backwards from `u`). `ext` extends a reversed
path in every possible way; `mem_paths` shows it lists exactly the simple paths and `nodup_ext`
that it lists each once, so `countFast` (used by `decide`) is the number of simple paths.
-/

namespace MaxPaths

variable {V : Type} [DecidableEq V] (vs : List V) (adj : V → V → Bool)

/-- Adjacency as a relation. -/
def R : V → V → Prop := fun a b => adj a b = true

/-- All extensions of the reversed path `p` (head = current end), using fuel `n`. -/
def ext : ℕ → List V → List (List V)
  | 0, p => [p]
  | _ + 1, [] => [[]]
  | n + 1, c :: p => (c :: p) :: (vs.filter fun w => adj w c && !(c :: p).contains w).flatMap
      fun w => ext n (w :: c :: p)

lemma ext_suffix : ∀ (n : ℕ) (p l : List V), l ∈ ext vs adj n p → ∃ q, l = q ++ p
  | 0, p, l, h => ⟨[], by simpa [ext] using h⟩
  | _ + 1, [], l, h => ⟨l, by simp⟩
  | n + 1, c :: p, l, h => by
    simp only [ext, List.mem_cons, List.mem_flatMap, List.mem_filter] at h
    rcases h with rfl | ⟨w, _, hl⟩
    · exact ⟨[], rfl⟩
    · obtain ⟨q, rfl⟩ := ext_suffix n _ _ hl
      exact ⟨q ++ [w], by simp⟩

/-- **The generator lists exactly the simple extensions.** -/
theorem mem_ext (hvs : ∀ w, w ∈ vs) : ∀ (n : ℕ) (p : List V), p ≠ [] → p.Nodup →
    p.IsChain (R adj) → ∀ l, l ∈ ext vs adj n p ↔
      ∃ q, l = q ++ p ∧ q.length ≤ n ∧ l.Nodup ∧ l.IsChain (R adj)
  | 0, p, _, hn, hc, l => by
    simp only [ext, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨[], rfl, le_rfl, hn, hc⟩
    · rintro ⟨q, rfl, hq, -⟩; simp [List.length_eq_zero_iff.mp (Nat.le_zero.mp hq)]
  | _ + 1, [], hp, _, _, _ => absurd rfl hp
  | n + 1, c :: p, _, hn, hc, l => by
    simp only [ext, List.mem_cons, List.mem_flatMap, List.mem_filter, Bool.and_eq_true,
      Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
    constructor
    · rintro (rfl | ⟨w, ⟨-, hwc, hw⟩, hl⟩)
      · exact ⟨[], rfl, Nat.zero_le _, hn, hc⟩
      · have hn' : (w :: c :: p).Nodup := List.nodup_cons.2 ⟨by simpa using hw, hn⟩
        have hc' : (w :: c :: p).IsChain (R adj) := List.isChain_cons_cons.2 ⟨hwc, hc⟩
        obtain ⟨q, rfl, hq, hln, hlc⟩ := (mem_ext hvs n _ (by simp) hn' hc' l).1 hl
        exact ⟨q ++ [w], by simp, by simp; omega, by simpa using hln, by simpa using hlc⟩
    · rintro ⟨q, rfl, hq, hln, hlc⟩
      rcases List.eq_nil_or_concat q with rfl | ⟨q', w, rfl⟩
      · left; rfl
      · right
        simp only [List.concat_eq_append] at hq hln hlc ⊢
        have e : q' ++ [w] ++ c :: p = q' ++ (w :: c :: p) := by simp
        rw [e] at hln hlc ⊢
        have hwcp := (List.nodup_append.1 hln).2.1
        have hwc : R adj w c := (List.isChain_cons_cons.1 hlc.right_of_append).1
        refine ⟨w, ⟨hvs w, hwc, by simpa using (List.nodup_cons.1 hwcp).1⟩, ?_⟩
        have hc' : (w :: c :: p).IsChain (R adj) := List.isChain_cons_cons.2 ⟨hwc, hc⟩
        exact (mem_ext hvs n _ (by simp) hwcp hc' _).2 ⟨q', rfl, by simp at hq; omega, hln, hlc⟩

/-- **Each extension is listed once.** -/
theorem nodup_ext (hvn : vs.Nodup) : ∀ (n : ℕ) (p : List V), (ext vs adj n p).Nodup
  | 0, p => by simp [ext]
  | _ + 1, [] => by simp [ext]
  | n + 1, c :: p => by
    simp only [ext]
    refine List.nodup_cons.2 ⟨?_, ?_⟩
    · simp only [List.mem_flatMap, not_exists, not_and]
      intro w _ h
      obtain ⟨q, hq⟩ := ext_suffix vs adj n _ _ h
      have := congrArg List.length hq
      simp at this; omega
    · refine List.nodup_flatMap.2 ⟨fun w _ => nodup_ext hvn n _, ?_⟩
      refine List.Nodup.pairwise_of_forall_ne (List.Nodup.filter _ ?_) ?_
      · exact hvn
      · intro w₁ _ w₂ _ hne l h₁ h₂
        obtain ⟨q₁, rfl⟩ := ext_suffix vs adj n _ _ h₁
        obtain ⟨q₂, hq⟩ := ext_suffix vs adj n _ _ h₂
        have hlen : q₁.length = q₂.length := by
          have := congrArg List.length hq; simp at this; omega
        have := (List.append_inj hq hlen).2
        simp only [List.cons.injEq] at this
        exact hne this.1

/-- A simple path from `u` to `v`, stored backwards: last entry `u`, first entry `v`. -/
def IsPathL (u v : V) (l : List V) : Prop :=
  l.getLast? = some u ∧ l.head? = some v ∧ l.Nodup ∧ l.IsChain (R adj)

/-- The finite set of simple paths from `u` to `v`. -/
def paths (u v : V) : Finset (List V) :=
  ((ext vs adj vs.length [u]).filter fun l => decide (l.head? = some v)).toFinset

/-- The number of simple paths, computed by the generator (used by `decide`). -/
def countFast (u v : V) : ℕ :=
  ((ext vs adj vs.length [u]).filter fun l => decide (l.head? = some v)).length

omit [DecidableEq V] in
lemma getLast?_eq_some_iff' {l : List V} {u : V} : l.getLast? = some u ↔ ∃ q, l = q ++ [u] := by
  rcases List.eq_nil_or_concat l with rfl | ⟨q, w, rfl⟩
  · simp
  · simp only [List.concat_eq_append, List.getLast?_append, List.getLast?_singleton,
      Option.some_or, Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨q, rfl⟩
    · rintro ⟨q', h⟩; exact (List.append_inj' h rfl).2 |> List.singleton_inj.1

theorem mem_paths (hvs : ∀ w, w ∈ vs) {u v : V} {l : List V} :
    l ∈ paths vs adj u v ↔ IsPathL adj u v l := by
  simp only [paths, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  rw [mem_ext vs adj hvs _ [u] (by simp) (by simp) (by simp)]
  constructor
  · rintro ⟨⟨q, rfl, -, hn, hc⟩, hv⟩
    exact ⟨by simp, hv, hn, hc⟩
  · rintro ⟨hu, hv, hn, hc⟩
    obtain ⟨q, rfl⟩ := getLast?_eq_some_iff'.1 hu
    refine ⟨⟨q, rfl, ?_, hn, hc⟩, hv⟩
    have := hn.length_le_of_subset (l₂ := vs) (fun w _ => hvs w)
    simp at this; omega

theorem countFast_eq (hvn : vs.Nodup) (u v : V) : countFast vs adj u v = (paths vs adj u v).card := by
  rw [paths, List.toFinset_card_of_nodup ((nodup_ext vs adj hvn _ _).filter _), countFast]

/-! ### Pulling paths back along an adjacency-preserving injection -/

omit [DecidableEq V] in
lemma exists_map_eq {W : Type} (E : W → V) (ws : List W) :
    ∀ l : List V, (∀ x ∈ l, x ∈ ws.map E) → ∃ l' : List W, l'.map E = l
  | [], _ => ⟨[], rfl⟩
  | x :: l, h => by
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 (h x (by simp))
    obtain ⟨l', hl'⟩ := exists_map_eq E ws l fun z hz => h z (by simp [hz])
    exact ⟨y :: l', by simp [hl']⟩

/-- **Pullback.** If `E` is injective and preserves and reflects adjacency, the paths of the small
graph correspond to the paths of the big graph that stay inside the image of `E`. -/
theorem card_pullback {W : Type} [DecidableEq W] (ws : List W) (adjW : W → W → Bool)
    (hws : ∀ w, w ∈ ws) (hvs : ∀ w, w ∈ vs) (E : W → V)
    (hE : Function.Injective E) (hadj : ∀ s t, adj (E s) (E t) = adjW s t)
    (P : List V → Prop) [DecidablePred P] (s t : W) :
    ((paths ws adjW s t).filter fun l => P (l.map E)).card
      = ((paths vs adj (E s) (E t)).filter fun l => (∀ x ∈ l, x ∈ ws.map E) ∧ P l).card := by
  refine Finset.card_bij (fun l _ => l.map E) ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_filter, mem_paths ws adjW hws, mem_paths vs adj hvs] at hl ⊢
    obtain ⟨⟨hu, hv, hn, hc⟩, hP⟩ := hl
    refine ⟨⟨by simp [List.getLast?_map, hu], by simp [List.head?_map, hv], hn.map hE, ?_⟩, ?_, hP⟩
    · exact List.isChain_map_of_isChain E (fun a b h => by simp only [R] at h ⊢; rw [hadj]; exact h) hc
    · intro x hx
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      exact List.mem_map_of_mem (hws y)
  · intro l₁ _ l₂ _ h
    exact (List.map_injective_iff.2 hE) h
  · intro l hl
    simp only [Finset.mem_filter, mem_paths ws adjW hws, mem_paths vs adj hvs] at hl ⊢
    obtain ⟨⟨hu, hv, hn, hc⟩, hin, hP⟩ := hl
    obtain ⟨l', rfl⟩ := exists_map_eq E ws l hin
    refine ⟨l', ⟨⟨?_, ?_, List.Nodup.of_map E hn, ?_⟩, hP⟩, rfl⟩
    · rw [List.getLast?_map, Option.map_eq_some_iff] at hu
      obtain ⟨a, ha, he⟩ := hu; rw [ha, hE he]
    · rw [List.head?_map, Option.map_eq_some_iff] at hv
      obtain ⟨a, ha, he⟩ := hv; rw [ha, hE he]
    · exact List.isChain_of_isChain_map E (fun a b h => by simp only [R] at h ⊢; rw [← hadj]; exact h) hc

/-! ### A vertex whose only neighbours are `X` and `Y` -/

omit [DecidableEq V] in
/-- An interior vertex `n` whose neighbours all lie in `{X, Y}` sits between `X` and `Y`. -/
lemma interior (X Y : V) {l : List V} (hn : l.Nodup) (hc : l.IsChain (R adj)) {n : V}
    (hnb : ∀ w, (adj w n = true ∨ adj n w = true) → w = X ∨ w = Y) (m : n ∈ l)
    (e : l.head? ≠ some n) (e' : l.getLast? ≠ some n) :
    ∃ k, ∃ hk : k + 2 < l.length, l[k + 1] = n ∧
      ((l[k] = X ∧ l[k + 2] = Y) ∨ (l[k] = Y ∧ l[k + 2] = X)) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem m
  rcases i with _ | k
  · exact absurd (by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hi]) e
  have hk : k + 2 < l.length := by
    by_contra hcon
    apply e'
    rw [List.getLast?_eq_getElem?, show l.length - 1 = k + 1 by omega, List.getElem?_eq_getElem]
  refine ⟨k, hk, rfl, ?_⟩
  have c1 := List.isChain_iff_getElem.1 hc k (by omega)
  have c2 := List.isChain_iff_getElem.1 hc (k + 1) hk
  have a1 := hnb _ (Or.inl c1)
  have a2 := hnb _ (Or.inr c2)
  have hne : l[k] ≠ l[k + 2] := fun h => by
    have := (hn.getElem_inj_iff).1 h; omega
  rcases a1 with a1 | a1 <;> rcases a2 with a2 | a2
  · exact absurd (a1.trans a2.symm) hne
  · exact Or.inl ⟨a1, a2⟩
  · exact Or.inr ⟨a1, a2⟩
  · exact absurd (a1.trans a2.symm) hne

omit [DecidableEq V] in
/-- **At most one interior new vertex.** Two interior vertices whose neighbours lie in `{X, Y}`
coincide. -/
theorem at_most_one (X Y : V) {l : List V} (hn : l.Nodup) (hc : l.IsChain (R adj)) {n₁ n₂ : V}
    (hnb₁ : ∀ w, (adj w n₁ = true ∨ adj n₁ w = true) → w = X ∨ w = Y)
    (hnb₂ : ∀ w, (adj w n₂ = true ∨ adj n₂ w = true) → w = X ∨ w = Y)
    (m₁ : n₁ ∈ l) (m₂ : n₂ ∈ l) (e₁ : l.head? ≠ some n₁) (e₁' : l.getLast? ≠ some n₁)
    (e₂ : l.head? ≠ some n₂) (e₂' : l.getLast? ≠ some n₂) : n₁ = n₂ := by
  obtain ⟨k₁, hk₁, r₁, p₁⟩ := interior adj X Y hn hc hnb₁ m₁ e₁ e₁'
  obtain ⟨k₂, hk₂, r₂, p₂⟩ := interior adj X Y hn hc hnb₂ m₂ e₂ e₂'
  have inj : ∀ {i j : ℕ} (hi : i < l.length) (hj : j < l.length), l[i] = l[j] → i = j :=
    fun _ _ h => (hn.getElem_inj_iff).1 h
  have : k₁ = k₂ := by
    rcases p₁ with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases p₂ with ⟨c, d⟩ | ⟨c, d⟩
    · exact inj _ _ (a.trans c.symm)
    · have := inj _ _ (a.trans d.symm); have := inj _ _ (b.trans c.symm); omega
    · have := inj _ _ (a.trans d.symm); have := inj _ _ (b.trans c.symm); omega
    · exact inj _ _ (a.trans c.symm)
  subst this
  rw [← r₁, ← r₂]

/-- **Decomposition.** If no path contains two of the vertices `f k`, `k ∈ Z`, the paths split into
those avoiding all of them and, for each `k`, those through `f k`. -/
theorem card_decomp {ι : Type} [DecidableEq ι] (P : Finset (List V)) (Z : Finset ι) (f : ι → V)
    (huniq : ∀ l ∈ P, ∀ k ∈ Z, ∀ k' ∈ Z, f k ∈ l → f k' ∈ l → k = k') :
    P.card = (P.filter fun l => ∀ k ∈ Z, f k ∉ l).card + ∑ k ∈ Z, (P.filter fun l => f k ∈ l).card := by
  rw [← Finset.card_biUnion]
  · rw [← Finset.card_filter_add_card_filter_not (fun l => ∃ k ∈ Z, f k ∈ l), add_comm]
    congr 2
    · ext l; simp
    · ext l; simp only [Finset.mem_filter, Finset.mem_biUnion]; tauto
  · intro k hk k' hk' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_filter]
    intro l hl h1 h2
    exact hne (huniq l hl k hk k' hk' h1 h2)

end MaxPaths
