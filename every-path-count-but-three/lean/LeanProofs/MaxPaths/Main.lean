import LeanProofs.MaxPaths.Bound

/-!
# Every `k ≠ 3` is the largest number of simple paths between two vertices (MO 371851)

`f(G)` is the maximum over pairs `u ≠ v` of the number of simple `u`–`v` paths. `every_k`: for every
`k ≥ 1`, `k ≠ 3`, some simple graph has `f(G) = k`. The graphs are `K₂`, `K₄`, the wheel `W₄`, one
6-vertex graph (for 11), and four families `G_a` with `f(G_a) = 2a, 6a + 1, 6a + 9, 6a + 11` for every
`a ≥ 1` (`bound` from the affine lemma and finite checks, plus an explicit pair attaining the bound).

That `k = 3` is impossible is classical (IOI 2020, "Connecting Supertrees") and is not formalised.
-/

namespace MaxPaths

attribute [local instance high] instBEqOfDecidableEq

/-- `G` is a simple graph: symmetric, loopless. -/
def IsSimple (h : ℕ) (E : List (ℕ × ℕ)) (x y a : ℕ) : Prop :=
  (∀ u v, gadj h E x y a u v = gadj h E x y a v u) ∧ ∀ u, gadj h E x y a u u = false

/-- `f(G_a) = k`. -/
def IsMax (h : ℕ) (E : List (ℕ × ℕ)) (x y a k : ℕ) : Prop :=
  (∃ u v : Fin h ⊕ Fin a, u ≠ v ∧ N h E x y a u v = k) ∧
    ∀ u v : Fin h ⊕ Fin a, u ≠ v → N h E x y a u v ≤ k

lemma isSimple {h : ℕ} {E : List (ℕ × ℕ)} {x y : ℕ} (hE : ∀ p ∈ E, p.1 ≠ p.2) (a : ℕ) :
    IsSimple h E x y a := by
  refine ⟨fun u v => ?_, fun u => ?_⟩
  · rcases u with i | i <;> rcases v with j | j <;> simp [gadj, Bool.or_comm]
  · rcases u with i | i
    · simp only [gadj, Bool.or_self, decide_eq_false_iff_not]
      exact fun hm => hE _ hm rfl
    · rfl

/-! ### Witnesses: one pair on the line `sl·a + r` -/

theorem witness1 {h : ℕ} {E : List (ℕ × ℕ)} {x y sl r : ℕ} (hx : x < h) (hy : y < h) (i : Fin h)
    (h1 : countFast (verts h 1) (gadj h E x y 1) (.inl i) (.inr 0) = sl + r)
    (h2 : countFast (verts h 2) (gadj h E x y 2) (.inl i) (.inr 0) = sl + r + sl)
    {a : ℕ} (ha : 1 ≤ a) : N h E x y a (.inl i) (.inr ⟨0, ha⟩) = sl * a + r := by
  have hall : ∀ m : Fin 1, (Sum.inr m : Fin h ⊕ Fin 1) = Sum.inl i ∨ (Sum.inr m : Fin h ⊕ Fin 1) = Sum.inr 0 :=
    fun m => Or.inr (by rw [Subsingleton.elim m 0])
  have hA := affine hx hy (E := E) (fun _ : Fin 1 => (⟨0, ha⟩ : Fin a))
    (fun m m' _ => Subsingleton.elim m m') _ _ hall
  have hS := N_succ hx hy (E := E) _ _ hall
  simp only [emb, Sum.map_inl, Sum.map_inr, id] at hA hS
  rw [N_eq_countFast, N_eq_countFast] at hS
  rw [N_eq_countFast] at hA ⊢
  rw [N_eq_countFast] at hA
  have : Fin.castSucc (0 : Fin 1) = (0 : Fin 2) := rfl
  rw [this, h1, h2] at hS
  rw [hA, h1]
  have hT : T h E x y 1 (Sum.inl i) (Sum.inr 0) = sl := by omega
  rw [hT]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
  simp; ring

theorem witness0 {h : ℕ} {E : List (ℕ × ℕ)} {x y sl r : ℕ} (hx : x < h) (hy : y < h) (i j : Fin h)
    (h0 : countFast (verts h 0) (gadj h E x y 0) (.inl i) (.inl j) = r)
    (h1 : countFast (verts h 1) (gadj h E x y 1) (.inl i) (.inl j) = r + sl)
    (a : ℕ) : N h E x y a (.inl i) (.inl j) = sl * a + r := by
  have hall : ∀ k : Fin 0, (Sum.inr k : Fin h ⊕ Fin 0) = Sum.inl i ∨ (Sum.inr k : Fin h ⊕ Fin 0) = Sum.inl j :=
    fun k => k.elim0
  have hA := affine hx hy (E := E) (Fin.elim0 : Fin 0 → Fin a) (fun k => k.elim0) _ _ hall
  have hS := N_succ hx hy (E := E) _ _ hall
  simp only [emb, Sum.map_inl, id] at hA hS
  rw [N_eq_countFast, N_eq_countFast] at hS
  rw [N_eq_countFast, N_eq_countFast] at hA
  rw [N_eq_countFast, hA, h0]
  rw [h0, h1] at hS
  have hT : T h E x y 0 (Sum.inl i) (Sum.inl j) = sl := by omega
  rw [hT]; simp; ring

/-! ### The four families -/

def E2 : List (ℕ × ℕ) := [(0, 1), (1, 2)]
def E61 : List (ℕ × ℕ) := [(0, 1), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4)]
def E69 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (2, 3), (2, 5), (3, 4)]
def E611 : List (ℕ × ℕ) := [(0, 1), (0, 3), (0, 4), (0, 5), (1, 2), (1, 5), (2, 3), (2, 5), (3, 4)]

/-- `G_a = K_{2,a+1}`: `f = 2a`. -/
theorem fam2 {a : ℕ} (ha : 1 ≤ a) : IsMax 3 E2 0 2 a (2 * a + 0) :=
  ⟨⟨.inl 1, .inr ⟨0, ha⟩, by simp, witness1 (by norm_num) (by norm_num) 1 (by decide) (by decide) ha⟩,
    bound 3 E2 0 2 (by norm_num) (by norm_num) (by decide) (by decide) (by decide) ha⟩

/-- `f = 6a + 1`. -/
theorem fam61 {a : ℕ} (ha : 1 ≤ a) : IsMax 5 E61 0 3 a (6 * a + 1) :=
  ⟨⟨.inl 4, .inr ⟨0, ha⟩, by simp, witness1 (by norm_num) (by norm_num) 4 (by decide) (by decide) ha⟩,
    bound 5 E61 0 3 (by norm_num) (by norm_num) (by decide) (by decide) (by decide) ha⟩

/-- `f = 6a + 9`. -/
theorem fam69 {a : ℕ} (ha : 1 ≤ a) : IsMax 6 E69 2 4 a (6 * a + 9) :=
  ⟨⟨.inl 1, .inr ⟨0, ha⟩, by simp, witness1 (by norm_num) (by norm_num) 1 (by decide) (by decide) ha⟩,
    bound 6 E69 2 4 (by norm_num) (by norm_num) (by decide) (by decide) (by decide) ha⟩

/-- `f = 6a + 11`. -/
theorem fam611 {a : ℕ} (ha : 1 ≤ a) : IsMax 6 E611 0 2 a (6 * a + 11) :=
  ⟨⟨.inl 1, .inl 4, by simp, witness0 (by norm_num) (by norm_num) 1 4 (by decide) (by decide) a⟩,
    bound 6 E611 0 2 (by norm_num) (by norm_num) (by decide) (by decide) (by decide) ha⟩

/-! ### Small graphs (no new vertices) -/

/-- `f(G) = k` for a fixed graph, from a finite check over all pairs. -/
theorem small {h : ℕ} {E : List (ℕ × ℕ)} {k : ℕ}
    (hc : (verts h 0).all (fun u => (verts h 0).all fun v =>
      decide (u = v) || decide (countFast (verts h 0) (gadj h E 0 0 0) u v ≤ k)) = true)
    (u₀ v₀ : Fin h) (hne : u₀ ≠ v₀) (hw : countFast (verts h 0) (gadj h E 0 0 0) (.inl u₀) (.inl v₀) = k) :
    IsMax h E 0 0 0 k := by
  refine ⟨⟨.inl u₀, .inl v₀, by simpa using hne, by rw [N_eq_countFast, hw]⟩, fun u v huv => ?_⟩
  simp only [List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hc
  rw [N_eq_countFast]
  rcases hc u (mem_verts h 0 u) v (mem_verts h 0 v) with e | e
  · exact absurd e huv
  · exact e

def EK2 : List (ℕ × ℕ) := [(0, 1)]
def EK4 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
def EW4 : List (ℕ × ℕ) := [(0, 1), (1, 2), (2, 3), (3, 0), (4, 0), (4, 1), (4, 2), (4, 3)]
def E11 : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (3, 4), (4, 5)]

theorem K2_max : IsMax 2 EK2 0 0 0 1 := small (by decide) 0 1 (by decide) (by decide)
theorem K4_max : IsMax 4 EK4 0 0 0 5 := small (by decide) 0 1 (by decide) (by decide)
theorem W4_max : IsMax 5 EW4 0 0 0 9 := small (by decide) 0 2 (by decide) (by decide)
theorem G11_max : IsMax 6 E11 0 0 0 11 := small (by decide) 2 3 (by decide) (by decide)

/-! ### Every `k ≠ 3` -/

/-- **Answer to MO 371851.** For every `k ≥ 1` with `k ≠ 3` there is a simple graph whose largest
number of simple paths between two distinct vertices is exactly `k`. -/
theorem every_k (k : ℕ) (hk : 1 ≤ k) (h3 : k ≠ 3) :
    ∃ (h : ℕ) (E : List (ℕ × ℕ)) (x y a : ℕ), IsSimple h E x y a ∧ IsMax h E x y a k := by
  by_cases he : k % 2 = 0
  · have e : 2 * (k / 2) + 0 = k := by omega
    have hm := fam2 (a := k / 2) (by omega); rw [e] at hm
    exact ⟨3, E2, 0, 2, k / 2, isSimple (by decide) _, hm⟩
  have h6 : k % 6 = 1 ∨ k % 6 = 3 ∨ k % 6 = 5 := by omega
  rcases h6 with h6 | h6 | h6
  · by_cases k1 : k = 1
    · subst k1; exact ⟨2, EK2, 0, 0, 0, isSimple (by decide) _, K2_max⟩
    · have e : 6 * ((k - 1) / 6) + 1 = k := by omega
      have hm := fam61 (a := (k - 1) / 6) (by omega); rw [e] at hm
      exact ⟨5, E61, 0, 3, (k - 1) / 6, isSimple (by decide) _, hm⟩
  · by_cases k9 : k = 9
    · subst k9; exact ⟨5, EW4, 0, 0, 0, isSimple (by decide) _, W4_max⟩
    · have e : 6 * ((k - 9) / 6) + 9 = k := by omega
      have hm := fam69 (a := (k - 9) / 6) (by omega); rw [e] at hm
      exact ⟨6, E69, 2, 4, (k - 9) / 6, isSimple (by decide) _, hm⟩
  · by_cases k5 : k = 5
    · subst k5; exact ⟨4, EK4, 0, 0, 0, isSimple (by decide) _, K4_max⟩
    by_cases k11 : k = 11
    · subst k11; exact ⟨6, E11, 0, 0, 0, isSimple (by decide) _, G11_max⟩
    · have e : 6 * ((k - 11) / 6) + 11 = k := by omega
      have hm := fam611 (a := (k - 11) / 6) (by omega); rw [e] at hm
      exact ⟨6, E611, 0, 2, (k - 11) / 6, isSimple (by decide) _, hm⟩

end MaxPaths
