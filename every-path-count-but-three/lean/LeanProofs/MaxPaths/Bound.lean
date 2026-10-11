import LeanProofs.MaxPaths.Family

/-!
# From a finite check to a bound for every `a`

`okB` checks, for every pair `s ≠ t` of `G_b` (`b ≤ 2`) whose new vertices are all endpoints, that
the line `a ↦ N_b + (a - b) T` stays below `sl·a + r` (slope `T ≤ sl`, and the value at the first
`a` where the pair exists). `bound` turns that into `N_a(u,v) ≤ sl·a + r` for every pair of every
`G_a`, using the affine lemma: every pair of `G_a` is the image of such a pair.
-/

namespace MaxPaths

attribute [local instance high] instBEqOfDecidableEq

variable (h : ℕ) (E : List (ℕ × ℕ)) (x y : ℕ)

/-- every new vertex of `G_b` is `s` or `t` -/
def hallB (b : ℕ) (s t : Fin h ⊕ Fin b) : Bool :=
  (List.finRange b).all fun k => decide (Sum.inr k = s ∨ Sum.inr k = t)

/-- The finite check for one `b`. -/
def okAt (sl r b : ℕ) : Bool :=
  (verts h b).all fun s => (verts h b).all fun t =>
    decide (s = t) || !hallB h b s t ||
      (let n0 := countFast (verts h b) (gadj h E x y b) s t
       let n1 := countFast (verts h (b + 1)) (gadj h E x y (b + 1))
         (emb h Fin.castSucc s) (emb h Fin.castSucc t)
       decide (n1 - n0 ≤ sl ∧ n0 + (max b 1 - b) * (n1 - n0) ≤ sl * max b 1 + r))

lemma okAt_spec {sl r b : ℕ} (hok : okAt h E x y sl r b = true) (hx : x < h) (hy : y < h)
    (s t : Fin h ⊕ Fin b) (hst : s ≠ t) (hall : ∀ k : Fin b, Sum.inr k = s ∨ Sum.inr k = t) :
    T h E x y b s t ≤ sl ∧ N h E x y b s t + (max b 1 - b) * T h E x y b s t ≤ sl * max b 1 + r := by
  simp only [okAt, List.all_eq_true] at hok
  have := hok s (mem_verts h b s) t (mem_verts h b t)
  have hh : hallB h b s t = true := by
    simp only [hallB, List.all_eq_true, decide_eq_true_eq]; exact fun k _ => hall k
  simp only [hst, decide_false, hh, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
  have hsucc := N_succ hx hy s t hall (E := E)
  rw [N_eq_countFast, N_eq_countFast] at hsucc
  rw [N_eq_countFast]
  have hT : T h E x y b s t = countFast (verts h (b + 1)) (gadj h E x y (b + 1))
      (emb h Fin.castSucc s) (emb h Fin.castSucc t) - countFast (verts h b) (gadj h E x y b) s t := by
    omega
  rw [hT]; exact this

/-- Arithmetic: a line below `sl·a + r` at `a₀` with slope `≤ sl` stays below for `a ≥ a₀`. -/
lemma line_le {n T sl r a a₀ b : ℕ} (hb : b ≤ a₀) (ha : a₀ ≤ a) (hT : T ≤ sl)
    (h0 : n + (a₀ - b) * T ≤ sl * a₀ + r) : n + (a - b) * T ≤ sl * a + r := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ha
  have e : a₀ + d - b = (a₀ - b) + d := by omega
  rw [e, add_mul, mul_add]
  nlinarith [Nat.mul_le_mul_right d hT]

/-- **Every pair of every `G_a` (`a ≥ 1`) has at most `sl·a + r` paths**, given the finite checks. -/
theorem bound {sl r : ℕ} (hx : x < h) (hy : y < h) (h0 : okAt h E x y sl r 0 = true)
    (h1 : okAt h E x y sl r 1 = true) (h2 : okAt h E x y sl r 2 = true) {a : ℕ} (ha : 1 ≤ a)
    (u v : Fin h ⊕ Fin a) (huv : u ≠ v) : N h E x y a u v ≤ sl * a + r := by
  rcases u with i | k <;> rcases v with j | k'
  · -- both old: b = 0
    have hall : ∀ k : Fin 0, (Sum.inr k : Fin h ⊕ Fin 0) = Sum.inl i ∨ (Sum.inr k : Fin h ⊕ Fin 0) = Sum.inl j :=
      fun k => k.elim0
    have hne : (Sum.inl i : Fin h ⊕ Fin 0) ≠ Sum.inl j := by
      intro e; exact huv (by simpa using e)
    have := affine hx hy (E := E) (Fin.elim0 : Fin 0 → Fin a) (fun k => k.elim0) _ _ hall
    obtain ⟨hT, hv⟩ := okAt_spec h E x y h0 hx hy _ _ hne hall
    simp only [emb, Sum.map_inl, id] at this
    rw [this]
    exact line_le (a₀ := 1) (by norm_num) ha hT (by simpa using hv)
  · -- old, new: b = 1
    have hall : ∀ m : Fin 1, (Sum.inr m : Fin h ⊕ Fin 1) = Sum.inl i ∨ (Sum.inr m : Fin h ⊕ Fin 1) = Sum.inr 0 :=
      fun m => Or.inr (by rw [Subsingleton.elim m 0])
    have := affine hx hy (E := E) (fun _ : Fin 1 => k') (fun m m' _ => Subsingleton.elim m m') _ _ hall
    obtain ⟨hT, hv⟩ := okAt_spec h E x y h1 hx hy _ _ (by simp) hall
    simp only [emb, Sum.map_inl, Sum.map_inr, id] at this
    rw [this]
    exact line_le (a₀ := 1) (by norm_num) ha hT (by simpa using hv)
  · -- new, old: b = 1
    have hall : ∀ m : Fin 1, (Sum.inr m : Fin h ⊕ Fin 1) = Sum.inr 0 ∨ (Sum.inr m : Fin h ⊕ Fin 1) = Sum.inl j :=
      fun m => Or.inl (by rw [Subsingleton.elim m 0])
    have := affine hx hy (E := E) (fun _ : Fin 1 => k) (fun m m' _ => Subsingleton.elim m m') _ _ hall
    obtain ⟨hT, hv⟩ := okAt_spec h E x y h1 hx hy _ _ (by simp) hall
    simp only [emb, Sum.map_inl, Sum.map_inr, id] at this
    rw [this]
    exact line_le (a₀ := 1) (by norm_num) ha hT (by simpa using hv)
  · -- both new: b = 2 (then a ≥ 2)
    have hkk : k ≠ k' := fun e => huv (by rw [e])
    have ha2 : 2 ≤ a := by
      by_contra hc
      have : a = 1 := by omega
      subst this
      exact hkk (Subsingleton.elim _ _)
    have hall : ∀ m : Fin 2, (Sum.inr m : Fin h ⊕ Fin 2) = Sum.inr 0 ∨ (Sum.inr m : Fin h ⊕ Fin 2) = Sum.inr 1 := by
      intro m; fin_cases m <;> simp
    have hinj : Function.Injective (![k, k'] : Fin 2 → Fin a) := by
      intro m m' e
      fin_cases m <;> fin_cases m' <;>
        simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one] at e <;>
        first | rfl | exact absurd e hkk | exact absurd e.symm hkk
    have := affine hx hy (E := E) ![k, k'] hinj _ _ hall
    obtain ⟨hT, hv⟩ := okAt_spec h E x y h2 hx hy _ _ (by simp) hall
    simp only [emb, Sum.map_inr, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rw [this]
    exact line_le (a₀ := 2) (by norm_num) ha2 hT (by simpa using hv)

end MaxPaths
