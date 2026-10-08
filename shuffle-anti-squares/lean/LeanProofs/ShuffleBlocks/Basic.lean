import LeanProofs.ShuffleW

/-!
  Words given by runs of letters, for the blow-up theorem (`V K λ μ`).

  A word is `rw [(c₀, n₀), (c₁, n₁), …] = c₀^n₀ c₁^n₁ ⋯`. A shuffle of two words into `rw l` gives each
  copy a share of every run (`Split`), and two run words spelling the same word have equal
  "zeros before the t-th one" functions (`zb`), which yields one linear fact for every pair of
  overlapping blocks of ones (`pair_fact`). Rotations of a run word cut one run in two (`rot_cons`).
-/

namespace Blocks

/-- The word `c₀^n₀ c₁^n₁ ⋯`. -/
def rw : List (Bool × Nat) → List Bool
  | [] => []
  | (c, n) :: l => List.replicate n c ++ rw l

/-- Ones in the first `i` runs. -/
def onesB : List (Bool × Nat) → Nat → Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | (c, n) :: l, i + 1 => (if c then n else 0) + onesB l i

/-- Zeros in the first `i` runs. -/
def zerosB : List (Bool × Nat) → Nat → Nat
  | _, 0 => 0
  | [], _ + 1 => 0
  | (c, n) :: l, i + 1 => (if c then 0 else n) + zerosB l i

/-- `Split l la lb`: run `i` of `l` has length `aᵢ + bᵢ`, with `aᵢ` in `la` and `bᵢ` in `lb`. -/
inductive Split : List (Bool × Nat) → List (Bool × Nat) → List (Bool × Nat) → Prop
  | nil : Split [] [] []
  | cons {c : Bool} {n a b : Nat} {l la lb : List (Bool × Nat)} :
      a + b = n → Split l la lb → Split ((c, n) :: l) ((c, a) :: la) ((c, b) :: lb)

theorem shuffle_append {u v : List Bool} : ∀ {x y : List Bool}, Shuffle u v (x ++ y) →
    ∃ u₁ u₂ v₁ v₂, u = u₁ ++ u₂ ∧ v = v₁ ++ v₂ ∧ Shuffle u₁ v₁ x ∧ Shuffle u₂ v₂ y
  | [], _, h => ⟨[], u, [], v, rfl, rfl, .nil, h⟩
  | _ :: _, _, h => by
    cases h with
    | left h' =>
      obtain ⟨u₁, u₂, v₁, v₂, rfl, rfl, h₁, h₂⟩ := shuffle_append h'
      exact ⟨_ :: u₁, u₂, v₁, v₂, rfl, rfl, .left h₁, h₂⟩
    | right h' =>
      obtain ⟨u₁, u₂, v₁, v₂, rfl, rfl, h₁, h₂⟩ := shuffle_append h'
      exact ⟨u₁, u₂, _ :: v₁, v₂, rfl, rfl, .right h₁, h₂⟩

theorem shuffle_replicate {c : Bool} : ∀ {n : Nat} {u v : List Bool},
    Shuffle u v (List.replicate n c) →
    ∃ a b, a + b = n ∧ u = List.replicate a c ∧ v = List.replicate b c
  | 0, _, _, h => by cases h; exact ⟨0, 0, rfl, rfl, rfl⟩
  | n + 1, _, _, h => by
    rw [List.replicate_succ] at h
    cases h with
    | left h' =>
      obtain ⟨a, b, hab, rfl, rfl⟩ := shuffle_replicate h'
      exact ⟨a + 1, b, by omega, rfl, rfl⟩
    | right h' =>
      obtain ⟨a, b, hab, rfl, rfl⟩ := shuffle_replicate h'
      exact ⟨a, b + 1, by omega, rfl, rfl⟩

/-- A shuffle into a run word gives each copy a share of every run. -/
theorem shuffle_split : ∀ {l : List (Bool × Nat)} {u v : List Bool}, Shuffle u v (rw l) →
    ∃ la lb, Split l la lb ∧ u = rw la ∧ v = rw lb
  | [], _, _, h => by cases h; exact ⟨[], [], .nil, rfl, rfl⟩
  | (c, n) :: l, _, _, h => by
    obtain ⟨u₁, u₂, v₁, v₂, rfl, rfl, h₁, h₂⟩ := shuffle_append h
    obtain ⟨a, b, hab, rfl, rfl⟩ := shuffle_replicate h₁
    obtain ⟨la, lb, hs, rfl, rfl⟩ := shuffle_split h₂
    exact ⟨(c, a) :: la, (c, b) :: lb, .cons hab hs, rfl, rfl⟩

theorem split_cons_inv {c : Bool} {n : Nat} {l la lb : List (Bool × Nat)}
    (h : Split ((c, n) :: l) la lb) :
    ∃ a b la' lb', la = (c, a) :: la' ∧ lb = (c, b) :: lb' ∧ a + b = n ∧ Split l la' lb' := by
  cases h with
  | cons hab hs => exact ⟨_, _, _, _, rfl, rfl, hab, hs⟩

theorem split_nil_inv {la lb : List (Bool × Nat)} (h : Split [] la lb) : la = [] ∧ lb = [] := by
  cases h; exact ⟨rfl, rfl⟩

/-! ### Zeros before the t-th one -/

/-- Number of zeros before the one with index `t` (counting from 0). -/
def zb : List Bool → Nat → Nat
  | [], _ => 0
  | false :: w, t => zb w t + 1
  | true :: _, 0 => 0
  | true :: w, t + 1 => zb w t

theorem zb_rep_false (n t : Nat) (w : List Bool) :
    zb (List.replicate n false ++ w) t = n + zb w t := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, List.cons_append, zb, ih]; omega

theorem zb_rep_true_lt : ∀ (n t : Nat) (w : List Bool), t < n →
    zb (List.replicate n true ++ w) t = 0
  | n + 1, 0, _, _ => by simp [List.replicate_succ, zb]
  | n + 1, t + 1, w, h => by
    simp only [List.replicate_succ, List.cons_append, zb]
    exact zb_rep_true_lt n t w (by omega)

theorem zb_rep_true_ge : ∀ (n t : Nat) (w : List Bool), n ≤ t →
    zb (List.replicate n true ++ w) t = zb w (t - n)
  | 0, t, _, _ => by simp
  | n + 1, t + 1, w, h => by
    simp only [List.replicate_succ, List.cons_append, zb]
    rw [zb_rep_true_ge n t w (by omega)]
    congr 1
    omega

/-- Inside the `i`-th run, a block of `p` ones, the function `zb` equals the zeros before that run. -/
theorem zb_rw : ∀ (la : List (Bool × Nat)) (i t p : Nat), la[i]? = some (true, p) →
    onesB la i ≤ t → t < onesB la i + p → zb (rw la) t = zerosB la i
  | [], _, _, _, h, _, _ => by simp at h
  | (c, n) :: l, 0, t, p, h, _, h₂ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [onesB, zerosB] at h₂ ⊢
    exact zb_rep_true_lt _ _ _ (by omega)
  | (c, n) :: l, i + 1, t, p, h, h₁, h₂ => by
    simp only [List.getElem?_cons_succ] at h
    cases c with
    | false =>
      simp only [onesB, zerosB, rw, Bool.false_eq_true, ite_false] at h₁ h₂ ⊢
      rw [zb_rep_false, zb_rw l i t p h (by omega) (by omega)]
    | true =>
      simp only [onesB, zerosB, rw, ite_true] at h₁ h₂ ⊢
      rw [zb_rep_true_ge _ _ _ (by omega), zb_rw l i (t - n) p h (by omega) (by omega)]
      omega

/-- Two run words spelling the same word: overlapping blocks of ones have equal zeros before them. -/
theorem pair_fact {la lb : List (Bool × Nat)} (E : rw la = rw lb) {i j p q : Nat}
    (hi : la[i]? = some (true, p)) (hj : lb[j]? = some (true, q)) :
    0 < p → 0 < q → onesB la i < onesB lb j + q → onesB lb j < onesB la i + p →
      zerosB la i = zerosB lb j := by
  intro hp hq h₁ h₂
  obtain ⟨t, ht₁, ht₂, ht⟩ : ∃ t, onesB la i ≤ t ∧ onesB lb j ≤ t ∧
      (t = onesB la i ∨ t = onesB lb j) :=
    ⟨max (onesB la i) (onesB lb j), le_max_left _ _, le_max_right _ _, max_choice _ _⟩
  have ea := zb_rw la i t p hi ht₁ (by omega)
  have eb := zb_rw lb j t q hj ht₂ (by omega)
  rw [← ea, ← eb, E]

theorem count_rw (b : Bool) : ∀ l : List (Bool × Nat),
    (rw l).count b = (l.map (fun r => if r.1 = b then r.2 else 0)).sum
  | [] => rfl
  | (c, n) :: l => by
    simp only [rw, List.count_append, List.count_replicate, count_rw b l, List.map_cons,
      List.sum_cons]
    by_cases h : c = b <;> simp [h]

/-! ### Rotations of a run word -/

theorem rot_cons {p s : List Bool} {c : Bool} {n : Nat} {l : List (Bool × Nat)}
    (h : p ++ s = List.replicate n c ++ rw l) :
    (∃ k, k ≤ n ∧ p = List.replicate k c ∧ s = List.replicate (n - k) c ++ rw l) ∨
    (∃ p', p = List.replicate n c ++ p' ∧ p' ++ s = rw l) := by
  rcases List.append_eq_append_iff.mp h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · -- replicate n c = p ++ a', s = a' ++ rw l: the cut is inside the run
    have hp : p = List.replicate p.length c := by
      apply List.eq_replicate_iff.mpr
      refine ⟨rfl, fun x hx => ?_⟩
      have : x ∈ List.replicate n c := h1 ▸ List.mem_append_left _ hx
      exact (List.mem_replicate.mp this).2
    have ha : a' = List.replicate a'.length c := by
      apply List.eq_replicate_iff.mpr
      refine ⟨rfl, fun x hx => ?_⟩
      have : x ∈ List.replicate n c := h1 ▸ List.mem_append_right _ hx
      exact (List.mem_replicate.mp this).2
    have hlen := congrArg List.length h1
    simp only [List.length_append, List.length_replicate] at hlen
    refine Or.inl ⟨p.length, by omega, hp, ?_⟩
    rw [h2, ha]
    congr 2
    omega
  · exact Or.inr ⟨c', h1, h2.symm⟩

end Blocks
