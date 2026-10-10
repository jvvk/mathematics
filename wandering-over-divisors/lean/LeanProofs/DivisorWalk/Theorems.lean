import LeanProofs.DivisorWalk.Game

/-!
# Theorems 3, 5 and 7 of the note

Theorem 3: from `(k, k)` with `k < n`, Alice's openings `E` and `N` lose.
Theorem 5: from `(a, 0)` with `1 ≤ a ≤ n` and `n ≥ 2`, Alice's opening `N` loses.
Theorem 7: the corners `(n, 0)`, `(0, n)` and the square `(2, 0)` are losing for `n ≥ 2`, and `(2, 2)` for
`n ≥ 3`.
-/

namespace DivisorWalk

/-! ## Theorem 3 -/

/-- End of a climb along the main diagonal: at `(n, n)` Alice's only move is `D`, which is named. -/
lemma corner_stuck (n : ℕ) (hn : 1 ≤ n) (V : Finset Sq) (hD : (n - 1, n - 1) ∈ V) :
    BobWins n V (n, n) := by
  refine BobWins.of ?_
  intro q hm hq
  obtain ⟨h1, h2, h | h | ⟨_, _, h⟩⟩ := hm
  · simp [h] at h1
  · simp [h] at h2
  · exact absurd (by simpa [h] using hD) hq

/-- Theorem 3: Alice starts at `(k, k)`, `k < n`, and opens `E` or `N`; Bob answers and wins. -/
theorem diag (n k : ℕ) (hk : k < n) (q : Sq) (hq : q = (k + 1, k) ∨ q = (k, k + 1)) :
    BobAnswers n (insert q {(k, k)}) q := by
  refine ⟨(k + 1, k + 1), ?_, ?_, ?_⟩
  · rcases hq with rfl | rfl
    · exact ⟨by simp; omega, by simp; omega, Or.inr (Or.inl rfl)⟩
    · exact ⟨by simp; omega, by simp; omega, Or.inl rfl⟩
  · rcases hq with rfl | rfl <;> simp [Prod.ext_iff]
  · refine climb n (fun _ => False) (fun _ => True) (fun _ _ _ => trivial) (fun x y => x = y)
      (fun x y h => by simp [h]) ?_ (2 * n) (k + 1) (k + 1) _ (by omega) (by omega) (by omega) rfl
      trivial (Finset.mem_insert_self _ _) (fun _ _ _ _ => ⟨id, id, id⟩) ?_ ?_
    · intro V x y he hx hy hxy _ hp _ hD
      subst hxy
      have hxn : x = n := by omega
      subst hxn
      rcases hD with h | h | h
      · omega
      · omega
      · exact corner_stuck x (by omega) V h
    · intro v hv
      right
      rcases hq with rfl | rfl <;> simp at hv <;> rcases hv with rfl | rfl | rfl <;> simp <;> omega
    · right; right
      rcases hq with rfl | rfl <;> simp

/-! ## Theorem 5 -/

/-- The end of the climb along `x - y = -2`, and the sweep down the right-hand edge. -/
lemma bottom_end (n a : ℕ) (hn : 2 ≤ n) (ha : a ≤ n) (V : Finset Sq) (x y : ℕ)
    (he : x = n ∨ y = n) (hx : x ≤ n) (hy : y ≤ n) (hQ : y = x + 2)
    (hP : ∀ j, 1 ≤ j → j ≤ a → (j, 1) ∈ V) (hp : (x, y) ∈ V)
    (hV : ∀ v ∈ V, (v.2 ≤ 1 ∧ v.1 ≤ a) ∨ (v.1 ≤ x ∧ v.2 ≤ y))
    (hD : x = 0 ∨ y = 0 ∨ (x - 1, y - 1) ∈ V) : BobWins n V (x, y) := by
  have hyn : y = n := by omega
  have hxn : x = n - 2 := by omega
  subst hxn
  rw [hyn] at hp hV hD ⊢
  clear hQ he hy hyn
  refine BobWins.of ?_
  intro q hm hq
  obtain ⟨h1, h2, h | h | ⟨hx1, _, h⟩⟩ := hm
  · -- Alice steps E to (n - 1, n); Bob steps E to the corner.
    subst h
    refine ⟨(n, n), ⟨le_refl _, le_refl _, Or.inl (by simp; omega)⟩, ?_, ?_⟩
    · intro hmem
      rcases Finset.mem_insert.mp hmem with h' | h'
      · simp [Prod.ext_iff] at h'; omega
      · rcases hV _ h' with h'' | h'' <;> simp at h'' <;> omega
    · refine sweep n n n (if a < n then 0 else 2) _ (by omega) (by split_ifs <;> omega) le_rfl
        (Finset.mem_insert_self _ _) (Or.inl rfl) ?_ ?_
      · intro j hj1 hj2 hmem
        rcases Finset.mem_insert.mp hmem with h' | h'
        · simp [Prod.ext_iff] at h'; omega
        rcases Finset.mem_insert.mp h' with h'' | h''
        · simp [Prod.ext_iff] at h''; omega
        · rcases hV _ h'' with h3 | h3
          · simp at h3; split_ifs at hj1 <;> omega
          · simp at h3; omega
      · split_ifs with hlt
        · exact Or.inl rfl
        · right
          have e : (n - 1, 2 - 1) = (n - 1, 1) := by simp
          rw [e]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hP (n - 1) (by omega) (by omega)))
  · simp [h] at h2
  · exfalso
    simp at hx1
    rcases hD with hD | hD | hD
    · omega
    · omega
    · exact hq (by simpa [h] using hD)

/-- Phase 1: the piece walks west along the bottom row. The named squares are exactly the bottom-row
squares from `b` to `a` and the row-one squares from `b + 1` to `a`. -/
theorem bottom_phase1 (n a : ℕ) (hn : 2 ≤ n) (ha : a ≤ n) (ha1 : 1 ≤ a) :
    ∀ (b : ℕ) (V : Finset Sq), b < a →
      (∀ v, v ∈ V ↔ (v.2 = 0 ∧ b ≤ v.1 ∧ v.1 ≤ a) ∨ (v.2 = 1 ∧ b < v.1 ∧ v.1 ≤ a)) →
      BobWins n V (b, 0) := by
  intro b
  induction b with
  | zero =>
    intro V hb hV
    refine BobWins.of ?_
    intro q hm hq
    obtain ⟨h1, h2, h | h | ⟨hx1, hy1, h⟩⟩ := hm
    · exact absurd ((hV q).mpr (Or.inl ⟨by simp [h], by simp [h], by simp [h]; try omega⟩)) hq
    · -- Alice steps N to (0, 1); Bob steps N to (0, 2) and climbs x - y = -2.
      subst h
      refine ⟨(0, 2), ⟨by simp, by simp; omega, Or.inr (Or.inl rfl)⟩, ?_, ?_⟩
      · intro hmem
        rcases Finset.mem_insert.mp hmem with h' | h'
        · simp at h'
        · have := (hV _).mp h'; simp at this
      · refine climb n (fun v => v.2 ≤ 1 ∧ v.1 ≤ a) (fun V => ∀ j, 1 ≤ j → j ≤ a → (j, 1) ∈ V)
          (fun V c h j h1 h2 => Finset.mem_insert_of_mem (h j h1 h2)) (fun x y => y = x + 2)
          (fun x y h => by omega) ?_ (2 * n) 0 2 _ (by omega) (by omega) (by omega) rfl ?_
          (Finset.mem_insert_self _ _) ?_ ?_ (Or.inl rfl)
        · intro V' x y he hx hy hQ hP hp hV' hD
          exact bottom_end n a hn ha V' x y he hx hy hQ hP hp hV' hD
        · intro j hj1 hj2
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((hV _).mpr (Or.inr ⟨rfl, by omega, hj2⟩)))
        · intro u w _ hw
          refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega
        · intro v hv
          rcases Finset.mem_insert.mp hv with h' | h'
          · right; simp [h']
          rcases Finset.mem_insert.mp h' with h'' | h''
          · left; simp [h'']
          · left
            rcases (hV v).mp h'' with ⟨e1, _, e3⟩ | ⟨e1, _, e3⟩ <;> omega
    · simp at hy1
  | succ b ih =>
    intro V hb hV
    refine BobWins.of ?_
    intro q hm hq
    obtain ⟨h1, h2, h | h | ⟨hx1, hy1, h⟩⟩ := hm
    · exact absurd ((hV q).mpr (Or.inl ⟨by simp [h], by simp [h]; try omega, by simp [h]; try omega⟩)) hq
    · -- Alice steps N to (b + 1, 1); Bob steps D to (b, 0).
      subst h
      refine ⟨(b, 0), ⟨by simp; omega, by simp, Or.inr (Or.inr ⟨by simp, by simp, by simp⟩)⟩, ?_, ?_⟩
      · intro hmem
        rcases Finset.mem_insert.mp hmem with h' | h'
        · simp at h'
        · have := (hV _).mp h'; simp at this
      · refine ih _ (by omega) ?_
        intro v
        constructor
        · intro hv
          rcases Finset.mem_insert.mp hv with h' | h'
          · left; simp [h']; omega
          rcases Finset.mem_insert.mp h' with h'' | h''
          · right; simp [h'']; omega
          · rcases (hV v).mp h'' with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
            · left; exact ⟨e1, by omega, e3⟩
            · right; exact ⟨e1, by omega, e3⟩
        · intro hv
          rcases hv with ⟨e1, e2, e3⟩ | ⟨e1, e2, e3⟩
          · by_cases hb' : v.1 = b
            · exact Finset.mem_insert.mpr (Or.inl (Prod.ext hb' e1))
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((hV v).mpr (Or.inl ⟨e1, by omega, e3⟩)))
          · by_cases hb' : v.1 = b + 1
            · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl (Prod.ext hb' e1)))
            · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((hV v).mpr (Or.inr ⟨e1, by omega, e3⟩)))
    · simp at hy1

/-- Theorem 5: Alice starts at `(a, 0)` and opens `N`; Bob answers and wins. -/
theorem bottom (n a : ℕ) (hn : 2 ≤ n) (ha1 : 1 ≤ a) (ha : a ≤ n) :
    BobAnswers n (insert (a, 1) {(a, 0)}) (a, 1) := by
  refine ⟨(a - 1, 0), ⟨by simp; omega, by simp, Or.inr (Or.inr ⟨by simp; omega, by simp, by simp⟩)⟩, ?_, ?_⟩
  · simp [Prod.ext_iff]; omega
  · refine bottom_phase1 n a hn ha ha1 (a - 1) _ (by omega) ?_
    intro v
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff]
    omega

/-! ## Theorem 7 -/

/-- The corner `(n, 0)` is losing for `n ≥ 2`. -/
theorem corner_right (n : ℕ) (hn : 2 ≤ n) : BobWins n {(n, 0)} (n, 0) := by
  refine BobWins.of ?_
  intro q hm hq
  obtain ⟨h1, h2, h | h | ⟨_, hy1, h⟩⟩ := hm
  · simp [h] at h1
  · subst h
    exact bottom n n hn (by omega) le_rfl
  · simp at hy1

/-- The corner `(0, n)` is losing for `n ≥ 2`, by reflection. -/
theorem corner_left (n : ℕ) (hn : 2 ≤ n) : BobWins n {(0, n)} (0, n) := by
  simpa [sw] using reflect (corner_right n hn)

/-- End of a climb along `x - y = 2`: Alice's only move from `(n, n - 2)` is `N`, Bob steps to the corner,
and the top row is swept. `F` holds the named squares off the climb; none lies in the top row. -/
lemma two_end (n : ℕ) (hn : 3 ≤ n) (F : Sq → Prop) (hFtop : ∀ j, ¬ F (j, n))
    (V : Finset Sq) (x y : ℕ) (he : x = n ∨ y = n) (hx : x ≤ n) (hy : y ≤ n) (hQ : x = y + 2)
    (hp : (x, y) ∈ V) (hV : ∀ v ∈ V, F v ∨ (v.1 ≤ x ∧ v.2 ≤ y))
    (hD : x = 0 ∨ y = 0 ∨ (x - 1, y - 1) ∈ V) : BobWins n V (x, y) := by
  have hxn : x = n := by omega
  have hyn : y = n - 2 := by omega
  subst hxn
  subst hyn
  refine BobWins.of ?_
  intro q hm hq
  obtain ⟨h1, h2, h | h | ⟨_, hy1, h⟩⟩ := hm
  · simp [h] at h1
  · -- Alice steps N to (n, n - 1); Bob steps N to (n, n).
    subst h
    refine ⟨(x, x), ⟨le_refl _, le_refl _, Or.inr (Or.inl (by simp; omega))⟩, ?_, ?_⟩
    · intro hmem
      rcases Finset.mem_insert.mp hmem with h' | h'
      · simp [Prod.ext_iff] at h'; omega
      · rcases hV _ h' with h'' | h''
        · exact hFtop x h''
        · simp at h''; omega
    · refine sweep_top x x 0 _ (by omega) le_rfl (Finset.mem_insert_self _ _) (Or.inl rfl) ?_ (Or.inl rfl)
      intro j _ hj hmem
      rcases Finset.mem_insert.mp hmem with h' | h'
      · simp [Prod.ext_iff] at h'; omega
      rcases Finset.mem_insert.mp h' with h'' | h''
      · simp [Prod.ext_iff] at h''; omega
      · rcases hV _ h'' with h3 | h3
        · exact hFtop j h3
        · simp at h3; omega
  · exfalso
    rcases hD with hD | hD | hD
    · omega
    · simp at hy1; omega
    · exact hq (by simpa [h] using hD)

/-- The climb along `x - y = 2` from `(3, 1)`, with the squares in `F` out of its way. -/
lemma two_climb (n : ℕ) (hn : 3 ≤ n) (F : Sq → Prop) (hFtop : ∀ j, ¬ F (j, n))
    (hFfar : ∀ u w, 3 ≤ u → ¬ F (u + 1, w) ∧ ¬ F (u, w + 1) ∧ ¬ F (u + 1, w + 1))
    (V : Finset Sq) (hp : (3, 1) ∈ V) (h20 : (2, 0) ∈ V) (hV : ∀ v ∈ V, F v ∨ (v.1 ≤ 3 ∧ v.2 ≤ 1)) :
    BobWins n V (3, 1) :=
  climb n F (fun _ => True) (fun _ _ _ => trivial) (fun x y => x = y + 2) (fun x y h => by omega)
    (fun V' x y he hx hy hQ _ hp' hV' hD => two_end n hn F hFtop V' x y he hx hy hQ hp' hV' hD)
    (2 * n) 3 1 V (by omega) (by omega) (by omega) rfl trivial hp
    (fun u w hu _ => hFfar u w hu) hV (Or.inr (Or.inr (by simpa using h20)))

/-- The square `(2, 0)` is losing for `n ≥ 2`. -/
theorem two_zero (n : ℕ) (hn : 2 ≤ n) : BobWins n {(2, 0)} (2, 0) := by
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · have : n = 2 := by omega
    subst this
    exact corner_right 2 le_rfl
  refine BobWins.of ?_
  intro q hm hq
  obtain ⟨h1, h2, h | h | ⟨_, hy1, h⟩⟩ := hm
  · -- Alice opens E to (3, 0); Bob answers N to (3, 1) and climbs.
    subst h
    refine ⟨(3, 1), ⟨by simp; omega, by simp; omega, Or.inr (Or.inl rfl)⟩, by simp, ?_⟩
    refine two_climb n h3 (fun _ => False) (fun _ => id) (fun _ _ _ => ⟨id, id, id⟩) _
      (Finset.mem_insert_self _ _) (by simp) ?_
    intro v hv
    right
    simp at hv
    rcases hv with rfl | rfl | rfl <;> simp
  · subst h
    exact bottom n 2 hn (by omega) (by omega)
  · simp at hy1

/-- From `(2, 0)` with `(0, 0)`, `(1, 0)`, `(1, 1)`, `(2, 2)` named: Bob wins (part of the proof for
`(2, 2)`). -/
lemma two_zero_after (n : ℕ) (hn : 3 ≤ n) :
    BobWins n {(2, 0), (1, 0), (0, 0), (1, 1), (2, 2)} (2, 0) := by
  have hF : ∀ v : Sq, v ∈ ({(1, 0), (0, 0), (1, 1), (2, 2)} : Finset Sq) → v.1 ≤ 2 ∧ v.2 ≤ 2 := by
    intro v hv; simp at hv; rcases hv with rfl | rfl | rfl | rfl <;> simp
  refine BobWins.of ?_
  intro q hm hq
  obtain ⟨h1, h2, h | h | ⟨_, hy1, h⟩⟩ := hm
  · subst h
    refine ⟨(3, 1), ⟨by simp; omega, by simp; omega, Or.inr (Or.inl rfl)⟩, by simp, ?_⟩
    refine two_climb n hn (fun v => v.1 ≤ 2 ∧ v.2 ≤ 2) (fun j h => by simp at h; omega)
      (fun u w hu => ⟨by simp; omega, by simp; omega, by simp; omega⟩) _ (Finset.mem_insert_self _ _)
      (by simp) ?_
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · subst h
    refine ⟨(3, 1), ⟨by simp; omega, by simp; omega, Or.inl rfl⟩, by simp, ?_⟩
    refine two_climb n hn (fun v => v.1 ≤ 2 ∧ v.2 ≤ 2) (fun j h => by simp at h; omega)
      (fun u w hu => ⟨by simp; omega, by simp; omega, by simp; omega⟩) _ (Finset.mem_insert_self _ _)
      (by simp) ?_
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · simp at hy1

/-- The square `(2, 2)` is losing for `n ≥ 3`. -/
theorem two_two (n : ℕ) (hn : 3 ≤ n) : BobWins n {(2, 2)} (2, 2) := by
  refine BobWins.of ?_
  intro q hm hq
  obtain ⟨h1, h2, h | h | ⟨_, _, h⟩⟩ := hm
  · subst h
    obtain ⟨r, hr, hrV, hw⟩ := diag n 2 (by omega) (3, 2) (Or.inl rfl)
    exact ⟨r, hr, hrV, hw⟩
  · subst h
    obtain ⟨r, hr, hrV, hw⟩ := diag n 2 (by omega) (2, 3) (Or.inr rfl)
    exact ⟨r, hr, hrV, hw⟩
  · -- Alice opens D to (1, 1); Bob answers D to (0, 0).
    subst h
    refine ⟨(0, 0), ⟨by simp, by simp, Or.inr (Or.inr ⟨by simp, by simp, by simp⟩)⟩, by simp, ?_⟩
    refine BobWins.of ?_
    intro q hm hq
    obtain ⟨_, _, h | h | ⟨hx1, _, _⟩⟩ := hm
    · -- Alice steps E to (1, 0); Bob steps E to (2, 0).
      subst h
      refine ⟨(2, 0), ⟨by simp; omega, by simp, Or.inl rfl⟩, by simp, ?_⟩
      have e : (insert (2, 0) (insert (1, 0) (insert (0, 0) (insert (1, 1) {(2, 2)}))) : Finset Sq)
          = {(2, 0), (1, 0), (0, 0), (1, 1), (2, 2)} := rfl
      simpa using two_zero_after n hn
    · -- Alice steps N to (0, 1); Bob steps N to (0, 2): the reflection of the previous case.
      subst h
      refine ⟨(0, 2), ⟨by simp, by simp; omega, Or.inr (Or.inl rfl)⟩, by simp, ?_⟩
      have h := reflect (two_zero_after n hn)
      have e : ({(2, 0), (1, 0), (0, 0), (1, 1), (2, 2)} : Finset Sq).image sw
          = {(0, 2), (0, 1), (0, 0), (1, 1), (2, 2)} := by decide
      rw [e] at h
      have e2 : (insert (0, 2) (insert (0, 1) (insert (0, 0) (insert (1, 1) {(2, 2)}))) : Finset Sq)
          = {(0, 2), (0, 1), (0, 0), (1, 1), (2, 2)} := rfl
      simpa [sw] using h
    · simp at hx1

end DivisorWalk
