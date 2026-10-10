import LeanProofs.CappedDice

/-!
# Capped dice: the equality cases (MSE 5149864)

For `k = 4` faces and `1/3 < r < 1/2`, `s = 1 - 2r`, which pairs `(p, q)` rolled `n` times reach the least overlap?

* `equality_ge3`: for `n ≥ 3` only the staircase pair with its faces relabelled: one face each of `(r, 0)`, `(r, s)`,
  `(s, r)`, `(0, r)`.
* `equality_one`: for `n = 1` exactly the pairs with `max(pᵢ, qᵢ) = r` on every face.
* `equality_two_family`: for `n = 2` the pairs `p = (r, r, x, s - x)`, `q = (0, s, r, r)` reach it too.

The route: equal overlaps force equal excess at every pair of rates `(u, v)` that the proof of `G_le` passes
through (`tight_rates`). Equal excess at one pair of rates forces the faces where `u p > v q` to be tight
(`tight`): their `p` mass is `min(1, a r)` and their `q` mass is `max(0, 1 - (k - a) r)`. Three rates pin the pair.
-/

namespace CappedDice

open Finset

/-! ### Tightness at one pair of rates (any `k`) -/

/-- The faces where `u p` beats `v q`. -/
noncomputable def pos {k : ℕ} (p q : Fin k → ℝ) (u v : ℝ) : Finset (Fin k) := univ.filter (fun i => 0 < u * p i - v * q i)

theorem g_eq_pos {k : ℕ} (p q : Fin k → ℝ) (u v : ℝ) :
    g p q u v = u * ∑ i ∈ pos p q u v, p i - v * ∑ i ∈ pos p q u v, q i := by
  rw [g, sum_pos_part, sum_sub_distrib, mul_sum, mul_sum]; rfl

theorem p_le {k : ℕ} {r : ℝ} {p : Fin k → ℝ} (hp : Adm r p) (A : Finset (Fin k)) :
    ∑ i ∈ A, p i ≤ min 1 (A.card * r) := by
  refine le_min ?_ ?_
  · rw [← hp.2]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ A) fun i _ _ => (hp.1 i).1
  · have := sum_le_card_nsmul A p r fun i _ => (hp.1 i).2
    simpa using this

theorem card_compl' {k : ℕ} (A : Finset (Fin k)) : (Aᶜ.card : ℝ) = k - A.card := by
  rw [card_compl, Fintype.card_fin, Nat.cast_sub (card_le_univ A |>.trans (by simp))]

theorem q_ge {k : ℕ} {r : ℝ} {q : Fin k → ℝ} (hq : Adm r q) (A : Finset (Fin k)) :
    max 0 (1 - (k - A.card) * r) ≤ ∑ i ∈ A, q i := by
  refine max_le (sum_nonneg fun i _ => (hq.1 i).1) ?_
  have hsplit := sum_add_sum_compl A q
  rw [hq.2] at hsplit
  have hc : ∑ i ∈ Aᶜ, q i ≤ (Aᶜ.card : ℝ) * r := by
    have := sum_le_card_nsmul Aᶜ q r fun i _ => (hq.1 i).2
    simpa using this
  rw [card_compl'] at hc
  linarith

/-- The bound of `excess_le` for `a` faces. -/
noncomputable def bnd (k : ℕ) (r u v : ℝ) (a : ℕ) : ℝ := u * min 1 (a * r) - v * max 0 (1 - (k - a) * r)

/-- Equal excess at `(u, v)` makes the faces where `u p > v q` tight, and their bound the largest. -/
theorem tight {k : ℕ} {r : ℝ} (hr : 0 ≤ r) (hk : 1 ≤ k * r) {p q : Fin k → ℝ} (hp : Adm r p) (hq : Adm r q)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (h : g p q u v = g (pstar k r) (qstar k r) u v) :
    ∑ i ∈ pos p q u v, p i = min 1 ((pos p q u v).card * r) ∧
      ∑ i ∈ pos p q u v, q i = max 0 (1 - (k - (pos p q u v).card) * r) ∧
      ∀ a ≤ k, bnd k r u v a ≤ bnd k r u v (pos p q u v).card := by
  set A := pos p q u v
  have h1 := p_le hp A
  have h2 := q_ge hq A
  have h3 := stair_excess_ge hr hk (u := u) (v := v) (card_le_univ A |>.trans (by simp))
  have hg := g_eq_pos p q u v
  have m1 := mul_le_mul_of_nonneg_left h1 hu.le
  have m2 := mul_le_mul_of_nonneg_left h2 hv.le
  refine ⟨?_, ?_, fun a ha => ?_⟩
  · by_contra hne
    have : u * ∑ i ∈ A, p i < u * min 1 (A.card * r) := mul_lt_mul_of_pos_left (lt_of_le_of_ne h1 hne) hu
    linarith
  · by_contra hne
    have : v * max 0 (1 - (k - A.card) * r) < v * ∑ i ∈ A, q i :=
      mul_lt_mul_of_pos_left (lt_of_le_of_ne h2 (Ne.symm hne)) hv
    linarith
  · have := stair_excess_ge hr hk (u := u) (v := v) ha
    unfold bnd; linarith

theorem eq_of_sum_le {k : ℕ} {A : Finset (Fin k)} {f : Fin k → ℝ} {c : ℝ} (hle : ∀ i ∈ A, f i ≤ c)
    (hs : ∑ i ∈ A, f i = A.card * c) : ∀ i ∈ A, f i = c := by
  have h0 : ∑ i ∈ A, (c - f i) = 0 := by rw [sum_sub_distrib, hs]; simp
  intro i hi
  have := (sum_eq_zero_iff_of_nonneg fun j hj => sub_nonneg.mpr (hle j hj)).mp h0 i hi
  linarith

theorem eq_zero_of_sum {k : ℕ} {A : Finset (Fin k)} {f : Fin k → ℝ} (hnn : ∀ i ∈ A, 0 ≤ f i)
    (hs : ∑ i ∈ A, f i = 0) : ∀ i ∈ A, f i = 0 :=
  (sum_eq_zero_iff_of_nonneg hnn).mp hs

theorem compl_sum {k : ℕ} {f : Fin k → ℝ} (hf : ∑ i, f i = 1) (A : Finset (Fin k)) :
    ∑ i ∈ Aᶜ, f i = 1 - ∑ i ∈ A, f i := by
  have := sum_add_sum_compl A f; rw [hf] at this; linarith

/-! ### Four faces, `1/3 < r < 1/2` -/

section Four

variable {r : ℝ}

theorem bnd_vals (h1 : 1 / 3 < r) (h2 : r < 1 / 2) (u v : ℝ) :
    bnd 4 r u v 0 = 0 ∧ bnd 4 r u v 1 = u * r ∧ bnd 4 r u v 2 = 2 * u * r - v * (1 - 2 * r) ∧
      bnd 4 r u v 3 = u - v * (1 - r) ∧ bnd 4 r u v 4 = u - v := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [bnd] <;> push_cast
  · rw [zero_mul, min_eq_right zero_le_one, max_eq_left (by linarith)]; ring
  · rw [one_mul, min_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · rw [min_eq_right (by linarith), max_eq_right (by linarith)]; ring
  · rw [min_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [min_eq_left (by linarith), max_eq_right (by linarith)]; ring

/-- Card of the tight set, with its masses, for four faces. -/
theorem tight4 (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {p q : Fin 4 → ℝ} (hp : Adm r p) (hq : Adm r q)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (h : g p q u v = g (pstar 4 r) (qstar 4 r) u v) :
    ∃ c ≤ 4, (pos p q u v).card = c ∧ ∑ i ∈ pos p q u v, p i = min 1 (c * r) ∧
      ∑ i ∈ pos p q u v, q i = max 0 (1 - (4 - c) * r) ∧ ∀ a ≤ 4, bnd 4 r u v a ≤ bnd 4 r u v c := by
  have hk : 1 ≤ (4 : ℕ) * r := by push_cast; linarith
  obtain ⟨t1, t2, t3⟩ := tight (by linarith) hk hp hq hu hv h
  refine ⟨_, card_le_univ _ |>.trans (by simp), rfl, t1, by simpa using t2, t3⟩

/-- A rate above `r/s` forces a face `(r, 0)`. -/
theorem face_r0 (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {p q : Fin 4 → ℝ} (hp : Adm r p) (hq : Adm r q)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : u * r < v * (1 - 2 * r))
    (h : g p q u v = g (pstar 4 r) (qstar 4 r) u v) : ∃ i, p i = r ∧ q i = 0 := by
  obtain ⟨c, hc, hcard, sp, sq, hb⟩ := tight4 h1 h2 hp hq hu hv h
  obtain ⟨b0, b1, b2, b3, b4⟩ := bnd_vals h1 h2 u v
  have k1 := hb 1 (by norm_num)
  interval_cases c
  · rw [b0, b1] at k1; nlinarith
  · obtain ⟨i, hi⟩ := card_eq_one.mp hcard
    rw [hi] at sp sq
    simp only [sum_singleton, Nat.cast_one, one_mul] at sp sq
    refine ⟨i, by rw [sp, min_eq_right (by linarith)], by rw [sq, max_eq_left (by norm_num; linarith)]⟩
  · rw [b2, b1] at k1; nlinarith
  · rw [b3, b1] at k1; nlinarith
  · rw [b4, b1] at k1; nlinarith

/-- A rate below `s/r` forces a face `(0, r)`. -/
theorem face_0r (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {p q : Fin 4 → ℝ} (hp : Adm r p) (hq : Adm r q)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (huv : v * r < u * (1 - 2 * r))
    (h : g p q u v = g (pstar 4 r) (qstar 4 r) u v) : ∃ j, p j = 0 ∧ q j = r := by
  obtain ⟨c, hc, hcard, sp, sq, hb⟩ := tight4 h1 h2 hp hq hu hv h
  obtain ⟨b0, b1, b2, b3, b4⟩ := bnd_vals h1 h2 u v
  have k3 := hb 3 (by norm_num)
  interval_cases c
  · rw [b0, b3] at k3; nlinarith
  · rw [b1, b3] at k3; nlinarith
  · rw [b2, b3] at k3; nlinarith
  · have hcc : (pos p q u v)ᶜ.card = 1 := by rw [card_compl, Fintype.card_fin, hcard]
    obtain ⟨j, hj⟩ := card_eq_one.mp hcc
    have pc := compl_sum hp.2 (pos p q u v)
    have qc := compl_sum hq.2 (pos p q u v)
    rw [sp, min_eq_left (by norm_num; linarith)] at pc
    rw [sq, max_eq_right (by norm_num; linarith)] at qc
    rw [hj, sum_singleton] at pc qc
    norm_num at pc qc
    exact ⟨j, by linarith, by linarith⟩
  · rw [b4, b3] at k3; nlinarith

/-- Between the two rates, `s/r ≤ v/u ≤ 1`: the tight set has two faces, or three when `v/u = s/r`. -/
theorem mid_card (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {p q : Fin 4 → ℝ} (hp : Adm r p) (hq : Adm r q)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u) (huv : u * (1 - 2 * r) ≤ v * r)
    (h : g p q u v = g (pstar 4 r) (qstar 4 r) u v) :
    ((pos p q u v).card = 2 ∧ ∑ i ∈ pos p q u v, p i = 2 * r ∧ ∑ i ∈ pos p q u v, q i = 1 - 2 * r) ∨
      ((pos p q u v).card = 3 ∧ u * (1 - 2 * r) = v * r) := by
  obtain ⟨c, hc, hcard, sp, sq, hb⟩ := tight4 h1 h2 hp hq hu hv h
  obtain ⟨b0, b1, b2, b3, b4⟩ := bnd_vals h1 h2 u v
  have k2 := hb 2 (by norm_num)
  have k3 := hb 3 (by norm_num)
  interval_cases c
  · rw [b0, b2] at k2; nlinarith
  · rw [b1, b2] at k2; nlinarith
  · left
    refine ⟨hcard, by rw [sp, min_eq_right (by norm_num; linarith)]; push_cast; ring, ?_⟩
    rw [sq, max_eq_right (by norm_num; linarith)]; push_cast; ring
  · right; rw [b3, b2] at k2; exact ⟨hcard, by nlinarith⟩
  · rw [b4, b2] at k2; nlinarith

end Four

/-! ### From equal overlaps to equal excess at the rates of the proof -/

/-- Consing the same first roll preserves domination of the rest. -/
theorem cons_mono {k n : ℕ} (h : (Fin k → ℝ) × (Fin k → ℝ)) (hh1 : ∀ i, 0 ≤ h.1 i) (hh2 : ∀ i, 0 ≤ h.2 i)
    {D E : Fin n → (Fin k → ℝ) × (Fin k → ℝ)} (hDE : ∀ u v, 0 ≤ u → 0 ≤ v → G D u v ≤ G E u v)
    (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) : G (Fin.cons h D) u v ≤ G (Fin.cons h E) u v := by
  rw [G_succ, G_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  exact sum_le_sum fun i _ => hDE _ _ (mul_nonneg hu (hh1 i)) (mul_nonneg hv (hh2 i))

theorem const_succ {k n : ℕ} (h : (Fin k → ℝ) × (Fin k → ℝ)) :
    (fun _ : Fin (n + 1) => h) = Fin.cons h (fun _ : Fin n => h) := by
  funext i; refine Fin.cases rfl (fun _ => rfl) i

section Chain

variable {k : ℕ} {r : ℝ} {p q : Fin k → ℝ}

/-- `m` rolls of the staircase pair. -/
noncomputable abbrev S (k : ℕ) (r : ℝ) (m : ℕ) : Fin m → (Fin k → ℝ) × (Fin k → ℝ) :=
  fun _ => (pstar k r, qstar k r)

theorem head_terms (h : (Fin k → ℝ) × (Fin k → ℝ)) (m : ℕ) (u v : ℝ) :
    G (Fin.cons h (S k r m)) u v = ∑ w, g h.1 h.2 (u * P (S k r m) w) (v * Q (S k r m) w) := by
  rw [G_succ']; simp only [Fin.cons_zero, Fin.cons_succ]

theorem star_terms (m : ℕ) (u v : ℝ) :
    G (S k r (m + 1)) u v = ∑ w, g (pstar k r) (qstar k r) (u * P (S k r m) w) (v * Q (S k r m) w) := by
  rw [show S k r (m + 1) = Fin.cons (pstar k r, qstar k r) (S k r m) from const_succ _, head_terms]

/-- Swapping in `(p, q)` for the first staircase roll can only lower the excess, termwise. -/
theorem head_gap (hr : 0 ≤ r) (hk : 1 ≤ k * r) (hp : Adm r p) (hq : Adm r q) (m : ℕ) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (w : Fin m → Fin k) :
    0 ≤ g (pstar k r) (qstar k r) (u * P (S k r m) w) (v * Q (S k r m) w) -
      g p q (u * P (S k r m) w) (v * Q (S k r m) w) :=
  sub_nonneg.mpr (dominates hr hk hp hq
    (mul_nonneg hu (P_nonneg (fun _ i => ((pstar_adm hr hk).1 i).1) w))
    (mul_nonneg hv (Q_nonneg (fun _ i => ((qstar_adm hr hk).1 i).1) w)))

theorem head_le (hr : 0 ≤ r) (hk : 1 ≤ k * r) (hp : Adm r p) (hq : Adm r q) (m : ℕ) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) : G (Fin.cons (p, q) (S k r m)) u v ≤ G (S k r (m + 1)) u v := by
  rw [head_terms, star_terms]
  exact sum_le_sum fun w _ => sub_nonneg.mp (head_gap hr hk hp hq m hu hv w)

/-- Equal excess after the swap forces equal excess at every rate `(u P*(w), v Q*(w))`. -/
theorem head_eq (hr : 0 ≤ r) (hk : 1 ≤ k * r) (hp : Adm r p) (hq : Adm r q) (m : ℕ) {u v : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (h : G (Fin.cons (p, q) (S k r m)) u v = G (S k r (m + 1)) u v)
    (w : Fin m → Fin k) :
    g p q (u * P (S k r m) w) (v * Q (S k r m) w) =
      g (pstar k r) (qstar k r) (u * P (S k r m) w) (v * Q (S k r m) w) := by
  rw [head_terms, star_terms] at h
  have hsum : ∑ w, (g (pstar k r) (qstar k r) (u * P (S k r m) w) (v * Q (S k r m) w) -
      g p q (u * P (S k r m) w) (v * Q (S k r m) w)) = 0 := by
    rw [sum_sub_distrib]; linarith
  have := (sum_eq_zero_iff_of_nonneg fun w _ => head_gap hr hk hp hq m hu hv w).mp hsum w (mem_univ w)
  simpa using (sub_eq_zero.mp this).symm

theorem G_eq_of_overlap (hr : 0 ≤ r) (hk : 1 ≤ k * r) (hp : Adm r p) (n : ℕ)
    (h : overlap (fun _ : Fin n => (p, q)) = overlap (S k r n)) :
    G (fun _ : Fin n => (p, q)) 1 1 = G (S k r n) 1 1 := by
  rw [overlap_eq (fun _ => hp.2), overlap_eq (fun _ => (pstar_adm hr hk).2)] at h; linarith

theorem const_le (hr : 0 ≤ r) (hk : 1 ≤ k * r) (hp : Adm r p) (hq : Adm r q) (m : ℕ) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) : G (fun _ : Fin m => (p, q)) u v ≤ G (S k r m) u v :=
  G_le (fun i => ((pstar_adm hr hk).1 i).1) (fun i => ((qstar_adm hr hk).1 i).1) m _
    (fun _ i => (hp.1 i).1) (fun _ i => (hq.1 i).1) (fun _ _ _ hu hv => dominates hr hk hp hq hu hv) u v hu hv

/-- First level: equal overlaps over `m + 1` rolls force equal excess at `(P*(w), Q*(w))` for every staircase
word `w` of length `m`. -/
theorem tight_rates (hr : 0 ≤ r) (hk : 1 ≤ k * r) (hp : Adm r p) (hq : Adm r q) (m : ℕ)
    (h : overlap (fun _ : Fin (m + 1) => (p, q)) = overlap (S k r (m + 1))) (w : Fin m → Fin k) :
    g p q (P (S k r m) w) (Q (S k r m) w) = g (pstar k r) (qstar k r) (P (S k r m) w) (Q (S k r m) w) := by
  have hG := G_eq_of_overlap hr hk hp _ h
  have c1 : G (fun _ : Fin (m + 1) => (p, q)) 1 1 ≤ G (Fin.cons (p, q) (S k r m)) 1 1 := by
    rw [const_succ]
    exact cons_mono (p, q) (fun i => (hp.1 i).1) (fun i => (hq.1 i).1) (const_le hr hk hp hq m) 1 1
      zero_le_one zero_le_one
  have c2 := head_le hr hk hp hq m 1 1 zero_le_one zero_le_one
  simpa using head_eq hr hk hp hq m zero_le_one zero_le_one (by linarith) w

/-- Second level: equal overlaps over `m + 2` rolls force equal excess at `(pᵢ P*(w), qᵢ Q*(w))` for every face
`i` and every staircase word `w` of length `m`. -/
theorem tight_rates2 (hr : 0 ≤ r) (hk : 1 ≤ k * r) (hp : Adm r p) (hq : Adm r q) (m : ℕ)
    (h : overlap (fun _ : Fin (m + 2) => (p, q)) = overlap (S k r (m + 2))) (i : Fin k) (w : Fin m → Fin k) :
    g p q (p i * P (S k r m) w) (q i * Q (S k r m) w) =
      g (pstar k r) (qstar k r) (p i * P (S k r m) w) (q i * Q (S k r m) w) := by
  have hp0 : ∀ i, 0 ≤ p i := fun i => (hp.1 i).1
  have hq0 : ∀ i, 0 ≤ q i := fun i => (hq.1 i).1
  have hG := G_eq_of_overlap hr hk hp _ h
  -- G((p,q)^(m+2)) ≤ X2 = G((p,q) ⊗ (p,q) ⊗ S^m) ≤ X1 = G((p,q) ⊗ S^(m+1)) ≤ G(S^(m+2))
  have c1 : G (fun _ : Fin (m + 2) => (p, q)) 1 1 ≤ G (Fin.cons (p, q) (Fin.cons (p, q) (S k r m))) 1 1 := by
    rw [const_succ, const_succ]
    exact cons_mono (p, q) hp0 hq0 (fun u v hu hv => cons_mono (p, q) hp0 hq0 (const_le hr hk hp hq m) u v hu hv)
      1 1 zero_le_one zero_le_one
  have c2 : G (Fin.cons (p, q) (Fin.cons (p, q) (S k r m))) 1 1 ≤ G (Fin.cons (p, q) (S k r (m + 1))) 1 1 :=
    cons_mono (p, q) hp0 hq0 (head_le hr hk hp hq m) 1 1 zero_le_one zero_le_one
  have c3 := head_le hr hk hp hq (m + 1) 1 1 zero_le_one zero_le_one
  have e : G (Fin.cons (p, q) (Fin.cons (p, q) (S k r m))) 1 1 = G (Fin.cons (p, q) (S k r (m + 1))) 1 1 := by
    linarith
  rw [G_succ, G_succ] at e
  simp only [Fin.cons_zero, Fin.cons_succ, one_mul] at e
  have hle : ∀ j ∈ (univ : Finset (Fin k)),
      0 ≤ G (S k r (m + 1)) (p j) (q j) - G (Fin.cons (p, q) (S k r m)) (p j) (q j) := fun j _ =>
    sub_nonneg.mpr (head_le hr hk hp hq m _ _ (hp0 j) (hq0 j))
  have hsum : ∑ j, (G (S k r (m + 1)) (p j) (q j) - G (Fin.cons (p, q) (S k r m)) (p j) (q j)) = 0 := by
    rw [sum_sub_distrib]; linarith
  have hi := (sum_eq_zero_iff_of_nonneg hle).mp hsum i (mem_univ i)
  exact head_eq hr hk hp hq m (hp0 i) (hq0 i) (by linarith) w

end Chain

/-! ### Staircase words for four faces -/

section Words

variable {r : ℝ}

/-- Faces of the four-face staircase pair: `0 ↦ (r, 0)`, `1 ↦ (r, s)`, `2 ↦ (s, r)`, `3 ↦ (0, r)`. -/
theorem star4 (h1 : 1 / 3 < r) (h2 : r < 1 / 2) :
    pstar 4 r 0 = r ∧ qstar 4 r 0 = 0 ∧ pstar 4 r 1 = r ∧ qstar 4 r 1 = 1 - 2 * r ∧
      pstar 4 r 2 = 1 - 2 * r ∧ qstar 4 r 2 = r ∧ pstar 4 r 3 = 0 ∧ qstar 4 r 3 = r := by
  obtain ⟨e0, e1, e2, e3⟩ := stair_values h1 h2
  simp [pstar, qstar, e0, e1, e2, e3]

theorem P_const (m : ℕ) (k : ℕ) (r : ℝ) (i : Fin k) :
    P (S k r m) (fun _ => i) = pstar k r i ^ m ∧ Q (S k r m) (fun _ => i) = qstar k r i ^ m := by
  simp [P, Q]

/-- A balanced word: `j` faces `(r, s)` then `j` faces `(s, r)`; it has `P = Q`. -/
theorem P_balanced (h1 : 1 / 3 < r) (h2 : r < 1 / 2) (j : ℕ) :
    P (S 4 r (j + j)) (fun i => if i.val < j then 1 else 2) = (r * (1 - 2 * r)) ^ j ∧
      Q (S 4 r (j + j)) (fun i => if i.val < j then 1 else 2) = (r * (1 - 2 * r)) ^ j := by
  obtain ⟨-, -, a1, b1, a2, b2, -, -⟩ := star4 h1 h2
  constructor
  · simp only [P]
    rw [Fin.prod_univ_eq_prod_range (fun i => pstar 4 r (if i < j then 1 else 2)) (j + j), prod_range_add]
    have hA : ∀ i ∈ range j, pstar 4 r (if i < j then 1 else 2) = r := fun i hi => by
      simp [mem_range.mp hi, a1]
    have hB : ∀ i ∈ range j, pstar 4 r (if j + i < j then 1 else 2) = 1 - 2 * r := fun i _ => by simp [a2]
    rw [prod_congr rfl hA, prod_congr rfl hB]
    simp [mul_pow]
  · simp only [Q]
    rw [Fin.prod_univ_eq_prod_range (fun i => qstar 4 r (if i < j then 1 else 2)) (j + j), prod_range_add]
    have hA : ∀ i ∈ range j, qstar 4 r (if i < j then 1 else 2) = 1 - 2 * r := fun i hi => by
      simp [mem_range.mp hi, b1]
    have hB : ∀ i ∈ range j, qstar 4 r (if j + i < j then 1 else 2) = r := fun i _ => by simp [b2]
    rw [prod_congr rfl hA, prod_congr rfl hB]
    simp [mul_pow, mul_comm]

theorem rate_gap (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {m : ℕ} (hm : 2 ≤ m) :
    (1 - 2 * r) ^ m * r < r ^ m * (1 - 2 * r) := by
  obtain ⟨l, rfl⟩ : ∃ l, m = l + 2 := ⟨m - 2, by omega⟩
  have hs : 0 < 1 - 2 * r := by linarith
  have hsr : 1 - 2 * r < r := by linarith
  have := pow_lt_pow_left₀ hsr hs.le (show l + 1 ≠ 0 by omega)
  have hrs : 0 < r * (1 - 2 * r) := by nlinarith
  calc (1 - 2 * r) ^ (l + 2) * r = (1 - 2 * r) ^ (l + 1) * (r * (1 - 2 * r)) := by ring
    _ < r ^ (l + 1) * (r * (1 - 2 * r)) := mul_lt_mul_of_pos_right this hrs
    _ = r ^ (l + 2) * (1 - 2 * r) := by ring

end Words

/-! ### Pinning the pair -/

section Pin

variable {r : ℝ}

theorem pair_of_card_two {A : Finset (Fin 4)} {x : Fin 4} (hA : A.card = 2) (hx : x ∈ A) :
    ∃ y, y ≠ x ∧ A = {x, y} := by
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hA
  simp only [mem_insert, mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact ⟨b, hab.symm, rfl⟩
  · exact ⟨a, hab, pair_comm _ _⟩

/-- The staircase pair with its faces relabelled. -/
def Relabel (r : ℝ) (p q : Fin 4 → ℝ) : Prop :=
  ∃ a b c d : Fin 4, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    p a = r ∧ q a = 0 ∧ p b = r ∧ q b = 1 - 2 * r ∧ p c = 1 - 2 * r ∧ q c = r ∧ p d = 0 ∧ q d = r

theorem mem_pos {k : ℕ} {p q : Fin k → ℝ} {u v : ℝ} {i : Fin k} : i ∈ pos p q u v ↔ 0 < u * p i - v * q i := by
  simp [pos]

/-- `n` odd: faces `(r, 0)` and `(0, r)` and equal excess at equal rates pin the pair. -/
theorem pin_odd (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {p q : Fin 4 → ℝ} (hp : Adm r p) (hq : Adm r q)
    {i0 j0 : Fin 4} (hi0 : p i0 = r ∧ q i0 = 0) (hj0 : p j0 = 0 ∧ q j0 = r) {c : ℝ} (hc : 0 < c)
    (h : g p q c c = g (pstar 4 r) (qstar 4 r) c c) : Relabel r p q := by
  rcases mid_card h1 h2 hp hq hc hc le_rfl (by nlinarith) h with ⟨hcard, sp, sq⟩ | ⟨-, he⟩
  swap; · exfalso; nlinarith
  set A := pos p q c c
  have hiA : i0 ∈ A := mem_pos.mpr (by rw [hi0.1, hi0.2]; nlinarith)
  have hjA : j0 ∉ A := fun h => by have := mem_pos.mp h; rw [hj0.1, hj0.2] at this; nlinarith
  obtain ⟨i1, hne, hA⟩ := pair_of_card_two hcard hiA
  have hpA := eq_of_sum_le (A := A) (f := p) (c := r) (fun i _ => (hp.1 i).2) (by rw [sp, hcard]; push_cast; ring)
  have hi1 : i1 ∈ A := by rw [hA]; simp
  have pi1 := hpA i1 hi1
  have qi1 : q i1 = 1 - 2 * r := by
    rw [hA, sum_pair hne.symm, hi0.2] at sq; linarith
  have hcc : Aᶜ.card = 2 := by rw [card_compl, Fintype.card_fin, hcard]
  obtain ⟨j1, hne', hAc⟩ := pair_of_card_two hcc (mem_compl.mpr hjA)
  have pc := compl_sum hp.2 A
  have qc := compl_sum hq.2 A
  rw [sp] at pc; rw [sq] at qc
  have hqAc := eq_of_sum_le (A := Aᶜ) (f := q) (c := r) (fun i _ => (hq.1 i).2)
    (by rw [qc, hcc]; push_cast; ring)
  have hj1 : j1 ∈ Aᶜ := by rw [hAc]; simp
  have qj1 := hqAc j1 hj1
  have pj1 : p j1 = 1 - 2 * r := by rw [hAc, sum_pair hne'.symm, hj0.1] at pc; linarith
  have hj1A : j1 ∉ A := mem_compl.mp hj1
  refine ⟨i0, i1, j1, j0, hne.symm, fun e => hj1A (e ▸ hiA), fun e => hjA (e ▸ hiA),
    fun e => hj1A (e ▸ hi1), fun e => hjA (e ▸ hi1), hne', hi0.1, hi0.2, pi1, qi1, pj1, qj1, hj0.1, hj0.2⟩

/-- `n` even: faces `(r, 0)` and `(0, r)`, and equal excess at `(pᵢ c, qᵢ c)` for every face, pin the pair. -/
theorem pin_even (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {p q : Fin 4 → ℝ} (hp : Adm r p) (hq : Adm r q)
    {i0 j0 : Fin 4} (hi0 : p i0 = r ∧ q i0 = 0) (hj0 : p j0 = 0 ∧ q j0 = r) {c : ℝ} (hc : 0 < c)
    (h : ∀ i, g p q (p i * c) (q i * c) = g (pstar 4 r) (qstar 4 r) (p i * c) (q i * c)) : Relabel r p q := by
  have hij : i0 ≠ j0 := fun e => by rw [e, hj0.1] at hi0; linarith [hi0.1]
  set M : Finset (Fin 4) := ({i0, j0} : Finset (Fin 4))ᶜ
  have hM : M.card = 2 := by rw [card_compl, Fintype.card_fin, card_pair hij]
  have pM : ∑ i ∈ M, p i = 1 - r := by rw [compl_sum hp.2, sum_pair hij, hi0.1, hj0.1]; ring
  have qM : ∑ i ∈ M, q i = 1 - r := by rw [compl_sum hq.2, sum_pair hij, hi0.2, hj0.2]; ring
  obtain ⟨i1, hi1M, hqp⟩ : ∃ i1 ∈ M, q i1 ≤ p i1 := by
    by_contra hcon
    push Not at hcon
    have hne : M.Nonempty := card_pos.mp (by omega)
    have := sum_lt_sum_of_nonempty hne hcon
    linarith
  obtain ⟨i2, hne2, hM2⟩ := pair_of_card_two hM hi1M
  have p12 : p i1 + p i2 = 1 - r := by rw [hM2, sum_pair hne2.symm] at pM; exact pM
  have q12 : q i1 + q i2 = 1 - r := by rw [hM2, sum_pair hne2.symm] at qM; exact qM
  have hq1 : 1 - 2 * r ≤ q i1 := by linarith [(hq.1 i2).2]
  have hpr : p i1 ≤ r := (hp.1 i1).2
  have hi1 : i1 ∉ ({i0, j0} : Finset (Fin 4)) := mem_compl.mp hi1M
  have hi2M : i2 ∈ M := by rw [hM2]; simp
  have hi2 : i2 ∉ ({i0, j0} : Finset (Fin 4)) := mem_compl.mp hi2M
  simp only [mem_insert, mem_singleton, not_or] at hi1 hi2
  -- the key rate: (p i1 c, q i1 c), with s/r ≤ q i1 / p i1 ≤ 1
  have hu : 0 < p i1 * c := mul_pos (by linarith) hc
  have hv : 0 < q i1 * c := mul_pos (by linarith) hc
  have key : p i1 = r ∧ q i1 = 1 - 2 * r := by
    rcases mid_card h1 h2 hp hq hu hv (by nlinarith) (by nlinarith) (h i1) with ⟨hcard, sp, sq⟩ | ⟨-, he⟩
    · set A := pos p q (p i1 * c) (q i1 * c)
      have hiA : i0 ∈ A := mem_pos.mpr (by rw [hi0.1, hi0.2]; nlinarith)
      have hjA : j0 ∉ A := fun h => by have := mem_pos.mp h; rw [hj0.1, hj0.2] at this; nlinarith
      have hpA := eq_of_sum_le (A := A) (f := p) (c := r) (fun i _ => (hp.1 i).2)
        (by rw [sp, hcard]; push_cast; ring)
      obtain ⟨y, hy, hA⟩ := pair_of_card_two hcard hiA
      by_cases h1A : i1 ∈ A
      · have hy1 : i1 = y := by
          rw [hA] at h1A; simp only [mem_insert, mem_singleton] at h1A
          exact h1A.resolve_left hi1.1
        subst hy1
        refine ⟨hpA i1 h1A, ?_⟩
        rw [hA, sum_pair hy.symm, hi0.2] at sq; linarith
      · exfalso
        have hcc : Aᶜ.card = 2 := by rw [card_compl, Fintype.card_fin, hcard]
        have qc := compl_sum hq.2 A
        rw [sq] at qc
        have hqAc := eq_of_sum_le (A := Aᶜ) (f := q) (c := r) (fun i _ => (hq.1 i).2)
          (by rw [qc, hcc]; push_cast; ring)
        have q1 := hqAc i1 (mem_compl.mpr h1A)
        have p1 : p i1 = r := by linarith
        have hyA : y ∈ A := by rw [hA]; simp
        have hy2 : y = i2 := by
          have : y ∈ M := mem_compl.mpr (by
            simp only [mem_insert, mem_singleton, not_or]
            exact ⟨hy, fun e => hjA (e ▸ hyA)⟩)
          rw [hM2] at this; simp only [mem_insert, mem_singleton] at this
          exact this.resolve_left fun e => h1A (e ▸ hyA)
        have := hpA y hyA
        rw [hy2] at this
        linarith
    · constructor <;> nlinarith
  refine ⟨i0, i1, i2, j0, Ne.symm hi1.1, Ne.symm hi2.1, hij, hne2.symm, hi1.2, hi2.2, hi0.1, hi0.2, key.1, key.2,
    by linarith [key.1], by linarith [key.2], hj0.1, hj0.2⟩

end Pin

/-! ### The equality cases -/

section Main

variable {r : ℝ}

/-- **Equality for `n ≥ 3`.** Only the staircase pair, faces relabelled, reaches the least overlap. -/
theorem equality_ge3 (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {p q : Fin 4 → ℝ} (hp : Adm r p) (hq : Adm r q)
    (n : ℕ) (hn : 3 ≤ n) (h : overlap (fun _ : Fin n => (p, q)) = overlap (S 4 r n)) : Relabel r p q := by
  have hr : (0 : ℝ) ≤ r := by linarith
  have hk : 1 ≤ (4 : ℕ) * r := by push_cast; linarith
  have hs : 0 < 1 - 2 * r := by linarith
  have hr0 : 0 < r := by linarith
  obtain ⟨-, -, a1, b1, a2, b2, -, -⟩ := star4 h1 h2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  have t := tight_rates hr hk hp hq m h
  have gap := rate_gap h1 h2 hm
  obtain ⟨i0, hi0⟩ : ∃ i, p i = r ∧ q i = 0 := by
    have e := t (fun _ => 2)
    rw [(P_const m 4 r 2).1, (P_const m 4 r 2).2, a2, b2] at e
    exact face_r0 h1 h2 hp hq (pow_pos hs m) (pow_pos hr0 m) (by linarith) e
  obtain ⟨j0, hj0⟩ : ∃ j, p j = 0 ∧ q j = r := by
    have e := t (fun _ => 1)
    rw [(P_const m 4 r 1).1, (P_const m 4 r 1).2, a1, b1] at e
    exact face_0r h1 h2 hp hq (pow_pos hr0 m) (pow_pos hs m) (by linarith) e
  have hc : ∀ j : ℕ, 0 < (r * (1 - 2 * r)) ^ j := fun j => pow_pos (mul_pos hr0 hs) j
  rcases Nat.even_or_odd m with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have e := t (fun i => if i.val < j then 1 else 2)
    rw [(P_balanced h1 h2 j).1, (P_balanced h1 h2 j).2] at e
    exact pin_odd h1 h2 hp hq hi0 hj0 (hc j) e
  · obtain ⟨l, hl⟩ : ∃ l, 2 * j + 1 + 1 = l + l + 2 := ⟨j, by ring⟩
    have h' : overlap (fun _ : Fin (j + j + 2) => (p, q)) = overlap (S 4 r (j + j + 2)) := by
      have e : 2 * j + 1 + 1 = j + j + 2 := by ring
      rw [e] at h; exact h
    refine pin_even h1 h2 hp hq hi0 hj0 (hc j) fun i => ?_
    have e := tight_rates2 hr hk hp hq (j + j) h' i (fun i => if i.val < j then 1 else 2)
    rw [(P_balanced h1 h2 j).1, (P_balanced h1 h2 j).2] at e
    exact e

/-- **Converse.** Every relabelling of the staircase pair reaches the least overlap, for every `n`. -/
theorem relabel_attains (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {p q : Fin 4 → ℝ} (hrel : Relabel r p q) (n : ℕ) :
    overlap (fun _ : Fin n => (p, q)) = overlap (S 4 r n) := by
  have hr : (0 : ℝ) ≤ r := by linarith
  have hk : 1 ≤ (4 : ℕ) * r := by push_cast; linarith
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, pa, qa, pb, qb, pc, qc, pd, qd⟩ := hrel
  obtain ⟨a0, b0, a1, b1, a2, b2, a3, b3⟩ := star4 h1 h2
  have huniv : (univ : Finset (Fin 4)) = {a, b, c, d} := by
    refine (eq_of_subset_of_card_le (subset_univ _) ?_).symm
    rw [card_univ, Fintype.card_fin, card_insert_of_notMem (by simp [hab, hac, had]),
      card_insert_of_notMem (by simp [hbc, hbd]), card_pair hcd]
  have hg : ∀ u v, g p q u v = g (pstar 4 r) (qstar 4 r) u v := by
    intro u v
    rw [g, huniv, sum_insert (by simp [hab, hac, had]), sum_insert (by simp [hbc, hbd]), sum_pair hcd, g,
      Fin.sum_univ_four, pa, qa, pb, qb, pc, qc, pd, qd, a0, b0, a1, b1, a2, b2, a3, b3]
    ring
  have hadm : Adm r p ∧ Adm r q := by
    have hall : ∀ i, i = a ∨ i = b ∨ i = c ∨ i = d := fun i => by
      have := mem_univ i; rw [huniv] at this; simpa using this
    refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun i => ?_, ?_⟩⟩
    · rcases hall i with rfl | rfl | rfl | rfl <;> constructor <;> linarith
    · rw [huniv, sum_insert (by simp [hab, hac, had]), sum_insert (by simp [hbc, hbd]), sum_pair hcd]; linarith
    · rcases hall i with rfl | rfl | rfl | rfl <;> constructor <;> linarith
    · rw [huniv, sum_insert (by simp [hab, hac, had]), sum_insert (by simp [hbc, hbd]), sum_pair hcd]; linarith
  refine le_antisymm ?_ (overlap_ge hr hk n _ fun _ => hadm)
  exact overlap_ge_of_dominant hadm.1 hadm.2
    (fun p' q' hp' hq' u v hu hv => (hg u v).symm ▸ dominates hr hk hp' hq' hu hv) n _
    fun _ => ⟨pstar_adm hr hk, qstar_adm hr hk⟩

theorem overlap_one {k : ℕ} (p q : Fin k → ℝ) : overlap (fun _ : Fin 1 => (p, q)) = ∑ i, min (p i) (q i) :=
  Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin k)) _ _ fun w => by simp [P, Q]

/-- **Equality for `n = 1`:** exactly the pairs with `max(pᵢ, qᵢ) = r` on every face. -/
theorem equality_one (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {p q : Fin 4 → ℝ} (hp : Adm r p) (hq : Adm r q) :
    overlap (fun _ : Fin 1 => (p, q)) = overlap (S 4 r 1) ↔ ∀ i, max (p i) (q i) = r := by
  obtain ⟨a0, b0, a1, b1, a2, b2, a3, b3⟩ := star4 h1 h2
  have hmin : ∀ x y : ℝ, min x y = x + y - max x y := fun x y => by
    rcases le_total x y with h | h <;> simp [h]
  have hsum : ∑ i, min (p i) (q i) = 2 - ∑ i, max (p i) (q i) := by
    simp only [hmin, sum_sub_distrib, sum_add_distrib, hp.2, hq.2]; ring
  have hstar : overlap (S 4 r 1) = 2 - 4 * r := by
    rw [show S 4 r 1 = fun _ : Fin 1 => (pstar 4 r, qstar 4 r) from rfl, overlap_one, Fin.sum_univ_four,
      a0, b0, a1, b1, a2, b2, a3, b3, min_eq_right (by linarith), min_eq_right (by linarith),
      min_eq_left (by linarith), min_eq_left (by linarith)]
    ring
  rw [overlap_one, hsum, hstar]
  constructor
  · intro h
    have hs : ∑ i ∈ (univ : Finset (Fin 4)), max (p i) (q i) = (univ : Finset (Fin 4)).card * r := by
      simp only [card_univ, Fintype.card_fin]; push_cast; linarith
    exact fun i => eq_of_sum_le (fun i _ => max_le (hp.1 i).2 (hq.1 i).2) hs i (mem_univ i)
  · intro h
    simp only [h, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring

end Main

/-! ### `n = 2`: a one-parameter family -/

section Two

variable {r : ℝ}

/-- `p = (r, r, x, s - x)`, `q = (0, s, r, r)`; `x = s` is the staircase pair. -/
def pF (r x : ℝ) : Fin 4 → ℝ := ![r, r, x, 1 - 2 * r - x]
def qF (r : ℝ) : Fin 4 → ℝ := ![0, 1 - 2 * r, r, r]

theorem family_adm (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {x : ℝ} (hx0 : 0 ≤ x) (hxs : x ≤ 1 - 2 * r) :
    Adm r (pF r x) ∧ Adm r (qF r) := by
  refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun i => ?_, ?_⟩⟩
  · fin_cases i <;> simp [pF] <;> (try constructor) <;> linarith
  · simp [pF, Fin.sum_univ_four]; ring
  · fin_cases i <;> simp [qF] <;> (try constructor) <;> linarith
  · simp [qF, Fin.sum_univ_four]; ring

theorem G_one {k : ℕ} (h : (Fin k → ℝ) × (Fin k → ℝ)) (u v : ℝ) :
    G (fun _ : Fin 1 => h) u v = g h.1 h.2 u v :=
  Fintype.sum_equiv (Equiv.funUnique (Fin 1) (Fin k)) _ _ fun w => by simp [P, Q]

theorem G_two {k : ℕ} (p q : Fin k → ℝ) (u v : ℝ) :
    G (fun _ : Fin 2 => (p, q)) u v = ∑ i, g p q (u * p i) (v * q i) := by
  rw [G_succ]; exact sum_congr rfl fun i _ => G_one (p, q) _ _

/-- One face at a time: `g(pF, qF)` at the rate pair of each face of `pF`. -/
theorem family_g (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {x : ℝ} (hx0 : 0 ≤ x) (hxs : x ≤ 1 - 2 * r) :
    g (pF r x) (qF r) r 0 = r ∧ g (pF r x) (qF r) r (1 - 2 * r) = 2 * r ^ 2 - (1 - 2 * r) ^ 2 ∧
      g (pF r x) (qF r) x r = x * r ∧ g (pF r x) (qF r) (1 - 2 * r - x) r = (1 - 2 * r - x) * r := by
  have hy : (0 : ℝ) ≤ 1 - 2 * r - x := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [g, Fin.sum_univ_four, pF, qF, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    have t0 : (0 : ℝ) ≤ r * r - 0 * 0 := by nlinarith [mul_nonneg hx0 hy, mul_nonneg hx0 hx0, mul_nonneg hy hy, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ r)]
    have t1 : (0 : ℝ) ≤ r * r - 0 * (1 - 2 * r) := by nlinarith [mul_nonneg hx0 hy, mul_nonneg hx0 hx0, mul_nonneg hy hy, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ r)]
    have t2 : (0 : ℝ) ≤ r * x - 0 * r := by nlinarith [mul_nonneg hx0 hy, mul_nonneg hx0 hx0, mul_nonneg hy hy, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ r)]
    have t3 : (0 : ℝ) ≤ r * (1 - 2 * r - x) - 0 * r := by nlinarith [mul_nonneg hx0 hy, mul_nonneg hx0 hx0, mul_nonneg hy hy, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ r)]
    rw [max_eq_left t0, max_eq_left t1, max_eq_left t2, max_eq_left t3]; ring
  · simp only [g, Fin.sum_univ_four, pF, qF, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    have t0 : (0 : ℝ) ≤ r * r - (1 - 2 * r) * 0 := by nlinarith [mul_nonneg hx0 hy, mul_nonneg hx0 hx0, mul_nonneg hy hy, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ r)]
    have t1 : (0 : ℝ) ≤ r * r - (1 - 2 * r) * (1 - 2 * r) := by nlinarith [mul_nonneg hx0 hy, mul_nonneg hx0 hx0, mul_nonneg hy hy, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ r)]
    have t2 : r * x - (1 - 2 * r) * r ≤ 0 := by nlinarith [mul_nonneg hx0 hy, mul_nonneg hx0 hx0, mul_nonneg hy hy, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ r)]
    have t3 : r * (1 - 2 * r - x) - (1 - 2 * r) * r ≤ 0 := by nlinarith [mul_nonneg hx0 hy, mul_nonneg hx0 hx0, mul_nonneg hy hy, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ r)]
    rw [max_eq_left t0, max_eq_left t1, max_eq_right t2, max_eq_right t3]; ring
  · simp only [g, Fin.sum_univ_four, pF, qF, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    have t0 : (0 : ℝ) ≤ x * r - r * 0 := by nlinarith [mul_nonneg hx0 hy, mul_nonneg hx0 hx0, mul_nonneg hy hy, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ r)]
    have t1 : x * r - r * (1 - 2 * r) ≤ 0 := by nlinarith [mul_nonneg hx0 hy, mul_nonneg hx0 hx0, mul_nonneg hy hy, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ r)]
    have t2 : x * x - r * r ≤ 0 := by nlinarith [mul_nonneg hx0 hy, mul_nonneg hx0 hx0, mul_nonneg hy hy, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ r)]
    have t3 : x * (1 - 2 * r - x) - r * r ≤ 0 := by nlinarith [mul_nonneg hx0 hy, mul_nonneg hx0 hx0, mul_nonneg hy hy, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ r)]
    rw [max_eq_left t0, max_eq_right t1, max_eq_right t2, max_eq_right t3]; ring
  · simp only [g, Fin.sum_univ_four, pF, qF, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    have t0 : (0 : ℝ) ≤ (1 - 2 * r - x) * r - r * 0 := by nlinarith [mul_nonneg hx0 hy, mul_nonneg hx0 hx0, mul_nonneg hy hy, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ r)]
    have t1 : (1 - 2 * r - x) * r - r * (1 - 2 * r) ≤ 0 := by nlinarith [mul_nonneg hx0 hy, mul_nonneg hx0 hx0, mul_nonneg hy hy, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ r)]
    have t2 : (1 - 2 * r - x) * x - r * r ≤ 0 := by nlinarith [mul_nonneg hx0 hy, mul_nonneg hx0 hx0, mul_nonneg hy hy, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ r)]
    have t3 : (1 - 2 * r - x) * (1 - 2 * r - x) - r * r ≤ 0 := by nlinarith [mul_nonneg hx0 hy, mul_nonneg hx0 hx0, mul_nonneg hy hy, mul_nonneg hx0 (by linarith : (0 : ℝ) ≤ r)]
    rw [max_eq_left t0, max_eq_right t1, max_eq_right t2, max_eq_right t3]; ring

/-- The excess of two rolls of the family does not depend on `x`. -/
theorem family_G (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {x : ℝ} (hx0 : 0 ≤ x) (hxs : x ≤ 1 - 2 * r) :
    G (fun _ : Fin 2 => (pF r x, qF r)) 1 1 = r + 2 * r ^ 2 - (1 - 2 * r) ^ 2 + (1 - 2 * r) * r := by
  obtain ⟨e0, e1, e2, e3⟩ := family_g h1 h2 hx0 hxs
  rw [G_two, Fin.sum_univ_four]
  simp only [one_mul, pF, qF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  simp only [pF, qF] at e0 e1 e2 e3
  rw [e0, e1, e2, e3]; ring

/-- **Equality for `n = 2`:** every member of the family reaches the least overlap. -/
theorem equality_two_family (h1 : 1 / 3 < r) (h2 : r < 1 / 2) {x : ℝ} (hx0 : 0 ≤ x) (hxs : x ≤ 1 - 2 * r) :
    overlap (fun _ : Fin 2 => (pF r x, qF r)) = overlap (S 4 r 2) := by
  obtain ⟨a0, b0, a1, b1, a2, b2, a3, b3⟩ := star4 h1 h2
  have hps : pstar 4 r = pF r (1 - 2 * r) := by
    funext i; fin_cases i <;> simp [pF, a0, a1, a2, a3]
  have hqs : qstar 4 r = qF r := by
    funext i; fin_cases i <;> simp [qF, b0, b1, b2, b3]
  have hA := family_adm h1 h2 hx0 hxs
  have hS := family_adm h1 h2 (by linarith : (0 : ℝ) ≤ 1 - 2 * r) le_rfl
  rw [show S 4 r 2 = fun _ : Fin 2 => (pF r (1 - 2 * r), qF r) by rw [← hps, ← hqs],
    overlap_eq (fun _ => hA.1.2), overlap_eq (fun _ => hS.1.2), family_G h1 h2 hx0 hxs,
    family_G h1 h2 (by linarith) le_rfl]

end Two

end CappedDice
