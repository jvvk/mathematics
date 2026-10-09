import LeanProofs.QNarayana.Words

/-!
# MO 501839, Step 3: fixed points of the involution ↔ mirror-symmetric Motzkin words

A fixed point (shape `F`, Words.lean) has blocks `uu, dd, aa, bb`, and `ab` at height 0, then possibly one
level letter. Halving the blocks (`ab ↦ u`) gives a path prefix `half w` that stays at
height `≥ 0`; `ψ w = half w ++ tl w ++ mirror (half w)` is mirror-symmetric. The `u` letters that came from `ab`
are the last departures from each level, recovered by `minRel` (the running minimum of the rest).
-/

namespace QNarayana

open L

/-! ### Heights -/

def sΔ : List L → ℤ
  | [] => 0
  | x :: w => Δ x + sΔ w

/-- From height `h` the path never goes below 0. -/
def pre : ℤ → List L → Bool
  | _, [] => true
  | h, x :: w => decide (0 ≤ h + Δ x) && pre (h + Δ x) w

def minRel : List L → ℤ
  | [] => 0
  | x :: w => min 0 (Δ x + minRel w)

lemma okTo_iff : ∀ (w : List L) (h e : ℤ), okTo h e w = (pre h w && (h + sΔ w == e))
  | [], h, e => by simp [okTo, pre, sΔ]
  | x :: w, h, e => by
    simp only [okTo, pre, sΔ, okTo_iff w, Bool.and_assoc]
    congr 3; simp [add_assoc]

lemma sΔ_append (p q : List L) : sΔ (p ++ q) = sΔ p + sΔ q := by
  induction p with
  | nil => simp [sΔ]
  | cons x p ih => simp [sΔ, ih]; ring

lemma pre_append : ∀ (p q : List L) (h : ℤ), pre h (p ++ q) = (pre h p && pre (h + sΔ p) q)
  | [], q, h => by simp [pre, sΔ]
  | x :: p, q, h => by
    simp only [List.cons_append, pre, sΔ, pre_append p q, Bool.and_assoc, add_assoc]

lemma minRel_nonpos : ∀ w : List L, minRel w ≤ 0
  | [] => le_rfl
  | _ :: _ => min_le_left _ _

lemma pre_iff : ∀ (w : List L) (h : ℤ), 0 ≤ h → (pre h w = true ↔ 0 ≤ h + minRel w)
  | [], h, h0 => by simp [pre, minRel, h0]
  | x :: w, h, h0 => by
    have := minRel_nonpos w
    simp only [pre, Bool.and_eq_true, decide_eq_true_eq, minRel]
    constructor
    · rintro ⟨h1, h2⟩
      have := (pre_iff w _ h1).1 h2
      rcases min_cases 0 (Δ x + minRel w) with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> omega
    · intro hm
      have h1 : 0 ≤ h + (Δ x + minRel w) := le_trans hm (by simp [min_le_right])
      exact ⟨by omega, (pre_iff w _ (by omega)).2 (by omega)⟩

lemma pre_fin : ∀ (w : List L) (h : ℤ), 0 ≤ h → pre h w = true → 0 ≤ h + sΔ w
  | [], h, h0, _ => by simp [sΔ, h0]
  | x :: w, h, _, hw => by
    simp only [pre, Bool.and_eq_true, decide_eq_true_eq] at hw
    have := pre_fin w _ hw.1 hw.2
    simp only [sΔ]; omega

/-! ### Mirror -/

lemma mirror_append (p q : List L) : mirror (p ++ q) = mirror q ++ mirror p := by
  simp [mirror]

lemma sw_sw (x : L) : sw (sw x) = x := by cases x <;> rfl

lemma mirror_mirror (p : List L) : mirror (mirror p) = p := by
  simp [mirror, List.map_reverse, List.map_map, Function.comp_def, sw_sw]

lemma mirror_cons (x : L) (p : List L) : mirror (x :: p) = mirror p ++ [sw x] := by
  simp [mirror]

lemma length_mirror (p : List L) : (mirror p).length = p.length := by simp [mirror]

lemma Δ_sw (x : L) : Δ (sw x) = - Δ x := by cases x <;> simp [sw, Δ]

lemma w2_sw (x : L) : w2 (sw x) = w2 x := by cases x <;> rfl

lemma wt2_append : ∀ p q : List L, wt2 (p ++ q) = wt2 p + wt2 q
  | [], q => by simp [wt2]
  | x :: p, q => by simp [wt2, wt2_append p q]; ring

lemma wt2_mirror : ∀ p : List L, wt2 (mirror p) = wt2 p
  | [] => rfl
  | x :: p => by rw [mirror_cons, wt2_append, wt2_mirror p]; simp [wt2, w2_sw]; ring

lemma sΔ_mirror : ∀ p : List L, sΔ (mirror p) = - sΔ p
  | [] => rfl
  | x :: p => by rw [mirror_cons, sΔ_append, sΔ_mirror p]; simp [sΔ, Δ_sw]

/-- The mirror image of a path that stays `≥ 0` from `h` walks back down from its end to `h`. -/
lemma okTo_mirror : ∀ (p : List L) (h : ℤ), 0 ≤ h → pre h p = true → okTo (h + sΔ p) h (mirror p) = true
  | [], h, _, _ => by simp [mirror, okTo, sΔ]
  | x :: p, h, h0, hp => by
    simp only [pre, Bool.and_eq_true, decide_eq_true_eq] at hp
    have ih := okTo_mirror p _ hp.1 hp.2
    rw [mirror_cons, okTo_iff, pre_append, sΔ_append, sΔ_mirror]
    rw [okTo_iff] at ih
    simp only [Bool.and_eq_true, beq_iff_eq] at ih
    simp only [sΔ, pre, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Δ_sw, Bool.and_true]
    refine ⟨⟨by simpa [add_assoc] using ih.1, ?_⟩, by ring⟩
    have : h + Δ x + sΔ p + -sΔ p = h + Δ x := by ring
    rw [show h + (Δ x + sΔ p) + -sΔ p = h + Δ x by ring]; omega

/-! ### Halving -/

def cv : L → L → L
  | u, u => u
  | d, d => d
  | b, b => b
  | a, b => u
  | _, _ => a

def half : List L → List L
  | [] => []
  | [_] => []
  | x :: y :: w => cv x y :: half w

def tl : List L → List L
  | [] => []
  | [x] => [x]
  | _ :: _ :: w => tl w

def ψ (w : List L) : List L := half w ++ tl w ++ mirror (half w)

/-- Undo one halved letter, given the rest `p` of the prefix. -/
def ub (x : L) (p : List L) : L × L :=
  match x with
  | u => if minRel p = 0 then (a, b) else (u, u)
  | d => (d, d)
  | a => (a, a)
  | b => (b, b)

def unhalf : List L → List L
  | [] => []
  | x :: p => (ub x p).1 :: (ub x p).2 :: unhalf p

def ψ' (s : List L) : List L :=
  unhalf (s.take (s.length / 2)) ++ (s.drop (s.length / 2)).take (s.length % 2)

def Sym (m j : ℕ) : Finset (List L) := (Mot m j).filter (fun w => mirror w = w)

/-- `tl` is empty or one level letter. -/
def lvTail (t : List L) : Prop := t = [] ∨ ∃ x, t = [x] ∧ lv x = true

lemma lvTail_tl : ∀ (w : List L) (h : ℤ), F h w = true → lvTail (tl w)
  | [], _, _ => Or.inl rfl
  | [x], h, hF => by
    simp only [F, Bool.and_eq_true] at hF; exact Or.inr ⟨x, rfl, hF.1⟩
  | x :: y :: w, h, hF => by
    simp only [F, Bool.and_eq_true] at hF; exact lvTail_tl w _ hF.2

lemma length_half_tl : ∀ w : List L, 2 * (half w).length + (tl w).length = w.length ∧ (tl w).length ≤ 1
  | [] => by simp [half, tl]
  | [_] => by simp [half, tl]
  | x :: y :: w => by
    have := length_half_tl w
    simp only [half, tl, List.length_cons]; omega

lemma pre_half : ∀ (w : List L) (h c : ℤ) (t : ℕ), h = 2 * t → 0 ≤ c → F h w = true →
    pre (t + c) (half w) = true
  | [], _, _, _, _, _, _ => rfl
  | [_], _, _, _, _, _, _ => rfl
  | x :: y :: w, h, c, t, ht, hc, hF => by
    simp only [F, Bool.and_eq_true] at hF
    obtain ⟨hb, hw⟩ := hF
    simp only [half, pre, Bool.and_eq_true, decide_eq_true_eq]
    cases x <;> cases y <;> simp [blockOK] at hb <;> simp only [cv, Δ] at hw ⊢
    · exact ⟨by omega, by
        have := pre_half w _ c (t + 1) (by push_cast; omega) hc hw
        rwa [show (↑(t + 1) : ℤ) + c = ↑t + c + 1 by push_cast; ring] at this⟩
    · exact ⟨by omega, by
        have := pre_half w _ c (t - 1) (by omega) hc hw
        rwa [show (↑(t - 1) : ℤ) + c = ↑t + c + -1 by omega] at this⟩
    · exact ⟨by omega, by simpa using pre_half w _ c t (by omega) hc hw⟩
    · exact ⟨by omega, by
        have := pre_half w _ (c + 1) t (by omega) (by omega) hw
        rwa [show (↑t : ℤ) + (c + 1) = ↑t + c + 1 by ring] at this⟩
    · exact ⟨by omega, by simpa using pre_half w _ c t (by omega) hc hw⟩

lemma minRel_half : ∀ (w : List L) (h : ℤ) (t : ℕ), h = 2 * t → F h w = true → minRel (half w) = -t
  | [], h, t, ht, hF => by simp [F] at hF; simp [half, minRel]; omega
  | [x], h, t, ht, hF => by simp [F] at hF; simp [half, minRel]; omega
  | x :: y :: w, h, t, ht, hF => by
    simp only [F, Bool.and_eq_true] at hF
    obtain ⟨hb, hw⟩ := hF
    simp only [half, minRel]
    cases x <;> cases y <;> simp [blockOK] at hb <;> simp only [cv, Δ] at hw ⊢
    · rw [minRel_half w _ (t + 1) (by push_cast; omega) hw]; push_cast; omega
    · rw [minRel_half w _ (t - 1) (by omega) hw]; omega
    · rw [minRel_half w _ t (by omega) hw]; omega
    · rw [minRel_half w _ 0 (by omega) hw]; omega
    · rw [minRel_half w _ t (by omega) hw]; omega

lemma unhalf_half : ∀ (w : List L) (h : ℤ) (t : ℕ), h = 2 * t → F h w = true → unhalf (half w) ++ tl w = w
  | [], _, _, _, _ => rfl
  | [_], _, _, _, _ => rfl
  | x :: y :: w, h, t, ht, hF => by
    simp only [F, Bool.and_eq_true] at hF
    obtain ⟨hb, hw⟩ := hF
    simp only [half, tl, unhalf, List.cons_append]
    cases x <;> cases y <;> simp [blockOK] at hb <;> simp only [cv, Δ, ub] at hw ⊢
    · have hne : (-1 + -(↑t : ℤ)) ≠ 0 := by omega
      rw [minRel_half w _ (t + 1) (by push_cast; omega) hw, unhalf_half w _ (t + 1) (by push_cast; omega) hw]
      simp [hne]
    · rw [unhalf_half w _ (t - 1) (by omega) hw]
    · rw [unhalf_half w _ t (by omega) hw]
    · rw [minRel_half w _ 0 (by omega) hw, unhalf_half w _ 0 (by omega) hw]; simp
    · rw [unhalf_half w _ t (by omega) hw]

lemma wt2_F : ∀ (w : List L) (h : ℤ), F h w = true → wt2 w = 2 * wt2 (half w) + wt2 (tl w)
  | [], _, _ => rfl
  | [_], _, _ => by simp [half, tl, wt2]
  | x :: y :: w, h, hF => by
    simp only [F, Bool.and_eq_true] at hF
    have := wt2_F w _ hF.2
    cases x <;> cases y <;> simp [blockOK] at hF <;> simp [half, tl, wt2, cv, w2] at this ⊢ <;> omega

/-! ### The inverse direction -/

lemma half_unhalf_append : ∀ (p t : List L), t.length ≤ 1 → half (unhalf p ++ t) = p ∧ tl (unhalf p ++ t) = t
  | [], t, ht => by
    match t, ht with
    | [], _ => exact ⟨rfl, rfl⟩
    | [_], _ => exact ⟨rfl, rfl⟩
  | x :: p, t, ht => by
    obtain ⟨h1, h2⟩ := half_unhalf_append p t ht
    simp only [unhalf, List.cons_append, half, tl, h1, h2, and_true]
    cases x <;> simp only [ub] <;> (try split_ifs) <;> rfl

lemma length_unhalf : ∀ p : List L, (unhalf p).length = 2 * p.length
  | [] => rfl
  | x :: p => by simp [unhalf, length_unhalf p]; ring

lemma wt2_unhalf : ∀ p : List L, wt2 (unhalf p) = 2 * wt2 p
  | [] => rfl
  | x :: p => by
    have := wt2_unhalf p
    cases x <;> simp only [unhalf, ub, wt2] <;> (try split_ifs) <;> simp [w2, this] <;> ring

lemma F_unhalf : ∀ (p t : List L) (h : ℤ), lvTail t → h = 2 * (- minRel p) → F h (unhalf p ++ t) = true
  | [], t, h, ht, hh => by
    simp only [minRel, neg_zero, mul_zero] at hh
    subst hh
    rcases ht with rfl | ⟨x, rfl, hx⟩
    · rfl
    · simp [unhalf, F, hx]
  | x :: p, t, h, ht, hh => by
    have hn := minRel_nonpos p
    simp only [unhalf, List.cons_append, F, Bool.and_eq_true]
    simp only [minRel] at hh
    cases x
    · simp only [Δ] at hh
      by_cases h0 : minRel p = 0
      · simp only [ub, h0, ite_true, blockOK, Δ]
        rw [h0] at hh
        have : h = 0 := by simpa using hh
        subst this
        exact ⟨by simp, F_unhalf p t _ ht (by simp [h0])⟩
      · simp only [ub, h0, ite_false, blockOK, Δ]
        have : min 0 (1 + minRel p) = 1 + minRel p := min_eq_right (by omega)
        rw [this] at hh
        exact ⟨by simp only [decide_eq_true_eq]; omega, F_unhalf p t _ ht (by omega)⟩
    · simp only [Δ] at hh
      simp only [ub, blockOK, Δ]
      have : min 0 (-1 + minRel p) = -1 + minRel p := min_eq_right (by omega)
      rw [this] at hh
      exact ⟨by simp only [decide_eq_true_eq]; omega, F_unhalf p t _ ht (by omega)⟩
    · simp only [Δ] at hh
      simp only [ub, blockOK, Δ]
      have : min 0 (0 + minRel p) = minRel p := by simp [hn]
      rw [this] at hh
      exact ⟨by simp only [decide_eq_true_eq]; omega, F_unhalf p t _ ht (by omega)⟩
    · simp only [Δ] at hh
      simp only [ub, blockOK, Δ]
      have : min 0 (0 + minRel p) = minRel p := by simp [hn]
      rw [this] at hh
      exact ⟨by simp only [decide_eq_true_eq]; omega, F_unhalf p t _ ht (by omega)⟩

lemma lv_iff_sw (x : L) : sw x = x ↔ lv x = true := by cases x <;> simp [sw, lv]

lemma mirror_lvTail {t : List L} (ht : lvTail t) : mirror t = t := by
  rcases ht with rfl | ⟨x, rfl, hx⟩
  · rfl
  · simp [mirror, (lv_iff_sw x).2 hx]

/-- A mirror-symmetric word is `p ++ t ++ mirror p` with `t` empty or one level letter. -/
theorem sym_decomp : ∀ (n : ℕ) (s : List L), s.length = n → mirror s = s →
    ∃ p t, lvTail t ∧ s = p ++ t ++ mirror p
  | 0, s, hl, _ => ⟨[], [], Or.inl rfl, by simp [mirror]; simpa using hl⟩
  | 1, s, hl, hs => by
    match s, hl with
    | [x], _ =>
      have : sw x = x := by simpa [mirror] using hs
      exact ⟨[], [x], Or.inr ⟨x, rfl, (lv_iff_sw x).1 this⟩, by simp [mirror]⟩
  | n + 2, s, hl, hs => by
    match s, hl with
    | x :: s', hl =>
      have hne : s' ≠ [] := by rintro rfl; simp at hl
      obtain ⟨r, y, rfl⟩ : ∃ r y, s' = r ++ [y] := ⟨s'.dropLast, s'.getLast hne, (List.dropLast_append_getLast hne).symm⟩
      have hs' : mirror (x :: (r ++ [y])) = sw y :: (mirror r ++ [sw x]) := by
        simp [mirror]
      rw [hs'] at hs
      simp only [List.cons.injEq] at hs
      obtain ⟨hxy, hr⟩ := hs
      have hr' : mirror r = r := List.append_cancel_right (by rw [hr]; simp [← hxy, sw_sw])
      have hy : y = sw x := by rw [← hxy, sw_sw]
      obtain ⟨p, t, ht, rfl⟩ := sym_decomp n r (by simp at hl; omega) hr'
      refine ⟨x :: p, t, ht, ?_⟩
      rw [mirror_cons, hy]; simp

/-- Height check of `p ++ t ++ mirror p`. -/
lemma okTo_sym (p t : List L) (ht : lvTail t) (hp : pre 0 p = true) : okTo 0 0 (p ++ t ++ mirror p) = true := by
  have hf := pre_fin p 0 le_rfl hp
  have hm := okTo_mirror p 0 le_rfl hp
  rw [okTo_iff] at hm ⊢
  simp only [Bool.and_eq_true, beq_iff_eq] at hm ⊢
  have htΔ : sΔ t = 0 ∧ pre (0 + sΔ p) t = true := by
    rcases ht with rfl | ⟨x, rfl, hx⟩
    · simp [sΔ, pre]
    · cases x <;> simp_all [sΔ, pre, lv, Δ]
  rw [pre_append, pre_append, sΔ_append, sΔ_append, sΔ_mirror, htΔ.1]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨hp, htΔ.2⟩, ?_⟩, by rw [sΔ_append, htΔ.1]; ring⟩
  simpa using hm.1

theorem card_Fix_eq_card_Sym (m j : ℕ) : (Fix m j).card = (Sym m j).card := by
  refine Finset.card_bij' (fun w _ => ψ w) (fun s _ => ψ' s) ?_ ?_ ?_ ?_
  · -- ψ maps fixed points to symmetric words
    intro w hw
    obtain ⟨hl, hF, hwt⟩ := mem_Fix.1 hw
    have ht := lvTail_tl w 0 hF
    have hp : pre 0 (half w) = true := by simpa using pre_half w 0 0 0 rfl le_rfl hF
    simp only [Sym, Mot, Finset.mem_filter, mem_words]
    obtain ⟨hlen, -⟩ := length_half_tl w
    refine ⟨⟨?_, okTo_sym _ _ ht hp, ?_⟩, ?_⟩
    · simp only [ψ, List.length_append, length_mirror]; omega
    · simp only [ψ, wt2_append, wt2_mirror]; rw [← hwt, wt2_F w 0 hF]; ring
    · simp only [ψ, mirror_append, mirror_mirror, mirror_lvTail ht, List.append_assoc]
  · -- ψ' maps symmetric words to fixed points
    intro s hs
    simp only [Sym, Mot, Finset.mem_filter, mem_words] at hs
    obtain ⟨⟨hl, hok, hwt⟩, hsym⟩ := hs
    obtain ⟨p, t, ht, rfl⟩ := sym_decomp _ s rfl hsym
    have htl : t.length ≤ 1 := by rcases ht with rfl | ⟨x, rfl, -⟩ <;> simp
    have hψ' : ψ' (p ++ t ++ mirror p) = unhalf p ++ t := by
      simp only [ψ', List.length_append, length_mirror]
      have e1 : (p.length + t.length + p.length) / 2 = p.length := by omega
      have e2 : (p.length + t.length + p.length) % 2 = t.length := by omega
      rw [e1, e2, List.append_assoc, List.take_left' rfl, List.drop_left' rfl, List.take_left' rfl]
    rw [hψ']
    have hp : pre 0 p = true := by
      rw [okTo_iff, List.append_assoc, pre_append] at hok
      simp only [Bool.and_eq_true] at hok
      exact hok.1.1
    have hmin : minRel p = 0 := le_antisymm (minRel_nonpos p) (by simpa using (pre_iff p 0 le_rfl).1 hp)
    refine mem_Fix.2 ⟨?_, F_unhalf p t 0 ht (by rw [hmin]; ring), ?_⟩
    · simp only [List.length_append, length_unhalf, length_mirror] at hl ⊢; omega
    · simp only [wt2_append, wt2_unhalf, wt2_mirror] at hwt ⊢; omega
  · -- ψ' ∘ ψ = id
    intro w hw
    obtain ⟨-, hF, -⟩ := mem_Fix.1 hw
    obtain ⟨hlen, htl⟩ := length_half_tl w
    simp only [ψ, ψ', List.length_append, length_mirror]
    have e1 : ((half w).length + (tl w).length + (half w).length) / 2 = (half w).length := by omega
    have e2 : ((half w).length + (tl w).length + (half w).length) % 2 = (tl w).length := by omega
    rw [e1, e2, List.append_assoc, List.take_left' rfl, List.drop_left' rfl, List.take_left' rfl]
    exact unhalf_half w 0 0 rfl hF
  · -- ψ ∘ ψ' = id
    intro s hs
    simp only [Sym, Mot, Finset.mem_filter, mem_words] at hs
    obtain ⟨-, hsym⟩ := hs
    obtain ⟨p, t, ht, rfl⟩ := sym_decomp _ _ rfl hsym
    have htl : t.length ≤ 1 := by rcases ht with rfl | ⟨x, rfl, -⟩ <;> simp
    simp only [ψ', List.length_append, length_mirror]
    have e1 : (p.length + t.length + p.length) / 2 = p.length := by omega
    have e2 : (p.length + t.length + p.length) % 2 = t.length := by omega
    rw [e1, e2, List.append_assoc, List.take_left' rfl, List.drop_left' rfl, List.take_left' rfl]
    obtain ⟨h1, h2⟩ := half_unhalf_append p t htl
    simp only [ψ, h1, h2, List.append_assoc]

/-- Steps 2 and 3 on words: the signed count of Motzkin words equals the count of mirror-symmetric ones. -/
theorem signed_sum_eq_card_sym (m j : ℕ) : ∑ w ∈ Mot m j, sgnFrom 1 w = (Sym m j).card := by
  rw [signed_sum_eq_card_fix, card_Fix_eq_card_Sym]

end QNarayana
