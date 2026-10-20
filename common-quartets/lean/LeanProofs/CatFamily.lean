import Mathlib

/-!
An explicit family of k caterpillars on 2^k + 1 leaves with no common quartet, so h*(k) ≥ 2^k + 2 and hence
h(k) ≥ 2^k + 2 for Snir-Yuster's common-quartet number (arXiv 2602.23096 §5, construction omitted there).

Leaves are the integers -h..h, h = 2^(k-1). A caterpillar is a leaf order, given by a position map; the quartet at
positions p1 < p2 < p3 < p4 splits p1 p2 | p3 p4. Order `none` is the identity. Order `some b` (b < k-1) sends
label x to -x exactly when x ≠ 0 and bit b of |x| - 1 is 0. `disp p a b c d` says the order p splits ab | cd.

Proof: induction on k, doubling [-h, h] to [-2h, 2h] (PROOF.md): inner block, outer copy via psi, top order.
-/

namespace CatFamily

/-- Position of label x in order o. -/
def pos : Option ℕ → ℤ → ℤ
  | none, x => x
  | some b, x => if x ≠ 0 ∧ (x.natAbs - 1).testBit b = false then -x else x

/-- The order p splits the quartet as ab | cd. -/
def disp (p : ℤ → ℤ) (a b c d : ℤ) : Prop :=
  (p a < p c ∧ p a < p d ∧ p b < p c ∧ p b < p d) ∨ (p c < p a ∧ p c < p b ∧ p d < p a ∧ p d < p b)

/-- All k orders of the family split ab | cd. -/
def Common (k : ℕ) (a b c d : ℤ) : Prop :=
  disp (pos none) a b c d ∧ ∀ j < k - 1, disp (pos (some j)) a b c d

theorem pos_some (b : ℕ) (x : ℤ) :
    pos (some b) x = if x ≠ 0 ∧ (x.natAbs - 1).testBit b = false then -x else x := rfl

theorem pos_cases (o : Option ℕ) (x : ℤ) : pos o x = x ∨ pos o x = -x := by
  cases o with
  | none => exact Or.inl rfl
  | some b => rw [pos_some]; split_ifs <;> simp

/-- Each order is a bijection of [-h, h]: an involution preserving |x|. -/
theorem pos_pos (o : Option ℕ) (x : ℤ) : pos o (pos o x) = x := by
  cases o with
  | none => rfl
  | some b =>
    by_cases h : x ≠ 0 ∧ (x.natAbs - 1).testBit b = false
    · have h' : -x ≠ 0 ∧ ((-x).natAbs - 1).testBit b = false := by
        rw [Int.natAbs_neg]; exact ⟨neg_ne_zero.mpr h.1, h.2⟩
      have e1 : pos (some b) x = -x := by rw [pos_some]; exact if_pos h
      rw [e1, pos_some]; simp only [h', neg_neg]; exact if_pos ⟨h'.1, trivial⟩
    · have e1 : pos (some b) x = x := by rw [pos_some]; exact if_neg h
      rw [e1, e1]

theorem pos_natAbs (o : Option ℕ) (x : ℤ) : (pos o x).natAbs = x.natAbs := by
  rcases pos_cases o x with h | h <;> rw [h]; simp

theorem pos_zero (o : Option ℕ) : pos o 0 = 0 := by
  cases o <;> simp [pos]

/-- The top order b = k-1 reverses the inner block [-H, H] and fixes the outer leaves (H = 2^(k-1)). -/
theorem pos_top (k H : ℕ) (hH : H = 2 ^ (k - 1)) (x : ℤ) (hx : x.natAbs ≤ 2 * H) :
    (x.natAbs ≤ H → pos (some (k - 1)) x = -x) ∧ (H < x.natAbs → pos (some (k - 1)) x = x) := by
  constructor
  · intro hin
    rw [pos_some]
    by_cases h0 : x = 0
    · simp [h0]
    · have : (x.natAbs - 1).testBit (k - 1) = false := Nat.testBit_lt_two_pow (by omega)
      simp [h0, this]
  · intro hout
    rw [pos_some]
    have hn : x.natAbs - 1 = 2 ^ (k - 1) + (x.natAbs - 1 - H) := by omega
    have hb : (x.natAbs - 1).testBit (k - 1) = true := by
      rw [hn, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow (by omega)]; rfl
    simp [hb]

/-- psi folds the outer leaves of [-2H, 2H] onto [-H, H] minus 0. -/
def psi (H : ℤ) (x : ℤ) : ℤ := if 0 < x then x - H else x + H

/-- g unfolds positions back: y ↦ y + sign(y) H. -/
def g (H : ℤ) (y : ℤ) : ℤ := if 0 < y then y + H else y - H

theorem psi_natAbs (H : ℕ) (x : ℤ) (h1 : H < x.natAbs) : (psi H x).natAbs = x.natAbs - H := by
  unfold psi; split_ifs <;> omega

theorem psi_ne (H : ℕ) (x : ℤ) (h1 : H < x.natAbs) : psi H x ≠ 0 := by
  unfold psi; split_ifs <;> omega

/-- On outer leaves the non-top orders of F_(k+1) are those of F_k transported by psi and g. -/
theorem pos_outer (k H : ℕ) (hH : H = 2 ^ (k - 1)) (o : Option ℕ) (ho : ∀ b, o = some b → b < k - 1)
    (x : ℤ) (h1 : H < x.natAbs) (h2 : x.natAbs ≤ 2 * H) :
    pos o x = g H (pos o (psi H x)) := by
  have hpsi := psi_natAbs H x h1
  have hne := psi_ne H x h1
  cases o with
  | none => simp only [pos, g, psi]; split_ifs <;> omega
  | some b =>
    have hb := ho b rfl
    have hbit : (x.natAbs - 1).testBit b = ((psi H x).natAbs - 1).testBit b := by
      have hn : x.natAbs - 1 = 2 ^ (k - 1) + ((psi H x).natAbs - 1) := by omega
      rw [hn, Nat.testBit_two_pow_add_gt (by omega)]
    have hx0 : x ≠ 0 := by omega
    rw [pos_some, pos_some, hbit]
    simp only [ne_eq, hx0, hne, not_false_eq_true, true_and]
    split_ifs <;> simp only [g, psi] at * <;> split_ifs at * <;> omega

/-- `disp` only depends on the eight cross comparisons. -/
theorem disp_congr (p q : ℤ → ℤ) (a b c d a' b' c' d' : ℤ)
    (hac : p a < p c ↔ q a' < q c') (had : p a < p d ↔ q a' < q d')
    (hbc : p b < p c ↔ q b' < q c') (hbd : p b < p d ↔ q b' < q d')
    (hca : p c < p a ↔ q c' < q a') (hda : p d < p a ↔ q d' < q a')
    (hcb : p c < p b ↔ q c' < q b') (hdb : p d < p b ↔ q d' < q b') :
    disp p a b c d ↔ disp q a' b' c' d' := by
  unfold disp; rw [hac, had, hbc, hbd, hca, hda, hcb, hdb]

/-- Phi: inner leaves to the centre 0, outer leaves by psi. -/
def Phi (H : ℕ) (x : ℤ) : ℤ := if x.natAbs ≤ H then 0 else psi H x

/-- Order transfer for two leaves that are not both inner. -/
theorem lt_transfer (k H : ℕ) (hH : H = 2 ^ (k - 1)) (o : Option ℕ) (ho : ∀ b, o = some b → b < k - 1)
    (u v : ℤ) (hu : u.natAbs ≤ 2 * H) (hv : v.natAbs ≤ 2 * H)
    (hnot : ¬ (u.natAbs ≤ H ∧ v.natAbs ≤ H)) :
    pos o u < pos o v ↔ pos o (Phi H u) < pos o (Phi H v) := by
  have pin : ∀ x : ℤ, x.natAbs ≤ H → (pos o x).natAbs ≤ H := fun x hx => by
    rw [pos_natAbs]; exact hx
  have pnz : ∀ y : ℤ, y ≠ 0 → pos o y ≠ 0 := fun y hy => by
    intro h; apply hy; have := pos_natAbs o y; rw [h] at this; omega
  by_cases hui : u.natAbs ≤ H
  · have hvo : H < v.natAbs := by omega
    have ev := pos_outer k H hH o ho v hvo hv
    have := pin u hui
    have := pnz _ (psi_ne H v hvo)
    simp only [Phi, hui, if_true, show ¬ v.natAbs ≤ H by omega, if_false, pos_zero, ev, g]
    split_ifs <;> omega
  · by_cases hvi : v.natAbs ≤ H
    · have eu := pos_outer k H hH o ho u (by omega) hu
      have := pin v hvi
      have := pnz _ (psi_ne H u (by omega))
      simp only [Phi, hvi, if_true, hui, if_false, pos_zero, eu, g]
      split_ifs <;> omega
    · have eu := pos_outer k H hH o ho u (by omega) hu
      have ev := pos_outer k H hH o ho v (by omega) hv
      have := pnz _ (psi_ne H u (by omega))
      have := pnz _ (psi_ne H v (by omega))
      simp only [Phi, hui, hvi, if_false, eu, ev, g]
      split_ifs <;> omega

/-- Two outer leaves on the same side at different distances are split apart by some non-top order. -/
theorem outer_split (k H : ℕ) (hH : H = 2 ^ (k - 1)) (y z : ℤ) (hy1 : H < y.natAbs)
    (hy2 : y.natAbs ≤ 2 * H) (hz1 : H < z.natAbs) (hz2 : z.natAbs ≤ 2 * H)
    (hs : (0 < y ∧ 0 < z) ∨ (y < 0 ∧ z < 0)) (hyz : y ≠ z) :
    ∃ b < k - 1, (pos (some b) y < -(H : ℤ) ∧ (H : ℤ) < pos (some b) z) ∨
      ((H : ℤ) < pos (some b) y ∧ pos (some b) z < -(H : ℤ)) := by
  have hd : y.natAbs - 1 - H ≠ z.natAbs - 1 - H := by omega
  obtain ⟨b, hb⟩ : ∃ b, (y.natAbs - 1 - H).testBit b ≠ (z.natAbs - 1 - H).testBit b := by
    by_contra hc; push Not at hc; exact hd (Nat.eq_of_testBit_eq hc)
  have hbk : b < k - 1 := by
    by_contra hge; push Not at hge
    have hp : 2 ^ (k - 1) ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hge
    have h1 : (y.natAbs - 1 - H).testBit b = false := Nat.testBit_lt_two_pow (by omega)
    have h2 : (z.natAbs - 1 - H).testBit b = false := Nat.testBit_lt_two_pow (by omega)
    exact hb (h1.trans h2.symm)
  have ey : (y.natAbs - 1).testBit b = (y.natAbs - 1 - H).testBit b := by
    have hn : y.natAbs - 1 = 2 ^ (k - 1) + (y.natAbs - 1 - H) := by omega
    have := Nat.testBit_two_pow_add_gt (show b < k - 1 by omega) (y.natAbs - 1 - H)
    rw [← hn] at this; exact this
  have ez : (z.natAbs - 1).testBit b = (z.natAbs - 1 - H).testBit b := by
    have hn : z.natAbs - 1 = 2 ^ (k - 1) + (z.natAbs - 1 - H) := by omega
    have := Nat.testBit_two_pow_add_gt (show b < k - 1 by omega) (z.natAbs - 1 - H)
    rw [← hn] at this; exact this
  refine ⟨b, hbk, ?_⟩
  have hy0 : y ≠ 0 := by omega
  have hz0 : z ≠ 0 := by omega
  have py : pos (some b) y = if (y.natAbs - 1 - H).testBit b = false then -y else y := by
    rw [pos_some, ey]; simp only [ne_eq, hy0, not_false_eq_true, true_and]
  have pz : pos (some b) z = if (z.natAbs - 1 - H).testBit b = false then -z else z := by
    rw [pos_some, ez]; simp only [ne_eq, hz0, not_false_eq_true, true_and]
  rw [py, pz]
  cases hyb : (y.natAbs - 1 - H).testBit b <;> cases hzb : (z.natAbs - 1 - H).testBit b <;>
    simp only [hyb, hzb, ne_eq, not_true_eq_false] at hb ⊢ <;> simp <;> omega

/-- F_k has no common quartet. -/
theorem family (k : ℕ) (hk : 1 ≤ k) : ∀ a b c d : ℤ, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    a.natAbs ≤ 2 ^ (k - 1) → b.natAbs ≤ 2 ^ (k - 1) → c.natAbs ≤ 2 ^ (k - 1) →
    d.natAbs ≤ 2 ^ (k - 1) → ¬ Common k a b c d := by
  induction k, hk using Nat.le_induction with
  | base => intro a b c d _ _ _ _ _ _ ha hb hc hd; simp at ha hb hc hd; omega
  | succ k hk ih =>
    intro a b c d hab hac had hbc hbd hcd ha hb hc hd hcom
    have hpow : (2 : ℕ) ^ (k + 1 - 1) = 2 * 2 ^ (k - 1) := by
      rw [show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ]; ring
    obtain ⟨H, hH⟩ : ∃ H, H = 2 ^ (k - 1) := ⟨_, rfl⟩
    rw [hpow, ← hH] at ha hb hc hd
    rw [← hH] at ih
    obtain ⟨hid, hall⟩ := hcom
    have hsub : ∀ j < k - 1, disp (pos (some j)) a b c d := fun j hj => hall j (by omega)
    have htop := hall (k - 1) (by omega)
    obtain ⟨ta1, ta2⟩ := pos_top k H hH a ha
    obtain ⟨tb1, tb2⟩ := pos_top k H hH b hb
    obtain ⟨tc1, tc2⟩ := pos_top k H hH c hc
    obtain ⟨td1, td2⟩ := pos_top k H hH d hd
    have phi_case : (¬ (a.natAbs ≤ H ∧ b.natAbs ≤ H)) → (¬ (a.natAbs ≤ H ∧ c.natAbs ≤ H)) →
        (¬ (a.natAbs ≤ H ∧ d.natAbs ≤ H)) → (¬ (b.natAbs ≤ H ∧ c.natAbs ≤ H)) →
        (¬ (b.natAbs ≤ H ∧ d.natAbs ≤ H)) → (¬ (c.natAbs ≤ H ∧ d.natAbs ≤ H)) → False := by
      intro n1 n2 n3 n4 n5 n6
      have tr : ∀ o : Option ℕ, (∀ b, o = some b → b < k - 1) →
          (disp (pos o) a b c d ↔ disp (pos o) (Phi H a) (Phi H b) (Phi H c) (Phi H d)) := by
        intro o ho
        have T := lt_transfer k H hH o ho
        exact disp_congr _ _ _ _ _ _ _ _ _ _ (T a c ha hc n2) (T a d ha hd n3) (T b c hb hc n4)
          (T b d hb hd n5) (T c a hc ha fun h => n2 ⟨h.2, h.1⟩) (T d a hd ha fun h => n3 ⟨h.2, h.1⟩)
          (T c b hc hb fun h => n4 ⟨h.2, h.1⟩) (T d b hd hb fun h => n5 ⟨h.2, h.1⟩)
      have hP : ∀ x : ℤ, x.natAbs ≤ 2 * H → (Phi H x).natAbs ≤ H := fun x hx => by
        unfold Phi psi; split_ifs <;> omega
      have hPinj : ∀ x y : ℤ, x.natAbs ≤ 2 * H → y.natAbs ≤ 2 * H → x ≠ y →
          ¬ (x.natAbs ≤ H ∧ y.natAbs ≤ H) → Phi H x ≠ Phi H y := fun x y hx hy hxy hn => by
        unfold Phi psi; split_ifs <;> omega
      refine ih (Phi H a) (Phi H b) (Phi H c) (Phi H d)
        (hPinj _ _ ha hb hab n1) (hPinj _ _ ha hc hac n2) (hPinj _ _ ha hd had n3)
        (hPinj _ _ hb hc hbc n4) (hPinj _ _ hb hd hbd n5) (hPinj _ _ hc hd hcd n6)
        (hP a ha) (hP b hb) (hP c hc) (hP d hd) ⟨(tr none (by simp)).mp hid, fun j hj => ?_⟩
      exact (tr (some j) (by intro b hb; cases hb; exact hj)).mp (hsub j hj)
    have pin : ∀ (o : Option ℕ) (x : ℤ), x.natAbs ≤ H → (pos o x).natAbs ≤ H := fun o x hx => by
      rw [pos_natAbs]; exact hx
    have hid' := hid
    simp only [disp, pos] at hid'
    unfold disp at htop
    by_cases h4 : a.natAbs ≤ H ∧ b.natAbs ≤ H ∧ c.natAbs ≤ H ∧ d.natAbs ≤ H
    · exact ih a b c d hab hac had hbc hbd hcd h4.1 h4.2.1 h4.2.2.1 h4.2.2.2 ⟨hid, hsub⟩
    by_cases h1 : (¬ (a.natAbs ≤ H ∧ b.natAbs ≤ H)) ∧ (¬ (a.natAbs ≤ H ∧ c.natAbs ≤ H)) ∧
        (¬ (a.natAbs ≤ H ∧ d.natAbs ≤ H)) ∧ (¬ (b.natAbs ≤ H ∧ c.natAbs ≤ H)) ∧
        (¬ (b.natAbs ≤ H ∧ d.natAbs ≤ H)) ∧ (¬ (c.natAbs ≤ H ∧ d.natAbs ≤ H))
    · exact phi_case h1.1 h1.2.1 h1.2.2.1 h1.2.2.2.1 h1.2.2.2.2.1 h1.2.2.2.2.2
    by_cases ia : a.natAbs ≤ H <;> by_cases ib : b.natAbs ≤ H <;>
      by_cases ic : c.natAbs ≤ H <;> by_cases id : d.natAbs ≤ H
    all_goals
      first | rw [ta1 ia] at htop | rw [ta2 (by omega)] at htop
      first | rw [tb1 ib] at htop | rw [tb2 (by omega)] at htop
      first | rw [tc1 ic] at htop | rw [tc2 (by omega)] at htop
      first | rw [td1 id] at htop | rw [td2 (by omega)] at htop
    all_goals clear ta1 ta2 tb1 tb2 tc1 tc2 td1 td2 phi_case ih hall hid
    all_goals first
      | omega
      | (by_cases hs : (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0)
         · obtain ⟨j, hj, hj'⟩ := outer_split k H hH a b (by omega) ha (by omega) hb hs hab
           have := hsub j hj; unfold disp at this
           have := pin (some j) c ic; have := pin (some j) d id
           omega
         · omega)
      | (by_cases hs : (0 < c ∧ 0 < d) ∨ (c < 0 ∧ d < 0)
         · obtain ⟨j, hj, hj'⟩ := outer_split k H hH c d (by omega) hc (by omega) hd hs hcd
           have := hsub j hj; unfold disp at this
           have := pin (some j) a ia; have := pin (some j) b ib
           omega
         · omega)

end CatFamily
