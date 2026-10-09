import LeanProofs.QNarayana.Bijection

/-!
# MO 501839, Step 1 and the main theorem: Dyck paths

A path is a list of steps, `true` = up, `false` = down. A valley is a down step followed by an up step; `maj` is
the sum of the positions of the valley down steps (positions from 1).

Encoding. `fu P` records, for each up step, whether it is followed by a down step (or the end); `fd P` records,
for each down step, whether it is followed by an up step. For a Dyck path of semilength `n ≥ 1` both have length
`n`, `fu` ends with `true` and `fd` with `false`; `encW P` pairs their first `n - 1` entries letter by letter
(`(x ∈ U, x ∈ D)` in PROOF.md). `dec` rebuilds the path by alternating runs: ups until a `true` flag, then downs
until a `true` flag.

Main theorem (`signed_dyck`): for `n ≥ 1`, the sum of `(-1)^maj` over Dyck paths of semilength `n` with `k`
valleys equals the number of those paths that equal their reverse-complement (the symmetric paths).
-/

namespace QNarayana

open L

/-! ### Paths -/

def stepΔ (s : Bool) : ℤ := if s then 1 else -1

/-- From height `h` the path stays `≥ 0` and ends at height 0. -/
def dk : ℤ → List Bool → Bool
  | h, [] => h == 0
  | h, s :: P => decide (0 ≤ h + stepΔ s) && dk (h + stepΔ s) P

/-- Valley positions: `i` steps read so far, `pd` = the previous step was down. -/
def majP : ℕ → Bool → List Bool → ℕ
  | _, _, [] => 0
  | i, pd, s :: P => (if pd && s then i else 0) + majP (i + 1) (!s) P

def maj (P : List Bool) : ℕ := majP 0 false P

def valP : Bool → List Bool → ℕ
  | _, [] => 0
  | pd, s :: P => (if pd && s then 1 else 0) + valP (!s) P

/-- Number of valleys. -/
def valleys (P : List Bool) : ℕ := valP false P

/-- Reverse-complement: the mirror image of a path. -/
def rc (P : List Bool) : List Bool := (P.map not).reverse

def bwords : ℕ → Finset (List Bool)
  | 0 => {[]}
  | m + 1 => ({true, false} : Finset Bool).biUnion (fun s => (bwords m).image (s :: ·))

lemma mem_bwords {m : ℕ} {P : List Bool} : P ∈ bwords m ↔ P.length = m := by
  induction m generalizing P with
  | zero => cases P <;> simp [bwords]
  | succ m ih =>
    cases P with
    | nil => simp [bwords]
    | cons s P => cases s <;> simp [bwords, ih]

/-- Dyck paths of semilength `n` with `k` valleys. -/
def Dyck (n k : ℕ) : Finset (List Bool) :=
  (bwords (2 * n)).filter (fun P => dk 0 P = true ∧ valleys P = k)

/-- Number of `true` entries. -/
def ct : List Bool → ℕ
  | [] => 0
  | s :: l => (if s then 1 else 0) + ct l

lemma ct_append : ∀ l m : List Bool, ct (l ++ m) = ct l + ct m
  | [], _ => by simp [ct]
  | s :: l, m => by simp [ct, ct_append l m]; ring

lemma ct_pos_of_getLast : ∀ l : List Bool, l.getLast? = some true → 0 < ct l
  | [], h => by simp at h
  | [s], h => by simp at h; subst h; simp [ct]
  | s :: t :: l, h => by
    have := ct_pos_of_getLast (t :: l) (by simpa using h)
    simp only [ct] at this ⊢; omega

/-! ### Flags and the rebuilding map -/

def nxF : List Bool → Bool
  | [] => true
  | s :: _ => !s

def nxT : List Bool → Bool
  | [] => false
  | s :: _ => s

def fu : List Bool → List Bool
  | [] => []
  | s :: P => if s then nxF P :: fu P else fu P

def fd : List Bool → List Bool
  | [] => []
  | s :: P => if s then fd P else nxT P :: fd P

@[simp] lemma fu_nil : fu [] = [] := rfl
@[simp] lemma fd_nil : fd [] = [] := rfl
@[simp] lemma nxF_nil : nxF [] = true := rfl
@[simp] lemma nxT_nil : nxT [] = false := rfl
@[simp] lemma fu_true (P : List Bool) : fu (true :: P) = nxF P :: fu P := rfl
@[simp] lemma fu_false (P : List Bool) : fu (false :: P) = fu P := rfl
@[simp] lemma fd_true (P : List Bool) : fd (true :: P) = fd P := rfl
@[simp] lemma fd_false (P : List Bool) : fd (false :: P) = nxT P :: fd P := rfl
@[simp] lemma nxF_cons (s : Bool) (P : List Bool) : nxF (s :: P) = !s := rfl
@[simp] lemma nxT_cons (s : Bool) (P : List Bool) : nxT (s :: P) = s := rfl

/-- Rebuild a path from its flags: ups until a `true` flag, then downs until a `true` flag. -/
def dec : Bool → List Bool → List Bool → List Bool
  | true, f :: p, v => true :: dec (!f) p v
  | true, [], v => v.map (fun _ => false)
  | false, p, g :: v => false :: dec g p v
  | false, p, [] => p.map (fun _ => true)
termination_by _ p v => p.length + v.length

lemma dec_tc (f : Bool) (p v : List Bool) : dec true (f :: p) v = true :: dec (!f) p v := by rw [dec]
lemma dec_tn (v : List Bool) : dec true [] v = v.map (fun _ => false) := by rw [dec]
lemma dec_fc (g : Bool) (p v : List Bool) : dec false p (g :: v) = false :: dec g p v := by
  cases p <;> rw [dec]
lemma dec_fn (p : List Bool) : dec false p [] = p.map (fun _ => true) := by cases p <;> rw [dec]

lemma dec_up_head {p : List Bool} (v : List Bool) (h : p ≠ []) : ∃ q, dec true p v = true :: q := by
  cases p with
  | nil => exact absurd rfl h
  | cons f p => exact ⟨_, dec_tc f p v⟩

lemma dec_down_head (p : List Bool) {v : List Bool} (h : v ≠ []) : ∃ q, dec false p v = false :: q := by
  cases v with
  | nil => exact absurd rfl h
  | cons g v => exact ⟨_, dec_fc g p v⟩

/-- `dec` undoes the flags of any path, from the phase of its first step. -/
theorem dec_flags : ∀ (P : List Bool) (ph : Bool), (P = [] ∨ P.head? = some ph) → dec ph (fu P) (fd P) = P
  | [], ph, _ => by cases ph <;> simp [fu, fd, dec_tn, dec_fn]
  | s :: P, ph, hP => by
    have hs : s = ph := by simpa using hP
    subst hs
    cases s
    · rw [fd_false, fu_false, dec_fc]
      congr 1
      exact dec_flags P _ (by cases P <;> simp)
    · rw [fd_true, fu_true, dec_tc]
      congr 1
      exact dec_flags P _ (by cases P <;> simp)

lemma length_dec : ∀ (ph : Bool) (p v : List Bool), (dec ph p v).length = p.length + v.length
  | true, f :: p, v => by rw [dec_tc]; simp [length_dec (!f) p v]; ring
  | true, [], v => by simp [dec_tn]
  | false, p, g :: v => by rw [dec_fc]; simp [length_dec g p v]; ring
  | false, p, [] => by simp [dec_fn]
termination_by _ p v => p.length + v.length

/-! ### Flags and valley positions of the rebuilt path -/

def sumIdx : ℕ → List Bool → ℕ
  | _, [] => 0
  | o, s :: l => (if s then o + 1 else 0) + sumIdx (o + 1) l

/-- Shape of the remaining flags in each phase of `dec`. -/
def Inv : Bool → List Bool → List Bool → Prop
  | true, p, v => p.getLast? = some true ∧ v.getLast? = some false ∧ ct p = ct v + 1
  | false, p, v => v.getLast? = some false ∧ (p = [] ∨ p.getLast? = some true) ∧ ct p = ct v

/-- What remains of `maj` from a phase of `dec` (`i` ups and `j` downs already emitted). -/
def M : Bool → ℕ → ℕ → Bool → List Bool → List Bool → ℕ
  | true, i, j, pd, p, v => (if pd then i + j else 0) + sumIdx i p.dropLast + sumIdx j v.dropLast
  | false, i, j, _, p, v => (if 0 < ct v then i else 0) + sumIdx i p.dropLast + sumIdx j v.dropLast

lemma getLast?_cons_of_ne {s : Bool} {l : List Bool} (h : l ≠ []) : (s :: l).getLast? = l.getLast? := by
  cases l with
  | nil => exact absurd rfl h
  | cons t l => simp

lemma inv_tf {p v : List Bool} (hI : Inv true (false :: p) v) : p ≠ [] ∧ Inv true p v := by
  obtain ⟨h1, h2, h3⟩ := hI
  have hne : p ≠ [] := by rintro rfl; simp at h1
  exact ⟨hne, by rwa [getLast?_cons_of_ne hne] at h1, h2, by simpa [ct] using h3⟩

lemma inv_tt {p v : List Bool} (hI : Inv true (true :: p) v) : Inv false p v := by
  obtain ⟨h1, h2, h3⟩ := hI
  refine ⟨h2, ?_, by simp [ct] at h3; omega⟩
  by_cases hne : p = []
  · exact Or.inl hne
  · exact Or.inr (by rwa [getLast?_cons_of_ne hne] at h1)

lemma inv_ft {p v : List Bool} (hI : Inv false p (true :: v)) : p ≠ [] ∧ v ≠ [] ∧ Inv true p v := by
  obtain ⟨h1, h2, h3⟩ := hI
  have hv : v ≠ [] := by rintro rfl; simp at h1
  have hp : p ≠ [] := by rintro rfl; simp [ct] at h3; omega
  refine ⟨hp, hv, by simpa [hp] using h2, by rwa [getLast?_cons_of_ne hv] at h1, by simp [ct] at h3; omega⟩

lemma inv_ff {p v : List Bool} (hI : Inv false p (false :: v)) :
    (v = [] ∧ p = []) ∨ (v ≠ [] ∧ Inv false p v) := by
  obtain ⟨h1, h2, h3⟩ := hI
  by_cases hv : v = []
  · subst hv
    left
    refine ⟨rfl, ?_⟩
    rcases h2 with h | h
    · exact h
    · have := ct_pos_of_getLast p h; simp [ct] at h3; omega
  · exact Or.inr ⟨hv, by rwa [getLast?_cons_of_ne hv] at h1, h2, by simpa [ct] using h3⟩

/-- `dec` returns a path whose flags are the input, and its valley positions are `M`. -/
theorem dec_spec : ∀ (ph : Bool) (p v : List Bool), Inv ph p v →
    fu (dec ph p v) = p ∧ fd (dec ph p v) = v ∧ ∀ a b pd, majP (a + b) pd (dec ph p v) = M ph a b pd p v
  | true, f :: p, v, hI => by
    rw [dec_tc]
    cases f
    · obtain ⟨hne, hI'⟩ := inv_tf hI
      obtain ⟨ih1, ih2, ih3⟩ := dec_spec true p v hI'
      obtain ⟨q, hq⟩ := dec_up_head v hne
      simp only [Bool.not_false] at ih1 ih2 ih3 ⊢
      refine ⟨by rw [fu_true, ih1, hq]; rfl, by rw [fd_true, ih2], fun a b pd => ?_⟩
      rw [majP, show a + b + 1 = (a + 1) + b by ring, ih3]
      simp [M, List.dropLast_cons_of_ne_nil hne, sumIdx]; ring
    · have hI' := inv_tt hI
      obtain ⟨ih1, ih2, ih3⟩ := dec_spec false p v hI'
      have hv : v ≠ [] := by rintro rfl; simp [Inv] at hI'
      obtain ⟨q, hq⟩ := dec_down_head p hv
      simp only [Bool.not_true] at ih1 ih2 ih3 ⊢
      refine ⟨by rw [fu_true, ih1, hq]; rfl, by rw [fd_true, ih2], fun a b pd => ?_⟩
      rw [majP, show a + b + 1 = (a + 1) + b by ring, ih3]
      obtain ⟨-, hp, hc⟩ := hI'
      rcases hp with rfl | hp
      · simp [M, sumIdx, ← hc, ct]
      · have := ct_pos_of_getLast p hp
        have hne : p ≠ [] := by rintro rfl; simp at hp
        simp only [M, Bool.and_true, ← hc, this, ite_true, List.dropLast_cons_of_ne_nil hne, sumIdx]
        ring
  | true, [], v, hI => by simp [Inv] at hI
  | false, p, g :: v, hI => by
    rw [dec_fc]
    cases g
    · rcases inv_ff hI with ⟨rfl, rfl⟩ | ⟨hv, hI'⟩
      · simp [dec_fn, fu, fd, majP, M, ct, sumIdx]
      · obtain ⟨ih1, ih2, ih3⟩ := dec_spec false p v hI'
        obtain ⟨q, hq⟩ := dec_down_head p hv
        refine ⟨by rw [fu_false, ih1], by rw [fd_false, ih2, hq, nxT_cons], fun a b pd => ?_⟩
        rw [majP, show a + b + 1 = a + (b + 1) by ring, ih3]
        simp [M, ct, List.dropLast_cons_of_ne_nil hv, sumIdx]
    · obtain ⟨hp, hv, hI'⟩ := inv_ft hI
      obtain ⟨ih1, ih2, ih3⟩ := dec_spec true p v hI'
      obtain ⟨q, hq⟩ := dec_up_head v hp
      refine ⟨by rw [fu_false, ih1], by rw [fd_false, ih2, hq, nxT_cons], fun a b pd => ?_⟩
      rw [majP, show a + b + 1 = a + (b + 1) by ring, ih3]
      simp [M, ct, List.dropLast_cons_of_ne_nil hv, sumIdx]
      ring
  | false, p, [], hI => by simp [Inv] at hI
termination_by _ p v => p.length + v.length

/-! ### Heights of the rebuilt path -/

/-- Prefix condition on the flags in each phase (`h` = current height). -/
def R : Bool → ℕ → List Bool → List Bool → Prop
  | true, h, p, v => ∀ y < p.length, ct (p.take y) ≤ ct (v.take (y + h))
  | false, h, p, v => ∀ y < p.length, ct (p.take y) + 1 ≤ ct (v.take (y + h))

lemma take_succ_cons (s : Bool) (l : List Bool) (y : ℕ) : (s :: l).take (y + 1) = s :: l.take y := rfl

lemma R_up_cons (f : Bool) (p v : List Bool) (h : ℕ) : R true h (f :: p) v ↔ R (!f) (h + 1) p v := by
  cases f <;> simp only [R, List.length_cons, Bool.not_false, Bool.not_true] <;> constructor
  all_goals first
    | (intro H y hy
       have := H (y + 1) (by omega)
       rw [take_succ_cons, show y + 1 + h = y + (h + 1) by ring] at this
       (simp [ct] at this ⊢) <;> omega)
    | (intro H y hy
       cases y with
       | zero => simp [ct]
       | succ y =>
         have := H y (by omega)
         rw [take_succ_cons, show y + 1 + h = y + (h + 1) by ring]
         (simp [ct] at this ⊢) <;> omega)

lemma R_down_cons (g : Bool) (p v : List Bool) (h : ℕ) : R false (h + 1) p (g :: v) ↔ R g h p v := by
  cases g <;> simp only [R] <;> constructor <;> intro H y hy <;> have := H y hy <;>
    rw [show y + (h + 1) = (y + h) + 1 by ring, take_succ_cons] at * <;> simp [ct] at this ⊢ <;> omega

lemma dk_downs : ∀ (v : List Bool) (h : ℕ), v.length = h → dk h (v.map (fun _ => false)) = true
  | [], h, hl => by simp at hl; subst hl; simp [dk]
  | g :: v, h, hl => by
    simp only [List.length_cons] at hl
    simp only [List.map_cons, dk, stepΔ, Bool.false_eq_true, ite_false, Bool.and_eq_true, decide_eq_true_eq]
    have := dk_downs v (h - 1) (by omega)
    refine ⟨by omega, ?_⟩
    rwa [show ((h - 1 : ℕ) : ℤ) = (h : ℤ) + -1 by omega] at this

theorem dk_dec : ∀ (ph : Bool) (p v : List Bool) (h : ℕ), v.length = p.length + h →
    (dk h (dec ph p v) = true ↔ R ph h p v)
  | true, f :: p, v, h, hl => by
    rw [dec_tc, R_up_cons, ← dk_dec (!f) p v (h + 1) (by simp only [List.length_cons] at hl; omega)]
    simp only [dk, stepΔ, ite_true, Bool.and_eq_true, decide_eq_true_eq]
    rw [show (h : ℤ) + 1 = ((h + 1 : ℕ) : ℤ) by push_cast; ring]
    simp only [show (0 : ℤ) ≤ ((h + 1 : ℕ) : ℤ) by positivity, true_and]
  | true, [], v, h, hl => by
    rw [dec_tn]
    simp only [List.length_nil, zero_add] at hl
    exact ⟨fun _ y hy => by simp at hy, fun _ => dk_downs v h hl⟩
  | false, p, g :: v, h, hl => by
    rw [dec_fc]
    simp only [dk, stepΔ, Bool.false_eq_true, ite_false, Bool.and_eq_true, decide_eq_true_eq]
    simp only [List.length_cons] at hl
    cases h with
    | zero =>
      simp only [R]
      constructor
      · rintro ⟨h1, -⟩; norm_num at h1
      · intro hR; have := hR 0 (by omega); simp [ct] at this
    | succ h =>
      rw [R_down_cons, ← dk_dec g p v h (by omega)]
      rw [show ((h + 1 : ℕ) : ℤ) + -1 = (h : ℤ) by push_cast; ring]
      simp only [show (0 : ℤ) ≤ h by positivity, true_and]
  | false, p, [], h, hl => by
    rw [dec_fn]
    simp only [List.length_nil] at hl
    have hp : p = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hh : h = 0 := by omega
    subst hp hh
    simp [dk, R]
termination_by _ p v => p.length + v.length

/-! ### Flags of Dyck paths -/

lemma length_fu : ∀ P : List Bool, (fu P).length = ct P
  | [] => rfl
  | s :: P => by cases s <;> simp [ct, length_fu P]; ring

lemma length_fu_fd : ∀ P : List Bool, (fu P).length + (fd P).length = P.length
  | [] => rfl
  | s :: P => by have := length_fu_fd P; cases s <;> simp <;> omega

lemma ct_fu : ∀ P : List Bool, ct (fu P) = ct (fd P) + (if P.head? = some true then 1 else 0)
  | [] => rfl
  | s :: P => by
    have := ct_fu P
    cases s <;> cases P with
    | nil => simp [ct]
    | cons t P => cases t <;> simp_all [ct] <;> omega

lemma fu_append_false : ∀ Q : List Bool, fu (Q ++ [false]) = fu Q
  | [] => rfl
  | s :: Q => by
    have := fu_append_false Q
    cases Q with
    | nil => cases s <;> rfl
    | cons t Q => cases s <;> simp_all

lemma fu_append_true : ∀ Q : List Bool, ∃ X, fu (Q ++ [true]) = X ++ [true]
  | [] => ⟨[], rfl⟩
  | s :: Q => by
    obtain ⟨X, hX⟩ := fu_append_true Q
    cases s
    · exact ⟨X, by simp [hX]⟩
    · exact ⟨nxF (Q ++ [true]) :: X, by simp [hX]⟩

lemma fd_append_false : ∀ Q : List Bool, ∃ X, fd (Q ++ [false]) = X ++ [false]
  | [] => ⟨[], rfl⟩
  | s :: Q => by
    obtain ⟨X, hX⟩ := fd_append_false Q
    cases s
    · exact ⟨nxT (Q ++ [false]) :: X, by simp [hX]⟩
    · exact ⟨X, by simp [hX]⟩

lemma fu_last (P : List Bool) (h : 0 < ct P) : ∃ X, fu P = X ++ [true] := by
  induction P using List.reverseRecOn with
  | nil => simp [ct] at h
  | append_singleton Q s ih =>
    cases s
    · rw [fu_append_false]; exact ih (by simpa [ct_append, ct] using h)
    · exact fu_append_true Q

lemma dk_sum : ∀ (P : List Bool) (h : ℤ), dk h P = true → h + 2 * (ct P : ℤ) = P.length
  | [], h, hP => by simpa [dk, ct] using hP
  | s :: P, h, hP => by
    simp only [dk, Bool.and_eq_true, decide_eq_true_eq] at hP
    have := dk_sum P _ hP.2
    cases s <;> simp [stepΔ, ct] at this ⊢ <;> omega

lemma dk_head : ∀ (P : List Bool), P ≠ [] → dk 0 P = true → P.head? = some true
  | [], h, _ => absurd rfl h
  | s :: P, _, hP => by
    cases s
    · simp [dk, stepΔ] at hP
    · rfl

lemma dk_last (P : List Bool) (hne : P ≠ []) (hP : dk 0 P = true) : ∃ Q, P = Q ++ [false] := by
  obtain ⟨Q, s, rfl⟩ : ∃ Q s, P = Q ++ [s] :=
    ⟨P.dropLast, P.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  cases s
  · exact ⟨Q, rfl⟩
  · -- the height before a final up step would be -1
    exfalso
    have key : ∀ (Q : List Bool) (h : ℤ), 0 ≤ h → dk h (Q ++ [true]) = true → False := by
      intro Q
      induction Q with
      | nil => intro h h0 hh; simp [dk, stepΔ] at hh; omega
      | cons t Q ih =>
        intro h _ hh
        simp only [List.cons_append, dk, Bool.and_eq_true, decide_eq_true_eq] at hh
        exact ih _ hh.1 hh.2
    exact key Q 0 le_rfl hP

/-- The data of a Dyck path in the domain of the encoding. -/
structure DyckData (n : ℕ) (P : List Bool) (p0 v0 : List Bool) : Prop where
  hp : fu P = p0 ++ [true]
  hv : fd P = v0 ++ [false]
  lp : p0.length = n - 1
  lv : v0.length = n - 1
  hc : ct p0 = ct v0

theorem dyck_flags {n : ℕ} (hn : 1 ≤ n) {P : List Bool} (hl : P.length = 2 * n) (hP : dk 0 P = true) :
    ∃ p0 v0, DyckData n P p0 v0 := by
  have hne : P ≠ [] := by rintro rfl; simp at hl; omega
  have hsum := dk_sum P 0 hP
  obtain ⟨p0, hp0⟩ := fu_last P (by omega)
  obtain ⟨Q, rfl⟩ := dk_last P hne hP
  obtain ⟨v0, hv0⟩ := fd_append_false Q
  have h1 := length_fu (Q ++ [false])
  have h2 := length_fu_fd (Q ++ [false])
  have h3 := ct_fu (Q ++ [false])
  rw [hp0] at h1 h2 h3
  rw [hv0] at h2 h3
  rw [dk_head _ hne hP] at h3
  simp [ct_append, ct] at h1 h2 h3 hsum hl
  refine ⟨p0, v0, hp0, hv0, by omega, by omega, by omega⟩

/-! ### Letters -/

def pu : L → Bool
  | d => true
  | b => true
  | _ => false

def pv : L → Bool
  | u => true
  | b => true
  | _ => false

def letter : Bool → Bool → L
  | false, true => u
  | true, false => d
  | false, false => a
  | true, true => b

def encW (P : List Bool) : List L := List.zipWith letter (fu P).dropLast (fd P).dropLast

def decW (w : List L) : List Bool := dec true (w.map pu ++ [true]) (w.map pv ++ [false])

lemma zipWith_letter : ∀ (w : List L), List.zipWith letter (w.map pu) (w.map pv) = w
  | [] => rfl
  | x :: w => by cases x <;> simp [letter, pu, pv, zipWith_letter w]

lemma map_zipWith_letter : ∀ (p v : List Bool), p.length = v.length →
    (List.zipWith letter p v).map pu = p ∧ (List.zipWith letter p v).map pv = v
  | [], [], _ => ⟨rfl, rfl⟩
  | f :: p, g :: v, hl => by
    have := map_zipWith_letter p v (by simpa using hl)
    cases f <;> cases g <;> simp [letter, pu, pv, this]
  | [], _ :: _, hl => by simp at hl
  | _ :: _, [], hl => by simp at hl

/-- `okTo` in counting form: prefixes never have more `d`-flags than `u`-flags (plus the start height). -/
theorem okTo_count : ∀ (w : List L) (h : ℤ), 0 ≤ h → (okTo h 0 w = true ↔
    (∀ y ≤ w.length, (ct ((w.map pu).take y) : ℤ) ≤ h + ct ((w.map pv).take y)) ∧
      (ct (w.map pu) : ℤ) = h + ct (w.map pv))
  | [], h, h0 => by
    simp only [okTo, beq_iff_eq, List.map_nil, List.take_nil, ct, List.length_nil, Nat.cast_zero, add_zero]
    constructor
    · rintro rfl; exact ⟨fun _ _ => le_rfl, rfl⟩
    · rintro ⟨-, h2⟩; exact h2.symm
  | x :: w, h, h0 => by
    simp only [okTo, Bool.and_eq_true, decide_eq_true_eq, List.map_cons, List.length_cons]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨A, B⟩ := (okTo_count w _ h1).1 h2
      refine ⟨fun y hy => ?_, ?_⟩
      · cases y with
        | zero => simp [ct]; omega
        | succ y =>
          have := A y (by omega)
          rw [take_succ_cons, take_succ_cons]
          cases x <;> simp [ct, pu, pv, Δ] at this ⊢ <;> omega
      · cases x <;> simp [ct, pu, pv, Δ] at B ⊢ <;> omega
    · rintro ⟨A, B⟩
      have h1 : 0 ≤ h + Δ x := by
        have := A 1 (by omega)
        cases x <;> simp [take_succ_cons, ct, pu, pv, Δ] at this ⊢ <;> omega
      refine ⟨h1, (okTo_count w _ h1).2 ⟨fun y hy => ?_, ?_⟩⟩
      · have := A (y + 1) (by omega)
        rw [take_succ_cons, take_succ_cons] at this
        cases x <;> simp [ct, pu, pv, Δ] at this ⊢ <;> omega
      · cases x <;> simp [ct, pu, pv, Δ] at B ⊢ <;> omega

lemma R_iff_okTo (w : List L) :
    R true 0 (w.map pu ++ [true]) (w.map pv ++ [false]) ∧ ct (w.map pu) = ct (w.map pv) ↔ okTo 0 0 w = true := by
  rw [okTo_count w 0 le_rfl]
  simp only [R, List.length_append, List.length_map, List.length_singleton, add_zero, zero_add]
  have key : ∀ y ≤ w.length, (w.map pu ++ [true]).take y = (w.map pu).take y ∧
      (w.map pv ++ [false]).take y = (w.map pv).take y := fun y hy =>
    ⟨List.take_append_of_le_length (by simpa using hy), List.take_append_of_le_length (by simpa using hy)⟩
  constructor
  · rintro ⟨hR, hc⟩
    refine ⟨fun y hy => ?_, by omega⟩
    have := hR y (by omega)
    rw [(key y hy).1, (key y hy).2] at this
    exact_mod_cast this
  · rintro ⟨h1, h2⟩
    refine ⟨fun y hy => ?_, by omega⟩
    rw [(key y (by omega)).1, (key y (by omega)).2]
    exact_mod_cast h1 y (by omega)

lemma sgn_sumIdx : ∀ (w : List L) (o : ℕ),
    sgnFrom (o + 1) w = (-1) ^ (sumIdx o (w.map pu) + sumIdx o (w.map pv))
  | [], _ => by simp [sgnFrom, sumIdx]
  | x :: w, o => by
    simp only [sgnFrom, List.map_cons, sumIdx]
    rw [sgn_sumIdx w (o + 1)]
    have key : (if lv x then (1 : ℤ) else (-1) ^ (o + 1)) =
        (-1) ^ ((if pu x then o + 1 else 0) + (if pv x then o + 1 else 0)) := by
      cases x <;> simp [lv, pu, pv, ← two_mul, pow_mul]
    rw [key, ← pow_add]; congr 1; ring

lemma wt2_ct : ∀ w : List L, wt2 w = ct (w.map pu) + ct (w.map pv)
  | [] => rfl
  | x :: w => by
    have := wt2_ct w
    cases x <;> simp [wt2, w2, pu, pv, ct, this] <;> ring

lemma valP_ct : ∀ (P : List Bool) (pd : Bool),
    valP pd P = (if pd && P.head? == some true then 1 else 0) + ct (fd P)
  | [], pd => by cases pd <;> rfl
  | s :: P, pd => by
    have := valP_ct P (!s)
    cases P with
    | nil => cases s <;> cases pd <;> simp [valP, ct]
    | cons t P => cases s <;> cases pd <;> cases t <;> simp_all [valP, ct] <;> omega

/-! ### Reverse-complement -/

/-- For each down step: is the previous step up (`pr` before the first step)? -/
def gd : Bool → List Bool → List Bool
  | _, [] => []
  | pr, s :: P => if s then gd true P else pr :: gd false P

/-- For each up step: is the previous step down (`pd` before the first step)? -/
def gu : Bool → List Bool → List Bool
  | _, [] => []
  | pd, s :: P => if s then pd :: gu false P else gu true P

lemma rc_cons (s : Bool) (P : List Bool) : rc (s :: P) = rc P ++ [!s] := by simp [rc]

lemma fu_rc_append : ∀ (P R : List Bool), fu (rc P ++ R) = (gd (nxF R) P).reverse ++ fu R
  | [], R => by simp [rc, gd]
  | s :: P, R => by
    rw [rc_cons, List.append_assoc, List.singleton_append, fu_rc_append P]
    cases s <;> simp [fu, gd, nxF]

lemma fd_rc_append : ∀ (P R : List Bool), fd (rc P ++ R) = (gu (nxT R) P).reverse ++ fd R
  | [], R => by simp [rc, gu]
  | s :: P, R => by
    rw [rc_cons, List.append_assoc, List.singleton_append, fd_rc_append P]
    cases s <;> simp [fd, gu, nxT]

def g1 (pr : Bool) : List Bool → Bool
  | false :: _ => pr
  | _ => true

def h1 (pd : Bool) : List Bool → Bool
  | true :: _ => pd
  | _ => true

lemma gd_eq : ∀ (P : List Bool) (pr : Bool), gd pr P = (g1 pr P :: fd P).dropLast
  | [], _ => rfl
  | s :: P, pr => by
    have ih := gd_eq P
    cases s
    · simp only [gd, Bool.false_eq_true, ite_false, fd, g1, ih]
      cases P with
      | nil => rfl
      | cons t P => cases t <;> rfl
    · simp only [gd, ite_true, fd, ih]
      cases P with
      | nil => rfl
      | cons t P => cases t <;> rfl

lemma gu_eq : ∀ (P : List Bool) (pd : Bool), gu pd P = (h1 pd P :: fu P).dropLast
  | [], _ => rfl
  | s :: P, pd => by
    have ih := gu_eq P
    cases s
    · simp only [gu, Bool.false_eq_true, ite_false, fu, ih]
      cases P with
      | nil => rfl
      | cons t P => cases t <;> rfl
    · simp only [gu, ite_true, fu, h1, ih]
      cases P with
      | nil => rfl
      | cons t P => cases t <;> rfl

lemma flags_rc {P p0 v0 : List Bool} (hhead : P.head? = some true) (hp : fu P = p0 ++ [true])
    (hv : fd P = v0 ++ [false]) : fu (rc P) = v0.reverse ++ [true] ∧ fd (rc P) = p0.reverse ++ [false] := by
  have e1 := fu_rc_append P []
  have e2 := fd_rc_append P []
  simp only [List.append_nil, nxF, nxT, fu, fd] at e1 e2
  obtain ⟨t, P', rfl⟩ : ∃ t P', P = t :: P' := by
    cases P with
    | nil => simp at hhead
    | cons t P' => exact ⟨t, P', rfl⟩
  simp at hhead; subst hhead
  rw [e1, e2, gd_eq, gu_eq, hp, hv]
  simp only [g1, h1]
  constructor
  · rw [show (true :: (v0 ++ [false])).dropLast = true :: v0 by simp [List.dropLast_cons_of_ne_nil]]
    simp
  · rw [show (false :: (p0 ++ [true])).dropLast = false :: p0 by simp [List.dropLast_cons_of_ne_nil]]
    simp

lemma mirror_zipWith : ∀ (p v : List Bool), p.length = v.length →
    mirror (List.zipWith letter p v) = List.zipWith letter v.reverse p.reverse
  | [], [], _ => rfl
  | f :: p, g :: v, hl => by
    have ih := mirror_zipWith p v (by simpa using hl)
    rw [List.zipWith_cons_cons, mirror_cons, ih]
    simp only [List.reverse_cons]
    rw [List.zipWith_append (by simp at hl ⊢; omega)]
    cases f <;> cases g <;> rfl
  | [], _ :: _, hl => by simp at hl
  | _ :: _, [], hl => by simp at hl

/-! ### The main theorem -/

lemma encW_eq {n : ℕ} {P p0 v0 : List Bool} (D : DyckData n P p0 v0) :
    encW P = List.zipWith letter p0 v0 := by
  simp [encW, D.hp, D.hv]

lemma inv_data {p0 v0 : List Bool} (hc : ct p0 = ct v0) : Inv true (p0 ++ [true]) (v0 ++ [false]) :=
  ⟨by simp, by simp, by simp [ct_append, ct, hc]⟩

theorem encW_mem {n k : ℕ} (hn : 1 ≤ n) {P : List Bool} (hP : P ∈ Dyck n k) :
    ∃ p0 v0, DyckData n P p0 v0 ∧ encW P ∈ Mot (n - 1) (2 * k) ∧ P = dec true (p0 ++ [true]) (v0 ++ [false]) := by
  simp only [Dyck, Finset.mem_filter, mem_bwords] at hP
  obtain ⟨hl, hdk, hval⟩ := hP
  obtain ⟨p0, v0, D⟩ := dyck_flags hn hl hdk
  have hdec : P = dec true (p0 ++ [true]) (v0 ++ [false]) := by
    rw [← D.hp, ← D.hv, dec_flags P true (Or.inr (dk_head P (by rintro rfl; simp at hl; omega) hdk))]
  refine ⟨p0, v0, D, ?_, hdec⟩
  obtain ⟨m1, m2⟩ := map_zipWith_letter p0 v0 (by rw [D.lp, D.lv])
  simp only [Mot, Finset.mem_filter, mem_words, encW_eq D]
  refine ⟨by simp [D.lp, D.lv], ?_, ?_⟩
  · rw [← R_iff_okTo, m1, m2]
    exact ⟨(dk_dec true (p0 ++ [true]) (v0 ++ [false]) 0 (by simp [D.lp, D.lv])).1 (hdec ▸ hdk), D.hc⟩
  · rw [wt2_ct, m1, m2, ← hval, valleys, valP_ct, D.hv]
    simp [ct_append, ct, D.hc]; ring

theorem decW_mem {n k : ℕ} (hn : 1 ≤ n) {w : List L} (hw : w ∈ Mot (n - 1) (2 * k)) :
    decW w ∈ Dyck n k ∧ encW (decW w) = w := by
  simp only [Mot, Finset.mem_filter, mem_words] at hw
  obtain ⟨hl, hok, hwt⟩ := hw
  obtain ⟨hR, hc⟩ := (R_iff_okTo w).2 hok
  obtain ⟨f1, f2, -⟩ := dec_spec true _ _ (inv_data hc)
  have henc : encW (decW w) = w := by
    simp only [encW, decW, f1, f2, List.dropLast_concat, zipWith_letter]
  refine ⟨?_, henc⟩
  simp only [Dyck, Finset.mem_filter, mem_bwords]
  refine ⟨?_, (dk_dec true _ _ 0 (by simp)).2 hR, ?_⟩
  · simp only [decW, length_dec, List.length_append, List.length_map, List.length_singleton]; omega
  · rw [valleys, valP_ct, decW, f2]
    rw [wt2_ct] at hwt
    simp [ct_append, ct]; omega

theorem maj_sign {n k : ℕ} (hn : 1 ≤ n) {P : List Bool} (hP : P ∈ Dyck n k) :
    (-1 : ℤ) ^ maj P = sgnFrom 1 (encW P) := by
  obtain ⟨p0, v0, D, -, hdec⟩ := encW_mem hn hP
  obtain ⟨-, -, hm⟩ := dec_spec true _ _ (inv_data D.hc)
  have hmaj : maj P = sumIdx 0 p0 + sumIdx 0 v0 := by
    rw [maj, hdec, show (0 : ℕ) = 0 + 0 from rfl, hm]
    simp [M, List.dropLast_concat]
  obtain ⟨m1, m2⟩ := map_zipWith_letter p0 v0 (by rw [D.lp, D.lv])
  rw [hmaj, encW_eq D, sgn_sumIdx, m1, m2]

theorem sym_iff {n k : ℕ} (hn : 1 ≤ n) {P : List Bool} (hP : P ∈ Dyck n k) :
    rc P = P ↔ mirror (encW P) = encW P := by
  obtain ⟨p0, v0, D, -, -⟩ := encW_mem hn hP
  simp only [Dyck, Finset.mem_filter, mem_bwords] at hP
  have hne : P ≠ [] := by rintro rfl; simp at hP; omega
  have hhead := dk_head P hne hP.2.1
  obtain ⟨r1, r2⟩ := flags_rc hhead D.hp D.hv
  have hl : p0.length = v0.length := by rw [D.lp, D.lv]
  rw [encW_eq D, mirror_zipWith p0 v0 hl]
  constructor
  · intro h
    have e1 := r1; have e2 := r2
    rw [h, D.hp] at e1; rw [h, D.hv] at e2
    simp only [List.append_cancel_right_eq] at e1 e2
    rw [← e1, ← e2]
  · intro h
    obtain ⟨m1, m2⟩ := map_zipWith_letter p0 v0 hl
    obtain ⟨n1, n2⟩ := map_zipWith_letter v0.reverse p0.reverse (by simp [hl])
    have e1 : v0.reverse = p0 := by rw [← n1, h, m1]
    have e2 : p0.reverse = v0 := by rw [← n2, h, m2]
    have hrc_head : (rc P).head? = some true := by
      obtain ⟨Q, hQ⟩ := dk_last P hne hP.2.1
      rw [hQ]; simp [rc]
    rw [← dec_flags (rc P) true (Or.inr hrc_head), r1, r2, e1, e2, ← D.hp, ← D.hv,
      dec_flags P true (Or.inr hhead)]

/-- **Main theorem.** For `n ≥ 1`: the sum of `(-1)^maj` over Dyck paths of semilength `n` with `k` valleys
equals the number of symmetric ones. With `q^{k(k+1)} N_{n,k}(q) = ∑ q^maj` (Fürlinger and Hofbauer 1985)
this is `N_{n,k}(-1) = #` symmetric Dyck paths with `k + 1` peaks. -/
theorem signed_dyck (n k : ℕ) (hn : 1 ≤ n) :
    ∑ P ∈ Dyck n k, (-1 : ℤ) ^ maj P = ((Dyck n k).filter (fun P => rc P = P)).card := by
  have inv1 : ∀ P (hP : P ∈ Dyck n k), decW (encW P) = P := by
    intro P hP
    obtain ⟨p0, v0, D, -, hdec⟩ := encW_mem hn hP
    obtain ⟨m1, m2⟩ := map_zipWith_letter p0 v0 (by rw [D.lp, D.lv])
    rw [decW, encW_eq D, m1, m2, ← hdec]
  have step1 : ∑ P ∈ Dyck n k, (-1 : ℤ) ^ maj P = ∑ w ∈ Mot (n - 1) (2 * k), sgnFrom 1 w := by
    refine Finset.sum_bij' (fun P _ => encW P) (fun w _ => decW w) ?_ ?_ ?_ ?_ ?_
    · intro P hP; obtain ⟨_, _, _, h, _⟩ := encW_mem hn hP; exact h
    · intro w hw; exact (decW_mem hn hw).1
    · intro P hP; exact inv1 P hP
    · intro w hw; exact (decW_mem hn hw).2
    · intro P hP; exact maj_sign hn hP
  have step3 : ((Dyck n k).filter (fun P => rc P = P)).card = (Sym (n - 1) (2 * k)).card := by
    refine Finset.card_bij' (fun P _ => encW P) (fun w _ => decW w) ?_ ?_ ?_ ?_
    · intro P hP
      rw [Finset.mem_filter] at hP
      obtain ⟨_, _, _, h, _⟩ := encW_mem hn hP.1
      exact Finset.mem_filter.2 ⟨h, (sym_iff hn hP.1).1 hP.2⟩
    · intro w hw
      rw [Sym, Finset.mem_filter] at hw
      obtain ⟨h1, h2⟩ := decW_mem hn hw.1
      exact Finset.mem_filter.2 ⟨h1, (sym_iff hn h1).2 (by rw [h2]; exact hw.2)⟩
    · intro P hP; exact inv1 P (Finset.mem_filter.1 hP).1
    · intro w hw; exact (decW_mem hn (Finset.mem_filter.1 hw).1).2
  rw [step1, signed_sum_eq_card_sym, step3]

end QNarayana
