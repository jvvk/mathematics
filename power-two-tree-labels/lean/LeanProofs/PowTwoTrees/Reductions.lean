import LeanProofs.PowTwoTrees.Basic

/-!
# The reductions: building a labelling of a tree from labellings of smaller trees

* `parity`: branch sizes equal (Machacek) or differing by one: odd labels on the larger branch, even on the
  smaller.
* `mersenne`: a branch of size `2^k - 1` (Machacek).
* `prefix_case1`, `prefix_case2`: one branch is a unary chain of `d` vertices above a subtree.
* `two_prefix_case1`, `two_prefix_case2`: both branches are unary chains above subtrees.
-/

namespace PowTwoTrees

open Finset

/-! ## Label sets -/

/-- `{c, c + 2, …, c + 2(m - 1)}`: the labels of a branch scaled by 2 and shifted by `c`. -/
def aff (c m : ℕ) : Finset ℕ := (range m).image (fun z => 2 * z + c)

lemma mem_aff {c m x : ℕ} : x ∈ aff c m ↔ c ≤ x ∧ (x - c) % 2 = 0 ∧ (x - c) / 2 < m := by
  simp only [aff, mem_image, mem_range]
  constructor
  · rintro ⟨z, hz, rfl⟩; omega
  · rintro ⟨h1, h2, h3⟩; exact ⟨(x - c) / 2, h3, by omega⟩

/-- `{c, …, c + m - 1}`: the labels of a branch shifted by `c`. -/
lemma mem_image_add_range {c m x : ℕ} : x ∈ (range m).image (· + c) ↔ c ≤ x ∧ x < c + m := by
  simp only [mem_image, mem_range]
  constructor
  · rintro ⟨z, hz, rfl⟩; omega
  · rintro ⟨h1, h2⟩; exact ⟨x - c, by omega, by omega⟩

/-- A labelled tree, doubled and shifted. -/
lemma Labelled.aff {t : BT} (h : Labelled t) (c : ℕ) : Fits t (PowTwoTrees.aff c t.size) c := by
  have := (h.double).shift c
  simpa [PowTwoTrees.aff, Finset.image_image, Function.comp_def] using this

/-- A labelled tree, shifted. -/
lemma Labelled.shift' {t : BT} (h : Labelled t) (c : ℕ) : Fits t ((range t.size).image (· + c)) c := by
  simpa using h.shift c

/-! ## Equal or nearly equal branches; a branch of size `2^k - 1` -/

/-- Machacek's equal-branch reduction, extended to branch sizes differing by one. -/
theorem parity {a b : BT} (ha : Labelled a) (hb : Labelled b)
    (hsize : a.size = b.size ∨ a.size = b.size + 1) : Labelled (.two a b) := by
  have h := Fits.two 0 1 (r := 0) (by rw [show (0 : ℕ) + 2 ^ 0 = 1 by norm_num]; exact ha.aff 1)
    (by rw [show (0 : ℕ) + 2 ^ 1 = 2 by norm_num]; exact hb.aff 2)
    (by rw [disjoint_left]; intro x h1 h2; rw [mem_aff] at h1 h2; omega)
    (by rw [mem_aff]; omega) (by rw [mem_aff]; omega)
  have e : insert 0 (aff 1 a.size ∪ aff 2 b.size) = range (BT.two a b).size := by
    ext x
    simp only [mem_insert, mem_union, mem_aff, mem_range, BT.size]
    omega
  unfold Labelled
  rwa [e] at h

/-- A root with a single child: label the child 1 and shift its subtree by 1. -/
theorem unary_root {c : BT} (hc : Labelled c) : Labelled (.one c) := by
  have h := Fits.one (r := 0) 0 (by rw [show (0 : ℕ) + 2 ^ 0 = 1 by norm_num]; exact hc.shift' 1)
    (by rw [mem_image_add_range]; omega)
  have e : insert 0 ((range c.size).image (· + 1)) = range (BT.one c).size := by
    ext x
    simp only [mem_insert, mem_image_add_range, mem_range, BT.size]
    omega
  unfold Labelled
  rwa [e] at h

/-- Machacek's reduction for a branch of size `2^k - 1`. -/
theorem mersenne {a b : BT} (ha : Labelled a) (hb : Labelled b) (k : ℕ)
    (hsize : a.size + 1 = 2 ^ k) : Labelled (.two a b) := by
  have hk := Nat.two_pow_pos k
  have h := Fits.two 0 k (r := 0) (by rw [show (0 : ℕ) + 2 ^ 0 = 1 by norm_num]; exact ha.shift' 1)
    (by rw [zero_add]; exact hb.shift' (2 ^ k))
    (by rw [disjoint_left]; intro x h1 h2; rw [mem_image_add_range] at h1 h2; omega)
    (by rw [mem_image_add_range]; omega) (by rw [mem_image_add_range]; omega)
  have e : insert 0 ((range a.size).image (· + 1) ∪ (range b.size).image (· + 2 ^ k)) =
      range (BT.two a b).size := by
    ext x
    simp only [mem_insert, mem_union, mem_image_add_range, mem_range, BT.size]
    omega
  unfold Labelled
  rwa [e] at h

/-! ## Unary prefixes -/

/-- `pre d c`: a chain of `d` vertices, each with one child, above the tree `c`. -/
def BT.pre : ℕ → BT → BT
  | 0, c => c
  | d + 1, c => .one (BT.pre d c)

lemma BT.size_pre (d : ℕ) (c : BT) : (BT.pre d c).size = c.size + d := by
  induction d with
  | zero => rfl
  | succ d ih => simp [BT.pre, BT.size, ih]; omega

/-- A chain of `d + 1` vertices labelled `u, …, u + d`, above a tree whose root is `u + d + 2^k`. -/
lemma fits_pre (k : ℕ) :
    ∀ (d u : ℕ) (c : BT) (C : Finset ℕ), Fits c C (u + d + 2 ^ k) → (∀ x ∈ C, u + d < x) →
      Fits (BT.pre (d + 1) c) (C ∪ Icc u (u + d)) u := by
  intro d
  induction d with
  | zero =>
    intro u c C hc hC
    have hu : u ∉ C := fun h => by have := hC u h; omega
    have := Fits.one k (by simpa using hc) hu
    have e : insert u C = C ∪ Icc u (u + 0) := by
      rw [add_zero, Finset.Icc_self, Finset.union_comm, ← Finset.insert_eq]
    rw [e] at this
    simpa [BT.pre] using this
  | succ d ih =>
    intro u c C hc hC
    have h1 := ih (u + 1) c C (by rw [show u + 1 + d = u + (d + 1) by ring]; exact hc)
      (fun x hx => by have := hC x hx; omega)
    have hu : u ∉ C ∪ Icc (u + 1) (u + 1 + d) := by
      simp only [mem_union, mem_Icc, not_or, not_and, not_le]
      exact ⟨(fun h => by have := hC u h; omega), (fun h => by omega)⟩
    have h2 := Fits.one 0 (by simpa using h1) hu
    have e : insert u (C ∪ Icc (u + 1) (u + 1 + d)) = C ∪ Icc u (u + (d + 1)) := by
      rw [← Finset.union_insert, show u + 1 + d = u + (d + 1) by ring,
        Finset.insert_Icc_add_one_left_eq_Icc (by omega)]
    rw [e] at h2
    simpa [BT.pre] using h2

/-- One branch is `d ≥ 1` unary vertices above `c`; the other is `b`. Case 1: `|c| ∈ {|b|, |b| + 1}` and
`d + 2` is a power of two. -/
theorem prefix_case1 {c b : BT} (hc : Labelled c) (hb : Labelled b) (d m : ℕ) (hd : 1 ≤ d)
    (hsize : c.size = b.size ∨ c.size = b.size + 1) (hm : d + 2 = 2 ^ m) :
    Labelled (.two (BT.pre d c) b) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hA := fits_pre 0 d' 1 c (aff (d' + 2) c.size)
    (by rw [show 1 + d' + 2 ^ 0 = d' + 2 by ring]; exact hc.aff _)
    (fun x hx => by rw [mem_aff] at hx; omega)
  have hB : Fits b (aff (d' + 3) b.size) (0 + 2 ^ m) := by
    have e : 0 + 2 ^ m = d' + 3 := by omega
    rw [e]; exact hb.aff _
  have h := Fits.two 0 m (by simpa using hA) hB
    (by rw [disjoint_left]; intro x h1 h2
        simp only [mem_union, mem_aff, mem_Icc] at h1 h2; omega)
    (by simp only [mem_union, mem_aff, mem_Icc]; omega) (by rw [mem_aff]; omega)
  have e : insert 0 ((aff (d' + 2) c.size ∪ Icc 1 (1 + d')) ∪ aff (d' + 3) b.size) =
      range (BT.two (BT.pre (d' + 1) c) b).size := by
    ext x
    simp only [mem_insert, mem_union, mem_aff, mem_Icc, mem_range, BT.size, BT.size_pre]
    omega
  unfold Labelled
  rwa [e] at h

/-- Case 2: `|b| ∈ {|c|, |c| + 1}` and `d + 1` is a power of two. -/
theorem prefix_case2 {c b : BT} (hc : Labelled c) (hb : Labelled b) (d m : ℕ) (hd : 1 ≤ d)
    (hsize : b.size = c.size ∨ b.size = c.size + 1) (hm : d + 1 = 2 ^ m) :
    Labelled (.two (BT.pre d c) b) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have hA := fits_pre 1 d' 1 c (aff (d' + 3) c.size)
    (by rw [show 1 + d' + 2 ^ 1 = d' + 3 by ring]; exact hc.aff _)
    (fun x hx => by rw [mem_aff] at hx; omega)
  have hB : Fits b (aff (d' + 2) b.size) (0 + 2 ^ m) := by
    have e : 0 + 2 ^ m = d' + 2 := by omega
    rw [e]; exact hb.aff _
  have h := Fits.two 0 m (by simpa using hA) hB
    (by rw [disjoint_left]; intro x h1 h2
        simp only [mem_union, mem_aff, mem_Icc] at h1 h2; omega)
    (by simp only [mem_union, mem_aff, mem_Icc]; omega) (by rw [mem_aff]; omega)
  have e : insert 0 ((aff (d' + 3) c.size ∪ Icc 1 (1 + d')) ∪ aff (d' + 2) b.size) =
      range (BT.two (BT.pre (d' + 1) c) b).size := by
    ext x
    simp only [mem_insert, mem_union, mem_aff, mem_Icc, mem_range, BT.size, BT.size_pre]
    omega
  unfold Labelled
  rwa [e] at h

/-- Both branches are unary chains, of `d ≥ 1` and `e ≥ 1` vertices, above `a` and `b`; `d + 1` is a power
of two. Case 1: `|a| ∈ {|b|, |b| + 1}` and `e + 1` is a power of two. -/
theorem two_prefix_case1 {a b : BT} (ha : Labelled a) (hb : Labelled b) (d e m p : ℕ) (hd : 1 ≤ d)
    (he : 1 ≤ e) (hsize : a.size = b.size ∨ a.size = b.size + 1) (hm : d + 1 = 2 ^ m)
    (hp : e + 1 = 2 ^ p) : Labelled (.two (BT.pre d a) (BT.pre e b)) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  -- labels: root 0; first chain 1..d; second chain d+1..D; A at D+1+2α; B at D+2+2β (D = d + e)
  have hA := fits_pre p d' 1 a (aff (d' + e' + 3) a.size)
    (by rw [show 1 + d' + 2 ^ p = d' + e' + 3 by omega]; exact ha.aff _)
    (fun x hx => by rw [mem_aff] at hx; omega)
  have hB := fits_pre 1 e' (d' + 2) b (aff (d' + e' + 4) b.size)
    (by rw [show d' + 2 + e' + 2 ^ 1 = d' + e' + 4 by ring]; exact hb.aff _)
    (fun x hx => by rw [mem_aff] at hx; omega)
  have hB' : Fits (BT.pre (e' + 1) b) (aff (d' + e' + 4) b.size ∪ Icc (d' + 2) (d' + 2 + e'))
      (0 + 2 ^ m) := by
    have e : 0 + 2 ^ m = d' + 2 := by omega
    rw [e]; exact hB
  have h := Fits.two 0 m (by simpa using hA) hB'
    (by rw [disjoint_left]; intro x h1 h2
        simp only [mem_union, mem_aff, mem_Icc] at h1 h2; omega)
    (by simp only [mem_union, mem_aff, mem_Icc]; omega)
    (by simp only [mem_union, mem_aff, mem_Icc]; omega)
  have eq : insert 0 ((aff (d' + e' + 3) a.size ∪ Icc 1 (1 + d')) ∪
      (aff (d' + e' + 4) b.size ∪ Icc (d' + 2) (d' + 2 + e'))) =
      range (BT.two (BT.pre (d' + 1) a) (BT.pre (e' + 1) b)).size := by
    ext x
    simp only [mem_insert, mem_union, mem_aff, mem_Icc, mem_range, BT.size, BT.size_pre]
    omega
  unfold Labelled
  rwa [eq] at h

/-- Case 2: `|b| ∈ {|a|, |a| + 1}` and `e + 2` is a power of two. -/
theorem two_prefix_case2 {a b : BT} (ha : Labelled a) (hb : Labelled b) (d e m p : ℕ) (hd : 1 ≤ d)
    (he : 1 ≤ e) (hsize : b.size = a.size ∨ b.size = a.size + 1) (hm : d + 1 = 2 ^ m)
    (hp : e + 2 = 2 ^ p) : Labelled (.two (BT.pre d a) (BT.pre e b)) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  -- labels: root 0; first chain 1..d; second chain d+1..D; A at D+2+2α; B at D+1+2β
  have hA := fits_pre p d' 1 a (aff (d' + e' + 4) a.size)
    (by rw [show 1 + d' + 2 ^ p = d' + e' + 4 by omega]; exact ha.aff _)
    (fun x hx => by rw [mem_aff] at hx; omega)
  have hB := fits_pre 0 e' (d' + 2) b (aff (d' + e' + 3) b.size)
    (by rw [show d' + 2 + e' + 2 ^ 0 = d' + e' + 3 by ring]; exact hb.aff _)
    (fun x hx => by rw [mem_aff] at hx; omega)
  have hB' : Fits (BT.pre (e' + 1) b) (aff (d' + e' + 3) b.size ∪ Icc (d' + 2) (d' + 2 + e'))
      (0 + 2 ^ m) := by
    have e : 0 + 2 ^ m = d' + 2 := by omega
    rw [e]; exact hB
  have h := Fits.two 0 m (by simpa using hA) hB'
    (by rw [disjoint_left]; intro x h1 h2
        simp only [mem_union, mem_aff, mem_Icc] at h1 h2; omega)
    (by simp only [mem_union, mem_aff, mem_Icc]; omega)
    (by simp only [mem_union, mem_aff, mem_Icc]; omega)
  have eq : insert 0 ((aff (d' + e' + 4) a.size ∪ Icc 1 (1 + d')) ∪
      (aff (d' + e' + 3) b.size ∪ Icc (d' + 2) (d' + 2 + e'))) =
      range (BT.two (BT.pre (d' + 1) a) (BT.pre (e' + 1) b)).size := by
    ext x
    simp only [mem_insert, mem_union, mem_aff, mem_Icc, mem_range, BT.size, BT.size_pre]
    omega
  unfold Labelled
  rwa [eq] at h

end PowTwoTrees
