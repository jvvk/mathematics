import LeanProofs.PentChains.Basic

/-!
# The inflation step

A layout is a list of items: glue numbers `g v`, and blocks `b c u r` meaning the block `t.map (f c)`
(`u = true`) or `s.map (f c)` (`u = false`), reversed if `r = true`. `assemble L s t` concatenates them.

`step`: if `s` is `Good n`, `t` is `Good (n+1)`, and the layout passes the Boolean check `validB r (n % 2) L`
(conditions S1-S6), then `assemble L s t` is `Good (49 n + r)`; here `26 ≤ r ≤ 74`, glue `1..25`. The check depends on `n`
only through its parity, so finitely many layouts serve every `n`.
-/

namespace PentChains

inductive Item where
  | g (v : ℤ)
  | b (c : ℤ) (useT : Bool) (rev : Bool)
  deriving DecidableEq, Repr

/-- The entries contributed by one item. -/
def piece (s t : List ℤ) : Item → List ℤ
  | .g v => [v]
  | .b c u r => if r then ((if u then t else s).map (f c)).reverse else (if u then t else s).map (f c)

def assemble (L : List Item) (s t : List ℤ) : List ℤ := L.flatMap (piece s t)

/-- `bEnd N = bEndP (N % 2)`. -/
def bEndP (q : ℕ) : ℤ := if q = 0 then 2 else 19

theorem bEnd_eq (N : ℕ) : bEnd N = bEndP (N % 2) := by unfold bEnd bEndP; rfl

/-- Parity of the length of the chain a block uses, given `p = n % 2`. -/
def lenPar (p : ℕ) (u : Bool) : ℕ := if u then (p + 1) % 2 else p

def firstE (p : ℕ) : Item → ℤ
  | .g v => v
  | .b c u r => if r then f c (bEndP (lenPar p u)) else f c 3

def lastE (p : ℕ) : Item → ℤ
  | .g v => v
  | .b c u r => if r then f c 3 else f c (bEndP (lenPar p u))

def key : Item → ℤ ⊕ ℤ
  | .g v => .inl v
  | .b c _ _ => .inr c

def isG : Item → Bool
  | .g _ => true
  | _ => false

def isB : Item → Bool
  | .b _ _ _ => true
  | _ => false

def isBT : Item → Bool
  | .b _ u _ => u
  | _ => false

/-- The top entry of a `t`-block is `49(n+1) + top offset`; S4 asks the top offset to be `≤ r - 49`. -/
def itemOK (r p : ℕ) : Item → Bool
  | .g v => decide (1 ≤ v) && decide (v ≤ 25)
  | .b c u _ => decide (-23 ≤ c) && decide (c ≤ 25) &&
      (!u || decide ((if (p + 1) % 2 = 1 then c else 2 - c) ≤ (r : ℤ) - 49))

def chainB (p : ℕ) : List Item → Bool
  | a :: b :: rest => otB (lastE p a + firstE p b) && chainB p (b :: rest)
  | _ => true

/-- The finite conditions on a layout (S1-S6). -/
def validB (r p : ℕ) (L : List Item) : Bool :=
  decide (26 ≤ r) && decide (r ≤ 74) && decide (L.map key).Nodup &&
  (L.filter isG).length == 25 && (L.filter isB).length == 49 && (L.filter isBT).length + 25 == r &&
  L.all (itemOK r p) && L.head? == some (.g 3) && L.getLast? == some (.g (bEndP ((p + r) % 2))) &&
  chainB p L

/-! ### Soundness -/

theorem chainB_sound (p : ℕ) : ∀ L : List Item, chainB p L = true →
    L.IsChain (fun a b => OT (lastE p a) (firstE p b))
  | [] , _ => List.IsChain.nil
  | [_], _ => List.isChain_singleton _
  | a :: b :: rest, h => by
      simp only [chainB, Bool.and_eq_true] at h
      exact List.IsChain.cons_cons (oddTri_of_otB h.1) (chainB_sound p (b :: rest) h.2)

section
variable {n : ℕ} {s t : List ℤ}

theorem mem_piece {x : ℤ} {it : Item} :
    x ∈ piece s t it ↔ match it with
      | .g v => x = v
      | .b c u _ => ∃ v ∈ (if u then t else s), f c v = x := by
  cases it with
  | g v => simp [piece]
  | b c u r => cases r <;> simp [piece]

theorem piece_ne_nil (hs : s ≠ []) (ht : t ≠ []) (it : Item) : piece s t it ≠ [] := by
  cases it with
  | g v => simp [piece]
  | b c u r => cases r <;> cases u <;> simp [piece, hs, ht]

theorem piece_head (hs : Good n s) (ht : Good (n + 1) t) (it : Item) :
    (piece s t it).head? = some (firstE (n % 2) it) := by
  have hsl : s.getLast? = some (bEndP (lenPar (n % 2) false)) := by
    rw [hs.last, bEnd_eq]; rfl
  have htl : t.getLast? = some (bEndP (lenPar (n % 2) true)) := by
    rw [ht.last, bEnd_eq]; simp [lenPar]
  cases it with
  | g v => simp [piece, firstE]
  | b c u r =>
    cases r <;> cases u <;>
      simp [piece, firstE, List.head?_map, List.head?_reverse, List.getLast?_map, hs.head, ht.head, hsl, htl]

theorem piece_last (hs : Good n s) (ht : Good (n + 1) t) (it : Item) :
    (piece s t it).getLast? = some (lastE (n % 2) it) := by
  have hsl : s.getLast? = some (bEndP (lenPar (n % 2) false)) := by
    rw [hs.last, bEnd_eq]; rfl
  have htl : t.getLast? = some (bEndP (lenPar (n % 2) true)) := by
    rw [ht.last, bEnd_eq]; simp [lenPar]
  cases it with
  | g v => simp [piece, lastE]
  | b c u r =>
    cases r <;> cases u <;>
      simp [piece, lastE, List.getLast?_map, List.getLast?_reverse, List.head?_map, hs.head, ht.head, hsl, htl]

theorem piece_chain (hs : Good n s) (ht : Good (n + 1) t) (it : Item) : (piece s t it).IsChain OT := by
  cases it with
  | g v => simp [piece]
  | b c u r =>
    have hx : (if u then t else s).IsChain OT := by cases u <;> simp [hs.chain, ht.chain]
    cases r
    · simpa [piece] using chain_map_f c hx
    · simpa [piece] using chain_reverse (chain_map_f c hx)

end

/-- Concatenating nonempty chains whose junctions are related gives a chain. -/
theorem isChain_flatMap {α β : Type*} {R : β → β → Prop} (F : α → List β) (hd tl : α → β) :
    ∀ L : List α, (∀ a ∈ L, F a ≠ []) → (∀ a ∈ L, (F a).head? = some (hd a)) →
      (∀ a ∈ L, (F a).getLast? = some (tl a)) → (∀ a ∈ L, (F a).IsChain R) →
      L.IsChain (fun a b => R (tl a) (hd b)) → (L.flatMap F).IsChain R
  | [], _, _, _, _, _ => by simp
  | a :: L, hne, hhd, htl, hc, hj => by
      rw [List.flatMap_cons]
      refine List.IsChain.append (hc a (by simp))
        (isChain_flatMap F hd tl L (fun x hx => hne x (by simp [hx])) (fun x hx => hhd x (by simp [hx]))
          (fun x hx => htl x (by simp [hx])) (fun x hx => hc x (by simp [hx])) hj.tail) ?_
      intro x hx y hy
      rw [htl a (by simp)] at hx
      cases L with
      | nil => simp at hy
      | cons b L' =>
        rw [List.flatMap_cons, List.head?_append_of_ne_nil _ (hne b (by simp)), hhd b (by simp)] at hy
        simp only [Option.mem_def, Option.some.injEq] at hx hy
        subst hx hy
        exact (List.isChain_cons_cons.1 hj).1

theorem length_assemble (n : ℕ) (s t : List ℤ) (hs : s.length = n) (ht : t.length = n + 1) :
    ∀ L : List Item, (assemble L s t).length =
      (L.filter isG).length + n * (L.filter isB).length + (L.filter isBT).length
  | [] => by simp [assemble]
  | it :: L => by
      have ih := length_assemble n s t hs ht L
      unfold assemble at ih ⊢
      rw [List.flatMap_cons, List.length_append, ih]
      cases it with
      | g v => simp [List.filter_cons, piece, isG, isB, isBT]; ring
      | b c u r => cases r <;> cases u <;> simp [List.filter_cons, piece, isG, isB, isBT, hs, ht] <;> ring

theorem step {n r : ℕ} {L : List Item} {s t : List ℤ} (hn : 1 ≤ n) (hs : Good n s) (ht : Good (n + 1) t)
    (hv : validB r (n % 2) L = true) : Good (49 * n + r) (assemble L s t) := by
  simp only [validB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at hv
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hr1, hr2⟩, hkey⟩, hG⟩, hB⟩, hBT⟩, hok⟩, hhead⟩, hlast⟩, hch⟩ := hv
  have hsne : s ≠ [] := by intro h; have := hs.len; simp [h] at this; omega
  have htne : t ≠ [] := by intro h; have := ht.len; simp [h] at this
  -- membership of the assembled list
  have hmem : ∀ x, x ∈ assemble L s t → ∃ it ∈ L, x ∈ piece s t it := by
    intro x hx; simpa [assemble, List.mem_flatMap] using hx
  -- bounds for block values
  have hval : ∀ c v : ℤ, -23 ≤ c → c ≤ 25 → 1 ≤ v → 26 ≤ f c v := by
    intro c v h1 h2 hv; unfold f; split_ifs <;> omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- nodup
    unfold assemble
    rw [List.nodup_flatMap]
    refine ⟨?_, ?_⟩
    · intro it hit
      cases it with
      | g v => simp [piece]
      | b c u r =>
        have hc := hok _ hit
        simp only [itemOK, Bool.and_eq_true, decide_eq_true_eq] at hc
        have hinj : Function.Injective (f c) := fun a b hab =>
          (f_window ⟨hc.1.1, hc.1.2⟩ ⟨hc.1.1, hc.1.2⟩ hab).1
        have hx : (if u then t else s).Nodup := by cases u <;> simp [hs.nodup, ht.nodup]
        cases r <;> simp [piece, List.nodup_reverse, hx.map hinj]
    · have hp : L.Pairwise (fun a b => key a ≠ key b) := by
        have := hkey; rw [List.Nodup, List.pairwise_map] at this; exact this
      refine List.Pairwise.imp_of_mem ?_ hp
      intro a b ha hb hab
      show List.Disjoint (piece s t a) (piece s t b)
      rw [List.disjoint_left]
      intro x hxa hxb
      rw [mem_piece] at hxa hxb
      have hoka := hok a ha; have hokb := hok b hb
      cases a with
      | g v =>
        cases b with
        | g w => simp only [key, ne_eq, Sum.inl.injEq] at hab; exact hab (hxa ▸ hxb)
        | b c u r =>
          obtain ⟨y, hy, rfl⟩ := hxb
          simp only [itemOK, Bool.and_eq_true, decide_eq_true_eq] at hoka hokb
          have hy1 : 1 ≤ y := by cases u <;> simp at hy <;> first | exact (ht.range y hy).1 | exact (hs.range y hy).1
          have := hval c y hokb.1.1 hokb.1.2 hy1; omega
      | b c u r =>
        obtain ⟨y, hy, rfl⟩ := hxa
        simp only [itemOK, Bool.and_eq_true, decide_eq_true_eq] at hoka
        have hy1 : 1 ≤ y := by cases u <;> simp at hy <;> first | exact (ht.range y hy).1 | exact (hs.range y hy).1
        cases b with
        | g w =>
          simp only [itemOK, Bool.and_eq_true, decide_eq_true_eq] at hokb
          have := hval c y hoka.1.1 hoka.1.2 hy1; omega
        | b c' u' r' =>
          obtain ⟨z, hz, hzy⟩ := hxb
          simp only [itemOK, Bool.and_eq_true, decide_eq_true_eq] at hokb
          have := (f_window ⟨hokb.1.1, hokb.1.2⟩ ⟨hoka.1.1, hoka.1.2⟩ hzy).2
          simp only [key, ne_eq, Sum.inr.injEq] at hab; exact hab this.symm
  · -- length
    rw [length_assemble n s t hs.len ht.len, hG, hB]; omega
  · -- range
    intro x hx
    obtain ⟨it, hit, hxp⟩ := hmem x hx
    rw [mem_piece] at hxp
    have hokit := hok it hit
    cases it with
    | g v =>
      simp only [itemOK, Bool.and_eq_true, decide_eq_true_eq] at hokit; subst hxp; omega
    | b c u r =>
      obtain ⟨y, hy, rfl⟩ := hxp
      simp only [itemOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hokit
      obtain ⟨⟨hc1, hc2⟩, htop⟩ := hokit
      cases u with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hy
        obtain ⟨hy1, hy2⟩ := hs.range y hy
        have := hval c y hc1 hc2 hy1
        constructor
        · omega
        · unfold f; split_ifs <;> push_cast <;> omega
      | true =>
        simp only [↓reduceIte] at hy
        obtain ⟨hy1, hy2⟩ := ht.range y hy
        have := hval c y hc1 hc2 hy1
        constructor
        · omega
        · rcases htop with h | h
          · simp at h
          · push_cast at hy2
            rcases lt_or_eq_of_le hy2 with hlt | heq
            · unfold f; split_ifs <;> push_cast <;> omega
            · subst heq
              unfold f
              have hpar : ((n : ℤ) + 1) % 2 = 1 ↔ (n % 2 + 1) % 2 = 1 := by omega
              split_ifs at h ⊢ <;> push_cast <;> omega
  · -- chain
    exact isChain_flatMap (piece s t) (firstE (n % 2)) (lastE (n % 2)) L
      (fun it _ => piece_ne_nil hsne htne it) (fun it _ => piece_head hs ht it)
      (fun it _ => piece_last hs ht it) (fun it _ => piece_chain hs ht it) (chainB_sound _ L hch)
  · -- head
    cases L with
    | nil => simp at hhead
    | cons a L' =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      simp [assemble, List.flatMap_cons, piece]
  · -- last
    have hL : L ≠ [] := by intro h; simp [h] at hhead
    obtain ⟨L', a, rfl⟩ := List.eq_nil_or_concat L |>.resolve_left hL
    simp only [List.concat_eq_append, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.some.injEq] at hlast
    subst hlast
    have hN : (49 * n + r) % 2 = (n % 2 + r) % 2 := by omega
    simp [assemble, List.flatMap_append, piece, bEnd_eq, hN]

end PentChains
