import Mathlib

/-!
# Orbits of linear extensions (MO 516140): the general facts

A linear extension of a finite poset `α` is an order-preserving bijection `σ : α ≃ Fin n` onto
the chain `n = #α` (Stanley, EC1 §3.5). The automorphism group `α ≃o α` acts by
`φ • σ = σ ∘ φ⁻¹`. The action is free, so every orbit has `#Aut(α)` elements and
`e(α) = #Aut(α) · f(α)`, where `f(α)` is the number of orbits.
-/

namespace Orbits516140

open MulAction

variable (α : Type*) [Fintype α] [PartialOrder α]

/-- Linear extensions: order-preserving bijections onto the chain `Fin (card α)`. -/
def LinExt : Type _ := {σ : α ≃ Fin (Fintype.card α) // StrictMono σ}

variable {α}

instance : MulAction (α ≃o α) (LinExt α) where
  smul φ σ := ⟨φ.symm.toEquiv.trans σ.1, σ.2.comp φ.symm.strictMono⟩
  one_smul σ := by
    apply Subtype.ext; apply Equiv.ext; intro x; rfl
  mul_smul φ ψ σ := by
    apply Subtype.ext; apply Equiv.ext; intro x; rfl

@[simp] theorem smul_apply (φ : α ≃o α) (σ : LinExt α) (x : α) :
    (φ • σ).1 x = σ.1 (φ.symm x) := rfl

/-- The action of `Aut(P)` on linear extensions is free. -/
theorem smul_eq_self_iff (φ : α ≃o α) (σ : LinExt α) : φ • σ = σ ↔ φ = 1 := by
  constructor
  · intro h
    ext x
    have hx : σ.1 (φ.symm (φ x)) = σ.1 (φ x) := by
      rw [← smul_apply, h]
    simpa using (σ.1.injective hx).symm
  · rintro rfl; exact one_smul _ _

theorem stabilizer_eq_bot (σ : LinExt α) : stabilizer (α ≃o α) σ = ⊥ := by
  ext φ; simp [mem_stabilizer_iff, smul_eq_self_iff]

/-- Each orbit is in bijection with the group (orbit-stabiliser, trivial stabiliser). -/
noncomputable def orbitEquivAut (σ : LinExt α) : orbit (α ≃o α) σ ≃ (α ≃o α) :=
  have : Unique (stabilizer (α ≃o α) σ) := by
    rw [stabilizer_eq_bot]; exact Subgroup.instUniqueSubtypeMemBot
  (Equiv.prodUnique _ _).symm.trans (orbitProdStabilizerEquivGroup (α ≃o α) σ)

/-- The number of orbits of `Aut(P)` on linear extensions, `f(P)` in the question. -/
noncomputable def orbitCount (α : Type*) [Fintype α] [PartialOrder α] : ℕ :=
  Nat.card (orbitRel.Quotient (α ≃o α) (LinExt α))

instance : Finite (LinExt α) := by unfold LinExt; infer_instance

instance {β : Type*} [PartialOrder β] [Finite β] : Finite (β ≃o β) :=
  Finite.of_injective (fun φ : β ≃o β => (φ : β → β)) fun _ _ h => OrderIso.ext h

/-- `e(P) = #Aut(P) · f(P)`. -/
theorem card_linExt_eq :
    Nat.card (LinExt α) = Nat.card (α ≃o α) * orbitCount α := by
  classical
  have e : LinExt α ≃ orbitRel.Quotient (α ≃o α) (LinExt α) × (α ≃o α) :=
    (selfEquivSigmaOrbits (α ≃o α) (LinExt α)).trans <|
      (Equiv.sigmaCongrRight fun ω : orbitRel.Quotient (α ≃o α) (LinExt α) =>
        orbitEquivAut (Quotient.out ω)).trans
        (Equiv.sigmaEquivProd _ _)
  rw [Nat.card_congr e, Nat.card_prod, mul_comm, orbitCount]

/-- `#Aut(P)` divides `e(P)` for every finite poset. -/
theorem card_aut_dvd : Nat.card (α ≃o α) ∣ Nat.card (LinExt α) :=
  ⟨_, card_linExt_eq⟩

/-- `f(P) = e(P) / #Aut(P)`, as in the question. -/
theorem orbitCount_eq_div : orbitCount α = Nat.card (LinExt α) / Nat.card (α ≃o α) := by
  rw [card_linExt_eq, Nat.mul_div_cancel_left _ Nat.card_pos]

end Orbits516140
