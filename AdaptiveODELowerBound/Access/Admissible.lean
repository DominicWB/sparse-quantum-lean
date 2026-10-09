import AdaptiveODELowerBound.Access.Calls
import AdaptiveHamiltonianLowerBound.Access.HardData
import ODELowerBoundExtensions.Release.Registers

set_option autoImplicit false

/-!
# Call forms of the spectated native primitives are admissible

Manuscript lines 2388-2390 and 2594-2597 (Hamiltonian lower bound: "with inverses and coherent
controls"; inverse and controlled location calls reveal no hidden information) and lines
4105-4108 (the same access for the ODE class).

The adaptive Hamiltonian lower bound admits every label that is a native call
(`AdaptiveHamiltonianLowerBound.Access.NativeCall`: in a fixed isometric layout of the workspace
as spectator branches of the native space, every branch applies the identity, one native query
or its inverse) or an input-independent unitary (`Access.Admissible`). For data with
input-independent locators, every call form of every spectated native primitive is admissible
with the value-query weight (`admissible_callFamily_spec`): the plain and inverse value forms are
native calls in the layout `ℂ^Bool ⊗ ℂ^Ω ⊗ NSpace ≃ ℂ^{Bool × Ω} ⊗ NSpace`
(`Release.jointFlatten`), the controlled forms apply the identity on the branches with control
`0`, and the location forms are input-independent unitaries.

For the one-stage families of the ODE lower bound (`hamFamily D`, `Psd.heatFamily D`) the
sampled-time access is `specOracles (ι × Fin 1) D`, so their access and its call forms are
admissible for `D`, and the adaptive Hamiltonian lower bound applies to both.
-/

namespace AdaptiveODELowerBound.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit NativeSparseBlockEncoding
open AdaptiveHamiltonianLowerBound.Access (Admissible valueWeight)

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {s : ℕ}

/-- **Every call form of a spectated native primitive is admissible** with the value-query
weight, for data with input-independent locators: value forms are native calls (the controlled
ones with identity branches on control `0`), location forms are input-independent unitaries. -/
theorem admissible_callFamily_spec (Ω : Type) [Fintype Ω] (D : Data X N Z s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x') (c : Query × CallForm) :
    Admissible D (callFamily (specOracles Ω D) c) (valueWeight c.1) := by
  rcases c with ⟨q, f⟩
  cases q with
  | rowLocation =>
      refine Or.inr ⟨fun x x' => callFamily_const (fun x x' => ?_) f x x',
        fun x => callFamily_unitary (specOracles_unitary Ω D) _ x⟩
      simp only [specOracles, oracles, SparseFlagEmbedding.location, hrow x x']
  | columnLocation =>
      refine Or.inr ⟨fun x x' => callFamily_const (fun x x' => ?_) f x x',
        fun x => callFamily_unitary (specOracles_unitary Ω D) _ x⟩
      simp only [specOracles, oracles, SparseFlagEmbedding.location, hcol x x']
  | value =>
      cases f with
      | plain =>
          refine Or.inl ⟨⟨Bool × Ω, inferInstance,
            (ODELowerBoundExtensions.Release.jointFlatten Bool Ω _).symm,
            fun _ => some (.value, false), fun x => ?_⟩, le_rfl⟩
          ext Ψ c σ
          rfl
      | inverse =>
          refine Or.inl ⟨⟨Bool × Ω, inferInstance,
            (ODELowerBoundExtensions.Release.jointFlatten Bool Ω _).symm,
            fun _ => some (.value, true), fun x => ?_⟩, le_rfl⟩
          ext Ψ c σ
          simp only [callFamily, formOp, specOracles, Joint.star_fiber, Joint.fiber_apply]
          rfl
      | controlled =>
          refine Or.inl ⟨⟨Bool × Ω, inferInstance,
            (ODELowerBoundExtensions.Release.jointFlatten Bool Ω _).symm,
            fun σ => if σ.1 then some (.value, false) else none, fun x => ?_⟩, le_rfl⟩
          ext Ψ c σ
          cases c <;> simp only [callFamily, formOp, ctrlOp, MaskedProgram.masked_apply] <;> rfl
      | controlledInverse =>
          refine Or.inl ⟨⟨Bool × Ω, inferInstance,
            (ODELowerBoundExtensions.Release.jointFlatten Bool Ω _).symm,
            fun σ => if σ.1 then some (.value, true) else none, fun x => ?_⟩, le_rfl⟩
          ext Ψ c σ
          cases c <;>
            simp only [callFamily, formOp, ctrlOp, MaskedProgram.masked_apply, specOracles,
              Joint.star_fiber] <;> rfl

end

end AdaptiveODELowerBound.Access
