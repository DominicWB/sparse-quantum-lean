import SparseLowerBounds.Query.Joint
import SparseHamiltonian.OracleCircuit
import SparseHamiltonian.MaskedProgram
import SparseLowerBounds.Query.PhaseCircuit

set_option autoImplicit false

/-!
# The four call forms of an oracle label

Manuscript Section `odel:sec:main`, lines 4105-4108 ("Access is through a reversible value
oracle and in-place row/column locators, their inverses and controls, with a coherent time
address when needed"), and lines 4289-4294 and 2595-2597 (a value call, including its inverse
or controlled form, needs at most two Boolean queries).

For a labelled oracle family `O : L → X → W →L[ℂ] W`, the **call family** `callFamily O` has
the labels `L × CallForm` and acts on a control qubit times the workspace, `ℂ^Bool ⊗ W`:

* `plain`: `1 ⊗ O_l(x)`;
* `inverse`: `1 ⊗ O_l(x)†`;
* `controlled`: `|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ O_l(x)` (`ctrlOp`);
* `controlledInverse`: `|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ O_l(x)†`.

The controlled operator is the package's branch mask `SparseHamiltonian.MaskedProgram.masked`
with the identity mask on the control (`Joint Bool W` is `PiLp 2 (fun _ : Bool => W)`), so its
unitarity, adjoint and products are `masked_unitary`, `masked_adjoint` and `masked_mul`; the plain
form `1 ⊗ U` is `Joint.fiber`, the all-active mask
(`SparseLowerBounds.Helpers.Adaptive.Access.masked_true_eq_fiber`).

Since a program of the package (`MultiOracleCircuit.Program`) also has inverse calls, every
form of every label, and its inverse, is available to an algorithm over `callFamily O`, and
each call is counted with the weight of its label. Unitarity: `callFamily_unitary`.
-/

namespace AdaptiveODELowerBound.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit

/-- **The call forms** of one oracle label: the call, its inverse, its controlled form and its
controlled inverse. -/
inductive CallForm
  | plain
  | inverse
  | controlled
  | controlledInverse
  deriving DecidableEq

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **The controlled operator** `|0⟩⟨0| ⊗ 1 + |1⟩⟨1| ⊗ U` on control ⊗ workspace: the branch
mask `MaskedProgram.masked` with the identity mask on the control. -/
def ctrlOp (U : W →L[ℂ] W) : Joint Bool W →L[ℂ] Joint Bool W :=
  MaskedProgram.masked (fun c : Bool => c) U

/-- **The operator of a call form** on control ⊗ workspace. -/
def formOp : CallForm → (W →L[ℂ] W) → Joint Bool W →L[ℂ] Joint Bool W
  | .plain, U => Joint.fiber fun _ => U
  | .inverse, U => Joint.fiber fun _ => star U
  | .controlled, U => ctrlOp U
  | .controlledInverse, U => ctrlOp (star U)

/-- **The call family** of a labelled oracle family: every label in each of its four call forms,
on control ⊗ workspace. -/
def callFamily {L X : Type*} (O : L → X → W →L[ℂ] W) :
    L × CallForm → X → Joint Bool W →L[ℂ] Joint Bool W :=
  fun c x => formOp c.2 (O c.1 x)

/-- Every call form of a unitary is unitary. -/
theorem formOp_unitary (f : CallForm) {U : W →L[ℂ] W} (hU : IsUnitary U) :
    IsUnitary (formOp f U) := by
  have hU' : IsUnitary (star U) :=
    ⟨by rw [star_star]; exact hU.2, by rw [star_star]; exact hU.1⟩
  cases f
  · exact PhaseCircuit.isUnitary_fiber _ fun _ => hU
  · exact PhaseCircuit.isUnitary_fiber _ fun _ => hU'
  · exact MaskedProgram.masked_unitary _ U hU
  · exact MaskedProgram.masked_unitary _ _ hU'

/-- The call family of a unitary family is unitary. -/
theorem callFamily_unitary {L X : Type*} {O : L → X → W →L[ℂ] W}
    (hO : ∀ l x, IsUnitary (O l x)) (c : L × CallForm) (x : X) :
    IsUnitary (callFamily O c x) :=
  formOp_unitary c.2 (hO c.1 x)

/-- The call forms of an input-independent label are input-independent. -/
theorem callFamily_const {L X : Type*} {O : L → X → W →L[ℂ] W} {l : L}
    (hl : ∀ x x', O l x = O l x') (f : CallForm) (x x' : X) :
    callFamily O (l, f) x = callFamily O (l, f) x' := by
  simp only [callFamily, hl x x']

end

end AdaptiveODELowerBound.Access
