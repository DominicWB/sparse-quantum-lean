import MeasuredUnitaryLowerBound.OperatorNorm.Notion
import DeferredMeasurementLowerBounds.Deferral.Theorem

set_option autoImplicit false

/-!
# The operator-norm notion through the deferred unitary

"Purification and deferred measurement include adaptive and randomised algorithms"
(proof of `hsl:lem:precision` of the manuscript). The deferral of a measured
algorithm `M` (`DeferredMeasurementLowerBounds.Deferral`) is one unitary program on the
workspace with record registers, run on the fresh record and read through the isometric output
`deferredOutput M`. Its decoded map `deferredMap counted M x`
(`φ ↦ amplitude counted M x φ`) is a purification of the output of `M`: its record components
form a Kraus family of `successDensity`
(`DeferredMeasurementLowerBounds.Deferral.sum_pure_amplitude`)
and its squared norm is the success probability (`successMass_eq_norm_deferredMap`). If the
deferred unitary, decoded and read, is within operator norm `ε` of `U ⊗ γ` on the encoded inputs,
with success probability `‖ψ‖²`, then `M` implements `U` within operator norm `ε`
(`normImplements_of_deferred`).
-/

namespace MeasuredUnitaryLowerBound.OperatorNorm

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout ContinuousLinearMap
open DeferredMeasurementLowerBounds.Model DeferredMeasurementLowerBounds.Deferral
open scoped InnerProduct InnerProductSpace

variable {S G E K X L : Type*} [Fintype S] [DecidableEq S]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {O : L → X → K →L[ℂ] K}

/-- **The decoded deferred map** of a measured algorithm on the instance `x`: the fresh record,
the deferred program and the adjoint of the deferred output. -/
def deferredMap (counted : L → Prop) [DecidablePred counted] (M : Measured O E) (x : X) :
    K →L[ℂ] Joint (DOut M) E :=
  (deferredOutput M)† ∘L (deferredProgram counted M).eval x ∘L freshInj M.width M.depth

/-- The decoded deferred map gives the deferral's decoded final vector. -/
theorem deferredMap_apply (counted : L → Prop) [DecidablePred counted] (M : Measured O E)
    (x : X) (φ : K) : deferredMap counted M x φ = amplitude counted M x φ := by
  rfl

/-- The success probability of `M` is the squared norm of the decoded deferred map: the map
form of `DeferredMeasurementLowerBounds.Deferral.norm_sq_amplitude`. -/
theorem successMass_eq_norm_deferredMap (counted : L → Prop) [DecidablePred counted]
    (M : Measured O E) (x : X) (φ : K) :
    M.successMass x φ = ‖deferredMap counted M x φ‖ ^ 2 := by
  rw [deferredMap_apply, norm_sq_amplitude]

omit [DecidableEq S] [CompleteSpace G] in
/-- **The deferred form of the operator-norm notion.** If the decoded deferred map of `M` on
the encoded inputs, read through `e` record by record, is within operator norm `ε` of `U ⊗ γ`
for a unit garbage vector `γ` over the output records, and `M` succeeds with probability `‖ψ‖²`
on `J ψ`, then `M` implements `U` within operator-norm error `ε` on the instance `x`. -/
theorem normImplements_of_deferred (counted : L → Prop) [DecidablePred counted]
    (M : Measured O E) (J : EuclideanSpace ℂ S →L[ℂ] K) (e : E →L[ℂ] SysGarb S G) (x : X)
    (U : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) (γ : Joint (DOut M) G) (hγ : ‖γ‖ = 1)
    (hmass : ∀ ψ, M.successMass x (J ψ) = ‖ψ‖ ^ 2) {ε : ℝ}
    (h : ‖readKraus e (fun r => Joint.proj r ∘L deferredMap counted M x ∘L J) -
      garbageTensor U γ‖ ≤ ε) :
    NormImplements M J e x U ε := by
  refine ⟨DOut M, inferInstance, fun r => Joint.proj r ∘L deferredMap counted M x ∘L J, γ, hγ,
    fun ψ => ?_, hmass, h⟩
  rw [← sum_pure_amplitude (counted := counted) M x (J ψ)]
  simp only [ContinuousLinearMap.comp_apply, Joint.proj_apply, deferredMap_apply]

end
end MeasuredUnitaryLowerBound.OperatorNorm
