import SparseODE.ODEPublicGaussianEndpoint

/-!
# Public positive-time ODE solver outcome

The public result existentially packages the physical schedule and encoding,
while retaining the complete primitive trial certificate. The internal
normalization scale is absent from the statement. Frequency and source
cardinalities, coefficients and the target are the explicit public choices.

The conclusion has the existing pointwise scope: for each promised input it
provides trial circuits that are globally unitary. Equality of the trial
constructors across different input witnesses is a separate uniformity
result; this predicate does not change that quantifier order.

-/

namespace SparseHamiltonian.ODEPublicGaussianEndpoint

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Full public trial outcome for the actual ODE solution, with the physical
schedule and encoding packaged existentially. No correctness or complexity
field of the underlying primitive trial certificate is discarded. -/
def Outcome (D : Data X n Z s) (etaH etaD T g ε : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (v b seed : EuclideanSpace ℂ n) (x : X) : Prop :=
  ∃ (Tslots d : ℕ)
    (E : ODEFinalNativeSource.SourceSpace (Fin (gridSize D T g ε) ⊕ Bool) n
        (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε)) →L[ℂ]
      ODEFinalNativeSource.MatrixSpace (Fin (gridSize D T g ε) ⊕ Bool) n Z
        (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε)) Tslots d),
    ODEPrimitiveEndpoint.TrialOutcome
      (ι := Fin (gridSize D T g ε) ⊕ Bool) D (Sum.inr false)
      (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
      Tslots d J₀ Jb E
      (ODESourceBranches.sourceVector v b T
        (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε)))
      (ODECoefficientPadding.paddedCoefficient (coefficients D T g ε) 3)
      seed (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T) x
      (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
      (ImprovedODEQueryBudget.logBudget g ε) g ε

/-- The implemented schedule and canonical encoding witness the public
outcome, with the complete trial certificate unchanged. -/
theorem outcome_of_scale (D : Data X n Z s) (γ etaH etaD T g ε : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (v b seed : EuclideanSpace ℂ n) (x : X)
    (h : ODEActualPrimitiveEndpoint.OutcomeAtScale
      (ι := Fin (gridSize D T g ε)) D γ etaH etaD T g ε J₀ Jb
      (coefficients D T g ε) v b seed x) :
    Outcome D etaH etaD T g ε J₀ Jb v b seed x := by
  unfold Outcome
  refine ⟨ODENativeSimulation.slots (s : ℝ) γ
      (etaH + ImprovedODEQueryBudget.radius g ε * etaD) T
      (ImprovedODEQueryBudget.precision g ε),
    ODENativeSimulation.degree (s : ℝ) γ
      (etaH + ImprovedODEQueryBudget.radius g ε * etaD) T
      (ImprovedODEQueryBudget.precision g ε),
    ODENativeSourceCertificate.encoding
      (σ := Option (Fin (ODEPublicSourceMesh.meshSize D T
        (ImprovedODEQueryBudget.precision g ε))))
      (ι := Fin (gridSize D T g ε) ⊕ Bool)
      D (none, Sum.inr false) γ
      (etaH + ImprovedODEQueryBudget.radius g ε * etaD) T
      (ImprovedODEQueryBudget.precision g ε), ?_⟩
  exact h

/-- Public positive-time, positive-effective-energy solver conclusion. All
analytic approximation and finite-grid inputs have been discharged. The
remaining hypotheses describe only the sparse access, physical matrix,
public numerical bounds and the supplied initial/source preparation
interfaces. Success, normalized output accuracy and both query counts are
exactly those in the full primitive trial certificate. -/
theorem positive_time_solver (D : Data X n Z s)
    (etaH etaD T g ε : ℝ) (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD)
    (hρ : 0 < etaH + ImprovedODEQueryBudget.radius g ε * etaD)
    (hT : 0 < T) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (x : X) (v : EuclideanSpace ℂ n),
      0 ≤ (inner ℂ v
        (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) v)).re) :
    ∀ J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n,
      (∀ y, IsUnitary (J₀ y)) → (∀ y, IsUnitary (Jb y)) →
      ∀ v b seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∀ x : X,
          (v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v) →
          (b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b) →
          ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
          ‖v‖ + T * ‖b‖ ≤
            g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ →
          Outcome D etaH etaD T g ε J₀ Jb v b seed x := by
  obtain ⟨γ, _hγ, _hγOne, _hWidth, hTrials⟩ := actual_ode_trials
    D etaH etaD T g ε hH hDiss hρ hT hg hε hεHalf hrH hcH hrD hcD hPSD
  intro J₀ Jb hJ₀ hJb v b seed hSeed x hInitial hForcing hTarget hBudget
  exact outcome_of_scale D γ etaH etaD T g ε J₀ Jb v b seed x
    (hTrials J₀ Jb hJ₀ hJb v b seed hSeed x hInitial hForcing hTarget hBudget)

end
end SparseHamiltonian.ODEPublicGaussianEndpoint
