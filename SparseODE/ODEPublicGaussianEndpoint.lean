import SparseODE.ODEGaussianFiniteTableContinuation3

/-!
# Actual ODE trials with an explicit public Gaussian frequency table

The node set and Gaussian coefficients are fixed by the supplied sparse-data
scale, final time, normalization bound and precision. The finite LCHS
certificate is proved from dissipativity and then fed into the primitive
actual-solution endpoint. No finite-LCHS, truncated-integral or full-line
approximation premise is supplied by the caller.

This endpoint covers positive final time and positive effective energy.
The full trial conclusion preserves the earlier success, normalized-state
accuracy, primitive sparse-query and two source-query guarantees.

-/

namespace SparseHamiltonian.ODEPublicGaussianEndpoint

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Public Gaussian frequency-grid cardinality, independent of the unknown
matrix input, source vectors and branch duration. -/
def gridSize (D : Data X n Z s) (T g ε : ℝ) : ℕ :=
  ODEFiniteLCHSConstruction.gridSize D T
    (ODEGaussianKernel.lipschitzConstant (ODEGaussianParameters.width g ε))
    (Real.exp 1 / Real.pi) g ε

/-- The actual public frequency nodes used by the circuit. -/
def nodes (D : Data X n Z s) (T g ε : ℝ) : Fin (gridSize D T g ε) → ℝ :=
  ODEUniformQuadrature.node (-ImprovedODEQueryBudget.radius g ε)
    (ImprovedODEQueryBudget.radius g ε) (gridSize D T g ε)

/-- The actual public Gaussian coefficients, before mass-three padding. -/
def coefficients (D : Data X n Z s) (T g ε : ℝ) :
    Fin (gridSize D T g ε) → ℂ :=
  ODEUniformQuadrature.coefficient
    (ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε))
    (-ImprovedODEQueryBudget.radius g ε) (ImprovedODEQueryBudget.radius g ε)
    (gridSize D T g ε)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The explicit node type is nonempty even before parameter validity is used. -/
theorem gridSize_pos (D : Data X n Z s) (T g ε : ℝ) :
    0 < gridSize D T g ε :=
  ODEUniformQuadrature.meshSize_pos _ _ _ _

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- All finite-table hypotheses of the primitive solver follow from the
physical dissipativity promise and the public precision parameters. -/
theorem table_certificate (D : Data X n Z s)
    (hPSD : ∀ (x : X) (v : EuclideanSpace ℂ n), 0 ≤ (inner ℂ v
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) v)).re)
    (T g ε : ℝ) (hT : 0 ≤ T) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    0 < gridSize D T g ε ∧
      (∀ i : Fin (gridSize D T g ε),
        |nodes D T g ε i| ≤ ImprovedODEQueryBudget.radius g ε) ∧
      ODECoherentLCU.coefficientMass (coefficients D T g ε) ≤ 3 ∧
      (∀ x : X, ODEActualPrimitiveEndpoint.FiniteLCHS D
        (nodes D T g ε) (coefficients D T g ε) T g ε x) := by
  exact ODEGaussianFiniteTable.public_table_from_dissipativity
    D hPSD T g ε hT hg hε hεOne

/-- Positive-time actual ODE solution trials with no caller-supplied analytic
approximation certificate. The scale is chosen once before the source
interfaces, source vectors and unknown matrix input. The transparent
`OutcomeAtScale` conclusion retains globally unitary trial circuits,
mean heralded success at least one quarter, phase-adjusted output error at
most epsilon/500, matrix cost at most 318504960*g*queryShape, and at most
10*g calls to each of the two source interfaces. -/
theorem actual_ode_trials (D : Data X n Z s)
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
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n,
        (∀ y, IsUnitary (J₀ y)) → (∀ y, IsUnitary (Jb y)) →
        ∀ v b seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
          ∀ x : X,
            (v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v) →
            (b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b) →
            ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
            ‖v‖ + T * ‖b‖ ≤
              g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ →
            ODEActualPrimitiveEndpoint.OutcomeAtScale
              (ι := Fin (gridSize D T g ε)) D γ etaH etaD T g ε J₀ Jb
              (coefficients D T g ε) v b seed x := by
  have hεOne : ε ≤ 1 := hεHalf.trans (by norm_num)
  have hTable := table_certificate D hPSD T g ε hT.le hg hε hεOne
  obtain ⟨γ, hγ, hγOne, hWidth, hTrials⟩ :=
    ODEActualPrimitiveEndpoint.actual_ode_trials (ι := Fin (gridSize D T g ε))
      D etaH etaD T g ε hH hDiss hρ hT hg hε hεHalf hrH hcH hrD hcD hPSD
  refine ⟨γ, hγ, hγOne, hWidth, ?_⟩
  intro J₀ Jb hJ₀ hJb v b seed hSeed x hInitial hForcing hTarget hBudget
  exact hTrials (nodes D T g ε) (coefficients D T g ε)
    hTable.2.1 hTable.2.2.1 J₀ Jb hJ₀ hJb v b seed hSeed x
    hInitial hForcing hTarget hBudget (hTable.2.2.2 x)

end
end SparseHamiltonian.ODEPublicGaussianEndpoint
