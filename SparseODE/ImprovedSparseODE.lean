import SparseODE.ODEUniformMain

/-!
# Improved sparse ODE preparation from the manuscript's normalization promise

These endpoints discharge the auxiliary public positivity assumptions from
the existence of one nonzero dissipative solution with the supplied source
norms. Their conclusion is the same uniform physical circuit certificate:
the circuit is chosen before every unknown matrix input and source direction.
The witness is used only to prove inequalities between public scalars.

The model counts primitive sparse-oracle and source-preparation calls.
Public query-free gates are exact and may be chosen noncomputably; no gate
synthesis cost or classical circuit-generation bound is asserted here.

-/

namespace SparseHamiltonian.ImprovedSparseODE

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- The complete uniform trial certificate, including all public boundary
cases, primitive query bounds, heralded success and normalized accuracy. -/
abbrev Outcome (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ODEUniformMain.Outcome D etaH etaD T g ε r₀ rb J₀ Jb seed

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- For a nonzero actual final solution, the manuscript's ratio promise is
exactly the source-mass inequality consumed by every trial certificate. -/
theorem ratio_budget_iff (D : Data X n Z s) (T g r₀ rb : ℝ)
    (x : X) (v b : EuclideanSpace ℂ n)
    (hTarget : ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0) :
    (r₀ + T * rb) /
        ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ ≤ g ↔
      r₀ + T * rb ≤
        g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ := by
  exact div_le_iff₀ (norm_pos_iff.mpr hTarget)

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 2000000 in
/-- Uniform preparation from a nonempty analytic promise class. Dissipativity
derives `g ≥ 1`, positive source mass, and nonnegative supplied norms; none
is an additional assumption. The witness does not enter the public outcome
or restrict the conclusion to that witness: one chosen circuit family still
serves every input satisfying the supplied source-preparation promises.

The inherited certificate has mean success at least one quarter, normalized
phase-adjusted error at most `ε / 500`, at most
`318504960 * g * queryShape` primitive matrix calls, and at most `10 * g`
calls to each source interface. -/
theorem solver_of_nonempty_promise (D : Data X n Z s)
    (etaH etaD T g ε r₀ rb : ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (x : X) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1)
    (hPromise : ∃ (x : X) (v b : EuclideanSpace ℂ n),
      ‖v‖ = r₀ ∧ ‖b‖ = rb ∧
      ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 ∧
      (r₀ + T * rb) /
        ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ ≤ g) :
    Outcome D etaH etaD T g ε r₀ rb J₀ Jb seed := by
  rcases hPromise with ⟨x, v, b, hv, hb, hTarget, hBudget⟩
  have h₀ : 0 ≤ r₀ := by
    rw [← hv]
    exact norm_nonneg v
  have hbNonneg : 0 ≤ rb := by
    rw [← hb]
    exact norm_nonneg b
  have hB : 0 < r₀ + T * rb :=
    ODEUniformMain.source_mass_pos D T r₀ rb hT x v b hv hb (hPSD x) hTarget
  have hRatio := ODEConstantForcing.normalization_ratio_ge_one
    (ODEPublicSourceMesh.generator D x)
    (ODEPublicSourceMesh.generator_dissipative D x (hPSD x)) v b T hT hTarget
  rw [hv, hb] at hRatio
  exact ODEUniformMain.solver D etaH etaD T g ε r₀ rb
    hH hDiss hT (hRatio.trans hBudget) hε hεHalf h₀ hbNonneg hB
    hrH hcH hrD hcD hPSD J₀ Jb hJ₀ hJb seed hSeed

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 2000000 in
/-- Manuscript-facing form with one supplied nonzero actual solution. Its
normalization ratio only certifies public scalar bounds. The resulting
circuit family remains uniform over every admissible input and both source
directions, retaining exactly the public `Outcome` quantifier order. -/
theorem solver (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (x : X) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1)
    (x : X) (v b : EuclideanSpace ℂ n) (hv : ‖v‖ = r₀) (hb : ‖b‖ = rb)
    (hTarget : ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0)
    (hBudget : (r₀ + T * rb) /
      ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ ≤ g) :
    Outcome D etaH etaD T g ε r₀ rb J₀ Jb seed := by
  exact solver_of_nonempty_promise D etaH etaD T g ε r₀ rb
    hH hDiss hT hε hεHalf hrH hcH hrD hcD hPSD J₀ Jb hJ₀ hJb seed hSeed
    ⟨x, v, b, hv, hb, hTarget, hBudget⟩

end
end SparseHamiltonian.ImprovedSparseODE
