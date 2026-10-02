import SparseODE.ODEUniformBoundary

/-!
# Uniform constant-coefficient ODE solver across public parameter cases

Each branch selects one primitive circuit family before the unknown matrix
input and source directions. The case decision uses only public numerical
parameters. Positive supplied source mass excludes no admissible nonzero
solution, as proved below. The full trial certificate retains mean heralded
success, normalized output accuracy and both query bounds.

-/

namespace SparseHamiltonian.ODEUniformMain

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- A nonzero dissipative solution forces the supplied source mass to be
positive. Thus this public normalization condition excludes no promised
instance of normalized solution preparation. -/
theorem source_mass_pos (D : Data X n Z s) (T r₀ rb : ℝ) (hT : 0 ≤ T)
    (x : X) (v b : EuclideanSpace ℂ n)
    (hv : ‖v‖ = r₀) (hb : ‖b‖ = rb)
    (hPSD : ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (hTarget : ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0) :
    0 < r₀ + T * rb := by
  have hNorm := ODEConstantForcing.solution_norm_le
    (ODEPublicSourceMesh.generator D x)
    (ODEPublicSourceMesh.generator_dissipative D x hPSD) v b T hT
  rw [hv, hb] at hNorm
  exact (norm_pos_iff.mpr hTarget).trans_le hNorm

/-- Public parameter cases with a fixed family valid for every promised
input in the selected branch. Each branch retains its concrete oracle
provenance and the complete trial resource/correctness certificate. -/
def Outcome (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  (T = 0 ∧ ODEUniformBoundary.ZeroTimeOutcome D etaH etaD g ε J₀ Jb seed) ∨
    (0 < T ∧ etaH + ImprovedODEQueryBudget.radius g ε * etaD = 0 ∧
      ODEUniformBoundary.ZeroEnergyOutcome D etaH etaD T g ε r₀ rb J₀ Jb seed) ∨
    (0 < T ∧ 0 < etaH + ImprovedODEQueryBudget.radius g ε * etaD ∧
      ODEUniformPositiveEndpoint.Outcome D etaH etaD T g ε r₀ rb J₀ Jb seed)

set_option maxRecDepth 4096 in
set_option synthInstance.maxSize 2048 in
set_option maxHeartbeats 2000000 in
/-- Uniform sparse-access solution preparation for dissipative constant
coefficients. The circuit family is fixed from public data before any
unknown input or source direction; no pointwise circuit choice occurs in
the conclusion. Source mass is a supplied scalar, and source_mass_pos
derives its positivity from every admissible nonzero solution.

Every branch carries the original full TrialCertificate: mean success at
least one quarter, phase-adjusted normalized error at most epsilon/500,
matrix cost at most 318504960*g*queryShape, and at most 10*g calls to each
source interface. Boundary branches additionally have zero matrix cost. -/
theorem solver (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (h₀ : 0 ≤ r₀) (hb : 0 ≤ rb) (hB : 0 < r₀ + T * rb)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (x : X) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    Outcome D etaH etaD T g ε r₀ rb J₀ Jb seed := by
  rcases ODEMainEndpoint.parameter_cases etaH etaD T g ε hH hDiss hT hg hε
      (hεHalf.trans (by norm_num)) with hZero | ⟨hPositive, hEnergyZero⟩ |
      ⟨hPositive, hEnergyPositive⟩
  · exact Or.inl ⟨hZero, ODEUniformBoundary.zero_time_solver
      D etaH etaD g ε hg hε hεHalf J₀ Jb hJ₀ seed hSeed⟩
  · exact Or.inr (Or.inl ⟨hPositive, hEnergyZero,
      ODEUniformBoundary.zero_energy_solver D etaH etaD T g ε r₀ rb
        hH hDiss hT hg hε hεHalf h₀ hb hEnergyZero hrH hrD
        J₀ Jb hJ₀ hJb seed hSeed⟩)
  · exact Or.inr (Or.inr ⟨hPositive, hEnergyPositive,
      ODEUniformPositiveEndpoint.positive_time_solver D etaH etaD T g ε r₀ rb
        hH hDiss hEnergyPositive hPositive hg hε hεHalf h₀ hb hB
        hrH hcH hrD hcD hPSD J₀ Jb hJ₀ hJb seed hSeed⟩)

end
end SparseHamiltonian.ODEUniformMain
