import SparseODE.ODEComplexFrequency

/-!
# Public Gaussian table after integrated truncation

This bridge discharges the finite-interval approximation from a full-line
approximation with the precise remaining exponential allowance. The tail
estimate, integrability and public precision allocation are proved above.
The full-line contour approximation remains an explicit obligation.

-/

namespace SparseHamiltonian.ODEGaussianFiniteTable

noncomputable section
open NativeSparseBlockEncoding ODEUniformQuadrature ODEWeightedLCHS
open scoped BigOperators Interval

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The proved exterior tail and exact scalar budget turn the remaining
full-line estimate into the required public truncated estimate. -/
theorem truncated_error_of_full (D : Data X n Z s) (x : X) (u g ε : ℝ)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hFull : ‖(∫ k : ℝ,
        nativeWeighted D x u (ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε)) k) -
      NormedSpace.exp (u • ODEPublicSourceMesh.generator D x)‖ ≤
        Real.exp (1 - ODEGaussianParameters.width g ε)) :
    ‖(∫ k in (-ImprovedODEQueryBudget.radius g ε)..
        (ImprovedODEQueryBudget.radius g ε),
        nativeWeighted D x u (ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε)) k) -
      NormedSpace.exp (u • ODEPublicSourceMesh.generator D x)‖ ≤
        ImprovedODEQueryBudget.precision g ε := by
  have hBound := ODEGaussianIntegral.native_truncated_error_of_full D x u
    (ODEGaussianParameters.width g ε) (ImprovedODEQueryBudget.radius g ε)
    (Real.exp (1 - ODEGaussianParameters.width g ε))
    (ODEGaussianParameters.width_ge_two g ε hg hε hεOne)
    (ODEGaussianParameters.cutoff_le_radius g ε hg hε hεOne) hFull
  rw [ODEGaussianParameters.integral_error_budget g ε hg hε] at hBound
  exact hBound

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- One public Gaussian table now needs only the full-line contour estimate.
No scalar mass, regularity, integrability, truncation or mesh-accuracy
premise is left for the caller to supply. -/
theorem public_table_of_full (D : Data X n Z s) (T g ε : ℝ)
    (hT : 0 ≤ T) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hFull : ∀ (x : X) (u : ℝ), 0 ≤ u → u ≤ T →
      ‖(∫ k : ℝ,
          nativeWeighted D x u (ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε)) k) -
        NormedSpace.exp (u • ODEPublicSourceMesh.generator D x)‖ ≤
          Real.exp (1 - ODEGaussianParameters.width g ε)) :
    let w := ODEGaussianParameters.width g ε
    let R := ImprovedODEQueryBudget.radius g ε
    let N := ODEFiniteLCHSConstruction.gridSize D T
      (ODEGaussianKernel.lipschitzConstant w) (Real.exp 1 / Real.pi) g ε
    0 < N ∧
      (∀ i : Fin N, |node (-R) R N i| ≤ R) ∧
      ODECoherentLCU.coefficientMass (coefficient (ODEGaussianKernel.kernel w) (-R) R N) ≤ 3 ∧
      (∀ x : X, ODEActualPrimitiveEndpoint.FiniteLCHS D
        (node (-R) R N) (coefficient (ODEGaussianKernel.kernel w) (-R) R N) T g ε x) := by
  exact public_table D T g ε hT hg hε hεOne
    (fun x u hu huT => truncated_error_of_full D x u g ε hg hε hεOne
      (hFull x u hu huT))

end
end SparseHamiltonian.ODEGaussianFiniteTable
