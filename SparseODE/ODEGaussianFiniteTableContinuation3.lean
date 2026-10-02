import SparseODE.ODEGaussianFull

/-!
# Gaussian frequency table from the dissipativity promise

The continuous approximation is now supplied by the proved contour identity
and its shifted residual estimate. The caller supplies the physical positive
dissipative-part promise, with no LCHS identity or approximation assumption.

-/

namespace SparseHamiltonian.ODEGaussianFiniteTable

noncomputable section
open NativeSparseBlockEncoding ODEUniformQuadrature ODEWeightedLCHS
open scoped BigOperators Interval InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The public truncated operator error follows from positivity of the
actual dissipative part, with no continuous approximation premise. -/
theorem truncated_error (D : Data X n Z s) (x : X)
    (hPSD : ∀ v : EuclideanSpace ℂ n, 0 ≤ (inner ℂ v
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) v)).re)
    (u g ε : ℝ) (hu : 0 ≤ u) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ‖(∫ k in (-ImprovedODEQueryBudget.radius g ε)..
        (ImprovedODEQueryBudget.radius g ε),
        nativeWeighted D x u (ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε)) k) -
      NormedSpace.exp (u • ODEPublicSourceMesh.generator D x)‖ ≤
        ImprovedODEQueryBudget.precision g ε := by
  exact truncated_error_of_full D x u g ε hg hε hεOne
    (ODEGaussianFull.native_full_line_error D x hPSD u
      (ODEGaussianParameters.width g ε) hu
      (ODEGaussianParameters.width_ge_one g ε hg hε hεOne))

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- Explicit Gaussian nodes and coefficients satisfying the finite LCHS
certificate for every input matrix and every duration in the public range.
All analytic and quadrature obligations are derived from dissipativity. -/
theorem public_table_from_dissipativity (D : Data X n Z s)
    (hPSD : ∀ (x : X) (v : EuclideanSpace ℂ n), 0 ≤ (inner ℂ v
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) v)).re)
    (T g ε : ℝ) (hT : 0 ≤ T) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
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
    (fun x u hu _ => truncated_error D x (hPSD x) u g ε hu hg hε hεOne)

end
end SparseHamiltonian.ODEGaussianFiniteTable
