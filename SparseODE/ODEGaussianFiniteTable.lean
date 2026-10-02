import SparseODE.ODEGaussianParameters

/-!
# Concrete Gaussian frequency tables

All scalar-kernel premises of the verified finite-table construction are
proved here using the explicit Gaussian density. The only remaining analytic
premise is the approximation of the dissipative propagator by its truncated
continuous integral. It is not assumed as an axiom or claimed as proved.

-/

namespace SparseHamiltonian.ODEGaussianFiniteTable

noncomputable section
open NativeSparseBlockEncoding ODEUniformQuadrature ODEWeightedLCHS
open scoped BigOperators Interval

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- Explicit finite Gaussian coefficients at one public mesh. There are no
assumed coefficient-mass, continuity, Lipschitz or finite-grid error bounds.
The continuous propagator approximation remains an explicit proof obligation. -/
theorem public_table (D : Data X n Z s) (T g ε : ℝ)
    (hT : 0 ≤ T) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hTruncated : ∀ (x : X) (u : ℝ), 0 ≤ u → u ≤ T →
      ‖(∫ k in (-ImprovedODEQueryBudget.radius g ε)..
          (ImprovedODEQueryBudget.radius g ε),
          nativeWeighted D x u (ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε)) k) -
        NormedSpace.exp (u • ODEPublicSourceMesh.generator D x)‖ ≤
          ImprovedODEQueryBudget.precision g ε) :
    let w := ODEGaussianParameters.width g ε
    let R := ImprovedODEQueryBudget.radius g ε
    let N := ODEFiniteLCHSConstruction.gridSize D T
      (ODEGaussianKernel.lipschitzConstant w) (Real.exp 1 / Real.pi) g ε
    0 < N ∧
      (∀ i : Fin N, |node (-R) R N i| ≤ R) ∧
      ODECoherentLCU.coefficientMass (coefficient (ODEGaussianKernel.kernel w) (-R) R N) ≤ 3 ∧
      (∀ x : X, ODEActualPrimitiveEndpoint.FiniteLCHS D
        (node (-R) R N) (coefficient (ODEGaussianKernel.kernel w) (-R) R N) T g ε x) := by
  let w := ODEGaussianParameters.width g ε
  have hw : 0 < w := ODEGaussianParameters.width_pos g ε hg hε hεOne
  have hK : 0 ≤ ODEGaussianKernel.lipschitzConstant w :=
    ODEGaussianKernel.lipschitzConstant_nonneg w hw
  have hM : 0 ≤ Real.exp 1 / Real.pi := by positivity
  have hR : 0 ≤ ImprovedODEQueryBudget.radius g ε :=
    ImprovedODEQueryBudget.radius_nonneg g ε hg hε hεOne
  exact ODEFiniteLCHSConstruction.public_table D T
    (ODEGaussianKernel.lipschitzConstant w) (Real.exp 1 / Real.pi) g ε
    hT hK hM hg hε hεOne (ODEGaussianKernel.kernel w)
    (ODEGaussianKernel.kernel_continuous w)
    (ODEGaussianKernel.kernel_lipschitz w hw)
    (fun k => ODEGaussianKernel.norm_kernel_le w k hw)
    (ODEGaussianMass.kernel_mass_budget w (ImprovedODEQueryBudget.radius g ε)
      g ε hw hR hg hεOne) hTruncated

end
end SparseHamiltonian.ODEGaussianFiniteTable
