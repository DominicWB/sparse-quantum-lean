import SparseODE.ImprovedODEOutput

/-!
# Constant-forcing reduction with a proved source discretization

This theorem chooses the actual quadrature size and discharges its error
obligation before invoking the finite LCHS output estimate. Gaussian LCHS
coefficients and simulated Hamiltonian branches are still explicit inputs;
it is not a completed sparse-oracle state-preparation theorem.
-/

namespace SparseHamiltonian.ImprovedODESourceOutput

noncomputable section
open ContinuousLinearMap NormedSpace ODEDissipative ODEConstantForcing
open ODEErrorBudget ODEStateNormalization ODESourceQuadrature
open scoped BigOperators

variable {E κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E] [Fintype κ]

/-- One finite mesh works for any LCHS approximation and simulated branch
family satisfying the displayed errors at its durations. Its source error
and norm budget are proved from the ODE, rather than supplied as hypotheses. -/
theorem exists_discretized_output_certificate
    (A : E →L[ℂ] E) (hA : Dissipative A) (v b : E) (T g ε : ℝ)
    (hT : 0 ≤ T) (hx : solution A v b T ≠ 0)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hBudget : ‖v‖ + T * ‖b‖ ≤ g * ‖solution A v b T‖) :
    ∃ N : ℕ, 0 < N ∧
      (∀ i : Fin N, 0 ≤ time T N i ∧ time T N i ≤ T) ∧
      ∀ (c : κ → ℂ) (U₀ V₀ : κ → E →L[ℂ] E)
        (U V : Fin N → κ → E →L[ℂ] E),
        (∑ k, ‖c k‖ ≤ 3) →
        ‖(∑ k, c k • U₀ k) - exp (T • A)‖ ≤
          2 * ImprovedODEQueryBudget.precision g ε →
        (∀ i, ‖(∑ k, c k • U i k) - exp (time T N i • A)‖ ≤
          2 * ImprovedODEQueryBudget.precision g ε) →
        (∀ k, ‖V₀ k - U₀ k‖ ≤ ImprovedODEQueryBudget.precision g ε) →
        (∀ i k, ‖V i k - U i k‖ ≤ ImprovedODEQueryBudget.precision g ε) →
        let y := finiteDuhamel (∑ k, c k • V₀ k)
          (fun i => ∑ k, c k • V i k) v (weight T N) (fun _ : Fin N => b)
        y ≠ 0 ∧ ‖unitDirection y‖ = 1 ∧
          ‖unitDirection y - unitDirection (solution A v b T)‖ ≤ ε / 500 ∧
          1 / (4 * g) ≤ ‖y‖ / (3 * (‖v‖ + T * ‖b‖)) ∧
          ‖y‖ / (3 * (‖v‖ + T * ‖b‖)) < 1 / 2 := by
  obtain ⟨N, hN, hw, ht, hB, hQuad⟩ := exists_finiteDuhamel_certificate
    A hA v b T hT (ImprovedODEQueryBudget.precision g ε)
    (ImprovedODEQueryBudget.precision_pos g ε hg hε)
  refine ⟨N, hN, ht, ?_⟩
  intro c U₀ V₀ U V hCoeff hLCHS₀ hLCHS hSimulation₀ hSimulation
  have hNorm : ‖solution A v b T‖ ≤
      sourceBudget v (weight T N) (fun _ : Fin N => b) := by
    rw [hB]
    exact solution_norm_le A hA v b T hT
  have hRatio : sourceBudget v (weight T N) (fun _ : Fin N => b) ≤
      g * ‖solution A v b T‖ := by
    rw [hB]
    exact hBudget
  have hResult := ImprovedODEOutput.finite_lchs_output_certificate
    c U₀ V₀ U V (exp (T • A)) (fun i : Fin N => exp (time T N i • A))
    v (solution A v b T) (weight T N) (fun _ : Fin N => b) g ε
    hx hg hε hεHalf hw hNorm hRatio hCoeff hLCHS₀ hLCHS
    hSimulation₀ hSimulation hQuad
  dsimp only at hResult ⊢
  simpa only [hB] using hResult

end
end SparseHamiltonian.ImprovedODESourceOutput
