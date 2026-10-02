import SparseHamiltonian.NativeWholeProgramActiveContinuation2

/-!
# Fixed-boundary sparse accuracy in a labeled physical query workspace

All sparse analytic obligations are discharged from the original data.  The
only circuit hypothesis is a uniform clean implementation of the active
conjugated edge action; its cost q must still be supplied by the primitive
locator/value circuit.  The rescaling budget is the one already constructed
by ImprovedPrecisionBudget.exists_rescaling_for_precision.
-/

namespace SparseHamiltonian.FixedNativeCayleyQuery

noncomputable section
open ContinuousLinearMap OracleCircuit ImprovedCayleyMoments CayleyClockInterface
open FixedNativeCayleySimulation
open scoped BigOperators InnerProduct

variable {X n Z Label K : Type*} [Fintype n] [DecidableEq n] {s : ℕ}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- A common native active-action certificate supplies the actual full-output
program.  Analytic moments, full inverses, fixed preparation, and the physical
Hamiltonian are proved rather than granted as circuit premises. -/
theorem query_certificate
    (D : NativeSparseBlockEncoding.Data X n Z s)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (γ τ ε : ℝ) (hγ : 0 < γ) (hγOne : γ ≤ 1)
    (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hBudget : time (s : ℝ) τ γ * moment γ +
      width (s : ℝ) γ * ImprovedPrecisionBudget.circuitLog ε ≤
        12 * ImprovedPrecisionBudget.shape (s : ℝ) τ (ImprovedPrecisionBudget.targetLog ε))
    (O : Label → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (E : SharpClockQuery.EvolutionSpace (P := EuclideanSpace ℂ n)
      (V := SparseEdgeMoments.OrientedSpace n)
      (time (s : ℝ) τ γ) (width (s : ℝ) γ) (moment γ) ε →L[ℂ] K)
    (hE : E† ∘L E = 1) (q : ℕ)
    (hQuery : ∀ r < 2 * SharpFilterSchedule.degree (width (s : ℝ) γ)
      (time (s : ℝ) τ γ * moment γ) (ε / 3),
      LabeledEncodedOracle.ImplementsOn O
        (fun x => SharpLabeledActiveClockQuery.evolutionActiveClock
          (P := EuclideanSpace ℂ n) (action D x γ)
          (time (s : ℝ) τ γ) (width (s : ℝ) γ) (moment γ) ε r) E q) :
    ∃ p : MultiOracleCircuit.Program O,
      (p.count : ℝ) ≤ 9216 * (q : ℝ) *
        ImprovedPrecisionBudget.shape (s : ℝ) τ (ImprovedPrecisionBudget.targetLog ε) ∧
      (E ∘L SharpClockQuery.evolutionInput (P := EuclideanSpace ℂ n)
        (V := SparseEdgeMoments.OrientedSpace n)
        (time (s : ℝ) τ γ) (width (s : ℝ) γ) (moment γ) ε)† ∘L
        (E ∘L SharpClockQuery.evolutionInput
          (time (s : ℝ) τ γ) (width (s : ℝ) γ) (moment γ) ε) = 1 ∧
      (E ∘L output (n := n) (s := s) γ τ ε)† ∘L
        (E ∘L output (n := n) (s := s) γ τ ε) = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L (E ∘L SharpClockQuery.evolutionInput (P := EuclideanSpace ℂ n)
            (V := SparseEdgeMoments.OrientedSpace n)
            (time (s : ℝ) τ γ) (width (s : ℝ) γ) (moment γ) ε) -
          (E ∘L output (n := n) (s := s) γ τ ε) ∘L
            NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  have ht : 0 ≤ time (s : ℝ) τ γ :=
    div_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _)) hγ.le
  have hJ := boundary_isometry D
  have hSelf := generator_self_adjoint D
  -- Instantiate the abstract star-algebra lemmas before comparing them with
  -- concrete operator composition. This avoids recovering the algebra and
  -- both operators by unfolding the concrete sparse construction.
  have hD : ∀ x, (action D x γ)† ∘L action D x γ = 1 := by
    intro x
    change star (action D x γ) * action D x γ = 1
    rw [FixedNativeCayleySimulation.action_eq_cayley D x γ]
    exact ImprovedCayleyMoments.cayleyAction_star_mul_self
      (A := SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n)
      (scaled (generator D x) γ) (inverse D x γ)
      (CayleyClockInterface.scaled_self_adjoint (generator D x) γ (hSelf x))
      (FixedNativeCayleySimulation.inverse_right D x γ)
  have hRight : ∀ x, (1 - action D x γ) ∘L
      resolventAtOne (scaled (generator D x) γ) = 1 := by
    intro x
    change (1 - action D x γ) * resolventAtOne (scaled (generator D x) γ) = 1
    rw [FixedNativeCayleySimulation.action_eq_cayley D x γ]
    exact ImprovedCayleyMoments.one_sub_cayleyAction_mul_resolventAtOne
      (A := SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n)
      (scaled (generator D x) γ) (inverse D x γ)
      (FixedNativeCayleySimulation.inverse_right D x γ)
      (FixedNativeCayleySimulation.inverse_left D x γ)
  have hLeft : ∀ x, resolventAtOne (scaled (generator D x) γ) ∘L
      (1 - action D x γ) = 1 := by
    intro x
    change resolventAtOne (scaled (generator D x) γ) * (1 - action D x γ) = 1
    rw [FixedNativeCayleySimulation.action_eq_cayley D x γ]
    exact ImprovedCayleyMoments.resolventAtOne_mul_one_sub_cayleyAction
      (A := SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n)
      (scaled (generator D x) γ) (inverse D x γ)
      (FixedNativeCayleySimulation.inverse_right D x γ)
  obtain ⟨p, _hNat, hCount, hIn, hOut, hAction⟩ :=
    SharpLabeledActiveClockQuery.evolution_query_certificate
      (fun x => action D x γ) (fun x => resolventAtOne (scaled (generator D x) γ))
      (boundary D) (fun x => compressed (generator D x) (boundary D) γ)
      (time (s : ℝ) τ γ) (width (s : ℝ) γ) (endpoint γ) (moment γ) ε
      ht (width_ge_one (s : ℝ) γ) hD hJ hRight hLeft
      (fun x => resolvent_norm (generator D x) (s : ℝ) γ hγ.le
        (generator_norm_le D x (hrow x)))
      (fun x => resolventAtOne_compression (scaled (generator D x) γ) (boundary D) hJ)
      (fun x => compressed_self_adjoint (generator D x) (boundary D) γ (hSelf x))
      (fun x => (compressed_norm (generator D x) (boundary D) γ hγ.le hJ
        (generator_boundary_norm_le D x (hrow x) (hcol x))).trans hγOne)
      (fun x => endpoint_norm (generator D x) (boundary D) γ (hSelf x) hJ hγ.le
        (generator_boundary_norm_le D x (hrow x) (hcol x)))
      (endpoint_sq γ).le (moment_le_width (s : ℝ) γ hγ.le hγOne)
      hε hεOne O hO E hE q hQuery
  refine ⟨p, ?_, hIn, hOut, fun x => ?_⟩
  · change time (s : ℝ) τ γ * moment γ + width (s : ℝ) γ *
      (1 + Real.log (3 / ε)) ≤
        12 * ImprovedPrecisionBudget.shape (s : ℝ) τ (ImprovedPrecisionBudget.targetLog ε)
      at hBudget
    have hMul := mul_le_mul_of_nonneg_left hBudget
      (show (0 : ℝ) ≤ 768 * (q : ℝ) by positivity)
    calc
      (p.count : ℝ) ≤ 768 * (q : ℝ) * (time (s : ℝ) τ γ * moment γ +
          width (s : ℝ) γ * (1 + Real.log (3 / ε))) := hCount
      _ ≤ (768 * (q : ℝ)) * (12 * ImprovedPrecisionBudget.shape (s : ℝ) τ
          (ImprovedPrecisionBudget.targetLog ε)) := hMul
      _ = _ := by ring
  · obtain ⟨hUnitary, hError⟩ := hAction x
    rw [physical_exponent D x (hH x) τ γ hγ.ne'] at hError
    exact ⟨hUnitary, hError⟩

end
end SparseHamiltonian.FixedNativeCayleyQuery
