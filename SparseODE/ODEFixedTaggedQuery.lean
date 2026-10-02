import SparseODE.ODECommonDuration

/-!
# Native sharp simulation for one tagged ODE Hamiltonian

This connects the proved tagged moment bounds and concrete native active
circuits to full-output simulation. The exact target is exp(-i t (H+kD)),
using the original sparse row, column and value oracles. The rescaling can
be chosen from a common radius independently of k. Coherent SELECT over
all branches is a separate construction, not inferred from equal counts.

-/

namespace SparseHamiltonian.ODEFixedTaggedQuery

noncomputable section
open ContinuousLinearMap OracleCircuit ImprovedCayleyMoments CayleyClockInterface
open ODEFixedTaggedMoments
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
    (M : X → Matrix n n ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hH : ∀ x, (M x).IsHermitian)
    (hSupport : ∀ x i j, D.matrix x i j = 0 → D.matrix x j i = 0 → M x i j = 0)
    (hrow : ∀ x i, ∑ j, ‖M x i j‖ ^ 2 ≤ ρ ^ 2)
    (hcol : ∀ x j, ∑ i, ‖M x i j‖ ^ 2 ≤ ρ ^ 2)
    (γ t ε : ℝ) (hγ : 0 < γ) (hγOne : γ ≤ 1)
    (htPhys : 0 ≤ t) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hBudget : time (2 * (s : ℝ)) (ρ * t) γ * moment γ +
      width (2 * (s : ℝ)) γ * ImprovedPrecisionBudget.circuitLog ε ≤
        12 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (ρ * t) (ImprovedPrecisionBudget.targetLog ε))
    (O : Label → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (E : SharpClockQuery.EvolutionSpace (P := EuclideanSpace ℂ n)
      (V := ODETaggedMoments.PrivateSpace n)
      (time (2 * (s : ℝ)) (ρ * t) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε →L[ℂ] K)
    (hE : E† ∘L E = 1) (q : ℕ)
    (hQuery : ∀ r < 2 * SharpFilterSchedule.degree (width (2 * (s : ℝ)) γ)
      (time (2 * (s : ℝ)) (ρ * t) γ * moment γ) (ε / 3),
      LabeledEncodedOracle.ImplementsOn O
        (fun x => SharpLabeledActiveClockQuery.evolutionActiveClock
          (P := EuclideanSpace ℂ n) (action D x (M x) ρ γ)
          (time (2 * (s : ℝ)) (ρ * t) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε r) E q) :
    ∃ p : MultiOracleCircuit.Program O,
      (p.count : ℝ) ≤ 9216 * (q : ℝ) *
        ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (ρ * t) (ImprovedPrecisionBudget.targetLog ε) ∧
      (E ∘L SharpClockQuery.evolutionInput (P := EuclideanSpace ℂ n)
        (V := ODETaggedMoments.PrivateSpace n)
        (time (2 * (s : ℝ)) (ρ * t) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε)† ∘L
        (E ∘L SharpClockQuery.evolutionInput
          (time (2 * (s : ℝ)) (ρ * t) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε) = 1 ∧
      (E ∘L SharpClockSimulation.evolutionOutput (P := EuclideanSpace ℂ n)
        (V := ODETaggedMoments.PrivateSpace n)
        (time (2 * (s : ℝ)) (ρ * t) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε)† ∘L
        (E ∘L SharpClockSimulation.evolutionOutput (P := EuclideanSpace ℂ n)
        (V := ODETaggedMoments.PrivateSpace n)
        (time (2 * (s : ℝ)) (ρ * t) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε) = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L (E ∘L SharpClockQuery.evolutionInput (P := EuclideanSpace ℂ n)
            (V := ODETaggedMoments.PrivateSpace n)
            (time (2 * (s : ℝ)) (ρ * t) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε) -
          (E ∘L SharpClockSimulation.evolutionOutput (P := EuclideanSpace ℂ n)
        (V := ODETaggedMoments.PrivateSpace n)
        (time (2 * (s : ℝ)) (ρ * t) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε) ∘L
            NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (M x))‖ ≤ ε := by
  have ht : 0 ≤ time (2 * (s : ℝ)) (ρ * t) γ :=
    div_nonneg (mul_nonneg (mul_nonneg hρ.le htPhys) (Real.sqrt_nonneg _)) hγ.le
  have hJ := boundary_isometry D
  have hMoments := fun x => native_moment_certificate D x (M x) (hH x) ρ hρ
    (hSupport x) (hrow x) (hcol x)
  have hSelf : ∀ x, star (generator D x (M x) ρ) = generator D x (M x) ρ :=
    fun x => (hMoments x).2.1
  -- Instantiate the abstract star-algebra lemmas before comparing them with
  -- concrete operator composition. This avoids recovering the algebra and
  -- both operators by unfolding the concrete sparse construction.
  have hD : ∀ x, (action D x (M x) ρ γ)† ∘L action D x (M x) ρ γ = 1 := by
    intro x
    change star (action D x (M x) ρ γ) * action D x (M x) ρ γ = 1
    rw [ODEFixedTaggedMoments.action_eq_cayley D x (M x) ρ γ]
    exact ImprovedCayleyMoments.cayleyAction_star_mul_self
      (A := ODETaggedMoments.PrivateSpace n →L[ℂ] ODETaggedMoments.PrivateSpace n)
      (scaled (generator D x (M x) ρ) γ) (inverse D x (M x) ρ γ)
      (CayleyClockInterface.scaled_self_adjoint (generator D x (M x) ρ) γ (hSelf x))
      (ODEFixedTaggedMoments.inverse_right D x (M x) ρ γ)
  have hRight : ∀ x, (1 - action D x (M x) ρ γ) ∘L
      resolventAtOne (scaled (generator D x (M x) ρ) γ) = 1 := by
    intro x
    change (1 - action D x (M x) ρ γ) * resolventAtOne (scaled (generator D x (M x) ρ) γ) = 1
    rw [ODEFixedTaggedMoments.action_eq_cayley D x (M x) ρ γ]
    exact ImprovedCayleyMoments.one_sub_cayleyAction_mul_resolventAtOne
      (A := ODETaggedMoments.PrivateSpace n →L[ℂ] ODETaggedMoments.PrivateSpace n)
      (scaled (generator D x (M x) ρ) γ) (inverse D x (M x) ρ γ)
      (ODEFixedTaggedMoments.inverse_right D x (M x) ρ γ)
      (ODEFixedTaggedMoments.inverse_left D x (M x) ρ γ)
  have hLeft : ∀ x, resolventAtOne (scaled (generator D x (M x) ρ) γ) ∘L
      (1 - action D x (M x) ρ γ) = 1 := by
    intro x
    change resolventAtOne (scaled (generator D x (M x) ρ) γ) * (1 - action D x (M x) ρ γ) = 1
    rw [ODEFixedTaggedMoments.action_eq_cayley D x (M x) ρ γ]
    exact ImprovedCayleyMoments.resolventAtOne_mul_one_sub_cayleyAction
      (A := ODETaggedMoments.PrivateSpace n →L[ℂ] ODETaggedMoments.PrivateSpace n)
      (scaled (generator D x (M x) ρ) γ) (inverse D x (M x) ρ γ)
      (ODEFixedTaggedMoments.inverse_right D x (M x) ρ γ)
  obtain ⟨p, _hNat, hCount, hIn, hOut, hAction⟩ :=
    SharpLabeledActiveClockQuery.evolution_query_certificate
      (fun x => action D x (M x) ρ γ) (fun x => resolventAtOne (scaled (generator D x (M x) ρ) γ))
      (boundary D) (fun x => compressed (generator D x (M x) ρ) (boundary D) γ)
      (time (2 * (s : ℝ)) (ρ * t) γ) (width (2 * (s : ℝ)) γ) (endpoint γ) (moment γ) ε
      ht (width_ge_one (2 * (s : ℝ)) γ) hD hJ hRight hLeft
      (fun x => resolvent_norm (generator D x (M x) ρ) (2 * (s : ℝ)) γ hγ.le
        (hMoments x).2.2.1)
      (fun x => resolventAtOne_compression (scaled (generator D x (M x) ρ) γ) (boundary D) hJ)
      (fun x => compressed_self_adjoint (generator D x (M x) ρ) (boundary D) γ (hSelf x))
      (fun x => (compressed_norm (generator D x (M x) ρ) (boundary D) γ hγ.le hJ
        (hMoments x).2.2.2.1).trans hγOne)
      (fun x => endpoint_norm (generator D x (M x) ρ) (boundary D) γ (hSelf x) hJ hγ.le
        (hMoments x).2.2.2.1)
      (endpoint_sq γ).le (moment_le_width (2 * (s : ℝ)) γ hγ.le hγOne)
      hε hεOne O hO E hE q hQuery
  refine ⟨p, ?_, hIn, hOut, fun x => ?_⟩
  · change time (2 * (s : ℝ)) (ρ * t) γ * moment γ + width (2 * (s : ℝ)) γ *
      (1 + Real.log (3 / ε)) ≤
        12 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (ρ * t) (ImprovedPrecisionBudget.targetLog ε)
      at hBudget
    have hMul := mul_le_mul_of_nonneg_left hBudget
      (show (0 : ℝ) ≤ 768 * (q : ℝ) by positivity)
    calc
      (p.count : ℝ) ≤ 768 * (q : ℝ) * (time (2 * (s : ℝ)) (ρ * t) γ * moment γ +
          width (2 * (s : ℝ)) γ * (1 + Real.log (3 / ε))) := hCount
      _ ≤ (768 * (q : ℝ)) * (12 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (ρ * t)
          (ImprovedPrecisionBudget.targetLog ε)) := hMul
      _ = _ := by ring
  · obtain ⟨hUnitary, hError⟩ := hAction x
    rw [physical_exponent D x (M x) (hH x) ρ t γ hρ.ne' hγ.ne' (hSupport x)] at hError
    exact ⟨hUnitary, hError⟩

end
end SparseHamiltonian.ODEFixedTaggedQuery
