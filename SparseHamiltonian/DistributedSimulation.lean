import SparseHamiltonian.ClockSimulation

/-!
# Hamiltonian evolution implemented from distributed weighted clocks

This theorem starts with probabilities, Hermitian involutions, public isometric
encodings and boundary-fixing slot gauges. It constructs the actual amplified
coherent-reuse isometry and proves its complete-output approximation to the
Hamiltonian exponential. All clock resolvent, compression, endpoint and filter
premises are discharged. The degree has logarithmic precision dependence.

This is an operator construction and degree bound. It does not assert a sparse
oracle implementation, a cost for selected link operations, or a query bound.
-/

namespace SparseHamiltonian.DistributedSimulation

noncomputable section
open ContinuousLinearMap CanonicalWeightedClock
open scoped BigOperators InnerProduct

variable {ι P : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)]
  [∀ i, CompleteSpace (V i)] [∀ i, FiniteDimensional ℂ (V i)]

/-- The actual distributed-clock implementation approximates continuous-time
Hamiltonian evolution on its entire output, with no analytic clock promises
among the assumptions. Only the supplied branch data and scalar bounds remain. -/
theorem evolution_error (p : ι → ℝ) (q : ι → ℕ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (Q : ℝ) (hQ : 1 ≤ Q) (hqQ : ∀ i, ((q i + 1 : ℕ) : ℝ) ≤ Q)
    (O : ∀ i, V i →ₗ[ℂ] V i)
    (hO : ∀ i v, O i (O i v) = v)
    (hHerm : ∀ i v w, inner ℂ (O i v) w = inner ℂ v (O i w))
    (E : ∀ i, P →ₗᵢ[ℂ] V i)
    (G : ∀ i, Fin (q i + 1) → V i ≃ₗᵢ[ℂ] V i)
    (hG : ∀ i, G i 0 = LinearIsometryEquiv.refl ℂ (V i))
    (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    let D := WeightedClock.diagonal (fun i =>
      ClockGauge.distributedClock (O i) (q i) (hO i) (hHerm i) (G i))
    let J := WeightedClock.boundary p (fun i => branchBoundary (q i) (E i))
    let H := WeightedClock.generator p (fun i => branchGenerator (O i) (E i))
    let qbar := ∑ i, p i * ((q i + 1 : ℕ) : ℝ)
    let S := ClockSimulation.evolutionImplementation D J τ Q qbar ε
    let F := ClockSimulation.evolutionOutput (P := P)
      (V := PiLp 2 (fun i => ClockOperators.H (q i) (V i))) τ Q qbar ε
    F† ∘L F = 1 ∧ S† ∘L S = 1 ∧
    ‖S - F ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ ε ∧
    (FilterSchedule.degree Q (τ * qbar) (ε / 3) : ℝ) ≤
      64 * (τ * qbar + Q * (1 + Real.log (3 * (Q + τ * qbar + 2) / ε))) := by
  obtain ⟨hDg, hJg, hLeftg, hRightg, hRnormg, hBoundaryg, hHermg, hHnormg,
    hEndpointg, hSqg, hAverageg⟩ :=
    DistributedWeightedClock.distributed_weighted_clock_promises
      p q hp hsum Q (zero_le_one.trans hQ) hqQ O hO hHerm E G hG
  have h := ClockSimulation.evolution_error
    (WeightedClock.diagonal (fun i => ClockGauge.distributedClock (O i) (q i) (hO i) (hHerm i) (G i)))
    (WeightedClock.diagonal (fun i => ClockGauge.distributedResolvent (O i) (q i) (hO i) (G i)))
    (WeightedClock.boundary p (fun i => branchBoundary (q i) (E i)))
    (WeightedClock.generator p (fun i => branchGenerator (O i) (E i)))
    τ Q (Real.sqrt ((∑ i, p i * ((q i + 1 : ℕ) : ℝ)) / 2))
    (∑ i, p i * ((q i + 1 : ℕ) : ℝ)) ε hτ hQ
    hDg hJg hRightg hLeftg hRnormg hBoundaryg hHermg hHnormg
    hEndpointg hSqg.le hAverageg hε hεOne
  refine ⟨ClockSimulation.evolutionOutput_isometry τ Q
    (∑ i, p i * ((q i + 1 : ℕ) : ℝ)) ε hQ, h.1, h.2.1, ?_⟩
  have hRatio (a : ℝ) : a / (ε / 3) = 3 * a / ε := by ring
  simpa only [hRatio] using h.2.2

end
end SparseHamiltonian.DistributedSimulation
