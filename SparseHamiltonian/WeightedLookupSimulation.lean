import SparseHamiltonian.EncodedLookupClockSimulation

/-!
# Full-output simulation from weighted uniform lookup programs

The Hamiltonian is a convex combination of fixed public compressions of
uniform lookup programs implementing involutions. Heterogeneous program
clocks, their weighted analytic budgets, all register encodings, the active
clock queries, synchronized reuse, and amplification are constructed.
The theorem has no analytic clock or query-implementation premise.

This provides an actual lookup-query bound in terms of program query counts.
Constructing sparse-band programs meeting the square-root sparsity budgets
is a separate remaining obligation.
-/

namespace SparseHamiltonian.WeightedLookupSimulation

noncomputable section
open ContinuousLinearMap OracleCircuit MaskedLookupCurry HeterogeneousLookupClock
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {X I A Z : Type*} [Fintype I] [Fintype A] [Fintype Z] [AddCommGroup Z]
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- Fixed preparation into the actual ordinary-lookup workspace. -/
def input (f : X → A → Z) (ps : I → Program (localSigned 1 f))
    (e : P →ₗᵢ[ℂ] Payload A Z) (τ Q qbar ε : ℝ) :
    P →L[ℂ] ClockQuery.EvolutionSpace (P := Payload A Z)
      (V := PiLp 2 (fun _ : Slot f ps => Payload A Z)) τ Q qbar ε :=
  EncodedLookupClockSimulation.evolutionEncoding (C := Slot f ps) e τ Q qbar ε ∘L
    ClockQuery.evolutionInput (P := P)
      (V := PiLp 2 (fun _ : Slot f ps => Payload A Z)) τ Q qbar ε

/-- The clean physical output retains every ancillary register in the error norm. -/
def output (f : X → A → Z) (ps : I → Program (localSigned 1 f))
    (e : P →ₗᵢ[ℂ] Payload A Z) (τ Q qbar ε : ℝ) :
    P →L[ℂ] ClockQuery.EvolutionSpace (P := Payload A Z)
      (V := PiLp 2 (fun _ : Slot f ps => Payload A Z)) τ Q qbar ε :=
  EncodedLookupClockSimulation.evolutionEncoding (C := Slot f ps) e τ Q qbar ε ∘L
    ClockSimulation.evolutionOutput (P := P)
      (V := PiLp 2 (fun _ : Slot f ps => Payload A Z)) τ Q qbar ε

/-- The complete weighted lookup simulation, with no implementation hypotheses
for selected queries, clocks, reuse layers, or amplification. The maximum clock
length Q bounds actual syntax counts plus two; qbar is their weighted average. -/
theorem evolution_query_certificate [FiniteDimensional ℂ P]
    (f : X → A → Z) (weights : I → ℝ) (ps : I → Program (localSigned 1 f))
    (hw : ∀ i, 0 ≤ weights i) (hsum : ∑ i, weights i = 1)
    (Q : ℝ) (hQ : 1 ≤ Q) (hqQ : ∀ i, (QueryClockStep.slots (ps i) : ℝ) ≤ Q)
    (hInv : ∀ i x v, (ps i).eval x ((ps i).eval x v) = v)
    (E : I → P →ₗᵢ[ℂ] Payload A Z) (e : P →ₗᵢ[ℂ] Payload A Z)
    (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    let qbar := WeightedProgramClockBounds.averageLength weights ps
    ∃ c : Program (EncodedLookupClockSimulation.evolutionOracle
        (C := Slot f ps) f τ Q qbar ε),
      c.count ≤ 12 * FilterSchedule.degree Q (τ * qbar) (ε / 3) ∧
      (c.count : ℝ) ≤ 768 *
        (τ * qbar + Q * (1 + Real.log (3 * (Q + τ * qbar + 2) / ε))) ∧
      (input f ps e τ Q qbar ε)† ∘L input f ps e τ Q qbar ε = 1 ∧
      (output f ps e τ Q qbar ε)† ∘L output f ps e τ Q qbar ε = 1 ∧
      ∀ x, IsUnitary (c.eval x) ∧
        ‖c.eval x ∘L input f ps e τ Q qbar ε -
          output f ps e τ Q qbar ε ∘L
            NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
              WeightedProgramClockBounds.generator weights ps E x)‖ ≤ ε := by
  obtain ⟨_hD, hJ, hRight, hLeft, hR, hBoundary, hSelf, hH, hEndpoint, hbq, hqbarQ⟩ :=
    FlattenedLookupClockBounds.family_promises f weights ps hw hsum Q hQ hqQ hInv E
  exact EncodedLookupClockSimulation.evolution_query_certificate f
    (flatFixed f ps) (flatFixed_unitary f ps) (mask f ps)
    (flatFamilyClock f ps hInv) (FlattenedLookupClockBounds.flatResolvent f ps hInv)
    (flatFamilyClock_factor f ps hInv) e
    (FlattenedLookupClockBounds.flatBoundary f weights ps E)
    (WeightedProgramClockBounds.generator weights ps E) τ Q
    (Real.sqrt (WeightedProgramClockBounds.averageLength weights ps / 2))
    (WeightedProgramClockBounds.averageLength weights ps) ε hτ hQ hJ hRight hLeft hR
    hBoundary hSelf hH hEndpoint hbq hqbarQ hε hεOne

end
end SparseHamiltonian.WeightedLookupSimulation
