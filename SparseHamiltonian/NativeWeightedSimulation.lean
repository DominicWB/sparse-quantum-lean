import SparseHamiltonian.NativeWeightedClockBounds

/-!
# Full-output weighted simulation from actual native program families

Every branch is a given native involution program. Unequal branch lengths are
kept throughout the clock construction; all analytic clock bounds and physical
active-clock implementations are derived. Only original labeled primitives,
extended by spectators, occur in the resulting simulation program.
-/
namespace SparseHamiltonian.NativeWeightedSimulation
noncomputable section
open ContinuousLinearMap OracleCircuit NativeHeterogeneousActiveClock
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

variable {X I B L : Type*} [Fintype I] [Fintype B] [DecidableEq B]
  [Fintype L] [DecidableEq L]
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- Fixed schedule degree, before the exact weighted-budget simplification. -/
def scheduleDegree (τ Q qbar ε : ℝ) : ℕ :=
  FilterSchedule.degree Q
    ((TimeSchedule.steps τ (ε / 3) : ℝ) * TimeSchedule.stepSize τ (ε / 3) * qbar)
    (ε / 3)

/-- A single physical native family serves every reuse step. -/
abbrev evolutionOracle (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (ps : I → MultiOracleCircuit.Program F) (τ Q qbar ε : ℝ) :=
  oracle F ps (TimeSchedule.steps τ (ε / 3)) (scheduleDegree τ Q qbar ε)

/-- The input-independent encoding also embeds every public bypass cell. -/
def evolutionEncoding (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (ps : I → MultiOracleCircuit.Program F) (e : P →ₗᵢ[ℂ] EuclideanSpace ℂ B)
    (a : B) (τ Q qbar ε : ℝ) :=
  (NativeHeterogeneousActiveClock.input F ps e a (TimeSchedule.steps τ (ε / 3))
    (scheduleDegree τ Q qbar ε)).toContinuousLinearMap

/-- Physical fixed preparation for the complete simulation. -/
def simulationInput (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (ps : I → MultiOracleCircuit.Program F) (e : P →ₗᵢ[ℂ] EuclideanSpace ℂ B)
    (a : B) (τ Q qbar ε : ℝ) :=
  evolutionEncoding F ps e a τ Q qbar ε ∘L
    ClockQuery.evolutionInput (P := P) (V := NativeMaskedOracle.Logical (Slot F ps) B)
      τ Q qbar ε

/-- Physical fixed output preparation, including all ancillary outputs. -/
def simulationOutput (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (ps : I → MultiOracleCircuit.Program F) (e : P →ₗᵢ[ℂ] EuclideanSpace ℂ B)
    (a : B) (τ Q qbar ε : ℝ) :=
  evolutionEncoding F ps e a τ Q qbar ε ∘L
    ClockSimulation.evolutionOutput (P := P) (V := NativeMaskedOracle.Logical (Slot F ps) B)
      τ Q qbar ε

/-- Actual native-program evolution certificate. Neither a clock resolvent nor
an active query implementation is an input assumption. In the three-primitive
sparse model the multiplicative native overhead is 18 per active step. -/
theorem evolution_query_certificate [FiniteDimensional ℂ P]
    (F : L → X → EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)
    (hF : ∀ l x, IsUnitary (F l x))
    (ps : I → MultiOracleCircuit.Program F)
    (hInv : ∀ i x v, (ps i).eval x ((ps i).eval x v) = v)
    (weights : I → ℝ) (hw : ∀ i, 0 ≤ weights i) (hsum : ∑ i, weights i = 1)
    (E : I → P →ₗᵢ[ℂ] EuclideanSpace ℂ B) (e : P →ₗᵢ[ℂ] EuclideanSpace ℂ B)
    (a : B) (image : L → X → B)
    (hvalid : ∀ l x, F l x (EuclideanSpace.single a 1) = EuclideanSpace.single (image l x) 1)
    (τ Q ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hqQ : ∀ i, (MultiQueryClock.slots (ps i) : ℝ) ≤ Q)
    (hε : 0 < ε) (hεOne : ε ≤ 1) :
    let qbar := MultiWeightedProgramClockBounds.averageLength weights ps
    ∃ p : MultiOracleCircuit.Program (evolutionOracle F ps τ Q qbar ε),
      p.count ≤ 6 * FilterSchedule.degree Q (τ * qbar) (ε / 3) * (6 * Fintype.card L) ∧
      (p.count : ℝ) ≤ 384 * ((6 * Fintype.card L : ℕ) : ℝ) *
        (τ * qbar + Q * (1 + Real.log (3 * (Q + τ * qbar + 2) / ε))) ∧
      (simulationInput F ps e a τ Q qbar ε)† ∘L simulationInput F ps e a τ Q qbar ε = 1 ∧
      (simulationOutput F ps e a τ Q qbar ε)† ∘L simulationOutput F ps e a τ Q qbar ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L simulationInput F ps e a τ Q qbar ε -
          simulationOutput F ps e a τ Q qbar ε ∘L
            NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
              MultiWeightedProgramClockBounds.generator weights ps E x)‖ ≤ ε := by
  let qbar := MultiWeightedProgramClockBounds.averageLength weights ps
  obtain ⟨hD, hJ, hRight, hLeft, hNorm, hBoundary, hSelf, hH, hEnd, hSq, hAvg⟩ :=
    NativeWeightedClockBounds.family_promises F weights ps hw hsum Q hQ hqQ hF hInv E
  have hEnc : (evolutionEncoding F ps e a τ Q qbar ε)† ∘L
      evolutionEncoding F ps e a τ Q qbar ε = 1 :=
    (NativeHeterogeneousActiveClock.input F ps e a (TimeSchedule.steps τ (ε / 3))
      (scheduleDegree τ Q qbar ε)).adjoint_comp_self
  apply LabeledActiveClockQuery.evolution_query_certificate
    (flatFamilyClock F ps hF hInv) (NativeWeightedClockBounds.flatResolvent F ps hF hInv)
    (NativeWeightedClockBounds.flatBoundary F weights ps E)
    (MultiWeightedProgramClockBounds.generator weights ps E)
    τ Q (Real.sqrt (qbar / 2)) qbar ε hτ hQ hD hJ hRight hLeft hNorm hBoundary
    hSelf hH hEnd hSq hAvg hε hεOne (evolutionOracle F ps τ Q qbar ε)
    (fun l x => NativeMaskedOracle.oracle_unitary (F l) (hF l) x)
    (evolutionEncoding F ps e a τ Q qbar ε) hEnc (6 * Fintype.card L)
  intro r _
  exact ⟨program F ps a (TimeSchedule.steps τ (ε / 3)) (scheduleDegree τ Q qbar ε) r,
    program_intertwines F ps hF hInv a image hvalid e
      (TimeSchedule.steps τ (ε / 3)) (scheduleDegree τ Q qbar ε) r,
    (program_count F ps a _ _ r).le⟩

end
end SparseHamiltonian.NativeWeightedSimulation
