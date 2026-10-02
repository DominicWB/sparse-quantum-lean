import SparseHamiltonian.ReuseLayerFactorization

/-!
# Hamiltonian simulation using explicit active clock implementations

The full chronological coupling is derived to be a fixed unitary. The only
query implementation hypotheses now concern the parallel private clock action
on unfinished branches, all relative to the same supplied primitive oracle.
-/

namespace SparseHamiltonian.ActiveClockQuery

noncomputable section
open ContinuousLinearMap OracleCircuit ReuseLayerFactorization
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Composing the isolated clock actions gives the complete amplified program.
The query count is independent of the size of the fixed chronological network. -/
theorem implementation_query_certificate
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {X : Type*} (D : X → V →L[ℂ] V) (J : P →L[ℂ] V)
    (w Q qbar : ℝ) (T : ℕ) (δ : ℝ)
    (hQ : 1 ≤ Q) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (hD : ∀ x, (D x)† ∘L D x = 1) (hJ : J† ∘L J = 1)
    (O : X → ClockQuery.Space (P := P) (V := V) w Q qbar T δ →L[ℂ]
      ClockQuery.Space (P := P) (V := V) w Q qbar T δ)
    (q : ℕ)
    (hQuery : ∀ r < 2 * FilterSchedule.degree Q ((T : ℝ) * w * qbar) δ,
      Implements O (fun x => activeClock (P := P) (D x) T
        (FilterSchedule.degree Q ((T : ℝ) * w * qbar) δ) r) q) :
    ∃ p : Program O,
      p.count ≤ 6 * FilterSchedule.degree Q ((T : ℝ) * w * qbar) δ * q ∧
      ∀ x, p.eval x ∘L ClockQuery.input (P := P) (V := V) w Q qbar T δ =
        ClockSimulation.implementation (D x) J w Q qbar T δ := by
  apply ClockQuery.implementation_query_certificate D J w Q qbar T δ
    hQ hw hwQuarter hD hJ O q
  intro r hr
  exact clockLayer_implements D J hJ w Q qbar T δ hw hwQuarter r q O (hQuery r hr)

/-- The isolated clock action for the continuous-time simulation schedule. -/
def evolutionActiveClock (D : V →L[ℂ] V) (τ Q qbar ε : ℝ) (r : ℕ) :
    ClockQuery.EvolutionSpace (P := P) (V := V) τ Q qbar ε →L[ℂ]
      ClockQuery.EvolutionSpace (P := P) (V := V) τ Q qbar ε :=
  activeClock D (TimeSchedule.steps τ (ε / 3))
    (FilterSchedule.degree Q
      ((TimeSchedule.steps τ (ε / 3) : ℝ) * TimeSchedule.stepSize τ (ε / 3) * qbar)
      (ε / 3)) r

/-- A primitive-oracle implementation of each active clock action suffices for
the full-output simulation guarantee and the logarithmic precision query bound. -/
theorem evolution_query_certificate
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {X : Type*} (D R1 : X → V →L[ℂ] V) (J : P →L[ℂ] V) (H : X → P →L[ℂ] P)
    (τ Q b qbar ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hD : ∀ x, (D x)† ∘L D x = 1) (hJ : J† ∘L J = 1)
    (hRight : ∀ x, (1 - D x) ∘L R1 x = 1)
    (hLeft : ∀ x, R1 x ∘L (1 - D x) = 1)
    (hR1 : ∀ x, ‖R1 x‖ ≤ Q)
    (hBoundary : ∀ x, J† ∘L R1 x ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H x))
    (hSelf : ∀ x, star (H x) = H x) (hH : ∀ x, ‖H x‖ ≤ 1)
    (hEndpoint : ∀ x, ‖R1 x ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (O : X → ClockQuery.EvolutionSpace (P := P) (V := V) τ Q qbar ε →L[ℂ]
      ClockQuery.EvolutionSpace (P := P) (V := V) τ Q qbar ε)
    (hO : ∀ x, IsUnitary (O x)) (q : ℕ)
    (hQuery : ∀ r < 2 * FilterSchedule.degree Q (τ * qbar) (ε / 3),
      Implements O (fun x => evolutionActiveClock (P := P) (D x) τ Q qbar ε r) q) :
    ∃ p : Program O,
      p.count ≤ 6 * FilterSchedule.degree Q (τ * qbar) (ε / 3) * q ∧
      (p.count : ℝ) ≤ 384 * (q : ℝ) *
        (τ * qbar + Q * (1 + Real.log (3 * (Q + τ * qbar + 2) / ε))) ∧
      (ClockQuery.evolutionInput (P := P) (V := V) τ Q qbar ε)† ∘L
        ClockQuery.evolutionInput τ Q qbar ε = 1 ∧
      (ClockSimulation.evolutionOutput (P := P) (V := V) τ Q qbar ε)† ∘L
        ClockSimulation.evolutionOutput τ Q qbar ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L ClockQuery.evolutionInput (P := P) (V := V) τ Q qbar ε -
          ClockSimulation.evolutionOutput (P := P) (V := V) τ Q qbar ε ∘L
            NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H x)‖ ≤ ε := by
  apply ClockQuery.evolution_query_certificate D R1 J H τ Q b qbar ε hτ hQ
    hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ hε hεOne O hO q
  intro r hr
  exact clockLayer_implements D J hJ (TimeSchedule.stepSize τ (ε / 3)) Q qbar
    (TimeSchedule.steps τ (ε / 3)) (ε / 3)
    (TimeSchedule.stepSize_nonneg τ (ε / 3) hτ)
    (TimeSchedule.stepSize_le_quarter τ (ε / 3)) r q O (hQuery r hr)

end
end SparseHamiltonian.ActiveClockQuery
