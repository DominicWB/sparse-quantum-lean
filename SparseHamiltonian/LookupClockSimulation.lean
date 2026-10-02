import SparseHamiltonian.EncodedActiveClockQuery

/-!
# Full-output Hamiltonian simulation from ordinary lookup clock steps

A fixed unitary followed by a signed lookup diagonal is implemented on all
active clock registers using two ordinary queries. Combining this concrete
implementation with the analytic clock promises removes the query-circuit
premise from the simulation theorem. All masks, layouts, and free gates are
independent of the unknown table.
-/

namespace SparseHamiltonian.LookupClockSimulation

noncomputable section
open ContinuousLinearMap OracleCircuit MaskedLookupCurry
open scoped InnerProduct

variable {X C A Z : Type*} [Fintype C] [Fintype A] [Fintype Z] [AddCommGroup Z]

/-- One ordinary scratch lookup, with every simulation index a spectator.
This oracle is common to every synchronized layer. -/
def evolutionOracle (f : X → A → Z) (τ Q qbar ε : ℝ) (x : X) :
    ClockQuery.EvolutionSpace (P := Payload A Z)
      (V := PiLp 2 (fun _ : C => Payload A Z)) τ Q qbar ε →L[ℂ]
    ClockQuery.EvolutionSpace (P := Payload A Z)
      (V := PiLp 2 (fun _ : C => Payload A Z)) τ Q qbar ε :=
  ActiveLookupClock.ordinaryOracle C f (TimeSchedule.steps τ (ε / 3))
    (FilterSchedule.degree Q
      ((TimeSchedule.steps τ (ε / 3) : ℝ) * TimeSchedule.stepSize τ (ε / 3) * qbar)
      (ε / 3)) x

/-- The complete simulation's common oracle is an actual unitary lookup. -/
theorem evolutionOracle_unitary (f : X → A → Z) (τ Q qbar ε : ℝ) (x : X) :
    IsUnitary (evolutionOracle (C := C) f τ Q qbar ε x) :=
  ActiveLookupClock.ordinaryOracle_unitary C f _ _ x

/-- All whole-layer query obligations are discharged by the ordinary lookup
construction. Only analytic promises for the specified clock remain. -/
theorem evolution_query_certificate (f : X → A → Z)
    (F : PiLp 2 (fun _ : C => Payload A Z) →L[ℂ]
      PiLp 2 (fun _ : C => Payload A Z)) (hF : IsUnitary F) (m : C → ℤ)
    (D R1 : X → PiLp 2 (fun _ : C => Payload A Z) →L[ℂ]
      PiLp 2 (fun _ : C => Payload A Z))
    (hFactor : ∀ x, D x = F ∘L WeightedClock.diagonal (fun c => localSigned (m c) f x))
    (J : Payload A Z →L[ℂ] PiLp 2 (fun _ : C => Payload A Z))
    (H : X → Payload A Z →L[ℂ] Payload A Z)
    (τ Q b qbar ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hD : ∀ x, (D x)† ∘L D x = 1) (hJ : J† ∘L J = 1)
    (hRight : ∀ x, (1 - D x) ∘L R1 x = 1)
    (hLeft : ∀ x, R1 x ∘L (1 - D x) = 1)
    (hR1 : ∀ x, ‖R1 x‖ ≤ Q)
    (hBoundary : ∀ x, J† ∘L R1 x ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H x))
    (hSelf : ∀ x, star (H x) = H x) (hH : ∀ x, ‖H x‖ ≤ 1)
    (hEndpoint : ∀ x, ‖R1 x ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ∃ p : Program (evolutionOracle (C := C) f τ Q qbar ε),
      p.count ≤ 12 * FilterSchedule.degree Q (τ * qbar) (ε / 3) ∧
      (p.count : ℝ) ≤ 768 *
        (τ * qbar + Q * (1 + Real.log (3 * (Q + τ * qbar + 2) / ε))) ∧
      (ClockQuery.evolutionInput (P := Payload A Z)
        (V := PiLp 2 (fun _ : C => Payload A Z)) τ Q qbar ε)† ∘L
        ClockQuery.evolutionInput τ Q qbar ε = 1 ∧
      (ClockSimulation.evolutionOutput (P := Payload A Z)
        (V := PiLp 2 (fun _ : C => Payload A Z)) τ Q qbar ε)† ∘L
        ClockSimulation.evolutionOutput τ Q qbar ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L ClockQuery.evolutionInput (P := Payload A Z)
            (V := PiLp 2 (fun _ : C => Payload A Z)) τ Q qbar ε -
          ClockSimulation.evolutionOutput (P := Payload A Z)
            (V := PiLp 2 (fun _ : C => Payload A Z)) τ Q qbar ε ∘L
            NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H x)‖ ≤ ε := by
  have hQuery : ∀ r < 2 * FilterSchedule.degree Q (τ * qbar) (ε / 3),
      Implements (evolutionOracle (C := C) f τ Q qbar ε)
        (fun x => ActiveClockQuery.evolutionActiveClock (P := Payload A Z)
          (D x) τ Q qbar ε r) 2 := by
    intro r _hr
    have h := ActiveLookupClock.activeClock_fixed_signed_two_queries f F hF m
      (TimeSchedule.steps τ (ε / 3))
      (FilterSchedule.degree Q
        ((TimeSchedule.steps τ (ε / 3) : ℝ) * TimeSchedule.stepSize τ (ε / 3) * qbar)
        (ε / 3)) r
    apply h.congr
    intro x
    rw [ActiveClockQuery.evolutionActiveClock, hFactor]
  obtain ⟨p, hn, hr, hi, ho, he⟩ :=
    ActiveClockQuery.evolution_query_certificate D R1 J H τ Q b qbar ε hτ hQ
      hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ hε hεOne
      (evolutionOracle (C := C) f τ Q qbar ε)
      (evolutionOracle_unitary f τ Q qbar ε) 2 hQuery
  refine ⟨p, ?_, ?_, hi, ho, he⟩
  · omega
  · simpa only [Nat.cast_ofNat, show (384 : ℝ) * 2 = 768 by norm_num] using hr

/-- For a full-workspace involution program, both the analytic clock promises
and the primitive lookup implementation are proved. The only supplied circuit
is the original uniform program; no clock or simulation-query premise remains. -/
theorem program_evolution_query_certificate (f : X → A → Z)
    (p : Program (localSigned 1 f))
    (hInv : ∀ x v, p.eval x (p.eval x v) = v)
    (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    let Q : ℝ := QueryClockStep.slots p
    ∃ c : Program (evolutionOracle (C := Fin (p.count + 1 + 1)) f τ Q Q ε),
      c.count ≤ 12 * FilterSchedule.degree Q (τ * Q) (ε / 3) ∧
      (c.count : ℝ) ≤ 768 *
        (τ * Q + Q * (1 + Real.log (3 * (Q + τ * Q + 2) / ε))) ∧
      (ClockQuery.evolutionInput (P := Payload A Z)
        (V := ClockOperators.H (p.count + 1) (Payload A Z)) τ Q Q ε)† ∘L
        ClockQuery.evolutionInput τ Q Q ε = 1 ∧
      (ClockSimulation.evolutionOutput (P := Payload A Z)
        (V := ClockOperators.H (p.count + 1) (Payload A Z)) τ Q Q ε)† ∘L
        ClockSimulation.evolutionOutput τ Q Q ε = 1 ∧
      ∀ x, IsUnitary (c.eval x) ∧
        ‖c.eval x ∘L ClockQuery.evolutionInput (P := Payload A Z)
            (V := ClockOperators.H (p.count + 1) (Payload A Z)) τ Q Q ε -
          ClockSimulation.evolutionOutput (P := Payload A Z)
            (V := ClockOperators.H (p.count + 1) (Payload A Z)) τ Q Q ε ∘L
            NormedSpace.exp ((-Complex.I * (τ : ℂ)) • p.eval x)‖ ≤ ε := by
  obtain ⟨hQ, hD, hJ, hRight, hLeft, hR, hBoundary, hSelf, hH, hEndpoint, hbq, hqQ⟩ :=
    ProgramClockBounds.programClock_promises p (localSigned_unitary 1 f) hInv
  have hFactor (x : X) :
      QueryClockStep.programClock p (localSigned_unitary 1 f) hInv x =
        ActiveLookupClock.fixedClockGate f p ∘L
          WeightedClock.diagonal (fun j => localSigned (LookupClockStep.clockMask f p j) f x) := by
    rw [LookupClockStep.signed_diagonal_eq_selected, ActiveLookupClock.fixedClockGate,
      ContinuousLinearMap.comp_assoc]
    exact QueryClockStep.programClock_factor p (localSigned_unitary 1 f) hInv x
  exact evolution_query_certificate f (ActiveLookupClock.fixedClockGate f p)
    (ActiveLookupClock.fixedClockGate_unitary f p) (LookupClockStep.clockMask f p)
    (QueryClockStep.programClock p (localSigned_unitary 1 f) hInv)
    (QueryClockStep.programResolvent p (localSigned_unitary 1 f) hInv) hFactor
    (ClockOperators.boundary (p.count + 1)) p.eval τ (QueryClockStep.slots p)
    (Real.sqrt ((QueryClockStep.slots p : ℝ) / 2)) (QueryClockStep.slots p) ε
    hτ hQ hD hJ hRight hLeft hR hBoundary hSelf hH hEndpoint hbq hqQ hε hεOne

end
end SparseHamiltonian.LookupClockSimulation
