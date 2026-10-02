import SparseHamiltonian.LabeledEncodedAmplification

/-!
# Active clock simulation retaining native oracle labels

A fixed isometric encoding embeds the logical coherent workspace into the
physical oracle registers. Active clock implementations need only be correct
on its image. Fixed coupling gates are lifted to physical unitaries, and the
full simulation and query bounds transfer without conditions on complement
states. Neither the boundary map nor the encoding may depend on unknown data.
-/

namespace SparseHamiltonian.LabeledActiveClockQuery

noncomputable section
open ContinuousLinearMap OracleCircuit LabeledEncodedOracle ReuseLayerFactorization
open GlobalResolvent ChronologicalResolvent ChronologicalCatalyst GlobalColligation
open scoped InnerProduct
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

variable {Label : Type*}
variable {P V K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The lifted, fixed coupling adds no queries to an encoded active clock
implementation. Its extension outside the encoding is supplied by `lift`. -/
theorem clockLayer_implementsOn [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {X : Type*} (D : X → V →L[ℂ] V) (J : P →L[ℂ] V) (hJ : J† ∘L J = 1)
    (w Q qbar : ℝ) (T : ℕ) (δ : ℝ) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (r q : ℕ) (O : Label → X → K →L[ℂ] K)
    (E : ClockQuery.Space (P := P) (V := V) w Q qbar T δ →L[ℂ] K)
    (hE : E† ∘L E = 1)
    (hQuery : ImplementsOn O (fun x => activeClock (P := P) (D x) T
      (FilterSchedule.degree Q ((T : ℝ) * w * qbar) δ) r) E q) :
    ImplementsOn O (fun x => ClockQuery.layer (D x) J w Q qbar T δ r) E q := by
  obtain ⟨_hκ, _hκUpper, hκc, hσc, _hσw⟩ := CayleyTransfer.scalar_promises w hw hwQuarter
  have hFixed := ImplementsOn.fixed (O := O) hE
    (couplingLayer J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
      (CayleyTransfer.sigma w) T (FilterSchedule.degree Q ((T : ℝ) * w * qbar) δ) r)
    (couplingLayer_unitary J hJ _ _ _ hκc hσc T _ r)
  have h := (hFixed.mul hQuery).congr (fun x =>
    (clockReuseLayer_factor (D x) J _ _ _ T _ r).symm)
  simpa only [Nat.zero_add, ClockQuery.layer] using h

/-- Encoded whole-layer certificates compose into the precise logical clock
implementation, now acting on prepared vectors in the physical workspace. -/
theorem layer_implementation_query_certificate
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {X : Type*} (D : X → V →L[ℂ] V) (J : P →L[ℂ] V)
    (w Q qbar : ℝ) (T : ℕ) (δ : ℝ)
    (hQ : 1 ≤ Q) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (hD : ∀ x, (D x)† ∘L D x = 1) (hJ : J† ∘L J = 1)
    (O : Label → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (E : ClockQuery.Space (P := P) (V := V) w Q qbar T δ →L[ℂ] K)
    (hE : E† ∘L E = 1)
    (q : ℕ) (hLayer : ∀ r < 2 * FilterSchedule.degree Q ((T : ℝ) * w * qbar) δ,
      ImplementsOn O (fun x => ClockQuery.layer (D x) J w Q qbar T δ r) E q) :
    ∃ p : MultiOracleCircuit.Program O,
      p.count ≤ 6 * FilterSchedule.degree Q ((T : ℝ) * w * qbar) δ * q ∧
      ∀ x, p.eval x ∘L (E ∘L ClockQuery.input (P := P) (V := V) w Q qbar T δ) =
        E ∘L ClockSimulation.implementation (D x) J w Q qbar T δ := by
  let A := ((CayleyTransfer.c w : ℂ) • (1 : P →L[ℂ] P)) ^ T
  let B := fun x => publicExit ((CayleyTransfer.c w : ℂ) • (1 : P →L[ℂ] P))
    ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D x)) T
  let C := stackedResponse ((CayleyTransfer.sigma w : ℂ) • J)
    ((CayleyTransfer.c w : ℂ) • 1) T
  let G := fun x => globalPrivateBlock (D x) J (CayleyTransfer.c w)
    (CayleyTransfer.kappa w) (CayleyTransfer.sigma w) T
  obtain ⟨_hκ, _hκUpper, hκc, hσc, _hσw⟩ :=
    CayleyTransfer.scalar_promises w hw hwQuarter
  have hStep : ∀ x p v, ‖A p + B x v‖ ^ 2 + ‖G x v + C p‖ ^ 2 =
      ‖p‖ ^ 2 + ‖v‖ ^ 2 := by
    intro x p v
    have h := chronological_full_energy
      (localPrivateBlock (D x) J (CayleyTransfer.kappa w))
      ((CayleyTransfer.sigma w : ℂ) • J) ((CayleyTransfer.c w : ℂ) • 1)
      ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D x))
      (LocalRotation.local_step_energy (D x) J _ _ _ hκc hσc (hD x) hJ) T p v
    change ‖A p + B x v‖ ^ 2 + ‖C p + G x v‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2 at h
    simpa only [add_comm (G x v) (C p)] using h
  have hL : 1 ≤ FilterSchedule.length Q := by
    apply Nat.one_le_ceil_iff.mpr
    linarith
  exact LabeledEncodedAmplification.implementation_query_certificate
    (FilterSchedule.length Q) (FilterSchedule.depth Q ((T : ℝ) * w * qbar) δ)
    hL (FilterSchedule.degree_pos Q _ δ hQ) O hO E hE (fun _ => A) B (fun _ => C) G
      hStep q hLayer

/-- A physical active clock implementation suffices for the entire amplified
program. Its count is independent of the fixed chronological network's size. -/
theorem implementation_query_certificate
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {X : Type*} (D : X → V →L[ℂ] V) (J : P →L[ℂ] V)
    (w Q qbar : ℝ) (T : ℕ) (δ : ℝ)
    (hQ : 1 ≤ Q) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (hD : ∀ x, (D x)† ∘L D x = 1) (hJ : J† ∘L J = 1)
    (O : Label → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (E : ClockQuery.Space (P := P) (V := V) w Q qbar T δ →L[ℂ] K)
    (hE : E† ∘L E = 1) (q : ℕ)
    (hQuery : ∀ r < 2 * FilterSchedule.degree Q ((T : ℝ) * w * qbar) δ,
      ImplementsOn O (fun x => activeClock (P := P) (D x) T
        (FilterSchedule.degree Q ((T : ℝ) * w * qbar) δ) r) E q) :
    ∃ p : MultiOracleCircuit.Program O,
      p.count ≤ 6 * FilterSchedule.degree Q ((T : ℝ) * w * qbar) δ * q ∧
      ∀ x, p.eval x ∘L (E ∘L ClockQuery.input (P := P) (V := V) w Q qbar T δ) =
        E ∘L ClockSimulation.implementation (D x) J w Q qbar T δ := by
  apply layer_implementation_query_certificate D J w Q qbar T δ
    hQ hw hwQuarter hD hJ O hO E hE q
  intro r hr
  exact clockLayer_implementsOn D J hJ w Q qbar T δ hw hwQuarter r q O E hE (hQuery r hr)

/-- A physical program achieves the full continuous-time simulation error and
logarithmic precision query bound on a fixed encoded workspace. The physical
input and output preparations are isometries; no preparation cost is asserted. -/
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
    (O : Label → X → K →L[ℂ] K) (hO : ∀ l x, IsUnitary (O l x))
    (E : ClockQuery.EvolutionSpace (P := P) (V := V) τ Q qbar ε →L[ℂ] K)
    (hE : E† ∘L E = 1) (q : ℕ)
    (hQuery : ∀ r < 2 * FilterSchedule.degree Q (τ * qbar) (ε / 3),
      ImplementsOn O
        (fun x => ActiveClockQuery.evolutionActiveClock (P := P) (D x) τ Q qbar ε r) E q) :
    ∃ p : MultiOracleCircuit.Program O,
      p.count ≤ 6 * FilterSchedule.degree Q (τ * qbar) (ε / 3) * q ∧
      (p.count : ℝ) ≤ 384 * (q : ℝ) *
        (τ * qbar + Q * (1 + Real.log (3 * (Q + τ * qbar + 2) / ε))) ∧
      (E ∘L ClockQuery.evolutionInput (P := P) (V := V) τ Q qbar ε)† ∘L
        (E ∘L ClockQuery.evolutionInput τ Q qbar ε) = 1 ∧
      (E ∘L ClockSimulation.evolutionOutput (P := P) (V := V) τ Q qbar ε)† ∘L
        (E ∘L ClockSimulation.evolutionOutput τ Q qbar ε) = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L (E ∘L ClockQuery.evolutionInput (P := P) (V := V) τ Q qbar ε) -
          E ∘L ClockSimulation.evolutionOutput (P := P) (V := V) τ Q qbar ε ∘L
            NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H x)‖ ≤ ε := by
  let δ := ε / 3
  let T := TimeSchedule.steps τ δ
  let w := TimeSchedule.stepSize τ δ
  have hBudget : (T : ℝ) * w * qbar = τ * qbar :=
    TimeSchedule.weighted_budget_eq τ δ qbar
  have hQuery' : ∀ r < 2 * FilterSchedule.degree Q ((T : ℝ) * w * qbar) δ,
      ImplementsOn O (fun x => activeClock (P := P) (D x) T
        (FilterSchedule.degree Q ((T : ℝ) * w * qbar) δ) r) E q := by
    intro r hr
    apply hQuery r
    simpa only [hBudget] using hr
  obtain ⟨p, hp, hEval⟩ := implementation_query_certificate D J w Q qbar T δ hQ
    (TimeSchedule.stepSize_nonneg τ δ hτ) (TimeSchedule.stepSize_le_quarter τ δ)
    hD hJ O hO E hE q hQuery'
  have hp' : p.count ≤ 6 * FilterSchedule.degree Q (τ * qbar) (ε / 3) * q := by
    simpa only [hBudget] using hp
  have hqbar : 0 ≤ qbar := by nlinarith [sq_nonneg b]
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδOne : δ ≤ 1 := by dsimp [δ]; linarith
  have hDegree := FilterSchedule.degree_le Q (τ * qbar) δ hQ
    (mul_nonneg hτ hqbar) hδ hδOne
  have hArg : (Q + τ * qbar + 2) / δ = 3 * (Q + τ * qbar + 2) / ε := by
    dsimp [δ]
    ring
  dsimp only [FilterSchedule.logBudget] at hDegree
  rw [hArg] at hDegree
  have hInput : (E ∘L ClockQuery.evolutionInput (P := P) (V := V) τ Q qbar ε)† ∘L
      (E ∘L ClockQuery.evolutionInput τ Q qbar ε) = 1 := by
    apply norm_map_iff_adjoint_comp_self _ |>.mp
    intro v
    rw [comp_apply, E.norm_map_iff_adjoint_comp_self.mpr hE]
    exact (ClockQuery.evolutionInput (P := P) (V := V) τ Q qbar ε).norm_map_iff_adjoint_comp_self.mpr
      (ClockQuery.input_isometry w Q qbar T δ hQ) v
  have hOutput : (E ∘L ClockSimulation.evolutionOutput (P := P) (V := V) τ Q qbar ε)† ∘L
      (E ∘L ClockSimulation.evolutionOutput τ Q qbar ε) = 1 := by
    apply norm_map_iff_adjoint_comp_self _ |>.mp
    intro v
    rw [comp_apply, E.norm_map_iff_adjoint_comp_self.mpr hE]
    exact (ClockSimulation.evolutionOutput (P := P) (V := V) τ Q qbar ε).norm_map_iff_adjoint_comp_self.mpr
      (ClockSimulation.evolutionOutput_isometry τ Q qbar ε hQ) v
  refine ⟨p, hp', ?_, hInput, hOutput, fun x => ?_⟩
  · have hNat : (p.count : ℝ) ≤ 6 * (FilterSchedule.degree Q (τ * qbar) δ : ℝ) *
        (q : ℝ) := by exact_mod_cast hp'
    have hProduct := mul_le_mul_of_nonneg_right hDegree (show (0 : ℝ) ≤ 6 * q by positivity)
    nlinarith
  · refine ⟨p.eval_unitary hO x, ?_⟩
    rw [show ClockQuery.evolutionInput (P := P) (V := V) τ Q qbar ε =
      ClockQuery.input w Q qbar T δ from rfl, hEval, ← comp_sub, EncodedOracle.norm_comp_eq E hE]
    exact (ClockSimulation.evolution_error (D x) (R1 x) J (H x) τ Q b qbar ε hτ hQ
      (hD x) hJ (hRight x) (hLeft x) (hR1 x) (hBoundary x) (hSelf x) (hH x)
      (hEndpoint x) hbq hqQ hε hεOne).2.1

end
end SparseHamiltonian.LabeledActiveClockQuery
