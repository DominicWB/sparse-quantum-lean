import SparseHamiltonian.SharpClockSimulation

namespace SparseHamiltonian.SharpClockQuery

noncomputable section
open ContinuousLinearMap OracleCircuit
open GlobalResolvent ChronologicalResolvent ChronologicalCatalyst GlobalColligation
open scoped InnerProduct
set_option maxRecDepth 4096

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Complete coherent workspace for the chosen clock and filter schedule. -/
abbrev Space (w Q qbar : ℝ) (T : ℕ) (δ : ℝ) :=
  PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := BlockOperator.H T V)
    (SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ * (SharpFilterSchedule.length Q - 1)))

/-- The input preparation depends only on fixed schedule parameters. -/
def input (w Q qbar : ℝ) (T : ℕ) (δ : ℝ) :
    P →L[ℂ] Space (P := P) (V := V) w Q qbar T δ :=
  SmoothingLCU.input (P := P) (V := BlockOperator.H T V)
    (AveragingPolynomial.filter (SharpFilterSchedule.length Q)
      (SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ)).coeff
    (SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ)

/-- One complete synchronized layer of the actual chronological clock reuse. -/
def layer (D : V →L[ℂ] V) (J : P →L[ℂ] V)
    (w Q qbar : ℝ) (T : ℕ) (δ : ℝ) (r : ℕ) :
    Space (P := P) (V := V) w Q qbar T δ →L[ℂ]
      Space (P := P) (V := V) w Q qbar T δ :=
  ReuseQuery.reuseLayer
    (((CayleyTransfer.c w : ℂ) • (1 : P →L[ℂ] P)) ^ T)
    (publicExit ((CayleyTransfer.c w : ℂ) • 1)
      ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D)) T)
    (stackedResponse ((CayleyTransfer.sigma w : ℂ) • J)
      ((CayleyTransfer.c w : ℂ) • 1) T)
    (globalPrivateBlock D J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
      (CayleyTransfer.sigma w) T)
    (SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ) r

/-- The scheduled input is a genuine isometry. -/
theorem input_isometry (w Q qbar : ℝ) (T : ℕ) (δ : ℝ) (hQ : 1 ≤ Q) :
    (input (P := P) (V := V) w Q qbar T δ)† ∘L input w Q qbar T δ = 1 := by
  have hL : 1 ≤ SharpFilterSchedule.length Q := by
    apply Nat.one_le_ceil_iff.mpr
    linarith
  have hd := SharpFilterSchedule.degree_pos Q ((T : ℝ) * w * qbar) δ hQ
  exact SmoothingLCU.input_isometry _ _ hd
    (ReuseWeights.concrete_absolute_mass _ _ hL hd)

/-- Layer certificates compose into the already precision-certified clock
implementation. The oracle family and the layer circuits share one workspace. -/
theorem implementation_query_certificate
    [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    {X : Type*} (D : X → V →L[ℂ] V) (J : P →L[ℂ] V)
    (w Q qbar : ℝ) (T : ℕ) (δ : ℝ)
    (hQ : 1 ≤ Q) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (hD : ∀ x, (D x)† ∘L D x = 1) (hJ : J† ∘L J = 1)
    (O : X → Space (P := P) (V := V) w Q qbar T δ →L[ℂ]
      Space (P := P) (V := V) w Q qbar T δ)
    (q : ℕ) (hLayer : ∀ r < 2 * SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ,
      Implements O (fun x => layer (D x) J w Q qbar T δ r) q) :
    ∃ p : Program O,
      p.count ≤ 6 * SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ * q ∧
      ∀ x, p.eval x ∘L input (P := P) (V := V) w Q qbar T δ =
        SharpClockSimulation.implementation (D x) J w Q qbar T δ := by
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
  have hL : 1 ≤ SharpFilterSchedule.length Q := by
    apply Nat.one_le_ceil_iff.mpr
    linarith
  exact ReuseQuery.implementation_query_certificate
    (SharpFilterSchedule.length Q) (SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ)
    hL (SharpFilterSchedule.degree_pos Q _ δ hQ) O (fun _ => A) B (fun _ => C) G hStep q hLayer

/-- Fixed input for the continuous-time schedule; no unknown operator appears
in the preparation. -/
def evolutionInput (τ Q qbar ε : ℝ) :=
  input (P := P) (V := V) (TimeSchedule.stepSize τ (ε / 3)) Q qbar
    (TimeSchedule.steps τ (ε / 3)) (ε / 3)

/-- The full workspace for the continuous-time schedule. -/
abbrev EvolutionSpace (τ Q qbar ε : ℝ) :=
  Space (P := P) (V := V) (TimeSchedule.stepSize τ (ε / 3)) Q qbar
    (TimeSchedule.steps τ (ε / 3)) (ε / 3)

/-- The whole controlled reuse layer whose implementation cost must be supplied. -/
def evolutionLayer (D : V →L[ℂ] V) (J : P →L[ℂ] V)
    (τ Q qbar ε : ℝ) (r : ℕ) :=
  layer D J (TimeSchedule.stepSize τ (ε / 3)) Q qbar
    (TimeSchedule.steps τ (ε / 3)) (ε / 3) r

/-- A uniform family of clock certificates and whole-layer implementations
produces a unitary oracle program with the claimed full-output precision.
The query bound depends on precision only through the displayed logarithm;
the separate whole-layer cost `q` remains an explicit hypothesis. -/
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
    (O : X → EvolutionSpace (P := P) (V := V) τ Q qbar ε →L[ℂ]
      EvolutionSpace (P := P) (V := V) τ Q qbar ε)
    (hO : ∀ x, IsUnitary (O x)) (q : ℕ)
    (hLayer : ∀ r < 2 * SharpFilterSchedule.degree Q (τ * qbar) (ε / 3),
      Implements O (fun x => evolutionLayer (D x) J τ Q qbar ε r) q) :
    ∃ p : Program O,
      p.count ≤ 6 * SharpFilterSchedule.degree Q (τ * qbar) (ε / 3) * q ∧
      (p.count : ℝ) ≤ 768 * (q : ℝ) *
        (τ * qbar + Q * (1 + Real.log (3 / ε))) ∧
      (evolutionInput (P := P) (V := V) τ Q qbar ε)† ∘L
        evolutionInput τ Q qbar ε = 1 ∧
      (SharpClockSimulation.evolutionOutput (P := P) (V := V) τ Q qbar ε)† ∘L
        SharpClockSimulation.evolutionOutput τ Q qbar ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L evolutionInput (P := P) (V := V) τ Q qbar ε -
          SharpClockSimulation.evolutionOutput (P := P) (V := V) τ Q qbar ε ∘L
            NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H x)‖ ≤ ε := by
  let δ := ε / 3
  let T := TimeSchedule.steps τ δ
  let w := TimeSchedule.stepSize τ δ
  have hBudget : (T : ℝ) * w * qbar = τ * qbar :=
    TimeSchedule.weighted_budget_eq τ δ qbar
  have hLayer' : ∀ r < 2 * SharpFilterSchedule.degree Q ((T : ℝ) * w * qbar) δ,
      Implements O (fun x => layer (D x) J w Q qbar T δ r) q := by
    intro r hr
    apply hLayer r
    simpa only [hBudget] using hr
  obtain ⟨p, hp, hEval⟩ := implementation_query_certificate D J w Q qbar T δ hQ
    (TimeSchedule.stepSize_nonneg τ δ hτ) (TimeSchedule.stepSize_le_quarter τ δ)
    hD hJ O q hLayer'
  have hp' : p.count ≤ 6 * SharpFilterSchedule.degree Q (τ * qbar) (ε / 3) * q := by
    simpa only [hBudget] using hp
  have hqbar : 0 ≤ qbar := by nlinarith [sq_nonneg b]
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδOne : δ ≤ 1 := by dsimp [δ]; linarith
  have hDegree := SharpFilterSchedule.degree_le Q (τ * qbar) δ hQ
    (mul_nonneg hτ hqbar) hδ hδOne
  have hArg : 1 / δ = 3 / ε := by
    dsimp [δ]
    ring
  dsimp only [SharpFilterSchedule.logBudget] at hDegree
  rw [hArg] at hDegree
  refine ⟨p, hp', ?_, input_isometry _ _ _ _ _ hQ,
    SharpClockSimulation.evolutionOutput_isometry _ _ _ _ hQ, fun x => ?_⟩
  · have hNat : (p.count : ℝ) ≤ 6 * (SharpFilterSchedule.degree Q (τ * qbar) δ : ℝ) *
        (q : ℝ) := by exact_mod_cast hp'
    have hProduct := mul_le_mul_of_nonneg_right hDegree (show (0 : ℝ) ≤ 6 * q by positivity)
    nlinarith
  · refine ⟨p.eval_unitary hO x, ?_⟩
    rw [show evolutionInput (P := P) (V := V) τ Q qbar ε = input w Q qbar T δ from rfl,
      hEval]
    exact (SharpClockSimulation.evolution_error (D x) (R1 x) J (H x) τ Q b qbar ε hτ hQ
      (hD x) hJ (hRight x) (hLeft x) (hR1 x) (hBoundary x) (hSelf x) (hH x)
      (hEndpoint x) hbq hqQ hε hεOne).2.1

end
end SparseHamiltonian.SharpClockQuery
