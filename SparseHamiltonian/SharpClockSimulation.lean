import SparseHamiltonian.SharpGlobalFilter

/-!
# Sharp clock simulation and its conditional oracle query certificate

This extension uses the improved filter schedule while retaining the existing
chronological catalyst, Cayley approximation, full-output error, and physical
amplification constructions. Its precision logarithm is independent of the
resolvent scale Q. The whole-layer oracle cost remains an explicit assumption:
this file does not assert a native sparse-oracle implementation for the new
entrywise Cayley construction.

Depends on the baseline SparseHamiltonian development and the preceding
SharpFilterSchedule and SharpGlobalFilter extensions.
-/

namespace SparseHamiltonian.SharpClockSimulation

noncomputable section

open ContinuousLinearMap
open GlobalResolvent ChronologicalResolvent ChronologicalCatalyst GlobalColligation
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The explicitly scheduled amplified implementation of the full chronological
clock transducer, including every private and branch register. -/
def implementation (D : V →L[ℂ] V) (J : P →L[ℂ] V)
    (w Q qbar : ℝ) (T : ℕ) (δ : ℝ) :=
  AmplifiedSmoothing.implementation (SharpFilterSchedule.length Q)
    (SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ)
    (((CayleyTransfer.c w : ℂ) • (1 : P →L[ℂ] P)) ^ T)
    (publicExit ((CayleyTransfer.c w : ℂ) • 1)
      ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D)) T)
    (stackedResponse ((CayleyTransfer.sigma w : ℂ) • J)
      ((CayleyTransfer.c w : ℂ) • 1) T)
    (globalPrivateBlock D J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
      (CayleyTransfer.sigma w) T)

/-- The clean output embedding carries all explicit signed-smoothing weights
and uniform clocks; it is independent of the simulated public input. -/
def output (w Q qbar : ℝ) (T : ℕ) (δ : ℝ) :
    P →L[ℂ] PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := BlockOperator.H T V)
      (SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ * (SharpFilterSchedule.length Q - 1))) :=
  SmoothingLCU.output (P := P) (V := BlockOperator.H T V)
    (AveragingPolynomial.filter (SharpFilterSchedule.length Q)
      (SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ)).coeff
    (SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ * (SharpFilterSchedule.length Q - 1))

set_option maxRecDepth 4096 in
/-- The clean output preparation is an isometry for the explicit filter schedule. -/
theorem output_isometry (w Q qbar : ℝ) (T : ℕ) (δ : ℝ) (hQ : 1 ≤ Q) :
    (output (P := P) (V := V) w Q qbar T δ)† ∘L output w Q qbar T δ = 1 := by
  have hL : 1 ≤ SharpFilterSchedule.length Q := by
    apply Nat.one_le_ceil_iff.mpr
    linarith
  have hd : 0 < SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ *
      (SharpFilterSchedule.length Q - 1) := SharpFilterSchedule.degree_pos Q _ δ hQ
  exact SmoothingLCU.output_isometry _ _ hd
    (ReuseWeights.concrete_absolute_mass _ _ hL hd)

set_option maxRecDepth 4096 in
/-- A clock certificate yields an actual norm-preserving amplified simulation
with complete-output error at most `2δ`, and an explicit filter degree bound.
The target public action is the constructed Cayley transform, not an arbitrary
unitary supplied as a promise. -/
theorem exists_precise_implementation
    (D R1 : V →L[ℂ] V) (J : P →L[ℂ] V) (H : P →L[ℂ] P)
    (w Q b qbar : ℝ) (T : ℕ)
    (hQ : 1 ≤ Q) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (δ : ℝ) (hδ : 0 < δ) (hδOne : δ ≤ 1) :
    let W := (T : ℝ) * w * qbar
    ∃ (Γ : P →L[ℂ] V) (U R : P →L[ℂ] P),
      CayleyTransfer.cayleyDenominator w H ∘L R = 1 ∧
      R ∘L CayleyTransfer.cayleyDenominator w H = 1 ∧
      U = CayleyTransfer.cayleyNumerator w H ∘L R ∧
      (U ^ T)† ∘L (U ^ T) = 1 ∧ (U ^ T) ∘L (U ^ T)† = 1 ∧
      ‖stackedResponse Γ U T‖ ^ 2 ≤ 3 * W ∧
      (implementation D J w Q qbar T δ)† ∘L implementation D J w Q qbar T δ = 1 ∧
      ‖implementation D J w Q qbar T δ - output (P := P) (V := V) w Q qbar T δ ∘L (U ^ T)‖ ≤ 2 * δ ∧
      (SharpFilterSchedule.degree Q W δ : ℝ) ≤
        128 * (W + Q * (1 + Real.log (1 / δ))) := by
  let W := (T : ℝ) * w * qbar
  let c := CayleyTransfer.c w
  let κ := CayleyTransfer.kappa w
  let σ := CayleyTransfer.sigma w
  let A := ((c : ℂ) • (1 : P →L[ℂ] P)) ^ T
  let B := publicExit ((c : ℂ) • (1 : P →L[ℂ] P))
    ((-(σ : ℂ)) • (J† ∘L D)) T
  let C := stackedResponse ((σ : ℂ) • J) ((c : ℂ) • 1) T
  let G := globalPrivateBlock D J c κ σ T
  obtain ⟨hκ, hκUpper, hκc, hσc, hσw⟩ := CayleyTransfer.scalar_promises w hw hwQuarter
  obtain ⟨Γ, U, hLocalPrivate, hLocalPublic, hUNorm, hPrivate, _hTrajectory, hCost⟩ :=
    exists_global_catalyst D R1 J H c κ σ w Q b qbar (by linarith) hw hκ hκUpper
      hκc hσc hσw hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ T
  obtain ⟨R, hRRight, hRLeft, hCayley⟩ :=
    local_public_is_cayley D R1 J Γ H U w hw hwQuarter hRight hLeft hJ hBoundary
      hSelf hH hLocalPrivate hLocalPublic
  have hUnitary := local_public_unitary D R1 J Γ H U w hw hwQuarter
    hRight hLeft hJ hBoundary hSelf hH hLocalPrivate hLocalPublic
  have hPowUnitary := CayleyTransfer.unitary_pow U hUnitary.1 hUnitary.2 T
  have hPublic : A + B ∘L stackedResponse Γ U T = U ^ T :=
    catalyst_public_transduction Γ U ((c : ℂ) • 1)
      ((-(σ : ℂ)) • (J† ∘L D)) hLocalPublic T
  have hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖G v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2 := by
    intro p v
    have h := chronological_full_energy (localPrivateBlock D J κ) ((σ : ℂ) • J)
      ((c : ℂ) • 1) ((-(σ : ℂ)) • (J† ∘L D))
      (LocalRotation.local_step_energy D J c κ σ hκc hσc hD hJ) T p v
    change ‖A p + B v‖ ^ 2 + ‖C p + G v‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2 at h
    simpa only [add_comm (G v) (C p)] using h
  have hExit : B = (U ^ T) ∘L ((stackedResponse Γ U T)† ∘L (1 - G)) :=
    GlobalExit.clock_exit_block_eq D R1 J Γ H U w hw hwQuarter hD hJ hRight hLeft
      hBoundary hSelf hH hLocalPrivate hLocalPublic T
  have hf := SharpGlobalFilter.global_filter_precision D R1 J H c κ σ w Q b qbar T
    hQ hw hκ hκUpper hκc hσc hσw hD hJ hRight hLeft hR1 hBoundary hSelf hH
    hEndpoint hbq hqQ δ hδ hδOne
  have hNorm : ‖U ^ T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    simp only [hUNorm, one_mul, le_refl]
  have hResidual : ‖smoothedTransducerResidual (U ^ T) (stackedResponse Γ U T)
      (averagedGeometricFilter G (SharpFilterSchedule.length Q) ^ SharpFilterSchedule.depth Q W δ)
      G (SharpFilterSchedule.degree Q W δ)‖ ≤ δ := by
    apply smoothedTransducerResidual_norm_le_filter (W := 3 * W)
      (U ^ T) (stackedResponse Γ U T) _ G hNorm
      (globalPrivateBlock_norm_le_one D J c κ σ T hκc hσc hD hJ) hCost
      (SharpFilterSchedule.degree_pos Q W δ hQ) _ hf.1
    have hdegree := hf.2.1
    dsimp only [W]
    nlinarith
  have hL : 1 ≤ SharpFilterSchedule.length Q := by
    apply Nat.one_le_ceil_iff.mpr
    linarith
  have hd : 0 < SharpFilterSchedule.depth Q W δ * (SharpFilterSchedule.length Q - 1) :=
    SharpFilterSchedule.degree_pos Q W δ hQ
  refine ⟨Γ, U, R, hRRight, hRLeft, hCayley, hPowUnitary.1, hPowUnitary.2,
    hCost, ?_, ?_, hf.2.2⟩
  · exact AmplifiedSmoothing.implementation_isometry (SharpFilterSchedule.length Q)
      (SharpFilterSchedule.depth Q W δ) hL hd A B C G hStep
  · exact AmplifiedSmoothing.implementation_error (SharpFilterSchedule.length Q)
      (SharpFilterSchedule.depth Q W δ) hL hd A (U ^ T) B C (stackedResponse Γ U T) G
      hStep hPublic hPrivate hExit hPowUnitary.1 hPowUnitary.2 δ hδ.le hδOne hResidual

/-- The complete circuit uses equal error budgets for the filter residual and
Cayley subdivision; reflection amplification consumes twice the first budget. -/
def evolutionImplementation (D : V →L[ℂ] V) (J : P →L[ℂ] V)
    (τ Q qbar ε : ℝ) :=
  implementation D J (TimeSchedule.stepSize τ (ε / 3)) Q qbar
    (TimeSchedule.steps τ (ε / 3)) (ε / 3)

/-- The corresponding clean output preparation for continuous-time evolution. -/
def evolutionOutput (τ Q qbar ε : ℝ) :=
  output (P := P) (V := V) (TimeSchedule.stepSize τ (ε / 3)) Q qbar
    (TimeSchedule.steps τ (ε / 3)) (ε / 3)

set_option maxRecDepth 4096 in
/-- The clean output preparation for continuous-time evolution is an isometry. -/
theorem evolutionOutput_isometry (τ Q qbar ε : ℝ) (hQ : 1 ≤ Q) :
    (evolutionOutput (P := P) (V := V) τ Q qbar ε)† ∘L
      evolutionOutput τ Q qbar ε = 1 :=
  output_isometry _ _ _ _ _ hQ

set_option maxRecDepth 4096 in
/-- From clock promises to an actual implemented approximation of the
Hamiltonian exponential, including all output registers. The explicit degree
retains only logarithmic dependence on the requested precision, despite the
precision-dependent Cayley subdivision count. -/
theorem evolution_error
    (D R1 : V →L[ℂ] V) (J : P →L[ℂ] V) (H : P →L[ℂ] P)
    (τ Q b qbar ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hε : 0 < ε) (hεOne : ε ≤ 1) :
    (evolutionImplementation D J τ Q qbar ε)† ∘L
      evolutionImplementation D J τ Q qbar ε = 1 ∧
    ‖evolutionImplementation D J τ Q qbar ε -
      evolutionOutput (P := P) (V := V) τ Q qbar ε ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ ε ∧
    (SharpFilterSchedule.degree Q (τ * qbar) (ε / 3) : ℝ) ≤
      128 * (τ * qbar + Q * (1 + Real.log (1 / (ε / 3)))) := by
  let δ := ε / 3
  let T := TimeSchedule.steps τ δ
  let w := TimeSchedule.stepSize τ δ
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδOne : δ ≤ 1 := by dsimp [δ]; linarith
  have hw : 0 ≤ w := TimeSchedule.stepSize_nonneg τ δ hτ
  have hwQuarter : w ≤ 1 / 4 := TimeSchedule.stepSize_le_quarter τ δ
  have hBudget : (T : ℝ) * w * qbar = τ * qbar := TimeSchedule.weighted_budget_eq τ δ qbar
  obtain ⟨Γ, U, R, hRRight, _hRLeft, hCayley, _hUIso, _hUCoiso,
      _hCost, hIsometry, hImplementation, hDegree⟩ :=
    exists_precise_implementation D R1 J H w Q b qbar T hQ hw hwQuarter
      hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ δ hδ hδOne
  have hTime : (T : ℝ) * w = τ := by
    simpa only [mul_one] using TimeSchedule.weighted_budget_eq τ δ 1
  have hTimeC : (T : ℂ) * (w : ℂ) = (τ : ℂ) := by exact_mod_cast hTime
  have hScalar : -Complex.I * (T : ℂ) * (w : ℂ) = -Complex.I * (τ : ℂ) := by
    rw [mul_assoc, hTimeC]
  have hTarget : ‖U ^ T - NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ δ := by
    have h := CayleyApproximation.hamiltonian_cayley_error H R w hw (by linarith)
      hSelf hH hRRight T
    change ‖(CayleyTransfer.cayleyNumerator w H ∘L R) ^ T -
      NormedSpace.exp ((-Complex.I * (T : ℂ) * (w : ℂ)) • H)‖ ≤ (T : ℝ) * w ^ 3 at h
    rw [← hCayley, hScalar] at h
    exact h.trans (TimeSchedule.accumulated_cubic_le τ δ hτ hδ)
  have hL : 1 ≤ SharpFilterSchedule.length Q := by
    apply Nat.one_le_ceil_iff.mpr
    linarith
  have hd : 0 < SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ *
      (SharpFilterSchedule.length Q - 1) := SharpFilterSchedule.degree_pos Q _ δ hQ
  have hFull : ‖implementation D J w Q qbar T δ -
      output (P := P) (V := V) w Q qbar T δ ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤
      2 * δ + δ := by
    exact AmplifiedSmoothing.implementation_error_to_target (SharpFilterSchedule.length Q)
      (SharpFilterSchedule.depth Q ((T : ℝ) * w * qbar) δ) hL hd
      (((CayleyTransfer.c w : ℂ) • (1 : P →L[ℂ] P)) ^ T) (U ^ T)
      (NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H))
      (publicExit ((CayleyTransfer.c w : ℂ) • 1)
        ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D)) T)
      (stackedResponse ((CayleyTransfer.sigma w : ℂ) • J)
        ((CayleyTransfer.c w : ℂ) • 1) T)
      (globalPrivateBlock D J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
        (CayleyTransfer.sigma w) T) (2 * δ) δ hImplementation hTarget
  refine ⟨hIsometry, ?_, ?_⟩
  · change ‖implementation D J w Q qbar T δ -
      output (P := P) (V := V) w Q qbar T δ ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ ε
    exact hFull.trans (by dsimp [δ]; linarith)
  · simpa only [hBudget] using hDegree

end

end SparseHamiltonian.SharpClockSimulation
