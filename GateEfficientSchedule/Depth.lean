import SparseHamiltonian.SharpClockSimulation

/-!
# The clock simulation for every admissible filter depth

The released clock simulation (`SharpClockSimulation.exists_precise_implementation`) fixes the
filter depth `k_Lean = 1 + ⌈4W/Q + 2 log(1/δ)⌉` (`SharpFilterSchedule.depth`). Its proof uses
the depth only through three facts: `k ≥ 1`, the filter decay `prefactor(Q, W) (1/4)^k ≤ δ`
(with the depth-independent resolvent bound `GlobalFilter.global_filter_norm_le`), and the
smoothing slack `6W ≤ k (L - 1)` for the filter length `L = ⌈32Q⌉`. A natural number with these
properties is an **admissible depth** (`Admissible Q W δ k`), and the clock simulation holds for
every admissible depth (`exists_precise_implementation_k`), with the same full-output error
`2δ` and the explicit degree `d = k (L - 1)`.

* `sharp_admissible`: the released depth is admissible, so the released theorem is one
  instance.
* `exists_precise_implementation_k`: the actual amplified implementation with any admissible
  depth is an isometry within `2δ` of the clean output preparation applied to the Cayley power.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSchedule

noncomputable section

open ContinuousLinearMap
open GlobalResolvent ChronologicalResolvent ChronologicalCatalyst GlobalColligation
open scoped InnerProduct

/-- **An admissible filter depth** for the resolvent scale `Q`, the clock budget `W` and the
filter accuracy `δ`: `k ≥ 1`, the decay `prefactor(Q, W) (1/4)^k ≤ δ`, and the smoothing slack
`6W ≤ k (⌈32Q⌉ - 1)`. -/
structure Admissible (Q W δ : ℝ) (k : ℕ) : Prop where
  pos : 1 ≤ k
  decay : FilterSchedule.prefactor Q W * (1 / 4 : ℝ) ^ k ≤ δ
  slack : 6 * W ≤ (k : ℝ) * ((SharpFilterSchedule.length Q - 1 : ℕ) : ℝ)

/-- **The released depth is admissible.** -/
theorem sharp_admissible (Q W δ : ℝ) (hQ : 1 ≤ Q) (hW : 0 ≤ W) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Admissible Q W δ (SharpFilterSchedule.depth Q W δ) where
  pos := SharpFilterSchedule.depth_pos Q W δ
  decay := SharpFilterSchedule.quarter_decay_le Q W δ hQ hW hδ
  slack := by
    have h := SharpFilterSchedule.degree_ge_six Q W δ hQ hW hδ hδ1
    simpa only [SharpFilterSchedule.degree, Nat.cast_mul] using h

/-- The filter degree `k (L - 1)` of an admissible depth is positive. -/
theorem degree_pos_of_admissible {Q W δ : ℝ} {k : ℕ} (hQ : 1 ≤ Q) (hk : Admissible Q W δ k) :
    0 < k * (SharpFilterSchedule.length Q - 1) := by
  have hL : (1 : ℝ) ≤ ((SharpFilterSchedule.length Q - 1 : ℕ) : ℝ) :=
    hQ.trans (SharpFilterSchedule.length_sub_one_bounds Q hQ).1
  have hLnat : 1 ≤ SharpFilterSchedule.length Q - 1 := by exact_mod_cast hL
  exact Nat.mul_pos hk.pos hLnat

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The amplified implementation of the full chronological clock transducer with the filter
depth `k`. -/
def implementationK (D : V →L[ℂ] V) (J : P →L[ℂ] V) (w Q : ℝ) (T k : ℕ) :=
  AmplifiedSmoothing.implementation (SharpFilterSchedule.length Q) k
    (((CayleyTransfer.c w : ℂ) • (1 : P →L[ℂ] P)) ^ T)
    (publicExit ((CayleyTransfer.c w : ℂ) • 1)
      ((-(CayleyTransfer.sigma w : ℂ)) • (J† ∘L D)) T)
    (stackedResponse ((CayleyTransfer.sigma w : ℂ) • J)
      ((CayleyTransfer.c w : ℂ) • 1) T)
    (globalPrivateBlock D J (CayleyTransfer.c w) (CayleyTransfer.kappa w)
      (CayleyTransfer.sigma w) T)

/-- The clean output preparation with the filter depth `k`. -/
def outputK (Q : ℝ) (T k : ℕ) :
    P →L[ℂ] PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := BlockOperator.H T V)
      (k * (SharpFilterSchedule.length Q - 1))) :=
  SmoothingLCU.output (P := P) (V := BlockOperator.H T V)
    (AveragingPolynomial.filter (SharpFilterSchedule.length Q) k).coeff
    (k * (SharpFilterSchedule.length Q - 1))

set_option maxRecDepth 4096 in
/-- **The clock simulation with an admissible filter depth**: a clock certificate yields the
Cayley transform `U` (its denominator inverse `R`), the unitary `U^T`, and the actual amplified
implementation with depth `k`, an isometry within `2δ` of the clean output preparation applied
to `U^T` (complete output, every private and branch register included). -/
theorem exists_precise_implementation_k
    (D R1 : V →L[ℂ] V) (J : P →L[ℂ] V) (H : P →L[ℂ] P)
    (w Q b qbar : ℝ) (T : ℕ)
    (hQ : 1 ≤ Q) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (δ : ℝ) (hδ : 0 < δ) (hδOne : δ ≤ 1) (k : ℕ)
    (hk : Admissible Q ((T : ℝ) * w * qbar) δ k) :
    ∃ U R : P →L[ℂ] P,
      CayleyTransfer.cayleyDenominator w H ∘L R = 1 ∧
      R ∘L CayleyTransfer.cayleyDenominator w H = 1 ∧
      U = CayleyTransfer.cayleyNumerator w H ∘L R ∧
      (U ^ T)† ∘L (U ^ T) = 1 ∧ (U ^ T) ∘L (U ^ T)† = 1 ∧
      (implementationK D J w Q T k)† ∘L implementationK D J w Q T k = 1 ∧
      ‖implementationK D J w Q T k - outputK (P := P) (V := V) Q T k ∘L (U ^ T)‖ ≤ 2 * δ := by
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
  have hfilter := GlobalFilter.global_filter_norm_le D R1 J H c κ σ w Q b qbar T
    (by linarith) hw hκ hκUpper hκc hσc hσw hD hJ hRight hLeft hR1 hBoundary hSelf hH
    hEndpoint hbq hqQ (SharpFilterSchedule.length Q) k (SharpFilterSchedule.length_ge Q) hk.pos
  have hNorm : ‖U ^ T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    simp only [hUNorm, one_mul, le_refl]
  have hd := degree_pos_of_admissible hQ hk
  have hResidual : ‖smoothedTransducerResidual (U ^ T) (stackedResponse Γ U T)
      (averagedGeometricFilter G (SharpFilterSchedule.length Q) ^ k)
      G (k * (SharpFilterSchedule.length Q - 1))‖ ≤ δ := by
    apply smoothedTransducerResidual_norm_le_filter (W := 3 * W)
      (U ^ T) (stackedResponse Γ U T) _ G hNorm
      (globalPrivateBlock_norm_le_one D J c κ σ T hκc hσc hD hJ) hCost hd _
      (hfilter.trans hk.decay)
    have hslack := hk.slack
    have e : ((k * (SharpFilterSchedule.length Q - 1) : ℕ) : ℝ) =
        (k : ℝ) * ((SharpFilterSchedule.length Q - 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e]
    dsimp only [W]
    linarith
  have hL : 1 ≤ SharpFilterSchedule.length Q := by
    apply Nat.one_le_ceil_iff.mpr
    linarith
  refine ⟨U, R, hRRight, hRLeft, hCayley, hPowUnitary.1, hPowUnitary.2, ?_, ?_⟩
  · exact AmplifiedSmoothing.implementation_isometry (SharpFilterSchedule.length Q) k hL hd
      A B C G hStep
  · exact AmplifiedSmoothing.implementation_error (SharpFilterSchedule.length Q) k hL hd A
      (U ^ T) B C (stackedResponse Γ U T) G hStep hPublic hPrivate hExit hPowUnitary.1
      hPowUnitary.2 δ hδ.le hδOne hResidual

end

end SparseHamiltonian.GateSchedule
