import GateEfficientSchedule.Depth
import TimeDependentHamiltonian.Chronology.Simulation

/-!
# The slot-dependent clock simulation for every admissible filter depth

The released slot-dependent clock simulation (`TimeDependent.exists_precise_implementationV`)
fixes the filter depth `SharpFilterSchedule.depth`. As for the time-independent clock
(`exists_precise_implementation_k`), its proof uses the depth only through `k ≥ 1`, the filter
decay `prefactor(Q, W) (1/4)^k ≤ δ` (with the depth-independent resolvent disk of the
slot-dependent private block) and the smoothing slack `6W ≤ k (⌈32Q⌉ - 1)`.

* `filter_precisionV_k`: the averaged geometric filter of depth `k` of the slot-dependent private
  block has norm at most `δ` for every admissible `k`;
* `exists_precise_implementationV_k`: the actual amplified implementation of the slot-dependent
  clock with any admissible depth is an isometry within `2δ` of the clean output preparation
  applied to the ordered product of the local Cayley steps.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSchedule

noncomputable section

open ContinuousLinearMap OracleCircuit
open SparseHamiltonian.ChronologicalResolvent SparseHamiltonian.ChronologicalCatalyst
open SparseHamiltonian.GlobalColligation SparseHamiltonian.GlobalResolvent
open SparseHamiltonian.TimeDependent
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The amplified implementation of the slot-dependent chronological clock with the filter depth
`k`, including every private and branch register. -/
def implementationVK (D : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V) (w Q : ℝ) (T k : ℕ) :=
  AmplifiedSmoothing.implementation (SharpFilterSchedule.length Q) k
    (((CayleyTransfer.c w : ℂ) • (1 : P →L[ℂ] P)) ^ T)
    (exitV D J (CayleyTransfer.c w) (CayleyTransfer.sigma w) T)
    (stackedResponse ((CayleyTransfer.sigma w : ℂ) • J) ((CayleyTransfer.c w : ℂ) • 1) T)
    (privateV D J (CayleyTransfer.c w) (CayleyTransfer.kappa w) (CayleyTransfer.sigma w) T)

/-- **The filter of an admissible depth** for the slot-dependent private block. -/
theorem filter_precisionV_k
    (D R1 : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V) (H : ℕ → P →L[ℂ] P)
    (c κ σ w Q b qbar : ℝ) (T : ℕ)
    (hQ : 1 ≤ Q) (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hκUpper : κ ≤ 2 / 9)
    (hκc : κ = 1 - c) (hσc : σ ^ 2 = 1 - c ^ 2) (hσw : σ ^ 2 ≤ 2 * w)
    (hD : ∀ k, (D k)† ∘L D k = 1) (hJ : J† ∘L J = 1)
    (hRight : ∀ k, (1 - D k) ∘L R1 k = 1) (hLeft : ∀ k, R1 k ∘L (1 - D k) = 1)
    (hR1 : ∀ k, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k, J† ∘L R1 k ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H k))
    (hSelf : ∀ k, star (H k) = H k) (hH : ∀ k, ‖H k‖ ≤ 1)
    (hEndpoint : ∀ k, ‖R1 k ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (δ : ℝ) (k : ℕ) (hk : Admissible Q ((T : ℝ) * w * qbar) δ k) :
    ‖averagedGeometricFilter (privateV D J c κ σ T) (SharpFilterSchedule.length Q) ^ k‖ ≤ δ := by
  have hQpos : 0 < Q := by linarith
  have hContract := privateV_norm_le_one D J hJ hD c κ σ hκc hσc T
  have hdisk (z : ℂ) (hz : ‖z - 1‖ ≤ 1 / (4 * Q)) :=
    exists_privateV_resolvent D R1 J H c κ σ w Q b qbar T z hQpos hw hκ hκUpper
      hκc hσc hσw hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ hz
  have hdecay := FilterDecay.filter_norm_le_clock_scale
    (privateV D J c κ σ T) (SharpFilterSchedule.length Q) k Q
    (3 * (Q + (T : ℝ) * w * qbar) * Real.exp (3 * ((T : ℝ) * w * qbar) / (4 * Q)))
    hQpos (SharpFilterSchedule.length_ge Q) hk.pos hContract hdisk
  refine hdecay.trans (le_of_eq_of_le ?_ hk.decay)
  unfold FilterSchedule.prefactor
  ring

set_option maxRecDepth 4096 in
/-- **The slot-dependent clock simulation with an admissible filter depth**: clock promises at
every sampled time give the Cayley steps `U k` (with the denominator inverses `R k`) and the
actual amplified implementation with depth `k`, an isometry within `2δ` of the clean output
preparation applied to the ordered product `U (T-1) ⋯ U 0`. -/
theorem exists_precise_implementationV_k
    (D R1 : ℕ → V →L[ℂ] V) (J : P →L[ℂ] V) (H : ℕ → P →L[ℂ] P)
    (w Q b qbar : ℝ) (T : ℕ)
    (hQ : 1 ≤ Q) (hw : 0 ≤ w) (hwQuarter : w ≤ 1 / 4)
    (hD : ∀ k, (D k)† ∘L D k = 1) (hJ : J† ∘L J = 1)
    (hRight : ∀ k, (1 - D k) ∘L R1 k = 1) (hLeft : ∀ k, R1 k ∘L (1 - D k) = 1)
    (hR1 : ∀ k, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k, J† ∘L R1 k ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H k))
    (hSelf : ∀ k, star (H k) = H k) (hH : ∀ k, ‖H k‖ ≤ 1)
    (hEndpoint : ∀ k, ‖R1 k ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (δ : ℝ) (hδ : 0 < δ) (hδOne : δ ≤ 1) (k : ℕ)
    (hk : Admissible Q ((T : ℝ) * w * qbar) δ k) :
    ∃ (U R : ℕ → P →L[ℂ] P),
      (∀ j, CayleyTransfer.cayleyDenominator w (H j) ∘L R j = 1) ∧
      (∀ j, R j ∘L CayleyTransfer.cayleyDenominator w (H j) = 1) ∧
      (∀ j, U j = CayleyTransfer.cayleyNumerator w (H j) ∘L R j) ∧
      (implementationVK D J w Q T k)† ∘L implementationVK D J w Q T k = 1 ∧
      ‖implementationVK D J w Q T k -
        outputK (P := P) (V := V) Q T k ∘L evolution U T‖ ≤ 2 * δ := by
  let c := CayleyTransfer.c w
  let κ := CayleyTransfer.kappa w
  let σ := CayleyTransfer.sigma w
  have hQpos : 0 < Q := by linarith
  obtain ⟨hκ, hκUpper, hκc, hσc, hσw⟩ := CayleyTransfer.scalar_promises w hw hwQuarter
  have hcat := fun j => exists_local_catalyst (D j) (R1 j) J (H j) c κ σ w Q b qbar
    hQpos hw hκ hκUpper hκc hσc hσw (hD j) hJ (hRight j) (hLeft j) (hR1 j) (hBoundary j)
    (hSelf j) (hH j) (hEndpoint j) hbq hqQ
  choose Γ U hLocalPrivate hLocalPublic hUNorm hΓ using hcat
  have hcay := fun j => local_public_is_cayley (D j) (R1 j) J (Γ j) (H j) (U j) w hw
    hwQuarter (hRight j) (hLeft j) hJ (hBoundary j) (hSelf j) (hH j) (hLocalPrivate j)
    (hLocalPublic j)
  choose R hRRight hRLeft hCayley using hcay
  have hUnit := fun j => local_public_unitary (D j) (R1 j) J (Γ j) (H j) (U j) w hw
    hwQuarter (hRight j) (hLeft j) hJ (hBoundary j) (hSelf j) (hH j) (hLocalPrivate j)
    (hLocalPublic j)
  have hEvol := evolution_unitary U (fun j => (hUnit j).1) (fun j => (hUnit j).2) T
  have hPublic := colligation_public D J c σ Γ U hLocalPublic T
  have hPrivate := colligation_private D J c κ σ Γ U hLocalPrivate hLocalPublic T
  have hStep := step_energy D J hJ hD w hw hwQuarter T
  have hExit := exitV_identity D J hJ hD c κ σ hκc hσc Γ U hLocalPrivate hLocalPublic T
    hEvol.2
  have hf := filter_precisionV_k D R1 J H c κ σ w Q b qbar T hQ hw hκ hκUpper hκc hσc hσw
    hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ δ k hk
  have hb : 0 ≤ b := (norm_nonneg _).trans (hEndpoint 0)
  have hq : 0 ≤ qbar := by nlinarith [sq_nonneg b]
  have hW : 0 ≤ (T : ℝ) * w * qbar := by positivity
  have hNorm : ‖evolution U T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    rw [evolution_norm U hUNorm, one_mul]
  have hCost : ‖stackedV Γ U T‖ ^ 2 ≤ 3 * ((T : ℝ) * w * qbar) := by
    have h := stackedV_norm_sq_le Γ U hUNorm ((144 / 49 : ℝ) * w * qbar) hΓ T
    have hle : (T : ℝ) * ((144 / 49 : ℝ) * w * qbar) ≤ 3 * ((T : ℝ) * w * qbar) := by
      nlinarith
    linarith
  have hContract := privateV_norm_le_one D J hJ hD c κ σ hκc hσc T
  have hd := degree_pos_of_admissible hQ hk
  have hResidual : ‖smoothedTransducerResidual (evolution U T) (stackedV Γ U T)
      (averagedGeometricFilter (privateV D J c κ σ T) (SharpFilterSchedule.length Q) ^ k)
      (privateV D J c κ σ T) (k * (SharpFilterSchedule.length Q - 1))‖ ≤ δ := by
    apply smoothedTransducerResidual_norm_le_filter (W := 3 * ((T : ℝ) * w * qbar))
      (evolution U T) (stackedV Γ U T) _ (privateV D J c κ σ T) hNorm hContract hCost hd _ hf
    have hslack := hk.slack
    have e : ((k * (SharpFilterSchedule.length Q - 1) : ℕ) : ℝ) =
        (k : ℝ) * ((SharpFilterSchedule.length Q - 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e]
    linarith
  have hL : 1 ≤ SharpFilterSchedule.length Q := by
    apply Nat.one_le_ceil_iff.mpr
    linarith
  refine ⟨U, R, hRRight, hRLeft, hCayley, ?_, ?_⟩
  · exact AmplifiedSmoothing.implementation_isometry (SharpFilterSchedule.length Q) k hL hd
      _ _ _ _ hStep
  · exact AmplifiedSmoothing.implementation_error (SharpFilterSchedule.length Q) k hL hd _
      (evolution U T) _ _ (stackedV Γ U T) _ hStep hPublic hPrivate hExit hEvol.1 hEvol.2 δ
      hδ.le hδOne hResidual

end

end SparseHamiltonian.GateSchedule
