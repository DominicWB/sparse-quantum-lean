import SparseHamiltonian.FilterSchedule

/-!
# Exponential operator filters for chronological clock transducers

The global resolvent and conservation of energy supply all analytic hypotheses
of the Cauchy inverse-power argument. No contour estimate or filter norm bound
is left as an assumption. Sparse-oracle implementations remain a separate task.
-/

namespace SparseHamiltonian.GlobalFilter

noncomputable section
open ContinuousLinearMap
open GlobalResolvent
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Exponential filter decay for the actual finite chronological private block. -/
theorem global_filter_norm_le
    (D R1 : V →L[ℂ] V) (J : P →L[ℂ] V) (H : P →L[ℂ] P)
    (c κ σ w Q b qbar : ℝ) (T : ℕ)
    (hQ : 0 < Q) (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hκUpper : κ ≤ 2 / 9)
    (hκc : κ = 1 - c) (hσc : σ ^ 2 = 1 - c ^ 2) (hσw : σ ^ 2 ≤ 2 * w)
    (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (L k : ℕ) (hL : 32 * Q ≤ (L : ℝ)) (hk : 1 ≤ k) :
    ‖averagedGeometricFilter (globalPrivateBlock D J c κ σ T) L ^ k‖ ≤
      FilterSchedule.prefactor Q ((T : ℝ) * w * qbar) * (1 / 4 : ℝ) ^ k := by
  have hContract := globalPrivateBlock_norm_le_one D J c κ σ T hκc hσc hD hJ
  have hdisk (z : ℂ) (hz : ‖z - 1‖ ≤ 1 / (4 * Q)) :=
    exists_global_resolvent D R1 J H c κ σ w Q b qbar T z hQ hw hκ hκUpper
      hκc hσc hσw hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ hz
  have hdecay := FilterDecay.filter_norm_le_clock_scale
    (globalPrivateBlock D J c κ σ T) L k Q
    (3 * (Q + (T : ℝ) * w * qbar) * Real.exp (3 * ((T : ℝ) * w * qbar) / (4 * Q)))
    hQ hL hk hContract hdisk
  convert hdecay using 1
  unfold FilterSchedule.prefactor
  ring

/-- A concrete filter achieves the requested error with degree linear in the
weighted clock budget and logarithmic in precision. The lower degree bound
also covers the conservative threefold catalyst budget. -/
theorem global_filter_precision
    (D R1 : V →L[ℂ] V) (J : P →L[ℂ] V) (H : P →L[ℂ] P)
    (c κ σ w Q b qbar : ℝ) (T : ℕ)
    (hQ : 1 ≤ Q) (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hκUpper : κ ≤ 2 / 9)
    (hκc : κ = 1 - c) (hσc : σ ^ 2 = 1 - c ^ 2) (hσw : σ ^ 2 ≤ 2 * w)
    (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (δ : ℝ) (hδ : 0 < δ) (hδOne : δ ≤ 1) :
    let W := (T : ℝ) * w * qbar
    ‖averagedGeometricFilter (globalPrivateBlock D J c κ σ T) (FilterSchedule.length Q) ^
      FilterSchedule.depth Q W δ‖ ≤ δ ∧
    6 * W ≤ (FilterSchedule.degree Q W δ : ℝ) ∧
    (FilterSchedule.degree Q W δ : ℝ) ≤
      64 * (W + Q * (1 + Real.log ((Q + W + 2) / δ))) := by
  let W := (T : ℝ) * w * qbar
  have hq : 0 ≤ qbar := by nlinarith [sq_nonneg b]
  have hW : 0 ≤ W := mul_nonneg (mul_nonneg (Nat.cast_nonneg T) hw) hq
  have hf := global_filter_norm_le D R1 J H c κ σ w Q b qbar T (by linarith)
    hw hκ hκUpper hκc hσc hσw hD hJ hRight hLeft hR1 hBoundary hSelf hH
    hEndpoint hbq hqQ (FilterSchedule.length Q) (FilterSchedule.depth Q W δ)
    (FilterSchedule.length_ge Q) (FilterSchedule.depth_pos Q W δ)
  refine ⟨hf.trans (FilterSchedule.quarter_decay_le Q W δ hQ hW hδ),
    FilterSchedule.degree_ge_six Q W δ hQ hW hδ hδOne, ?_⟩
  exact FilterSchedule.degree_le Q W δ hQ hW hδ hδOne

end
end SparseHamiltonian.GlobalFilter
