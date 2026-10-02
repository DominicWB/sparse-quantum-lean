import SparseHamiltonian.SharpFilterSchedule

namespace SparseHamiltonian.SharpGlobalFilter

noncomputable section
open ContinuousLinearMap
open GlobalResolvent
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The sharper scalar schedule controls the actual chronological private
block, using the existing operator-norm resolvent proof without modification. -/
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
    ‖averagedGeometricFilter (globalPrivateBlock D J c κ σ T)
      (SharpFilterSchedule.length Q) ^ SharpFilterSchedule.depth Q W δ‖ ≤ δ ∧
    6 * W ≤ (SharpFilterSchedule.degree Q W δ : ℝ) ∧
    (SharpFilterSchedule.degree Q W δ : ℝ) ≤
      128 * (W + Q * (1 + Real.log (1 / δ))) := by
  let W := (T : ℝ) * w * qbar
  have hq : 0 ≤ qbar := by nlinarith [sq_nonneg b]
  have hW : 0 ≤ W := mul_nonneg (mul_nonneg (Nat.cast_nonneg T) hw) hq
  have hf := GlobalFilter.global_filter_norm_le D R1 J H c κ σ w Q b qbar T
    (by linarith) hw hκ hκUpper hκc hσc hσw hD hJ hRight hLeft hR1 hBoundary
    hSelf hH hEndpoint hbq hqQ (SharpFilterSchedule.length Q)
    (SharpFilterSchedule.depth Q W δ) (SharpFilterSchedule.length_ge Q)
    (SharpFilterSchedule.depth_pos Q W δ)
  refine ⟨hf.trans (SharpFilterSchedule.quarter_decay_le Q W δ hQ hW hδ),
    SharpFilterSchedule.degree_ge_six Q W δ hQ hW hδ hδOne, ?_⟩
  exact SharpFilterSchedule.degree_le Q W δ hQ hW hδ hδOne

end
end SparseHamiltonian.SharpGlobalFilter
