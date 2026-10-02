import SparseHamiltonian.ClockCayley

/-!
# Precision of the smoothed residual for a constructed catalyst

The catalyst and public map are constructed from clock data. Their weighted
cost and the actual operator filter bound imply the smoothing residual error.
This is an operator statement; the LCU/reuse circuit implementation is separate.
-/

namespace SparseHamiltonian.GlobalResidual

noncomputable section
open ContinuousLinearMap
open GlobalResolvent ChronologicalCatalyst
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- A constructed stationary catalyst has a smoothed residual at most δ with
an explicit degree linear in its weighted cost and logarithmic in precision. -/
theorem exists_precise_smoothed_catalyst
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
    let F := averagedGeometricFilter (globalPrivateBlock D J c κ σ T) (FilterSchedule.length Q) ^
      FilterSchedule.depth Q W δ
    let d := FilterSchedule.degree Q W δ
    ∃ (Γ : P →L[ℂ] V) (U : P →L[ℂ] P),
      (∀ p, ‖(U ^ T) p‖ = ‖p‖) ∧
      stackedResponse ((σ : ℂ) • J) ((c : ℂ) • 1) T +
        globalPrivateBlock D J c κ σ T ∘L stackedResponse Γ U T = stackedResponse Γ U T ∧
      ‖stackedResponse Γ U T‖ ^ 2 ≤ 3 * W ∧
      ‖smoothedTransducerResidual (U ^ T) (stackedResponse Γ U T)
        F (globalPrivateBlock D J c κ σ T) d‖ ≤ δ ∧
      (d : ℝ) ≤ 64 * (W + Q * (1 + Real.log ((Q + W + 2) / δ))) := by
  let W := (T : ℝ) * w * qbar
  obtain ⟨Γ, U, _hLocalPrivate, _hLocalPublic, hU, hPrivate, _hPublic, hCost⟩ :=
    exists_global_catalyst D R1 J H c κ σ w Q b qbar (by linarith) hw hκ hκUpper
      hκc hσc hσw hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ T
  have hf := GlobalFilter.global_filter_precision D R1 J H c κ σ w Q b qbar T
    hQ hw hκ hκUpper hκc hσc hσw hD hJ hRight hLeft hR1 hBoundary hSelf hH
    hEndpoint hbq hqQ δ hδ hδOne
  have hNorm : ‖U ^ T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro p
    simp only [hU, one_mul, le_refl]
  refine ⟨Γ, U, hU, hPrivate, hCost, ?_, hf.2.2⟩
  apply smoothedTransducerResidual_norm_le_filter (W := 3 * W)
    (U ^ T) (stackedResponse Γ U T) _ (globalPrivateBlock D J c κ σ T)
    hNorm (globalPrivateBlock_norm_le_one D J c κ σ T hκc hσc hD hJ) hCost
    (FilterSchedule.degree_pos Q W δ hQ) _ hf.1
  have hdegree := hf.2.1
  dsimp only [W]
  nlinarith

end
end SparseHamiltonian.GlobalResidual
