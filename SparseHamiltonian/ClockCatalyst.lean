import SparseHamiltonian.ChronologicalCatalyst

/-!
# Clock promises construct a catalyst with weighted cost

The catalyst and its public isometry are conclusions. The norm estimate uses
the already established local endpoint bound; its harmless factor `144/49`
is slightly larger than the sharp Cayley constant in the manuscript.
-/

namespace SparseHamiltonian.GlobalResolvent

noncomputable section

open ContinuousLinearMap
open CatalystConstruction ChronologicalCatalyst
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Clock boundary promises construct the local transducer's stationary
catalyst and norm-preserving public action, with weighted catalyst cost. -/
theorem exists_local_catalyst
    (D R1 : V →L[ℂ] V) (J : P →L[ℂ] V) (H : P →L[ℂ] P)
    (c κ σ w Q b qbar : ℝ)
    (hQ : 0 < Q) (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hκUpper : κ ≤ 2 / 9)
    (hκc : κ = 1 - c) (hσc : σ ^ 2 = 1 - c ^ 2) (hσw : σ ^ 2 ≤ 2 * w)
    (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q) :
    ∃ (Γ : P →L[ℂ] V) (U : P →L[ℂ] P),
      (σ : ℂ) • J + localPrivateBlock D J κ ∘L Γ = Γ ∧
      (c : ℂ) • 1 + ((-(σ : ℂ)) • (J† ∘L D)) ∘L Γ = U ∧
      (∀ p, ‖U p‖ = ‖p‖) ∧
      ‖Γ‖ ^ 2 ≤ (144 / 49 : ℝ) * w * qbar := by
  have hz : ‖(1 : ℂ) - 1‖ ≤ 1 / (4 * Q) := by
    simp only [sub_self, norm_zero]
    positivity
  obtain ⟨S, hSRight, _hSLeft, _hSNorm, hSJ, _hES, _hTransfer⟩ :=
    exists_local_clock_certificate D R1 J H c κ σ w Q b qbar 1 hQ hw hκ hκUpper
      hκc hσc hσw hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ hz
  have hS : (1 - localPrivateBlock D J κ) ∘L S = 1 := by
    simpa only [one_smul] using hSRight
  refine ⟨catalyst S ((σ : ℂ) • J),
    publicAction ((c : ℂ) • 1) ((-(σ : ℂ)) • (J† ∘L D)) S ((σ : ℂ) • J),
    private_transduction (localPrivateBlock D J κ) S ((σ : ℂ) • J) hS,
    rfl, ?_, ?_⟩
  · exact publicAction_norm_map (localPrivateBlock D J κ) S ((σ : ℂ) • J)
      ((c : ℂ) • 1) ((-(σ : ℂ)) • (J† ∘L D)) hS
      (LocalRotation.local_step_energy D J c κ σ hκc hσc hD hJ)
  · exact catalyst_norm_sq_le S J σ w b qbar hw hσw hbq hSJ

/-- The actual chronological private block preserves the explicitly stacked
catalyst when supplied with its initial public input. -/
theorem global_catalyst_transduction (D : V →L[ℂ] V) (J : P →L[ℂ] V)
    (c κ σ : ℝ) (Γ : P →L[ℂ] V) (U : P →L[ℂ] P) (T : ℕ)
    (hPrivate : (σ : ℂ) • J + localPrivateBlock D J κ ∘L Γ = Γ)
    (hPublic : (c : ℂ) • 1 + ((-(σ : ℂ)) • (J† ∘L D)) ∘L Γ = U) :
    stackedResponse ((σ : ℂ) • J) ((c : ℂ) • 1) T +
      globalPrivateBlock D J c κ σ T ∘L stackedResponse Γ U T = stackedResponse Γ U T :=
  catalyst_private_transduction (localPrivateBlock D J κ) ((σ : ℂ) • J) Γ U
    ((c : ℂ) • 1) ((-(σ : ℂ)) • (J† ∘L D)) hPrivate hPublic T

omit [CompleteSpace P] [CompleteSpace V] in
/-- The constructed catalyst's chronological cost grows linearly with the
number of time slots and the weighted local query cost. -/
theorem global_catalyst_cost (Γ : P →L[ℂ] V) (U : P →L[ℂ] P)
    (w qbar : ℝ) (T : ℕ) (hU : ∀ p, ‖U p‖ = ‖p‖)
    (hΓ : ‖Γ‖ ^ 2 ≤ (144 / 49 : ℝ) * w * qbar) :
    ‖stackedResponse Γ U T‖ ^ 2 ≤ (144 / 49 : ℝ) * ((T : ℝ) * w * qbar) := by
  have h := stackedResponse_norm_sq_le Γ U hU ((144 / 49 : ℝ) * w * qbar) hΓ T
  convert h using 1
  ring


/-- Full chronological catalyst certificate derived from clock promises.
The private catalyst, public action, and weighted cost are all constructed. -/
theorem exists_global_catalyst
    (D R1 : V →L[ℂ] V) (J : P →L[ℂ] V) (H : P →L[ℂ] P)
    (c κ σ w Q b qbar : ℝ)
    (hQ : 0 < Q) (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hκUpper : κ ≤ 2 / 9)
    (hκc : κ = 1 - c) (hσc : σ ^ 2 = 1 - c ^ 2) (hσw : σ ^ 2 ≤ 2 * w)
    (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q) (T : ℕ) :
    ∃ (Γ : P →L[ℂ] V) (U : P →L[ℂ] P),
      (σ : ℂ) • J + localPrivateBlock D J κ ∘L Γ = Γ ∧
      (c : ℂ) • 1 + ((-(σ : ℂ)) • (J† ∘L D)) ∘L Γ = U ∧
      (∀ p, ‖(U ^ T) p‖ = ‖p‖) ∧
      stackedResponse ((σ : ℂ) • J) ((c : ℂ) • 1) T +
        globalPrivateBlock D J c κ σ T ∘L stackedResponse Γ U T =
          stackedResponse Γ U T ∧
      (∀ p, publicState ((c : ℂ) • 1) ((-(σ : ℂ)) • (J† ∘L D))
        (fun k => Γ ((U ^ k) p)) p T = (U ^ T) p) ∧
      ‖stackedResponse Γ U T‖ ^ 2 ≤ 3 * ((T : ℝ) * w * qbar) := by
  obtain ⟨Γ, U, hPrivate, hPublic, hU, hΓ⟩ :=
    exists_local_catalyst D R1 J H c κ σ w Q b qbar hQ hw hκ hκUpper
      hκc hσc hσw hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ
  refine ⟨Γ, U, hPrivate, hPublic, public_pow_norm U hU T,
    global_catalyst_transduction D J c κ σ Γ U T hPrivate hPublic, ?_, ?_⟩
  · intro p
    exact catalyst_publicState Γ U ((c : ℂ) • 1) ((-(σ : ℂ)) • (J† ∘L D)) hPublic p T
  · have hq : 0 ≤ qbar := by nlinarith [sq_nonneg b]
    have hW : 0 ≤ (T : ℝ) * w * qbar := by positivity
    have h := global_catalyst_cost Γ U w qbar T hU hΓ
    nlinarith

end

end SparseHamiltonian.GlobalResolvent
