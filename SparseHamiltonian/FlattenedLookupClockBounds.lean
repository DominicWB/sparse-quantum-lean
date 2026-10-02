import SparseHamiltonian.WeightedProgramClockBounds

/-!
# Analytic bounds in the flattened ordinary-lookup clock layout

A fixed Hilbert-space regrouping transports the actual heterogeneous clock and
its resolvent. The public boundary is transported by the same isometry. Every
analytic promise is preserved, including the weighted average query budget,
the exact compressed Hamiltonian, and the endpoint norm. Public branch
encodings may embed a proper subspace of the lookup payload.
-/

namespace SparseHamiltonian.FlattenedLookupClockBounds

noncomputable section
open ContinuousLinearMap OracleCircuit MaskedLookupCurry HeterogeneousLookupClock
open scoped InnerProduct BigOperators

section Transport
variable {P V K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Operator norms are unchanged by a fixed unitary change of Hilbert space. -/
theorem conjugate_norm (e : V ≃ₗᵢ[ℂ] K) (R : V →L[ℂ] V) :
    ‖e.conjStarAlgEquiv R‖ = ‖R‖ := by
  apply le_antisymm
  · apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      e.norm_map, e.symm.norm_map] using R.le_opNorm (e.symm x)
  · apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    have h := (e.conjStarAlgEquiv R).le_opNorm (e x)
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      e.symm_apply_apply, e.norm_map] using h

/-- The public boundary is moved into the new private layout without changing inputs. -/
def transportBoundary (e : V ≃ₗᵢ[ℂ] K) (J : P →L[ℂ] V) : P →L[ℂ] K :=
  e.toLinearIsometry.toContinuousLinearMap ∘L J

/-- The transported public boundary remains isometric. -/
theorem transportBoundary_isometry (e : V ≃ₗᵢ[ℂ] K) (J : P →L[ℂ] V)
    (hJ : J† ∘L J = 1) :
    (transportBoundary e J)† ∘L transportBoundary e J = 1 := by
  rw [← ContinuousLinearMap.norm_map_iff_adjoint_comp_self] at hJ ⊢
  intro x
  change ‖e (J x)‖ = ‖x‖
  rw [e.norm_map, hJ]

/-- Transporting both the private operator and boundary leaves public compression exact. -/
theorem transportBoundary_compression (e : V ≃ₗᵢ[ℂ] K) (R : V →L[ℂ] V)
    (J : P →L[ℂ] V) :
    (transportBoundary e J)† ∘L e.conjStarAlgEquiv R ∘L transportBoundary e J =
      J† ∘L R ∘L J := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  simp only [comp_apply, adjoint_inner_right, transportBoundary,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  change inner ℂ (e (J y)) (e (R (e.symm (e (J x))))) = inner ℂ (J y) (R (J x))
  rw [e.symm_apply_apply, e.inner_map_map]

omit [CompleteSpace P] in
/-- The endpoint operator norm is preserved by the same fixed regrouping. -/
theorem transportBoundary_endpoint_norm (e : V ≃ₗᵢ[ℂ] K) (R : V →L[ℂ] V)
    (J : P →L[ℂ] V) :
    ‖e.conjStarAlgEquiv R ∘L transportBoundary e J‖ = ‖R ∘L J‖ := by
  have hPoint : ∀ x, ‖(e.conjStarAlgEquiv R ∘L transportBoundary e J) x‖ =
      ‖(R ∘L J) x‖ := by
    intro x
    change ‖e (R (e.symm (e (J x))))‖ = ‖R (J x)‖
    rw [e.symm_apply_apply, e.norm_map]
  apply le_antisymm
  · apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [hPoint]
    exact (R ∘L J).le_opNorm x
  · apply opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [← hPoint]
    exact (e.conjStarAlgEquiv R ∘L transportBoundary e J).le_opNorm x

/-- Both resolvent identities are preserved, independently of boundary properties. -/
theorem conjugate_inverse (e : V ≃ₗᵢ[ℂ] K) (D R : V →L[ℂ] V)
    (hRight : (1 - D) ∘L R = 1) (hLeft : R ∘L (1 - D) = 1) :
    (1 - e.conjStarAlgEquiv D) ∘L e.conjStarAlgEquiv R = 1 ∧
      e.conjStarAlgEquiv R ∘L (1 - e.conjStarAlgEquiv D) = 1 := by
  constructor
  · change (1 - e.conjStarAlgEquiv D) * e.conjStarAlgEquiv R = 1
    change (1 - D) * R = 1 at hRight
    simpa only [map_mul, map_sub, map_one] using congrArg e.conjStarAlgEquiv hRight
  · change e.conjStarAlgEquiv R * (1 - e.conjStarAlgEquiv D) = 1
    change R * (1 - D) = 1 at hLeft
    simpa only [map_mul, map_sub, map_one] using congrArg e.conjStarAlgEquiv hLeft

end Transport

variable {X I A Z : Type*} [Fintype I] [Fintype A] [Fintype Z] [AddCommGroup Z]
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The explicit heterogeneous inverse in the single clock-label layout. -/
def flatResolvent (f : X → A → Z) (p : I → Program (localSigned 1 f))
    (hInv : ∀ i x v, (p i).eval x ((p i).eval x v) = v) (x : X) :
    PiLp 2 (fun _ : Slot f p => Payload A Z) →L[ℂ]
      PiLp 2 (fun _ : Slot f p => Payload A Z) :=
  (flatten f p).conjStarAlgEquiv
    (WeightedProgramClockBounds.familyResolvent p (localSigned_unitary 1 f) hInv x)

/-- Fixed weighted preparation into flattened clock boundaries. -/
def flatBoundary (f : X → A → Z) (weights : I → ℝ) (p : I → Program (localSigned 1 f))
    (E : I → P →ₗᵢ[ℂ] Payload A Z) : P →L[ℂ] PiLp 2 (fun _ : Slot f p => Payload A Z) :=
  transportBoundary (flatten f p) (WeightedProgramClockBounds.boundary weights p E)

/-- All analytic simulation promises for the exact, flattened heterogeneous
lookup clocks. No inverse, norm, compression, or clock implementation is assumed. -/
theorem family_promises (f : X → A → Z) (weights : I → ℝ)
    (p : I → Program (localSigned 1 f))
    (hw : ∀ i, 0 ≤ weights i) (hsum : ∑ i, weights i = 1)
    (Q : ℝ) (hQ : 1 ≤ Q) (hqQ : ∀ i, (QueryClockStep.slots (p i) : ℝ) ≤ Q)
    (hInv : ∀ i x v, (p i).eval x ((p i).eval x v) = v)
    (E : I → P →ₗᵢ[ℂ] Payload A Z) :
    let D := flatFamilyClock f p hInv
    let R := flatResolvent f p hInv
    let J := flatBoundary f weights p E
    let H := WeightedProgramClockBounds.generator weights p E
    let qbar := WeightedProgramClockBounds.averageLength weights p
    let b := Real.sqrt (qbar / 2)
    (∀ x, (D x)† ∘L D x = 1) ∧ J† ∘L J = 1 ∧
      (∀ x, (1 - D x) ∘L R x = 1) ∧ (∀ x, R x ∘L (1 - D x) = 1) ∧
      (∀ x, ‖R x‖ ≤ Q) ∧
      (∀ x, J† ∘L R x ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H x)) ∧
      (∀ x, star (H x) = H x) ∧ (∀ x, ‖H x‖ ≤ 1) ∧
      (∀ x, ‖R x ∘L J‖ ≤ b) ∧ b ^ 2 ≤ qbar / 2 ∧ qbar ≤ Q := by
  obtain ⟨hD, hJ, hRight, hLeft, hNorm, hBoundary, hSelf, hH, hEnd, hSq, hAverage⟩ :=
    WeightedProgramClockBounds.family_promises weights p hw hsum Q hQ hqQ
      (localSigned_unitary 1 f) hInv E
  dsimp only
  refine ⟨?_, transportBoundary_isometry _ _ hJ, ?_, ?_, ?_, ?_, hSelf, hH, ?_, hSq, hAverage⟩
  · intro x
    exact ((familyClock_unitary f p hInv x).transport (flatten f p)).1
  · intro x
    exact (conjugate_inverse (flatten f p) _ _ (hRight x) (hLeft x)).1
  · intro x
    exact (conjugate_inverse (flatten f p) _ _ (hRight x) (hLeft x)).2
  · intro x
    rw [flatResolvent, conjugate_norm]
    exact hNorm x
  · intro x
    rw [flatResolvent, flatBoundary, transportBoundary_compression]
    exact hBoundary x
  · intro x
    rw [flatResolvent, flatBoundary, transportBoundary_endpoint_norm]
    exact hEnd x

end
end SparseHamiltonian.FlattenedLookupClockBounds
