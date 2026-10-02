import SparseHamiltonian.FilterDepth

/-!
# A global chronological resolvent from clock boundary promises

This module combines the local clock inverse, weighted boundary compression,
Woodbury correction, base transfer identity, and chronological block estimate.
The resulting inverse is constructed for the actual finite private operator.
The clock boundary identities remain explicit hypotheses; no local corrected
norm bound or global inverse is assumed.
-/

namespace SparseHamiltonian.GlobalResolvent

noncomputable section

open ContinuousLinearMap
open scoped InnerProduct
open SparseHamiltonian.ChronologicalResolvent

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The local clock after the boundary rotation's private action. -/
def localPrivateBlock (D : V →L[ℂ] V) (J : P →L[ℂ] V) (κ : ℝ) : V →L[ℂ] V :=
  (1 - (κ : ℂ) • (J ∘L J†)) ∘L D

/-- The actual finite chronological private block, including both boundary
couplings and the direct public action. -/
def globalPrivateBlock (D : V →L[ℂ] V) (J : P →L[ℂ] V)
    (c κ σ : ℝ) (T : ℕ) : BlockOperator.H T V →L[ℂ] BlockOperator.H T V :=
  chronologicalOperator (localPrivateBlock D J κ) ((σ : ℂ) • J)
    ((c : ℂ) • 1) ((-(σ : ℂ)) • (J† ∘L D)) T

omit [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] in
/-- The clock disk inverse also exists when the private space is trivial. -/
theorem exists_clock_disk_inverse (D R1 : V →L[ℂ] V) {Q : ℝ} (hQ : 0 < Q)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hR1 : ‖R1‖ ≤ Q) (z : ℂ) (hz : ‖z - 1‖ ≤ 1 / (4 * Q)) :
    ∃ Rz : V →L[ℂ] V,
      (z • 1 - D) ∘L Rz = 1 ∧ Rz ∘L (z • 1 - D) = 1 ∧ ‖Rz‖ ≤ 4 * Q / 3 := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · letI := hV
    refine ⟨0, Subsingleton.elim _ _, Subsingleton.elim _ _, ?_⟩
    simp only [norm_zero]
    positivity
  · letI := hV
    exact OperatorResolvent.exists_resolvent_in_disk D R1 Q hQ hRight hLeft hR1 z hz

/-- The local denominator has exactly the finite-rank-update form. -/
theorem localPrivateBlock_denominator (D : V →L[ℂ] V) (J : P →L[ℂ] V)
    (κ : ℝ) (z : ℂ) :
    z • 1 - localPrivateBlock D J κ =
      (z • 1 - D) + (κ : ℂ) • (J ∘L (J† ∘L D)) := by
  simp only [localPrivateBlock, sub_comp, smul_comp, one_def, id_comp, comp_assoc]
  abel

/-- Clock boundary promises imply a corrected local inverse, both weighted
endpoint bounds, and the public transfer growth bound throughout the disk. -/
theorem exists_local_clock_certificate
    (D R1 : V →L[ℂ] V) (J : P →L[ℂ] V) (H : P →L[ℂ] P)
    (c κ σ w Q b qbar : ℝ) (z : ℂ)
    (hQ : 0 < Q) (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hκUpper : κ ≤ 2 / 9)
    (hκc : κ = 1 - c) (hσc : σ ^ 2 = 1 - c ^ 2) (hσw : σ ^ 2 ≤ 2 * w)
    (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hz : ‖z - 1‖ ≤ 1 / (4 * Q)) :
    ∃ S : V →L[ℂ] V,
      (z • 1 - localPrivateBlock D J κ) ∘L S = 1 ∧
      S ∘L (z • 1 - localPrivateBlock D J κ) = 1 ∧
      ‖S‖ ≤ 2 * Q ∧ ‖S ∘L J‖ ≤ 12 * b / 7 ∧
      ‖(J† ∘L D) ∘L S‖ ≤ 12 * b / 7 ∧
      ‖(c : ℂ) • 1 + ((-(σ : ℂ)) • (J† ∘L D)) ∘L S ∘L ((σ : ℂ) • J)‖ ≤
        1 + 3 * w * qbar / (4 * Q) := by
  have hb : 0 ≤ b := (norm_nonneg _).trans hEndpoint
  have hq : 0 ≤ qbar := by nlinarith [sq_nonneg b]
  have hBudget : b ^ 2 ≤ Q / 2 := by linarith
  obtain ⟨Rz, hRightz, hLeftz, hRz⟩ :=
    exists_clock_disk_inverse D R1 hQ hRight hLeft hR1 z hz
  let E : V →L[ℂ] P := J† ∘L D
  let F0 : P →L[ℂ] P := boundaryCompression D R1 J
  let Fz : P →L[ℂ] P := boundaryCompression D Rz J
  have hExit : ‖E ∘L R1‖ ≤ b := by
    calc
      ‖E ∘L R1‖ = ‖R1 ∘L J‖ := by
        simpa only [E, comp_assoc] using
          UnitaryResolvent.boundary_endpoint_norm D R1 J hD hRight
      _ ≤ b := hEndpoint
  have hRzJ : ‖Rz ∘L J‖ ≤ 4 * b / 3 :=
    ResolventEndpoints.right_endpoint_norm_le D R1 Rz J z Q b hQ hRight hLeftz hRz hz hEndpoint
  have hERz : ‖E ∘L Rz‖ ≤ 4 * b / 3 :=
    ResolventEndpoints.left_endpoint_norm_le D R1 Rz E z Q b hQ hLeft hRightz hRz hz hExit
  have hFz : ‖E ∘L Rz ∘L J‖ ≤ 1 := by
    have h := boundaryCompression_norm_le D R1 Rz J H z Q b hQ hD hJ hRight hLeft
      hRightz hLeftz hRz hz hBoundary hSelf hH hEndpoint hBudget
    have h' : ‖E ∘L Rz ∘L J‖ ≤ 11 / 12 := by
      simpa only [E, boundaryCompression, comp_assoc] using h
    linarith
  obtain ⟨K, S, hKRight, hKLeft, hK, hS, hSRight, hSLeft, hSNorm, hSJ, hES⟩ :=
    exists_bounded_local_resolvent (z • 1 - D) Rz J E hκ hκUpper hb hBudget
      hRightz hLeftz hFz hRz hRzJ hERz
  have hF0eq : F0 = BaseTransfer.halfGenerator H :=
    boundaryCompression_at_one D R1 J H hRight hJ hBoundary
  have hF0norm : ‖F0‖ ≤ 1 := by
    have h : ‖F0‖ ≤ 3 / 4 := by
      rw [hF0eq]
      exact UnitaryResolvent.boundary_generator_norm H hSelf hH
    linarith
  obtain ⟨K0, hK0Right, hK0Left, hK0⟩ :=
    exists_public_feedback_inverse F0 hκ hκUpper hF0norm
  have hF0star : F0 + star F0 = -1 := by
    rw [hF0eq]
    exact BaseTransfer.halfGenerator_star_sum H hSelf
  have hBase : ‖BoundaryTransfer.transfer (c : ℂ) (σ ^ 2) F0 K0‖ ≤ 1 :=
    BaseTransfer.transfer_norm_le_one c κ (σ ^ 2) F0 K0 hκc hσc hF0star hK0Right
  have hDifference : ‖Fz - F0‖ ≤ (2 / 3 : ℝ) * qbar * ‖z - 1‖ := by
    have h := ResolventEndpoints.compressed_resolvent_difference_le D R1 Rz J E z Q b hQ
      hRight hLeft hRightz hLeftz hRz hz hEndpoint hExit
    calc
      ‖Fz - F0‖ ≤ (4 / 3 : ℝ) * b ^ 2 * ‖z - 1‖ := by
        simpa only [Fz, F0, E, boundaryCompression, comp_assoc] using h
      _ ≤ (4 / 3 : ℝ) * (qbar / 2) * ‖z - 1‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbq (by norm_num)) (norm_nonneg _)
      _ = (2 / 3 : ℝ) * qbar * ‖z - 1‖ := by ring
  have hKRight' : (1 + (κ : ℂ) • Fz) * K = 1 := by
    simpa only [Fz, E, boundaryCompression, mul_def, comp_assoc] using hKRight
  have hKLeft' : K * (1 + (κ : ℂ) • Fz) = 1 := by
    simpa only [Fz, E, boundaryCompression, mul_def, comp_assoc] using hKLeft
  have hTransfer := BoundaryTransfer.transfer_norm_le (c : ℂ) (κ : ℂ)
    (σ ^ 2) w qbar ‖z - 1‖ Fz F0 K K0 hw hq (norm_nonneg _) (sq_nonneg σ) hσw
    hKRight' hKLeft' hK0Right hK0Left hK hK0 hDifference hBase
  have hTransferDisk : ‖BoundaryTransfer.transfer (c : ℂ) (σ ^ 2) Fz K‖ ≤
      1 + 3 * w * qbar / (4 * Q) := by
    calc
      _ ≤ 1 + 3 * w * qbar * ‖z - 1‖ := hTransfer
      _ ≤ 1 + 3 * w * qbar * (1 / (4 * Q)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hz (by positivity))
      _ = _ := by ring
  refine ⟨S, ?_, ?_, hSNorm, hSJ, hES, ?_⟩
  · simpa only [localPrivateBlock_denominator, E] using hSRight
  · simpa only [localPrivateBlock_denominator, E] using hSLeft
  · rw [hS, woodbury_chronological_transfer Rz J K E κ c σ hKLeft]
    simpa only [Fz, E, boundaryCompression, comp_assoc] using hTransferDisk

/-- The clock promises imply existence and the weighted norm bound for the
resolvent of the actual finite chronological private block. All corrected
local estimates and the global inverse are conclusions of the construction. -/
theorem exists_global_resolvent
    (D R1 : V →L[ℂ] V) (J : P →L[ℂ] V) (H : P →L[ℂ] P)
    (c κ σ w Q b qbar : ℝ) (T : ℕ) (z : ℂ)
    (hQ : 0 < Q) (hw : 0 ≤ w) (hκ : 0 ≤ κ) (hκUpper : κ ≤ 2 / 9)
    (hκc : κ = 1 - c) (hσc : σ ^ 2 = 1 - c ^ 2) (hσw : σ ^ 2 ≤ 2 * w)
    (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L J‖ ≤ b) (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hz : ‖z - 1‖ ≤ 1 / (4 * Q)) :
    ∃ S : BlockOperator.H T V →L[ℂ] BlockOperator.H T V,
      (z • 1 - globalPrivateBlock D J c κ σ T) ∘L S = 1 ∧
      S ∘L (z • 1 - globalPrivateBlock D J c κ σ T) = 1 ∧
      ‖S‖ ≤ 3 * (Q + (T : ℝ) * w * qbar) *
        Real.exp (3 * ((T : ℝ) * w * qbar) / (4 * Q)) := by
  have hb : 0 ≤ b := (norm_nonneg _).trans hEndpoint
  have hq : 0 ≤ qbar := by nlinarith [sq_nonneg b]
  obtain ⟨R, hRRight, hRLeft, hRNorm, hRJ, hER, hTransfer⟩ :=
    exists_local_clock_certificate D R1 J H c κ σ w Q b qbar z hQ hw hκ hκUpper
      hκc hσc hσw hD hJ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ hz
  have hσNorm : ‖(σ : ℂ)‖ ^ 2 ≤ 2 * w := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hσw
  have hCoupling :
      ‖R ∘L ((σ : ℂ) • J)‖ * ‖((-(σ : ℂ)) • (J† ∘L D)) ∘L R‖ ≤
        (144 / 49 : ℝ) * w * qbar := by
    simpa only [comp_smul, smul_comp] using
      ChronologicalBound.coupling_norm_product_le (R ∘L J) ((J† ∘L D) ∘L R)
        (σ : ℂ) hw hb hσNorm hbq hRJ hER
  exact ChronologicalBound.exists_chronological_resolvent
    (localPrivateBlock D J κ) R ((σ : ℂ) • J) ((c : ℂ) • 1)
    ((-(σ : ℂ)) • (J† ∘L D)) T z hQ hw hq
    hRRight hRLeft hRNorm hCoupling hTransfer

end

end SparseHamiltonian.GlobalResolvent
