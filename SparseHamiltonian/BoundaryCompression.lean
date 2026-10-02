import SparseHamiltonian.LocalResolvent

/-!
# The boundary compression stays strictly below one on the clock disk

The norm bound is derived from the unitary clock, its resolvent, the exact
boundary compression at one, and the weighted endpoint budget. A small norm
for the compressed resolvent is a conclusion, not an additional assumption.
-/

namespace SparseHamiltonian

noncomputable section

open ContinuousLinearMap
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The public compression of the clock's outgoing resolvent. -/
def boundaryCompression (D R : V →L[ℂ] V) (J : P →L[ℂ] V) : P →L[ℂ] P :=
  J† ∘L D ∘L R ∘L J

/-- Subtracting the identity converts the boundary resolvent into its generator. -/
theorem boundaryCompression_at_one (D R1 : V →L[ℂ] V)
    (J : P →L[ℂ] V) (H : P →L[ℂ] P)
    (hRight : (1 - D) ∘L R1 = 1) (hJ : J† ∘L J = 1)
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H)) :
    boundaryCompression D R1 J = (2 : ℂ)⁻¹ • (-1 + Complex.I • H) := by
  have hDR : D ∘L R1 = R1 - 1 := by
    have h := hRight
    simp only [sub_comp, one_def, id_comp] at h
    apply eq_sub_iff_add_eq.mpr
    have hAdd := sub_add_cancel R1 (D ∘L R1)
    rw [h] at hAdd
    simpa only [one_def, add_comm] using hAdd
  calc
    boundaryCompression D R1 J = (J† ∘L (D ∘L R1)) ∘L J := by
      simp only [boundaryCompression, comp_assoc]
    _ = (J† ∘L (R1 - 1)) ∘L J := by rw [hDR]
    _ = (J† ∘L R1 ∘L J) - 1 := by
      simp only [comp_sub, sub_comp, one_def, comp_id, comp_assoc, hJ]
    _ = (2 : ℂ)⁻¹ • (-1 + Complex.I • H) := by
      rw [hBoundary]
      apply smul_right_injective (P →L[ℂ] P) (two_ne_zero : (2 : ℂ) ≠ 0)
      simp only [smul_sub, smul_smul,
        mul_inv_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0), one_smul, two_smul]
      abel

/-- The compressed resolvent changes by at most one sixth on the clock disk. -/
theorem boundaryCompression_difference_le (D R1 Rz : V →L[ℂ] V)
    (J : P →L[ℂ] V) (z : ℂ) (Q b : ℝ) (hQ : 0 < Q)
    (hD : D† ∘L D = 1)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hRightz : (z • (1 : V →L[ℂ] V) - D) ∘L Rz = 1)
    (hLeftz : Rz ∘L (z • (1 : V →L[ℂ] V) - D) = 1)
    (hRz : ‖Rz‖ ≤ 4 * Q / 3) (hz : ‖z - 1‖ ≤ 1 / (4 * Q))
    (hEndpoint : ‖R1 ∘L J‖ ≤ b) (hBudget : b ^ 2 ≤ Q / 2) :
    ‖boundaryCompression D Rz J - boundaryCompression D R1 J‖ ≤ 1 / 6 := by
  have hExit : ‖(J† ∘L D) ∘L R1‖ ≤ b := by
    rw [comp_assoc, UnitaryResolvent.boundary_endpoint_norm D R1 J hD hRight]
    exact hEndpoint
  have hDiff := ResolventEndpoints.compressed_resolvent_difference_le
    D R1 Rz J (J† ∘L D) z Q b hQ hRight hLeft hRightz hLeftz
    hRz hz hEndpoint hExit
  have hDiff' : ‖boundaryCompression D Rz J - boundaryCompression D R1 J‖ ≤
      (4 / 3 : ℝ) * b ^ 2 * ‖z - 1‖ := by
    simpa only [boundaryCompression, comp_assoc] using hDiff
  refine hDiff'.trans ?_
  calc
    (4 / 3 : ℝ) * b ^ 2 * ‖z - 1‖ ≤
        (4 / 3 : ℝ) * (Q / 2) * (1 / (4 * Q)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hBudget (by norm_num)) hz
        (norm_nonneg _) (by positivity)
    _ = (1 : ℝ) / 6 := by field_simp [ne_of_gt hQ]; ring

/-- Clock boundary promises imply the uniform bound `11/12` throughout the disk. -/
theorem boundaryCompression_norm_le (D R1 Rz : V →L[ℂ] V)
    (J : P →L[ℂ] V) (H : P →L[ℂ] P) (z : ℂ) (Q b : ℝ) (hQ : 0 < Q)
    (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hRightz : (z • (1 : V →L[ℂ] V) - D) ∘L Rz = 1)
    (hLeftz : Rz ∘L (z • (1 : V →L[ℂ] V) - D) = 1)
    (hRz : ‖Rz‖ ≤ 4 * Q / 3) (hz : ‖z - 1‖ ≤ 1 / (4 * Q))
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L J‖ ≤ b) (hBudget : b ^ 2 ≤ Q / 2) :
    ‖boundaryCompression D Rz J‖ ≤ 11 / 12 := by
  have hOne : ‖boundaryCompression D R1 J‖ ≤ 3 / 4 := by
    rw [boundaryCompression_at_one D R1 J H hRight hJ hBoundary]
    exact UnitaryResolvent.boundary_generator_norm H hSelf hH
  have hDiff := boundaryCompression_difference_le D R1 Rz J z Q b hQ hD
    hRight hLeft hRightz hLeftz hRz hz hEndpoint hBudget
  calc
    ‖boundaryCompression D Rz J‖ =
        ‖(boundaryCompression D Rz J - boundaryCompression D R1 J) +
          boundaryCompression D R1 J‖ := by rw [sub_add_cancel]
    _ ≤ ‖boundaryCompression D Rz J - boundaryCompression D R1 J‖ +
        ‖boundaryCompression D R1 J‖ := norm_add_le _ _
    _ ≤ (1 : ℝ) / 6 + 3 / 4 := add_le_add hDiff hOne
    _ = 11 / 12 := by norm_num

/-- In particular the public feedback compression has norm strictly below one. -/
theorem boundaryCompression_norm_lt_one (D R1 Rz : V →L[ℂ] V)
    (J : P →L[ℂ] V) (H : P →L[ℂ] P) (z : ℂ) (Q b : ℝ) (hQ : 0 < Q)
    (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1)
    (hRightz : (z • (1 : V →L[ℂ] V) - D) ∘L Rz = 1)
    (hLeftz : Rz ∘L (z • (1 : V →L[ℂ] V) - D) = 1)
    (hRz : ‖Rz‖ ≤ 4 * Q / 3) (hz : ‖z - 1‖ ≤ 1 / (4 * Q))
    (hBoundary : J† ∘L R1 ∘L J = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L J‖ ≤ b) (hBudget : b ^ 2 ≤ Q / 2) :
    ‖boundaryCompression D Rz J‖ < 1 :=
  (boundaryCompression_norm_le D R1 Rz J H z Q b hQ hD hJ hRight hLeft
    hRightz hLeftz hRz hz hBoundary hSelf hH hEndpoint hBudget).trans_lt (by norm_num)

end

end SparseHamiltonian
