import SparseHamiltonian.UnitaryResolvent

/-!
# Weighted resolvent endpoints in the genuine operator norm

The public and private normed spaces are different types. Two-sided inverse
identities at one and at `z` imply both orientations of the resolvent identity.
Consequently bounds on the *weighted endpoints* at one persist throughout the
small resolvent disk, without inserting the larger unweighted factor `Q`.

No finite-dimensionality, normality, or completeness is needed after the
inverse identities are supplied. Existence of the inverses in the clock disk
is proved separately in `OperatorResolvent.lean`.
-/

namespace SparseHamiltonian
namespace ResolventEndpoints

section RingIdentity

variable {A : Type*} [Ring A]

/-- The algebraic resolvent identity using opposite sides of the two inverses. -/
theorem inverse_sub_identity (X Y R S : A)
    (hXR : X * R = 1) (hSY : S * Y = 1) :
    S - R = S * (X - Y) * R := by
  calc
    S - R = S * (X * R) - (S * Y) * R := by rw [hXR, hSY, mul_one, one_mul]
    _ = S * (X - Y) * R := by noncomm_ring

/-- The reversed product orientation uses the other sides of the inverses. -/
theorem inverse_sub_identity_reversed (X Y R S : A)
    (hRX : R * X = 1) (hYS : Y * S = 1) :
    S - R = R * (X - Y) * S := by
  calc
    S - R = (R * X) * S - R * (Y * S) := by rw [hRX, hYS, one_mul, mul_one]
    _ = R * (X - Y) * S := by noncomm_ring

end RingIdentity

section Endpoints

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

local notation "EndV" => V →L[ℂ] V

/-- Resolvent identity with `Rz` to the left of `R1`. -/
theorem resolvent_sub_right (D R1 Rz : EndV) (z : ℂ)
    (hRight : (1 - D) * R1 = 1)
    (hLeftz : Rz * (z • (1 : EndV) - D) = 1) :
    Rz - R1 = -(z - 1) • (Rz * R1) := by
  have hDiff : (1 - D) - (z • (1 : EndV) - D) = -(z - 1) • (1 : EndV) := by
    simp only [neg_sub, sub_smul, one_smul]
    abel
  rw [inverse_sub_identity (1 - D) (z • (1 : EndV) - D) R1 Rz hRight hLeftz,
    hDiff, mul_smul_comm, smul_mul_assoc, mul_one]

/-- Resolvent identity with `R1` to the left of `Rz`. -/
theorem resolvent_sub_left (D R1 Rz : EndV) (z : ℂ)
    (hLeft : R1 * (1 - D) = 1)
    (hRightz : (z • (1 : EndV) - D) * Rz = 1) :
    Rz - R1 = -(z - 1) • (R1 * Rz) := by
  have hDiff : (1 - D) - (z • (1 : EndV) - D) = -(z - 1) • (1 : EndV) := by
    simp only [neg_sub, sub_smul, one_smul]
    abel
  rw [inverse_sub_identity_reversed (1 - D) (z • (1 : EndV) - D) R1 Rz hLeft hRightz,
    hDiff, mul_smul_comm, smul_mul_assoc, mul_one]

/-- Exact weighted resolvent identity at the incoming endpoint. -/
theorem right_endpoint_identity (D R1 Rz : EndV) (J : P →L[ℂ] V) (z : ℂ)
    (hRight : (1 - D) * R1 = 1)
    (hLeftz : Rz * (z • (1 : EndV) - D) = 1) :
    Rz.comp J = R1.comp J - (z - 1) • (Rz.comp (R1.comp J)) := by
  have h := congrArg (fun T : EndV ↦ T.comp J)
    (resolvent_sub_right D R1 Rz z hRight hLeftz)
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] at h
  rw [sub_eq_iff_eq_add] at h
  simpa only [neg_smul, sub_eq_add_neg, add_comm] using h

/-- Exact weighted resolvent identity at the outgoing endpoint. -/
theorem left_endpoint_identity (D R1 Rz : EndV) (B : V →L[ℂ] P) (z : ℂ)
    (hLeft : R1 * (1 - D) = 1)
    (hRightz : (z • (1 : EndV) - D) * Rz = 1) :
    B.comp Rz = B.comp R1 - (z - 1) • ((B.comp R1).comp Rz) := by
  have h := congrArg (fun T : EndV ↦ B.comp T)
    (resolvent_sub_left D R1 Rz z hLeft hRightz)
  simp only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.mul_def, ← ContinuousLinearMap.comp_assoc] at h
  rw [sub_eq_iff_eq_add] at h
  simpa only [neg_smul, sub_eq_add_neg, add_comm] using h

/-- The incoming weighted endpoint incurs only a relative growth factor. -/
theorem right_endpoint_norm_growth (D R1 Rz : EndV) (J : P →L[ℂ] V) (z : ℂ)
    (hRight : (1 - D) * R1 = 1)
    (hLeftz : Rz * (z • (1 : EndV) - D) = 1) :
    ‖Rz.comp J‖ ≤ (1 + ‖z - 1‖ * ‖Rz‖) * ‖R1.comp J‖ := by
  rw [right_endpoint_identity D R1 Rz J z hRight hLeftz]
  calc
    ‖R1.comp J - (z - 1) • Rz.comp (R1.comp J)‖ ≤
        ‖R1.comp J‖ + ‖(z - 1) • Rz.comp (R1.comp J)‖ := norm_sub_le _ _
    _ = ‖R1.comp J‖ + ‖z - 1‖ * ‖Rz.comp (R1.comp J)‖ := by rw [norm_smul]
    _ ≤ ‖R1.comp J‖ + ‖z - 1‖ * (‖Rz‖ * ‖R1.comp J‖) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (Rz.opNorm_comp_le (R1.comp J)) (norm_nonneg (z - 1)))
    _ = (1 + ‖z - 1‖ * ‖Rz‖) * ‖R1.comp J‖ := by ring

/-- The outgoing weighted endpoint has the same relative growth factor. -/
theorem left_endpoint_norm_growth (D R1 Rz : EndV) (B : V →L[ℂ] P) (z : ℂ)
    (hLeft : R1 * (1 - D) = 1)
    (hRightz : (z • (1 : EndV) - D) * Rz = 1) :
    ‖B.comp Rz‖ ≤ (1 + ‖z - 1‖ * ‖Rz‖) * ‖B.comp R1‖ := by
  rw [left_endpoint_identity D R1 Rz B z hLeft hRightz]
  calc
    ‖B.comp R1 - (z - 1) • (B.comp R1).comp Rz‖ ≤
        ‖B.comp R1‖ + ‖(z - 1) • (B.comp R1).comp Rz‖ := norm_sub_le _ _
    _ = ‖B.comp R1‖ + ‖z - 1‖ * ‖(B.comp R1).comp Rz‖ := by rw [norm_smul]
    _ ≤ ‖B.comp R1‖ + ‖z - 1‖ * (‖B.comp R1‖ * ‖Rz‖) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        ((B.comp R1).opNorm_comp_le Rz) (norm_nonneg (z - 1)))
    _ = (1 + ‖z - 1‖ * ‖Rz‖) * ‖B.comp R1‖ := by ring

/-- The relative endpoint growth factor is at most `4/3` in the clock disk. -/
theorem endpoint_growth_factor_le (Rz : EndV) (z : ℂ) (Q : ℝ) (hQ : 0 < Q)
    (hRz : ‖Rz‖ ≤ 4 * Q / 3) (hz : ‖z - 1‖ ≤ 1 / (4 * Q)) :
    1 + ‖z - 1‖ * ‖Rz‖ ≤ 4 / 3 := by
  calc
    1 + ‖z - 1‖ * ‖Rz‖ ≤ 1 + (1 / (4 * Q)) * (4 * Q / 3) := by
      exact add_le_add le_rfl (mul_le_mul hz hRz (norm_nonneg Rz) (by positivity))
    _ = (4 : ℝ) / 3 := by field_simp [ne_of_gt hQ]; ring

/-- Weighted incoming endpoint bound, independent of the public dimension. -/
theorem right_endpoint_norm_le (D R1 Rz : EndV) (J : P →L[ℂ] V)
    (z : ℂ) (Q b : ℝ) (hQ : 0 < Q)
    (hRight : (1 - D) * R1 = 1)
    (hLeftz : Rz * (z • (1 : EndV) - D) = 1)
    (hRz : ‖Rz‖ ≤ 4 * Q / 3) (hz : ‖z - 1‖ ≤ 1 / (4 * Q))
    (hJ : ‖R1.comp J‖ ≤ b) :
    ‖Rz.comp J‖ ≤ 4 * b / 3 := by
  calc
    ‖Rz.comp J‖ ≤ (1 + ‖z - 1‖ * ‖Rz‖) * ‖R1.comp J‖ :=
      right_endpoint_norm_growth D R1 Rz J z hRight hLeftz
    _ ≤ (4 / 3 : ℝ) * b := mul_le_mul
      (endpoint_growth_factor_le Rz z Q hQ hRz hz) hJ (norm_nonneg _) (by norm_num)
    _ = 4 * b / 3 := by ring

/-- Weighted outgoing endpoint bound. -/
theorem left_endpoint_norm_le (D R1 Rz : EndV) (B : V →L[ℂ] P)
    (z : ℂ) (Q b : ℝ) (hQ : 0 < Q)
    (hLeft : R1 * (1 - D) = 1)
    (hRightz : (z • (1 : EndV) - D) * Rz = 1)
    (hRz : ‖Rz‖ ≤ 4 * Q / 3) (hz : ‖z - 1‖ ≤ 1 / (4 * Q))
    (hB : ‖B.comp R1‖ ≤ b) :
    ‖B.comp Rz‖ ≤ 4 * b / 3 := by
  calc
    ‖B.comp Rz‖ ≤ (1 + ‖z - 1‖ * ‖Rz‖) * ‖B.comp R1‖ :=
      left_endpoint_norm_growth D R1 Rz B z hLeft hRightz
    _ ≤ (4 / 3 : ℝ) * b := mul_le_mul
      (endpoint_growth_factor_le Rz z Q hQ hRz hz) hB (norm_nonneg _) (by norm_num)
    _ = 4 * b / 3 := by ring

/-- Exact compressed resolvent difference retaining both weighted endpoints. -/
theorem compressed_resolvent_difference (D R1 Rz : EndV)
    (J : P →L[ℂ] V) (B : V →L[ℂ] P) (z : ℂ)
    (hRight : (1 - D) * R1 = 1)
    (hLeftz : Rz * (z • (1 : EndV) - D) = 1) :
    (B.comp Rz).comp J - (B.comp R1).comp J =
      -(z - 1) • ((B.comp Rz).comp (R1.comp J)) := by
  have h := congrArg (fun T : EndV ↦ (B.comp T).comp J)
    (resolvent_sub_right D R1 Rz z hRight hLeftz)
  simpa only [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc] using h

/-- Sharp endpoint-product estimate for the compressed resolvent difference. -/
theorem compressed_resolvent_difference_norm (D R1 Rz : EndV)
    (J : P →L[ℂ] V) (B : V →L[ℂ] P) (z : ℂ)
    (hRight : (1 - D) * R1 = 1)
    (hLeftz : Rz * (z • (1 : EndV) - D) = 1) :
    ‖(B.comp Rz).comp J - (B.comp R1).comp J‖ ≤
      ‖z - 1‖ * (‖B.comp Rz‖ * ‖R1.comp J‖) := by
  rw [compressed_resolvent_difference D R1 Rz J B z hRight hLeftz, norm_smul, norm_neg]
  exact mul_le_mul_of_nonneg_left ((B.comp Rz).opNorm_comp_le (R1.comp J)) (norm_nonneg _)

/-- A Lipschitz estimate controlled by the squared weighted endpoint bound.
For `b² = qbar/2`, the coefficient is `2 qbar / 3`.
-/
theorem compressed_resolvent_difference_le (D R1 Rz : EndV)
    (J : P →L[ℂ] V) (B : V →L[ℂ] P) (z : ℂ) (Q b : ℝ) (hQ : 0 < Q)
    (hRight : (1 - D) * R1 = 1) (hLeft : R1 * (1 - D) = 1)
    (hRightz : (z • (1 : EndV) - D) * Rz = 1)
    (hLeftz : Rz * (z • (1 : EndV) - D) = 1)
    (hRz : ‖Rz‖ ≤ 4 * Q / 3) (hz : ‖z - 1‖ ≤ 1 / (4 * Q))
    (hJ : ‖R1.comp J‖ ≤ b) (hB : ‖B.comp R1‖ ≤ b) :
    ‖(B.comp Rz).comp J - (B.comp R1).comp J‖ ≤ (4 / 3 : ℝ) * b ^ 2 * ‖z - 1‖ := by
  have hb : 0 ≤ b := (norm_nonneg _).trans hJ
  have hBz := left_endpoint_norm_le D R1 Rz B z Q b hQ hLeft hRightz hRz hz hB
  calc
    ‖(B.comp Rz).comp J - (B.comp R1).comp J‖ ≤
        ‖z - 1‖ * (‖B.comp Rz‖ * ‖R1.comp J‖) :=
      compressed_resolvent_difference_norm D R1 Rz J B z hRight hLeftz
    _ ≤ ‖z - 1‖ * ((4 * b / 3) * b) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hBz hJ (norm_nonneg _) (by positivity)) (norm_nonneg _)
    _ = (4 / 3 : ℝ) * b ^ 2 * ‖z - 1‖ := by ring

end Endpoints

end ResolventEndpoints
end SparseHamiltonian
