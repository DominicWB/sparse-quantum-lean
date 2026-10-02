import SparseHamiltonian.CyclicClock

/-!
# Adjoint symmetry of a unitary resolvent

Unitarity relates the two boundary endpoint factors without a normality or
spectral-calculus argument. The estimates below use the Hilbert operator norm.
-/

namespace SparseHamiltonian.UnitaryResolvent

section Algebra

variable {A : Type*} [Ring A] [StarRing A]

/-- The resolvent of a unitary at one satisfies a useful adjoint identity. -/
theorem adjoint_resolvent (D R : A)
    (hD : star D * D = 1) (hR : (1 - D) * R = 1) :
    star R = -(D * R) := by
  have hAdj : star R * (1 - star D) = 1 := by
    simpa only [star_mul, star_sub, star_one] using congrArg star hR
  have hInv : (1 - star D) * (-(D * R)) = 1 := by
    calc
      _ = (star D * D - D) * R := by noncomm_ring
      _ = 1 := by rw [hD, hR]
  calc
    star R = star R * 1 := (mul_one _).symm
    _ = star R * ((1 - star D) * (-(D * R))) := by rw [hInv]
    _ = -(D * R) := by rw [← mul_assoc, hAdj, one_mul]

end Algebra

open ContinuousLinearMap
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The exit endpoint is the negative adjoint of the entrance endpoint. -/
theorem boundary_endpoint_adjoint (D R : V →L[ℂ] V) (J : P →L[ℂ] V)
    (hD : D† ∘L D = 1) (hR : (1 - D) ∘L R = 1) :
    J† ∘L (D ∘L R) = -((R ∘L J)†) := by
  have h := adjoint_resolvent D R hD hR
  change R† = -(D ∘L R) at h
  rw [adjoint_comp, h, comp_neg, neg_neg]

/-- Both boundary endpoint factors therefore have exactly the same norm. -/
theorem boundary_endpoint_norm (D R : V →L[ℂ] V) (J : P →L[ℂ] V)
    (hD : D† ∘L D = 1) (hR : (1 - D) ∘L R = 1) :
    ‖J† ∘L (D ∘L R)‖ = ‖R ∘L J‖ := by
  rw [boundary_endpoint_adjoint D R J hD hR, norm_neg]
  exact LinearIsometryEquiv.norm_map _ _

/-- The compressed resolvent generator is uniformly below one in norm.
The rational bound is chosen to leave room for perturbation on the disk. -/
theorem boundary_generator_norm (H : P →L[ℂ] P)
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1) :
    ‖(2 : ℂ)⁻¹ • (-1 + Complex.I • H)‖ ≤ (3 : ℝ) / 4 := by
  let A : P →L[ℂ] P := -1 + Complex.I • H
  have hGram : star A * A = 1 + H * H := by
    simp [A, hSelf, add_mul, mul_add, smul_add, smul_smul]
    abel
  have hHH : ‖H * H‖ ≤ 1 := by
    calc
      _ ≤ ‖H‖ * ‖H‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := mul_le_mul hH hH (norm_nonneg H) (by norm_num)
      _ = 1 := by norm_num
  have hSquare : ‖A‖ ^ 2 ≤ 2 := by
    calc
      _ = ‖star A * A‖ := by
        change ‖A‖ ^ 2 = ‖A† ∘L A‖
        rw [norm_adjoint_comp_self, pow_two]
      _ = ‖1 + H * H‖ := by rw [hGram]
      _ ≤ ‖(1 : P →L[ℂ] P)‖ + ‖H * H‖ := norm_add_le _ _
      _ ≤ 1 + 1 := add_le_add ContinuousLinearMap.norm_id_le hHH
      _ = 2 := by norm_num
  change ‖(2 : ℂ)⁻¹ • A‖ ≤ (3 : ℝ) / 4
  rw [norm_smul, norm_inv]
  norm_num only [Complex.norm_ofNat]
  nlinarith [norm_nonneg A]

end SparseHamiltonian.UnitaryResolvent
