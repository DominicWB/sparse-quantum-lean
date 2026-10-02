import SparseHamiltonian.WeightedClock

/-!
# Energy conservation for the clock boundary rotation

The two outputs of one clock step preserve the sum of squared Hilbert norms.
Only the clock and boundary isometry identities and the real rotation
relations are needed; no inverse or spectral assumption is used.
-/

namespace SparseHamiltonian.LocalRotation

noncomputable section

open ContinuousLinearMap
open scoped InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

omit [CompleteSpace P] in
theorem norm_real_smul_sq (r : ℝ) (x : P) :
    ‖(r : ℂ) • x‖ ^ 2 = r ^ 2 * ‖x‖ ^ 2 := by
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

omit [CompleteSpace P] in
/-- Two-dimensional real rotations preserve energy for Hilbert-space vectors. -/
theorem rotation_energy (c σ : ℝ) (a p : P) (hσ : σ ^ 2 = 1 - c ^ 2) :
    ‖(c : ℂ) • a + (σ : ℂ) • p‖ ^ 2 +
      ‖(c : ℂ) • p - (σ : ℂ) • a‖ ^ 2 = ‖a‖ ^ 2 + ‖p‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ)]
  simp only [norm_real_smul_sq, inner_smul_left, inner_smul_right,
    RCLike.re_to_complex, Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have hi : (inner ℂ p a).re = (inner ℂ a p).re := by
    rw [← inner_conj_symm a p]
    rfl
  rw [hi, hσ]
  ring

/-- Orthogonal decomposition into the range of the boundary isometry and its
orthogonal complement, expressed as a squared norm identity. -/
theorem boundary_decomposition_energy (J : P →L[ℂ] V) (hJ : J† ∘L J = 1)
    (y : V) (v : P) :
    ‖y - J ((J†) y) + J v‖ ^ 2 = ‖y - J ((J†) y)‖ ^ 2 + ‖v‖ ^ 2 := by
  have hn := J.norm_map_iff_adjoint_comp_self.mpr hJ
  have hi : inner ℂ (y - J ((J†) y)) (J v) = 0 := by
    rw [← adjoint_inner_left, map_sub]
    have hJJ : (J†) (J ((J†) y)) = (J†) y := by
      change (J† ∘L J) ((J†) y) = (J†) y
      rw [hJ]
      rfl
    rw [hJJ, sub_self, inner_zero_left]
  rw [norm_add_sq (𝕜 := ℂ), hi]
  simp [hn]

/-- The boundary rotation conserves private plus public energy. -/
theorem boundary_rotation_energy (J : P →L[ℂ] V) (hJ : J† ∘L J = 1)
    (c κ σ : ℝ) (hκ : κ = 1 - c) (hσ : σ ^ 2 = 1 - c ^ 2)
    (y : V) (p : P) :
    ‖y - (κ : ℂ) • J ((J†) y) + (σ : ℂ) • J p‖ ^ 2 +
      ‖(c : ℂ) • p - (σ : ℂ) • (J†) y‖ ^ 2 = ‖y‖ ^ 2 + ‖p‖ ^ 2 := by
  have hout : y - (κ : ℂ) • J ((J†) y) + (σ : ℂ) • J p =
      y - J ((J†) y) + J ((c : ℂ) • (J†) y + (σ : ℂ) • p) := by
    rw [hκ]
    simp only [map_add, map_smul, Complex.ofReal_sub, Complex.ofReal_one]
    module
  have hin := boundary_decomposition_energy J hJ y ((J†) y)
  have hrot := rotation_energy c σ ((J†) y) p hσ
  rw [hout, boundary_decomposition_energy J hJ]
  have hin' : ‖y‖ ^ 2 = ‖y - J ((J†) y)‖ ^ 2 + ‖(J†) y‖ ^ 2 := by
    simpa only [sub_add_cancel] using hin
  linarith

/-- The actual local private and public blocks preserve total energy. -/
theorem local_step_energy (D : V →L[ℂ] V) (J : P →L[ℂ] V)
    (c κ σ : ℝ) (hκ : κ = 1 - c) (hσ : σ ^ 2 = 1 - c ^ 2)
    (hD : D† ∘L D = 1) (hJ : J† ∘L J = 1) (x : V) (p : P) :
    ‖GlobalResolvent.localPrivateBlock D J κ x + ((σ : ℂ) • J) p‖ ^ 2 +
      ‖((c : ℂ) • (1 : P →L[ℂ] P)) p +
        ((-(σ : ℂ)) • (J† ∘L D)) x‖ ^ 2 = ‖x‖ ^ 2 + ‖p‖ ^ 2 := by
  have h := boundary_rotation_energy J hJ c κ σ hκ hσ (D x) p
  have hn := D.norm_map_iff_adjoint_comp_self.mpr hD
  simpa only [GlobalResolvent.localPrivateBlock, comp_apply, sub_apply, smul_apply,
    one_def, id_apply, neg_smul, neg_apply, ← sub_eq_add_neg, hn] using h

end

end SparseHamiltonian.LocalRotation
