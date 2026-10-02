import SparseHamiltonian.HermitianLookupProgram

/-!
# Sharp stability of bounded Hamiltonian evolution

A unitary interpolation gives a derivative bounded by the difference of the
generators. The resulting estimate is linear in time and has no exponential
norm factor. The argument holds on an arbitrary complete complex Hilbert space.
-/

namespace SparseHamiltonian.HamiltonianStability

noncomputable section
open ContinuousLinearMap NormedSpace
open scoped InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The derivative of the unitary interpolation factors through the generator
difference, without requiring the two generators to commute. -/
theorem interpolation_hasDerivAt (X Y : V →L[ℂ] V) (s : ℝ) :
    HasDerivAt (fun u : ℝ => exp ((1 - u) • X) * exp (u • Y))
      (exp ((1 - s) • X) * (Y - X) * exp (s • Y)) s := by
  have hLeft := (hasDerivAt_exp_smul_const X (1 - s)).scomp s
    ((hasDerivAt_id s).const_sub 1)
  have hRight := hasDerivAt_exp_smul_const' Y s
  convert! hLeft.mul hRight using 1
  simp only [neg_one_smul, Function.comp_apply]
  noncomm_ring

/-- Exponentiation is nonexpansive on skew-adjoint bounded operators. -/
theorem skew_exp_sub_norm_le (X Y : V →L[ℂ] V)
    (hX : star X = -X) (hY : star Y = -Y) :
    ‖exp X - exp Y‖ ≤ ‖X - Y‖ := by
  have hBound (s : ℝ) :
      ‖exp ((1 - s) • X) * (Y - X) * exp (s • Y)‖ ≤ ‖Y - X‖ := by
    have hLeft : ‖exp ((1 - s) • X)‖ ≤ 1 :=
      CayleyApproximation.skew_exp_norm_le _ (by simp [star_smul, hX])
    have hRight : ‖exp (s • Y)‖ ≤ 1 :=
      CayleyApproximation.skew_exp_norm_le _ (by simp [star_smul, hY])
    calc
      _ ≤ (‖exp ((1 - s) • X)‖ * ‖Y - X‖) * ‖exp (s • Y)‖ :=
        (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1 * ‖Y - X‖) * 1 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_right hLeft (norm_nonneg _)
        · exact hRight
        · exact norm_nonneg _
        · exact mul_nonneg (by norm_num) (norm_nonneg _)
      _ = ‖Y - X‖ := by ring
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun s _ => (interpolation_hasDerivAt X Y s).hasDerivWithinAt)
    (fun s _ => hBound s)
  simpa only [sub_self, zero_smul, exp_zero, one_smul, one_mul, sub_zero,
    mul_one, norm_sub_rev (exp Y) (exp X), norm_sub_rev Y X] using h

/-- Self-adjoint Hamiltonians generate skew-adjoint Schrödinger generators. -/
theorem generator_skew (H : V →L[ℂ] V) (t : ℝ) (hH : star H = H) :
    star ((-Complex.I * (t : ℂ)) • H) = -((-Complex.I * (t : ℂ)) • H) := by
  simp only [star_smul, hH, star_mul, star_neg, Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal]
  module

/-- Hamiltonian evolution changes by at most time times the operator error. -/
theorem evolution_error_le (H G : V →L[ℂ] V) (t : ℝ)
    (hH : star H = H) (hG : star G = G) :
    ‖exp ((-Complex.I * (t : ℂ)) • H) - exp ((-Complex.I * (t : ℂ)) • G)‖ ≤
      |t| * ‖H - G‖ := by
  have h := skew_exp_sub_norm_le _ _ (generator_skew H t hH) (generator_skew G t hG)
  simpa only [← smul_sub, norm_smul, norm_mul, norm_neg, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs] using h

section Output
variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- An implementation for an approximate Hamiltonian retains its full-output
error guarantee for the target Hamiltonian, with the sharp perturbation cost.
The fixed output encoding need only be a contraction. -/
theorem output_error_le (S F : V →L[ℂ] K) (H G : V →L[ℂ] V)
    (t ε δ : ℝ) (hF : ‖F‖ ≤ 1) (hH : star H = H) (hG : star G = G)
    (hError : ‖S - F ∘L exp ((-Complex.I * (t : ℂ)) • G)‖ ≤ ε)
    (hApprox : ‖G - H‖ ≤ δ) :
    ‖S - F ∘L exp ((-Complex.I * (t : ℂ)) • H)‖ ≤ ε + |t| * δ := by
  have hEvolution :
      ‖exp ((-Complex.I * (t : ℂ)) • G) - exp ((-Complex.I * (t : ℂ)) • H)‖ ≤
        |t| * δ :=
    (evolution_error_le G H t hG hH).trans
      (mul_le_mul_of_nonneg_left hApprox (abs_nonneg t))
  have hOutput :
      ‖F ∘L exp ((-Complex.I * (t : ℂ)) • G) -
        F ∘L exp ((-Complex.I * (t : ℂ)) • H)‖ ≤ |t| * δ := by
    rw [← comp_sub]
    calc
      _ ≤ ‖F‖ * ‖exp ((-Complex.I * (t : ℂ)) • G) -
          exp ((-Complex.I * (t : ℂ)) • H)‖ := opNorm_comp_le _ _
      _ ≤ 1 * ‖exp ((-Complex.I * (t : ℂ)) • G) -
          exp ((-Complex.I * (t : ℂ)) • H)‖ :=
        mul_le_mul_of_nonneg_right hF (norm_nonneg _)
      _ ≤ |t| * δ := by simpa only [one_mul] using hEvolution
  exact (norm_sub_le_norm_sub_add_norm_sub S
    (F ∘L exp ((-Complex.I * (t : ℂ)) • G))
    (F ∘L exp ((-Complex.I * (t : ℂ)) • H))).trans
      (add_le_add hError hOutput)

end Output

end
end SparseHamiltonian.HamiltonianStability
