import ODELowerBoundExtensions.Homogeneous.Endpoint

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
-- The flag-extended joint index exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-!
# Proposition `odel:rem:homogeneous`: the half readout and the ideal correlation

Manuscript: the proof of Proposition `odel:rem:homogeneous` (with the readout of the proof of
Theorem `odel:thm:joint`). On success the
solver's output is measured with the half indicator `homHalfObs` of the candidate register
(whatever the flag): it is Hermitian (`homHalfObs_isSelfAdjoint`), a contraction
(`norm_homHalfObs_le`), and every candidate state `|f, a, ω⟩` is an eigenvector with eigenvalue
`halfSign a` (`homHalfObs_flagCand`). Since the normalised final state has probability
`p_* ≥ 16/17` on `a_*` (`homEnd_prob_ge`, `ODELowerBoundExtensions.Homogeneous.Endpoint`),
the ideal signed correlation with `halfSign(a_*)` is at least `p_* - (1 - p_*) ≥ 15/17`
(`homEnd_ideal_corr`; equivalently decision success `(2/3)(16/17 - ε) + 1/6`).
-/

namespace ODELowerBoundExtensions.Homogeneous

noncomputable section
open SparseLowerBounds SparseLowerBounds.ODE SparseHamiltonian
open scoped InnerProductSpace

variable {M n μ s : ℕ}

/-! ### The half indicator -/

/-- The half indicator on a candidate coordinate multiplies by `halfSign`. -/
theorem homHalfObs_inl (v : EuclideanSpace ℂ (HomIndex M μ s)) (g : Bool) (a : Fin M)
    (β : Bool) (c : Fin (2 ^ μ)) :
    homHalfObs M μ s v (g, Sum.inl (a, β, c)) =
      (halfSign M a : ℂ) * v (g, Sum.inl (a, β, c)) := by
  simp [homHalfObs, SparseStateOverlap.matrixOperator_apply, Matrix.diagonal_apply]

/-- The half indicator vanishes on the padding. -/
theorem homHalfObs_inr (v : EuclideanSpace ℂ (HomIndex M μ s)) (g : Bool) (t : Fin s) :
    homHalfObs M μ s v (g, Sum.inr t) = 0 := by
  simp [homHalfObs, SparseStateOverlap.matrixOperator_apply, Matrix.diagonal_apply]

/-- `|f, a, ω⟩` is an eigenvector of the half indicator with eigenvalue `halfSign a`. -/
theorem homHalfObs_flagCand (f : Bool) (a : Fin M) :
    homHalfObs M μ s (flagCand M μ s f a) = (halfSign M a : ℂ) • flagCand M μ s f a := by
  ext i
  rcases i with ⟨g, ⟨a', β, c⟩ | t⟩
  · rw [homHalfObs_inl, PiLp.smul_apply, smul_eq_mul, flagCand_apply]
    dsimp only
    simp only [candState_inl]
    by_cases h : a' = a
    · subst h; rfl
    · simp [h]
  · rw [homHalfObs_inr, PiLp.smul_apply, flagCand_apply]
    simp [candState_inr]

/-- The half indicator on a combination with real coefficients. -/
theorem homHalfObs_flagComb (p q : Fin M → ℝ) :
    homHalfObs M μ s (flagComb M μ s (fun a => (p a : ℂ)) (fun a => (q a : ℂ))) =
      flagComb M μ s (fun a => ((halfSign M a * p a : ℝ) : ℂ))
        (fun a => ((halfSign M a * q a : ℝ) : ℂ)) := by
  simp only [flagComb, map_sum, map_add, map_smul, homHalfObs_flagCand, smul_smul,
    Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm (p a : ℂ), mul_comm (q a : ℂ)]

/-- The half indicator is Hermitian. -/
theorem homHalfObs_isSelfAdjoint : IsSelfAdjoint (homHalfObs M μ s) := by
  refine Hamiltonian.star_matrixOperator_of_isHermitian ?_
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  ext i
  rcases i with ⟨g, ⟨a, β, c⟩ | t⟩ <;> simp [Complex.conj_ofReal]

/-- The half indicator is a contraction. -/
theorem norm_homHalfObs_le : ‖homHalfObs M μ s‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rcases i with ⟨g, ⟨a, β, c⟩ | t⟩
  · rw [homHalfObs_inl, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_halfSign, one_mul]
  · rw [homHalfObs_inr, norm_zero, zero_pow two_ne_zero]; exact sq_nonneg _

/-- Two half signs multiply to at least `-1`. -/
theorem neg_one_le_halfSign_mul (a b : Fin M) : -1 ≤ halfSign M b * halfSign M a := by
  unfold halfSign; split_ifs <;> norm_num

/-- **The ideal signed correlation** (Proposition `odel:rem:homogeneous`): measuring the candidate
half of the normalised final state agrees with the half of `a_*` with signed correlation at least
`p_* - (1 - p_*) ≥ 15/17`. -/
theorem homEnd_ideal_corr (hM : 1 ≤ M) (b : Fin M) :
    15 / 17 ≤ halfSign M b *
      (⟪ODEStateNormalization.unitDirection (homEnd M μ s b),
        homHalfObs M μ s (ODEStateNormalization.unitDirection (homEnd M μ s b))⟫_ℂ).re := by
  rw [unitDirection_homEnd, homHalfObs_flagComb, inner_flagComb_ofReal, Complex.ofReal_re]
  have hN : 0 < ‖homEnd M μ s b‖ := norm_pos_iff.mpr (homEnd_ne_zero hM b)
  have hN2 := norm_sq_homEnd_eq (μ := μ) (s := s) b
  set N := ‖homEnd M μ s b‖
  obtain ⟨hQ, hP, h16⟩ := endPQ_facts hM b
  have hterm : ∀ a, endQ M b a ^ 2 - endP M b a ^ 2 ≤
      halfSign M b * halfSign M a * (endP M b a ^ 2 + endQ M b a ^ 2) := fun a => by
    by_cases ha : a = b
    · subst ha
      have := halfSign_sq a
      simp only [endP, endQ]; nlinarith
    · have := neg_one_le_halfSign_mul a b
      simp only [endP, endQ, if_neg ha]
      nlinarith [sq_nonneg ((Real.sqrt M)⁻¹ * (4 * Real.sqrt M)⁻¹)]
  have hsum : halfSign M b * ∑ a, (N⁻¹ * endP M b a * (halfSign M a * (N⁻¹ * endP M b a)) +
      N⁻¹ * endQ M b a * (halfSign M a * (N⁻¹ * endQ M b a))) =
      (N ^ 2)⁻¹ * ∑ a, halfSign M b * halfSign M a * (endP M b a ^ 2 + endQ M b a ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    field_simp
  rw [hsum]
  have hlow : ∑ a, endQ M b a ^ 2 - ∑ a, endP M b a ^ 2 ≤
      ∑ a, halfSign M b * halfSign M a * (endP M b a ^ 2 + endQ M b a ^ 2) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_le_sum fun a _ => hterm a
  have hQ0 : 0 < ∑ a, endQ M b a ^ 2 := by
    by_contra h; have h' := not_lt.mp h; nlinarith
  rw [← div_eq_inv_mul, le_div_iff₀ (by positivity), hN2]
  nlinarith

end

end ODELowerBoundExtensions.Homogeneous
