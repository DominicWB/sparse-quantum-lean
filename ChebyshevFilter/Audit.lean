import ChebyshevFilter.Proposition

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`. The audits cover every theorem of the
positive Chebyshev filtering library, beginning with Proposition
`qls:prop:chebyshev` and its program form with Lemma `qls:lem:signedwalk`.
-/

/-! ### Proposition `qls:prop:chebyshev` and its program form -/

/-- info: 'ChebyshevFilter.chebyshev_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.chebyshev_filter

/-- info: 'ChebyshevFilter.chebyshev_filter_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.chebyshev_filter_program

/-! ### The augmented walk: degree, probability tests and final projection -/

/-- info: 'ChebyshevFilter.le_artanh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.le_artanh

/-- info: 'ChebyshevFilter.two_thirds_le_log_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.two_thirds_le_log_two

/-- info: 'ChebyshevFilter.arcosh_le_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.arcosh_le_log

/-- info: 'ChebyshevFilter.artanh_bLow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.artanh_bLow

/-- info: 'ChebyshevFilter.bLow_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.bLow_nonneg

/-- info: 'ChebyshevFilter.bLow_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.bLow_lt_one

/-- info: 'ChebyshevFilter.augDegree_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.augDegree_eq

/-- info: 'ChebyshevFilter.augDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.augDegree_le

/-- info: 'ChebyshevFilter.augmented_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.augmented_filter

/-- info: 'ChebyshevFilter.augmented_test_fact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.augmented_test_fact

/-- info: 'ChebyshevFilter.augmented_final_fact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.augmented_final_fact

/-! ### Coherent choice of walk direction (Lemma `qls:lem:signedwalk`) -/

/-- info: 'ChebyshevFilter.diagonal_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.diagonal_mul

/-- info: 'ChebyshevFilter.star_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.star_diagonal

/-- info: 'ChebyshevFilter.diagonal_one'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.diagonal_one'

/-- info: 'ChebyshevFilter.diagonal_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.diagonal_isUnitary

/-- info: 'ChebyshevFilter.lift_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.lift_eval

/-- info: 'ChebyshevFilter.lift_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.lift_cost

/-- info: 'ChebyshevFilter.forwardProg_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.forwardProg_eval

/-- info: 'ChebyshevFilter.forwardProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.forwardProg_cost

/-- info: 'ChebyshevFilter.conjWalk_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.conjWalk_unitary

/-- info: 'ChebyshevFilter.dirOp_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.dirOp_isUnitary

/-- info: 'ChebyshevFilter.fwdGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.fwdGate_unitary

/-- info: 'ChebyshevFilter.bwdGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.bwdGate_unitary

/-- info: 'ChebyshevFilter.midGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.midGate_unitary

/-- info: 'ChebyshevFilter.signedProg_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.signedProg_eval

/-- info: 'ChebyshevFilter.signedProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.signedProg_cost

/-- info: 'ChebyshevFilter.lcuProg_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.lcuProg_eval

/-- info: 'ChebyshevFilter.lcuProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.lcuProg_cost

/-- info: 'ChebyshevFilter.lcuProg_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.lcuProg_compression

/-! ### The LCU circuit with signed walk steps -/

/-- info: 'ChebyshevFilter.power_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.power_mem

/-- info: 'ChebyshevFilter.sum_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.sum_power

/-- info: 'ChebyshevFilter.wpow_zero'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.wpow_zero'

/-- info: 'ChebyshevFilter.dirOp_comp_wpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.dirOp_comp_wpow

/-- info: 'ChebyshevFilter.signedSteps_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.signedSteps_eq

/-- info: 'ChebyshevFilter.signedSteps_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.signedSteps_full

/-- info: 'ChebyshevFilter.adjoint_one_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.adjoint_one_eq

/-- info: 'ChebyshevFilter.seed_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.seed_isometry

/-- info: 'ChebyshevFilter.lcu_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.lcu_compression

/-! ### The filter of a unitary and its error -/

/-- info: 'ChebyshevFilter.wpow_natCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.wpow_natCast

/-- info: 'ChebyshevFilter.wpow_neg_natCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.wpow_neg_natCast

/-- info: 'ChebyshevFilter.filterOp_eq_pairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.filterOp_eq_pairs

/-- info: 'ChebyshevFilter.adjoint_mul_self_of_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.adjoint_mul_self_of_unitary

/-- info: 'ChebyshevFilter.mul_adjoint_self_of_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.mul_adjoint_self_of_unitary

/-- info: 'ChebyshevFilter.sum_pow_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.sum_pow_recurrence

/-- info: 'ChebyshevFilter.sum_pow_apply_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.sum_pow_apply_eigen

/-- info: 'ChebyshevFilter.filterOp_apply_defect_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.filterOp_apply_defect_eigen

/-- info: 'ChebyshevFilter.defect_apply_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.defect_apply_of_fixed

/-- info: 'ChebyshevFilter.eigenValues_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.eigenValues_eq

/-- info: 'ChebyshevFilter.eigenValues_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.eigenValues_nonneg

/-- info: 'ChebyshevFilter.eigenValues_le_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.eigenValues_le_four

/-- info: 'ChebyshevFilter.eigenBasis_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.eigenBasis_fixed

/-- info: 'ChebyshevFilter.eigenBasis_orth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.eigenBasis_orth

/-- info: 'ChebyshevFilter.filterOp_sub_apply_eigenBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.filterOp_sub_apply_eigenBasis

/-- info: 'ChebyshevFilter.abs_errEntry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.abs_errEntry_le

/-- info: 'ChebyshevFilter.norm_filterOp_sub_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.norm_filterOp_sub_apply_le

/-- info: 'ChebyshevFilter.norm_filterOp_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.norm_filterOp_sub_le

/-- info: 'ChebyshevFilter.norm_filterOp_sub_fixedProj_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.norm_filterOp_sub_fixedProj_le

/-- info: 'ChebyshevFilter.norm_filterOp_apply_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.norm_filterOp_apply_sq

/-- info: 'ChebyshevFilter.filterOp_probability_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.filterOp_probability_bounds

/-- info: 'ChebyshevFilter.pow_apply_of_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.pow_apply_of_eigen

/-- info: 'ChebyshevFilter.wpow_apply_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.wpow_apply_eigen

/-- info: 'ChebyshevFilter.filterOp_apply_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.filterOp_apply_eigen

/-- info: 'ChebyshevFilter.norm_exp_mul_I_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.norm_exp_mul_I_sub_one

/-- info: 'ChebyshevFilter.gap_of_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.gap_of_phase

/-! ### Laurent coefficients -/

/-- info: 'ChebyshevFilter.sum_Icc_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.sum_Icc_symm

/-- info: 'ChebyshevFilter.filterCoeff_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.filterCoeff_neg

/-- info: 'ChebyshevFilter.filterCoeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.filterCoeff_zero

/-- info: 'ChebyshevFilter.filterCoeff_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.filterCoeff_succ

/-- info: 'ChebyshevFilter.filterCoeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.filterCoeff_nonneg

/-- info: 'ChebyshevFilter.filterCoeff_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.filterCoeff_eq_zero

/-- info: 'ChebyshevFilter.filterCoeff_series' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.filterCoeff_series

/-- info: 'ChebyshevFilter.filterVal_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.filterVal_one

/-- info: 'ChebyshevFilter.filterFun_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.filterFun_zero

/-- info: 'ChebyshevFilter.sum_filterCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.sum_filterCoeff

/-- info: 'ChebyshevFilter.exp_add_exp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.exp_add_exp_neg

/-- info: 'ChebyshevFilter.laurent_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.laurent_eq

/-- info: 'ChebyshevFilter.abs_filterVal_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.abs_filterVal_le

/-! ### The normalisation and the degree -/

/-- info: 'ChebyshevFilter.sq_lt_one_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.sq_lt_one_of_mem

/-- info: 'ChebyshevFilter.one_add_two_lam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.one_add_two_lam

/-- info: 'ChebyshevFilter.filterNorm_eq_cosh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.filterNorm_eq_cosh

/-- info: 'ChebyshevFilter.one_le_filterNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.one_le_filterNorm

/-- info: 'ChebyshevFilter.filterNorm_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.filterNorm_pos

/-- info: 'ChebyshevFilter.inv_filterNorm_chebDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.inv_filterNorm_chebDegree_le

/-- info: 'ChebyshevFilter.abs_affine_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.abs_affine_le_one

/-- info: 'ChebyshevFilter.abs_T_affine_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.abs_T_affine_le_one

/-! ### Positivity of the shifted Chebyshev polynomial -/

/-- info: 'ChebyshevFilter.monomial_comp_X_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.monomial_comp_X_add

/-- info: 'ChebyshevFilter.comp_X_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.comp_X_add

/-- info: 'ChebyshevFilter.lam_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.lam_nonneg

/-- info: 'ChebyshevFilter.eval_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.eval_shifted

/-- info: 'ChebyshevFilter.hasseDeriv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.hasseDeriv_eq

/-- info: 'ChebyshevFilter.shifted_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.shifted_taylor

/-- info: 'ChebyshevFilter.shifted_mem_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.shifted_mem_cone

/-- info: 'ChebyshevFilter.shiftCoeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.shiftCoeff_nonneg

/-- info: 'ChebyshevFilter.shiftCoeff_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.shiftCoeff_eq_zero

/-- info: 'ChebyshevFilter.shifted_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.shifted_eq_sum

/-- info: 'ChebyshevFilter.eval_shifted_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.eval_shifted_eq_sum

/-- info: 'ChebyshevFilter.T_mem_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.T_mem_cone

/-- info: 'ChebyshevFilter.cone_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.cone_mono

/-- info: 'ChebyshevFilter.one_mem_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.one_mem_cone

/-- info: 'ChebyshevFilter.real_smul_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.real_smul_mem

/-- info: 'ChebyshevFilter.C_mul_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.C_mul_mem

/-- info: 'ChebyshevFilter.T_mul_T_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.T_mul_T_nat

/-- info: 'ChebyshevFilter.T_mul_T_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.T_mul_T_mem

/-- info: 'ChebyshevFilter.mul_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.mul_mem

/-- info: 'ChebyshevFilter.pow_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.pow_mem

/-- info: 'ChebyshevFilter.X_add_one_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.X_add_one_mem

/-- info: 'ChebyshevFilter.X_add_one_pow_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.X_add_one_pow_mem

/-- info: 'ChebyshevFilter.iterate_derivative_T_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.iterate_derivative_T_mem

/-- info: 'ChebyshevFilter.isUnit_leadingCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.isUnit_leadingCoeff

/-- info: 'ChebyshevFilter.chebBasis_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.chebBasis_apply

/-- info: 'ChebyshevFilter.chebCoeff_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.chebCoeff_T

/-- info: 'ChebyshevFilter.chebCoeff_cone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.chebCoeff_cone

/-- info: 'ChebyshevFilter.chebCoeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.chebCoeff_nonneg

/-- info: 'ChebyshevFilter.chebCoeff_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.chebCoeff_eq_zero

/-- info: 'ChebyshevFilter.eq_sum_chebCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevFilter.eq_sum_chebCoeff
