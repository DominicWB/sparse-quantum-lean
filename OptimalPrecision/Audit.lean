import OptimalPrecision.Taylor.Basic
import OptimalPrecision.Taylor.Estimates
import OptimalPrecision.Taylor.Fejer
import OptimalPrecision.Weights.Operator
import OptimalPrecision.Weights.Laguerre
import OptimalPrecision.Weights.Cesaro
import OptimalPrecision.Weights.Transfer
import OptimalPrecision.Weights.Profile
import OptimalPrecision.Weights.Resolvent
import OptimalPrecision.Weights.Gamma
import OptimalPrecision.Weights.Dual
import OptimalPrecision.Weights.Exact
import OptimalPrecision.Weights.LaguerreL2
import OptimalPrecision.Weights.Integral
import OptimalPrecision.Weights.Poisson
import OptimalPrecision.Weights.ChiBound
import OptimalPrecision.Weights.Theorem
import OptimalPrecision.Tail.ExpTail
import OptimalPrecision.Tail.Transfer
import OptimalPrecision.Tail.Jets
import OptimalPrecision.Tail.Joukowski
import OptimalPrecision.Tail.Lemma

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem of the library
(348 theorems) and every field of the structure `OptimalPrecision.Resolvent.Hyp` (8 fields),
beginning with Theorem `opt:thm:weights` and Lemma `opt:lem:tail`, then in module order.
Every report lists `propext`, `Classical.choice` and `Quot.sound`, except for 3 lemmas,
`ExpPoly.lagCoeff_eq_zero`, `ExpPoly.xic_zero` and `ExpPoly.xic_succ`, whose reports list a
strict subset of these three axioms. -/

/-! ### Final theorems: Theorem `opt:thm:weights` and Lemma `opt:lem:tail` -/

/-- info: 'OptimalPrecision.exists_clock_weights' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.exists_clock_weights

/-- info: 'OptimalPrecision.Tail.tail_estimate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.tail_estimate

/-- info: 'OptimalPrecision.clockLength_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.clockLength_le

/-- info: 'OptimalPrecision.sum_abs_clockWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.sum_abs_clockWeight_le

/-- info: 'OptimalPrecision.clock_moments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.clock_moments

/-! ### Taylor coefficients, Cauchy estimates and the Fejér contraction (`Taylor`) -/

/-! #### `OptimalPrecision.Taylor.Basic` -/

/-- info: 'OptimalPrecision.coeff_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_zero_eq

/-- info: 'OptimalPrecision.iteratedDeriv_eq_factorial_smul_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.iteratedDeriv_eq_factorial_smul_coeff

/-- info: 'OptimalPrecision.coeff_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_congr

/-- info: 'OptimalPrecision.ces_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ces_congr

/-- info: 'OptimalPrecision.ces_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ces_zero

/-- info: 'OptimalPrecision.ces_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ces_one

/-- info: 'OptimalPrecision.coeff_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_neg

/-- info: 'OptimalPrecision.coeff_const_smul_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_const_smul_field

/-- info: 'OptimalPrecision.ces_const_smul_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ces_const_smul_field

/-- info: 'OptimalPrecision.coeff_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_deriv

/-- info: 'OptimalPrecision.coeff_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_add

/-- info: 'OptimalPrecision.coeff_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_sub

/-- info: 'OptimalPrecision.coeff_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_sum

/-- info: 'OptimalPrecision.coeff_smul_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_smul_const

/-- info: 'OptimalPrecision.ces_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ces_add

/-- info: 'OptimalPrecision.ces_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ces_sub

/-- info: 'OptimalPrecision.ces_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ces_sum

/-- info: 'OptimalPrecision.ces_smul_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ces_smul_const

/-- info: 'OptimalPrecision.coeff_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_smul

/-- info: 'OptimalPrecision.coeff_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_mul

/-- info: 'OptimalPrecision.coeff_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_pow

/-- info: 'OptimalPrecision.coeff_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_const

/-- info: 'OptimalPrecision.coeff_X_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_X_mul

/-- info: 'OptimalPrecision.coeff_X_mul_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_X_mul_zero

/-! #### `OptimalPrecision.Taylor.Estimates` -/

/-- info: 'OptimalPrecision.norm_coeff_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.norm_coeff_le

/-- info: 'OptimalPrecision.norm_coeff_le_of_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.norm_coeff_le_of_ball

/-- info: 'OptimalPrecision.coeff_eq_zero_of_norm_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_eq_zero_of_norm_le_pow

/-- info: 'OptimalPrecision.hasSum_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.hasSum_coeff

/-! #### `OptimalPrecision.Taylor.Fejer` -/

/-- info: 'OptimalPrecision.rootN_isPrimitiveRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.rootN_isPrimitiveRoot

/-- info: 'OptimalPrecision.norm_rootN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.norm_rootN

/-- info: 'OptimalPrecision.rootN_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.rootN_ne_zero

/-- info: 'OptimalPrecision.sum_rootN_zpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.sum_rootN_zpow

/-- info: 'OptimalPrecision.fejerWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.fejerWeight_nonneg

/-- info: 'OptimalPrecision.fejerWeight_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.fejerWeight_eq

/-- info: 'OptimalPrecision.fejer_coeff_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.fejer_coeff_eq

/-- info: 'OptimalPrecision.fejer_count_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.fejer_count_lt

/-- info: 'OptimalPrecision.fejer_count_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.fejer_count_mid

/-- info: 'OptimalPrecision.norm_fejer_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.norm_fejer_count_le

/-- info: 'OptimalPrecision.cesAt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.cesAt_one

/-- info: 'OptimalPrecision.continuous_cesAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.continuous_cesAt

/-- info: 'OptimalPrecision.norm_cesAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.norm_cesAt_le

/-- info: 'OptimalPrecision.norm_ces_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.norm_ces_le

/-! ### Theorem `opt:thm:weights`: exact moments (`Weights`) -/

/-! #### `OptimalPrecision.Weights.Operator` -/

/-- info: 'OptimalPrecision.ExpPoly.derivPow_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.derivPow_apply

/-- info: 'OptimalPrecision.ExpPoly.derivPow_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.derivPow_eq_zero

/-- info: 'OptimalPrecision.ExpPoly.natDegree_derivPow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.natDegree_derivPow_le

/-- info: 'OptimalPrecision.ExpPoly.derivPow_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.derivPow_add

/-- info: 'OptimalPrecision.ExpPoly.op_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_eq_sum

/-- info: 'OptimalPrecision.ExpPoly.natDegree_op_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.natDegree_op_le

/-- info: 'OptimalPrecision.ExpPoly.op_add_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_add_right

/-- info: 'OptimalPrecision.ExpPoly.op_smul_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_smul_right

/-- info: 'OptimalPrecision.ExpPoly.op_sub_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_sub_right

/-- info: 'OptimalPrecision.ExpPoly.op_sum_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_sum_right

/-- info: 'OptimalPrecision.ExpPoly.op_add_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_add_left

/-- info: 'OptimalPrecision.ExpPoly.op_smul_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_smul_left

/-- info: 'OptimalPrecision.ExpPoly.op_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_one

/-- info: 'OptimalPrecision.ExpPoly.op_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_X

/-- info: 'OptimalPrecision.ExpPoly.op_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_mul

/-- info: 'OptimalPrecision.ExpPoly.op_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_pow

/-- info: 'OptimalPrecision.ExpPoly.op_xs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_xs

/-- info: 'OptimalPrecision.ExpPoly.constantCoeff_xs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.constantCoeff_xs

/-- info: 'OptimalPrecision.ExpPoly.op_inv_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_inv_cancel

/-- info: 'OptimalPrecision.ExpPoly.op_inv_cancel'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_inv_cancel'

/-- info: 'OptimalPrecision.ExpPoly.op_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_injective

/-- info: 'OptimalPrecision.ExpPoly.op_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_map

/-- info: 'OptimalPrecision.ExpPoly.map_inv_powerSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.map_inv_powerSeries

/-- info: 'OptimalPrecision.ExpPoly.map_xs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.map_xs

/-- info: 'OptimalPrecision.ExpPoly.taylor_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.taylor_shifted

/-- info: 'OptimalPrecision.ExpPoly.natDegree_shifted_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.natDegree_shifted_le

/-- info: 'OptimalPrecision.ExpPoly.shifted_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.shifted_map

/-- info: 'OptimalPrecision.ExpPoly.eval_derivPow_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.eval_derivPow_shifted

/-- info: 'OptimalPrecision.ExpPoly.eval_op_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.eval_op_shifted

/-- info: 'OptimalPrecision.ExpPoly.ev_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.ev_add

/-- info: 'OptimalPrecision.ExpPoly.ev_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.ev_sub

/-- info: 'OptimalPrecision.ExpPoly.ev_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.ev_smul

/-- info: 'OptimalPrecision.ExpPoly.ev_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.ev_sum

/-- info: 'OptimalPrecision.ExpPoly.ev_op_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.ev_op_shifted

/-! #### `OptimalPrecision.Weights.Laguerre` -/

/-- info: 'OptimalPrecision.ExpPoly.lagCoeff_eq_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.lagCoeff_eq_zero

/-- info: 'OptimalPrecision.ExpPoly.coeff_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.coeff_lag

/-- info: 'OptimalPrecision.ExpPoly.lag_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.lag_zero

/-- info: 'OptimalPrecision.ExpPoly.eval_zero_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.eval_zero_lag

/-- info: 'OptimalPrecision.ExpPoly.natDegree_lag_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.natDegree_lag_le

/-- info: 'OptimalPrecision.ExpPoly.lagCoeff_self_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.lagCoeff_self_ne_zero

/-- info: 'OptimalPrecision.ExpPoly.natDegree_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.natDegree_lag

/-- info: 'OptimalPrecision.ExpPoly.lag_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.lag_map

/-- info: 'OptimalPrecision.ExpPoly.sum_range_choose_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.sum_range_choose_eq

/-- info: 'OptimalPrecision.ExpPoly.derivative_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.derivative_lag

/-- info: 'OptimalPrecision.ExpPoly.X_mul_derivative_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.X_mul_derivative_lag

/-- info: 'OptimalPrecision.ExpPoly.derivative_lag_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.derivative_lag_succ

/-- info: 'OptimalPrecision.ExpPoly.lag_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.lag_recurrence

/-- info: 'OptimalPrecision.ExpPoly.lag_ode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.lag_ode

/-- info: 'OptimalPrecision.ExpPoly.op_xs_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_xs_lag

/-- info: 'OptimalPrecision.ExpPoly.exists_lag_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.exists_lag_expansion

/-! #### `OptimalPrecision.Weights.Cesaro` -/

/-- info: 'OptimalPrecision.ExpPoly.lagE_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.lagE_zero

/-- info: 'OptimalPrecision.ExpPoly.lagE_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.lagE_succ

/-- info: 'OptimalPrecision.ExpPoly.op_xs_lagE_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_xs_lagE_formula

/-- info: 'OptimalPrecision.ExpPoly.op_xs_lagE_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_xs_lagE_zero

/-- info: 'OptimalPrecision.ExpPoly.xic_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.xic_zero

/-- info: 'OptimalPrecision.ExpPoly.xic_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.xic_succ

/-- info: 'OptimalPrecision.ExpPoly.xiConv_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.xiConv_succ

/-- info: 'OptimalPrecision.ExpPoly.op_xs_lagE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_xs_lagE

/-- info: 'OptimalPrecision.ExpPoly.cesPoly_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.cesPoly_succ

/-- info: 'OptimalPrecision.ExpPoly.lagT_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.lagT_succ

/-- info: 'OptimalPrecision.ExpPoly.op_xs_lag_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_xs_lag_succ

/-- info: 'OptimalPrecision.ExpPoly.op_xs_lag_zero'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_xs_lag_zero'

/-- info: 'OptimalPrecision.ExpPoly.op_xs_lagS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_xs_lagS

/-- info: 'OptimalPrecision.ExpPoly.op_xs_lagR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_xs_lagR

/-- info: 'OptimalPrecision.ExpPoly.op_one_add_xs_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_one_add_xs_lag

/-- info: 'OptimalPrecision.ExpPoly.constantCoeff_xs_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.constantCoeff_xs_sq

/-- info: 'OptimalPrecision.ExpPoly.op_ramp_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.op_ramp_lag

/-- info: 'OptimalPrecision.ExpPoly.sumE_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.sumE_signed

/-- info: 'OptimalPrecision.ExpPoly.cesPoly_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.cesPoly_signed

/-! #### `OptimalPrecision.Weights.Transfer` -/

/-- info: 'OptimalPrecision.one_add_ne_zero_of_norm_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.one_add_ne_zero_of_norm_lt

/-- info: 'OptimalPrecision.analyticAt_xi_of_norm_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.analyticAt_xi_of_norm_lt

/-- info: 'OptimalPrecision.analyticAt_vt_of_norm_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.analyticAt_vt_of_norm_lt

/-- info: 'OptimalPrecision.analyticAt_lagGen_of_norm_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.analyticAt_lagGen_of_norm_lt

/-- info: 'OptimalPrecision.analyticAt_xi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.analyticAt_xi

/-- info: 'OptimalPrecision.analyticAt_vt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.analyticAt_vt

/-- info: 'OptimalPrecision.analyticAt_lagGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.analyticAt_lagGen

/-- info: 'OptimalPrecision.differentiableOn_vt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.differentiableOn_vt

/-- info: 'OptimalPrecision.hasDerivAt_lagGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.hasDerivAt_lagGen

/-- info: 'OptimalPrecision.lagGen_ode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.lagGen_ode

/-- info: 'OptimalPrecision.analyticAt_deriv_lagGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.analyticAt_deriv_lagGen

/-- info: 'OptimalPrecision.lagGenCoeff_rec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.lagGenCoeff_rec

/-- info: 'OptimalPrecision.lagGenCoeff_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.lagGenCoeff_zero

/-- info: 'OptimalPrecision.lagGenCoeff_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.lagGenCoeff_one

/-- info: 'OptimalPrecision.lagGenCoeff_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.lagGenCoeff_two

/-- info: 'OptimalPrecision.lagGenCoeff_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.lagGenCoeff_eq

/-- info: 'OptimalPrecision.coeff_vt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_vt

/-! #### `OptimalPrecision.Weights.Profile` -/

/-- info: 'OptimalPrecision.lamSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.lamSum_eq

/-- info: 'OptimalPrecision.prof_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.prof_add

/-- info: 'OptimalPrecision.prof_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.prof_smul

/-- info: 'OptimalPrecision.lamSum_vt_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.lamSum_vt_mul

/-- info: 'OptimalPrecision.coeff_xi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_xi

/-- info: 'OptimalPrecision.conv_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.conv_assoc

/-- info: 'OptimalPrecision.prof_xi_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.prof_xi_mul

/-- info: 'OptimalPrecision.analyticAt_eval_xi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.analyticAt_eval_xi

/-- info: 'OptimalPrecision.prof_aeval_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.prof_aeval_mul

/-! #### `OptimalPrecision.Weights.Resolvent` -/

/-- info: 'OptimalPrecision.Resolvent.constantCoeff_u' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.constantCoeff_u

/-- info: 'OptimalPrecision.Resolvent.constantCoeff_v' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.constantCoeff_v

/-- info: 'OptimalPrecision.Resolvent.constantCoeff_v'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.constantCoeff_v'

/-- info: 'OptimalPrecision.Resolvent.u_mul_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.u_mul_inv

/-- info: 'OptimalPrecision.Resolvent.v_mul_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.v_mul_inv

/-- info: 'OptimalPrecision.Resolvent.v'_mul_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.v'_mul_inv

/-- info: 'OptimalPrecision.Resolvent.ui_mul_vi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.ui_mul_vi

/-- info: 'OptimalPrecision.Resolvent.ui_mul_wi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.ui_mul_wi

/-- info: 'OptimalPrecision.Resolvent.vi_mul_wi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.vi_mul_wi

/-- info: 'OptimalPrecision.Resolvent.u_mul_vi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.u_mul_vi

/-- info: 'OptimalPrecision.Resolvent.u_mul_wi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.u_mul_wi

/-- info: 'OptimalPrecision.Resolvent.Hyp.c_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.Hyp.c_ne

/-- info: 'OptimalPrecision.Resolvent.Hyp.one_sub_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.Hyp.one_sub_ne

/-- info: 'OptimalPrecision.Resolvent.Hyp.one_add_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.Hyp.one_add_ne

/-- info: 'OptimalPrecision.Resolvent.Hyp.ui_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.Hyp.ui_sq

/-- info: 'OptimalPrecision.Resolvent.Hyp.ui' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.Hyp.ui

/-- info: 'OptimalPrecision.Resolvent.Hyp.u_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.Hyp.u_pow

/-- info: 'OptimalPrecision.Resolvent.Hyp.vi_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.Hyp.vi_pow

/-- info: 'OptimalPrecision.Resolvent.Hyp.wi_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.Hyp.wi_pow

/-- info: 'OptimalPrecision.Resolvent.vanish_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.vanish_zero

/-- info: 'OptimalPrecision.Resolvent.vanish_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.vanish_nonneg

/-- info: 'OptimalPrecision.Resolvent.vanish_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.vanish_neg_one

/-- info: 'OptimalPrecision.Resolvent.value_neg_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Resolvent.value_neg_two

/-! #### `OptimalPrecision.Weights.Gamma` -/

/-- info: 'OptimalPrecision.Gamma.theta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.theta_pos

/-- info: 'OptimalPrecision.Gamma.theta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.theta_le

/-- info: 'OptimalPrecision.Gamma.sin_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.sin_theta

/-- info: 'OptimalPrecision.Gamma.theta_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.theta_ge

/-- info: 'OptimalPrecision.Gamma.alpha_polar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.alpha_polar

/-- info: 'OptimalPrecision.Gamma.norm_alpha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.norm_alpha

/-- info: 'OptimalPrecision.Gamma.rho_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.rho_pos

/-- info: 'OptimalPrecision.Gamma.alpha_pow_polar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.alpha_pow_polar

/-- info: 'OptimalPrecision.Gamma.m0_theta_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.m0_theta_ge

/-- info: 'OptimalPrecision.Gamma.m0_theta_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.m0_theta_lt

/-- info: 'OptimalPrecision.Gamma.mid_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.mid_nonneg

/-- info: 'OptimalPrecision.Gamma.cst_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.cst_nonneg

/-- info: 'OptimalPrecision.Gamma.m0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.m0_pos

/-- info: 'OptimalPrecision.Gamma.norm0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.norm0_pos

/-- info: 'OptimalPrecision.Gamma.coeff_Araw_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.coeff_Araw_nonneg

/-- info: 'OptimalPrecision.Gamma.coeff_Apoly_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.coeff_Apoly_nonneg

/-- info: 'OptimalPrecision.Gamma.eval_one_Apoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.eval_one_Apoly

/-- info: 'OptimalPrecision.Gamma.eval_alpha_Araw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.eval_alpha_Araw

/-- info: 'OptimalPrecision.Gamma.eval_conj_alpha_Araw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.eval_conj_alpha_Araw

/-- info: 'OptimalPrecision.Gamma.ell_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.ell_pos

/-- info: 'OptimalPrecision.Gamma.eval_one_Bpoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.eval_one_Bpoly

/-- info: 'OptimalPrecision.Gamma.eval_one_C1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.eval_one_C1

/-- info: 'OptimalPrecision.Gamma.eval_one_C2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.eval_one_C2

/-- info: 'OptimalPrecision.Gamma.C2_sub_C1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.C2_sub_C1

/-- info: 'OptimalPrecision.Gamma.coeff_C1_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.coeff_C1_of_lt

/-- info: 'OptimalPrecision.Gamma.coeff_C2_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.coeff_C2_of_lt

/-- info: 'OptimalPrecision.Gamma.natDegree_Araw_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.natDegree_Araw_le

/-- info: 'OptimalPrecision.Gamma.natDegree_Apoly_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.natDegree_Apoly_le

/-- info: 'OptimalPrecision.Gamma.natDegree_Bpoly_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.natDegree_Bpoly_le

/-- info: 'OptimalPrecision.Gamma.natDegree_C1_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.natDegree_C1_le

/-- info: 'OptimalPrecision.Gamma.natDegree_C2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.natDegree_C2_le

/-- info: 'OptimalPrecision.Gamma.natDegree_C1_le_Dstar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.natDegree_C1_le_Dstar

/-- info: 'OptimalPrecision.Gamma.dvd_C1_alpha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.dvd_C1_alpha

/-- info: 'OptimalPrecision.Gamma.dvd_C1_conj_alpha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.dvd_C1_conj_alpha

/-- info: 'OptimalPrecision.Gamma.coeff_mul_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.coeff_mul_nonneg

/-- info: 'OptimalPrecision.Gamma.coeff_pow_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.coeff_pow_nonneg

/-- info: 'OptimalPrecision.Gamma.coeff_X_pow_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.coeff_X_pow_nonneg

/-- info: 'OptimalPrecision.Gamma.coeff_geomPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.coeff_geomPoly

/-- info: 'OptimalPrecision.Gamma.coeff_Bpoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.coeff_Bpoly

/-- info: 'OptimalPrecision.Gamma.coeff_Bpoly_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.coeff_Bpoly_nonneg

/-- info: 'OptimalPrecision.Gamma.coeff_mul_geomPoly_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.coeff_mul_geomPoly_le

/-- info: 'OptimalPrecision.Gamma.coeff_C1_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.coeff_C1_nonneg

/-- info: 'OptimalPrecision.Gamma.coeff_C2_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.coeff_C2_nonneg

/-- info: 'OptimalPrecision.Gamma.coeff_C1_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.coeff_C1_le

/-- info: 'OptimalPrecision.Gamma.coeff_C2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.coeff_C2_le

/-- info: 'OptimalPrecision.Gamma.sum_coeff_C1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.sum_coeff_C1

/-- info: 'OptimalPrecision.Gamma.sum_coeff_C2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.sum_coeff_C2

/-- info: 'OptimalPrecision.Gamma.m0_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.m0_le

/-- info: 'OptimalPrecision.Gamma.Dstar_add_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Gamma.Dstar_add_one_le

/-! #### `OptimalPrecision.Weights.Dual` -/

/-- info: 'OptimalPrecision.Dual.pair_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.pair_apply

/-- info: 'OptimalPrecision.Dual.coeff_geom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.coeff_geom

/-- info: 'OptimalPrecision.Dual.pair_geom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.pair_geom

/-- info: 'OptimalPrecision.Dual.v_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.v_zero

/-- info: 'OptimalPrecision.Dual.v_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.v_neg

/-- info: 'OptimalPrecision.Dual.v_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.v_inv

/-- info: 'OptimalPrecision.Dual.v_inv_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.v_inv_pow

/-- info: 'OptimalPrecision.Dual.u_inv_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.u_inv_pow

/-- info: 'OptimalPrecision.Dual.v'_inv_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.v'_inv_pow

/-- info: 'OptimalPrecision.Dual.coeff_u_pow_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.coeff_u_pow_of_lt

/-- info: 'OptimalPrecision.Dual.pair_geom_of_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.pair_geom_of_dvd

/-- info: 'OptimalPrecision.Dual.hyp_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.hyp_of

/-- info: 'OptimalPrecision.Dual.diffC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.diffC_eq

/-- info: 'OptimalPrecision.Dual.natDegree_diffC_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.natDegree_diffC_le

/-- info: 'OptimalPrecision.Dual.coeff_diffC_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.coeff_diffC_of_lt

/-- info: 'OptimalPrecision.Dual.eval_one_diffC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.eval_one_diffC

/-- info: 'OptimalPrecision.Dual.eval_one_derivative_X_mul_diffC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.eval_one_derivative_X_mul_diffC

/-- info: 'OptimalPrecision.Dual.cq_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.cq_ne_zero

/-- info: 'OptimalPrecision.Dual.one_sub_cq_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.one_sub_cq_ne_zero

/-- info: 'OptimalPrecision.Dual.one_add_cq_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.one_add_cq_ne_zero

/-- info: 'OptimalPrecision.Dual.inv_one_sub_cq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.inv_one_sub_cq

/-- info: 'OptimalPrecision.Dual.inv_one_add_cq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.inv_one_add_cq

/-- info: 'OptimalPrecision.Dual.dvd_diffC_alpha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.dvd_diffC_alpha

/-- info: 'OptimalPrecision.Dual.dvd_diffC_conj_alpha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.dvd_diffC_conj_alpha

/-- info: 'OptimalPrecision.Dual.hyp_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Dual.hyp_mixture

/-! #### `OptimalPrecision.Weights.Exact` -/

/-- info: 'OptimalPrecision.coeff_one_fun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_one_fun

/-- info: 'OptimalPrecision.prof_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.prof_one

/-- info: 'OptimalPrecision.prof_one_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.prof_one_eq

/-- info: 'OptimalPrecision.PR_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.PR_map

/-- info: 'OptimalPrecision.natDegree_QR_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.natDegree_QR_le

/-- info: 'OptimalPrecision.beta_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.beta_spec

/-- info: 'OptimalPrecision.beta_spec_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.beta_spec_complex

/-- info: 'OptimalPrecision.xi_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.xi_zero

/-- info: 'OptimalPrecision.one_add_sq_mul_xi_ne_zero_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.one_add_sq_mul_xi_ne_zero_at

/-- info: 'OptimalPrecision.analyticAt_Rfun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.analyticAt_Rfun

/-- info: 'OptimalPrecision.eventually_den_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.eventually_den_ne

/-- info: 'OptimalPrecision.aeval_xs_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.aeval_xs_C

/-- info: 'OptimalPrecision.pair_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.pair_term

/-- info: 'OptimalPrecision.lamSum_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.lamSum_moment

/-! ### Theorem `opt:thm:weights`: the variation bound and the clock length (`Weights`) -/

/-! #### `OptimalPrecision.Weights.LaguerreL2` -/

/-- info: 'OptimalPrecision.ExpPoly.J_monomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.J_monomial

/-- info: 'OptimalPrecision.ExpPoly.J_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.J_C

/-- info: 'OptimalPrecision.ExpPoly.J_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.J_one

/-- info: 'OptimalPrecision.ExpPoly.J_derivative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.J_derivative

/-- info: 'OptimalPrecision.ExpPoly.Lop_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.Lop_apply

/-- info: 'OptimalPrecision.ExpPoly.J_Lop_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.J_Lop_mul

/-- info: 'OptimalPrecision.ExpPoly.J_Lop_mul_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.J_Lop_mul_comm

/-- info: 'OptimalPrecision.ExpPoly.Lop_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.Lop_lag

/-- info: 'OptimalPrecision.ExpPoly.J_lag_mul_lag_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.J_lag_mul_lag_of_ne

/-- info: 'OptimalPrecision.ExpPoly.two_X_mul_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.two_X_mul_lag

/-- info: 'OptimalPrecision.ExpPoly.J_lag_sq_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.J_lag_sq_succ

/-- info: 'OptimalPrecision.ExpPoly.J_lag_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.J_lag_sq

/-- info: 'OptimalPrecision.ExpPoly.J_lag_mul_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.J_lag_mul_lag

/-- info: 'OptimalPrecision.ExpPoly.J_expansion_mul_lag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.J_expansion_mul_lag

/-- info: 'OptimalPrecision.ExpPoly.J_expansion_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.J_expansion_sq

/-- info: 'OptimalPrecision.ExpPoly.sum_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.sum_abs_le

/-! #### `OptimalPrecision.Weights.Integral` -/

/-- info: 'OptimalPrecision.ExpPoly.integrableOn_pow_mul_exp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.integrableOn_pow_mul_exp_neg

/-- info: 'OptimalPrecision.ExpPoly.integral_pow_mul_exp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.integral_pow_mul_exp_neg

/-- info: 'OptimalPrecision.ExpPoly.integrableOn_eval_mul_exp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.integrableOn_eval_mul_exp_neg

/-- info: 'OptimalPrecision.ExpPoly.integral_eval_mul_exp_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.integral_eval_mul_exp_neg

/-- info: 'OptimalPrecision.ExpPoly.J_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.J_eq_sum

/-- info: 'OptimalPrecision.ExpPoly.integral_eval_mul_exp_neg_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.integral_eval_mul_exp_neg_two

/-- info: 'OptimalPrecision.ExpPoly.integral_sq_eq_J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.integral_sq_eq_J

/-- info: 'OptimalPrecision.ExpPoly.integrableOn_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.integrableOn_sq

/-- info: 'OptimalPrecision.ExpPoly.setIntegral_Ioi_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.setIntegral_Ioi_shift

/-! #### `OptimalPrecision.Weights.Poisson` -/

/-- info: 'OptimalPrecision.ExpPoly.eval_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.eval_shifted

/-- info: 'OptimalPrecision.ExpPoly.exp_mul_eval_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.exp_mul_eval_shifted

/-- info: 'OptimalPrecision.ExpPoly.derivative_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.derivative_taylor

/-- info: 'OptimalPrecision.ExpPoly.coeff_sum_C_mul_X_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.coeff_sum_C_mul_X_pow

/-- info: 'OptimalPrecision.ExpPoly.derivative_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.derivative_shifted

/-- info: 'OptimalPrecision.ExpPoly.pk_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.pk_nonneg

/-- info: 'OptimalPrecision.ExpPoly.sum_pk_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.sum_pk_le_one

/-- info: 'OptimalPrecision.ExpPoly.abs_pk_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.abs_pk_le

/-- info: 'OptimalPrecision.ExpPoly.abs_Phi_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.abs_Phi_le

/-- info: 'OptimalPrecision.ExpPoly.Phi_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.Phi_le

/-- info: 'OptimalPrecision.ExpPoly.Phi_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.Phi_sq_le

/-- info: 'OptimalPrecision.ExpPoly.tail_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.tail_le_one

/-- info: 'OptimalPrecision.ExpPoly.abs_Phi_le_of_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.abs_Phi_le_of_nonpos

/-- info: 'OptimalPrecision.ExpPoly.pk_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.pk_eq

/-- info: 'OptimalPrecision.ExpPoly.integrableOn_pk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.integrableOn_pk

/-- info: 'OptimalPrecision.ExpPoly.integral_pk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.integral_pk

/-- info: 'OptimalPrecision.ExpPoly.sq_mul_pk_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.sq_mul_pk_eq

/-- info: 'OptimalPrecision.ExpPoly.integrableOn_sq_mul_pk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.integrableOn_sq_mul_pk

/-- info: 'OptimalPrecision.ExpPoly.integral_sq_mul_pk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.integral_sq_mul_pk

/-- info: 'OptimalPrecision.ExpPoly.integrableOn_Phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.integrableOn_Phi

/-- info: 'OptimalPrecision.ExpPoly.integral_Phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.integral_Phi

/-- info: 'OptimalPrecision.ExpPoly.integrableOn_sq_mul_Phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.integrableOn_sq_mul_Phi

/-- info: 'OptimalPrecision.ExpPoly.integral_sq_mul_Phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.integral_sq_mul_Phi

/-! #### `OptimalPrecision.Weights.ChiBound` -/

/-- info: 'OptimalPrecision.ExpPoly.exp_mul_eval_chi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.exp_mul_eval_chi

/-- info: 'OptimalPrecision.ExpPoly.sum_shift_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.sum_shift_le

/-- info: 'OptimalPrecision.ExpPoly.J_chi_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.ExpPoly.J_chi_le

/-! #### `OptimalPrecision.Weights.Theorem` -/

/-- info: 'OptimalPrecision.Lop_add_self_op' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Lop_add_self_op

/-- info: 'OptimalPrecision.sum_abs_lamOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.sum_abs_lamOf

/-- info: 'OptimalPrecision.J_chi_mixture_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.J_chi_mixture_le

/-! ### Lemma `opt:lem:tail`: the operator tail estimate (`Tail`) -/

/-! #### `OptimalPrecision.Tail.ExpTail` -/

/-- info: 'OptimalPrecision.norm_exp_sub_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.norm_exp_sub_sum_le

/-- info: 'OptimalPrecision.norm_exp_sub_sum_le'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.norm_exp_sub_sum_le'

/-- info: 'OptimalPrecision.exists_norm_le_mul_of_differentiableAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.exists_norm_le_mul_of_differentiableAt

/-- info: 'OptimalPrecision.exists_norm_le_of_continuousAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.exists_norm_le_of_continuousAt

/-- info: 'OptimalPrecision.coeff_smul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_smul_exp

/-! #### `OptimalPrecision.Tail.Transfer` -/

/-- info: 'OptimalPrecision.Tail.re_xi_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.re_xi_pos

/-- info: 'OptimalPrecision.Tail.qxi_sub_I_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.qxi_sub_I_ne_zero

/-- info: 'OptimalPrecision.Tail.qxi_add_I_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.qxi_add_I_ne_zero

/-- info: 'OptimalPrecision.Tail.one_add_sq_xi_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.one_add_sq_xi_ne_zero

/-- info: 'OptimalPrecision.Tail.re_muP_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.re_muP_nonneg

/-- info: 'OptimalPrecision.Tail.re_muM_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.re_muM_nonneg

/-- info: 'OptimalPrecision.Tail.qxi_mul_qxi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.qxi_mul_qxi

/-- info: 'OptimalPrecision.Tail.muP_sub_muM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.muP_sub_muM

/-- info: 'OptimalPrecision.Tail.muP_add_muM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.muP_add_muM

/-- info: 'OptimalPrecision.Tail.Omega_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.Omega_eq

/-- info: 'OptimalPrecision.Tail.re_inner_Omega_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.re_inner_Omega_nonneg

/-- info: 'OptimalPrecision.Tail.norm_Fop_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.norm_Fop_le_one

/-- info: 'OptimalPrecision.Tail.analyticAt_Rfun_of_norm_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.analyticAt_Rfun_of_norm_lt

/-- info: 'OptimalPrecision.Tail.analyticAt_Xop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.analyticAt_Xop

/-- info: 'OptimalPrecision.Tail.analyticAt_Omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.analyticAt_Omega

/-- info: 'OptimalPrecision.Tail.analyticAt_Fop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.analyticAt_Fop

/-- info: 'OptimalPrecision.Tail.differentiableOn_Fop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.differentiableOn_Fop

/-- info: 'OptimalPrecision.Tail.Rfun_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.Rfun_zero

/-- info: 'OptimalPrecision.Tail.Fop_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.Fop_eq

/-! #### `OptimalPrecision.Tail.Jets` -/

/-- info: 'OptimalPrecision.Tail.word_zero_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.word_zero_right

/-- info: 'OptimalPrecision.Tail.word_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.word_eq_zero

/-- info: 'OptimalPrecision.Tail.Xop_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.Xop_pow

/-- info: 'OptimalPrecision.Tail.word_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.word_smul

/-- info: 'OptimalPrecision.Tail.analyticAt_vRx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.analyticAt_vRx

/-- info: 'OptimalPrecision.Tail.differentiableOn_vRx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.differentiableOn_vRx

/-- info: 'OptimalPrecision.Tail.coeff_vRx_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.coeff_vRx_eq_zero

/-- info: 'OptimalPrecision.Tail.ces_vRx_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.ces_vRx_eq_zero

/-- info: 'OptimalPrecision.Tail.coeff_Fop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.coeff_Fop

/-- info: 'OptimalPrecision.Tail.coeff_Fop_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.coeff_Fop_of_lt

/-- info: 'OptimalPrecision.Tail.ces_Fop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.ces_Fop

/-- info: 'OptimalPrecision.Tail.clock_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.clock_smul

/-- info: 'OptimalPrecision.Tail.clockCoeff_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.clockCoeff_eq

/-! #### `OptimalPrecision.Tail.Joukowski` -/

/-- info: 'OptimalPrecision.differentiable_polyEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.differentiable_polyEval

/-- info: 'OptimalPrecision.coeff_polyEval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.coeff_polyEval

/-- info: 'OptimalPrecision.joukowski_radius_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.joukowski_radius_le

/-- info: 'OptimalPrecision.le_joukowski_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.le_joukowski_radius

/-- info: 'OptimalPrecision.norm_polyEval_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.norm_polyEval_le

/-- info: 'OptimalPrecision.norm_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.norm_tail_le

/-! #### `OptimalPrecision.Tail.Lemma` -/

/-- info: 'OptimalPrecision.Tail.norm_le_of_abs_re_inner_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.norm_le_of_abs_re_inner_le

/-- info: 'OptimalPrecision.Tail.re_inner_smul_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.re_inner_smul_one_sub

/-- info: 'OptimalPrecision.Tail.norm_le_of_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.norm_le_of_sandwich

/-- info: 'OptimalPrecision.Tail.scaled_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.scaled_positive

/-- info: 'OptimalPrecision.Tail.pow_div_factorial_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.pow_div_factorial_le

/-- info: 'OptimalPrecision.Tail.tail_estimate_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalPrecision.Tail.tail_estimate_of_pos
