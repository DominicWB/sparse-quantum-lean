import ChebyshevLinearSystemFinite.Alloc
import ChebyshevLinearSystemFinite.CentredAveraging

set_option autoImplicit false

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. The audits cover every theorem of the
library of Theorem `qls:thm:main` with approximate known gates and the explicit
constants of Remark `qls:rem:constants`, beginning with the endpoints `main_amp`,
`main`, `main_uniform`, `main_uniform_sharp`, `main_alloc`, `main_exact`, `main_improved`
and `main_improved_exists`; the theorems of `CentredAveraging` (Remark `qls:rem:averaging` and
the query comparison) are in their own section at the end. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except six arithmetic lemmas of `CentredAveraging`
(`lowHalf_add_highHalf`, `lowHalf_le_highHalf`, `highHalf_le_succ_lowHalf`,
`highHalf_eq_of_even`, `highHalf_eq_of_odd`, `halves_zero`), whose reports list a strict subset.
-/

/-! ### Theorem `qls:thm:main` with approximate known gates -/

/-- info: 'ChebyshevLinearSystemFinite.main_amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.main_amp

/-- info: 'ChebyshevLinearSystemFinite.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.main

/-- info: 'ChebyshevLinearSystemFinite.main_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.main_uniform

/-- info: 'ChebyshevLinearSystemFinite.main_uniform_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.main_uniform_sharp

/-- info: 'ChebyshevLinearSystemFinite.main_alloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.main_alloc

/-- info: 'ChebyshevLinearSystemFinite.main_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.main_exact

/-- info: 'ChebyshevLinearSystemFinite.main_improved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.main_improved

/-- info: 'ChebyshevLinearSystemFinite.main_improved_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.main_improved_exists

/-- info: 'ChebyshevLinearSystemFinite.allocRun_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.allocRun_approx

/-- info: 'ChebyshevLinearSystemFinite.one_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.one_isometry

/-- info: 'ChebyshevLinearSystemFinite.outJ_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.outJ_isometry

/-- info: 'ChebyshevLinearSystemFinite.allocTest_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.allocTest_approx

/-- info: 'ChebyshevLinearSystemFinite.allocFinal_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.allocFinal_approx

/-- info: 'ChebyshevLinearSystemFinite.alloc_test_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.alloc_test_arith

/-- info: 'ChebyshevLinearSystemFinite.alloc_final_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.alloc_final_arith

/-! ### Correctness with approximate known gates -/

/-- info: 'ChebyshevLinearSystemFinite.testRunF_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.testRunF_bounds

/-- info: 'ChebyshevLinearSystemFinite.impl_test_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.impl_test_bounds

/-- info: 'ChebyshevLinearSystemFinite.impl_bernoulli' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.impl_bernoulli

/-- info: 'ChebyshevLinearSystemFinite.impl_final_amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.impl_final_amp

/-- info: 'ChebyshevLinearSystemFinite.impl_final_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.impl_final_good

/-- info: 'ChebyshevLinearSystemFinite.impl_correctness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.impl_correctness

/-! ### Remark `qls:rem:constants` and the query counts -/

/-- info: 'ChebyshevLinearSystemFinite.log_two_hundred_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.log_two_hundred_lt

/-- info: 'ChebyshevLinearSystemFinite.arcosh_hundred_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.arcosh_hundred_lt

/-- info: 'ChebyshevLinearSystemFinite.div_sqrt_le_arsinh_chi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.div_sqrt_le_arsinh_chi

/-- info: 'ChebyshevLinearSystemFinite.finDegree_hundred_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.finDegree_hundred_le

/-- info: 'ChebyshevLinearSystemFinite.testconstant_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.testconstant_lt

/-- info: 'ChebyshevLinearSystemFinite.finDegree_hundred_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.finDegree_hundred_lt

/-- info: 'ChebyshevLinearSystemFinite.cosh_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.cosh_pow_le

/-- info: 'ChebyshevLinearSystemFinite.arcosh_le_kStages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.arcosh_le_kStages

/-- info: 'ChebyshevLinearSystemFinite.one_le_kStages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.one_le_kStages

/-- info: 'ChebyshevLinearSystemFinite.finDegree_le_kStages' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.finDegree_le_kStages

/-- info: 'ChebyshevLinearSystemFinite.qAv_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.qAv_ge

/-- info: 'ChebyshevLinearSystemFinite.averaging_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.averaging_ratio

/-- info: 'ChebyshevLinearSystemFinite.averaging_ratio_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.averaging_ratio_final

/-- info: 'ChebyshevLinearSystemFinite.dTestF_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.dTestF_lt

/-- info: 'ChebyshevLinearSystemFinite.kStages_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.kStages_le

/-- info: 'ChebyshevLinearSystemFinite.dFinF_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.dFinF_le

/-- info: 'ChebyshevLinearSystemFinite.reps_le_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.reps_le_sharp

/-- info: 'ChebyshevLinearSystemFinite.two_pow_stageOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.two_pow_stageOf_le

/-- info: 'ChebyshevLinearSystemFinite.eTest_ge_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.eTest_ge_uniform

/-- info: 'ChebyshevLinearSystemFinite.eTest_ge_uniform_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.eTest_ge_uniform_sharp

/-- info: 'ChebyshevLinearSystemFinite.walkStepsF_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.walkStepsF_le

/-- info: 'ChebyshevLinearSystemFinite.walkStepsC_le_walkStepsF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.walkStepsC_le_walkStepsF

/-- info: 'ChebyshevLinearSystemFinite.impl_worstCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.impl_worstCost

/-- info: 'ChebyshevLinearSystemFinite.impl_matrix_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.impl_matrix_queries

/-- info: 'ChebyshevLinearSystemFinite.impl_source_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.impl_source_queries

/-- info: 'ChebyshevLinearSystemFinite.algorithm_matrix_queries_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.algorithm_matrix_queries_sharp

/-- info: 'ChebyshevLinearSystemFinite.algorithm_source_queries_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.algorithm_source_queries_sharp

/-! ### The finite-degree protocol -/

/-- info: 'ChebyshevLinearSystemFinite.resid_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.resid_eq

/-- info: 'ChebyshevLinearSystemFinite.resid_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.resid_pos

/-- info: 'ChebyshevLinearSystemFinite.chi_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.chi_pos

/-- info: 'ChebyshevLinearSystemFinite.arsinh_chi_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.arsinh_chi_pos

/-- info: 'ChebyshevLinearSystemFinite.resid_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.resid_lt_one

/-- info: 'ChebyshevLinearSystemFinite.augDegree_resid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.augDegree_resid

/-- info: 'ChebyshevLinearSystemFinite.cosh_two_arsinh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.cosh_two_arsinh

/-- info: 'ChebyshevLinearSystemFinite.resid_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.resid_succ_le

/-- info: 'ChebyshevLinearSystemFinite.resid_succ_le_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.resid_succ_le_sharp

/-- info: 'ChebyshevLinearSystemFinite.resid_augDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.resid_augDegree_le

/-- info: 'ChebyshevLinearSystemFinite.delta0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.delta0_pos

/-- info: 'ChebyshevLinearSystemFinite.delta0_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.delta0_le

/-- info: 'ChebyshevLinearSystemFinite.delta0_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.delta0_lt

/-- info: 'ChebyshevLinearSystemFinite.delta0_le_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.delta0_le_sharp

/-- info: 'ChebyshevLinearSystemFinite.dTestF_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.dTestF_eq

/-- info: 'ChebyshevLinearSystemFinite.dFinF_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.dFinF_eq

/-- info: 'ChebyshevLinearSystemFinite.testF_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.testF_fits

/-- info: 'ChebyshevLinearSystemFinite.finalF_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.finalF_fits

/-- info: 'ChebyshevLinearSystemFinite.chi_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.chi_sq

/-- info: 'ChebyshevLinearSystemFinite.eTest_ge_chi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.eTest_ge_chi

/-- info: 'ChebyshevLinearSystemFinite.eTest_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.eTest_ge

/-- info: 'ChebyshevLinearSystemFinite.eTest_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.eTest_pos

/-- info: 'ChebyshevLinearSystemFinite.eTest_ge_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.eTest_ge_sharp

/-- info: 'ChebyshevLinearSystemFinite.eFin_ge_chi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.eFin_ge_chi

/-- info: 'ChebyshevLinearSystemFinite.eFin_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.eFin_ge

/-- info: 'ChebyshevLinearSystemFinite.eFin_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.eFin_pos

/-- info: 'ChebyshevLinearSystemFinite.eFin_ge_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.eFin_ge_sharp

/-- info: 'ChebyshevLinearSystemFinite.filter_proj_deg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.filter_proj_deg

/-- info: 'ChebyshevLinearSystemFinite.test_fact_deg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.test_fact_deg

/-- info: 'ChebyshevLinearSystemFinite.final_fact_deg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.final_fact_deg

/-- info: 'ChebyshevLinearSystemFinite.testRunF_amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.testRunF_amp

/-- info: 'ChebyshevLinearSystemFinite.finalRunF_amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.finalRunF_amp

/-- info: 'ChebyshevLinearSystemFinite.testRunF_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.testRunF_cost

/-- info: 'ChebyshevLinearSystemFinite.finalRunF_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.finalRunF_cost

/-! ### The estimator with the two-sided test tolerance -/

/-- info: 'ChebyshevLinearSystemFinite.reject_inv_tol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.reject_inv_tol

/-- info: 'ChebyshevLinearSystemFinite.last_accepts_tol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.last_accepts_tol

/-- info: 'ChebyshevLinearSystemFinite.candidates_le_tol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.candidates_le_tol

/-- info: 'ChebyshevLinearSystemFinite.stages_le_tol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.stages_le_tol

/-- info: 'ChebyshevLinearSystemFinite.algorithm_bad_le_tol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.algorithm_bad_le_tol

/-! ### Programs and runs with approximate known gates -/

/-- info: 'ChebyshevLinearSystemFinite.GateApprox.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.GateApprox.refl

/-- info: 'ChebyshevLinearSystemFinite.GateApprox.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.GateApprox.mono

/-- info: 'ChebyshevLinearSystemFinite.GateApprox.cost_of_count_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.GateApprox.cost_of_count_zero

/-- info: 'ChebyshevLinearSystemFinite.GateApprox.cost_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.GateApprox.cost_eq

/-- info: 'ChebyshevLinearSystemFinite.GateApprox.count_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.GateApprox.count_eq

/-- info: 'ChebyshevLinearSystemFinite.GateApprox.adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.GateApprox.adjoint

/-- info: 'ChebyshevLinearSystemFinite.GateApprox.eval_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.GateApprox.eval_sub_le

/-- info: 'ChebyshevLinearSystemFinite.GateApprox.eval_apply_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.GateApprox.eval_apply_sub_le

/-- info: 'ChebyshevLinearSystemFinite.GateApprox.nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.GateApprox.nonneg

/-- info: 'ChebyshevLinearSystemFinite.GateApprox.compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.GateApprox.compile

/-- info: 'ChebyshevLinearSystemFinite.probability_eq_amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.probability_eq_amp

/-- info: 'ChebyshevLinearSystemFinite.amp_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.amp_norm_le

/-- info: 'ChebyshevLinearSystemFinite.probability_sub_le_of_amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.probability_sub_le_of_amp

/-- info: 'ChebyshevLinearSystemFinite.RunApprox.refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.RunApprox.refl

/-- info: 'ChebyshevLinearSystemFinite.RunApprox.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.RunApprox.mono

/-- info: 'ChebyshevLinearSystemFinite.RunApprox.cost_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.RunApprox.cost_eq

/-- info: 'ChebyshevLinearSystemFinite.RunApprox.amp_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.RunApprox.amp_sub_le

/-- info: 'ChebyshevLinearSystemFinite.RunApprox.probability_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.RunApprox.probability_sub_le

/-- info: 'ChebyshevLinearSystemFinite.AmpApprox.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.AmpApprox.mono

/-- info: 'ChebyshevLinearSystemFinite.AmpApprox.cost_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.AmpApprox.cost_eq

/-- info: 'ChebyshevLinearSystemFinite.AmpApprox.amp_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.AmpApprox.amp_sub_le

/-- info: 'ChebyshevLinearSystemFinite.AmpApprox.probability_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.AmpApprox.probability_sub_le

/-- info: 'ChebyshevLinearSystemFinite.RunApprox.ampApprox' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.RunApprox.ampApprox

/-- info: 'ChebyshevLinearSystemFinite.repeatLeaf_successMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.repeatLeaf_successMass

/-- info: 'ChebyshevLinearSystemFinite.repeatLeaf_leafDir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.repeatLeaf_leafDir

/-- info: 'ChebyshevLinearSystemFinite.repeatLeaf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.repeatLeaf_spec

/-- info: 'ChebyshevLinearSystemFinite.repeatLeaf_worstCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.repeatLeaf_worstCost

/-! ### Centred averaging (Remark `qls:rem:averaging`) and the query comparison (`CentredAveraging`) -/

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.lowHalf_add_highHalf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.lowHalf_add_highHalf

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.lowHalf_le_highHalf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.lowHalf_le_highHalf

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.highHalf_le_succ_lowHalf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.highHalf_le_succ_lowHalf

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.highHalf_eq_of_even' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.highHalf_eq_of_even

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.highHalf_eq_of_odd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.highHalf_eq_of_odd

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.halves_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.halves_zero

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.highHalf_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.highHalf_bounds

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.Icc_low_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.Icc_low_sub

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.adjoint_pow_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.adjoint_pow_mul_pow

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.wpow_neg_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.wpow_neg_mul_pow

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.isometry_of_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.isometry_of_isUnitary

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.coisometry_of_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.coisometry_of_isUnitary

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.norm_pow_apply_of_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.norm_pow_apply_of_isometry

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.norm_wpow_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.norm_wpow_apply

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.wpow_neg_mul_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.wpow_neg_mul_of_fixed

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centred_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centred_sub_eq

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.norm_centred_sub_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.norm_centred_sub_apply

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.norm_centred_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.norm_centred_apply

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.opNorm_centred_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.opNorm_centred_sub

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.mul_fixedProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.mul_fixedProj

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centred_filter_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centred_filter_error

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.polyOp_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.polyOp_eq_sum

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.polyOp_avg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.polyOp_avg

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centCoeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centCoeff_nonneg

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centCoeff_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centCoeff_eq_zero

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centCoeff_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centCoeff_shift

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centCoeff_neg_highHalf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centCoeff_neg_highHalf

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.sum_centred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.sum_centred

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.sum_centCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.sum_centCoeff

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centred_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centred_sum

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.sum_centCoeff_powT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.sum_centCoeff_powT

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centSeedT_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centSeedT_isometry

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centSeedT_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centSeedT_norm

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centT_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centT_compression

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centSeedVec_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centSeedVec_norm

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centFlag_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centFlag_isometry

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centred_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centred_block

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centred_block_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centred_block_adjoint

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centred_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centred_run

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centred_test_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centred_test_amplitude

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centred_run_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centred_run_zero

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centred_averaging_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centred_averaging_run

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.qAv_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.qAv_eq

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.nAv_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.nAv_pos

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.one_le_sqrt_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.one_le_sqrt_of_pos

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.test_ratio_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.test_ratio_nat

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.final_ratio_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.final_ratio_nat

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.walkSteps_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.walkSteps_ratio

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centred_test_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centred_test_ratio

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.centred_final_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.centred_final_ratio

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.budget_query_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.budget_query_comparison

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.step_costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.step_costs

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.test_query_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.test_query_comparison

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.final_query_comparison' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.final_query_comparison

/-- info: 'ChebyshevLinearSystemFinite.CentredAveraging.averaging_schedules' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystemFinite.CentredAveraging.averaging_schedules
