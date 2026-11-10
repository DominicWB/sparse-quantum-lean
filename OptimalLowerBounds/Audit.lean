import OptimalLowerBounds.Access
import OptimalLowerBounds.Optimal
import OptimalLowerBounds.Embedding
import OptimalLowerBounds.Enlarge
import OptimalLowerBounds.TwoNorm
import OptimalLowerBounds.Denominator
import OptimalLowerBounds.AdaptiveAccess
import OptimalLowerBounds.Adaptive
import OptimalLowerBounds.Measured

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (141 theorems) and the 17
fields of the `Prop` structure `TwoNormInstance`, beginning with the main theorems, then in module
order. 156 reports list exactly `propext`, `Classical.choice` and `Quot.sound`; the other 2
(`enlargeTable_bit`, `enlargeTable_value`, definitional) depend on no axiom. -/

/-! ### Final theorems: `hs:eq:optimal-theta`, `hsl:prop:two-norm`, the denominator paragraph,
adaptive and measured forms -/

/-- info: 'OptimalLowerBounds.optimal_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.optimal_theta

/-- info: 'OptimalLowerBounds.not_uniform_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.not_uniform_sqrt

/-- info: 'OptimalLowerBounds.main_max_simulates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.main_max_simulates

/-- info: 'OptimalLowerBounds.two_norm_main_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.two_norm_main_max

/-- info: 'OptimalLowerBounds.two_norm_main_max_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.two_norm_main_max_native

/-- info: 'OptimalLowerBounds.two_norm_main_max_simulates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.two_norm_main_max_simulates

/-- info: 'OptimalLowerBounds.two_norm_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.two_norm_theta

/-- info: 'OptimalLowerBounds.two_instances' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.two_instances

/-- info: 'OptimalLowerBounds.wrong_denominator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.wrong_denominator

/-- info: 'OptimalLowerBounds.wrong_denominator_simulates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.wrong_denominator_simulates

/-- info: 'OptimalLowerBounds.denom_simulates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.denom_simulates

/-- info: 'OptimalLowerBounds.two_norm_main_max_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.two_norm_main_max_tree

/-- info: 'OptimalLowerBounds.two_norm_main_max_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.two_norm_main_max_measured

/-- info: 'OptimalLowerBounds.two_norm_main_max_measured_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.two_norm_main_max_measured_calls

/-- info: 'OptimalLowerBounds.two_norm_main_max_measured_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.two_norm_main_max_measured_common

/-- info: 'OptimalLowerBounds.main_max_measured_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.main_max_measured_common

/-- info: 'OptimalLowerBounds.optimal_measured_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.optimal_measured_theta

/-- info: 'OptimalLowerBounds.two_norm_measured_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.two_norm_measured_theta

/-- info: 'OptimalLowerBounds.wrong_denominator_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.wrong_denominator_tree

/-- info: 'OptimalLowerBounds.wrong_denominator_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.wrong_denominator_measured

/-- info: 'OptimalLowerBounds.wrong_denominator_measured_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.wrong_denominator_measured_common

/-- info: 'OptimalLowerBounds.denom_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.denom_measured

/-! ### Lower bounds for certified families and the common query form (`Access`) -/

/-- info: 'OptimalLowerBounds.time_of_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.time_of_access

/-- info: 'OptimalLowerBounds.mixed_of_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.mixed_of_access

/-- info: 'OptimalLowerBounds.precision_of_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.precision_of_access

/-- info: 'OptimalLowerBounds.main_max_of_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.main_max_of_access

/-- info: 'OptimalLowerBounds.common_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.common_unitary

/-! ### Theorem `hs:thm:optimal`: the `Θ` bracket (`Optimal`) -/

/-- info: 'OptimalLowerBounds.nonneg_of_simulates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.nonneg_of_simulates

/-- info: 'OptimalLowerBounds.simulationCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.simulationCost_le

/-- info: 'OptimalLowerBounds.exists_simulates_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.exists_simulates_lt

/-- info: 'OptimalLowerBounds.simulationCost_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.simulationCost_nonneg

/-- info: 'OptimalLowerBounds.time_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.time_common

/-- info: 'OptimalLowerBounds.mixed_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.mixed_common

/-- info: 'OptimalLowerBounds.precision_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.precision_common

/-- info: 'OptimalLowerBounds.rb_eq_hsR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.rb_eq_hsR

/-- info: 'OptimalLowerBounds.bound_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.bound_eq

/-- info: 'OptimalLowerBounds.optimal_of_hardInstance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.optimal_of_hardInstance

/-- info: 'OptimalLowerBounds.optimal_on_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.optimal_on_hard

/-- info: 'OptimalLowerBounds.le_exp_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.le_exp_self

/-- info: 'OptimalLowerBounds.bound_lt_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.bound_lt_sqrt

/-! ### The uniform ancilla (`Embedding`) -/

/-- info: 'OptimalLowerBounds.regroup_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.regroup_apply

/-- info: 'OptimalLowerBounds.regroup_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.regroup_symm_apply

/-- info: 'OptimalLowerBounds.exp_comp_eq_comp_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.exp_comp_eq_comp_exp

/-- info: 'OptimalLowerBounds.embedU_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.embedU_apply

/-- info: 'OptimalLowerBounds.sqrt_inv_sq_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.sqrt_inv_sq_mul

/-- info: 'OptimalLowerBounds.inner_embedU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.inner_embedU

/-- info: 'OptimalLowerBounds.embedU_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.embedU_isometry

/-- info: 'OptimalLowerBounds.norm_embedU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.norm_embedU

/-- info: 'OptimalLowerBounds.enlargeMatrix_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.enlargeMatrix_apply

/-- info: 'OptimalLowerBounds.matrixOperator_enlarge_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.matrixOperator_enlarge_comp

/-- info: 'OptimalLowerBounds.evolve_enlarge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.evolve_enlarge

/-- info: 'OptimalLowerBounds.norm_enlarge_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.norm_enlarge_ge

/-- info: 'OptimalLowerBounds.liftU_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.liftU_apply

/-- info: 'OptimalLowerBounds.isSelfAdjoint_liftU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.isSelfAdjoint_liftU

/-- info: 'OptimalLowerBounds.norm_liftU_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.norm_liftU_le

/-- info: 'OptimalLowerBounds.liftObs_regroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.liftObs_regroup

/-- info: 'OptimalLowerBounds.liftU_comp_embedU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.liftU_comp_embedU

/-- info: 'OptimalLowerBounds.inner_embedU_liftU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.inner_embedU_liftU

/-- info: 'OptimalLowerBounds.outObs_regroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.outObs_regroup

/-- info: 'OptimalLowerBounds.accurate_of_embedU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.accurate_of_embedU

/-- info: 'OptimalLowerBounds.regroup_comp_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.regroup_comp_isometry

/-! ### The enlarged families (`Enlarge`) -/

/-- info: 'OptimalLowerBounds.enlargeTable_bit' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.enlargeTable_bit

/-- info: 'OptimalLowerBounds.enlargeTable_value' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.enlargeTable_value

/-- info: 'OptimalLowerBounds.enlargeSlot_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.enlargeSlot_apply

/-- info: 'OptimalLowerBounds.mem_range_enlargeLoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.mem_range_enlargeLoc

/-- info: 'OptimalLowerBounds.enlargeData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.enlargeData_matrix

/-- info: 'OptimalLowerBounds.oracles_enlargeData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.oracles_enlargeData

/-- info: 'OptimalLowerBounds.implementsOn_enlargeData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.implementsOn_enlargeData

/-- info: 'OptimalLowerBounds.implementsOn_enlargeData_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.implementsOn_enlargeData_spec

/-- info: 'OptimalLowerBounds.filter_enlarge_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.filter_enlarge_row

/-- info: 'OptimalLowerBounds.filter_enlarge_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.filter_enlarge_col

/-- info: 'OptimalLowerBounds.row_mass_enlarge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.row_mass_enlarge

/-- info: 'OptimalLowerBounds.col_mass_enlarge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.col_mass_enlarge

/-- info: 'OptimalLowerBounds.enlargeData_twoNormInstance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.enlargeData_twoNormInstance

/-- info: 'OptimalLowerBounds.fullMatrix_refOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.fullMatrix_refOne

/-- info: 'OptimalLowerBounds.searchTwo_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.searchTwo_matrix

/-- info: 'OptimalLowerBounds.scalarTwo_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.scalarTwo_matrix

/-- info: 'OptimalLowerBounds.searchHam_refOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.searchHam_refOne

/-- info: 'OptimalLowerBounds.scalarHam_refOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.scalarHam_refOne

/-- info: 'OptimalLowerBounds.searchTwo_twoNormInstance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.searchTwo_twoNormInstance

/-- info: 'OptimalLowerBounds.scalarTwo_twoNormInstance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.scalarTwo_twoNormInstance

/-- info: 'OptimalLowerBounds.two_opNorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.two_opNorm

/-- info: 'OptimalLowerBounds.eta_lt_opNorm_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.eta_lt_opNorm_bound

/-! ### Proposition `hsl:prop:two-norm` (`TwoNorm`) -/

/-- info: 'OptimalLowerBounds.exists_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.exists_coeff

/-- info: 'OptimalLowerBounds.theta_eq_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.theta_eq_abs

/-- info: 'OptimalLowerBounds.two_shape_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.two_shape_eq

/-- info: 'OptimalLowerBounds.accurate_search_of_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.accurate_search_of_two

/-- info: 'OptimalLowerBounds.accurate_scalar_of_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.accurate_scalar_of_two

/-- info: 'OptimalLowerBounds.time_two_of_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.time_two_of_access

/-- info: 'OptimalLowerBounds.mixed_two_of_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.mixed_two_of_access

/-- info: 'OptimalLowerBounds.precision_two_of_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.precision_two_of_access

/-- info: 'OptimalLowerBounds.two_norm_max_of_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.two_norm_max_of_access

/-- info: 'OptimalLowerBounds.norm_embedU_searchInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.norm_embedU_searchInput

/-- info: 'OptimalLowerBounds.norm_embedU_scalarInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.norm_embedU_scalarInput

/-- info: 'OptimalLowerBounds.two_on_aligned_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.two_on_aligned_of

/-- info: 'OptimalLowerBounds.two_on_aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.two_on_aligned

/-- info: 'OptimalLowerBounds.TwoNormInstance.dyadic_entries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.dyadic_entries

/-! ### The logarithmic denominator (`Denominator`) -/

/-- info: 'OptimalLowerBounds.precision_scalar_of_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.precision_scalar_of_access

/-- info: 'OptimalLowerBounds.denomM_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.denomM_pos

/-- info: 'OptimalLowerBounds.denomMu_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.denomMu_pos

/-- info: 'OptimalLowerBounds.four_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.four_pow_eq

/-- info: 'OptimalLowerBounds.log_four_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.log_four_pow

/-- info: 'OptimalLowerBounds.denom_params' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.denom_params

/-- info: 'OptimalLowerBounds.denom_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.denom_instance

/-- info: 'OptimalLowerBounds.denom_L_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.denom_L_ge

/-- info: 'OptimalLowerBounds.denom_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.denom_range

/-- info: 'OptimalLowerBounds.denom_rmu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.denom_rmu

/-- info: 'OptimalLowerBounds.wrong_r_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.wrong_r_bounds

/-- info: 'OptimalLowerBounds.wrongShape_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.wrongShape_le

/-- info: 'OptimalLowerBounds.denom_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.denom_lower

/-- info: 'OptimalLowerBounds.wrong_lt_rmu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.wrong_lt_rmu

/-- info: 'OptimalLowerBounds.wrong_lt_of_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.wrong_lt_of_lower

/-! ### Admissible access: call forms, the common oracle, one-bit entries (`AdaptiveAccess`) -/

/-- info: 'OptimalLowerBounds.formOp_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.formOp_eq_fiber

/-- info: 'OptimalLowerBounds.nativeCall_formBranch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.nativeCall_formBranch

/-- info: 'OptimalLowerBounds.admissible_callFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.admissible_callFamily

/-- info: 'OptimalLowerBounds.isWrap_physWrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.isWrap_physWrap

/-- info: 'OptimalLowerBounds.physOracle_eq_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.physOracle_eq_wrap

/-- info: 'OptimalLowerBounds.common_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.common_normal_form

/-- info: 'OptimalLowerBounds.admissible_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.admissible_common

/-- info: 'OptimalLowerBounds.admissible_common_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.admissible_common_calls

/-- info: 'OptimalLowerBounds.hardAccess_searchTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.hardAccess_searchTwo

/-- info: 'OptimalLowerBounds.hardAccess_scalarTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.hardAccess_scalarTwo

/-- info: 'OptimalLowerBounds.hardAccess_timeTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.hardAccess_timeTwo

/-- info: 'OptimalLowerBounds.hardAccess_mixedTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.hardAccess_mixedTwo

/-- info: 'OptimalLowerBounds.hardAccess_precisionTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.hardAccess_precisionTwo

/-- info: 'OptimalLowerBounds.hardAccess_denomData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.hardAccess_denomData

/-! ### Adaptive protocols (`Adaptive`) -/

/-- info: 'OptimalLowerBounds.densityAccurate_of_embedU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.densityAccurate_of_embedU

/-- info: 'OptimalLowerBounds.densityAccurate_search_of_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.densityAccurate_search_of_two

/-- info: 'OptimalLowerBounds.densityAccurate_scalar_of_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.densityAccurate_scalar_of_two

/-- info: 'OptimalLowerBounds.time_two_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.time_two_tree

/-- info: 'OptimalLowerBounds.mixed_two_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.mixed_two_tree

/-- info: 'OptimalLowerBounds.precision_two_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.precision_two_tree

/-- info: 'OptimalLowerBounds.precision_scalar_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.precision_scalar_tree

/-- info: 'OptimalLowerBounds.denom_lower_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.denom_lower_tree

/-! ### Measured algorithms and non-vacuity (`Measured`) -/

/-- info: 'OptimalLowerBounds.time_two_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.time_two_measured

/-- info: 'OptimalLowerBounds.mixed_two_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.mixed_two_measured

/-- info: 'OptimalLowerBounds.precision_two_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.precision_two_measured

/-- info: 'OptimalLowerBounds.denom_lower_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.denom_lower_measured

/-- info: 'OptimalLowerBounds.measured_of_simulates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.measured_of_simulates

/-- info: 'OptimalLowerBounds.measured_on_aligned_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.measured_on_aligned_of

/-- info: 'OptimalLowerBounds.measured_on_aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.measured_on_aligned

/-! ### Fields of the `Prop` structure `TwoNormInstance` -/

/-- info: 'OptimalLowerBounds.TwoNormInstance.transpose_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.transpose_eq

/-- info: 'OptimalLowerBounds.TwoNormInstance.real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.real

/-- info: 'OptimalLowerBounds.TwoNormInstance.isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.isHermitian

/-- info: 'OptimalLowerBounds.TwoNormInstance.entry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.entry_le

/-- info: 'OptimalLowerBounds.TwoNormInstance.entry_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.entry_attained

/-- info: 'OptimalLowerBounds.TwoNormInstance.row_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.row_norm_le

/-- info: 'OptimalLowerBounds.TwoNormInstance.col_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.col_norm_le

/-- info: 'OptimalLowerBounds.TwoNormInstance.row_norm_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.row_norm_attained

/-- info: 'OptimalLowerBounds.TwoNormInstance.col_norm_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.col_norm_attained

/-- info: 'OptimalLowerBounds.TwoNormInstance.row_sparsity_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.row_sparsity_le

/-- info: 'OptimalLowerBounds.TwoNormInstance.col_sparsity_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.col_sparsity_le

/-- info: 'OptimalLowerBounds.TwoNormInstance.row_sparsity_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.row_sparsity_attained

/-- info: 'OptimalLowerBounds.TwoNormInstance.col_sparsity_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.col_sparsity_attained

/-- info: 'OptimalLowerBounds.TwoNormInstance.scale_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.scale_eq

/-- info: 'OptimalLowerBounds.TwoNormInstance.decode_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.decode_eq

/-- info: 'OptimalLowerBounds.TwoNormInstance.dyadic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.dyadic

/-- info: 'OptimalLowerBounds.TwoNormInstance.locators_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalLowerBounds.TwoNormInstance.locators_const
