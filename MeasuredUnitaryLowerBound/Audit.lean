import MeasuredUnitaryLowerBound.Statements

set_option autoImplicit false

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem and instance of the
library for the unitary `Ω(√N)` lower bound at trace-distance error `1/2` against adaptive
algorithms, measured algorithms and controlled calls, and of its operator-norm form for measured
algorithms (`MeasuredUnitaryLowerBound.OperatorNorm`; 100 declarations), in module order.
Definitions, including the `Prop`-valued notion `OperatorNorm.NormImplements`, are covered
through the theorems that use them. Every report lists `propext`, `Classical.choice` and
`Quot.sound`, except the two on the call forms (`Calls.fintypeCallForm`,
`Calls.card_callForm`), which list only `propext` and `Quot.sound`. -/

/-! ### The adversary sum (`MeasuredUnitaryLowerBound.Global.Sum`) -/

/-- info: 'MeasuredUnitaryLowerBound.Global.adversary_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Global.adversary_total

/-- info: 'MeasuredUnitaryLowerBound.Global.sq_sum_adversary_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Global.sq_sum_adversary_le

/-- info: 'MeasuredUnitaryLowerBound.Global.sum_le_of_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Global.sum_le_of_gaps

/-! ### The kernel-gap count bound (`MeasuredUnitaryLowerBound.Global.Kernel`) -/

/-- info: 'MeasuredUnitaryLowerBound.Global.adversary_deficit_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Global.adversary_deficit_le

/-- info: 'MeasuredUnitaryLowerBound.Global.tree_count_ge_of_kernel_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Global.tree_count_ge_of_kernel_gaps

/-! ### The read-gap count bound (`MeasuredUnitaryLowerBound.Global.Reads`) -/

/-- info: 'MeasuredUnitaryLowerBound.Global.sum_pair_gaps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Global.sum_pair_gaps

/-- info: 'MeasuredUnitaryLowerBound.Global.pair_gap_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Global.pair_gap_eq

/-- info: 'MeasuredUnitaryLowerBound.Global.tree_count_ge_of_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Global.tree_count_ge_of_reads

/-- info: 'MeasuredUnitaryLowerBound.Global.program_count_ge_of_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Global.program_count_ge_of_reads

/-! ### Reading the output register (`MeasuredUnitaryLowerBound.Reading`) -/

/-- info: 'MeasuredUnitaryLowerBound.Reading.liftObs_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Reading.liftObs_add

/-- info: 'MeasuredUnitaryLowerBound.Reading.liftObs_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Reading.liftObs_one

/-- info: 'MeasuredUnitaryLowerBound.Reading.outObs_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Reading.outObs_add

/-- info: 'MeasuredUnitaryLowerBound.Reading.outObs_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Reading.outObs_sum

/-- info: 'MeasuredUnitaryLowerBound.Reading.outObs_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Reading.outObs_sub

/-- info: 'MeasuredUnitaryLowerBound.Reading.outObs_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Reading.outObs_one

/-- info: 'MeasuredUnitaryLowerBound.Reading.sum_pure_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Reading.sum_pure_single

/-- info: 'MeasuredUnitaryLowerBound.Reading.corr_add_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Reading.corr_add_left

/-- info: 'MeasuredUnitaryLowerBound.Reading.corr_sum_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Reading.corr_sum_left

/-- info: 'MeasuredUnitaryLowerBound.Reading.sum_outObs_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Reading.sum_outObs_pure

/-- info: 'MeasuredUnitaryLowerBound.Reading.sum_readProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Reading.sum_readProb

/-- info: 'MeasuredUnitaryLowerBound.Reading.norm_outObs_pure_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Reading.norm_outObs_pure_sub_le

/-- info: 'MeasuredUnitaryLowerBound.Reading.corr_one_successDensity_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Reading.corr_one_successDensity_tree

/-- info: 'MeasuredUnitaryLowerBound.Reading.tree_read_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Reading.tree_read_bound

/-- info: 'MeasuredUnitaryLowerBound.Reading.measured_read_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Reading.measured_read_bound

/-! ### Adaptive algorithms at the endpoint (`MeasuredUnitaryLowerBound.Endpoint.Tree`) -/

/-- info: 'MeasuredUnitaryLowerBound.Adaptive.tree_search_count_ge_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Adaptive.tree_search_count_ge_endpoint

/-- info: 'MeasuredUnitaryLowerBound.Adaptive.implementation_count_ge_tree_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Adaptive.implementation_count_ge_tree_endpoint

/-- info: 'MeasuredUnitaryLowerBound.Adaptive.implementation_count_ge_calls_tree_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Adaptive.implementation_count_ge_calls_tree_endpoint

/-- info: 'MeasuredUnitaryLowerBound.Adaptive.entry_count_ge_tree_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Adaptive.entry_count_ge_tree_endpoint

/-- info: 'MeasuredUnitaryLowerBound.Adaptive.entry_count_ge_calls_tree_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Adaptive.entry_count_ge_calls_tree_endpoint

/-- info: 'MeasuredUnitaryLowerBound.Adaptive.implementation_count_ge_program_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Adaptive.implementation_count_ge_program_endpoint

/-! ### The entry oracles at trace distance `1/2` (`MeasuredUnitaryLowerBound.Endpoint.Entry`) -/

/-- info: 'MeasuredUnitaryLowerBound.Adaptive.sqrt_le_of_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Adaptive.sqrt_le_of_half

/-- info: 'MeasuredUnitaryLowerBound.Adaptive.unheralded_tree_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Adaptive.unheralded_tree_half

/-- info: 'MeasuredUnitaryLowerBound.Adaptive.heralded_tree_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Adaptive.heralded_tree_half

/-- info: 'MeasuredUnitaryLowerBound.Adaptive.unheralded_calls_tree_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Adaptive.unheralded_calls_tree_half

/-- info: 'MeasuredUnitaryLowerBound.Adaptive.heralded_calls_tree_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Adaptive.heralded_calls_tree_half

/-- info: 'MeasuredUnitaryLowerBound.Adaptive.unheralded_tree_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Adaptive.unheralded_tree_sqrt

/-- info: 'MeasuredUnitaryLowerBound.Adaptive.heralded_tree_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Adaptive.heralded_tree_sqrt

/-- info: 'MeasuredUnitaryLowerBound.Adaptive.unheralded_calls_tree_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Adaptive.unheralded_calls_tree_sqrt

/-- info: 'MeasuredUnitaryLowerBound.Adaptive.heralded_calls_tree_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Adaptive.heralded_calls_tree_sqrt

/-! ### Measured algorithms at the endpoint (`MeasuredUnitaryLowerBound.Endpoint.Measured`) -/

/-- info: 'MeasuredUnitaryLowerBound.Deferred.norm_sel_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Deferred.norm_sel_sub_le

/-- info: 'MeasuredUnitaryLowerBound.Deferred.search_count_ge_measured_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Deferred.search_count_ge_measured_endpoint

/-- info: 'MeasuredUnitaryLowerBound.Deferred.implementation_count_ge_measured_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Deferred.implementation_count_ge_measured_endpoint

/-- info: 'MeasuredUnitaryLowerBound.Deferred.entry_count_ge_measured_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Deferred.entry_count_ge_measured_endpoint

/-- info: 'MeasuredUnitaryLowerBound.Deferred.implementation_count_ge_measured_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Deferred.implementation_count_ge_measured_half

/-- info: 'MeasuredUnitaryLowerBound.Deferred.implementation_count_ge_measured_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Deferred.implementation_count_ge_measured_sqrt

/-! ### Measured algorithms over the call forms (`MeasuredUnitaryLowerBound.Endpoint.Calls`) -/

/-- info: 'MeasuredUnitaryLowerBound.Calls.fintypeCallForm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Calls.fintypeCallForm

/-- info: 'MeasuredUnitaryLowerBound.Calls.card_callForm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Calls.card_callForm

/-- info: 'MeasuredUnitaryLowerBound.Calls.implementsOn_ctrlTarget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Calls.implementsOn_ctrlTarget

/-- info: 'MeasuredUnitaryLowerBound.Calls.search_count_ge_measured_calls_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Calls.search_count_ge_measured_calls_endpoint

/-- info: 'MeasuredUnitaryLowerBound.Calls.implementation_count_ge_measured_calls_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Calls.implementation_count_ge_measured_calls_endpoint

/-- info: 'MeasuredUnitaryLowerBound.Calls.implementation_count_ge_measured_calls_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Calls.implementation_count_ge_measured_calls_half

/-- info: 'MeasuredUnitaryLowerBound.Calls.implementation_count_ge_measured_calls_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.Calls.implementation_count_ge_measured_calls_sqrt

/-! ### Non-vacuity (`MeasuredUnitaryLowerBound.NonVacuity`) -/

/-- info: 'MeasuredUnitaryLowerBound.NonVacuity.densityAccurate_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.NonVacuity.densityAccurate_mono

/-- info: 'MeasuredUnitaryLowerBound.NonVacuity.released_tree_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.NonVacuity.released_tree_half

/-- info: 'MeasuredUnitaryLowerBound.NonVacuity.released_calls_tree_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.NonVacuity.released_calls_tree_half

/-- info: 'MeasuredUnitaryLowerBound.NonVacuity.released_measured_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.NonVacuity.released_measured_half

/-- info: 'MeasuredUnitaryLowerBound.NonVacuity.released_measured_calls_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.NonVacuity.released_measured_calls_half

/-! ### From operator-norm error to trace distance, sharply (`MeasuredUnitaryLowerBound.OperatorNorm.Sharp`) -/

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.re_inner_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.re_inner_sub_eq

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.norm_add_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.norm_add_sq_le

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.mul_sqrt_four_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.mul_sqrt_four_sub_le

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.abs_re_inner_sub_le_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.abs_re_inner_sub_le_sharp

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.accurate_of_endpoint_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.accurate_of_endpoint_sharp

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.sharp_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.sharp_nonneg

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.sharp_le_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.sharp_le_self

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.sharp_le_of_le_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.sharp_le_of_le_half

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.sharp_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.sharp_half

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.sqrt_fifteen_div_eight_lt_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.sqrt_fifteen_div_eight_lt_half

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.sharp_lt_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.sharp_lt_half

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.sub_two_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.sub_two_sq_le

/-! ### Operator-norm implementation of a unitary by a measured algorithm (`MeasuredUnitaryLowerBound.OperatorNorm.Notion`) -/

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.readKraus_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.readKraus_apply

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.garbageTensor_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.garbageTensor_apply

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.norm_readKraus_apply_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.norm_readKraus_apply_sq

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.norm_garbageTensor_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.norm_garbageTensor_apply

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.NormImplements.nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.NormImplements.nonneg

/-! ### Operator-norm implementations are sharply trace-distance accurate (`MeasuredUnitaryLowerBound.OperatorNorm.Accuracy`) -/

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.inner_tensor_liftObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.inner_tensor_liftObs

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.corr_outObs_sum_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.corr_outObs_sum_pure

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.inner_garbageTensor_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.inner_garbageTensor_lift

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.fiber_liftObs_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.fiber_liftObs_selfAdjoint

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.densityAccurate_of_normImplements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.densityAccurate_of_normImplements

/-! ### Unitary programs implement within operator norm (`MeasuredUnitaryLowerBound.OperatorNorm.Programs`) -/

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.adjoint_one_comp_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.adjoint_one_comp_one

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.successDensity_runAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.successDensity_runAll

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.successMass_runAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.successMass_runAll

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.worstCost_runAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.worstCost_runAll

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.normImplements_runAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.normImplements_runAll

/-! ### The operator-norm notion through the deferred unitary (`MeasuredUnitaryLowerBound.OperatorNorm.Deferred`) -/

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.deferredMap_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.deferredMap_apply

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.successMass_eq_norm_deferredMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.successMass_eq_norm_deferredMap

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.normImplements_of_deferred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.normImplements_of_deferred

/-! ### The operator-norm `Ω(√N)` bound for measured algorithms (`MeasuredUnitaryLowerBound.OperatorNorm.Bound`) -/

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.search_accurate_of_normImplements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.search_accurate_of_normImplements

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_measured_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_measured_norm

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.entry_count_ge_measured_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.entry_count_ge_measured_norm

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_measured_norm_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_measured_norm_half

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_measured_norm_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_measured_norm_sqrt

/-! ### The operator-norm bound over controlled and controlled-inverse entry calls (`MeasuredUnitaryLowerBound.OperatorNorm.CallsBound`) -/

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_measured_calls_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_measured_calls_norm

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_measured_calls_norm_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_measured_calls_norm_half

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_measured_calls_norm_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_measured_calls_norm_sqrt

/-! ### Unitary programs: the operator-norm bounds through containment (`MeasuredUnitaryLowerBound.OperatorNorm.ProgramBound`) -/

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_program_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_program_norm

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.global_of_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.global_of_pairwise

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_calls_program_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.implementation_count_ge_calls_program_norm

/-! ### Non-vacuity of the measured operator-norm bounds (`MeasuredUnitaryLowerBound.OperatorNorm.NonVacuity`) -/

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.released_measured_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.released_measured_norm

/-- info: 'MeasuredUnitaryLowerBound.OperatorNorm.released_measured_calls_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms MeasuredUnitaryLowerBound.OperatorNorm.released_measured_calls_norm
