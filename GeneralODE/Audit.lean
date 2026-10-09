import GeneralODE.Theorem
import GeneralODE.Complexity

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 6 slot-index lemmas, whose
reports list a subset of these three axioms.
The audits cover every theorem of the general ODE library, beginning with
the main theorem. The library uses the block-input linear-system solver
only through the hypothesis `SparseHamiltonian.GeneralODE.Solver.BlockSolver`.
-/

/-! ### Main theorem and closed-form query bound -/

/-- info: 'SparseHamiltonian.GeneralODE.general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.general

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.general_query_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.general_query_bound

/-- info: 'SparseHamiltonian.GeneralODE.exists_protocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.exists_protocol

/-- info: 'SparseHamiltonian.GeneralODE.solution_zero_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.solution_zero_zero

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.two_pow_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.two_pow_le_exp

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.log_le_of_le_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.log_le_of_le_two_pow

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.half_le_log_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.half_le_log_two

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.pow_clog_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.pow_clog_lt

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.ratio_ge_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.ratio_ge_two

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.log_ratio_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.log_ratio_nonneg

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.one_le_logFactor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.one_le_logFactor

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.steps_le_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.steps_le_add

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.steps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.steps_le

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.ratio_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.ratio_le

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.one_le_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.one_le_ratio

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.degree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.degree_le

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.log_delta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.log_delta_le

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.kappa_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.kappa_le

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.nativeLog_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.nativeLog_le

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.nativeLog_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.nativeLog_nonneg

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.shape_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.shape_le

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.matrixBudget_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.matrixBudget_le

/-- info: 'SparseHamiltonian.GeneralODE.Complexity.sourceBudget_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Complexity.sourceBudget_le

/-! ### The protocol for a fixed block-encoding program -/

/-- info: 'SparseHamiltonian.GeneralODE.Solver.one_le_seven_kappaH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.one_le_seven_kappaH

/-- info: 'SparseHamiltonian.GeneralODE.Solver.exists_protocol_of_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.exists_protocol_of_block

/-! ### Damping, randomized amplification and four attempts -/

/-- info: 'SparseHamiltonian.GeneralODE.Amplify.norm_tiltVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Amplify.norm_tiltVec

/-- info: 'SparseHamiltonian.GeneralODE.Amplify.norm_single_bool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Amplify.norm_single_bool

/-- info: 'SparseHamiltonian.GeneralODE.Amplify.damper_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Amplify.damper_spec

/-- info: 'SparseHamiltonian.GeneralODE.Amplify.diag_branchState' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Amplify.diag_branchState

/-- info: 'SparseHamiltonian.GeneralODE.Amplify.true_tilt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Amplify.true_tilt

/-- info: 'SparseHamiltonian.GeneralODE.Amplify.liftOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Amplify.liftOracle_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Amplify.damped_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Amplify.damped_eval

/-- info: 'SparseHamiltonian.GeneralODE.Amplify.damped_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Amplify.damped_cost

/-- info: 'SparseHamiltonian.GeneralODE.Amplify.seedD_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Amplify.seedD_norm

/-- info: 'SparseHamiltonian.GeneralODE.Amplify.outF_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Amplify.outF_isometry

/-- info: 'SparseHamiltonian.GeneralODE.Amplify.damped_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Amplify.damped_decoded

/-- info: 'SparseHamiltonian.GeneralODE.Amplify.protocol_worstCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Amplify.protocol_worstCost

/-- info: 'SparseHamiltonian.GeneralODE.Amplify.outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Amplify.outcome

/-! ### The history system on one instance -/

/-- info: 'SparseHamiltonian.GeneralODE.Solver.uniformSlots_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.uniformSlots_norm

/-- info: 'SparseHamiltonian.GeneralODE.Solver.slotSource_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.slotSource_spec

/-- info: 'SparseHamiltonian.GeneralODE.Solver.restIn_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.restIn_seven

/-- info: 'SparseHamiltonian.GeneralODE.Solver.restOut_seven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.restOut_seven

/-- info: 'SparseHamiltonian.GeneralODE.Solver.block_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.block_eq

/-- info: 'SparseHamiltonian.GeneralODE.Solver.system' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.system

/-! ### Compilation to the native oracles -/

/-- info: 'SparseHamiltonian.GeneralODE.Solver.MultiOracleCircuit.Program.cost_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.MultiOracleCircuit.Program.cost_zero

/-- info: 'SparseHamiltonian.GeneralODE.Solver.totalOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.totalOracle_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Solver.refSlot_ne_slot0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.refSlot_ne_slot0

/-- info: 'SparseHamiltonian.GeneralODE.Solver.refSlot_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.refSlot_ne_none

/-- info: 'SparseHamiltonian.GeneralODE.Solver.totalOracle_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.totalOracle_valid

/-- info: 'SparseHamiltonian.GeneralODE.Solver.uProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.uProgram_eval

/-- info: 'SparseHamiltonian.GeneralODE.Solver.bProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.bProgram_eval

/-- info: 'SparseHamiltonian.GeneralODE.Solver.solverInput_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.solverInput_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Solver.composed_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.composed_eval

/-- info: 'SparseHamiltonian.GeneralODE.Solver.composed_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.composed_matrix_cost

/-- info: 'SparseHamiltonian.GeneralODE.Solver.composed_source_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.composed_source_cost

/-! ### Exact preparation of the right-hand side -/

/-- info: 'SparseHamiltonian.GeneralODE.Solver.slot0_ne_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.slot0_ne_none

/-- info: 'SparseHamiltonian.GeneralODE.Solver.slotControlled_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.slotControlled_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Solver.slotControlled_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.slotControlled_apply

/-- info: 'SparseHamiltonian.GeneralODE.Solver.sourceOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.sourceOracle_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Solver.sourceOracle_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.sourceOracle_single

/-- info: 'SparseHamiltonian.GeneralODE.Solver.slotWeights_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.slotWeights_apply

/-- info: 'SparseHamiltonian.GeneralODE.Solver.slotWeights_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.slotWeights_norm

/-- info: 'SparseHamiltonian.GeneralODE.Solver.slotRotation_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.slotRotation_spec

/-- info: 'SparseHamiltonian.GeneralODE.Solver.rotationGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.rotationGate_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Solver.prepProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.prepProgram_count

/-- info: 'SparseHamiltonian.GeneralODE.Solver.prepProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.prepProgram_cost

/-- info: 'SparseHamiltonian.GeneralODE.Solver.sourceSeed_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.sourceSeed_norm

/-- info: 'SparseHamiltonian.GeneralODE.Solver.rhsVector_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.rhsVector_apply

/-- info: 'SparseHamiltonian.GeneralODE.Solver.norm_rhsVector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.norm_rhsVector

/-- info: 'SparseHamiltonian.GeneralODE.Solver.prepProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.prepProgram_eval

/-! ### The block-input solver interface -/

/-- info: 'SparseHamiltonian.MultiOracleCircuit.Program.eval_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MultiOracleCircuit.Program.eval_reindex

/-- info: 'SparseHamiltonian.MultiOracleCircuit.Program.count_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MultiOracleCircuit.Program.count_reindex

/-- info: 'SparseHamiltonian.MultiOracleCircuit.Program.cost_reindex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MultiOracleCircuit.Program.cost_reindex

/-- info: 'SparseHamiltonian.MultiOracleCircuit.Program.cost_le_count_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MultiOracleCircuit.Program.cost_le_count_mul

/-- info: 'SparseHamiltonian.GeneralODE.Solver.solverOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.solverOracle_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Solver.norm_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.norm_initial

/-- info: 'SparseHamiltonian.GeneralODE.Solver.embed_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Solver.embed_isometry

/-! ### Public parameters -/

/-- info: 'SparseHamiltonian.GeneralODE.Plan.one_le_sqrt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.one_le_sqrt_two

/-- info: 'SparseHamiltonian.GeneralODE.Plan.alpha_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.alpha_pos

/-- info: 'SparseHamiltonian.GeneralODE.Plan.steps_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.steps_pos

/-- info: 'SparseHamiltonian.GeneralODE.Plan.alpha_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.alpha_mul_le

/-- info: 'SparseHamiltonian.GeneralODE.Plan.eight_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.eight_mul_le

/-- info: 'SparseHamiltonian.GeneralODE.Plan.budget_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.budget_pos

/-- info: 'SparseHamiltonian.GeneralODE.Plan.budget_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.budget_mul

/-- info: 'SparseHamiltonian.GeneralODE.Plan.budget_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.budget_le

/-- info: 'SparseHamiltonian.GeneralODE.Plan.steps_half_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.steps_half_pow_le

/-- info: 'SparseHamiltonian.GeneralODE.Plan.nativeError_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.nativeError_pos

/-- info: 'SparseHamiltonian.GeneralODE.Plan.nativeError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.nativeError_le

/-- info: 'SparseHamiltonian.GeneralODE.Plan.budget_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.budget_identity

/-- info: 'SparseHamiltonian.GeneralODE.Plan.budget_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.budget_matrix

/-- info: 'SparseHamiltonian.GeneralODE.Plan.budget_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.budget_taylor

/-- info: 'SparseHamiltonian.GeneralODE.Plan.one_le_kappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.one_le_kappa

/-- info: 'SparseHamiltonian.GeneralODE.Plan.delta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.delta_pos

/-- info: 'SparseHamiltonian.GeneralODE.Plan.delta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.delta_le

/-- info: 'SparseHamiltonian.GeneralODE.Plan.theta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.theta_pos

/-- info: 'SparseHamiltonian.GeneralODE.Plan.delta_lt_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.delta_lt_theta

/-- info: 'SparseHamiltonian.GeneralODE.Plan.one_le_gain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.one_le_gain

/-- info: 'SparseHamiltonian.GeneralODE.Plan.amplitude_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.amplitude_bound

/-- info: 'SparseHamiltonian.GeneralODE.Plan.direction_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Plan.direction_bound

/-! ### Lemma ode:lem:block: arcsine series, LCU and native block encoding -/

/-- info: 'SparseHamiltonian.GeneralODE.Arcsine.series_zero_eq_arcsin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Arcsine.series_zero_eq_arcsin

/-- info: 'SparseHamiltonian.GeneralODE.Arcsine.correction_sin_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Arcsine.correction_sin_sub_le

/-- info: 'SparseHamiltonian.GeneralODE.Arcsine.sin_ofReal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Arcsine.sin_ofReal_eq

/-- info: 'SparseHamiltonian.GeneralODE.Arcsine.sin_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Arcsine.sin_pow_eq

/-- info: 'SparseHamiltonian.GeneralODE.Arcsine.correction_sin_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Arcsine.correction_sin_eq

/-- info: 'SparseHamiltonian.GeneralODE.Arcsine.norm_lcuCoef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Arcsine.norm_lcuCoef

/-- info: 'SparseHamiltonian.GeneralODE.Arcsine.sum_norm_lcuCoef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Arcsine.sum_norm_lcuCoef

/-- info: 'SparseHamiltonian.GeneralODE.Arcsine.sum_coefficient_zero_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Arcsine.sum_coefficient_zero_le_two

/-- info: 'SparseHamiltonian.GeneralODE.Arcsine.coefficient_zero_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Arcsine.coefficient_zero_nonneg

/-- info: 'SparseHamiltonian.GeneralODE.Spectral.exp_apply_of_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Spectral.exp_apply_of_eigen

/-- info: 'SparseHamiltonian.GeneralODE.Spectral.norm_le_of_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Spectral.norm_le_of_diagonal

/-- info: 'SparseHamiltonian.GeneralODE.Spectral.lcu_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Spectral.lcu_approx

/-- info: 'SparseHamiltonian.GeneralODE.LCU.lcu_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.LCU.lcu_pair

/-- info: 'SparseHamiltonian.GeneralODE.LCU.norm_sq_lcuIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.LCU.norm_sq_lcuIn

/-- info: 'SparseHamiltonian.GeneralODE.LCU.norm_sq_lcuOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.LCU.norm_sq_lcuOut

/-- info: 'SparseHamiltonian.GeneralODE.LCU.norm_lcuIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.LCU.norm_lcuIn

/-- info: 'SparseHamiltonian.GeneralODE.LCU.norm_lcuOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.LCU.norm_lcuOut

/-- info: 'SparseHamiltonian.GeneralODE.LCU.branchState_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.LCU.branchState_apply

/-- info: 'SparseHamiltonian.GeneralODE.LCU.branchCostate_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.LCU.branchCostate_apply

/-- info: 'SparseHamiltonian.GeneralODE.LCU.branchState_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.LCU.branchState_adjoint

/-- info: 'SparseHamiltonian.GeneralODE.LCU.branchState_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.LCU.branchState_isometry

/-- info: 'SparseHamiltonian.GeneralODE.LCU.branch_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.LCU.branch_block

/-- info: 'SparseHamiltonian.GeneralODE.NativeMatrix.neg_eq_lchs_combination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeMatrix.neg_eq_lchs_combination

/-- info: 'SparseHamiltonian.GeneralODE.NativeMatrix.neg_matrixOperator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeMatrix.neg_matrixOperator_eq

/-- info: 'SparseHamiltonian.GeneralODE.NativeMatrix.norm_dissipativePart_op_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeMatrix.norm_dissipativePart_op_le

/-- info: 'SparseHamiltonian.GeneralODE.NativeMatrix.norm_hamiltonianPart_op_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeMatrix.norm_hamiltonianPart_op_le

/-- info: 'SparseHamiltonian.GeneralODE.NativeMatrix.norm_lchs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeMatrix.norm_lchs_le

/-- info: 'SparseHamiltonian.GeneralODE.NativeMatrix.column_energy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeMatrix.column_energy_le

/-- info: 'SparseHamiltonian.GeneralODE.NativeMatrix.row_energy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeMatrix.row_energy_le

/-- info: 'SparseHamiltonian.GeneralODE.NativeMatrix.hamiltonian_energy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeMatrix.hamiltonian_energy_le

/-- info: 'SparseHamiltonian.GeneralODE.NativeMatrix.dissipative_energy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeMatrix.dissipative_energy_le

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.abs_kTab_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.abs_kTab_le

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.abs_freq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.abs_freq_le

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.abs_sTab_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.abs_sTab_le

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.norm_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.norm_weight

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.mass_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.mass_nonneg

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.mass_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.mass_le_one

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.pad_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.pad_nonneg

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.sum_fin_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.sum_fin_prod

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.sum_norm_coef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.sum_norm_coef

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.Kop_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.Kop_star

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.Xop_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.Xop_selfAdjoint

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.norm_Xop_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.norm_Xop_le

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.branchEvolution_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.branchEvolution_inl

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.branchEvolution_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.branchEvolution_inr

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.lcu_block_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.lcu_block_approx

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.uPlus_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.uPlus_nonneg

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.uMinus_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.uMinus_nonneg

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.uPlus_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.uPlus_le

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.uMinus_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.uMinus_le

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.uPlus_sub_uMinus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.uPlus_sub_uMinus

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.exp_adjoint_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.exp_adjoint_mul

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.evolution_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.evolution_unitary

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.signed_evolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.signed_evolution

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.signed_program_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.signed_program_error

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.flatOracle_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.flatOracle_valid

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.flatOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.flatOracle_unitary

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.layout_compress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.layout_compress

/-- info: 'SparseHamiltonian.GeneralODE.NativeBlock.exists_native_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.NativeBlock.exists_native_block

/-! ### Block encodings: registers, products, standard forms, programs -/

/-- info: 'SparseHamiltonian.GeneralODE.Registers.isUnitary_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.isUnitary_map

/-- info: 'SparseHamiltonian.GeneralODE.Registers.diagHom_apply_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.diagHom_apply_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.specHom_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.specHom_eq

/-- info: 'SparseHamiltonian.GeneralODE.Registers.spectator_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.spectator_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.permutationUnitary_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.permutationUnitary_symm_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.onFactor_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.onFactor_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.onFactor_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.onFactor_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Registers.onFactor_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.onFactor_single

/-- info: 'SparseHamiltonian.GeneralODE.Registers.ketR_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.ketR_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.braR_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.braR_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.ketR_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.ketR_adjoint

/-- info: 'SparseHamiltonian.GeneralODE.Registers.braR_ketR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.braR_ketR

/-- info: 'SparseHamiltonian.GeneralODE.Registers.ketR_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.ketR_isometry

/-- info: 'SparseHamiltonian.GeneralODE.Registers.norm_le_one_of_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.norm_le_one_of_isometry

/-- info: 'SparseHamiltonian.GeneralODE.Registers.norm_unitary_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.norm_unitary_le

/-- info: 'SparseHamiltonian.GeneralODE.Registers.norm_blk_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.norm_blk_le

/-- info: 'SparseHamiltonian.GeneralODE.Registers.slice_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.slice_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.slice_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.slice_add

/-- info: 'SparseHamiltonian.GeneralODE.Registers.slice_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.slice_smul

/-- info: 'SparseHamiltonian.GeneralODE.Registers.inner_eq_sum_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.inner_eq_sum_slice

/-- info: 'SparseHamiltonian.GeneralODE.Registers.selMap_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.selMap_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.slice_selMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.slice_selMap

/-- info: 'SparseHamiltonian.GeneralODE.Registers.selMap_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.selMap_adjoint

/-- info: 'SparseHamiltonian.GeneralODE.Registers.selMap_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.selMap_comp

/-- info: 'SparseHamiltonian.GeneralODE.Registers.selMap_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.selMap_one

/-- info: 'SparseHamiltonian.GeneralODE.Registers.selMap_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.selMap_isometry

/-- info: 'SparseHamiltonian.GeneralODE.Registers.specHom_comp_selMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.specHom_comp_selMap

/-- info: 'SparseHamiltonian.GeneralODE.Registers.selMap_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.selMap_block

/-- info: 'SparseHamiltonian.GeneralODE.Registers.selMap_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.selMap_const

/-- info: 'SparseHamiltonian.GeneralODE.Registers.actLeft_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.actLeft_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.actLeft_ketR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.actLeft_ketR

/-- info: 'SparseHamiltonian.GeneralODE.Registers.braR_actLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.braR_actLeft

/-- info: 'SparseHamiltonian.GeneralODE.Registers.single_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.single_pair

/-- info: 'SparseHamiltonian.GeneralODE.Registers.blk_one_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.blk_one_unit

/-- info: 'SparseHamiltonian.GeneralODE.Registers.blk_powOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.blk_powOp

/-- info: 'SparseHamiltonian.GeneralODE.Registers.powOp_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.powOp_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Registers.ordProd_selMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.ordProd_selMap

/-- info: 'SparseHamiltonian.GeneralODE.Registers.powOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.powOracle_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Registers.powProg_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.powProg_eval

/-- info: 'SparseHamiltonian.GeneralODE.Registers.powProg_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.powProg_count

/-- info: 'SparseHamiltonian.GeneralODE.Registers.powProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.powProg_cost

/-- info: 'SparseHamiltonian.GeneralODE.Registers.powOracle_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.powOracle_single

/-- info: 'SparseHamiltonian.GeneralODE.Registers.exists_unitary_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.exists_unitary_comp

/-- info: 'SparseHamiltonian.GeneralODE.Registers.one_comp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.one_comp_eq

/-- info: 'SparseHamiltonian.GeneralODE.Registers.ketL_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.ketL_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.braL_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.braL_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.ketL_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.ketL_adjoint

/-- info: 'SparseHamiltonian.GeneralODE.Registers.spectator_ketL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.spectator_ketL

/-- info: 'SparseHamiltonian.GeneralODE.Registers.ketL_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.ketL_isometry

/-- info: 'SparseHamiltonian.GeneralODE.Registers.standardize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.standardize

/-- info: 'SparseHamiltonian.GeneralODE.Registers.load_ketR_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.load_ketR_isometry

/-- info: 'SparseHamiltonian.GeneralODE.Registers.load_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.load_isometry

/-- info: 'SparseHamiltonian.GeneralODE.Registers.standardLoad_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.standardLoad_spec

/-- info: 'SparseHamiltonian.GeneralODE.Registers.standardForm_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.standardForm_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Registers.blk_standardForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.blk_standardForm

/-- info: 'SparseHamiltonian.GeneralODE.Registers.tens_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.tens_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.norm_tens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.norm_tens

/-- info: 'SparseHamiltonian.GeneralODE.Registers.blk_mul_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.blk_mul_fresh

/-- info: 'SparseHamiltonian.MultiOracleCircuit.Program.eval_mapHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MultiOracleCircuit.Program.eval_mapHom

/-- info: 'SparseHamiltonian.MultiOracleCircuit.Program.count_mapHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MultiOracleCircuit.Program.count_mapHom

/-- info: 'SparseHamiltonian.MultiOracleCircuit.Program.cost_mapHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MultiOracleCircuit.Program.cost_mapHom

/-! ### The history unitary and its program -/

/-- info: 'SparseHamiltonian.GeneralODE.Registers.apply_eq_sum_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.apply_eq_sum_entry

/-- info: 'SparseHamiltonian.GeneralODE.Registers.sum_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.sum_term

/-- info: 'SparseHamiltonian.GeneralODE.Registers.coefMap_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.coefMap_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.coefAdj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.coefAdj_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.coefMap_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.coefMap_adjoint

/-- info: 'SparseHamiltonian.GeneralODE.Registers.coefMap_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.coefMap_isometry

/-- info: 'SparseHamiltonian.GeneralODE.Registers.liftSlot_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.liftSlot_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.block_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.block_formula

/-- info: 'SparseHamiltonian.GeneralODE.Registers.slotShift_symm_some' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.slotShift_symm_some

/-- info: 'SparseHamiltonian.GeneralODE.Registers.slotShift_symm_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.slotShift_symm_none

/-- info: 'SparseHamiltonian.GeneralODE.Registers.slotShift_symm_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.slotShift_symm_zero

/-- info: 'SparseHamiltonian.GeneralODE.Registers.sum_fin_ite_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.sum_fin_ite_zero

/-- info: 'SparseHamiltonian.GeneralODE.Registers.sum_fin_eq_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.sum_fin_eq_range

/-- info: 'SparseHamiltonian.GeneralODE.Registers.norm_sq_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.norm_sq_state

/-- info: 'SparseHamiltonian.GeneralODE.Registers.sum_sq_ite_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.sum_sq_ite_zero

/-- info: 'SparseHamiltonian.GeneralODE.Registers.sum_sq_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.sum_sq_sqrt_div

/-- info: 'SparseHamiltonian.GeneralODE.Registers.sum_sq_neg_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.sum_sq_neg_sqrt_div

/-- info: 'SparseHamiltonian.GeneralODE.Registers.stateIn_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.stateIn_norm

/-- info: 'SparseHamiltonian.GeneralODE.Registers.stateOut_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.stateOut_norm

/-- info: 'SparseHamiltonian.GeneralODE.Registers.entry_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.entry_one

/-- info: 'SparseHamiltonian.GeneralODE.Registers.entry_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.entry_perm

/-- info: 'SparseHamiltonian.GeneralODE.Registers.termSum_junkIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.termSum_junkIn

/-- info: 'SparseHamiltonian.GeneralODE.Registers.termSum_junkOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.termSum_junkOut

/-- info: 'SparseHamiltonian.GeneralODE.Registers.termSum_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.termSum_id

/-- info: 'SparseHamiltonian.GeneralODE.Registers.tslot_of_lt' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.tslot_of_lt

/-- info: 'SparseHamiltonian.GeneralODE.Registers.sum_entry_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.sum_entry_perm

/-- info: 'SparseHamiltonian.GeneralODE.Registers.termSum_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.termSum_step

/-- info: 'SparseHamiltonian.GeneralODE.Registers.termSum_step_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.termSum_step_none

/-- info: 'SparseHamiltonian.GeneralODE.Registers.termSum_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.termSum_src

/-- info: 'SparseHamiltonian.GeneralODE.Registers.stepPoly_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.stepPoly_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.block_eq_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.block_eq_residual

/-- info: 'SparseHamiltonian.GeneralODE.Registers.adjoint_comp_self_of_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.adjoint_comp_self_of_isUnitary

/-- info: 'SparseHamiltonian.GeneralODE.Registers.comp_adjoint_self_of_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.comp_adjoint_self_of_isUnitary

/-- info: 'SparseHamiltonian.GeneralODE.Registers.selMap_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.selMap_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Registers.isometry_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.isometry_comp

/-- info: 'SparseHamiltonian.GeneralODE.Registers.lineMap_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.lineMap_apply

/-- info: 'SparseHamiltonian.GeneralODE.Registers.lineMap_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.lineMap_isometry

/-- info: 'SparseHamiltonian.GeneralODE.Registers.exists_unitary_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.exists_unitary_single

/-- info: 'SparseHamiltonian.GeneralODE.Registers.ordProd_threshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.ordProd_threshold

/-- info: 'SparseHamiltonian.GeneralODE.Registers.facEnc_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.facEnc_isometry

/-- info: 'SparseHamiltonian.GeneralODE.Registers.factor_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.factor_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Registers.blk_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.blk_factor

/-- info: 'SparseHamiltonian.GeneralODE.Registers.powCircuit_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.powCircuit_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Registers.blk_powCircuit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.blk_powCircuit

/-- info: 'SparseHamiltonian.GeneralODE.Registers.histEnc_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.histEnc_isometry

/-- info: 'SparseHamiltonian.GeneralODE.Registers.slotUnitaries_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.slotUnitaries_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Registers.histCore_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.histCore_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Registers.histCore_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.histCore_block

/-- info: 'SparseHamiltonian.GeneralODE.Registers.HistData.inEnc_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.HistData.inEnc_isometry

/-- info: 'SparseHamiltonian.GeneralODE.Registers.HistData.outEnc_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.HistData.outEnc_isometry

/-- info: 'SparseHamiltonian.GeneralODE.Registers.HistData.unitary_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.HistData.unitary_isUnitary

/-- info: 'SparseHamiltonian.GeneralODE.Registers.HistData.block_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.HistData.block_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Registers.facProg_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.facProg_eval

/-- info: 'SparseHamiltonian.GeneralODE.Registers.facProg_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.facProg_count

/-- info: 'SparseHamiltonian.GeneralODE.Registers.facProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.facProg_cost

/-- info: 'SparseHamiltonian.GeneralODE.Registers.slotPart_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.slotPart_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Registers.powProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.powProgram_eval

/-- info: 'SparseHamiltonian.GeneralODE.Registers.histProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.histProgram_eval

/-- info: 'SparseHamiltonian.GeneralODE.Registers.histProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.histProgram_count

/-- info: 'SparseHamiltonian.GeneralODE.Registers.histProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.histProgram_cost

/-- info: 'SparseHamiltonian.GeneralODE.Registers.histOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.histOracle_unitary

/-- info: 'SparseHamiltonian.GeneralODE.Registers.histOracle_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Registers.histOracle_valid

/-! ### Analysis of the history system -/

/-- info: 'SparseHamiltonian.GeneralODE.Runs.add_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Runs.add_pow_eq

/-- info: 'SparseHamiltonian.GeneralODE.Runs.norm_add_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Runs.norm_add_pow_le

/-- info: 'SparseHamiltonian.GeneralODE.Runs.norm_add_pow_le_of_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Runs.norm_add_pow_le_of_exp

/-- info: 'SparseHamiltonian.GeneralODE.ExpBounds.norm_pow_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ExpBounds.norm_pow_le_pow

/-- info: 'SparseHamiltonian.GeneralODE.ExpBounds.factorial_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ExpBounds.factorial_mul_le

/-- info: 'SparseHamiltonian.GeneralODE.ExpBounds.real_exp_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ExpBounds.real_exp_hasSum

/-- info: 'SparseHamiltonian.GeneralODE.ExpBounds.norm_exp_sub_taylorExp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ExpBounds.norm_exp_sub_taylorExp_le

/-- info: 'SparseHamiltonian.GeneralODE.ExpBounds.norm_exp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ExpBounds.norm_exp_le

/-- info: 'SparseHamiltonian.GeneralODE.ExpBounds.norm_exp_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ExpBounds.norm_exp_sub_one_le

/-- info: 'SparseHamiltonian.GeneralODE.ExpBounds.norm_pow_sub_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ExpBounds.norm_pow_sub_pow_le

/-- info: 'SparseHamiltonian.GeneralODE.ExpBounds.norm_taylorExp_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ExpBounds.norm_taylorExp_sub_le

/-- info: 'SparseHamiltonian.GeneralODE.ExpBounds.solution_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ExpBounds.solution_add

/-- info: 'SparseHamiltonian.GeneralODE.ExpBounds.integral_taylorExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ExpBounds.integral_taylorExp

/-- info: 'SparseHamiltonian.GeneralODE.ExpBounds.norm_response_sub_phiTaylor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ExpBounds.norm_response_sub_phiTaylor_le

/-- info: 'SparseHamiltonian.GeneralODE.ExpBounds.norm_response_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ExpBounds.norm_response_ge

/-- info: 'SparseHamiltonian.GeneralODE.Recursion.unroll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Recursion.unroll

/-- info: 'SparseHamiltonian.GeneralODE.Recursion.norm_le_of_unroll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Recursion.norm_le_of_unroll

/-- info: 'SparseHamiltonian.GeneralODE.Recursion.norm_sub_le_of_recursions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Recursion.norm_sub_le_of_recursions

/-- info: 'SparseHamiltonian.GeneralODE.Recursion.unroll_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Recursion.unroll_le

/-- info: 'SparseHamiltonian.GeneralODE.Recursion.norm_le_of_unroll_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Recursion.norm_le_of_unroll_le

/-- info: 'SparseHamiltonian.GeneralODE.Recursion.norm_sub_le_of_recursions_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Recursion.norm_sub_le_of_recursions_le

/-- info: 'SparseHamiltonian.GeneralODE.History.seq_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.seq_some

/-- info: 'SparseHamiltonian.GeneralODE.History.seq_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.seq_of_lt

/-- info: 'SparseHamiltonian.GeneralODE.History.residual_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.residual_none

/-- info: 'SparseHamiltonian.GeneralODE.History.residual_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.residual_some

/-- info: 'SparseHamiltonian.GeneralODE.History.residual_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.residual_sub

/-- info: 'SparseHamiltonian.GeneralODE.History.norm_coord_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.norm_coord_le

/-- info: 'SparseHamiltonian.GeneralODE.History.norm_seq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.norm_seq_le

/-- info: 'SparseHamiltonian.GeneralODE.History.norm_sq_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.norm_sq_eq

/-- info: 'SparseHamiltonian.GeneralODE.History.sum_norm_seq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.sum_norm_seq_le

/-- info: 'SparseHamiltonian.GeneralODE.History.coupling_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.coupling_norm

/-- info: 'SparseHamiltonian.GeneralODE.History.seq_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.seq_step

/-- info: 'SparseHamiltonian.GeneralODE.History.seq_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.seq_copy

/-- info: 'SparseHamiltonian.GeneralODE.History.seq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.seq_zero

/-- info: 'SparseHamiltonian.GeneralODE.History.none_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.none_eq

/-- info: 'SparseHamiltonian.GeneralODE.History.norm_le_kappaH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.norm_le_kappaH

/-- info: 'SparseHamiltonian.GeneralODE.History.seq_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.seq_solution

/-- info: 'SparseHamiltonian.GeneralODE.History.solution_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.solution_none

/-- info: 'SparseHamiltonian.GeneralODE.History.residual_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.residual_solution

/-- info: 'SparseHamiltonian.GeneralODE.History.solution_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.solution_copy

/-- info: 'SparseHamiltonian.GeneralODE.History.norm_sq_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.norm_sq_solution

/-- info: 'SparseHamiltonian.GeneralODE.History.samples_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.samples_succ

/-- info: 'SparseHamiltonian.GeneralODE.History.samples_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.samples_zero

/-- info: 'SparseHamiltonian.GeneralODE.History.exp_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.exp_pow

/-- info: 'SparseHamiltonian.GeneralODE.History.exp_eighth_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.exp_eighth_lt

/-- info: 'SparseHamiltonian.GeneralODE.History.forcing_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.forcing_le

/-- info: 'SparseHamiltonian.GeneralODE.History.exp_half_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.exp_half_lt

/-- info: 'SparseHamiltonian.GeneralODE.History.step_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.step_pow_le

/-- info: 'SparseHamiltonian.GeneralODE.History.trajectory_accuracy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.History.trajectory_accuracy

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.taylorCoef_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.taylorCoef_nonneg

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.phiCoef_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.phiCoef_nonneg

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.phiCoef_le_taylorCoef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.phiCoef_le_taylorCoef

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.sum_taylorCoef_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.sum_taylorCoef_le

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.sum_phiCoef_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.sum_phiCoef_le

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.norm_smul_sub_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.norm_smul_sub_smul

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.norm_pow_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.norm_pow_le_one

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.norm_pow_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.norm_pow_sub_one_le

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.norm_powers_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.norm_powers_le

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.norm_powers_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.norm_powers_sub_le

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.powers_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.powers_zero

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.norm_poly_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.norm_poly_sub_le

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.norm_poly_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.norm_poly_le

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.exists_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.exists_inverse

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.norm_sum_pow_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.norm_sum_pow_sub_le

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.taylorCoef_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.taylorCoef_scale

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.phiCoef_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.phiCoef_scale

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.implemented_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.implemented_bounds

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.stepSource_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.stepSource_eq

/-- info: 'SparseHamiltonian.GeneralODE.Implemented.history_accuracy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Implemented.history_accuracy

/-- info: 'SparseHamiltonian.GeneralODE.Decode.unitDirection_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Decode.unitDirection_smul

/-- info: 'SparseHamiltonian.GeneralODE.Decode.unitDirection_real_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Decode.unitDirection_real_smul

/-- info: 'SparseHamiltonian.GeneralODE.Decode.norm_adjoint_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Decode.norm_adjoint_le_one

/-- info: 'SparseHamiltonian.GeneralODE.Decode.decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Decode.decode

/-- info: 'SparseHamiltonian.GeneralODE.Decode.sum_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Decode.sum_final

/-- info: 'SparseHamiltonian.GeneralODE.Decode.finalSlots_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Decode.finalSlots_norm

/-- info: 'SparseHamiltonian.GeneralODE.Decode.decoder_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Decode.decoder_isometry

/-- info: 'SparseHamiltonian.GeneralODE.Decode.decoder_adjoint_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.Decode.decoder_adjoint_solution
