import RepresentedSampleODE.Repair
import RepresentedSampleODE.Family
import RepresentedSampleODE.Target
import RepresentedSampleODE.Theorem
import RepresentedSampleODE.Zero
import RepresentedSampleODE.Actual
import RepresentedSampleODE.Approx
import RepresentedSampleODE.Integral
import RepresentedSampleODE.Duhamel
import RepresentedSampleODE.Regular
import RepresentedSampleODE.Gate.Certificate
import RepresentedSampleODE.Gate.Native
import RepresentedSampleODE.Gate.Binary

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (93 theorems), beginning
with the main theorems, then in module order. Every report lists exactly `propext`,
`Classical.choice` and `Quot.sound`. -/

/-! ### Final theorems: the time-dependent dissipative ODE solvers on a mesh and the time-dependent
gate solver with represented samples of any sign, on a mesh also for integrable pieces and mild
solutions, the negativity bounds, Duhamel's formula for bounded pieces, the branch and target
errors and the positive repair -/

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_approx_solver_nonneg_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_approx_solver_nonneg_regular

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_approx_solver_nonneg_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_approx_solver_nonneg_path

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_approx_solver_nonneg_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_approx_solver_nonneg_integral

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_solver_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_solver_integral

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_approx_solver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_approx_solver_nonneg

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_mesh_solver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_mesh_solver_nonneg

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_mesh_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_mesh_solver

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_propagated_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_propagated_solver

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_zero_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_zero_core

/-- info: 'SparseHamiltonian.RepresentedSampleODE.mesh_zero_time_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.mesh_zero_time_core

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robustBudget_of_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robustBudget_of_path

/-- info: 'SparseHamiltonian.RepresentedSampleODE.pathNegativity_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.pathNegativity_bound

/-- info: 'SparseHamiltonian.RepresentedSampleODE.negativity_pathNegativity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.negativity_pathNegativity

/-- info: 'SparseHamiltonian.RepresentedSampleODE.dissipativeError_le_sampleError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.dissipativeError_le_sampleError

/-- info: 'SparseHamiltonian.RepresentedSampleODE.tableFamily_sub_robustFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.tableFamily_sub_robustFamily

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_target_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_target_error

/-- info: 'SparseHamiltonian.RepresentedSampleODE.repair_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.repair_nonneg

/-- info: 'SparseHamiltonian.RepresentedSampleODE.norm_repair_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.norm_repair_le

/-- info: 'SparseHamiltonian.RepresentedSampleODE.norm_repair_sub_le_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.norm_repair_sub_le_min

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.robust_binary_time_outcome_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.robust_binary_time_outcome_nonneg

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.robust_binary_time_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.robust_binary_time_outcome

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.robust_native_time_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.robust_native_time_outcome

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.robust_prep_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.robust_prep_certificate

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.robust_target_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.robust_target_facts

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.negativity_of_sample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.negativity_of_sample

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.RobustRest.of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.RobustRest.of_rest

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.RobustRest.toRest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.RobustRest.toRest

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.RobustRest.of_rest_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.RobustRest.of_rest_exact

/-- info: 'SparseHamiltonian.RepresentedSampleODE.mesh_duhamel_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.mesh_duhamel_bounded

/-- info: 'SparseHamiltonian.RepresentedSampleODE.RegularPieces.of_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.RegularPieces.of_continuous

/-- info: 'SparseHamiltonian.RepresentedSampleODE.MildSolution.of_solves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.MildSolution.of_solves

/-- info: 'SparseHamiltonian.RepresentedSampleODE.MildSolution.of_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.MildSolution.of_continuous

/-- info: 'SparseHamiltonian.RepresentedSampleODE.mesh_zero_generator_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.mesh_zero_generator_core

/-! ### The positive repair (`Repair`) -/

/-- info: 'SparseHamiltonian.RepresentedSampleODE.norm_one_op_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.norm_one_op_le

/-- info: 'SparseHamiltonian.RepresentedSampleODE.repair_coeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.repair_coeff_nonneg

/-- info: 'SparseHamiltonian.RepresentedSampleODE.repair_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.repair_selfAdjoint

/-- info: 'SparseHamiltonian.RepresentedSampleODE.norm_repair_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.norm_repair_sub_le

/-- info: 'SparseHamiltonian.RepresentedSampleODE.norm_repair_sub_le_two_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.norm_repair_sub_le_two_norm

/-- info: 'SparseHamiltonian.RepresentedSampleODE.productFamily_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.productFamily_sub_le

/-! ### The repaired LCHS family (`Family`) -/

/-- info: 'SparseHamiltonian.RepresentedSampleODE.sum_slotPiece_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.sum_slotPiece_blocks

/-- info: 'SparseHamiltonian.RepresentedSampleODE.sum_slotPiece' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.sum_slotPiece

/-- info: 'SparseHamiltonian.RepresentedSampleODE.negativity_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.negativity_nonneg

/-- info: 'SparseHamiltonian.RepresentedSampleODE.negativity_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.negativity_zero

/-- info: 'SparseHamiltonian.RepresentedSampleODE.dissipative_negativity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.dissipative_negativity

/-- info: 'SparseHamiltonian.RepresentedSampleODE.repairedDissipative_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.repairedDissipative_selfAdjoint

/-- info: 'SparseHamiltonian.RepresentedSampleODE.repairedDissipative_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.repairedDissipative_nonneg

/-- info: 'SparseHamiltonian.RepresentedSampleODE.repairedDissipative_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.repairedDissipative_norm_le

/-- info: 'SparseHamiltonian.RepresentedSampleODE.hamiltonian_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.hamiltonian_norm_le

/-- info: 'SparseHamiltonian.RepresentedSampleODE.repairedGenerator_accretive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.repairedGenerator_accretive

/-- info: 'SparseHamiltonian.RepresentedSampleODE.repairedGenerator_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.repairedGenerator_sub_le

/-- info: 'SparseHamiltonian.RepresentedSampleODE.repairedGenerator_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.repairedGenerator_norm_le

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robustFamily_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robustFamily_analyticAt

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robustFamily_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robustFamily_norm_le_one

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robustFamily_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robustFamily_lipschitz

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robustFamily_neg_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robustFamily_neg_I

/-- info: 'SparseHamiltonian.RepresentedSampleODE.tableFamily_sub_robustFamily_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.tableFamily_sub_robustFamily_slots

/-! ### The repaired target (`Target`) -/

/-- info: 'SparseHamiltonian.RepresentedSampleODE.integral_norm_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.integral_norm_sub_le

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robustTarget_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robustTarget_norm_le

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_branch_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_branch_error

/-! ### The zero cases (`Zero`) -/

/-- info: 'SparseHamiltonian.RepresentedSampleODE.tableFamily_zero_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.tableFamily_zero_time

/-- info: 'SparseHamiltonian.RepresentedSampleODE.zero_time_target_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.zero_time_target_error

/-- info: 'SparseHamiltonian.RepresentedSampleODE.RobustBudget.released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.RobustBudget.released

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_of_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_of_released

/-! ### The actual oracles (`Actual`) -/

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_actual_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_actual_build

/-! ### Approximate preparations (`Approx`) -/

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robust_approx_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robust_approx_build

/-! ### The integral certificates and the path negativity bounds (`Integral`) -/

/-- info: 'SparseHamiltonian.RepresentedSampleODE.re_inner_le_dissipative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.re_inner_le_dissipative

/-- info: 'SparseHamiltonian.RepresentedSampleODE.dissipative_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.dissipative_continuousOn

/-- info: 'SparseHamiltonian.RepresentedSampleODE.dissipativeError_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.dissipativeError_nonneg

/-- info: 'SparseHamiltonian.RepresentedSampleODE.pathNegativity_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.pathNegativity_nonneg

/-! ### Duhamel's formula on a mesh for bounded pieces (`Duhamel`) -/

/-- info: 'SparseHamiltonian.RepresentedSampleODE.piece_le_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.piece_le_last

/-- info: 'SparseHamiltonian.RepresentedSampleODE.piece_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.piece_mem

/-- info: 'SparseHamiltonian.RepresentedSampleODE.mesh_move_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.mesh_move_le

/-- info: 'SparseHamiltonian.RepresentedSampleODE.endMap_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.endMap_norm_le

/-- info: 'SparseHamiltonian.RepresentedSampleODE.propagated_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.propagated_sub_le

/-- info: 'SparseHamiltonian.RepresentedSampleODE.propagated_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.propagated_continuousOn

/-- info: 'SparseHamiltonian.RepresentedSampleODE.duhamel_right_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.duhamel_right_deriv

/-- info: 'SparseHamiltonian.RepresentedSampleODE.piece_duhamel_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.piece_duhamel_bounded

/-- info: 'SparseHamiltonian.RepresentedSampleODE.continuous_pieces_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.continuous_pieces_regular

/-! ### Integrable pieces and mild solutions (`Regular`) -/

/-- info: 'SparseHamiltonian.RepresentedSampleODE.dissipative_intervalIntegrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.dissipative_intervalIntegrable

/-- info: 'SparseHamiltonian.RepresentedSampleODE.dissipativeError_le_sampleError_of_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.dissipativeError_le_sampleError_of_int

/-- info: 'SparseHamiltonian.RepresentedSampleODE.pathNegativity_bound_of_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.pathNegativity_bound_of_int

/-- info: 'SparseHamiltonian.RepresentedSampleODE.robustBudget_of_path_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.robustBudget_of_path_int

/-! ### The gate-level certificate (`Gate/Certificate`) -/

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.RobustInstanceOK.of_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.RobustInstanceOK.of_released

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.RobustInstanceOK.unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.RobustInstanceOK.unitary

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.slot_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.slot_mem

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.re_inner_gens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.re_inner_gens

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.repaired_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.repaired_facts

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.RobustInstanceOK.δG_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.RobustInstanceOK.δG_nonneg

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.RobustInstanceOK.repaired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.RobustInstanceOK.repaired

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.branchU_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.branchU_sub_le

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.branch_sum_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.branch_sum_sub_le

/-! ### The gate-level solver from binary data (`Gate/Binary`) -/

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.robust_instanceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.robust_instanceOK

/-- info: 'SparseHamiltonian.RepresentedSampleODE.GateTime.robust_tzInstanceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.RepresentedSampleODE.GateTime.robust_tzInstanceOK
