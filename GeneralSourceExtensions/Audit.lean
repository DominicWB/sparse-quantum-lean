import GeneralSourceExtensions.Zero
import GeneralSourceExtensions.Approx.Recast
import GeneralSourceExtensions.Approx.Norms
import GeneralSourceExtensions.Approx.Pullback
import GeneralSourceExtensions.Approx.Theorem
import GeneralSourceExtensions.Mesh.Durations
import GeneralSourceExtensions.Mesh.Native
import GeneralSourceExtensions.Mesh.Oracles
import GeneralSourceExtensions.Mesh.Theorem
import GeneralSourceExtensions.Mesh.Zero
import GeneralSourceExtensions.Mesh.Actual
import GeneralSourceExtensions.Mesh.Approx
import GeneralSourceExtensions.Mesh.Duhamel
import GeneralSourceExtensions.Mesh.Integral
import GeneralSourceExtensions.Mesh.Corollaries
import GeneralSourceExtensions.Mesh.Uniform

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (122 theorems), beginning
with the main theorems, then in module order. Every report lists exactly `propext`,
`Classical.choice` and `Quot.sound`. -/

/-! ### Final theorems: Theorem `ode:thm:time` with the general source interface on meshes, with
approximate preparations and for every `T ≥ 0`, the uniform theorems from the mesh endpoints,
Duhamel's formula on a mesh, and non-vacuity -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_approx_solver_nonneg_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_approx_solver_nonneg_integral

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_approx_solver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_approx_solver_nonneg

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver_integral

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver_nonneg

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_propagated_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_propagated_solver

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.solver_of_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.solver_of_mesh

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.approx_solver_nonneg_of_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.approx_solver_nonneg_of_mesh

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_approx_solver_nonneg_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_approx_solver_nonneg_uniform

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_solver_uniform

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.approx_solver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.approx_solver_nonneg

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.approx_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.approx_solver

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.solver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.solver_nonneg

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.zero_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.zero_solver

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.zero_propagated_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.zero_propagated_solver

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_duhamel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_duhamel

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.exists_isMeshPropagator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.exists_isMeshPropagator

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.sampleError_le_of_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.sampleError_le_of_lipschitz

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.uniform_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.uniform_instance

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.uniform_budget_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.uniform_budget_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.approx_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.approx_certificate

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.perturbed_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.perturbed_four

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_target_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_target_error

/-! ### The zero cases (`Zero`) -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.trial_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.trial_matrix_cost

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.durationTable_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.durationTable_zero

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.durationTable_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.durationTable_eq_zero

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.zero_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.zero_core

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.budget_of_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.budget_of_trial

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.outcome_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.outcome_of_budget

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.budget_of_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.budget_of_outcome

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.actual_of_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.actual_of_trial

/-! ### Recast programs and the perturbed protocol (`Approx/Recast`) -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.cost_recast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.cost_recast

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.eval_recast_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.eval_recast_eq

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.eval_recast_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.eval_recast_sub_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.norm_adjoint_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.norm_adjoint_apply_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.ApproxCertificate.of_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.ApproxCertificate.of_actual

/-! ### Norms of the embedded supplied operations (`Approx/Norms`) -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.act_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.act_add

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.act_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.act_smul

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.act_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.act_sub

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.norm_act_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.norm_act_apply_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.norm_act_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.norm_act_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.norm_act_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.norm_act_sub_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.norm_loader_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.norm_loader_sub_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.norm_conj_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.norm_conj_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.norm_conj_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.norm_conj_sub_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.norm_sourcePhysical_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.norm_sourcePhysical_sub_le

/-! ### Exact preparation instances (`Approx/Pullback`) -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.pullback_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.pullback_matrix

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Inst.weight_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Inst.weight_unitary

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Inst.loader_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Inst.loader_unitary

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.actualOracle_pullback_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.actualOracle_pullback_matrix

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.actualOracle_dev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.actualOracle_dev

/-! ### Approximate preparations on the uniform mesh (`Approx/Theorem`) -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.approxOutcome_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.approxOutcome_of_budget

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.approx_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.approx_build

/-! ### Mesh durations, product families and node propagators (`Mesh/Durations`) -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.meshWidth_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.meshWidth_nonneg

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.meshWidth_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.meshWidth_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.meshDurations_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.meshDurations_nonneg

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.meshDurations_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.meshDurations_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.block_duration_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.block_duration_sub_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.roundingError_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.roundingError_nonneg

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.roundingError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.roundingError_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.roundingError_eq_zero_of_grid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.roundingError_eq_zero_of_grid

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.roundingError_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.roundingError_uniform

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.tableFamily_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.tableFamily_analyticAt

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.tableFamily_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.tableFamily_norm_le_one

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.tableFamily_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.tableFamily_lipschitz

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.tableFamily_neg_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.tableFamily_neg_I

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.branchEvolution_eq_tableFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.branchEvolution_eq_tableFamily

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.evolution_congr_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.evolution_congr_one

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.meshNodeProduct_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.meshNodeProduct_norm_le_one

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.node_error_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.node_error_nat

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.refined_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.refined_sub_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.refined_sub_le_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.refined_sub_le_of_nonneg

/-! ### The `N`-slot native layer (`Mesh/Native`) -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshNative.matrixOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshNative.matrixOracle_unitary

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshNative.matrix_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshNative.matrix_valid

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshNative.input_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshNative.input_isometry

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshNative.physicalOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshNative.physicalOracle_unitary

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshNative.trial_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshNative.trial_certificate

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshNative.seed_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshNative.seed_unit

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshNative.output_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshNative.output_isometry

/-! ### The supplied source oracles on `N` slots (`Mesh/Oracles`) -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.actualOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.actualOracle_unitary

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.phaseGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.phaseGate_unitary

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementation_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementation_eval

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementation_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementation_matrix

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementation_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementation_weight

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementation_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementation_load

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementation_unweight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementation_unweight

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementation_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.implementation_source

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.actualOracle_pullback_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.actualOracle_pullback_matrix

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.MeshOracles.actualOracle_dev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.MeshOracles.actualOracle_dev

/-! ### Branch and target errors and the two-interface solver on a mesh (`Mesh/Theorem`) -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.meshScale_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.meshScale_nonneg

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.sampleError_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.sampleError_nonneg

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.refinementError_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.refinementError_nonneg

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.refinementError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.refinementError_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.refinementError_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.refinementError_uniform

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.meshTarget_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.meshTarget_norm_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.branch_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.branch_error

/-! ### The zero cases on a mesh (`Mesh/Zero`) -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.meshDurations_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.meshDurations_eq_zero

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.propagated_of_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.propagated_of_trial

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.trial_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.trial_matrix_cost

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_zero_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_zero_core

/-! ### The actual oracles on a mesh (`Mesh/Actual`) -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.lchsCoefficients_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.lchsCoefficients_mass

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_actual_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_actual_build

/-! ### Approximate preparations on a mesh (`Mesh/Approx`) -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_approx_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_approx_build

/-! ### Duhamel's formula on a mesh (`Mesh/Duhamel`) -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_induction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.mesh_induction

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.accretive_after' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.accretive_after

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.SolvesFrom.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.SolvesFrom.unique

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.SolvesFrom.norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.SolvesFrom.norm_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.SolvesFrom.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.SolvesFrom.mono

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.SolvesFrom.lincomb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.SolvesFrom.lincomb

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.IsMeshPropagator.lincomb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.IsMeshPropagator.lincomb

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.IsMeshPropagator.norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.IsMeshPropagator.norm_le

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.IsMeshPropagator.cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.IsMeshPropagator.cocycle

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.IsMeshPropagator.map_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.IsMeshPropagator.map_zero

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.endMap_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.endMap_apply

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.solvesODE_shift_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.solvesODE_shift_forward

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.piece_duhamel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.piece_duhamel

/-! ### Non-vacuity of the mesh hypotheses (`Mesh/Corollaries`) -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.solvesODE_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.solvesODE_shift

/-! ### The uniform theorems from the mesh endpoints (`Mesh/Uniform`) -/

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.isMesh_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.isMesh_uniform

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.clock_conditions_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.clock_conditions_mul

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.actualOracle_eq_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.actualOracle_eq_released

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.uniformOutcome_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.uniformOutcome_eq

/-- info: 'SparseHamiltonian.GeneralSourceExtensions.Mesh.uniformApproxBudgetOutcome_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceExtensions.Mesh.uniformApproxBudgetOutcome_eq
