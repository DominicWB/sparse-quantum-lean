import ZeroTimeRemarks.Hamiltonian
import ZeroTimeRemarks.TimeUniform
import ZeroTimeRemarks.TimeMesh
import ZeroTimeRemarks.TimeBlock
import ZeroTimeRemarks.Gates
import ZeroTimeRemarks.ODEConstant
import ZeroTimeRemarks.ODETime
import ZeroTimeRemarks.ODEMesh

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`. The audits cover every theorem of the library
of the zero-time and zero-generator remarks, beginning with Theorem `hs:thm:main` at zero
time or zero norm bound (`simulation_zero`) and for every `η ≥ 0`
(`simulation_log_one_nonneg`).
-/

/-! ### Theorem `hs:thm:main` at zero time or zero norm bound -/

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.simulation_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.simulation_zero

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.simulation_log_one_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.simulation_log_one_nonneg

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.native_input_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.native_input_isometry

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.native_output_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.native_output_isometry

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.input_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.input_isometry

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.exp_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.exp_eq_one

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.zero_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.zero_certificate

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.one_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.one_admissible

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.simulation_spectral_log_one_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.simulation_spectral_log_one_nonneg

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.simulation_with_reference_log_one_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Hamiltonian.simulation_with_reference_log_one_nonneg

/-! ### Theorem `hs:thm:time` at zero time or zero norm bound (meshes, block encodings) -/

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeUniform.evolution_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeUniform.evolution_one

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeUniform.isometry_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeUniform.isometry_norm_le_one

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeUniform.identity_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeUniform.identity_error_le

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeUniform.zero_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeUniform.zero_bound

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeUniform.freeze_value_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeUniform.freeze_value_le

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeUniform.simulation_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeUniform.simulation_nonneg

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeUniform.simulation_with_reference_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeUniform.simulation_with_reference_nonneg

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeMesh.solvesOn_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeMesh.solvesOn_zero_eq

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeMesh.piecewise_zero_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeMesh.piecewise_zero_eq_one

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeMesh.input_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeMesh.input_isometry

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeMesh.zero_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeMesh.zero_certificate

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeMesh.zero_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeMesh.zero_bound

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeMesh.certificate_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeMesh.certificate_nonneg

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeMesh.simulation_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeMesh.simulation_nonneg

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeMesh.simulation_with_reference_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeMesh.simulation_with_reference_nonneg

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeBlock.alignedInput_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeBlock.alignedInput_isometry

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeBlock.blockSample_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeBlock.blockSample_zero

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeBlock.zero_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeBlock.zero_bound

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.TimeBlock.simulation_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.TimeBlock.simulation_nonneg

/-! ### Theorem `hs:thm:gates` at zero time -/

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Gates.exp_zero_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Gates.exp_zero_time

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Gates.identity_comp_error_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Gates.identity_comp_error_eq_zero

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Gates.identity_comp_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Gates.identity_comp_error_le

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Gates.simulation_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Gates.simulation_nonneg

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Gates.time_simulation_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Gates.time_simulation_nonneg

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Gates.native_simulation_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Gates.native_simulation_nonneg

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Gates.native_simulation_signed_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Gates.native_simulation_signed_zero

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.Gates.native_time_simulation_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.Gates.native_time_simulation_nonneg

/-! ### Theorem `ode:thm:main` at zero time or with a known zero generator -/

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEConstant.encoding_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEConstant.encoding_isometry

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEConstant.trial_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEConstant.trial_matrix_cost

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEConstant.identity_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEConstant.identity_trials

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEConstant.branchEvolution_eq_one_of_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEConstant.branchEvolution_eq_one_of_time

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEConstant.zero_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEConstant.zero_solver

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEConstant.outcome_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEConstant.outcome_of_budget

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEConstant.budget_of_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEConstant.budget_of_outcome

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEConstant.native_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEConstant.native_solver

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEConstant.solver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEConstant.solver_nonneg

/-! ### Theorem `ode:thm:time` at zero time or with a known zero generator (all meshes) -/

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODETime.alignedInput_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODETime.alignedInput_isometry

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODETime.trial_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODETime.trial_matrix_cost

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODETime.branchEvolution_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODETime.branchEvolution_eq_one

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODETime.identity_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODETime.identity_trials

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODETime.zero_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODETime.zero_solver

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODETime.outcome_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODETime.outcome_of_budget

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODETime.budget_of_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODETime.budget_of_outcome

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODETime.solver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODETime.solver_nonneg

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEMesh.alignedInput_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEMesh.alignedInput_isometry

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEMesh.trial_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEMesh.trial_matrix_cost

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEMesh.branchEvolution_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEMesh.branchEvolution_eq_one

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEMesh.exp_real_smul_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEMesh.exp_real_smul_zero

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEMesh.target_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEMesh.target_zero

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEMesh.identity_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEMesh.identity_trials

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEMesh.certified_error_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEMesh.certified_error_nonneg

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEMesh.zero_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEMesh.zero_solver

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEMesh.outcome_of_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEMesh.outcome_of_budget

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEMesh.budget_of_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEMesh.budget_of_outcome

/-- info: 'SparseHamiltonian.ZeroTimeRemarks.ODEMesh.solver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeRemarks.ODEMesh.solver_nonneg
