import TimeDependentExtensions.Hamiltonian.Corollaries
import TimeDependentExtensions.ODE.Corollaries
import TimeDependentExtensions.BlockEncoding.Theorem
import TimeDependentExtensions.Coherent.Theorem

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 6 lemmas, whose reports list a
subset of these three axioms. The audits cover every theorem of the library of
generalisations of the time-dependent theorems, beginning with Theorem
`hs:thm:time` on general meshes.
-/

/-! ### Theorem `hs:thm:time` on general meshes -/

/-- info: 'TimeDependentExtensions.Hamiltonian.simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Hamiltonian.simulation

/-- info: 'TimeDependentExtensions.Hamiltonian.simulation_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Hamiltonian.simulation_lipschitz

/-- info: 'TimeDependentExtensions.Hamiltonian.simulation_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Hamiltonian.simulation_path

/-- info: 'TimeDependentExtensions.Hamiltonian.sampleIndex_val' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Hamiltonian.sampleIndex_val

/-- info: 'TimeDependentExtensions.Hamiltonian.sampleIndex_of_lt' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Hamiltonian.sampleIndex_of_lt

/-- info: 'TimeDependentExtensions.Hamiltonian.oracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Hamiltonian.oracle_unitary

/-- info: 'TimeDependentExtensions.Hamiltonian.matrixOperator_norm_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Hamiltonian.matrixOperator_norm_le_sqrt

/-- info: 'TimeDependentExtensions.Hamiltonian.sample_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Hamiltonian.sample_norm_le

/-- info: 'TimeDependentExtensions.Hamiltonian.sampledEvolution_normalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Hamiltonian.sampledEvolution_normalize

/-- info: 'TimeDependentExtensions.Hamiltonian.simulation_with_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Hamiltonian.simulation_with_reference

/-- info: 'TimeDependentExtensions.Hamiltonian.slotCount_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Hamiltonian.slotCount_spec

/-- info: 'TimeDependentExtensions.Hamiltonian.isMesh_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Hamiltonian.isMesh_uniform

/-! ### Theorem `ode:thm:time` on general meshes -/

/-- info: 'TimeDependentExtensions.ODE.solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODE.solver

/-- info: 'TimeDependentExtensions.ODE.exists_solvesODE_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODE.exists_solvesODE_from

/-- info: 'TimeDependentExtensions.ODE.exists_piecewise_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODE.exists_piecewise_solution

/-- info: 'TimeDependentExtensions.ODE.solver_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODE.solver_lipschitz

/-- info: 'TimeDependentExtensions.ODE.publicError_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODE.publicError_le

/-! ### Time-indexed block encodings (`hs:eq:blockspecial`, `hs:eq:blockadditive`) -/

/-- info: 'TimeDependentExtensions.BlockEncoding.core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.core

/-- info: 'TimeDependentExtensions.BlockEncoding.exists_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.exists_simulation

/-- info: 'TimeDependentExtensions.BlockEncoding.blockSample_self_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.blockSample_self_adjoint

/-- info: 'TimeDependentExtensions.BlockEncoding.blockSample_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.blockSample_norm_le

/-- info: 'TimeDependentExtensions.BlockEncoding.sampleIndex_of_lt' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.sampleIndex_of_lt

/-- info: 'TimeDependentExtensions.BlockEncoding.simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.simulation

/-- info: 'TimeDependentExtensions.BlockEncoding.one_sub_mul_one_add' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.one_sub_mul_one_add

/-- info: 'TimeDependentExtensions.BlockEncoding.one_add_mul_one_sub' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.one_add_mul_one_sub

/-- info: 'TimeDependentExtensions.BlockEncoding.sq_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.sq_eq_one

/-- info: 'TimeDependentExtensions.BlockEncoding.privateAction_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.privateAction_isometry

/-- info: 'TimeDependentExtensions.BlockEncoding.resolvent_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.resolvent_right

/-- info: 'TimeDependentExtensions.BlockEncoding.resolvent_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.resolvent_left

/-- info: 'TimeDependentExtensions.BlockEncoding.resolvent_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.resolvent_boundary

/-- info: 'TimeDependentExtensions.BlockEncoding.resolvent_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.resolvent_moment

/-- info: 'TimeDependentExtensions.BlockEncoding.resolvent_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.resolvent_norm_le

/-- info: 'TimeDependentExtensions.BlockEncoding.endpoint_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.endpoint_norm_le

/-- info: 'TimeDependentExtensions.BlockEncoding.compressed_self_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.compressed_self_adjoint

/-- info: 'TimeDependentExtensions.BlockEncoding.compressed_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.compressed_norm_le

/-- info: 'TimeDependentExtensions.BlockEncoding.primitive_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.primitive_unitary

/-- info: 'TimeDependentExtensions.BlockEncoding.place_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.place_apply

/-- info: 'TimeDependentExtensions.BlockEncoding.controlled_place' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.controlled_place

/-- info: 'TimeDependentExtensions.BlockEncoding.layout_symm_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.layout_symm_single

/-- info: 'TimeDependentExtensions.BlockEncoding.primitive_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.primitive_valid

/-- info: 'TimeDependentExtensions.BlockEncoding.sourceProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.sourceProgram_count

/-- info: 'TimeDependentExtensions.BlockEncoding.oracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.oracle_unitary

/-- info: 'TimeDependentExtensions.BlockEncoding.implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.BlockEncoding.implementsOn

/-! ### Coherent selection of durations and start times -/

/-- info: 'TimeDependentExtensions.Coherent.hamiltonianPart_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Coherent.hamiltonianPart_rotate

/-- info: 'TimeDependentExtensions.Coherent.dissipativePart_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Coherent.dissipativePart_rotate

/-- info: 'TimeDependentExtensions.Coherent.lchsHamiltonian_rotate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Coherent.lchsHamiltonian_rotate

/-- info: 'TimeDependentExtensions.Coherent.coherent_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Coherent.coherent_select

/-- info: 'TimeDependentExtensions.Coherent.orderedProduct_eq_evolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Coherent.orderedProduct_eq_evolution

/-- info: 'TimeDependentExtensions.Coherent.orderedProduct_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Coherent.orderedProduct_congr

/-- info: 'TimeDependentExtensions.Coherent.evolution_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Coherent.evolution_window

/-- info: 'TimeDependentExtensions.Coherent.window_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Coherent.window_error

/-- info: 'TimeDependentExtensions.Coherent.coherent_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Coherent.coherent_windows

/-! ### The sampled native simulation with a slot-to-sample map -/

/-- info: 'TimeDependentExtensions.Refined.implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Refined.implementsOn

/-- info: 'TimeDependentExtensions.Refined.step_smul_compressed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Refined.step_smul_compressed

/-- info: 'TimeDependentExtensions.Refined.sampled_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Refined.sampled_core

/-- info: 'TimeDependentExtensions.Refined.exists_sampled_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.Refined.exists_sampled_simulation

/-! ### The ODE SELECT and the source layer on refined slots -/

/-- info: 'TimeDependentExtensions.MeshSelect.implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSelect.implementsOn

/-- info: 'TimeDependentExtensions.MeshSelect.select_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSelect.select_core

/-- info: 'TimeDependentExtensions.MeshSelect.exists_native_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSelect.exists_native_select

/-- info: 'TimeDependentExtensions.MeshSelect.alignedOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSelect.alignedOracle_unitary

/-- info: 'TimeDependentExtensions.MeshSelect.select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSelect.select

/-- info: 'TimeDependentExtensions.MeshSource.matrixOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSource.matrixOracle_unitary

/-- info: 'TimeDependentExtensions.MeshSource.matrix_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSource.matrix_valid

/-- info: 'TimeDependentExtensions.MeshSource.input_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSource.input_isometry

/-- info: 'TimeDependentExtensions.MeshSource.physicalOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSource.physicalOracle_unitary

/-- info: 'TimeDependentExtensions.MeshSource.coefficient_trial_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSource.coefficient_trial_certificate

/-! ### Mesh sources, slot families and the discretised target -/

/-- info: 'TimeDependentExtensions.MeshSampling.sampleIndex_of_lt' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.sampleIndex_of_lt

/-- info: 'TimeDependentExtensions.MeshSampling.target_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.target_norm_le

/-- info: 'TimeDependentExtensions.MeshSampling.family_neg_I_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.family_neg_I_eq

/-- info: 'TimeDependentExtensions.MeshSampling.target_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.target_error

/-- info: 'TimeDependentExtensions.MeshSampling.sum_norms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.sum_norms

/-- info: 'TimeDependentExtensions.MeshSampling.norms_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.norms_nonneg

/-- info: 'TimeDependentExtensions.MeshSampling.coefficients_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.coefficients_mass

/-- info: 'TimeDependentExtensions.MeshSampling.mass_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.mass_eq

/-- info: 'TimeDependentExtensions.MeshSampling.actual_coefficients_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.actual_coefficients_eq

/-- info: 'TimeDependentExtensions.MeshSampling.sources_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.sources_norm

/-- info: 'TimeDependentExtensions.MeshSampling.dissipative_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.dissipative_norm_le

/-- info: 'TimeDependentExtensions.MeshSampling.generator_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.generator_norm_le

/-- info: 'TimeDependentExtensions.MeshSampling.generator_accretive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.generator_accretive

/-- info: 'TimeDependentExtensions.MeshSampling.decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.decomposition

/-- info: 'TimeDependentExtensions.MeshSampling.slotDurations_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.slotDurations_nonneg

/-- info: 'TimeDependentExtensions.MeshSampling.slotDurations_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.slotDurations_le

/-- info: 'TimeDependentExtensions.MeshSampling.family_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.family_analyticAt

/-- info: 'TimeDependentExtensions.MeshSampling.family_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.family_norm_le_one

/-- info: 'TimeDependentExtensions.MeshSampling.family_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.family_lipschitz

/-- info: 'TimeDependentExtensions.MeshSampling.family_neg_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.family_neg_I

/-- info: 'TimeDependentExtensions.MeshSampling.branchEvolution_eq_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.MeshSampling.branchEvolution_eq_family

/-! ### Forced dissipative ODEs on general meshes -/

/-- info: 'TimeDependentExtensions.ODEMesh.exp_smul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODEMesh.exp_smul_pow

/-- info: 'TimeDependentExtensions.ODEMesh.intervalIntegrable_apply_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODEMesh.intervalIntegrable_apply_right

/-- info: 'TimeDependentExtensions.ODEMesh.intervalIntegrable_apply_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODEMesh.intervalIntegrable_apply_left

/-- info: 'TimeDependentExtensions.ODEMesh.norm_le_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODEMesh.norm_le_from

/-- info: 'TimeDependentExtensions.ODEMesh.piecewise_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODEMesh.piecewise_norm_le

/-- info: 'TimeDependentExtensions.ODEMesh.step_error_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODEMesh.step_error_integral

/-- info: 'TimeDependentExtensions.ODEMesh.meshRecurrence_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODEMesh.meshRecurrence_succ

/-- info: 'TimeDependentExtensions.ODEMesh.mesh_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODEMesh.mesh_error

/-- info: 'TimeDependentExtensions.ODEMesh.meshPropagator_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODEMesh.meshPropagator_norm_le_one

/-- info: 'TimeDependentExtensions.ODEMesh.meshPropagator_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODEMesh.meshPropagator_of_le

/-- info: 'TimeDependentExtensions.ODEMesh.meshPropagator_succ_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODEMesh.meshPropagator_succ_of_le

/-- info: 'TimeDependentExtensions.ODEMesh.meshRecurrence_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODEMesh.meshRecurrence_eq_sum

/-- info: 'TimeDependentExtensions.ODEMesh.refinedPropagator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODEMesh.refinedPropagator_eq

/-- info: 'TimeDependentExtensions.ODEMesh.refinedPropagator_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.ODEMesh.refinedPropagator_sub_le

/-! ### Piecewise paths and integrated certificates -/

/-- info: 'TimeDependentExtensions.duhamel_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.duhamel_integral

/-- info: 'TimeDependentExtensions.integral_le_of_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.integral_le_of_lipschitz

/-- info: 'TimeDependentExtensions.continuousOn_of_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.continuousOn_of_lipschitz

/-- info: 'TimeDependentExtensions.integral_le_of_lipschitz'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.integral_le_of_lipschitz'

/-- info: 'TimeDependentExtensions.piecewise_norm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.piecewise_norm_apply

/-- info: 'TimeDependentExtensions.piecewise_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.piecewise_norm_le

/-- info: 'TimeDependentExtensions.mesh_error_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.mesh_error_integral

/-- info: 'TimeDependentExtensions.refined_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.refined_error

/-- info: 'TimeDependentExtensions.exists_solvesOn_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.exists_solvesOn_from

/-- info: 'TimeDependentExtensions.exists_piecewise_propagator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.exists_piecewise_propagator

/-- info: 'TimeDependentExtensions.isPiecewisePropagator_of_solvesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.isPiecewisePropagator_of_solvesOn

/-! ### Meshes and their refinement -/

/-- info: 'TimeDependentExtensions.IsMesh.nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.IsMesh.nonneg

/-- info: 'TimeDependentExtensions.IsMesh.le_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.IsMesh.le_last

/-- info: 'TimeDependentExtensions.IsMesh.length_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.IsMesh.length_nonneg

/-- info: 'TimeDependentExtensions.IsMesh.sum_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.IsMesh.sum_length

/-- info: 'TimeDependentExtensions.blockStart_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.blockStart_zero

/-- info: 'TimeDependentExtensions.blockStart_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.blockStart_last

/-- info: 'TimeDependentExtensions.blockStart_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.blockStart_mono

/-- info: 'TimeDependentExtensions.blockStart_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.blockStart_le

/-- info: 'TimeDependentExtensions.blockStart_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.blockStart_bounds

/-- info: 'TimeDependentExtensions.blockLength_sub_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.blockLength_sub_lt

/-- info: 'TimeDependentExtensions.slotPiece_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.slotPiece_lt

/-- info: 'TimeDependentExtensions.slotPiece_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.slotPiece_eq

/-- info: 'TimeDependentExtensions.orderedProduct_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.orderedProduct_add

/-- info: 'TimeDependentExtensions.evolution_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.evolution_blocks

/-- info: 'TimeDependentExtensions.evolution_congr'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.evolution_congr'

/-- info: 'TimeDependentExtensions.orderedProduct_congr_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.orderedProduct_congr_const

/-- info: 'TimeDependentExtensions.evolution_slotPiece' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.evolution_slotPiece

/-- info: 'TimeDependentExtensions.exp_skew_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.exp_skew_norm_le

/-- info: 'TimeDependentExtensions.exp_add_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.exp_add_commute

/-- info: 'TimeDependentExtensions.exp_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.exp_pow

/-- info: 'TimeDependentExtensions.exp_sub_exp_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.exp_sub_exp_norm_le

/-- info: 'TimeDependentExtensions.refined_evolution_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.refined_evolution_eq

/-- info: 'TimeDependentExtensions.refined_evolution_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentExtensions.refined_evolution_sub_le
