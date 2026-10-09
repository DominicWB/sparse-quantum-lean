import GateEfficientMesh.Slots
import GateEfficientMesh.Exact
import GateEfficientMesh.Native
import GateEfficientMesh.Binary
import GateEfficientMesh.BinaryTheorem
import GateEfficientMesh.BinaryMesh
import GateEfficientMesh.Synth
import GateEfficientMesh.ODE.Core
import GateEfficientMesh.ODE.Target
import GateEfficientMesh.ODE.Exact
import GateEfficientMesh.ODE.Native
import GateEfficientMesh.ODE.Binary
import GateEfficientMesh.ODE.MeshScheme
import GateEfficientMesh.ODE.MeshTarget
import GateEfficientMesh.ODE.Mesh
import GateEfficientMesh.ODE.BinaryMesh
import GateEfficientMesh.ODE.Synth
import GateEfficientMesh.ODE.Trials
import GateEfficientMesh.NonVacuity

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`. The audits cover every theorem of the library
of the gate-level time-dependent theorems under integrated sample-error certificates and
on nonuniform meshes (98 theorems, in module order), beginning with Theorem `hs:thm:gates`
(time-dependent part) under the integrated certificate (`time_simulation_certified`) and on a
nonuniform mesh (`time_simulation_mesh`).
-/

/-! ### Theorem `hs:thm:gates`, time-dependent part, exact gates: slots, certificates, meshes -/

/-- info: 'SparseHamiltonian.GateMesh.time_simulation_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.time_simulation_certified

/-- info: 'SparseHamiltonian.GateMesh.time_simulation_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.time_simulation_mesh

/-- info: 'SparseHamiltonian.GateMesh.slotMesh_succ_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.slotMesh_succ_sub

/-- info: 'SparseHamiltonian.GateMesh.isMesh_slotMesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.isMesh_slotMesh

/-- info: 'SparseHamiltonian.GateMesh.slotEvolution_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.slotEvolution_congr

/-- info: 'SparseHamiltonian.GateMesh.meshEvolution_slotMesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.meshEvolution_slotMesh

/-- info: 'SparseHamiltonian.GateMesh.refinedEvolution_eq_slotEvolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.refinedEvolution_eq_slotEvolution

/-- info: 'SparseHamiltonian.GateMesh.slot_error_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.slot_error_integral

/-- info: 'SparseHamiltonian.GateMesh.slot_error_piecewise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.slot_error_piecewise

/-- info: 'SparseHamiltonian.GateMesh.mul_div_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.mul_div_two_pow

/-- info: 'SparseHamiltonian.GateMesh.mesh_slot_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.mesh_slot_error

/-- info: 'SparseHamiltonian.GateMesh.mesh_slot_error_piecewise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.mesh_slot_error_piecewise

/-- info: 'SparseHamiltonian.GateMesh.exists_slot_propagator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.exists_slot_propagator

/-- info: 'SparseHamiltonian.GateMesh.slot_certificate_le_of_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.slot_certificate_le_of_lipschitz

/-- info: 'SparseHamiltonian.GateMesh.slot_product_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.slot_product_error

/-- info: 'SparseHamiltonian.GateMesh.mesh_exponent_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.mesh_exponent_spec

/-- info: 'SparseHamiltonian.GateMesh.slotExponent_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.slotExponent_spec

/-- info: 'SparseHamiltonian.GateMesh.slotExponent_round_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.slotExponent_round_spec

/-- info: 'SparseHamiltonian.GateMesh.time_simulation_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.time_simulation_lipschitz

/-! ### Theorem `hs:thm:gates`, time-dependent part, native gates -/

/-- info: 'SparseHamiltonian.GateMesh.native_slot_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.native_slot_bounds

/-- info: 'SparseHamiltonian.GateMesh.native_time_simulation_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.native_time_simulation_certified

/-- info: 'SparseHamiltonian.GateMesh.native_time_simulation_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.native_time_simulation_mesh

/-! ### Theorem `hs:thm:gates`, time-dependent part, binary sparse data -/

/-- info: 'SparseHamiltonian.GateMesh.intervalIntegrable_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.intervalIntegrable_map

/-- info: 'SparseHamiltonian.GateMesh.integral_map_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.integral_map_le

/-- info: 'SparseHamiltonian.GateMesh.lifted_sample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.lifted_sample

/-- info: 'SparseHamiltonian.GateMesh.intervalIntegrable_qlift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.intervalIntegrable_qlift

/-- info: 'SparseHamiltonian.GateMesh.lifted_integral_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.lifted_integral_le

/-- info: 'SparseHamiltonian.GateMesh.binary_slot_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.binary_slot_bounds

/-- info: 'SparseHamiltonian.GateMesh.binary_slot_error_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.binary_slot_error_integral

/-- info: 'SparseHamiltonian.GateMesh.binary_slot_error_piecewise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.binary_slot_error_piecewise

/-- info: 'SparseHamiltonian.GateMesh.binary_time_simulation_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.binary_time_simulation_certified

/-- info: 'SparseHamiltonian.GateMesh.binary_time_simulation_budget_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.binary_time_simulation_budget_certified

/-- info: 'SparseHamiltonian.GateMesh.clockData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.clockData_matrix

/-- info: 'SparseHamiltonian.GateMesh.clockData_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.clockData_slot

/-- info: 'SparseHamiltonian.GateMesh.clockData_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.clockData_decode

/-- info: 'SparseHamiltonian.GateMesh.prims_reindexData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.prims_reindexData

/-- info: 'SparseHamiltonian.GateMesh.primsT_clockData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.primsT_clockData

/-- info: 'SparseHamiltonian.GateMesh.binary_time_simulation_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.binary_time_simulation_mesh

/-- info: 'SparseHamiltonian.GateMesh.binary_time_simulation_budget_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.binary_time_simulation_budget_mesh

/-! ### Theorem `hs:thm:gates`, time-dependent part, over a finite gate set -/

/-- info: 'SparseHamiltonian.GateMesh.native_time_simulation_certified_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.native_time_simulation_certified_synth

/-- info: 'SparseHamiltonian.GateMesh.native_time_simulation_mesh_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.native_time_simulation_mesh_synth

/-- info: 'SparseHamiltonian.GateMesh.binary_time_simulation_certified_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.binary_time_simulation_certified_synth

/-- info: 'SparseHamiltonian.GateMesh.binary_time_simulation_mesh_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.binary_time_simulation_mesh_synth

/-- info: 'SparseHamiltonian.GateMesh.binary_time_simulation_budget_certified_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.binary_time_simulation_budget_certified_synth

/-! ### Theorem `ode:thm:gates`, time-dependent part: instance conditions, the released chain -/

/-- info: 'SparseHamiltonian.GateMesh.ODE.CoreOK.unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.CoreOK.unitary

/-- info: 'SparseHamiltonian.GateMesh.ODE.target_facts_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.target_facts_of

/-- info: 'SparseHamiltonian.GateMesh.ODE.prep_certificate_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.prep_certificate_of

/-- info: 'SparseHamiltonian.GateMesh.ODE.trial_bounds_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.trial_bounds_of

/-- info: 'SparseHamiltonian.GateMesh.ODE.outcome_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.outcome_of

/-! ### Theorem `ode:thm:gates`, time-dependent part, certificates on the uniform slots -/

/-- info: 'SparseHamiltonian.GateMesh.ODE.meshRecurrence_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.meshRecurrence_const

/-- info: 'SparseHamiltonian.GateMesh.ODE.slot_target_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.slot_target_error

/-- info: 'SparseHamiltonian.GateMesh.ODE.slotCertificate_le_discretisation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.slotCertificate_le_discretisation

/-- info: 'SparseHamiltonian.GateMesh.ODE.certified_of_instanceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.certified_of_instanceOK

/-- info: 'SparseHamiltonian.GateMesh.ODE.ode_time_solver_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.ode_time_solver_certified

/-- info: 'SparseHamiltonian.GateMesh.ODE.native_outcome_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.native_outcome_of

/-- info: 'SparseHamiltonian.GateMesh.ODE.native_ode_time_solver_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.native_ode_time_solver_certified

/-- info: 'SparseHamiltonian.GateMesh.ODE.binary_coreOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.binary_coreOK

/-- info: 'SparseHamiltonian.GateMesh.ODE.binary_ode_time_solver_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.binary_ode_time_solver_certified

/-! ### Theorem `ode:thm:gates`, time-dependent part, nonuniform meshes -/

/-- info: 'SparseHamiltonian.GateMesh.ODE.sum_mask' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.sum_mask

/-- info: 'SparseHamiltonian.GateMesh.ODE.sum_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.sum_blocks

/-- info: 'SparseHamiltonian.GateMesh.ODE.sum_range_le_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.sum_range_le_sq

/-- info: 'SparseHamiltonian.GateMesh.ODE.mask_blockStart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.mask_blockStart

/-- info: 'SparseHamiltonian.GateMesh.ODE.maskedPropagator_blockStart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.maskedPropagator_blockStart

/-- info: 'SparseHamiltonian.GateMesh.ODE.maskedPropagator_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.maskedPropagator_sub_le

/-- info: 'SparseHamiltonian.GateMesh.ODE.block_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.block_error

/-- info: 'SparseHamiltonian.GateMesh.ODE.slot_mesh_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.slot_mesh_recurrence

/-- info: 'SparseHamiltonian.GateMesh.ODE.meshCertificate_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.meshCertificate_le

/-- info: 'SparseHamiltonian.GateMesh.ODE.mesh_target_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.mesh_target_error

/-- info: 'SparseHamiltonian.GateMesh.ODE.target_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.target_congr

/-- info: 'SparseHamiltonian.GateMesh.ODE.ode_time_solver_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.ode_time_solver_mesh

/-- info: 'SparseHamiltonian.GateMesh.ODE.native_ode_time_solver_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.native_ode_time_solver_mesh

/-- info: 'SparseHamiltonian.GateMesh.ODE.meshGens_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.meshGens_eq

/-- info: 'SparseHamiltonian.GateMesh.ODE.HsT_clockData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.HsT_clockData

/-- info: 'SparseHamiltonian.GateMesh.ODE.LsT_clockData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.LsT_clockData

/-- info: 'SparseHamiltonian.GateMesh.ODE.mesh_promises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.mesh_promises

/-- info: 'SparseHamiltonian.GateMesh.ODE.binary_mesh_targetOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.binary_mesh_targetOK

/-- info: 'SparseHamiltonian.GateMesh.ODE.binary_ode_time_solver_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.binary_ode_time_solver_mesh

/-! ### Theorem `ode:thm:gates`, time-dependent part, over a finite gate set -/

/-- info: 'SparseHamiltonian.GateMesh.ODE.native_ode_time_solver_certified_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.native_ode_time_solver_certified_synth

/-- info: 'SparseHamiltonian.GateMesh.ODE.native_ode_time_solver_mesh_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.native_ode_time_solver_mesh_synth

/-- info: 'SparseHamiltonian.GateMesh.ODE.binary_ode_time_solver_certified_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.binary_ode_time_solver_certified_synth

/-- info: 'SparseHamiltonian.GateMesh.ODE.binary_ode_time_solver_mesh_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.binary_ode_time_solver_mesh_synth

/-- info: 'SparseHamiltonian.GateMesh.ODE.trials_outcome_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.trials_outcome_of

/-- info: 'SparseHamiltonian.GateMesh.ODE.native_ode_time_solver_certified_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.native_ode_time_solver_certified_trials

/-- info: 'SparseHamiltonian.GateMesh.ODE.native_ode_time_solver_mesh_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.native_ode_time_solver_mesh_trials

/-- info: 'SparseHamiltonian.GateMesh.ODE.binary_ode_time_solver_certified_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.binary_ode_time_solver_certified_trials

/-- info: 'SparseHamiltonian.GateMesh.ODE.binary_ode_time_solver_mesh_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.binary_ode_time_solver_mesh_trials

/-- info: 'SparseHamiltonian.GateMesh.ODE.binary_ode_time_budget_certified_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.binary_ode_time_budget_certified_trials

/-- info: 'SparseHamiltonian.GateMesh.ODE.binary_ode_time_budget_mesh_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.binary_ode_time_budget_mesh_trials

/-! ### Theorems `hs:thm:gates` and `ode:thm:gates`, time-dependent parts: non-vacuity -/

/-- info: 'SparseHamiltonian.GateMesh.time_simulation_mesh_piecewise_constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.time_simulation_mesh_piecewise_constant

/-- info: 'SparseHamiltonian.GateMesh.time_simulation_mesh_glued' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.time_simulation_mesh_glued

/-- info: 'SparseHamiltonian.GateMesh.slotExponent_native_mesh_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.slotExponent_native_mesh_spec

/-- info: 'SparseHamiltonian.GateMesh.slotExponent_binary_mesh_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.slotExponent_binary_mesh_spec

/-- info: 'SparseHamiltonian.GateMesh.ODE.released_time_solver_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.released_time_solver_outcome

/-- info: 'SparseHamiltonian.GateMesh.ODE.meshCertificate_samples_zero_forcing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.meshCertificate_samples_zero_forcing

/-- info: 'SparseHamiltonian.GateMesh.ODE.meshCertificate_zero_forcing_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.meshCertificate_zero_forcing_le

/-- info: 'SparseHamiltonian.GateMesh.ODE.meshCertificate_one_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.meshCertificate_one_interval

/-- info: 'SparseHamiltonian.GateMesh.ODE.slotCertificate_samples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.slotCertificate_samples

/-- info: 'SparseHamiltonian.GateMesh.ODE.exists_mesh_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateMesh.ODE.exists_mesh_solution
