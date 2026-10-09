import GateEfficientSchedule.Depth
import GateEfficientSchedule.Manuscript
import GateEfficientSchedule.Cayley
import GateEfficientSchedule.Circuit
import GateEfficientSchedule.Endpoint
import GateEfficientSchedule.Selective
import GateEfficientSchedule.TimeClock
import GateEfficientSchedule.TimeMesh
import GateEfficientSchedule.TimeCircuit
import GateEfficientSchedule.SelectiveTime
import GateEfficientSchedule.Native
import GateEfficientSchedule.Abstract

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`. The audits cover every theorem of the
library, beginning with the final theorems. -/

/-! ### Final theorems: the manuscript's schedule -/

/-- info: 'SparseHamiltonian.GateSchedule.gate_efficient_simulation_ms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.gate_efficient_simulation_ms

/-- info: 'SparseHamiltonian.GateSchedule.sel_simulation_ms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.sel_simulation_ms

/-- info: 'SparseHamiltonian.GateSchedule.sel_simulation_ms_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.sel_simulation_ms_signed

/-- info: 'SparseHamiltonian.GateSchedule.sel_simulation_ms_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.sel_simulation_ms_native

/-- info: 'SparseHamiltonian.GateSchedule.gate_efficient_time_simulation_ms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.gate_efficient_time_simulation_ms

/-- info: 'SparseHamiltonian.GateSchedule.sel_time_simulation_ms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.sel_time_simulation_ms

/-- info: 'SparseHamiltonian.GateSchedule.sel_time_simulation_ms_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.sel_time_simulation_ms_native

/-- info: 'SparseHamiltonian.GateSchedule.abstract_simulation_ms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.abstract_simulation_ms

/-- info: 'SparseHamiltonian.GateSchedule.abstract_simulation_ms_explicit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.abstract_simulation_ms_explicit

/-! ### Admissible filter depths -/

/-- info: 'SparseHamiltonian.GateSchedule.sharp_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.sharp_admissible

/-- info: 'SparseHamiltonian.GateSchedule.degree_pos_of_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.degree_pos_of_admissible

/-- info: 'SparseHamiltonian.GateSchedule.exists_precise_implementation_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.exists_precise_implementation_k

/-! ### The manuscript's filter depth -/

/-- info: 'SparseHamiltonian.GateSchedule.length_of_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.length_of_nat

/-- info: 'SparseHamiltonian.GateSchedule.degreeMs_of_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.degreeMs_of_nat

/-- info: 'SparseHamiltonian.GateSchedule.length_natCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.length_natCast

/-- info: 'SparseHamiltonian.GateSchedule.degreeMs_natCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.degreeMs_natCast

/-- info: 'SparseHamiltonian.GateSchedule.logb_4096_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.logb_4096_le

/-- info: 'SparseHamiltonian.GateSchedule.depthMs_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.depthMs_ge

/-- info: 'SparseHamiltonian.GateSchedule.depthMs_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.depthMs_lt

/-- info: 'SparseHamiltonian.GateSchedule.depthMs_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.depthMs_admissible

/-- info: 'SparseHamiltonian.GateSchedule.degreeMs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.degreeMs_le

/-! ### The sharp Cayley error -/

/-- info: 'SparseHamiltonian.GateSchedule.re_inner_skew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.re_inner_skew

/-- info: 'SparseHamiltonian.GateSchedule.skew_half_inverse_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.skew_half_inverse_norm_le_one

/-- info: 'SparseHamiltonian.GateSchedule.exp_real_smul_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.exp_real_smul_norm_le

/-- info: 'SparseHamiltonian.GateSchedule.hasDerivAt_sq_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.hasDerivAt_sq_mul

/-- info: 'SparseHamiltonian.GateSchedule.hasDerivAt_cube_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.hasDerivAt_cube_mul

/-- info: 'SparseHamiltonian.GateSchedule.cayley_aux_deriv1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.cayley_aux_deriv1

/-- info: 'SparseHamiltonian.GateSchedule.cayley_aux_deriv2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.cayley_aux_deriv2

/-- info: 'SparseHamiltonian.GateSchedule.cayley_exp_error_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.cayley_exp_error_sharp

/-- info: 'SparseHamiltonian.GateSchedule.cayley_power_exp_error_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.cayley_power_exp_error_sharp

/-- info: 'SparseHamiltonian.GateSchedule.hamiltonian_cayley_error_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.hamiltonian_cayley_error_sharp

/-! ### The exact-gate circuit for every admissible depth -/

/-- info: 'SparseHamiltonian.GateSchedule.fDeg_eq_fDegK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.fDeg_eq_fDegK

/-- info: 'SparseHamiltonian.GateSchedule.length_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.length_ge_one

/-- info: 'SparseHamiltonian.GateSchedule.fDegK_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.fDegK_pos

/-- info: 'SparseHamiltonian.GateSchedule.labLenK_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.labLenK_spec

/-- info: 'SparseHamiltonian.GateSchedule.labWtK_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.labWtK_mass

/-- info: 'SparseHamiltonian.GateSchedule.stepW_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.stepW_mul

/-- info: 'SparseHamiltonian.GateSchedule.stepW_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.stepW_nonneg

/-- info: 'SparseHamiltonian.GateSchedule.amp_error_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.amp_error_k

/-- info: 'SparseHamiltonian.GateSchedule.simRK_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.simRK_spec

/-- info: 'SparseHamiltonian.GateSchedule.simLK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.simLK

/-- info: 'SparseHamiltonian.GateSchedule.card_simWireK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.card_simWireK

/-- info: 'SparseHamiltonian.GateSchedule.gate_efficient_simulation_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.gate_efficient_simulation_k

/-! ### The manuscript's slot count -/

/-- info: 'SparseHamiltonian.GateSchedule.slotMs_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.slotMs_spec

/-- info: 'SparseHamiltonian.GateSchedule.mesh_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.mesh_budget

/-- info: 'SparseHamiltonian.GateSchedule.fDegK_kMs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.fDegK_kMs

/-! ### Over a finite gate set -/

/-- info: 'SparseHamiltonian.GateSchedule.sim_supplied_ms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.sim_supplied_ms

/-! ### The slot-dependent clock and the discretisation estimate -/

/-- info: 'SparseHamiltonian.GateSchedule.filter_precisionV_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.filter_precisionV_k

/-- info: 'SparseHamiltonian.GateSchedule.exists_precise_implementationV_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.exists_precise_implementationV_k

/-- info: 'SparseHamiltonian.GateSchedule.cayley_step_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.cayley_step_sharp

/-- info: 'SparseHamiltonian.GateSchedule.exp_selfAdjoint_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.exp_selfAdjoint_norm_le

/-- info: 'SparseHamiltonian.GateSchedule.cayley_evolution_error_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.cayley_evolution_error_sharp

/-- info: 'SparseHamiltonian.GateSchedule.hasDerivAt_duhamel_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.hasDerivAt_duhamel_bound

/-- info: 'SparseHamiltonian.GateSchedule.duhamel_step_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.duhamel_step_sharp

/-- info: 'SparseHamiltonian.GateSchedule.mesh_error_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.mesh_error_sharp

/-! ### The slot-selected circuit -/

/-- info: 'SparseHamiltonian.GateSchedule.ampT_error_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.ampT_error_k

/-- info: 'SparseHamiltonian.GateSchedule.simulationT_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.simulationT_k

/-- info: 'SparseHamiltonian.GateSchedule.propagator_error_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.propagator_error_k

/-- info: 'SparseHamiltonian.GateSchedule.timegrid_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.timegrid_budget

/-! ### Lemma `hs:lem:abstract`: the constant of `hs:eq:abstractcost` -/

/-- info: 'SparseHamiltonian.GateSchedule.logb_4096_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.logb_4096_eq

/-- info: 'SparseHamiltonian.GateSchedule.degreeMs_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSchedule.degreeMs_cost_le
