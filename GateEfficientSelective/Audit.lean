import GateEfficientSelective.Compiler
import GateEfficientSelective.Prep
import GateEfficientSelective.Sources
import GateEfficientSelective.ODESolver
import GateEfficientSelective.ODEBudget
import GateEfficientSelective.Nodes
import GateEfficientSelective.HamMacro
import GateEfficientSelective.HamSim
import GateEfficientSelective.HamBridge

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 4 lemmas about the wire map
joining the synthesis ancillas to the scratch wires, whose reports list a subset
of these three axioms. The audits cover every theorem of the library, beginning
with the final theorems. -/

/-! ### Final theorems: retained supplied circuits over a finite gate set -/

/-- info: 'SparseHamiltonian.GateSelective.sel_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.sel_simulation

/-- info: 'SparseHamiltonian.GateSelective.sel_simulation_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.sel_simulation_signed

/-- info: 'SparseHamiltonian.GateSelective.sel_time_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.sel_time_simulation

/-- info: 'SparseHamiltonian.GateSelective.sel_simulation_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.sel_simulation_native

/-- info: 'SparseHamiltonian.GateSelective.sel_time_simulation_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.sel_time_simulation_native

/-- info: 'SparseHamiltonian.GateSelective.native_ode_solver_sel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.native_ode_solver_sel

/-- info: 'SparseHamiltonian.GateSelective.native_ode_time_solver_sel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.native_ode_time_solver_sel

/-- info: 'SparseHamiltonian.GateSelective.native_time_sel_outcomeBI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.native_time_sel_outcomeBI

/-- info: 'SparseHamiltonian.GateSelective.native_time_sel_outcomeB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.native_time_sel_outcomeB

/-- info: 'SparseHamiltonian.GateSelective.binary_ode_budget_sel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.binary_ode_budget_sel

/-- info: 'SparseHamiltonian.GateSelective.binary_ode_time_budget_sel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.binary_ode_time_budget_sel

/-- info: 'SparseHamiltonian.GateSelective.binary_nodes_solver_sel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.binary_nodes_solver_sel

/-- info: 'SparseHamiltonian.GateSelective.binary_nodes_budget_sel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.binary_nodes_budget_sel

/-! ### The selective compiler -/

/-- info: 'SparseHamiltonian.GateSelective.synB_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.synB_gate

/-- info: 'SparseHamiltonian.GateSelective.keepB_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.keepB_gate

/-- info: 'SparseHamiltonian.GateSelective.nSynN_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_nil

/-- info: 'SparseHamiltonian.GateSelective.nKeepN_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nKeepN_nil

/-- info: 'SparseHamiltonian.GateSelective.nSynN_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_append

/-- info: 'SparseHamiltonian.GateSelective.nKeepN_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nKeepN_append

/-- info: 'SparseHamiltonian.GateSelective.nSynN_cons_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_cons_gate

/-- info: 'SparseHamiltonian.GateSelective.nKeepN_cons_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nKeepN_cons_gate

/-- info: 'SparseHamiltonian.GateSelective.nSynN_cons_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_cons_call

/-- info: 'SparseHamiltonian.GateSelective.nKeepN_cons_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nKeepN_cons_call

/-- info: 'SparseHamiltonian.GateSelective.nKeepN_add_nSynN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nKeepN_add_nSynN

/-- info: 'SparseHamiltonian.GateSelective.nSynN_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_le

/-- info: 'SparseHamiltonian.GateSelective.nKeepN_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nKeepN_le

/-- info: 'SparseHamiltonian.GateSelective.nSynN_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_eq_zero

/-- info: 'SparseHamiltonian.GateSelective.nKeepN_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nKeepN_eq

/-- info: 'SparseHamiltonian.GateSelective.nSynN_flatMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_flatMap

/-- info: 'SparseHamiltonian.GateSelective.nKeepN_flatMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nKeepN_flatMap

/-- info: 'SparseHamiltonian.GateSelective.gateOf_map_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.gateOf_map_iff

/-- info: 'SparseHamiltonian.GateSelective.nSynN_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_map

/-- info: 'SparseHamiltonian.GateSelective.nKeepN_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nKeepN_map

/-- info: 'SparseHamiltonian.GateSelective.gateOf_inv_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.gateOf_inv_iff

/-- info: 'SparseHamiltonian.GateSelective.nSynN_cons_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_cons_inv

/-- info: 'SparseHamiltonian.GateSelective.nSynN_ninv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_ninv

/-- info: 'SparseHamiltonian.GateSelective.nKeepN_ninv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nKeepN_ninv

/-- info: 'SparseHamiltonian.GateSelective.nSynN_nGatesOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_nGatesOf

/-- info: 'SparseHamiltonian.GateSelective.selRep_kept' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selRep_kept

/-- info: 'SparseHamiltonian.GateSelective.selRep_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selRep_synth

/-- info: 'SparseHamiltonian.GateSelective.selRep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selRep_spec

/-- info: 'SparseHamiltonian.GateSelective.selRep_approxOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selRep_approxOn

/-- info: 'SparseHamiltonian.GateSelective.replace_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.replace_append

/-- info: 'SparseHamiltonian.GateSelective.selC_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selC_append

/-- info: 'SparseHamiltonian.GateSelective.selC_retained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selC_retained

/-- info: 'SparseHamiltonian.GateSelective.mem_selC_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.mem_selC_gate

/-- info: 'SparseHamiltonian.GateSelective.nGatesN_selC_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nGatesN_selC_le

/-- info: 'SparseHamiltonian.GateSelective.selC_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selC_spec

/-- info: 'SparseHamiltonian.GateSelective.selC_approxOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selC_approxOn

/-- info: 'SparseHamiltonian.GateSelective.selC_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selC_error

/-- info: 'SparseHamiltonian.GateSelective.selBudget_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selBudget_spec

/-- info: 'SparseHamiltonian.GateSelective.selBudget_approxOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selBudget_approxOn

/-- info: 'SparseHamiltonian.GateSelective.selBudget_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selBudget_error

/-- info: 'SparseHamiltonian.GateSelective.selBudget_gates_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selBudget_gates_log

/-- info: 'SparseHamiltonian.GateSelective.ninv_gateOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.ninv_gateOf

/-- info: 'SparseHamiltonian.GateSelective.selC_inv_gateOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selC_inv_gateOf

/-! ### The selective preparation and the supplied source circuits -/

/-- info: 'SparseHamiltonian.GateSelective.selPrep_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selPrep_valid

/-- info: 'SparseHamiltonian.GateSelective.selPrep_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selPrep_counts

/-- info: 'SparseHamiltonian.GateSelective.selPrep_gateOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selPrep_gateOf

/-- info: 'SparseHamiltonian.GateSelective.selPrep_inv_gateOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selPrep_inv_gateOf

/-- info: 'SparseHamiltonian.GateSelective.selPrep_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selPrep_pres

/-- info: 'SparseHamiltonian.GateSelective.trialSel_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.trialSel_valid

/-- info: 'SparseHamiltonian.GateSelective.trialSel_gateOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.trialSel_gateOf

/-- info: 'SparseHamiltonian.GateSelective.selPrep_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selPrep_approx

/-- info: 'SparseHamiltonian.GateSelective.sel_noutcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.sel_noutcome

/-- info: 'SparseHamiltonian.GateSelective.sel_protocol_worst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.sel_protocol_worst

/-- info: 'SparseHamiltonian.GateSelective.sel_protocol_worst_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.sel_protocol_worst_log

/-- info: 'SparseHamiltonian.GateSelective.nSynN_omacro_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_omacro_le

/-- info: 'SparseHamiltonian.GateSelective.nSynN_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_placed

/-- info: 'SparseHamiltonian.GateSelective.nSynN_nprepC_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_nprepC_le

/-- info: 'SparseHamiltonian.GateSelective.nSynN_tnprepC_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_tnprepC_le

/-! ### The released correctness arguments for every compiled preparation -/

/-- info: 'SparseHamiltonian.GateSelective.const_outcome_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.const_outcome_of

/-- info: 'SparseHamiltonian.GateSelective.time_outcome_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.time_outcome_of

/-- info: 'SparseHamiltonian.GateSelective.timeC_outcome_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.timeC_outcome_of

/-- info: 'SparseHamiltonian.GateSelective.sep_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.sep_arith

/-! ### The budgets in the word budget -/

/-- info: 'SparseHamiltonian.GateSelective.sep_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.sep_mono

/-- info: 'SparseHamiltonian.GateSelective.nGatesN_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nGatesN_empty

/-- info: 'SparseHamiltonian.GateSelective.prepBound_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.prepBound_split

/-- info: 'SparseHamiltonian.GateSelective.prepBoundT_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.prepBoundT_split

/-- info: 'SparseHamiltonian.GateSelective.prepBoundN_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.prepBoundN_split

/-! ### Native Hamiltonian macros with a supplied private circuit -/

/-- info: 'SparseHamiltonian.GateSelective.ctrlIdeal_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.ctrlIdeal_isUnitary

/-- info: 'SparseHamiltonian.GateSelective.ctrlIdeal_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.ctrlIdeal_preserves

/-- info: 'SparseHamiltonian.GateSelective.ctrl_inv_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.ctrl_inv_approx

/-- info: 'SparseHamiltonian.GateSelective.hmacroP_privMacro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.hmacroP_privMacro

/-- info: 'SparseHamiltonian.GateSelective.hcircP_privMacro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.hcircP_privMacro

/-- info: 'SparseHamiltonian.GateSelective.hmacroP_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.hmacroP_valid

/-- info: 'SparseHamiltonian.GateSelective.hcircP_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.hcircP_valid

/-- info: 'SparseHamiltonian.GateSelective.hmacroP_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.hmacroP_nCalls

/-- info: 'SparseHamiltonian.GateSelective.hcircP_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.hcircP_nCalls

/-- info: 'SparseHamiltonian.GateSelective.hmacroP_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.hmacroP_nGates

/-- info: 'SparseHamiltonian.GateSelective.hcircP_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.hcircP_nGates

/-- info: 'SparseHamiltonian.GateSelective.hmacroP_nil_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.hmacroP_nil_nGates

/-- info: 'SparseHamiltonian.GateSelective.hcircP_nil_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.hcircP_nil_nGates

/-- info: 'SparseHamiltonian.GateSelective.nSynN_hcircP_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_hcircP_le

/-- info: 'SparseHamiltonian.GateSelective.hmacroP_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.hmacroP_approx

/-- info: 'SparseHamiltonian.GateSelective.hcircP_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.hcircP_approx

/-- info: 'SparseHamiltonian.GateSelective.hcircP_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.hcircP_error

/-! ### The Hamiltonian endpoints -/

/-- info: 'SparseHamiltonian.GateSelective.sel_count_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.sel_count_arith

/-- info: 'SparseHamiltonian.GateSelective.selBudget_error_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.selBudget_error_of

/-- info: 'SparseHamiltonian.GateSelective.sim_supplied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.sim_supplied

/-! ### The finite-set private circuit from the native data -/

/-- info: 'SparseHamiltonian.GateSelective.approxOn_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.approxOn_restrict

/-- info: 'SparseHamiltonian.GateSelective.approxOn_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.approxOn_trans

/-- info: 'SparseHamiltonian.GateSelective.reW_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.reW_injective

/-- info: 'SparseHamiltonian.GateSelective.rePW_inl_selPR' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.rePW_inl_selPR

/-- info: 'SparseHamiltonian.GateSelective.rePW_inl_enW' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.rePW_inl_enW

/-- info: 'SparseHamiltonian.GateSelective.enW_ne_selPR' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.enW_ne_selPR

/-- info: 'SparseHamiltonian.GateSelective.localOp_rePW_liftB_ctrlIdeal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.localOp_rePW_liftB_ctrlIdeal

/-- info: 'SparseHamiltonian.GateSelective.nSynN_privMacro_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.nSynN_privMacro_le

/-- info: 'SparseHamiltonian.GateSelective.privSel_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelective.privSel_spec
