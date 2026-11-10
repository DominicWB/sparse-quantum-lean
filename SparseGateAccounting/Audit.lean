import SparseGateAccounting.Accounting
import SparseGateAccounting.Native
import SparseGateAccounting.Original

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover the theorems of the library. The report lists at most
`propext`, `Classical.choice` and `Quot.sound`. -/

/-- info: 'SparseHamiltonian.SparseGateAccounting.sbP_le_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.sbP_le_succ

/-- info: 'SparseHamiltonian.SparseGateAccounting.padUJ_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.padUJ_length

/-- info: 'SparseHamiltonian.SparseGateAccounting.abs_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.abs_clock

/-- info: 'SparseHamiltonian.SparseGateAccounting.dg_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.dg_pos

/-- info: 'SparseHamiltonian.SparseGateAccounting.synG_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.synG_le

/-- info: 'SparseHamiltonian.SparseGateAccounting.evolution_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.evolution_eq

/-- info: 'SparseHamiltonian.SparseGateAccounting.error_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.error_low

/-- info: 'SparseHamiltonian.SparseGateAccounting.normPad_energies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.normPad_energies

/-- info: 'SparseHamiltonian.SparseGateAccounting.normPad_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.normPad_range

/-- info: 'SparseHamiltonian.SparseGateAccounting.xi_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.xi_budget

/-- info: 'SparseHamiltonian.SparseGateAccounting.sparse_known_gates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.sparse_known_gates

/-- info: 'SparseHamiltonian.SparseGateAccounting.sparse_gate_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.sparse_gate_total

/-- info: 'SparseHamiltonian.SparseGateAccounting.sparse_gate_total_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.sparse_gate_total_signed

/-! ### The constructed controlled private circuit (`SparseGateAccounting.Native`) -/

/-- info: 'SparseHamiltonian.SparseGateAccounting.normPad_dec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.normPad_dec

/-- info: 'SparseHamiltonian.SparseGateAccounting.privOp_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.privOp_public

/-- info: 'SparseHamiltonian.SparseGateAccounting.privOp_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.privOp_calls

/-- info: 'SparseHamiltonian.SparseGateAccounting.privOp_gates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.privOp_gates

/-- info: 'SparseHamiltonian.SparseGateAccounting.normPad_zero_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.normPad_zero_slot

/-- info: 'SparseHamiltonian.SparseGateAccounting.privCirc_privOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.privCirc_privOK

/-- info: 'SparseHamiltonian.SparseGateAccounting.selGates_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.selGates_le

/-- info: 'SparseHamiltonian.SparseGateAccounting.privCirc_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.privCirc_spec

/-- info: 'SparseHamiltonian.SparseGateAccounting.exists_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.exists_arith

/-- info: 'SparseHamiltonian.SparseGateAccounting.sparse_gate_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.sparse_gate_native

/-- info: 'SparseHamiltonian.SparseGateAccounting.sparse_gate_native_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.sparse_gate_native_signed

/-- info: 'SparseHamiltonian.SparseGateAccounting.budget_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.budget_facts

/-- info: 'SparseHamiltonian.SparseGateAccounting.sparse_gate_constructed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.sparse_gate_constructed

/-! ### The schedule of the original sparsity (`SparseGateAccounting.Original`) -/

/-- info: 'SparseHamiltonian.SparseGateAccounting.padDataS_row_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.padDataS_row_covers

/-- info: 'SparseHamiltonian.SparseGateAccounting.padDataS_column_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.padDataS_column_covers

/-- info: 'SparseHamiltonian.SparseGateAccounting.prims_normS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.prims_normS

/-- info: 'SparseHamiltonian.SparseGateAccounting.normS_energies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.normS_energies

/-- info: 'SparseHamiltonian.SparseGateAccounting.normS_zero_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.normS_zero_slot

/-- info: 'SparseHamiltonian.SparseGateAccounting.hadUJ_prep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.hadUJ_prep

/-- info: 'SparseHamiltonian.SparseGateAccounting.boundary_lift_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.boundary_lift_of

/-- info: 'SparseHamiltonian.SparseGateAccounting.R1bin_boundary_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.R1bin_boundary_of

/-- info: 'SparseHamiltonian.SparseGateAccounting.R1bin_endpoint_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.R1bin_endpoint_of

/-- info: 'SparseHamiltonian.SparseGateAccounting.abs_clockS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.abs_clockS

/-- info: 'SparseHamiltonian.SparseGateAccounting.dgS_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.dgS_pos

/-- info: 'SparseHamiltonian.SparseGateAccounting.evolutionS_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.evolutionS_eq

/-- info: 'SparseHamiltonian.SparseGateAccounting.sparse_gate_total_s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.sparse_gate_total_s

/-- info: 'SparseHamiltonian.SparseGateAccounting.sparse_gate_total_signed_s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.sparse_gate_total_signed_s

/-- info: 'SparseHamiltonian.SparseGateAccounting.normS_dec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.normS_dec

/-- info: 'SparseHamiltonian.SparseGateAccounting.privOpS_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.privOpS_public

/-- info: 'SparseHamiltonian.SparseGateAccounting.privOpS_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.privOpS_calls

/-- info: 'SparseHamiltonian.SparseGateAccounting.privOpS_gates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.privOpS_gates

/-- info: 'SparseHamiltonian.SparseGateAccounting.privCircS_privOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.privCircS_privOK

/-- info: 'SparseHamiltonian.SparseGateAccounting.privCircS_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.privCircS_spec

/-- info: 'SparseHamiltonian.SparseGateAccounting.exists_arithS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.exists_arithS

/-- info: 'SparseHamiltonian.SparseGateAccounting.padUJ_prep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.padUJ_prep

/-- info: 'SparseHamiltonian.SparseGateAccounting.sparse_gate_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.sparse_gate_original

/-- info: 'SparseHamiltonian.SparseGateAccounting.sparse_gate_original_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseGateAccounting.sparse_gate_original_signed
