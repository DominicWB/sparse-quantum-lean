import GateEfficientBinaryTime.Slot
import GateEfficientBinaryTime.Oracles
import GateEfficientBinaryTime.Simulation
import GateEfficientBinaryTime.Budget

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 2 lemmas, whose reports list a
strict subset of these three axioms (one of them none). The audits cover every
theorem of the library of the time-dependent gate-level construction from binary
data, beginning with the time-dependent part of Theorem `hs:thm:gates` for
time-indexed binary sparse oracles.
-/

/-! ### The time-dependent part of Theorem `hs:thm:gates` from binary data -/

/-- info: 'SparseHamiltonian.GateBinary.binary_time_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.binary_time_simulation

/-- info: 'SparseHamiltonian.GateBinary.binary_time_simulation_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.binary_time_simulation_budget

/-- info: 'SparseHamiltonian.GateBinary.compressed_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.compressed_eq_smul

/-- info: 'SparseHamiltonian.GateBinary.Hbin_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Hbin_eq_smul

/-- info: 'SparseHamiltonian.GateBinary.DbinT_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.DbinT_word

/-! ### The slot-selected native identity from time-indexed binary oracles -/

/-- info: 'SparseHamiltonian.GateBinary.primsT_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.primsT_isUnitary

/-- info: 'SparseHamiltonian.GateBinary.sparseOpT_dec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.sparseOpT_dec

/-- info: 'SparseHamiltonian.GateBinary.sparseOpT_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.sparseOpT_public

/-- info: 'SparseHamiltonian.GateBinary.computeVT_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.computeVT_nGates

/-- info: 'SparseHamiltonian.GateBinary.computeVT_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.computeVT_nCalls

/-- info: 'SparseHamiltonian.GateBinary.sparse_nativeOK_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.sparse_nativeOK_time

/-! ### Slot-selected native operations from per-slot ones -/

/-- info: 'SparseHamiltonian.GateBinary.baseW_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.baseW_injective

/-- info: 'SparseHamiltonian.GateBinary.selW_ne_baseW' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.selW_ne_baseW

/-- info: 'SparseHamiltonian.GateBinary.adjIf_localOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.adjIf_localOp

/-- info: 'SparseHamiltonian.GateBinary.localOp_condOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.localOp_condOp

/-- info: 'SparseHamiltonian.GateBinary.slotPrim_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.slotPrim_isUnitary

/-- info: 'SparseHamiltonian.GateBinary.slotOf_clearCfg_baseW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.slotOf_clearCfg_baseW

/-- info: 'SparseHamiltonian.GateBinary.eval_slotInstr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.eval_slotInstr

/-- info: 'SparseHamiltonian.GateBinary.nrun_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.nrun_slot

/-- info: 'SparseHamiltonian.GateBinary.Rdec_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Rdec_slot

/-- info: 'SparseHamiltonian.GateBinary.selSlice_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.selSlice_apply

/-- info: 'SparseHamiltonian.GateBinary.slice_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.slice_cleanEmb

/-- info: 'SparseHamiltonian.GateBinary.nativeOK_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.nativeOK_slot

/-- info: 'SparseHamiltonian.GateBinary.nGatesN_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.nGatesN_slot

/-- info: 'SparseHamiltonian.GateBinary.nCallsN_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.nCallsN_slot

/-- info: 'SparseHamiltonian.GateBinary.valid_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.valid_slot

/-- info: 'SparseHamiltonian.GateBinary.slot_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.slot_public
