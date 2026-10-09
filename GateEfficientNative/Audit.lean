import GateEfficientNative.Corollaries

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 27 lemmas, whose reports list a
subset of these three axioms (or none). The audits cover every theorem of the
native gate-efficient library, beginning with the final theorems for Hamiltonian
simulation and for dissipative ODEs and their public and polynomial gate counts. -/

/-! ### Final theorems, public and polynomial counts, and the native solvers -/

/-- info: 'SparseHamiltonian.GateNative.native_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.native_simulation

/-- info: 'SparseHamiltonian.GateNative.native_simulation_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.native_simulation_signed

/-- info: 'SparseHamiltonian.GateNative.native_time_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.native_time_simulation

/-- info: 'SparseHamiltonian.GateNative.native_ode_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.native_ode_solver

/-- info: 'SparseHamiltonian.GateNative.native_ode_time_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.native_ode_time_solver

/-- info: 'SparseHamiltonian.GateNative.nativeSim_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nativeSim_counts

/-- info: 'SparseHamiltonian.GateNative.native_sparse_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.native_sparse_counts

/-- info: 'SparseHamiltonian.GateNative.native_ode_gate_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.native_ode_gate_count

/-- info: 'SparseHamiltonian.GateNative.native_ode_time_gate_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.native_ode_time_gate_count

/-- info: 'SparseHamiltonian.GateNative.simCircuit_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.simCircuit_counts

/-- info: 'SparseHamiltonian.GateNative.pow_simM_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.pow_simM_lt

/-- info: 'SparseHamiltonian.GateNative.ode_gate_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ode_gate_arith

/-- info: 'SparseHamiltonian.GateNative.ode_time_gate_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ode_time_gate_arith

/-- info: 'SparseHamiltonian.GateNative.wireRel_sec' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.wireRel_sec

/-- info: 'SparseHamiltonian.GateNative.ctrlOK_sec' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ctrlOK_sec

/-- info: 'SparseHamiltonian.GateNative.evalSel_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.evalSel_const

/-- info: 'SparseHamiltonian.GateNative.prodOps_evalSel_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.prodOps_evalSel_const

/-- info: 'SparseHamiltonian.GateNative.evalSel_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.evalSel_slot

/-- info: 'SparseHamiltonian.GateNative.prodOps_evalSel_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.prodOps_evalSel_slot

/-- info: 'SparseHamiltonian.GateNative.regIsTopologicalRing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.regIsTopologicalRing

/-- info: 'SparseHamiltonian.GateNative.err_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.err_neg

/-- info: 'SparseHamiltonian.GateNative.labEmbFun_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.labEmbFun_injective

/-- info: 'SparseHamiltonian.GateNative.ctrlOK_secW' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ctrlOK_secW

/-- info: 'SparseHamiltonian.GateNative.ode_oracle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ode_oracle_eq

/-- info: 'SparseHamiltonian.GateNative.ode_eval_uj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ode_eval_uj

/-- info: 'SparseHamiltonian.GateNative.ode_eval_priv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ode_eval_priv

/-- info: 'SparseHamiltonian.GateNative.conj_pctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.conj_pctl

/-- info: 'SparseHamiltonian.GateNative.srcIdeal_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.srcIdeal_isUnitary

/-- info: 'SparseHamiltonian.GateNative.srcIdeal_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.srcIdeal_adjoint

/-- info: 'SparseHamiltonian.GateNative.srcPlFun_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.srcPlFun_injective

/-- info: 'SparseHamiltonian.GateNative.liftB_conj_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.liftB_conj_src

/-- info: 'SparseHamiltonian.GateNative.liftB_conj_eval_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.liftB_conj_eval_src

/-- info: 'SparseHamiltonian.GateNative.osec_prepC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.osec_prepC

/-- info: 'SparseHamiltonian.GateNative.noseed_prepC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.noseed_prepC

/-- info: 'SparseHamiltonian.GateNative.prodOps_oeval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.prodOps_oeval

/-- info: 'SparseHamiltonian.GateNative.srcMacro_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.srcMacro_approx

/-- info: 'SparseHamiltonian.GateNative.srcMacro_not_touches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.srcMacro_not_touches

/-- info: 'SparseHamiltonian.GateNative.srcMacro_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.srcMacro_valid

/-- info: 'SparseHamiltonian.GateNative.srcMacro_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.srcMacro_counts

/-- info: 'SparseHamiltonian.GateNative.tselFun_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.tselFun_injective

/-- info: 'SparseHamiltonian.GateNative.ode_slot_oracle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ode_slot_oracle_eq

/-- info: 'SparseHamiltonian.GateNative.tode_eval_uj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.tode_eval_uj

/-- info: 'SparseHamiltonian.GateNative.tode_eval_priv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.tode_eval_priv

/-- info: 'SparseHamiltonian.GateNative.conj_psel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.conj_psel

/-- info: 'SparseHamiltonian.GateNative.conj_matOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.conj_matOp

/-- info: 'SparseHamiltonian.GateNative.loadPlFun_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.loadPlFun_injective

/-- info: 'SparseHamiltonian.GateNative.wpPlFun_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.wpPlFun_injective

/-- info: 'SparseHamiltonian.GateNative.loadIdeal_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.loadIdeal_isUnitary

/-- info: 'SparseHamiltonian.GateNative.loadIdeal_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.loadIdeal_adjoint

/-- info: 'SparseHamiltonian.GateNative.liftB_conj_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.liftB_conj_load

/-- info: 'SparseHamiltonian.GateNative.liftB_conj_wprep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.liftB_conj_wprep

/-- info: 'SparseHamiltonian.GateNative.osec_tprepC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.osec_tprepC

/-- info: 'SparseHamiltonian.GateNative.noseed_tprepC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.noseed_tprepC

/-- info: 'SparseHamiltonian.GateNative.prodOps_teval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.prodOps_teval

/-- info: 'SparseHamiltonian.GateNative.tsrcMacro_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.tsrcMacro_approx

/-- info: 'SparseHamiltonian.GateNative.tsrcMacro_not_touches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.tsrcMacro_not_touches

/-- info: 'SparseHamiltonian.GateNative.tsrcMacro_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.tsrcMacro_valid

/-- info: 'SparseHamiltonian.GateNative.tsrcMacro_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.tsrcMacro_counts

/-- info: 'SparseHamiltonian.GateNative.tnprepC_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.tnprepC_valid

/-- info: 'SparseHamiltonian.GateNative.tnprepC_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.tnprepC_pres

/-- info: 'SparseHamiltonian.GateNative.native_time_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.native_time_outcome

/-! ### Native instructions: runs, inverses, renaming and counts -/

/-- info: 'SparseHamiltonian.GateNative.NInstr.isGate_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.NInstr.isGate_inv

/-- info: 'SparseHamiltonian.GateNative.NInstr.isCall_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.NInstr.isCall_inv

/-- info: 'SparseHamiltonian.GateNative.NInstr.isGate_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.NInstr.isGate_map

/-- info: 'SparseHamiltonian.GateNative.NInstr.isCall_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.NInstr.isCall_map

/-- info: 'SparseHamiltonian.GateNative.NInstr.valid_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.NInstr.valid_inv

/-- info: 'SparseHamiltonian.GateNative.NInstr.valid_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.NInstr.valid_map

/-- info: 'SparseHamiltonian.GateNative.NInstr.eval_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.NInstr.eval_gate

/-- info: 'SparseHamiltonian.GateNative.NInstr.eval_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.NInstr.eval_call

/-- info: 'SparseHamiltonian.GateNative.NInstr.eval_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.NInstr.eval_inv

/-- info: 'SparseHamiltonian.GateNative.NInstr.eval_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.NInstr.eval_isUnitary

/-- info: 'SparseHamiltonian.GateNative.nrun_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nrun_nil

/-- info: 'SparseHamiltonian.GateNative.nrun_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nrun_cons

/-- info: 'SparseHamiltonian.GateNative.nrun_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nrun_append

/-- info: 'SparseHamiltonian.GateNative.nrun_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nrun_singleton

/-- info: 'SparseHamiltonian.GateNative.nrun_ninv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nrun_ninv

/-- info: 'SparseHamiltonian.GateNative.ninv_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ninv_append

/-- info: 'SparseHamiltonian.GateNative.ninv_ninv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ninv_ninv

/-- info: 'SparseHamiltonian.GateNative.nrun_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nrun_isUnitary

/-- info: 'SparseHamiltonian.GateNative.valid_ninv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.valid_ninv

/-- info: 'SparseHamiltonian.GateNative.nrun_nGatesOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nrun_nGatesOf

/-- info: 'SparseHamiltonian.GateNative.nGatesOf_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nGatesOf_append

/-- info: 'SparseHamiltonian.GateNative.valid_nGatesOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.valid_nGatesOf

/-- info: 'SparseHamiltonian.GateNative.ninv_nGatesOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ninv_nGatesOf

/-- info: 'SparseHamiltonian.GateNative.NInstr.eval_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.NInstr.eval_map

/-- info: 'SparseHamiltonian.GateNative.nrun_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nrun_map

/-- info: 'SparseHamiltonian.GateNative.valid_map_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.valid_map_list

/-- info: 'SparseHamiltonian.GateNative.ninv_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ninv_map

/-- info: 'SparseHamiltonian.GateNative.nGatesN_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nGatesN_append

/-- info: 'SparseHamiltonian.GateNative.nCallsN_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nCallsN_append

/-- info: 'SparseHamiltonian.GateNative.nGatesN_ninv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nGatesN_ninv

/-- info: 'SparseHamiltonian.GateNative.nCallsN_ninv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nCallsN_ninv

/-- info: 'SparseHamiltonian.GateNative.nGatesN_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nGatesN_map

/-- info: 'SparseHamiltonian.GateNative.nCallsN_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nCallsN_map

/-- info: 'SparseHamiltonian.GateNative.nGatesN_nGatesOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nGatesN_nGatesOf

/-- info: 'SparseHamiltonian.GateNative.nCallsN_nGatesOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nCallsN_nGatesOf

/-- info: 'SparseHamiltonian.GateNative.nGatesN_flatMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nGatesN_flatMap

/-- info: 'SparseHamiltonian.GateNative.nCallsN_flatMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nCallsN_flatMap

/-- info: 'SparseHamiltonian.GateNative.nGatesN_replicate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nGatesN_replicate

/-- info: 'SparseHamiltonian.GateNative.nCallsN_replicate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nCallsN_replicate

/-! ### The full-output calculus, flattening and untouched wires -/

/-- info: 'SparseHamiltonian.GateNative.clearCfg_apply_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.clearCfg_apply_out

/-- info: 'SparseHamiltonian.GateNative.clearCfg_apply_ι' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.clearCfg_apply_ι

/-- info: 'SparseHamiltonian.GateNative.ApproxOn.of_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ApproxOn.of_agrees

/-- info: 'SparseHamiltonian.GateNative.ApproxOn.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ApproxOn.mono

/-- info: 'SparseHamiltonian.GateNative.ApproxOn.congr_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ApproxOn.congr_left

/-- info: 'SparseHamiltonian.GateNative.ApproxOn.congr_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ApproxOn.congr_right

/-- info: 'SparseHamiltonian.GateNative.ApproxOn.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ApproxOn.comp

/-- info: 'SparseHamiltonian.GateNative.ApproxOn.adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ApproxOn.adjoint

/-- info: 'SparseHamiltonian.GateNative.norm_comp_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.norm_comp_sub_le

/-- info: 'SparseHamiltonian.GateNative.supp_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.supp_slice

/-- info: 'SparseHamiltonian.GateNative.agrees_localOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.agrees_localOp

/-- info: 'SparseHamiltonian.GateNative.norm_sq_eq_sum_slices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.norm_sq_eq_sum_slices

/-- info: 'SparseHamiltonian.GateNative.approxOn_localOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.approxOn_localOp

/-- info: 'SparseHamiltonian.GateNative.preserves_localOp'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.preserves_localOp'

/-- info: 'SparseHamiltonian.GateNative.IsUnitary.norm_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.IsUnitary.norm_apply_le

/-- info: 'SparseHamiltonian.GateNative.flat_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.flat_apply

/-- info: 'SparseHamiltonian.GateNative.flat_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.flat_symm_apply

/-- info: 'SparseHamiltonian.GateNative.fl_unfl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.fl_unfl

/-- info: 'SparseHamiltonian.GateNative.unfl_fl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.unfl_fl

/-- info: 'SparseHamiltonian.GateNative.fl_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.fl_adjoint

/-- info: 'SparseHamiltonian.GateNative.conj_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.conj_comp

/-- info: 'SparseHamiltonian.GateNative.conj_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.conj_one

/-- info: 'SparseHamiltonian.GateNative.conj_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.conj_adjoint

/-- info: 'SparseHamiltonian.GateNative.conj_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.conj_isUnitary

/-- info: 'SparseHamiltonian.GateNative.conj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.conj_apply

/-- info: 'SparseHamiltonian.GateNative.conj_gateOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.conj_gateOp

/-- info: 'SparseHamiltonian.GateNative.mapId_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.mapId_injective

/-- info: 'SparseHamiltonian.GateNative.overwrite_mapId' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.overwrite_mapId

/-- info: 'SparseHamiltonian.GateNative.clearCfg_mapId' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.clearCfg_mapId

/-- info: 'SparseHamiltonian.GateNative.conj_localOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.conj_localOp

/-- info: 'SparseHamiltonian.GateNative.cleanEmb_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.cleanEmb_apply

/-- info: 'SparseHamiltonian.GateNative.supp_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.supp_cleanEmb

/-- info: 'SparseHamiltonian.GateNative.norm_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.norm_cleanEmb

/-- info: 'SparseHamiltonian.GateNative.liftB_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.liftB_comp

/-- info: 'SparseHamiltonian.GateNative.liftB_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.liftB_one

/-- info: 'SparseHamiltonian.GateNative.liftB_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.liftB_adjoint

/-- info: 'SparseHamiltonian.GateNative.liftB_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.liftB_isUnitary

/-- info: 'SparseHamiltonian.GateNative.overwrite_inl_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.overwrite_inl_inr

/-- info: 'SparseHamiltonian.GateNative.preserves_liftB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.preserves_liftB

/-- info: 'SparseHamiltonian.GateNative.pres2_liftB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.pres2_liftB

/-- info: 'SparseHamiltonian.GateNative.liftB_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.liftB_cleanEmb

/-- info: 'SparseHamiltonian.GateNative.norm_sub_cleanEmb_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.norm_sub_cleanEmb_le

/-- info: 'SparseHamiltonian.GateNative.NInstr.touches_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.NInstr.touches_inv

/-- info: 'SparseHamiltonian.GateNative.NInstr.not_touches_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.NInstr.not_touches_map

/-- info: 'SparseHamiltonian.GateNative.preserves_eval_zeroOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.preserves_eval_zeroOn

/-- info: 'SparseHamiltonian.GateNative.preserves_nrun_zeroOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.preserves_nrun_zeroOn

/-- info: 'SparseHamiltonian.GateNative.pres2_nrun_zeroOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.pres2_nrun_zeroOn

/-! ### The edge rotation and the bit-controlled rotation circuit -/

/-- info: 'SparseHamiltonian.GateNative.real_cos_two_arctan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.real_cos_two_arctan

/-- info: 'SparseHamiltonian.GateNative.real_sin_two_arctan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.real_sin_two_arctan

/-- info: 'SparseHamiltonian.GateNative.edgeMat_eq_angMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.edgeMat_eq_angMat

/-- info: 'SparseHamiltonian.GateNative.rzMat_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rzMat_mul

/-- info: 'SparseHamiltonian.GateNative.rzMat_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rzMat_zero

/-- info: 'SparseHamiltonian.GateNative.rxMat_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rxMat_mul

/-- info: 'SparseHamiltonian.GateNative.rxMat_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rxMat_zero

/-- info: 'SparseHamiltonian.GateNative.angMat_eq_rot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.angMat_eq_rot

/-- info: 'SparseHamiltonian.GateNative.unitaryMat_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.unitaryMat_mul

/-- info: 'SparseHamiltonian.GateNative.rzMat_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rzMat_conjTranspose

/-- info: 'SparseHamiltonian.GateNative.rzMat_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rzMat_unitary

/-- info: 'SparseHamiltonian.GateNative.rxMat_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rxMat_conjTranspose

/-- info: 'SparseHamiltonian.GateNative.rxMat_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rxMat_unitary

/-- info: 'SparseHamiltonian.GateNative.neg_one_unitaryMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.neg_one_unitaryMat

/-- info: 'SparseHamiltonian.GateNative.frob2_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.frob2_nonneg

/-- info: 'SparseHamiltonian.GateNative.norm_exp_sub_exp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.norm_exp_sub_exp_le

/-- info: 'SparseHamiltonian.GateNative.frob2_angMat_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.frob2_angMat_sub_le

/-- info: 'SparseHamiltonian.GateNative.matOp_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.matOp_sub

/-- info: 'SparseHamiltonian.GateNative.qubitMat_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.qubitMat_sub

/-- info: 'SparseHamiltonian.GateNative.norm_matOp_qubitMat_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.norm_matOp_qubitMat_le

/-- info: 'SparseHamiltonian.GateNative.norm_condOp_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.norm_condOp_sub_le

/-- info: 'SparseHamiltonian.GateNative.rotGates_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rotGates_length

/-- info: 'SparseHamiltonian.GateNative.gRun_same_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.gRun_same_target

/-- info: 'SparseHamiltonian.GateNative.selProd_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.selProd_append

/-- info: 'SparseHamiltonian.GateNative.selProd_rz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.selProd_rz

/-- info: 'SparseHamiltonian.GateNative.selProd_rx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.selProd_rx

/-- info: 'SparseHamiltonian.GateNative.rotGates_targets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rotGates_targets

/-- info: 'SparseHamiltonian.GateNative.gRun_rotGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.gRun_rotGates

/-- info: 'SparseHamiltonian.GateNative.rotGates_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rotGates_ok

/-! ### The native private Cayley operation, selection and lifting -/

/-- info: 'SparseHamiltonian.GateNative.privMacro_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.privMacro_nGates

/-- info: 'SparseHamiltonian.GateNative.privMacro_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.privMacro_nCalls

/-- info: 'SparseHamiltonian.GateNative.classical_map_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.classical_map_ok

/-- info: 'SparseHamiltonian.GateNative.privMacro_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.privMacro_valid

/-- info: 'SparseHamiltonian.GateNative.put_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.put_bas

/-- info: 'SparseHamiltonian.GateNative.localOp_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.localOp_bas

/-- info: 'SparseHamiltonian.GateNative.gRun_map_gates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.gRun_map_gates

/-- info: 'SparseHamiltonian.GateNative.localOp_ite_condOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.localOp_ite_condOp

/-- info: 'SparseHamiltonian.GateNative.Arith.out_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.Arith.out_update

/-- info: 'SparseHamiltonian.GateNative.arOut_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.arOut_update

/-- info: 'SparseHamiltonian.GateNative.arith_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.arith_bas

/-- info: 'SparseHamiltonian.GateNative.arith_rot_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.arith_rot_agrees

/-- info: 'SparseHamiltonian.GateNative.Rtil_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.Rtil_approx

/-- info: 'SparseHamiltonian.GateNative.Rid_eq_localOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.Rid_eq_localOp

/-- info: 'SparseHamiltonian.GateNative.eq_cleanEmb_of_supp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.eq_cleanEmb_of_supp

/-- info: 'SparseHamiltonian.GateNative.agrees_of_nativeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.agrees_of_nativeOK

/-- info: 'SparseHamiltonian.GateNative.native_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.native_agrees

/-- info: 'SparseHamiltonian.GateNative.privMacro_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.privMacro_approx

/-- info: 'SparseHamiltonian.GateNative.ctrlIdeal_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ctrlIdeal_adjoint

/-- info: 'SparseHamiltonian.GateNative.privMacro_inv_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.privMacro_inv_approx

/-- info: 'SparseHamiltonian.GateNative.selOp_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.selOp_isUnitary

/-- info: 'SparseHamiltonian.GateNative.selOp_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.selOp_adjoint

/-- info: 'SparseHamiltonian.GateNative.ite_localOp_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ite_localOp_one

/-- info: 'SparseHamiltonian.GateNative.localOp_ctrlIdeal_selOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.localOp_ctrlIdeal_selOp

/-- info: 'SparseHamiltonian.GateNative.nrun_flatMap_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nrun_flatMap_le

/-- info: 'SparseHamiltonian.GateNative.approxOn_flatMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.approxOn_flatMap

/-- info: 'SparseHamiltonian.GateNative.nrun_eq_prodOps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nrun_eq_prodOps

/-- info: 'SparseHamiltonian.GateNative.localOp_ctrl_gateOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.localOp_ctrl_gateOp

/-- info: 'SparseHamiltonian.GateNative.localOp_ctrl_gRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.localOp_ctrl_gRun

/-- info: 'SparseHamiltonian.GateNative.ctrlGate_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ctrlGate_agrees

/-- info: 'SparseHamiltonian.GateNative.ctrlGate_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ctrlGate_ok

/-- info: 'SparseHamiltonian.GateNative.ctrlGate_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ctrlGate_length

/-! ### Native macros of the released Hamiltonian circuits -/

/-- info: 'SparseHamiltonian.GateNative.flagList_nodup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.flagList_nodup

/-- info: 'SparseHamiltonian.GateNative.ePWfun_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ePWfun_injective

/-- info: 'SparseHamiltonian.GateNative.liftB_conj_selOracle_canon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.liftB_conj_selOracle_canon

/-- info: 'SparseHamiltonian.GateNative.liftB_conj_selOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.liftB_conj_selOracle

/-- info: 'SparseHamiltonian.GateNative.card_HW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.card_HW

/-- info: 'SparseHamiltonian.GateNative.secOK_ofGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.secOK_ofGates

/-- info: 'SparseHamiltonian.GateNative.secOK_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.secOK_inv

/-- info: 'SparseHamiltonian.GateNative.secOK_invList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.secOK_invList

/-- info: 'SparseHamiltonian.GateNative.secOK_selectI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.secOK_selectI

/-- info: 'SparseHamiltonian.GateNative.secOK_lcuI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.secOK_lcuI

/-- info: 'SparseHamiltonian.GateNative.secOK_ampI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.secOK_ampI

/-- info: 'SparseHamiltonian.GateNative.conj_unfl_fl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.conj_unfl_fl

/-- info: 'SparseHamiltonian.GateNative.UJop_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.UJop_adjoint

/-- info: 'SparseHamiltonian.GateNative.UJop_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.UJop_isUnitary

/-- info: 'SparseHamiltonian.GateNative.cleanX_update_inl' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.cleanX_update_inl

/-- info: 'SparseHamiltonian.GateNative.ujGates_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ujGates_ok

/-- info: 'SparseHamiltonian.GateNative.ujGates_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ujGates_length

/-- info: 'SparseHamiltonian.GateNative.pEmb_ne_secW' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.pEmb_ne_secW

/-- info: 'SparseHamiltonian.GateNative.ujGates_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ujGates_agrees

/-- info: 'SparseHamiltonian.GateNative.hmacro_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.hmacro_approx

/-- info: 'SparseHamiltonian.GateNative.sum_priv_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.sum_priv_nat

/-- info: 'SparseHamiltonian.GateNative.sum_priv_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.sum_priv_real

/-- info: 'SparseHamiltonian.GateNative.sum_le_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.sum_le_counts

/-- info: 'SparseHamiltonian.GateNative.prodOps_liftB_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.prodOps_liftB_conj

/-- info: 'SparseHamiltonian.GateNative.norm_fl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.norm_fl

/-- info: 'SparseHamiltonian.GateNative.fl_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.fl_apply

/-- info: 'SparseHamiltonian.GateNative.conj_fl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.conj_fl

/-- info: 'SparseHamiltonian.GateNative.norm_sysEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.norm_sysEmb

/-- info: 'SparseHamiltonian.GateNative.hmacro_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.hmacro_valid

/-- info: 'SparseHamiltonian.GateNative.hcirc_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.hcirc_valid

/-- info: 'SparseHamiltonian.GateNative.selOracle_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.selOracle_isUnitary

/-- info: 'SparseHamiltonian.GateNative.evalSel_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.evalSel_isUnitary

/-- info: 'SparseHamiltonian.GateNative.hmacro_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.hmacro_nCalls

/-- info: 'SparseHamiltonian.GateNative.hcirc_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.hcirc_nCalls

/-- info: 'SparseHamiltonian.GateNative.hmacro_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.hmacro_nGates

/-- info: 'SparseHamiltonian.GateNative.hcirc_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.hcirc_nGates

/-- info: 'SparseHamiltonian.GateNative.hcirc_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.hcirc_approx

/-- info: 'SparseHamiltonian.GateNative.hcirc_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.hcirc_error

/-! ### Native macros of the released ODE preparations -/

/-- info: 'SparseHamiltonian.GateNative.nSrcAny_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nSrcAny_eq

/-- info: 'SparseHamiltonian.GateNative.sum_oweight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.sum_oweight

/-- info: 'SparseHamiltonian.GateNative.omacro_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.omacro_approx

/-- info: 'SparseHamiltonian.GateNative.omacro_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.omacro_valid

/-- info: 'SparseHamiltonian.GateNative.oprep_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.oprep_approx

/-- info: 'SparseHamiltonian.GateNative.sum_le_ocounts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.sum_le_ocounts

/-- info: 'SparseHamiltonian.GateNative.omacro_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.omacro_nGates

/-- info: 'SparseHamiltonian.GateNative.omacro_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.omacro_nCalls

/-- info: 'SparseHamiltonian.GateNative.andChain_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.andChain_target

/-- info: 'SparseHamiltonian.GateNative.mcGate_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.mcGate_target

/-- info: 'SparseHamiltonian.GateNative.ctrlGate_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ctrlGate_target

/-- info: 'SparseHamiltonian.GateNative.not_reflWire_inl' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.not_reflWire_inl

/-- info: 'SparseHamiltonian.GateNative.not_reflWire_xw' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.not_reflWire_xw

/-- info: 'SparseHamiltonian.GateNative.not_reflWire_zs' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.not_reflWire_zs

/-- info: 'SparseHamiltonian.GateNative.omacro_not_touches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.omacro_not_touches

/-! ### Native zero tests, amplification steps and trials -/

/-- info: 'SparseHamiltonian.GateNative.poolN_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.poolN_nodup

/-- info: 'SparseHamiltonian.GateNative.poolN_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.poolN_length

/-- info: 'SparseHamiltonian.GateNative.mem_poolN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.mem_poolN

/-- info: 'SparseHamiltonian.GateNative.zeroLitsN_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.zeroLitsN_length

/-- info: 'SparseHamiltonian.GateNative.sysLits_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.sysLits_length

/-- info: 'SparseHamiltonian.GateNative.zeroLitsN_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.zeroLitsN_false

/-- info: 'SparseHamiltonian.GateNative.sysLits_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.sysLits_false

/-- info: 'SparseHamiltonian.GateNative.zeroLitsN_not_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.zeroLitsN_not_refl

/-- info: 'SparseHamiltonian.GateNative.sysLits_not_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.sysLits_not_refl

/-- info: 'SparseHamiltonian.GateNative.reflWire_flgN' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.reflWire_flgN

/-- info: 'SparseHamiltonian.GateNative.reflWire_poolN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.reflWire_poolN

/-- info: 'SparseHamiltonian.GateNative.rgoodNG_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rgoodNG_length

/-- info: 'SparseHamiltonian.GateNative.rseedNG_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rseedNG_length

/-- info: 'SparseHamiltonian.GateNative.lits_ne_pool' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.lits_ne_pool

/-- info: 'SparseHamiltonian.GateNative.lits_ne_flg' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.lits_ne_flg

/-- info: 'SparseHamiltonian.GateNative.poolN_ne_flg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.poolN_ne_flg

/-- info: 'SparseHamiltonian.GateNative.rgoodNG_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rgoodNG_ok

/-- info: 'SparseHamiltonian.GateNative.rseedNG_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rseedNG_ok

/-- info: 'SparseHamiltonian.GateNative.negGateN_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.negGateN_ok

/-- info: 'SparseHamiltonian.GateNative.goodN_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.goodN_apply

/-- info: 'SparseHamiltonian.GateNative.norm_goodN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.norm_goodN

/-- info: 'SparseHamiltonian.GateNative.goodN_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.goodN_isometry

/-- info: 'SparseHamiltonian.GateNative.nonSysZero_sysCfg' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nonSysZero_sysCfg

/-- info: 'SparseHamiltonian.GateNative.sysCfg_of_nonSysZero' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.sysCfg_of_nonSysZero

/-- info: 'SparseHamiltonian.GateNative.goodN_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.goodN_bas

/-- info: 'SparseHamiltonian.GateNative.goodN_adjoint_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.goodN_adjoint_bas

/-- info: 'SparseHamiltonian.GateNative.norm_sN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.norm_sN

/-- info: 'SparseHamiltonian.GateNative.norm_seedV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.norm_seedV

/-- info: 'SparseHamiltonian.GateNative.sN_eq_goodN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.sN_eq_goodN

/-- info: 'SparseHamiltonian.GateNative.sN_eq_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.sN_eq_cleanEmb

/-- info: 'SparseHamiltonian.GateNative.rgoodNI_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rgoodNI_bas

/-- info: 'SparseHamiltonian.GateNative.rseedNI_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rseedNI_bas

/-- info: 'SparseHamiltonian.GateNative.rgoodNI_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rgoodNI_isUnitary

/-- info: 'SparseHamiltonian.GateNative.rseedNI_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rseedNI_isUnitary

/-- info: 'SparseHamiltonian.GateNative.zeroOn_of_nonSysZero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.zeroOn_of_nonSysZero

/-- info: 'SparseHamiltonian.GateNative.supp_goodN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.supp_goodN

/-- info: 'SparseHamiltonian.GateNative.supp_sN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.supp_sN

/-- info: 'SparseHamiltonian.GateNative.preserves_rgoodNI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.preserves_rgoodNI

/-- info: 'SparseHamiltonian.GateNative.preserves_rseedNI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.preserves_rseedNI

/-- info: 'SparseHamiltonian.GateNative.rgoodNI_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rgoodNI_adjoint

/-- info: 'SparseHamiltonian.GateNative.rseedNI_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rseedNI_adjoint

/-- info: 'SparseHamiltonian.GateNative.ctrlOK_zeroLitsN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ctrlOK_zeroLitsN

/-- info: 'SparseHamiltonian.GateNative.ctrlOK_seedLits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ctrlOK_seedLits

/-- info: 'SparseHamiltonian.GateNative.zeroOn_pool_of_refl' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.zeroOn_pool_of_refl

/-- info: 'SparseHamiltonian.GateNative.mcGate_flg_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.mcGate_flg_agrees

/-- info: 'SparseHamiltonian.GateNative.rgoodN_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rgoodN_agrees

/-- info: 'SparseHamiltonian.GateNative.rseedN_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.rseedN_agrees

/-- info: 'SparseHamiltonian.GateNative.gateOp_negN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.gateOp_negN

/-- info: 'SparseHamiltonian.GateNative.stepN_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.stepN_agrees

/-- info: 'SparseHamiltonian.GateNative.preserves_groverN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.preserves_groverN

/-- info: 'SparseHamiltonian.GateNative.stepsN_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.stepsN_agree

/-- info: 'SparseHamiltonian.GateNative.trialN_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.trialN_seed

/-- info: 'SparseHamiltonian.GateNative.stepN_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.stepN_valid

/-- info: 'SparseHamiltonian.GateNative.trialN_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.trialN_valid

/-- info: 'SparseHamiltonian.GateNative.trialN_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.trialN_nCalls

/-- info: 'SparseHamiltonian.GateNative.trialN_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.trialN_nGates

/-! ### The enlarged certificate, trial bounds and the protocol -/

/-- info: 'SparseHamiltonian.GateNative.output_certificate9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.output_certificate9

/-- info: 'SparseHamiltonian.GateNative.trial_bounds_of_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.trial_bounds_of_vec

/-- info: 'SparseHamiltonian.GateNative.cleanEmb_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.cleanEmb_isometry

/-- info: 'SparseHamiltonian.GateNative.goodN_adjoint_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.goodN_adjoint_cleanEmb

/-- info: 'SparseHamiltonian.GateNative.norm_goodN_adjoint_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.norm_goodN_adjoint_le

/-- info: 'SparseHamiltonian.GateNative.native_decoded_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.native_decoded_close

/-- info: 'SparseHamiltonian.GateNative.native_vector_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.native_vector_error

/-- info: 'SparseHamiltonian.GateNative.native_trial_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.native_trial_bounds

/-- info: 'SparseHamiltonian.GateNative.ntoProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ntoProgram_eval

/-- info: 'SparseHamiltonian.GateNative.ntoProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ntoProgram_cost

/-- info: 'SparseHamiltonian.GateNative.sum_indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.sum_indicator

/-- info: 'SparseHamiltonian.GateNative.ntoProgram_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ntoProgram_counts

/-- info: 'SparseHamiltonian.GateNative.ntrial_cost_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ntrial_cost_bound

/-- info: 'SparseHamiltonian.GateNative.nprotocol_worst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.nprotocol_worst

/-- info: 'SparseHamiltonian.GateNative.ntrials_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ntrials_eval

/-- info: 'SparseHamiltonian.GateNative.ntrials_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.ntrials_amplitude

/-- info: 'SparseHamiltonian.GateNative.noutcome_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.noutcome_of_bounds

/-- info: 'SparseHamiltonian.GateNative.noutcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateNative.noutcome
