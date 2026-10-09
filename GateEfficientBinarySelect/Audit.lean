import GateEfficientBinarySelect.Address
import GateEfficientBinarySelect.Computed
import GateEfficientBinarySelect.Native
import GateEfficientBinarySelect.Identity
import GateEfficientBinarySelect.Clock
import GateEfficientBinarySelect.Pub
import GateEfficientBinarySelect.Solver
import GateEfficientBinarySelect.Synth
import GateEfficientBinarySelect.Certified
import GateEfficientBinarySelect.SelectNative
import GateEfficientBinarySelect.SelectBinary
import GateEfficientBinarySelect.Budget
import GateEfficientBinarySelect.BudgetBits
import GateEfficientBinarySelect.BudgetTrials
import GateEfficientBinarySelect.SelectCost
import GateEfficientBinarySelect.NonVacuity

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 23 lemmas, whose reports list a subset of
these three axioms (or none). The audits cover every theorem of the library of coherent
selection from binary data on branch-dependent meshes, beginning with Lemma
`ode:lem:gate-select` from binary data with native private calls and exact gates, the native
and the certified lemma, followed by the solvers and budgets of Theorem `ode:thm:gates` on
these meshes, the construction of the private operation and the non-vacuity witnesses.
-/

/-! ### Lemma `ode:lem:gate-select`: certificate, native calls and binary data -/

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_native_gate_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_native_gate_select

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_gate_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_gate_select

/-- info: 'SparseHamiltonian.GateBinarySelect.native_gate_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.native_gate_select

/-- info: 'SparseHamiltonian.GateBinarySelect.gate_select_certified' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.gate_select_certified

/-- info: 'SparseHamiltonian.GateBinarySelect.sampleErr_le_of_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.sampleErr_le_of_uniform

/-- info: 'SparseHamiltonian.GateBinarySelect.slot_cert_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.slot_cert_le

/-- info: 'SparseHamiltonian.GateBinarySelect.branch_slot_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.branch_slot_error

/-- info: 'SparseHamiltonian.GateBinarySelect.branch_error_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.branch_error_cert

/-- info: 'SparseHamiltonian.GateBinarySelect.gate_select_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.gate_select_integral

/-- info: 'SparseHamiltonian.GateBinarySelect.selWFun_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.selWFun_injective

/-- info: 'SparseHamiltonian.GateBinarySelect.isGate_embW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.isGate_embW

/-- info: 'SparseHamiltonian.GateBinarySelect.isUJ_embW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.isUJ_embW

/-- info: 'SparseHamiltonian.GateBinarySelect.isPriv_embW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.isPriv_embW

/-- info: 'SparseHamiltonian.GateBinarySelect.nGates_embW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nGates_embW

/-- info: 'SparseHamiltonian.GateBinarySelect.nUJ_embW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nUJ_embW

/-- info: 'SparseHamiltonian.GateBinarySelect.nPriv_embW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nPriv_embW

/-- info: 'SparseHamiltonian.GateBinarySelect.valid_embW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.valid_embW

/-- info: 'SparseHamiltonian.GateBinarySelect.ctrlOK_sec'' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.ctrlOK_sec'

/-- info: 'SparseHamiltonian.GateBinarySelect.evalSel_embW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.evalSel_embW

/-- info: 'SparseHamiltonian.GateBinarySelect.prodOps_evalSel_embW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.prodOps_evalSel_embW

/-- info: 'SparseHamiltonian.GateBinarySelect.hcirc_error_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.hcirc_error_gen

/-- info: 'SparseHamiltonian.GateBinarySelect.norm_selN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.norm_selN

/-- info: 'SparseHamiltonian.GateBinarySelect.native_gate_select_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.native_gate_select_inverse

/-- info: 'SparseHamiltonian.GateBinarySelect.star_add_smul_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.star_add_smul_real

/-- info: 'SparseHamiltonian.GateBinarySelect.vOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.vOf_eq

/-- info: 'SparseHamiltonian.GateBinarySelect.addr_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.addr_eq

/-- info: 'SparseHamiltonian.GateBinarySelect.kOf_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.kOf_abs_le

/-- info: 'SparseHamiltonian.GateBinarySelect.vOf_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.vOf_mem

/-- info: 'SparseHamiltonian.GateBinarySelect.lam_mul_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.lam_mul_T

/-- info: 'SparseHamiltonian.GateBinarySelect.select_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.select_hyps

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_select_lemma_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_select_lemma_words

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_select_lemma_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_select_lemma_bits

/-! ### Theorem `ode:thm:gates` from binary data on branch-dependent meshes -/

/-- info: 'SparseHamiltonian.GateBinarySelect.layQ_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.layQ_ok

/-- info: 'SparseHamiltonian.GateBinarySelect.kapQ_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.kapQ_pos

/-- info: 'SparseHamiltonian.GateBinarySelect.ndQ_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.ndQ_public

/-- info: 'SparseHamiltonian.GateBinarySelect.arQ_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.arQ_ok

/-- info: 'SparseHamiltonian.GateBinarySelect.ndQ_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.ndQ_nGates

/-- info: 'SparseHamiltonian.GateBinarySelect.ndQ_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.ndQ_nCalls

/-- info: 'SparseHamiltonian.GateBinarySelect.card_ZA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.card_ZA

/-- info: 'SparseHamiltonian.GateBinarySelect.arQ_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.arQ_counts

/-- info: 'SparseHamiltonian.GateBinarySelect.nativeOKQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nativeOKQ

/-- info: 'SparseHamiltonian.GateBinarySelect.selectB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.selectB

/-- info: 'SparseHamiltonian.GateBinarySelect.sampleG_addr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.sampleG_addr

/-- info: 'SparseHamiltonian.GateBinarySelect.instanceB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.instanceB

/-- info: 'SparseHamiltonian.GateBinarySelect.instanceL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.instanceL

/-- info: 'SparseHamiltonian.GateBinarySelect.card_ZB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.card_ZB

/-- info: 'SparseHamiltonian.GateBinarySelect.privGatesQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.privGatesQ

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_select_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_select_counts

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_select_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_select_solver

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_select_solverL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_select_solverL

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_select_gate_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_select_gate_count

/-- info: 'SparseHamiltonian.GateBinarySelect.native_time_trials_outcomeB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.native_time_trials_outcomeB

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_select_solver_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_select_solver_synth

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_select_solverL_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_select_solverL_synth

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_select_solver_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_select_solver_trials

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_select_solverL_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_select_solverL_trials

/-! ### Equations `ode:eq:gate-main`, `ode:eq:gate-space` and `ode:eq:gate-select-gates` -/

/-- info: 'SparseHamiltonian.GateBinarySelect.card_ZA_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.card_ZA_le

/-- info: 'SparseHamiltonian.GateBinarySelect.card_apG_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.card_apG_le

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_select_arith_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_select_arith_words

/-- info: 'SparseHamiltonian.GateBinarySelect.select_gates_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.select_gates_words

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_select_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_select_budget

/-- info: 'SparseHamiltonian.GateBinarySelect.words_gate_arithB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.words_gate_arithB

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_select_budget_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_select_budget_words

/-- info: 'SparseHamiltonian.GateBinarySelect.wordsB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.wordsB_le

/-- info: 'SparseHamiltonian.GateBinarySelect.select_gates_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.select_gates_bits

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_select_budget_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_select_budget_bits

/-- info: 'SparseHamiltonian.GateBinarySelect.card_XW_ZB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.card_XW_ZB

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_select_budget_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_select_budget_trials

/-- info: 'SparseHamiltonian.GateBinarySelect.prepBoundB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.prepBoundB_le

/-- info: 'SparseHamiltonian.GateBinarySelect.log_factorB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.log_factorB_le

/-- info: 'SparseHamiltonian.GateBinarySelect.testedB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.testedB_le

/-- info: 'SparseHamiltonian.GateBinarySelect.binary_select_budget_trials_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.binary_select_budget_trials_bits

/-! ### The address program and the private operation from binary data -/

/-- info: 'SparseHamiltonian.GateBinarySelect.aLay_w' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.aLay_w

/-- info: 'SparseHamiltonian.GateBinarySelect.aLay_F' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.aLay_F

/-- info: 'SparseHamiltonian.GateBinarySelect.wordValue_testBit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.wordValue_testBit

/-- info: 'SparseHamiltonian.GateBinarySelect.wordValue_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.wordValue_congr

/-- info: 'SparseHamiltonian.GateBinarySelect.lvO_accA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.lvO_accA

/-- info: 'SparseHamiltonian.GateBinarySelect.length_addrOps' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.length_addrOps

/-- info: 'SparseHamiltonian.GateBinarySelect.opsA3_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.opsA3_ok

/-- info: 'SparseHamiltonian.GateBinarySelect.chainA_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.chainA_ok

/-- info: 'SparseHamiltonian.GateBinarySelect.opMd_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.opMd_ok

/-- info: 'SparseHamiltonian.GateBinarySelect.addrOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.addrOK

/-- info: 'SparseHamiltonian.GateBinarySelect.regsA_dst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.regsA_dst

/-- info: 'SparseHamiltonian.GateBinarySelect.uP_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.uP_lt

/-- info: 'SparseHamiltonian.GateBinarySelect.rS_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.rS_lt

/-- info: 'SparseHamiltonian.GateBinarySelect.gA_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.gA_lt

/-- info: 'SparseHamiltonian.GateBinarySelect.m_le_wA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.m_le_wA

/-- info: 'SparseHamiltonian.GateBinarySelect.ofBits_uBa' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.ofBits_uBa

/-- info: 'SparseHamiltonian.GateBinarySelect.v_ax1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.v_ax1

/-- info: 'SparseHamiltonian.GateBinarySelect.v_n1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.v_n1

/-- info: 'SparseHamiltonian.GateBinarySelect.v_z1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.v_z1

/-- info: 'SparseHamiltonian.GateBinarySelect.sum_dgA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.sum_dgA

/-- info: 'SparseHamiltonian.GateBinarySelect.v_acc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.v_acc

/-- info: 'SparseHamiltonian.GateBinarySelect.v_md' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.v_md

/-- info: 'SparseHamiltonian.GateBinarySelect.md_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.md_bit

/-- info: 'SparseHamiltonian.GateBinarySelect.md_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.md_word

/-- info: 'SparseHamiltonian.GateBinarySelect.n1_msb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.n1_msb

/-- info: 'SparseHamiltonian.GateBinarySelect.n1_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.n1_bit

/-- info: 'SparseHamiltonian.GateBinarySelect.n1_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.n1_word

/-- info: 'SparseHamiltonian.GateBinarySelect.n1_dv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.n1_dv

/-- info: 'SparseHamiltonian.GateBinarySelect.w_posA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.w_posA

/-- info: 'SparseHamiltonian.GateBinarySelect.length_addrG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.length_addrG

/-- info: 'SparseHamiltonian.GateBinarySelect.addrG_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.addrG_proper

/-- info: 'SparseHamiltonian.GateBinarySelect.addrG_cs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.addrG_cs

/-- info: 'SparseHamiltonian.GateBinarySelect.crun_addrG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.crun_addrG

/-- info: 'SparseHamiltonian.GateBinarySelect.eval_slotInstrR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.eval_slotInstrR

/-- info: 'SparseHamiltonian.GateBinarySelect.nrun_slotR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nrun_slotR

/-- info: 'SparseHamiltonian.GateBinarySelect.Rdec_slotR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.Rdec_slotR

/-- info: 'SparseHamiltonian.GateBinarySelect.nativeOK_slotR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nativeOK_slotR

/-- info: 'SparseHamiltonian.GateBinarySelect.nGatesN_slotR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nGatesN_slotR

/-- info: 'SparseHamiltonian.GateBinarySelect.nCallsN_slotR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nCallsN_slotR

/-- info: 'SparseHamiltonian.GateBinarySelect.valid_slotR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.valid_slotR

/-- info: 'SparseHamiltonian.GateBinarySelect.selP_xorFun' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.selP_xorFun

/-- info: 'SparseHamiltonian.GateBinarySelect.xor_false_iff' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.xor_false_iff

/-- info: 'SparseHamiltonian.GateBinarySelect.xorFun_xorFun' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.xorFun_xorFun

/-- info: 'SparseHamiltonian.GateBinarySelect.xorF_symm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.xorF_symm

/-- info: 'SparseHamiltonian.GateBinarySelect.xor_cleanEmb_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.xor_cleanEmb_apply

/-- info: 'SparseHamiltonian.GateBinarySelect.slice_reW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.slice_reW

/-- info: 'SparseHamiltonian.GateBinarySelect.nativeOK_computed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nativeOK_computed

/-- info: 'SparseHamiltonian.GateBinarySelect.classical_hAP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.classical_hAP

/-- info: 'SparseHamiltonian.GateBinarySelect.addrBit_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.addrBit_lt

/-- info: 'SparseHamiltonian.GateBinarySelect.mapInp_avoids' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.mapInp_avoids

/-- info: 'SparseHamiltonian.GateBinarySelect.decO_mapInp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.decO_mapInp

/-- info: 'SparseHamiltonian.GateBinarySelect.decO_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.decO_update

/-- info: 'SparseHamiltonian.GateBinarySelect.inpB_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.inpB_avoids

/-- info: 'SparseHamiltonian.GateBinarySelect.inpBB_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.inpBB_avoids

/-- info: 'SparseHamiltonian.GateBinarySelect.embP_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.embP_injective

/-- info: 'SparseHamiltonian.GateBinarySelect.odeArB_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.odeArB_ok

/-- info: 'SparseHamiltonian.GateBinarySelect.apG_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.apG_ok

/-- info: 'SparseHamiltonian.GateBinarySelect.apG_classical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.apG_classical

/-- info: 'SparseHamiltonian.GateBinarySelect.length_apG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.length_apG

/-- info: 'SparseHamiltonian.GateBinarySelect.odeOpB_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.odeOpB_public

/-- info: 'SparseHamiltonian.GateBinarySelect.odeOpB_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.odeOpB_nGates

/-- info: 'SparseHamiltonian.GateBinarySelect.odeOpB_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.odeOpB_nCalls

/-- info: 'SparseHamiltonian.GateBinarySelect.layB_kq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.layB_kq

/-- info: 'SparseHamiltonian.GateBinarySelect.layB_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.layB_ok

/-- info: 'SparseHamiltonian.GateBinarySelect.kapB_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.kapB_pos

/-- info: 'SparseHamiltonian.GateBinarySelect.twos_baseW2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.twos_baseW2

/-- info: 'SparseHamiltonian.GateBinarySelect.decOK_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.decOK_B

/-- info: 'SparseHamiltonian.GateBinarySelect.startW_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.startW_lt

/-- info: 'SparseHamiltonian.GateBinarySelect.addrN_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.addrN_lt

/-- info: 'SparseHamiltonian.GateBinarySelect.privFamB_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.privFamB_isUnitary

/-- info: 'SparseHamiltonian.GateBinarySelect.fA_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.fA_reg

/-- info: 'SparseHamiltonian.GateBinarySelect.cfgOf_zero_comp_embP' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.cfgOf_zero_comp_embP

/-- info: 'SparseHamiltonian.GateBinarySelect.apG_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.apG_run

/-- info: 'SparseHamiltonian.GateBinarySelect.addrC_fA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.addrC_fA

/-- info: 'SparseHamiltonian.GateBinarySelect.dvW_fA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.dvW_fA

/-- info: 'SparseHamiltonian.GateBinarySelect.nativeOK_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nativeOK_B

/-- info: 'SparseHamiltonian.GateBinarySelect.HbB_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.HbB_of_lt

/-- info: 'SparseHamiltonian.GateBinarySelect.LbB_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.LbB_of_lt

/-- info: 'SparseHamiltonian.GateBinarySelect.gensB_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.gensB_eq

/-- info: 'SparseHamiltonian.GateBinarySelect.HbB_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.HbB_self

/-- info: 'SparseHamiltonian.GateBinarySelect.LbB_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.LbB_self

/-- info: 'SparseHamiltonian.GateBinarySelect.HbB_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.HbB_norm_le

/-- info: 'SparseHamiltonian.GateBinarySelect.LbB_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.LbB_norm_le

/-- info: 'SparseHamiltonian.GateBinarySelect.LbB_psd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.LbB_psd

/-- info: 'SparseHamiltonian.GateBinarySelect.M_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.M_cast

/-- info: 'SparseHamiltonian.GateBinarySelect.startB_vQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.startB_vQ

/-- info: 'SparseHamiltonian.GateBinarySelect.durB_vQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.durB_vQ

/-- info: 'SparseHamiltonian.GateBinarySelect.addrB_vQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.addrB_vQ

/-- info: 'SparseHamiltonian.GateBinarySelect.clockB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.clockB

/-! ### Non-vacuity -/

/-- info: 'SparseHamiltonian.GateBinarySelect.nvcErr_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvcErr_mem

/-- info: 'SparseHamiltonian.GateBinarySelect.nvcVal_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvcVal_mem

/-- info: 'SparseHamiltonian.GateBinarySelect.nvc_sample_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvc_sample_eq

/-- info: 'SparseHamiltonian.GateBinarySelect.nvc_sampleErr_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvc_sampleErr_le

/-- info: 'SparseHamiltonian.GateBinarySelect.nvc_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvc_select

/-- info: 'SparseHamiltonian.GateBinarySelect.nvc_not_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvc_not_uniform

/-- info: 'SparseHamiltonian.GateBinarySelect.nvq_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvq_ok

/-- info: 'SparseHamiltonian.GateBinarySelect.nvq_γ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvq_γ

/-- info: 'SparseHamiltonian.GateBinarySelect.nvData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvData_matrix

/-- info: 'SparseHamiltonian.GateBinarySelect.nvData_dec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvData_dec

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_hamiltonianPart_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_hamiltonianPart_zero

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_dissipativePart_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_dissipativePart_zero

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_XOf_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_XOf_zero

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_sampleErr_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_sampleErr_zero

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_energies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_energies

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_zeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_zeta

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_binary_gate_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_binary_gate_select

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_binary_native_gate_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_binary_native_gate_select

/-- info: 'SparseHamiltonian.GateBinarySelect.select_all_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.select_all_hyps

/-- info: 'SparseHamiltonian.GateBinarySelect.nvq_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvq_T

/-- info: 'SparseHamiltonian.GateBinarySelect.nvq_g' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvq_g

/-- info: 'SparseHamiltonian.GateBinarySelect.nvq_ε' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvq_ε

/-- info: 'SparseHamiltonian.GateBinarySelect.nvq_m_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvq_m_pos

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_mLift_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_mLift_zero

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_psd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_psd

/-- info: 'SparseHamiltonian.GateBinarySelect.wordValue_nvW1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.wordValue_nvW1

/-- info: 'SparseHamiltonian.GateBinarySelect.nvxs_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvxs_zero

/-- info: 'SparseHamiltonian.GateBinarySelect.nvxs_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvxs_T

/-- info: 'SparseHamiltonian.GateBinarySelect.seedV_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.seedV_ne

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_mass1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_mass1

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_zsrc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_zsrc

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_prep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_prep

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_restB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_restB

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_instanceB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_instanceB

/-- info: 'SparseHamiltonian.GateBinarySelect.nvh_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvh_mass

/-- info: 'SparseHamiltonian.GateBinarySelect.nvh_zsrc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvh_zsrc

/-- info: 'SparseHamiltonian.GateBinarySelect.nvh_prep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvh_prep

/-- info: 'SparseHamiltonian.GateBinarySelect.nvh_restB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvh_restB

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_select_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_select_outcome

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_select_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_select_lemma

/-- info: 'SparseHamiltonian.GateBinarySelect.nvl_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvl_mass

/-- info: 'SparseHamiltonian.GateBinarySelect.nvl_zsrc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvl_zsrc

/-- info: 'SparseHamiltonian.GateBinarySelect.nvl_prep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvl_prep

/-- info: 'SparseHamiltonian.GateBinarySelect.nvh_restL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nvh_restL

/-- info: 'SparseHamiltonian.GateBinarySelect.nv_select_outcomeL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinarySelect.nv_select_outcomeL
