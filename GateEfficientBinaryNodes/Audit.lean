import GateEfficientBinaryNodes.Core
import GateEfficientBinaryNodes.Integrated
import GateEfficientBinaryNodes.SelectIntegrated
import GateEfficientBinaryNodes.Const
import GateEfficientBinaryNodes.ConstSolver
import GateEfficientBinaryNodes.NodeAddr
import GateEfficientBinaryNodes.NodeNative
import GateEfficientBinaryNodes.NodeIdentity
import GateEfficientBinaryNodes.NodeClock
import GateEfficientBinaryNodes.NodePub
import GateEfficientBinaryNodes.NodeSolver
import GateEfficientBinaryNodes.NodeBudget
import GateEfficientBinaryNodes.NodeBits
import GateEfficientBinaryNodes.NonVacuity

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 24 lemmas, whose reports list a subset of
these three axioms (or none). The audits cover every theorem of the library of the
constant-forcing source preparation, the integrated generator-sample certificates and the
coherently computed source nodes of Theorem `ode:thm:gates`, beginning with the solvers with
computed nodes and their budgets, followed by the integrated certificate, the constant-forcing
solvers, the construction of the private operation for computed nodes and the non-vacuity
witnesses.
-/

/-! ### Theorem `ode:thm:gates` from binary data with computed source nodes -/

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_nodes_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_nodes_solver

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_nodes_solver_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_nodes_solver_synth

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_nodes_solver_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_nodes_solver_trials

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_nodes_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_nodes_counts

/-- info: 'SparseHamiltonian.GateBinaryNodes.layQN_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.layQN_ok

/-- info: 'SparseHamiltonian.GateBinaryNodes.kapQN_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.kapQN_pos

/-- info: 'SparseHamiltonian.GateBinaryNodes.ndQN_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.ndQN_public

/-- info: 'SparseHamiltonian.GateBinaryNodes.arQN_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.arQN_ok

/-- info: 'SparseHamiltonian.GateBinaryNodes.ndQN_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.ndQN_nGates

/-- info: 'SparseHamiltonian.GateBinaryNodes.ndQN_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.ndQN_nCalls

/-- info: 'SparseHamiltonian.GateBinaryNodes.card_ZAN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.card_ZAN

/-- info: 'SparseHamiltonian.GateBinaryNodes.card_ZaN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.card_ZaN

/-- info: 'SparseHamiltonian.GateBinaryNodes.arQN_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.arQN_counts

/-- info: 'SparseHamiltonian.GateBinaryNodes.nativeOKQN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nativeOKQN

/-- info: 'SparseHamiltonian.GateBinaryNodes.selectN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.selectN

/-- info: 'SparseHamiltonian.GateBinaryNodes.sampleErrB_NQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.sampleErrB_NQ

/-- info: 'SparseHamiltonian.GateBinaryNodes.instanceN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.instanceN

/-- info: 'SparseHamiltonian.GateBinaryNodes.privGatesQN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.privGatesQN

/-- info: 'SparseHamiltonian.GateBinaryNodes.card_ZN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.card_ZN

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_nodes_gate_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_nodes_gate_count

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_nodes_synth_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_nodes_synth_counts

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_nodes_trials_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_nodes_trials_counts

/-! ### Equations `ode:eq:gate-main` and `ode:eq:gate-space` for computed nodes -/

/-- info: 'SparseHamiltonian.GateBinaryNodes.card_addrGT_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.card_addrGT_le

/-- info: 'SparseHamiltonian.GateBinaryNodes.card_ZAN_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.card_ZAN_le

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_nodes_arith_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_nodes_arith_words

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_nodes_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_nodes_budget

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_nodes_budget_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_nodes_budget_solver

/-- info: 'SparseHamiltonian.GateBinaryNodes.words_gate_arithN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.words_gate_arithN

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_nodes_budget_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_nodes_budget_words

/-- info: 'SparseHamiltonian.GateBinaryNodes.bitN_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.bitN_nonneg

/-- info: 'SparseHamiltonian.GateBinaryNodes.wordsN_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.wordsN_le

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_nodes_budget_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_nodes_budget_bits

/-- info: 'SparseHamiltonian.GateBinaryNodes.card_XW_ZN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.card_XW_ZN

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_nodes_budget_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_nodes_budget_trials

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_nodes_budget_solver_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_nodes_budget_solver_trials

/-- info: 'SparseHamiltonian.GateBinaryNodes.prepBoundN_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.prepBoundN_le

/-- info: 'SparseHamiltonian.GateBinaryNodes.log_factorN_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.log_factorN_le

/-- info: 'SparseHamiltonian.GateBinaryNodes.testedN_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.testedN_le

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_nodes_budget_trials_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_nodes_budget_trials_bits

/-! ### The integrated sample-error certificate -/

/-- info: 'SparseHamiltonian.GateBinaryNodes.BCore.unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.BCore.unitary

/-- info: 'SparseHamiltonian.GateBinaryNodes.BInstanceOK.core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.BInstanceOK.core

/-- info: 'SparseHamiltonian.GateBinaryNodes.target_facts_of_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.target_facts_of_error

/-- info: 'SparseHamiltonian.GateBinaryNodes.BInstanceOK.facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.BInstanceOK.facts

/-- info: 'SparseHamiltonian.GateBinaryNodes.prep_certificateC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.prep_certificateC

/-- info: 'SparseHamiltonian.GateBinaryNodes.native_time_outcomeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.native_time_outcomeC

/-- info: 'SparseHamiltonian.GateBinaryNodes.native_time_trials_outcomeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.native_time_trials_outcomeC

/-- info: 'SparseHamiltonian.GateBinaryNodes.homog_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.homog_norm_le

/-- info: 'SparseHamiltonian.GateBinaryNodes.homog_discI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.homog_discI

/-- info: 'SparseHamiltonian.GateBinaryNodes.sampleErrB_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.sampleErrB_nonneg

/-- info: 'SparseHamiltonian.GateBinaryNodes.sampleErrB_le_of_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.sampleErrB_le_of_uniform

/-- info: 'SparseHamiltonian.GateBinaryNodes.branch_discI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.branch_discI

/-- info: 'SparseHamiltonian.GateBinaryNodes.target_errorBI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.target_errorBI

/-- info: 'SparseHamiltonian.GateBinaryNodes.BInstanceOK.toI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.BInstanceOK.toI

/-- info: 'SparseHamiltonian.GateBinaryNodes.BInstanceOKI.core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.BInstanceOKI.core

/-- info: 'SparseHamiltonian.GateBinaryNodes.target_factsBI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.target_factsBI

/-- info: 'SparseHamiltonian.GateBinaryNodes.native_time_outcomeBI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.native_time_outcomeBI

/-- info: 'SparseHamiltonian.GateBinaryNodes.native_ode_time_solverBI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.native_ode_time_solverBI

/-- info: 'SparseHamiltonian.GateBinaryNodes.native_time_trials_outcomeBI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.native_time_trials_outcomeBI

/-- info: 'SparseHamiltonian.GateBinaryNodes.LInstanceOKI.toBI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.LInstanceOKI.toBI

/-- info: 'SparseHamiltonian.GateBinaryNodes.sampleOK_of_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.sampleOK_of_all

/-- info: 'SparseHamiltonian.GateBinaryNodes.clockBA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.clockBA

/-- info: 'SparseHamiltonian.GateBinaryNodes.selectBA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.selectBA

/-- info: 'SparseHamiltonian.GateBinaryNodes.sampleErrB_Q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.sampleErrB_Q

/-- info: 'SparseHamiltonian.GateBinaryNodes.sampleErrQ_le_of_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.sampleErrQ_le_of_uniform

/-- info: 'SparseHamiltonian.GateBinaryNodes.instanceBI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.instanceBI

/-- info: 'SparseHamiltonian.GateBinaryNodes.instanceLI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.instanceLI

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_select_solverI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_select_solverI

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_select_solverLI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_select_solverLI

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_select_solverI_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_select_solverI_synth

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_select_solverLI_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_select_solverLI_synth

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_select_solverI_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_select_solverI_trials

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_select_solverLI_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_select_solverLI_trials

/-! ### The source preparation for constant forcing (`ode:eq:gate-constant-source`) -/

/-- info: 'SparseHamiltonian.GateBinaryNodes.gRun_ctrlT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.gRun_ctrlT

/-- info: 'SparseHamiltonian.GateBinaryNodes.length_ctrlT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.length_ctrlT

/-- info: 'SparseHamiltonian.GateBinaryNodes.mem_ctrlT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.mem_ctrlT

/-- info: 'SparseHamiltonian.GateBinaryNodes.length_wpGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.length_wpGates

/-- info: 'SparseHamiltonian.GateBinaryNodes.tsW_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.tsW_last

/-- info: 'SparseHamiltonian.GateBinaryNodes.tsW_castSucc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.tsW_castSucc

/-- info: 'SparseHamiltonian.GateBinaryNodes.tsW_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.tsW_ne_zero

/-- info: 'SparseHamiltonian.GateBinaryNodes.sq_sqrt_srcB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.sq_sqrt_srcB

/-- info: 'SparseHamiltonian.GateBinaryNodes.wpGates_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.wpGates_ok

/-- info: 'SparseHamiltonian.GateBinaryNodes.MxW_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.MxW_last

/-- info: 'SparseHamiltonian.GateBinaryNodes.MxW_castSucc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.MxW_castSucc

/-- info: 'SparseHamiltonian.GateBinaryNodes.MxW_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.MxW_update

/-- info: 'SparseHamiltonian.GateBinaryNodes.rotC_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.rotC_col

/-- info: 'SparseHamiltonian.GateBinaryNodes.hadC_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.hadC_col

/-- info: 'SparseHamiltonian.GateBinaryNodes.prod_MxW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.prod_MxW

/-- info: 'SparseHamiltonian.GateBinaryNodes.gRun_wp_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.gRun_wp_zero

/-- info: 'SparseHamiltonian.GateBinaryNodes.matOp_matOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.matOp_matOf

/-- info: 'SparseHamiltonian.GateBinaryNodes.matOp_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.matOp_injective

/-- info: 'SparseHamiltonian.GateBinaryNodes.matOf_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.matOf_unitary

/-- info: 'SparseHamiltonian.GateBinaryNodes.matOp_WpConst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.matOp_WpConst

/-- info: 'SparseHamiltonian.GateBinaryNodes.WpConst_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.WpConst_unitary

/-- info: 'SparseHamiltonian.GateBinaryNodes.WpConst_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.WpConst_col

/-- info: 'SparseHamiltonian.GateBinaryNodes.nrun_wpConst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nrun_wpConst

/-- info: 'SparseHamiltonian.GateBinaryNodes.wpConst_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.wpConst_approx

/-- info: 'SparseHamiltonian.GateBinaryNodes.wpConst_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.wpConst_valid

/-- info: 'SparseHamiltonian.GateBinaryNodes.wpConst_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.wpConst_counts

/-- info: 'SparseHamiltonian.GateBinaryNodes.sqrt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.sqrt_two_pow

/-- info: 'SparseHamiltonian.GateBinaryNodes.zsrc_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.zsrc_const

/-- info: 'SparseHamiltonian.GateBinaryNodes.mass_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.mass_const

/-- info: 'SparseHamiltonian.GateBinaryNodes.srcAmp_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.srcAmp_const

/-- info: 'SparseHamiltonian.GateBinaryNodes.WpConst_srcAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.WpConst_srcAmp

/-- info: 'SparseHamiltonian.GateBinaryNodes.plCFun_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.plCFun_injective

/-- info: 'SparseHamiltonian.GateBinaryNodes.place_srcIdeal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.place_srcIdeal

/-- info: 'SparseHamiltonian.GateBinaryNodes.srcIdealL_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.srcIdealL_comp

/-- info: 'SparseHamiltonian.GateBinaryNodes.isUnitary_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.isUnitary_norm_le

/-- info: 'SparseHamiltonian.GateBinaryNodes.loadConst_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.loadConst_approx

/-- info: 'SparseHamiltonian.GateBinaryNodes.loadConst_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.loadConst_valid

/-- info: 'SparseHamiltonian.GateBinaryNodes.loadConst_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.loadConst_counts

/-- info: 'SparseHamiltonian.GateBinaryNodes.const_source_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.const_source_counts

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_ode_time_const_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_ode_time_const_counts

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_ode_time_solver_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_ode_time_solver_const

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_ode_time_solver_const_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_ode_time_solver_const_synth

/-- info: 'SparseHamiltonian.GateBinaryNodes.bsW_wQ_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.bsW_wQ_const

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_select_const_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_select_const_counts

/-- info: 'SparseHamiltonian.GateBinaryNodes.RestLIConst.toLI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.RestLIConst.toLI

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_select_solverLI_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_select_solverLI_const

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_select_solverLI_const_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_select_solverLI_const_synth

/-- info: 'SparseHamiltonian.GateBinaryNodes.binary_select_solverLI_const_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.binary_select_solverLI_const_trials

/-! ### The construction for computed nodes -/

/-- info: 'SparseHamiltonian.GateBinaryNodes.aLayN_w' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.aLayN_w

/-- info: 'SparseHamiltonian.GateBinaryNodes.aLayN_F' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.aLayN_F

/-- info: 'SparseHamiltonian.GateBinaryNodes.lvO_accN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.lvO_accN

/-- info: 'SparseHamiltonian.GateBinaryNodes.length_addrOpsN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.length_addrOpsN

/-- info: 'SparseHamiltonian.GateBinaryNodes.opsN3_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.opsN3_ok

/-- info: 'SparseHamiltonian.GateBinaryNodes.chainN_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.chainN_ok

/-- info: 'SparseHamiltonian.GateBinaryNodes.opMdN_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.opMdN_ok

/-- info: 'SparseHamiltonian.GateBinaryNodes.addrOKN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.addrOKN

/-- info: 'SparseHamiltonian.GateBinaryNodes.regsN_dst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.regsN_dst

/-- info: 'SparseHamiltonian.GateBinaryNodes.nuP_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nuP_lt

/-- info: 'SparseHamiltonian.GateBinaryNodes.rSN_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.rSN_lt

/-- info: 'SparseHamiltonian.GateBinaryNodes.addr_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.addr_lt

/-- info: 'SparseHamiltonian.GateBinaryNodes.gAN_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.gAN_lt

/-- info: 'SparseHamiltonian.GateBinaryNodes.mu_le_wN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.mu_le_wN

/-- info: 'SparseHamiltonian.GateBinaryNodes.ofBits_uBaN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.ofBits_uBaN

/-- info: 'SparseHamiltonian.GateBinaryNodes.vN_ax1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.vN_ax1

/-- info: 'SparseHamiltonian.GateBinaryNodes.vN_n1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.vN_n1

/-- info: 'SparseHamiltonian.GateBinaryNodes.vN_z1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.vN_z1

/-- info: 'SparseHamiltonian.GateBinaryNodes.sum_dgN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.sum_dgN

/-- info: 'SparseHamiltonian.GateBinaryNodes.vN_acc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.vN_acc

/-- info: 'SparseHamiltonian.GateBinaryNodes.vN_md' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.vN_md

/-- info: 'SparseHamiltonian.GateBinaryNodes.mdN_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.mdN_bit

/-- info: 'SparseHamiltonian.GateBinaryNodes.mdN_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.mdN_word

/-- info: 'SparseHamiltonian.GateBinaryNodes.n1N_msb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.n1N_msb

/-- info: 'SparseHamiltonian.GateBinaryNodes.n1N_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.n1N_bit

/-- info: 'SparseHamiltonian.GateBinaryNodes.n1N_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.n1N_word

/-- info: 'SparseHamiltonian.GateBinaryNodes.n1N_dv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.n1N_dv

/-- info: 'SparseHamiltonian.GateBinaryNodes.w_posN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.w_posN

/-- info: 'SparseHamiltonian.GateBinaryNodes.length_addrGN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.length_addrGN

/-- info: 'SparseHamiltonian.GateBinaryNodes.addrGN_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.addrGN_proper

/-- info: 'SparseHamiltonian.GateBinaryNodes.addrGN_cs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.addrGN_cs

/-- info: 'SparseHamiltonian.GateBinaryNodes.crun_addrGN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.crun_addrGN

/-- info: 'SparseHamiltonian.GateBinaryNodes.addrBitN_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.addrBitN_lt

/-- info: 'SparseHamiltonian.GateBinaryNodes.inpBN_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.inpBN_avoids

/-- info: 'SparseHamiltonian.GateBinaryNodes.inpBBN_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.inpBBN_avoids

/-- info: 'SparseHamiltonian.GateBinaryNodes.eNodeFun_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.eNodeFun_injective

/-- info: 'SparseHamiltonian.GateBinaryNodes.eAddrFun_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.eAddrFun_injective

/-- info: 'SparseHamiltonian.GateBinaryNodes.fN_reg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.fN_reg

/-- info: 'SparseHamiltonian.GateBinaryNodes.apGN_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.apGN_ok

/-- info: 'SparseHamiltonian.GateBinaryNodes.apGN_classical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.apGN_classical

/-- info: 'SparseHamiltonian.GateBinaryNodes.length_apGN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.length_apGN

/-- info: 'SparseHamiltonian.GateBinaryNodes.apGN_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.apGN_run

/-- info: 'SparseHamiltonian.GateBinaryNodes.odeArN_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.odeArN_ok

/-- info: 'SparseHamiltonian.GateBinaryNodes.odeOpN_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.odeOpN_public

/-- info: 'SparseHamiltonian.GateBinaryNodes.odeOpN_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.odeOpN_nGates

/-- info: 'SparseHamiltonian.GateBinaryNodes.odeOpN_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.odeOpN_nCalls

/-- info: 'SparseHamiltonian.GateBinaryNodes.length_addrGT' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.length_addrGT

/-- info: 'SparseHamiltonian.GateBinaryNodes.layN_kq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.layN_kq

/-- info: 'SparseHamiltonian.GateBinaryNodes.layN_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.layN_ok

/-- info: 'SparseHamiltonian.GateBinaryNodes.kapN_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.kapN_pos

/-- info: 'SparseHamiltonian.GateBinaryNodes.twos_baseWN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.twos_baseWN

/-- info: 'SparseHamiltonian.GateBinaryNodes.decOK_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.decOK_N

/-- info: 'SparseHamiltonian.GateBinaryNodes.startWN_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.startWN_lt

/-- info: 'SparseHamiltonian.GateBinaryNodes.addrNN_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.addrNN_lt

/-- info: 'SparseHamiltonian.GateBinaryNodes.privFamN_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.privFamN_isUnitary

/-- info: 'SparseHamiltonian.GateBinaryNodes.nuP_fN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nuP_fN

/-- info: 'SparseHamiltonian.GateBinaryNodes.addrCN_fN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.addrCN_fN

/-- info: 'SparseHamiltonian.GateBinaryNodes.dvWN_fN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.dvWN_fN

/-- info: 'SparseHamiltonian.GateBinaryNodes.nativeOK_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nativeOK_N

/-- info: 'SparseHamiltonian.GateBinaryNodes.wordEquivFin_symm_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.wordEquivFin_symm_word

/-- info: 'SparseHamiltonian.GateBinaryNodes.vN_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.vN_word

/-- info: 'SparseHamiltonian.GateBinaryNodes.vN_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.vN_mem

/-- info: 'SparseHamiltonian.GateBinaryNodes.startB_vN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.startB_vN

/-- info: 'SparseHamiltonian.GateBinaryNodes.durB_vN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.durB_vN

/-- info: 'SparseHamiltonian.GateBinaryNodes.addrB_vN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.addrB_vN

/-- info: 'SparseHamiltonian.GateBinaryNodes.HbN_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.HbN_of_lt

/-- info: 'SparseHamiltonian.GateBinaryNodes.LbN_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.LbN_of_lt

/-- info: 'SparseHamiltonian.GateBinaryNodes.gensN_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.gensN_eq

/-- info: 'SparseHamiltonian.GateBinaryNodes.HbN_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.HbN_self

/-- info: 'SparseHamiltonian.GateBinaryNodes.LbN_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.LbN_self

/-- info: 'SparseHamiltonian.GateBinaryNodes.clockN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.clockN

/-! ### Non-vacuity -/

/-- info: 'SparseHamiltonian.GateBinaryNodes.cpG_proper' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.cpG_proper

/-- info: 'SparseHamiltonian.GateBinaryNodes.cpG_run_inl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.cpG_run_inl

/-- info: 'SparseHamiltonian.GateBinaryNodes.cpG_run_other' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.cpG_run_other

/-- info: 'SparseHamiltonian.GateBinaryNodes.cpG_run_tgt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.cpG_run_tgt

/-- info: 'SparseHamiltonian.GateBinaryNodes.copyProg_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.copyProg_ok

/-- info: 'SparseHamiltonian.GateBinaryNodes.midProg_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.midProg_ok

/-- info: 'SparseHamiltonian.GateBinaryNodes.copyProg_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.copyProg_length

/-- info: 'SparseHamiltonian.GateBinaryNodes.midProg_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.midProg_length

/-- info: 'SparseHamiltonian.GateBinaryNodes.wordValue_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.wordValue_symm

/-- info: 'SparseHamiltonian.GateBinaryNodes.vN_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.vN_copy

/-- info: 'SparseHamiltonian.GateBinaryNodes.vN_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.vN_mid

/-- info: 'SparseHamiltonian.GateBinaryNodes.sampleErrNQ_le_of_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.sampleErrNQ_le_of_uniform

/-- info: 'SparseHamiltonian.GateBinaryNodes.nvq_copy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nvq_copy_le

/-- info: 'SparseHamiltonian.GateBinaryNodes.nvq_mid_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nvq_mid_le

/-- info: 'SparseHamiltonian.GateBinaryNodes.sampleOK_nv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.sampleOK_nv

/-- info: 'SparseHamiltonian.GateBinaryNodes.nv_sampleErrNQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nv_sampleErrNQ

/-- info: 'SparseHamiltonian.GateBinaryNodes.nvh_restN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nvh_restN

/-- info: 'SparseHamiltonian.GateBinaryNodes.nv_nodes_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nv_nodes_outcome

/-- info: 'SparseHamiltonian.GateBinaryNodes.nv_copy_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nv_copy_outcome

/-- info: 'SparseHamiltonian.GateBinaryNodes.nv_mid_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nv_mid_outcome

/-- info: 'SparseHamiltonian.GateBinaryNodes.nvMF_restN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nvMF_restN

/-- info: 'SparseHamiltonian.GateBinaryNodes.nvMF_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nvMF_node

/-- info: 'SparseHamiltonian.GateBinaryNodes.nvMF_instanceN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nvMF_instanceN

/-- info: 'SparseHamiltonian.GateBinaryNodes.nodes_all_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nodes_all_hyps

/-- info: 'SparseHamiltonian.GateBinaryNodes.nv_sampleErrQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nv_sampleErrQ

/-- info: 'SparseHamiltonian.GateBinaryNodes.nvc_restLIConst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nvc_restLIConst

/-- info: 'SparseHamiltonian.GateBinaryNodes.nv_const_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nv_const_outcome

/-- info: 'SparseHamiltonian.GateBinaryNodes.nvData1_dec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nvData1_dec

/-- info: 'SparseHamiltonian.GateBinaryNodes.nv1_hamiltonianPart_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nv1_hamiltonianPart_zero

/-- info: 'SparseHamiltonian.GateBinaryNodes.nv1_dissipativePart_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nv1_dissipativePart_zero

/-- info: 'SparseHamiltonian.GateBinaryNodes.nv1_mLift_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nv1_mLift_zero

/-- info: 'SparseHamiltonian.GateBinaryNodes.nvc_restConst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nvc_restConst

/-- info: 'SparseHamiltonian.GateBinaryNodes.nv_const_common_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nv_const_common_outcome

/-- info: 'SparseHamiltonian.GateBinaryNodes.nvh_restBI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nvh_restBI

/-- info: 'SparseHamiltonian.GateBinaryNodes.nv_selectI_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryNodes.nv_selectI_outcome
