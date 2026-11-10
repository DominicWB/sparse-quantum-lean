import GeneralDecoderODE.Decode
import GeneralDecoderODE.ImplDec
import GeneralDecoderODE.Compose
import GeneralDecoderODE.Solver
import GeneralDecoderODE.SolverBudget
import GeneralDecoderODE.SolverTime
import GeneralDecoderODE.SolverTimeBudget
import GeneralDecoderODE.Decoder

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (96 theorems), beginning
with the main theorems, then in module order. 86 reports list exactly `propext`, `Classical.choice`
and `Quot.sound`; the other 10 list a strict subset. -/

/-! ### Final theorems: the outcomes and budgets of the decoder solvers, the implementations
through the decoding circuit, the solvers through any implementation and the decodings -/

/-- info: 'SparseHamiltonian.GeneralDecoderODE.decoder_ode_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.decoder_ode_outcome

/-- info: 'SparseHamiltonian.GeneralDecoderODE.decoder_ode_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.decoder_ode_budget

/-- info: 'SparseHamiltonian.GeneralDecoderODE.decoder_time_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.decoder_time_outcome

/-- info: 'SparseHamiltonian.GeneralDecoderODE.decoder_time_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.decoder_time_budget

/-- info: 'SparseHamiltonian.GeneralDecoderODE.implOK_implDP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.implOK_implDP

/-- info: 'SparseHamiltonian.GeneralDecoderODE.kindOK_implDP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.kindOK_implDP

/-- info: 'SparseHamiltonian.GeneralDecoderODE.nGatesN_implDP_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.nGatesN_implDP_le

/-- info: 'SparseHamiltonian.GeneralDecoderODE.implDec_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.implDec_ok

/-- info: 'SparseHamiltonian.GeneralDecoderODE.kindOK_implDec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.kindOK_implDec

/-- info: 'SparseHamiltonian.GeneralDecoderODE.nGatesN_implDec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.nGatesN_implDec_le

/-- info: 'SparseHamiltonian.GeneralDecoderODE.implOK_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.implOK_comp

/-- info: 'SparseHamiltonian.GeneralDecoderODE.kindOK_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.kindOK_comp

/-- info: 'SparseHamiltonian.GeneralDecoderODE.nGatesN_implComp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.nGatesN_implComp_le

/-- info: 'SparseHamiltonian.GeneralDecoderODE.general_ode_outcomeI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.general_ode_outcomeI

/-- info: 'SparseHamiltonian.GeneralDecoderODE.general_ode_budgetI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.general_ode_budgetI

/-- info: 'SparseHamiltonian.GeneralDecoderODE.general_time_outcomeI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.general_time_outcomeI

/-- info: 'SparseHamiltonian.GeneralDecoderODE.general_time_budgetI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.general_time_budgetI

/-- info: 'SparseHamiltonian.GeneralDecoderODE.nativeOKTI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.nativeOKTI

/-- info: 'SparseHamiltonian.GeneralDecoderODE.robustRestG_decData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.robustRestG_decData

/-- info: 'SparseHamiltonian.GeneralDecoderODE.padLift_decData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.padLift_decData

/-- info: 'SparseHamiltonian.GeneralDecoderODE.BinDecode.copy_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.BinDecode.copy_exact

/-- info: 'SparseHamiltonian.GeneralDecoderODE.BinDecode.copy_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.BinDecode.copy_cost

/-- info: 'SparseHamiltonian.GeneralDecoderODE.BinDecode.table_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.BinDecode.table_cost_le

/-- info: 'SparseHamiltonian.GeneralDecoderODE.exists_table_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.exists_table_exact

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.decData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.decData_matrix

/-! ### Binary entry decoding (`Decode`) -/

/-- info: 'SparseHamiltonian.GeneralDecoderODE.BinDecode.wires_le_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.BinDecode.wires_le_cost

/-- info: 'SparseHamiltonian.GeneralDecoderODE.BinDecode.gateOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.BinDecode.gateOK

/-- info: 'SparseHamiltonian.GeneralDecoderODE.twos_allFalse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.twos_allFalse

/-- info: 'SparseHamiltonian.GeneralDecoderODE.gauss_allFalse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.gauss_allFalse

/-- info: 'SparseHamiltonian.GeneralDecoderODE.abs_twos_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.abs_twos_le

/-- info: 'SparseHamiltonian.GeneralDecoderODE.norm_gauss_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.norm_gauss_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.decData_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.decData_table

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.decData_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.decData_val

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.decData_rowOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.decData_rowOracle

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.decData_columnOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.decData_columnOracle

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.decData_val_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.decData_val_zero

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.decData_padMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.decData_padMat

/-- info: 'SparseHamiltonian.GeneralDecoderODE.flipCfg_copyGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.flipCfg_copyGate

/-- info: 'SparseHamiltonian.GeneralDecoderODE.cfgRun_copyGates_list' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.cfgRun_copyGates_list

/-- info: 'SparseHamiltonian.GeneralDecoderODE.classical_copyGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.classical_copyGates

/-- info: 'SparseHamiltonian.GeneralDecoderODE.card_VW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.card_VW

/-! ### The decoded oracles from the supplied ones (`ImplDec`) -/

/-- info: 'SparseHamiltonian.GeneralDecoderODE.flipCfg_cnot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.flipCfg_cnot

/-- info: 'SparseHamiltonian.GeneralDecoderODE.cfgRun_cnots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.cfgRun_cnots

/-- info: 'SparseHamiltonian.GeneralDecoderODE.classical_cnots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.classical_cnots

/-- info: 'SparseHamiltonian.GeneralDecoderODE.gateOK_cnots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.gateOK_cnots

/-- info: 'SparseHamiltonian.GeneralDecoderODE.posD_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.posD_injective

/-- info: 'SparseHamiltonian.GeneralDecoderODE.tmW_ne_vdW' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.tmW_ne_vdW

/-- info: 'SparseHamiltonian.GeneralDecoderODE.vdW_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.vdW_injective

/-- info: 'SparseHamiltonian.GeneralDecoderODE.length_outGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.length_outGates

/-- info: 'SparseHamiltonian.GeneralDecoderODE.classical_decG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.classical_decG

/-- info: 'SparseHamiltonian.GeneralDecoderODE.classical_outGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.classical_outGates

/-- info: 'SparseHamiltonian.GeneralDecoderODE.valid_decG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.valid_decG

/-- info: 'SparseHamiltonian.GeneralDecoderODE.valid_decG_rev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.valid_decG_rev

/-- info: 'SparseHamiltonian.GeneralDecoderODE.valid_implDec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.valid_implDec

/-- info: 'SparseHamiltonian.GeneralDecoderODE.posD_inl' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.posD_inl

/-- info: 'SparseHamiltonian.GeneralDecoderODE.posD_inr' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.posD_inr

/-- info: 'SparseHamiltonian.GeneralDecoderODE.edgeCall_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.edgeCall_clean

/-- info: 'SparseHamiltonian.GeneralDecoderODE.nrun_valCallD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.nrun_valCallD

/-- info: 'SparseHamiltonian.GeneralDecoderODE.valCallD_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.valCallD_clean

/-- info: 'SparseHamiltonian.GeneralDecoderODE.valCallD_restore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.valCallD_restore

/-- info: 'SparseHamiltonian.GeneralDecoderODE.cfgRun_decG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.cfgRun_decG

/-- info: 'SparseHamiltonian.GeneralDecoderODE.cfgRun_decG_rev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.cfgRun_decG_rev

/-- info: 'SparseHamiltonian.GeneralDecoderODE.cfgRun_outGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.cfgRun_outGates

/-- info: 'SparseHamiltonian.GeneralDecoderODE.classical_decG_rev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.classical_decG_rev

/-- info: 'SparseHamiltonian.GeneralDecoderODE.implDec_value_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.implDec_value_clean

/-! ### Composite implementations (`Compose`) -/

/-- info: 'SparseHamiltonian.GeneralDecoderODE.assocE_inl_inl' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.assocE_inl_inl

/-- info: 'SparseHamiltonian.GeneralDecoderODE.assocE_inl_inr' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.assocE_inl_inr

/-- info: 'SparseHamiltonian.GeneralDecoderODE.assocE_inr' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.assocE_inr

/-- info: 'SparseHamiltonian.GeneralDecoderODE.sum_elim_eq_false' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.sum_elim_eq_false

/-- info: 'SparseHamiltonian.GeneralDecoderODE.localOp_assocE_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.localOp_assocE_clean

/-- info: 'SparseHamiltonian.GeneralDecoderODE.kindOK_comp_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.kindOK_comp_id

/-! ### Constant coefficients through any implementation (`Solver`, `SolverBudget`) -/

/-- info: 'SparseHamiltonian.GeneralDecoderODE.ndI_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.ndI_public

/-- info: 'SparseHamiltonian.GeneralDecoderODE.arI_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.arI_ok

/-- info: 'SparseHamiltonian.GeneralDecoderODE.ndI_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.ndI_nGates

/-- info: 'SparseHamiltonian.GeneralDecoderODE.ndI_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.ndI_nCalls

/-- info: 'SparseHamiltonian.GeneralDecoderODE.words_gate_arith_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.words_gate_arith_i

/-- info: 'SparseHamiltonian.GeneralDecoderODE.budget_mono_i' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.budget_mono_i

/-- info: 'SparseHamiltonian.GeneralDecoderODE.GPubI.card_ZgI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.GPubI.card_ZgI

/-- info: 'SparseHamiltonian.GeneralDecoderODE.GPubI.card_regI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.GPubI.card_regI

/-- info: 'SparseHamiltonian.GeneralDecoderODE.GPubI.card_regI_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.GPubI.card_regI_le

/-- info: 'SparseHamiltonian.GeneralDecoderODE.GPubI.privGatesI_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.GPubI.privGatesI_le

/-- info: 'SparseHamiltonian.GeneralDecoderODE.GPubI.wiresI_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.GPubI.wiresI_le

/-! ### Time-dependent coefficients through any implementation (`SolverTime`, `SolverTimeBudget`) -/

/-- info: 'SparseHamiltonian.GeneralDecoderODE.ndTI_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.ndTI_public

/-- info: 'SparseHamiltonian.GeneralDecoderODE.arTI_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.arTI_ok

/-- info: 'SparseHamiltonian.GeneralDecoderODE.ndTI_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.ndTI_nGates

/-- info: 'SparseHamiltonian.GeneralDecoderODE.ndTI_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.ndTI_nCalls

/-- info: 'SparseHamiltonian.GeneralDecoderODE.budget_mono_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.budget_mono_c

/-- info: 'SparseHamiltonian.GeneralDecoderODE.GPubTI.card_ZgTI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.GPubTI.card_ZgTI

/-- info: 'SparseHamiltonian.GeneralDecoderODE.GPubTI.card_regTI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.GPubTI.card_regTI

/-- info: 'SparseHamiltonian.GeneralDecoderODE.GPubTI.card_regTI_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.GPubTI.card_regTI_le

/-- info: 'SparseHamiltonian.GeneralDecoderODE.GPubTI.privGatesTI_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.GPubTI.privGatesTI_le

/-- info: 'SparseHamiltonian.GeneralDecoderODE.GPubTI.wiresTI_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.GPubTI.wiresTI_le

/-! ### The decoder solvers (`Decoder`) -/

/-- info: 'SparseHamiltonian.GeneralDecoderODE.valid_implDP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.valid_implDP

/-- info: 'SparseHamiltonian.GeneralDecoderODE.card_DW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.card_DW

/-- info: 'SparseHamiltonian.GeneralDecoderODE.decoder_gate_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.decoder_gate_arith

/-- info: 'SparseHamiltonian.GeneralDecoderODE.decoder_space_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoderODE.decoder_space_arith
