import GeneralSparseAccess.MatOp
import GeneralSparseAccess.Compare
import GeneralSparseAccess.Data
import GeneralSparseAccess.Padded
import GeneralSparseAccess.PaddedData
import GeneralSparseAccess.Subst
import GeneralSparseAccess.CtrlRef
import GeneralSparseAccess.Implement
import GeneralSparseAccess.ImplVal
import GeneralSparseAccess.ImplOK
import GeneralSparseAccess.PadSpec
import GeneralSparseAccess.Keep
import GeneralSparseAccess.PadE
import GeneralSparseAccess.ImplE

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (252 theorems), beginning
with the main theorems, then in module order. 203 reports list exactly `propext`, `Classical.choice`
and `Quot.sound`; the other 49 list a strict subset. -/

/-! ### Final theorems: implementing the padded primitives from the supplied oracles, substitution,
synthesis and the padded data -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.implOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.implOK

/-- info: 'SparseHamiltonian.GeneralSparseAccess.kindOK_implP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.kindOK_implP

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nGatesN_implP_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nGatesN_implP_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.valid_implP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.valid_implP

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nrun_subst_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nrun_subst_cleanEmb

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nGatesN_subst_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nGatesN_subst_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nCallsN_subst_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nCallsN_subst_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.valid_subst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.valid_subst

/-- info: 'SparseHamiltonian.GeneralSparseAccess.keepC_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.keepC_error

/-- info: 'SparseHamiltonian.GeneralSparseAccess.keepC_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.keepC_spec

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nGatesOut_subst_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nGatesOut_subst_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padData_matrix

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padData_matrix_mark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padData_matrix_mark

/-- info: 'SparseHamiltonian.GeneralSparseAccess.pslot_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.pslot_range

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padData_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padData_isHermitian

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padData_row_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padData_row_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padData_col_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padData_col_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padData_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padData_entry_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.exp_comp_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.exp_comp_of_comp

/-- info: 'SparseHamiltonian.GeneralSparseAccess.qlift_refl_matrixOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.qlift_refl_matrixOperator

/-- info: 'SparseHamiltonian.GeneralSparseAccess.implVal_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.implVal_clean

/-- info: 'SparseHamiltonian.GeneralSparseAccess.maskCtrl_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.maskCtrl_clean

/-- info: 'SparseHamiltonian.GeneralSparseAccess.ctrlRef_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.ctrlRef_agrees

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_ltChain_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_ltChain_top

/-- info: 'SparseHamiltonian.GeneralSparseAccess.implOKE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.implOKE

/-- info: 'SparseHamiltonian.GeneralSparseAccess.kindOK_implPE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.kindOK_implPE

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nGatesN_implPE_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nGatesN_implPE_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.valid_implPE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.valid_implPE

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padDataE_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padDataE_matrix

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padDataE_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padDataE_decode

/-- info: 'SparseHamiltonian.GeneralSparseAccess.padForm_padDataE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.padForm_padDataE

/-- info: 'SparseHamiltonian.GeneralSparseAccess.implValE_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.implValE_clean

/-! ### Register operators as matrices (`MatOp`) -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.permOp_eq_matOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.permOp_eq_matOp

/-- info: 'SparseHamiltonian.GeneralSparseAccess.localOp_matOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.localOp_matOp

/-- info: 'SparseHamiltonian.GeneralSparseAccess.matOp_bas_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.matOp_bas_apply

/-- info: 'SparseHamiltonian.GeneralSparseAccess.matOp_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.matOp_bas

/-- info: 'SparseHamiltonian.GeneralSparseAccess.matOp_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.matOp_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.ofMat_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.ofMat_apply

/-- info: 'SparseHamiltonian.GeneralSparseAccess.ofMat_single_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.ofMat_single_apply

/-- info: 'SparseHamiltonian.GeneralSparseAccess.toMat_ofMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.toMat_ofMat

/-- info: 'SparseHamiltonian.GeneralSparseAccess.qlift_ofMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.qlift_ofMat

/-- info: 'SparseHamiltonian.GeneralSparseAccess.toMat_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.toMat_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.qlift_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.qlift_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.ofMat_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.ofMat_isUnitary

/-- info: 'SparseHamiltonian.GeneralSparseAccess.ofMat_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.ofMat_single

/-! ### Comparison with a public constant (`Compare`) -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_bStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_bStep

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_bTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_bTop

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_stepAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_stepAt

/-- info: 'SparseHamiltonian.GeneralSparseAccess.target_ne_xw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.target_ne_xw

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_chainUpTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_chainUpTo

/-- info: 'SparseHamiltonian.GeneralSparseAccess.target_chainUpTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.target_chainUpTo

/-- info: 'SparseHamiltonian.GeneralSparseAccess.ctrl_chainUpTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.ctrl_chainUpTo

/-- info: 'SparseHamiltonian.GeneralSparseAccess.gate_chainUpTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.gate_chainUpTo

/-- info: 'SparseHamiltonian.GeneralSparseAccess.length_stepAt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.length_stepAt_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.length_chainUpTo_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.length_chainUpTo_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.borrowValue_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.borrowValue_top

/-- info: 'SparseHamiltonian.GeneralSparseAccess.classical_ltChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.classical_ltChain

/-- info: 'SparseHamiltonian.GeneralSparseAccess.gateOK_ltChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.gateOK_ltChain

/-- info: 'SparseHamiltonian.GeneralSparseAccess.length_ltChain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.length_ltChain_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_ltChain_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_ltChain_out

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_reverse_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_reverse_cancel

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_cancel_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_cancel_reverse

/-! ### Sparse access of general size (`Data`) -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.wordValue_binW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.wordValue_binW

/-- info: 'SparseHamiltonian.GeneralSparseAccess.binW_wordValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.binW_wordValue

/-- info: 'SparseHamiltonian.GeneralSparseAccess.binW_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.binW_inj

/-- info: 'SparseHamiltonian.GeneralSparseAccess.edgeW_inl' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.edgeW_inl

/-- info: 'SparseHamiltonian.GeneralSparseAccess.edgeW_inr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.edgeW_inr

/-- info: 'SparseHamiltonian.GeneralSparseAccess.edgeW_eta' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.edgeW_eta

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.N_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.N_pos

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.s_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.s_le_pow

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.lt_pow_of_N' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.lt_pow_of_N

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.lt_pow_of_s' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.lt_pow_of_s

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.prims_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.prims_row

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.prims_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.prims_col

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.prims_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.prims_val

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.prims_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.prims_isUnitary

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padMat_binW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padMat_binW

/-! ### The padded lists, mask and locators (`Padded`) -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.mk_idx' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.mk_idx

/-- info: 'SparseHamiltonian.GeneralSparseAccess.lo_idx' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.lo_idx

/-- info: 'SparseHamiltonian.GeneralSparseAccess.idx_mark_lo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.idx_mark_lo

/-- info: 'SparseHamiltonian.GeneralSparseAccess.idx_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.idx_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.idx_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.idx_eq_iff

/-- info: 'SparseHamiltonian.GeneralSparseAccess.le_sP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.le_sP

/-- info: 'SparseHamiltonian.GeneralSparseAccess.sP_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.sP_pos

/-- info: 'SparseHamiltonian.GeneralSparseAccess.sbP_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.sbP_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.sP_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.sP_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.sP_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.sP_lt

/-- info: 'SparseHamiltonian.GeneralSparseAccess.binW_pdec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.binW_pdec

/-- info: 'SparseHamiltonian.GeneralSparseAccess.idx_binW_pdec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.idx_binW_pdec

/-- info: 'SparseHamiltonian.GeneralSparseAccess.pvalid_idx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.pvalid_idx

/-- info: 'SparseHamiltonian.GeneralSparseAccess.pdec_idx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.pdec_idx

/-- info: 'SparseHamiltonian.GeneralSparseAccess.pslot_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.pslot_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.plist_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.plist_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.prowloc_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.prowloc_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.pcolloc_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.pcolloc_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.lowE_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.lowE_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.lowE_ne_mw₁' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.lowE_ne_mw₁

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.lowE_ne_mw₂' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.lowE_ne_mw₂

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.mw₁_ne_mw₂' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.mw₁_ne_mw₂

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.wire_cases' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.wire_cases

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.cfg_ext_E' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.cfg_ext_E

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.outPart_lowE_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.outPart_lowE_eq_iff

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.evalid_update_mw₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.evalid_update_mw₂

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.maskF_maskF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.maskF_maskF

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.matOp_ctlBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.matOp_ctlBlock

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.matOp_rowMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.matOp_rowMat

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.matOp_colMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.matOp_colMat

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.ctl_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.ctl_isUnitary

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.rowMat_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.rowMat_isUnitary

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.colMat_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.colMat_isUnitary

/-! ### The padded data (`PaddedData`) -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.mul_permMat_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.mul_permMat_apply

/-- info: 'SparseHamiltonian.GeneralSparseAccess.permMat_mul_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.permMat_mul_apply

/-- info: 'SparseHamiltonian.GeneralSparseAccess.toMat_refl_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.toMat_refl_apply

/-- info: 'SparseHamiltonian.GeneralSparseAccess.edgeW_mw₁' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.edgeW_mw₁

/-- info: 'SparseHamiltonian.GeneralSparseAccess.edgeW_mw₂' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.edgeW_mw₂

/-- info: 'SparseHamiltonian.GeneralSparseAccess.edgeW_lowE' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.edgeW_lowE

/-- info: 'SparseHamiltonian.GeneralSparseAccess.phiE_refl_edgeW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.phiE_refl_edgeW

/-- info: 'SparseHamiltonian.GeneralSparseAccess.edgeW_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.edgeW_eq_iff

/-- info: 'SparseHamiltonian.GeneralSparseAccess.update_mw₂_edgeW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.update_mw₂_edgeW

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.locMat_lowE_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.locMat_lowE_apply

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.clearCfg_lowE_mw₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.clearCfg_lowE_mw₂

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.evalid_edge_pslot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.evalid_edge_pslot

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.maskE_edge_pslot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.maskE_edge_pslot

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.locMat_ctl_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.locMat_ctl_edge

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.ite_and_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.ite_and_one

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.ctlMask_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.ctlMask_col

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.rowMat_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.rowMat_col

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.colMat_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.colMat_col

/-! ### Substituting implementations for calls (`Subst`) -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.callEmb_inl' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.callEmb_inl

/-- info: 'SparseHamiltonian.GeneralSparseAccess.callEmb_inr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.callEmb_inr

/-- info: 'SparseHamiltonian.GeneralSparseAccess.subst_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.subst_nil

/-- info: 'SparseHamiltonian.GeneralSparseAccess.subst_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.subst_cons

/-- info: 'SparseHamiltonian.GeneralSparseAccess.subst_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.subst_append

/-- info: 'SparseHamiltonian.GeneralSparseAccess.slice_callEmb_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.slice_callEmb_cleanEmb

/-- info: 'SparseHamiltonian.GeneralSparseAccess.localOp_callEmb_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.localOp_callEmb_cleanEmb

/-- info: 'SparseHamiltonian.GeneralSparseAccess.adjoint_intertwine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.adjoint_intertwine

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nrun_substI_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nrun_substI_cleanEmb

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nGatesN_substI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nGatesN_substI

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nCallsN_le_of_kind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nCallsN_le_of_kind

/-! ### Controlled calls with a reference (`CtrlRef`) -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.put_eq_sum_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.put_eq_sum_bas

/-! ### The implementation circuits (`Implement`) -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.IW.e_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.IW.e_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.IW.tl_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.IW.tl_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.IW.rf_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.IW.rf_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.IW.dm_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.IW.dm_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.IW.bA_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.IW.bA_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.IW.bB_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.IW.bB_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.IW.sc_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.IW.sc_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.IW.v_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.IW.v_injective

/-- info: 'SparseHamiltonian.GeneralSparseAccess.IW.layoutA' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.IW.layoutA

/-- info: 'SparseHamiltonian.GeneralSparseAccess.IW.layoutB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.IW.layoutB

/-- info: 'SparseHamiltonian.GeneralSparseAccess.IW.refLayout' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.IW.refLayout

/-- info: 'SparseHamiltonian.GeneralSparseAccess.ltChain_avoids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.ltChain_avoids

/-- info: 'SparseHamiltonian.GeneralSparseAccess.ltChain_reverse_avoids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.ltChain_reverse_avoids

/-- info: 'SparseHamiltonian.GeneralSparseAccess.e_ne_xA' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.e_ne_xA

/-- info: 'SparseHamiltonian.GeneralSparseAccess.e_ne_xB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.e_ne_xB

/-- info: 'SparseHamiltonian.GeneralSparseAccess.bA_ne_e' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.bA_ne_e

/-- info: 'SparseHamiltonian.GeneralSparseAccess.bB_ne_e' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.bB_ne_e

/-- info: 'SparseHamiltonian.GeneralSparseAccess.bA_ne_bB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.bA_ne_bB

/-- info: 'SparseHamiltonian.GeneralSparseAccess.bB_ne_bA' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.bB_ne_bA

/-- info: 'SparseHamiltonian.GeneralSparseAccess.xA_ne_bB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.xA_ne_bB

/-- info: 'SparseHamiltonian.GeneralSparseAccess.xB_ne_bA' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.xB_ne_bA

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_maskC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_maskC

/-- info: 'SparseHamiltonian.GeneralSparseAccess.classical_maskC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.classical_maskC

/-- info: 'SparseHamiltonian.GeneralSparseAccess.gateOK_maskC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.gateOK_maskC

/-- info: 'SparseHamiltonian.GeneralSparseAccess.length_maskC_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.length_maskC_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.maskY_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.maskY_apply

/-- info: 'SparseHamiltonian.GeneralSparseAccess.gRun_maskC_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.gRun_maskC_cleanEmb

/-- info: 'SparseHamiltonian.GeneralSparseAccess.localOp_pos_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.localOp_pos_inl

/-- info: 'SparseHamiltonian.GeneralSparseAccess.binW_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.binW_zero

/-- info: 'SparseHamiltonian.GeneralSparseAccess.edgeW_binW_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.edgeW_binW_zero

/-- info: 'SparseHamiltonian.GeneralSparseAccess.supp_cleanEmb_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.supp_cleanEmb_ref

/-- info: 'SparseHamiltonian.GeneralSparseAccess.qlift_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.qlift_zero

/-- info: 'SparseHamiltonian.GeneralSparseAccess.gadgetCtl_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.gadgetCtl_eq

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_swap3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_swap3

/-- info: 'SparseHamiltonian.GeneralSparseAccess.classical_swap3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.classical_swap3

/-- info: 'SparseHamiltonian.GeneralSparseAccess.gateOK_swap3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.gateOK_swap3

/-- info: 'SparseHamiltonian.GeneralSparseAccess.e_inl_ne_e_inr' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.e_inl_ne_e_inr

/-- info: 'SparseHamiltonian.GeneralSparseAccess.swapW_inPairs' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.swapW_inPairs

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_swapList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_swapList

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_swapRegs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_swapRegs

/-- info: 'SparseHamiltonian.GeneralSparseAccess.classical_swapList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.classical_swapList

/-- info: 'SparseHamiltonian.GeneralSparseAccess.gateOK_swapRegs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.gateOK_swapRegs

/-- info: 'SparseHamiltonian.GeneralSparseAccess.length_swapList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.length_swapList

/-- info: 'SparseHamiltonian.GeneralSparseAccess.length_swapRegs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.length_swapRegs

/-- info: 'SparseHamiltonian.GeneralSparseAccess.gRun_swapRegs_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.gRun_swapRegs_cleanEmb

/-- info: 'SparseHamiltonian.GeneralSparseAccess.g₂_ne_v' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.g₂_ne_v

/-- info: 'SparseHamiltonian.GeneralSparseAccess.sc_ne_v' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.sc_ne_v

/-- info: 'SparseHamiltonian.GeneralSparseAccess.g₁_ne_g₂' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.g₁_ne_g₂

/-- info: 'SparseHamiltonian.GeneralSparseAccess.flipCfg_eq_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.flipCfg_eq_update

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_copyW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_copyW

/-- info: 'SparseHamiltonian.GeneralSparseAccess.copyW_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.copyW_target

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_copyList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_copyList

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_overwrite_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_overwrite_comm

/-- info: 'SparseHamiltonian.GeneralSparseAccess.classical_vflagC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.classical_vflagC

/-- info: 'SparseHamiltonian.GeneralSparseAccess.vflagC_avoids_v' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.vflagC_avoids_v

/-- info: 'SparseHamiltonian.GeneralSparseAccess.cfgRun_vflagC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.cfgRun_vflagC

/-! ### The padded value oracle (`ImplVal`) -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.valMap_sc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.valMap_sc

/-- info: 'SparseHamiltonian.GeneralSparseAccess.valMap_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.valMap_out

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nrun_valCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nrun_valCall

/-- info: 'SparseHamiltonian.GeneralSparseAccess.classical_copyC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.classical_copyC

/-- info: 'SparseHamiltonian.GeneralSparseAccess.classical_vflagC_rev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.classical_vflagC_rev

/-! ### The implementations of the padded primitives (`ImplOK`) -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.gateOK_vflagC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.gateOK_vflagC

/-- info: 'SparseHamiltonian.GeneralSparseAccess.gateOK_copyC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.gateOK_copyC

/-- info: 'SparseHamiltonian.GeneralSparseAccess.length_vflagC_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.length_vflagC_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.length_copyW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.length_copyW_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.length_copyC_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.length_copyC_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.callsOf_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.callsOf_append

/-- info: 'SparseHamiltonian.GeneralSparseAccess.callsOf_nGatesOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.callsOf_nGatesOf

/-- info: 'SparseHamiltonian.GeneralSparseAccess.callsOf_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.callsOf_call

/-- info: 'SparseHamiltonian.GeneralSparseAccess.callsOf_gadget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.callsOf_gadget

/-- info: 'SparseHamiltonian.GeneralSparseAccess.callsOf_ctrlRef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.callsOf_ctrlRef

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nGatesN_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nGatesN_call

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nCallsN_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nCallsN_call

/-- info: 'SparseHamiltonian.GeneralSparseAccess.valid_implLoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.valid_implLoc

/-- info: 'SparseHamiltonian.GeneralSparseAccess.valid_implVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.valid_implVal

/-- info: 'SparseHamiltonian.GeneralSparseAccess.callsOf_implLoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.callsOf_implLoc

/-- info: 'SparseHamiltonian.GeneralSparseAccess.callsOf_implVal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.callsOf_implVal

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.N_lt_pow_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.N_lt_pow_succ

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.s_lt_pow_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.s_lt_pow_succ

/-- info: 'SparseHamiltonian.GeneralSparseAccess.permOp_maskY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.permOp_maskY

/-- info: 'SparseHamiltonian.GeneralSparseAccess.permOp_swapY' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.permOp_swapY

/-- info: 'SparseHamiltonian.GeneralSparseAccess.prims_pad_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.prims_pad_row

/-- info: 'SparseHamiltonian.GeneralSparseAccess.prims_pad_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.prims_pad_col

/-- info: 'SparseHamiltonian.GeneralSparseAccess.implRow_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.implRow_clean

/-- info: 'SparseHamiltonian.GeneralSparseAccess.implCol_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.implCol_clean

/-- info: 'SparseHamiltonian.GeneralSparseAccess.implValP_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.implValP_clean

/-! ### The binary format of the padded data (`PadSpec`) -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.testBit_wordValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.testBit_wordValue

/-- info: 'SparseHamiltonian.GeneralSparseAccess.wordValue_lt_of_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.wordValue_lt_of_high

/-- info: 'SparseHamiltonian.GeneralSparseAccess.sum_pvalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.sum_pvalid

/-- info: 'SparseHamiltonian.GeneralSparseAccess.toMat_refl_matrixOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.toMat_refl_matrixOperator

/-! ### Synthesis of the gates outside the gate set (`Keep`) -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nGatesOut_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nGatesOut_append

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nGatesOut_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nGatesOut_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.nGatesOut_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.nGatesOut_cons

/-- info: 'SparseHamiltonian.GeneralSparseAccess.length_synthRep_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.length_synthRep_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.length_keepRep_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.length_keepRep_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.keepRep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.keepRep_spec

/-- info: 'SparseHamiltonian.GeneralSparseAccess.keepC_approxOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.keepC_approxOn

/-! ### The padded data with a validity decoder (`PadE`) -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.norm_pdecode_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.norm_pdecode_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.pdecode_ptableE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.pdecode_ptableE

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padDataE_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padDataE_table

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padDataE_rowOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padDataE_rowOracle

/-- info: 'SparseHamiltonian.GeneralSparseAccess.QData.padDataE_columnOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.QData.padDataE_columnOracle

/-- info: 'SparseHamiltonian.GeneralSparseAccess.PadForm.eq_mark' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.PadForm.eq_mark

/-- info: 'SparseHamiltonian.GeneralSparseAccess.PadForm.isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.PadForm.isHermitian

/-- info: 'SparseHamiltonian.GeneralSparseAccess.PadForm.row_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.PadForm.row_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.PadForm.col_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.PadForm.col_le

/-- info: 'SparseHamiltonian.GeneralSparseAccess.PadForm.entry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.PadForm.entry_le

/-! ### The implementations of its primitives (`ImplE`) -/

/-- info: 'SparseHamiltonian.GeneralSparseAccess.prims_padE_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.prims_padE_row

/-- info: 'SparseHamiltonian.GeneralSparseAccess.prims_padE_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.prims_padE_col

/-- info: 'SparseHamiltonian.GeneralSparseAccess.implRowE_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.implRowE_clean

/-- info: 'SparseHamiltonian.GeneralSparseAccess.implColE_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.implColE_clean

/-- info: 'SparseHamiltonian.GeneralSparseAccess.alongEquiv_posT_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseAccess.alongEquiv_posT_cleanEmb
