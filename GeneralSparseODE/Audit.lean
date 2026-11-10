import GeneralSparseODE.Subst
import GeneralSparseODE.SubstSlot
import GeneralSparseODE.Embed
import GeneralSparseODE.Padded
import GeneralSparseODE.Valid
import GeneralSparseODE.Source
import GeneralSparseODE.Constant
import GeneralSparseODE.ConstantBudget
import GeneralSparseODE.Time
import GeneralSparseODE.TimeBudget

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (116 theorems), beginning
with the main theorems, then in module order. 111 reports list exactly `propext`, `Classical.choice`
and `Quot.sound`; the other 5 list a strict subset. -/

/-! ### Final theorems: the outcomes and budgets of the general solvers, the substituted
operations, the padded instance and the problem on `ℂ^N` -/

/-- info: 'SparseHamiltonian.GeneralSparseODE.general_ode_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.general_ode_outcome

/-- info: 'SparseHamiltonian.GeneralSparseODE.general_ode_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.general_ode_budget

/-- info: 'SparseHamiltonian.GeneralSparseODE.general_time_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.general_time_outcome

/-- info: 'SparseHamiltonian.GeneralSparseODE.general_time_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.general_time_budget

/-- info: 'SparseHamiltonian.GeneralSparseODE.nativeOK_substOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.nativeOK_substOp

/-- info: 'SparseHamiltonian.GeneralSparseODE.nativeOK_substSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.nativeOK_substSlot

/-- info: 'SparseHamiltonian.GeneralSparseODE.arithOK_liftA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.arithOK_liftA

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.nativeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.nativeOK

/-- info: 'SparseHamiltonian.GeneralSparseODE.RobustRestG.padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.RobustRestG.padded

/-- info: 'SparseHamiltonian.GeneralSparseODE.solution_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.solution_comp

/-- info: 'SparseHamiltonian.GeneralSparseODE.solves_zext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.solves_zext

/-- info: 'SparseHamiltonian.GeneralSparseODE.accretive_zext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.accretive_zext

/-- info: 'SparseHamiltonian.GeneralSparseODE.mLift_padData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.mLift_padData

/-- info: 'SparseHamiltonian.GeneralSparseODE.zpad_row_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.zpad_row_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.zpad_col_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.zpad_col_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.zpad_accretive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.zpad_accretive

/-- info: 'SparseHamiltonian.GeneralSparseODE.padLift_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.padLift_eq

/-- info: 'SparseHamiltonian.GeneralSparseODE.solution_padLift_validEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.solution_padLift_validEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.solution_padLift_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.solution_padLift_invalid

/-- info: 'SparseHamiltonian.GeneralSparseODE.solves_validLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.solves_validLift

/-- info: 'SparseHamiltonian.GeneralSparseODE.approxOn_liftSrc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.approxOn_liftSrc

/-- info: 'SparseHamiltonian.GeneralSparseODE.approxOn_liftLoad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.approxOn_liftLoad

/-! ### Substituted native operations (`Subst`, `SubstSlot`) -/

/-- info: 'SparseHamiltonian.GeneralSparseODE.cleanOn_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.cleanOn_apply

/-- info: 'SparseHamiltonian.GeneralSparseODE.cleanOn_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.cleanOn_trans

/-- info: 'SparseHamiltonian.GeneralSparseODE.cleanOn_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.cleanOn_inl

/-- info: 'SparseHamiltonian.GeneralSparseODE.norm_cleanOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.norm_cleanOn

/-- info: 'SparseHamiltonian.GeneralSparseODE.localOp_cleanOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.localOp_cleanOn

/-- info: 'SparseHamiltonian.GeneralSparseODE.inclZ_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.inclZ_injective

/-- info: 'SparseHamiltonian.GeneralSparseODE.ascE_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.ascE_injective

/-- info: 'SparseHamiltonian.GeneralSparseODE.ascE_inl' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.ascE_inl

/-- info: 'SparseHamiltonian.GeneralSparseODE.substOp_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.substOp_public

/-- info: 'SparseHamiltonian.GeneralSparseODE.nGatesN_substOp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.nGatesN_substOp_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.nCallsN_substOp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.nCallsN_substOp_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.Rdec_substOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.Rdec_substOp

/-- info: 'SparseHamiltonian.GeneralSparseODE.liftW_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.liftW_injective

/-- info: 'SparseHamiltonian.GeneralSparseODE.liftA_circ_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.liftA_circ_length

/-- info: 'SparseHamiltonian.GeneralSparseODE.atSlot2_substSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.atSlot2_substSlot

/-- info: 'SparseHamiltonian.GeneralSparseODE.substSlot_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.substSlot_public

/-- info: 'SparseHamiltonian.GeneralSparseODE.nGatesN_substSlot_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.nGatesN_substSlot_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.nCallsN_substSlot_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.nCallsN_substSlot_le

/-! ### The marker embedding (`Embed`) -/

/-- info: 'SparseHamiltonian.GeneralSparseODE.sum_mark_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.sum_mark_false

/-- info: 'SparseHamiltonian.GeneralSparseODE.markEmb_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.markEmb_apply

/-- info: 'SparseHamiltonian.GeneralSparseODE.norm_markEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.norm_markEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.lowPart_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.lowPart_apply

/-- info: 'SparseHamiltonian.GeneralSparseODE.lowPart_markEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.lowPart_markEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.inner_markEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.inner_markEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.markEmb_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.markEmb_adjoint

/-- info: 'SparseHamiltonian.GeneralSparseODE.norm_markEmb_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.norm_markEmb_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.norm_lowPart_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.norm_lowPart_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.zext_markEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.zext_markEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.zext_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.zext_sub

/-- info: 'SparseHamiltonian.GeneralSparseODE.norm_zext_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.norm_zext_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.lowOp_markEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.lowOp_markEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.lowOp_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.lowOp_isUnitary

/-- info: 'SparseHamiltonian.GeneralSparseODE.lowOp_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.lowOp_one

/-- info: 'SparseHamiltonian.GeneralSparseODE.seedV_markEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.seedV_markEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.unitDirection_markEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.unitDirection_markEmb

/-! ### The padded instance (`Padded`) -/

/-- info: 'SparseHamiltonian.GeneralSparseODE.hamiltonianPart_zpad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.hamiltonianPart_zpad

/-- info: 'SparseHamiltonian.GeneralSparseODE.dissipativePart_zpad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.dissipativePart_zpad

/-- info: 'SparseHamiltonian.GeneralSparseODE.padData_zpad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.padData_zpad

/-- info: 'SparseHamiltonian.GeneralSparseODE.mLift_padData_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.mLift_padData_comp

/-- info: 'SparseHamiltonian.GeneralSparseODE.padData_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.padData_range

/-- info: 'SparseHamiltonian.GeneralSparseODE.padData_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.padData_decode

/-! ### The problem on `ℂ^N` (`Valid`) -/

/-- info: 'SparseHamiltonian.GeneralSparseODE.validEmb_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.validEmb_apply

/-- info: 'SparseHamiltonian.GeneralSparseODE.validRes_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.validRes_apply

/-- info: 'SparseHamiltonian.GeneralSparseODE.sum_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.sum_valid

/-- info: 'SparseHamiltonian.GeneralSparseODE.validRes_validEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.validRes_validEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.validRes_comp_validEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.validRes_comp_validEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.inner_validEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.inner_validEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.norm_validEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.norm_validEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.norm_validRes_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.norm_validRes_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.opNorm_validEmb_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.opNorm_validEmb_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.opNorm_validRes_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.opNorm_validRes_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.unitDirection_validEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.unitDirection_validEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.validLift_comp_validEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.validLift_comp_validEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.validLift_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.validLift_sub

/-- info: 'SparseHamiltonian.GeneralSparseODE.norm_validLift_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.norm_validLift_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.norm_validLift_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.norm_validLift_sub_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.accretive_validLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.accretive_validLift

/-- info: 'SparseHamiltonian.GeneralSparseODE.padLift_comp_validEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.padLift_comp_validEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.norm_validLift_sub_padLift_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.norm_validLift_sub_padLift_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.padLift_apply_invalid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.padLift_apply_invalid

/-- info: 'SparseHamiltonian.GeneralSparseODE.solves_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.solves_comp

/-! ### The source circuits on the low wires (`Source`) -/

/-- info: 'SparseHamiltonian.GeneralSparseODE.liftE_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.liftE_injective

/-- info: 'SparseHamiltonian.GeneralSparseODE.valid_liftC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.valid_liftC

/-- info: 'SparseHamiltonian.GeneralSparseODE.nGatesN_liftC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.nGatesN_liftC

/-- info: 'SparseHamiltonian.GeneralSparseODE.nCallsN_liftC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.nCallsN_liftC

/-- info: 'SparseHamiltonian.GeneralSparseODE.liftB_ctl_lowOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.liftB_ctl_lowOp

/-- info: 'SparseHamiltonian.GeneralSparseODE.srcIdeal_lowOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.srcIdeal_lowOp

/-- info: 'SparseHamiltonian.GeneralSparseODE.srcIdeal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.srcIdeal_eq

/-- info: 'SparseHamiltonian.GeneralSparseODE.approxOn_liftC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.approxOn_liftC

/-! ### Constant coefficients (`Constant`, `ConstantBudget`) -/

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPub.nd_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPub.nd_public

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPub.ar_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPub.ar_ok

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPub.nd_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPub.nd_nGates

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPub.nd_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPub.nd_nCalls

/-- info: 'SparseHamiltonian.GeneralSparseODE.wOutcome_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.wOutcome_target

/-- info: 'SparseHamiltonian.GeneralSparseODE.words_gate_arith_g' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.words_gate_arith_g

/-- info: 'SparseHamiltonian.GeneralSparseODE.card_AWg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.card_AWg

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPub.card_Zg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPub.card_Zg

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPub.card_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPub.card_reg

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPub.card_reg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPub.card_reg_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPub.privGates_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPub.privGates_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPub.wires_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPub.wires_le

/-! ### Time-dependent coefficients (`Time`, `TimeBudget`) -/

/-- info: 'SparseHamiltonian.GeneralSparseODE.primsTG_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.primsTG_isUnitary

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.nd_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.nd_public

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.ar_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.ar_ok

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.nd_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.nd_nGates

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.nd_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.nd_nCalls

/-- info: 'SparseHamiltonian.GeneralSparseODE.zsrc_markEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.zsrc_markEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.mass_markEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.mass_markEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.srcAmp_markEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.srcAmp_markEmb

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.card_Zg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.card_Zg

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.card_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.card_reg

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.card_reg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.card_reg_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.privGates_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.privGates_le

/-- info: 'SparseHamiltonian.GeneralSparseODE.GPubT.wires_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSparseODE.GPubT.wires_le
