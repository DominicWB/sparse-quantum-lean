import ODELowerBoundExtensions.Statements

set_option synthInstance.maxHeartbeats 400000

section
/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem of the extensions of the
dissipative-ODE lower bounds (694 theorems) and every `Prop`-valued field of the structures
`Psd.PsdRange`, `Homogeneous.HomRange`, `Padding.ZeroPad`, `Release.RetrySolver`,
`Release.RetryWitnesses`, `Release.PublicSources` and `Release.ReleaseRun` (26 fields), in
module order, helper modules included: Theorem `odel:thm:psd` (`Psd/`), Remark
`odel:rem:homogeneous` (`Homogeneous/`), the padding remarks of Section `part:odel`
(`Padding/`), the retry protocols, the released solver and the bracket (`Release/`), and Lemma
`odel:lem:dyson` with eq. `odel:eq:fixed` and its consequence (`Dyson/`). Every report lists
`propext`, `Classical.choice` and `Quot.sound`, except for 8 lemmas, whose reports list a subset
of these three axioms (one of them depends on no axiom): three word-table lemmas and the
padded-word identity `Padding.padWords_eq_value`, two weight lemmas of the released oracle
(`Release.matrixWeight_value_le`, `Release.matrixWeight_hardCost`), the flag-index involution
`Dyson.flipEquiv_flipEquiv` and the weight lemma `Dyson.sourceWeight_le_total`. Definitions are not
listed; the proof fields of the data and family constructions are reached through the theorems
about them. -/

/-! ### Theorem `odel:thm:psd` (`ODELowerBoundExtensions.Psd`) -/

/-! #### `ODELowerBoundExtensions.Psd.Heat` -/

/-- info: 'ODELowerBoundExtensions.Psd.norm_heat_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.norm_heat_le

/-- info: 'ODELowerBoundExtensions.Psd.heat_real_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heat_real_smul

/-- info: 'ODELowerBoundExtensions.Psd.heat_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heat_zero

/-- info: 'ODELowerBoundExtensions.Psd.heat_eq_evolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heat_eq_evolve

/-- info: 'ODELowerBoundExtensions.Psd.hasDerivAt_heat_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.hasDerivAt_heat_apply

/-- info: 'ODELowerBoundExtensions.Psd.solves_heat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.solves_heat

/-- info: 'ODELowerBoundExtensions.Psd.heat_apply_eq_of_solves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heat_apply_eq_of_solves

/-- info: 'ODELowerBoundExtensions.Psd.heat_apply_eq_of_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heat_apply_eq_of_hasDerivAt

/-- info: 'ODELowerBoundExtensions.Psd.heat_unitary_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heat_unitary_conj

/-- info: 'ODELowerBoundExtensions.Psd.psdCore_unitary_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdCore_unitary_conj

/-- info: 'ODELowerBoundExtensions.Psd.heat_psdCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heat_psdCore

/-- info: 'ODELowerBoundExtensions.Psd.heat_fullMatrix_coreVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heat_fullMatrix_coreVec

/-- info: 'ODELowerBoundExtensions.Psd.heat_fullMatrix_refZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heat_fullMatrix_refZero

/-- info: 'ODELowerBoundExtensions.Psd.inner_chainVec_heat_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.inner_chainVec_heat_kronecker

/-! #### `ODELowerBoundExtensions.Psd.Params` -/

/-- info: 'ODELowerBoundExtensions.Psd.PsdRange.s_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.PsdRange.s_ge

/-- info: 'ODELowerBoundExtensions.Psd.PsdRange.one_le_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.PsdRange.one_le_tau

/-- info: 'ODELowerBoundExtensions.Psd.PsdRange.eps_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.PsdRange.eps_pos

/-- info: 'ODELowerBoundExtensions.Psd.PsdRange.hL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.PsdRange.hL

/-- info: 'ODELowerBoundExtensions.Psd.PsdRange.of_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.PsdRange.of_paper

/-- info: 'ODELowerBoundExtensions.Psd.PsdRange.toHSRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.PsdRange.toHSRange

/-- info: 'ODELowerBoundExtensions.Psd.PsdRange.of_HSRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.PsdRange.of_HSRange

/-- info: 'ODELowerBoundExtensions.Psd.one_le_psdMu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.one_le_psdMu

/-- info: 'ODELowerBoundExtensions.Psd.two_mul_psdM_add_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.two_mul_psdM_add_one_le

/-- info: 'ODELowerBoundExtensions.Psd.psdM_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdM_gt

/-- info: 'ODELowerBoundExtensions.Psd.psdAmp_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdAmp_pos

/-- info: 'ODELowerBoundExtensions.Psd.psdAmp_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdAmp_ge

/-- info: 'ODELowerBoundExtensions.Psd.psdDelta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdDelta_pos

/-- info: 'ODELowerBoundExtensions.Psd.psdNum_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdNum_lt

/-- info: 'ODELowerBoundExtensions.Psd.psdWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdWeight_le

/-- info: 'ODELowerBoundExtensions.Psd.psdWeight_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdWeight_pos

/-- info: 'ODELowerBoundExtensions.Psd.norm_pathMatrix_psdWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.norm_pathMatrix_psdWeight_le

/-- info: 'ODELowerBoundExtensions.Psd.norm_pathMatrix_sub_psdWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.norm_pathMatrix_sub_psdWeight_le

/-! #### `ODELowerBoundExtensions.Psd.SpinAmp` -/

/-- info: 'ODELowerBoundExtensions.Psd.accretive_of_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.accretive_of_posSemidef

/-- info: 'ODELowerBoundExtensions.Psd.posSemidef_psdCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.posSemidef_psdCore

/-- info: 'ODELowerBoundExtensions.Psd.norm_psdCore_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.norm_psdCore_le

/-- info: 'ODELowerBoundExtensions.Psd.norm_psdCore_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.norm_psdCore_sub

/-- info: 'ODELowerBoundExtensions.Psd.norm_heat_sub_heat_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.norm_heat_sub_heat_apply_le

/-- info: 'ODELowerBoundExtensions.Psd.hasDerivAt_hypMonomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.hasDerivAt_hypMonomial

/-- info: 'ODELowerBoundExtensions.Psd.heatSpinSolution_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heatSpinSolution_zero

/-- info: 'ODELowerBoundExtensions.Psd.heatSpinSolution_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heatSpinSolution_last

/-- info: 'ODELowerBoundExtensions.Psd.hasDerivAt_heatSpinSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.hasDerivAt_heatSpinSolution

/-- info: 'ODELowerBoundExtensions.Psd.heat_neg_spinMatrix_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heat_neg_spinMatrix_last

/-- info: 'ODELowerBoundExtensions.Psd.heatEndAmp_spinWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heatEndAmp_spinWeight

/-- info: 'ODELowerBoundExtensions.Psd.norm_heatEndAmp_psdWeight_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.norm_heatEndAmp_psdWeight_sub_le

/-- info: 'ODELowerBoundExtensions.Psd.seven_eighths_le_heatEndAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.seven_eighths_le_heatEndAmp

/-! #### `ODELowerBoundExtensions.Psd.Matrices` -/

/-- info: 'ODELowerBoundExtensions.Psd.posSemidef_fromBlocks_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.posSemidef_fromBlocks_diag

/-- info: 'ODELowerBoundExtensions.Psd.posSemidef_refBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.posSemidef_refBlock

/-- info: 'ODELowerBoundExtensions.Psd.posSemidef_padBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.posSemidef_padBlock

/-- info: 'ODELowerBoundExtensions.Psd.posSemidef_fullMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.posSemidef_fullMatrix

/-- info: 'ODELowerBoundExtensions.Psd.psdCore_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdCore_apply

/-- info: 'ODELowerBoundExtensions.Psd.psdCore_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdCore_transpose

/-- info: 'ODELowerBoundExtensions.Psd.star_psdCore_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.star_psdCore_apply

/-- info: 'ODELowerBoundExtensions.Psd.sum_sq_psdCore_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.sum_sq_psdCore_le

/-- info: 'ODELowerBoundExtensions.Psd.card_row_psdCore_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.card_row_psdCore_le

/-- info: 'ODELowerBoundExtensions.Psd.card_row_psdSearchCore_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.card_row_psdSearchCore_le

/-- info: 'ODELowerBoundExtensions.Psd.card_row_psdScalarCore_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.card_row_psdScalarCore_le

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchMat_realSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchMat_realSymmetric

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarMat_realSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarMat_realSymmetric

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchMat_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchMat_posSemidef

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarMat_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarMat_posSemidef

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchMat_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchMat_props

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarMat_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarMat_props

/-! #### `ODELowerBoundExtensions.Psd.Readout` -/

/-- info: 'ODELowerBoundExtensions.Psd.psd_searchChain_amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_searchChain_amp

/-- info: 'ODELowerBoundExtensions.Psd.psd_scalarChain_amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_scalarChain_amp

/-- info: 'ODELowerBoundExtensions.Psd.heat_readoutInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heat_readoutInput

/-- info: 'ODELowerBoundExtensions.Psd.norm_sq_heat_readoutInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.norm_sq_heat_readoutInput

/-- info: 'ODELowerBoundExtensions.Psd.heat_readout_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heat_readout_expectation

/-- info: 'ODELowerBoundExtensions.Psd.endpoint_norm_psdCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.endpoint_norm_psdCore

/-- info: 'ODELowerBoundExtensions.Psd.seven_eighths_le_corr_unitDirection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.seven_eighths_le_corr_unitDirection

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchObs_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchObs_contraction

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarObs_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarObs_contraction

/-- info: 'ODELowerBoundExtensions.Psd.psdSearch_endpoint_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearch_endpoint_norm

/-- info: 'ODELowerBoundExtensions.Psd.psdScalar_endpoint_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalar_endpoint_norm

/-- info: 'ODELowerBoundExtensions.Psd.psd_search_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_search_corr

/-- info: 'ODELowerBoundExtensions.Psd.psd_scalar_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_scalar_corr

/-! #### `ODELowerBoundExtensions.Psd.Data.ScalarTable` -/

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarLocFun_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarLocFun_injective

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarTable_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarTable_bound

/-! #### `ODELowerBoundExtensions.Psd.Data.ScalarData` -/

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarTable_value_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarTable_value_diag

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarTable_value_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarTable_value_succ

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarTable_value_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarTable_value_pred

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarTable_value_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarTable_value_far

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarTable_value_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarTable_value_ref

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarTable_value_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarTable_value_pad

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarTable_value_core_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarTable_value_core_side

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarTable_value_side_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarTable_value_side_core

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarTable_value_ref_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarTable_value_ref_pad

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarTable_value_pad_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarTable_value_pad_ref

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarWord_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarWord_div

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarTable_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarTable_decode

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarLoc_diag_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarLoc_diag_mem

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarLoc_adj_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarLoc_adj_mem

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarLoc_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarLoc_row

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarLoc_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarLoc_col

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarData_matrix

/-- info: 'ODELowerBoundExtensions.Psd.implementsOn_psdScalarData_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.implementsOn_psdScalarData_spec

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarData_hardInstance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarData_hardInstance

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarData_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarData_posSemidef

/-! #### `ODELowerBoundExtensions.Psd.Data.SearchTable` -/

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchLocFun_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchLocFun_injective

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchTable_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchTable_bound

/-! #### `ODELowerBoundExtensions.Psd.Data.SearchData` -/

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchTable_value_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchTable_value_diag

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchTable_value_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchTable_value_succ

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchTable_value_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchTable_value_pred

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchTable_value_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchTable_value_far

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchTable_value_core_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchTable_value_core_side

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchTable_value_side_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchTable_value_side_core

/-- info: 'ODELowerBoundExtensions.Psd.psdGadgetWord_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdGadgetWord_div

/-- info: 'ODELowerBoundExtensions.Psd.psdDiagWord_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdDiagWord_div

/-- info: 'ODELowerBoundExtensions.Psd.psdPadWord_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdPadWord_div

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchTable_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchTable_decode

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchLoc_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchLoc_row

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchLoc_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchLoc_col

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchData_matrix

/-- info: 'ODELowerBoundExtensions.Psd.implementsOn_psdSearchData_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.implementsOn_psdSearchData_spec

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchData_hardInstance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchData_hardInstance

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchData_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchData_posSemidef

/-! #### `ODELowerBoundExtensions.Psd.Numerics` -/

/-- info: 'ODELowerBoundExtensions.Psd.half_tau_le_precN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.half_tau_le_precN

/-- info: 'ODELowerBoundExtensions.Psd.psd_two_le_hsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_two_le_hsH

/-- info: 'ODELowerBoundExtensions.Psd.psd_en_div_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_en_div_le

/-- info: 'ODELowerBoundExtensions.Psd.exp_neg_quarter_le_psdAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.exp_neg_quarter_le_psdAmp

/-- info: 'ODELowerBoundExtensions.Psd.eight_eps_le_psdAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.eight_eps_le_psdAmp

/-- info: 'ODELowerBoundExtensions.Psd.psd_pow_div_four_rpow_neg_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_pow_div_four_rpow_neg_inv

/-- info: 'ODELowerBoundExtensions.Psd.psd_four_rpow_inv_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_four_rpow_inv_le_two

/-- info: 'ODELowerBoundExtensions.Psd.psd_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_hyp

/-- info: 'ODELowerBoundExtensions.Psd.psd_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_root

/-- info: 'ODELowerBoundExtensions.Psd.psd_m_cond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_m_cond

/-- info: 'ODELowerBoundExtensions.Psd.psdConst_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdConst_pos

/-- info: 'ODELowerBoundExtensions.Psd.psd_gadget_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_gadget_arith

/-- info: 'ODELowerBoundExtensions.Psd.psd_scalar_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_scalar_sqrt

/-- info: 'ODELowerBoundExtensions.Psd.psd_assembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_assembly

/-! #### `ODELowerBoundExtensions.Psd.Family` -/

/-- info: 'ODELowerBoundExtensions.Psd.oneStageData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.oneStageData_matrix

/-- info: 'ODELowerBoundExtensions.Psd.heatFamily_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heatFamily_T

/-- info: 'ODELowerBoundExtensions.Psd.heatFamily_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heatFamily_mass

/-- info: 'ODELowerBoundExtensions.Psd.access_heatFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.access_heatFamily

/-- info: 'ODELowerBoundExtensions.Psd.heatFamily_solves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heatFamily_solves

/-- info: 'ODELowerBoundExtensions.Psd.heatFamily_inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.heatFamily_inClass

/-- info: 'ODELowerBoundExtensions.Psd.forces_of_spec_heat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.forces_of_spec_heat

/-- info: 'ODELowerBoundExtensions.Psd.hardInstance_oneStageData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.hardInstance_oneStageData

/-- info: 'ODELowerBoundExtensions.Psd.one_le_sqrt_two_mul_of_half_le_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.one_le_sqrt_two_mul_of_half_le_sq

/-- info: 'ODELowerBoundExtensions.Psd.one_div_mem_of_half_le_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.one_div_mem_of_half_le_sq

/-- info: 'ODELowerBoundExtensions.Psd.PsdRange.one_le_precN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.PsdRange.one_le_precN

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchDataAt_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchDataAt_matrix

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarDataAt_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarDataAt_matrix

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchFamilyAt_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchFamilyAt_data

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarFamilyAt_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarFamilyAt_data

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchFamilyAt_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchFamilyAt_T

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarFamilyAt_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarFamilyAt_T

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchFamilyAt_inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchFamilyAt_inClass

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarFamilyAt_inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarFamilyAt_inClass

/-- info: 'ODELowerBoundExtensions.Psd.psdSearchFamilyAt_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdSearchFamilyAt_props

/-- info: 'ODELowerBoundExtensions.Psd.psdScalarFamilyAt_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psdScalarFamilyAt_props

/-! #### `ODELowerBoundExtensions.Psd.SearchBound` -/

/-- info: 'ODELowerBoundExtensions.Psd.psd_heralded_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_heralded_corr

/-- info: 'ODELowerBoundExtensions.Psd.psd_search_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_search_cost

/-- info: 'ODELowerBoundExtensions.Psd.psd_search_forces_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_search_forces_local

/-- info: 'ODELowerBoundExtensions.Psd.psd_search_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_search_forces

/-! #### `ODELowerBoundExtensions.Psd.ScalarBound` -/

/-- info: 'ODELowerBoundExtensions.Psd.psd_scalar_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_scalar_cost

/-- info: 'ODELowerBoundExtensions.Psd.psd_scalar_forces_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_scalar_forces_quarter

/-- info: 'ODELowerBoundExtensions.Psd.psd_scalar_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_scalar_forces

/-- info: 'ODELowerBoundExtensions.Psd.psd_scalar_forces_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_scalar_forces_sqrt

/-! #### `ODELowerBoundExtensions.Psd.Theorem` -/

/-- info: 'ODELowerBoundExtensions.Psd.psd_hardInstance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_hardInstance

/-- info: 'ODELowerBoundExtensions.Psd.psd_family_hardInstance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_family_hardInstance

/-- info: 'ODELowerBoundExtensions.Psd.psd_search_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_search_witness

/-- info: 'ODELowerBoundExtensions.Psd.psd_scalar_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_scalar_witness

/-- info: 'ODELowerBoundExtensions.Psd.psd_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd_max

/-- info: 'ODELowerBoundExtensions.Psd.psd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Psd.psd

/-! ### Remark `odel:rem:homogeneous` (`ODELowerBoundExtensions.Homogeneous`) -/

/-! #### `ODELowerBoundExtensions.Homogeneous.Parameters` -/

/-- info: 'ODELowerBoundExtensions.Homogeneous.HomRange.s_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.HomRange.s_ge

/-- info: 'ODELowerBoundExtensions.Homogeneous.HomRange.gbar_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.HomRange.gbar_ge

/-- info: 'ODELowerBoundExtensions.Homogeneous.HomRange.tau_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.HomRange.tau_ge

/-- info: 'ODELowerBoundExtensions.Homogeneous.HomRange.eps_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.HomRange.eps_pos

/-- info: 'ODELowerBoundExtensions.Homogeneous.HomRange.eps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.HomRange.eps_le

/-- info: 'ODELowerBoundExtensions.Homogeneous.pulseLen_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.pulseLen_nonneg

/-- info: 'ODELowerBoundExtensions.Homogeneous.pulseLen_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.pulseLen_le

/-- info: 'ODELowerBoundExtensions.Homogeneous.homD_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homD_nonneg

/-- info: 'ODELowerBoundExtensions.Homogeneous.exp_neg_homD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.exp_neg_homD

/-- info: 'ODELowerBoundExtensions.Homogeneous.homD_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homD_le

/-- info: 'ODELowerBoundExtensions.Homogeneous.twenty_le_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.twenty_le_tau

/-- info: 'ODELowerBoundExtensions.Homogeneous.homN_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homN_time

/-- info: 'ODELowerBoundExtensions.Homogeneous.fifth_le_homN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.fifth_le_homN

/-- info: 'ODELowerBoundExtensions.Homogeneous.one_le_homN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.one_le_homN

/-- info: 'ODELowerBoundExtensions.Homogeneous.two_eps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.two_eps_le

/-- info: 'ODELowerBoundExtensions.Homogeneous.homCorr_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homCorr_ge

/-- info: 'ODELowerBoundExtensions.Homogeneous.hom_numeric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.hom_numeric

/-! #### `ODELowerBoundExtensions.Homogeneous.Defs` -/

/-- info: 'ODELowerBoundExtensions.Homogeneous.flagCand_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.flagCand_apply

/-! #### `ODELowerBoundExtensions.Homogeneous.Table` -/

/-- info: 'ODELowerBoundExtensions.Homogeneous.homDecode_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homDecode_bound

/-- info: 'ODELowerBoundExtensions.Homogeneous.homTable_word_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homTable_word_mem

/-- info: 'ODELowerBoundExtensions.Homogeneous.homTable_value_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homTable_value_hidden

/-- info: 'ODELowerBoundExtensions.Homogeneous.homTable_value_known' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homTable_value_known

/-- info: 'ODELowerBoundExtensions.Homogeneous.stageHam_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.stageHam_diag

/-- info: 'ODELowerBoundExtensions.Homogeneous.homGen_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homGen_decoded

/-! #### `ODELowerBoundExtensions.Homogeneous.Data` -/

/-- info: 'ODELowerBoundExtensions.Homogeneous.pulseLocFun_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.pulseLocFun_injective

/-- info: 'ODELowerBoundExtensions.Homogeneous.pulseLocFun_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.pulseLocFun_zero

/-- info: 'ODELowerBoundExtensions.Homogeneous.pulseLocFun_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.pulseLocFun_one

/-- info: 'ODELowerBoundExtensions.Homogeneous.homGen_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homGen_support

/-- info: 'ODELowerBoundExtensions.Homogeneous.homGen_row_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homGen_row_covers

/-- info: 'ODELowerBoundExtensions.Homogeneous.homGen_col_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homGen_col_covers

/-- info: 'ODELowerBoundExtensions.Homogeneous.homData_locators_input_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homData_locators_input_indep

/-- info: 'ODELowerBoundExtensions.Homogeneous.homData_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homData_dyadic

/-- info: 'ODELowerBoundExtensions.Homogeneous.homLen_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homLen_nonneg

/-- info: 'ODELowerBoundExtensions.Homogeneous.homFamily_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homFamily_src

/-- info: 'ODELowerBoundExtensions.Homogeneous.homFamily_lenNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homFamily_lenNat

/-- info: 'ODELowerBoundExtensions.Homogeneous.homFamily_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homFamily_mass

/-- info: 'ODELowerBoundExtensions.Homogeneous.homFamily_start_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homFamily_start_hidden

/-- info: 'ODELowerBoundExtensions.Homogeneous.homFamily_start_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homFamily_start_y

/-- info: 'ODELowerBoundExtensions.Homogeneous.homFamily_start_damp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homFamily_start_damp

/-- info: 'ODELowerBoundExtensions.Homogeneous.homFamily_start_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homFamily_start_idle

/-- info: 'ODELowerBoundExtensions.Homogeneous.homFamily_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homFamily_T

/-! #### `ODELowerBoundExtensions.Homogeneous.Compile` -/

/-- info: 'ODELowerBoundExtensions.Homogeneous.homStageProj_isStarProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homStageProj_isStarProjection

/-- info: 'ODELowerBoundExtensions.Homogeneous.homStageProj_orthogonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homStageProj_orthogonal

/-- info: 'ODELowerBoundExtensions.Homogeneous.homStageAddressFamily_proj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homStageAddressFamily_proj_apply

/-- info: 'ODELowerBoundExtensions.Homogeneous.hitProj_homStage_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.hitProj_homStage_apply

/-- info: 'ODELowerBoundExtensions.Homogeneous.homStageGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homStageGate_unitary

/-- info: 'ODELowerBoundExtensions.Homogeneous.homStageGate_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homStageGate_apply

/-- info: 'ODELowerBoundExtensions.Homogeneous.access_hom_value_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.access_hom_value_apply

/-- info: 'ODELowerBoundExtensions.Homogeneous.implementsOn_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.implementsOn_hom

/-! #### `ODELowerBoundExtensions.Homogeneous.Endpoint` -/

/-- info: 'ODELowerBoundExtensions.Homogeneous.inner_flagCand_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.inner_flagCand_eq

/-- info: 'ODELowerBoundExtensions.Homogeneous.inner_flagCand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.inner_flagCand

/-- info: 'ODELowerBoundExtensions.Homogeneous.norm_flagCand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.norm_flagCand

/-- info: 'ODELowerBoundExtensions.Homogeneous.inner_flagCand_flagComb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.inner_flagCand_flagComb

/-- info: 'ODELowerBoundExtensions.Homogeneous.inner_flagComb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.inner_flagComb

/-- info: 'ODELowerBoundExtensions.Homogeneous.inner_flagComb_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.inner_flagComb_ofReal

/-- info: 'ODELowerBoundExtensions.Homogeneous.smul_flagComb_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.smul_flagComb_ofReal

/-- info: 'ODELowerBoundExtensions.Homogeneous.smul_flagComb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.smul_flagComb

/-- info: 'ODELowerBoundExtensions.Homogeneous.homEnd_eq_flagComb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homEnd_eq_flagComb

/-- info: 'ODELowerBoundExtensions.Homogeneous.sum_endP_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.sum_endP_sq

/-- info: 'ODELowerBoundExtensions.Homogeneous.sum_endQ_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.sum_endQ_sq

/-- info: 'ODELowerBoundExtensions.Homogeneous.norm_sq_homEnd_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.norm_sq_homEnd_eq

/-- info: 'ODELowerBoundExtensions.Homogeneous.endPQ_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.endPQ_facts

/-- info: 'ODELowerBoundExtensions.Homogeneous.norm_homInit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.norm_homInit

/-- info: 'ODELowerBoundExtensions.Homogeneous.negI_pow_mul_exp_pulse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.negI_pow_mul_exp_pulse

/-- info: 'ODELowerBoundExtensions.Homogeneous.homAlpha_homBeta_of_busy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homAlpha_homBeta_of_busy_le

/-- info: 'ODELowerBoundExtensions.Homogeneous.homSol_of_busy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homSol_of_busy_le

/-- info: 'ODELowerBoundExtensions.Homogeneous.norm_sq_homEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.norm_sq_homEnd

/-- info: 'ODELowerBoundExtensions.Homogeneous.homEnd_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homEnd_ne_zero

/-- info: 'ODELowerBoundExtensions.Homogeneous.homEnd_g_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homEnd_g_bounds

/-- info: 'ODELowerBoundExtensions.Homogeneous.unitDirection_homEnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.unitDirection_homEnd

/-- info: 'ODELowerBoundExtensions.Homogeneous.homEnd_prob_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homEnd_prob_ge

/-! #### `ODELowerBoundExtensions.Homogeneous.General` -/

/-- info: 'ODELowerBoundExtensions.Homogeneous.outer_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.outer_general

/-! #### `ODELowerBoundExtensions.Homogeneous.Generator` -/

/-- info: 'ODELowerBoundExtensions.Homogeneous.sum_norm_sq_le_one_of_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.sum_norm_sq_le_one_of_single

/-- info: 'ODELowerBoundExtensions.Homogeneous.homGen_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homGen_of_lt

/-- info: 'ODELowerBoundExtensions.Homogeneous.homGen_of_eq_n' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homGen_of_eq_n

/-- info: 'ODELowerBoundExtensions.Homogeneous.homGen_of_eq_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homGen_of_eq_succ

/-- info: 'ODELowerBoundExtensions.Homogeneous.homGen_of_eq_damp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homGen_of_eq_damp

/-- info: 'ODELowerBoundExtensions.Homogeneous.homHam_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homHam_isHermitian

/-- info: 'ODELowerBoundExtensions.Homogeneous.accretive_homGen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.accretive_homGen

/-- info: 'ODELowerBoundExtensions.Homogeneous.sum_norm_sq_homHam_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.sum_norm_sq_homHam_row

/-- info: 'ODELowerBoundExtensions.Homogeneous.sum_norm_sq_homHam_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.sum_norm_sq_homHam_col

/-- info: 'ODELowerBoundExtensions.Homogeneous.sum_norm_sq_homGen_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.sum_norm_sq_homGen_row

/-- info: 'ODELowerBoundExtensions.Homogeneous.sum_norm_sq_homGen_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.sum_norm_sq_homGen_col

/-- info: 'ODELowerBoundExtensions.Homogeneous.homGen_hidden_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homGen_hidden_true

/-- info: 'ODELowerBoundExtensions.Homogeneous.homGen_hidden_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homGen_hidden_false

/-- info: 'ODELowerBoundExtensions.Homogeneous.homGen_pulse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homGen_pulse

/-- info: 'ODELowerBoundExtensions.Homogeneous.homGen_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homGen_y

/-- info: 'ODELowerBoundExtensions.Homogeneous.homGen_reject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homGen_reject

/-- info: 'ODELowerBoundExtensions.Homogeneous.homGen_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homGen_idle

/-! #### `ODELowerBoundExtensions.Homogeneous.Readout` -/

/-- info: 'ODELowerBoundExtensions.Homogeneous.homHalfObs_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homHalfObs_inl

/-- info: 'ODELowerBoundExtensions.Homogeneous.homHalfObs_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homHalfObs_inr

/-- info: 'ODELowerBoundExtensions.Homogeneous.homHalfObs_flagCand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homHalfObs_flagCand

/-- info: 'ODELowerBoundExtensions.Homogeneous.homHalfObs_flagComb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homHalfObs_flagComb

/-- info: 'ODELowerBoundExtensions.Homogeneous.homHalfObs_isSelfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homHalfObs_isSelfAdjoint

/-- info: 'ODELowerBoundExtensions.Homogeneous.norm_homHalfObs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.norm_homHalfObs_le

/-- info: 'ODELowerBoundExtensions.Homogeneous.neg_one_le_halfSign_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.neg_one_le_halfSign_mul

/-- info: 'ODELowerBoundExtensions.Homogeneous.homEnd_ideal_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homEnd_ideal_corr

/-! #### `ODELowerBoundExtensions.Homogeneous.Solution` -/

/-- info: 'ODELowerBoundExtensions.Homogeneous.ramp_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.ramp_eq_zero

/-- info: 'ODELowerBoundExtensions.Homogeneous.hasDerivWithinAt_phaseCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.hasDerivWithinAt_phaseCoeff

/-- info: 'ODELowerBoundExtensions.Homogeneous.hasDerivWithinAt_homBeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.hasDerivWithinAt_homBeta

/-- info: 'ODELowerBoundExtensions.Homogeneous.hasDerivWithinAt_homAlpha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.hasDerivWithinAt_homAlpha

/-- info: 'ODELowerBoundExtensions.Homogeneous.hasDerivWithinAt_homSol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.hasDerivWithinAt_homSol

/-- info: 'ODELowerBoundExtensions.Homogeneous.map_homSol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.map_homSol

/-- info: 'ODELowerBoundExtensions.Homogeneous.homSol_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homSol_zero

/-- info: 'ODELowerBoundExtensions.Homogeneous.solvesODE_hom_hidden' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.solvesODE_hom_hidden

/-- info: 'ODELowerBoundExtensions.Homogeneous.solvesODE_hom_pulse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.solvesODE_hom_pulse

/-- info: 'ODELowerBoundExtensions.Homogeneous.solvesODE_hom_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.solvesODE_hom_y

/-- info: 'ODELowerBoundExtensions.Homogeneous.solvesODE_hom_damp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.solvesODE_hom_damp

/-- info: 'ODELowerBoundExtensions.Homogeneous.solvesODE_hom_idle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.solvesODE_hom_idle

/-- info: 'ODELowerBoundExtensions.Homogeneous.homSol_solves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homSol_solves

/-! #### `ODELowerBoundExtensions.Homogeneous.Theorem` -/

/-- info: 'ODELowerBoundExtensions.Homogeneous.homFamily_inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homFamily_inClass

/-- info: 'ODELowerBoundExtensions.Homogeneous.homFamily_g' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homFamily_g

/-- info: 'ODELowerBoundExtensions.Homogeneous.hom_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.hom_forces

/-- info: 'ODELowerBoundExtensions.Homogeneous.homFamilyAt_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.homFamilyAt_src

/-- info: 'ODELowerBoundExtensions.Homogeneous.card_homIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.card_homIndex

/-- info: 'ODELowerBoundExtensions.Homogeneous.hom_instance_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.hom_instance_props

/-- info: 'ODELowerBoundExtensions.Homogeneous.hom_g_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.hom_g_theta

/-- info: 'ODELowerBoundExtensions.Homogeneous.hom_bound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.hom_bound_le

/-- info: 'ODELowerBoundExtensions.Homogeneous.hom_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Homogeneous.hom_witness

/-! ### Padding remarks of Section `part:odel` (`ODELowerBoundExtensions.Padding`) -/

/-! #### `ODELowerBoundExtensions.Padding.Readout` -/

/-- info: 'ODELowerBoundExtensions.Padding.norm_inlOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.norm_inlOp

/-- info: 'ODELowerBoundExtensions.Padding.unitDirection_inlOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.unitDirection_inlOp

/-- info: 'ODELowerBoundExtensions.Padding.heraldedAccurate_padReadout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.heraldedAccurate_padReadout

/-! #### `ODELowerBoundExtensions.Padding.ZeroPad` -/

/-- info: 'ODELowerBoundExtensions.Padding.ZeroPad.matrix_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.ZeroPad.matrix_eq

/-- info: 'ODELowerBoundExtensions.Padding.ZeroPad.len_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.ZeroPad.len_eq

/-- info: 'ODELowerBoundExtensions.Padding.ZeroPad.src_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.ZeroPad.src_eq

/-- info: 'ODELowerBoundExtensions.Padding.ZeroPad.init_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.ZeroPad.init_eq

/-- info: 'ODELowerBoundExtensions.Padding.padMat_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.padMat_smul

/-- info: 'ODELowerBoundExtensions.Padding.matrixOperator_padMat_inlOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.matrixOperator_padMat_inlOp

/-- info: 'ODELowerBoundExtensions.Padding.card_padMat_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.card_padMat_row

/-- info: 'ODELowerBoundExtensions.Padding.card_padMat_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.card_padMat_col

/-- info: 'ODELowerBoundExtensions.Padding.matrixOperator_padMat_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.matrixOperator_padMat_restrict

/-- info: 'ODELowerBoundExtensions.Padding.inner_inlOp_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.inner_inlOp_restrict

/-- info: 'ODELowerBoundExtensions.Padding.solvesODE_congr_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.solvesODE_congr_apply

/-- info: 'ODELowerBoundExtensions.Padding.solvesODE_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.solvesODE_map

/-- info: 'ODELowerBoundExtensions.Padding.ZeroPad.start_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.ZeroPad.start_eq

/-- info: 'ODELowerBoundExtensions.Padding.ZeroPad.T_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.ZeroPad.T_eq

/-- info: 'ODELowerBoundExtensions.Padding.ZeroPad.mass_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.ZeroPad.mass_eq

/-- info: 'ODELowerBoundExtensions.Padding.ZeroPad.gen_inlOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.ZeroPad.gen_inlOp

/-- info: 'ODELowerBoundExtensions.Padding.ZeroPad.solves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.ZeroPad.solves

/-- info: 'ODELowerBoundExtensions.Padding.ZeroPad.inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.ZeroPad.inClass

/-- info: 'ODELowerBoundExtensions.Padding.ZeroPad.sparsityAttained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.ZeroPad.sparsityAttained

/-- info: 'ODELowerBoundExtensions.Padding.ZeroPad.heraldedAccurate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.ZeroPad.heraldedAccurate

/-! #### `ODELowerBoundExtensions.Padding.StageData` -/

/-- info: 'ODELowerBoundExtensions.Padding.stageData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.stageData_matrix

/-- info: 'ODELowerBoundExtensions.Padding.stageData_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.stageData_table

/-- info: 'ODELowerBoundExtensions.Padding.stageData_locators_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.stageData_locators_const

/-- info: 'ODELowerBoundExtensions.Padding.stageData_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.stageData_dyadic

/-! #### `ODELowerBoundExtensions.Padding.StageCompile` -/

/-- info: 'ODELowerBoundExtensions.Padding.stageBitFamily_jointTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.stageBitFamily_jointTable

/-- info: 'ODELowerBoundExtensions.Padding.stageBoolean_jointTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.stageBoolean_jointTable

/-- info: 'ODELowerBoundExtensions.Padding.stageTableGate_jointTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.stageTableGate_jointTable

/-- info: 'ODELowerBoundExtensions.Padding.stageBitFamily_proj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.stageBitFamily_proj_apply

/-- info: 'ODELowerBoundExtensions.Padding.stageTableGate_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.stageTableGate_apply

/-- info: 'ODELowerBoundExtensions.Padding.hitProj_stageBit_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.hitProj_stageBit_apply

/-- info: 'ODELowerBoundExtensions.Padding.stageTableGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.stageTableGate_unitary

/-- info: 'ODELowerBoundExtensions.Padding.stageData_value_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.stageData_value_apply

/-- info: 'ODELowerBoundExtensions.Padding.implementsOn_stageData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.implementsOn_stageData

/-! #### `ODELowerBoundExtensions.Padding.Helpers.JointDense.Block` -/

/-- info: 'ODELowerBoundExtensions.Padding.denseBlock_sum_norm_sq_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseBlock_sum_norm_sq_row

/-- info: 'ODELowerBoundExtensions.Padding.denseBlock_sum_norm_sq_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseBlock_sum_norm_sq_col

/-- info: 'ODELowerBoundExtensions.Padding.denseBlock_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseBlock_norm_le

/-- info: 'ODELowerBoundExtensions.Padding.denseBlock_matrixOperator_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseBlock_matrixOperator_eq_zero

/-- info: 'ODELowerBoundExtensions.Padding.denseBlock_card_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseBlock_card_row

/-- info: 'ODELowerBoundExtensions.Padding.denseBlock_card_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseBlock_card_col

/-- info: 'ODELowerBoundExtensions.Padding.denseBlock_add_I_smul_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseBlock_add_I_smul_apply

/-- info: 'ODELowerBoundExtensions.Padding.denseBlock_card_mul_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseBlock_card_mul_norm_le

/-- info: 'ODELowerBoundExtensions.Padding.denseBlock_card_mul_norm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseBlock_card_mul_norm_sq_le

/-! #### `ODELowerBoundExtensions.Padding.Helpers.JointDense.Words` -/

/-- info: 'ODELowerBoundExtensions.Padding.denseWord_scale_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseWord_scale_mem

/-- info: 'ODELowerBoundExtensions.Padding.denseWord_scale_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseWord_scale_decode

/-- info: 'ODELowerBoundExtensions.Padding.denseWord_ite_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseWord_ite_mem

/-- info: 'ODELowerBoundExtensions.Padding.denseJointGen_inr_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseJointGen_inr_left

/-- info: 'ODELowerBoundExtensions.Padding.denseJointGen_inr_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseJointGen_inr_right

/-! #### `ODELowerBoundExtensions.Padding.JointDense` -/

/-- info: 'ODELowerBoundExtensions.Padding.denseHam_inl_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseHam_inl_left

/-- info: 'ODELowerBoundExtensions.Padding.denseHam_inl_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseHam_inl_right

/-- info: 'ODELowerBoundExtensions.Padding.denseHam_inr_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseHam_inr_inr

/-- info: 'ODELowerBoundExtensions.Padding.denseGen_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseGen_apply

/-- info: 'ODELowerBoundExtensions.Padding.denseHam_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseHam_false

/-- info: 'ODELowerBoundExtensions.Padding.denseGen_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseGen_false

/-- info: 'ODELowerBoundExtensions.Padding.denseHam_of_not_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseHam_of_not_block

/-- info: 'ODELowerBoundExtensions.Padding.jointDenseTable_word_of_not_block' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointDenseTable_word_of_not_block

/-- info: 'ODELowerBoundExtensions.Padding.jointDenseIdle_of_not_block' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointDenseIdle_of_not_block

/-- info: 'ODELowerBoundExtensions.Padding.jointDenseTable_word_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointDenseTable_word_mem

/-- info: 'ODELowerBoundExtensions.Padding.jointDense_word_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointDense_word_bound

/-- info: 'ODELowerBoundExtensions.Padding.jointDense_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointDense_decode

/-- info: 'ODELowerBoundExtensions.Padding.denseGen_row_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseGen_row_covers

/-- info: 'ODELowerBoundExtensions.Padding.denseGen_col_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseGen_col_covers

/-- info: 'ODELowerBoundExtensions.Padding.jointDenseFamily_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointDenseFamily_matrix

/-- info: 'ODELowerBoundExtensions.Padding.jointDenseFamily_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointDenseFamily_T

/-- info: 'ODELowerBoundExtensions.Padding.jointDenseFamily_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointDenseFamily_mass

/-! #### `ODELowerBoundExtensions.Padding.JointDenseFacts` -/

/-- info: 'ODELowerBoundExtensions.Padding.denseHam_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseHam_isHermitian

/-- info: 'ODELowerBoundExtensions.Padding.denseHam_padExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.denseHam_padExp

/-- info: 'ODELowerBoundExtensions.Padding.norm_denseHam_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.norm_denseHam_le

/-- info: 'ODELowerBoundExtensions.Padding.jointSol_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointSol_inr

/-- info: 'ODELowerBoundExtensions.Padding.jointDenseSol_solves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointDenseSol_solves

/-- info: 'ODELowerBoundExtensions.Padding.jointDenseFamily_skew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointDenseFamily_skew

/-- info: 'ODELowerBoundExtensions.Padding.jointDenseFamily_inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointDenseFamily_inClass

/-- info: 'ODELowerBoundExtensions.Padding.jointDenseFamily_sparsityAttained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointDenseFamily_sparsityAttained

/-- info: 'ODELowerBoundExtensions.Padding.jointDenseFamily_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointDenseFamily_dyadic

/-- info: 'ODELowerBoundExtensions.Padding.jointDenseFamily_table_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointDenseFamily_table_false

/-- info: 'ODELowerBoundExtensions.Padding.implementsOn_jointDense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.implementsOn_jointDense

/-! #### `ODELowerBoundExtensions.Padding.JointPad` -/

/-- info: 'ODELowerBoundExtensions.Padding.padWords_eq_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.padWords_eq_value

/-- info: 'ODELowerBoundExtensions.Padding.stageWord_padTable_inl_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.stageWord_padTable_inl_inl

/-- info: 'ODELowerBoundExtensions.Padding.stageWord_padTable_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.stageWord_padTable_off

/-- info: 'ODELowerBoundExtensions.Padding.jointPad_word_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointPad_word_bound

/-- info: 'ODELowerBoundExtensions.Padding.jointPad_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointPad_decode

/-- info: 'ODELowerBoundExtensions.Padding.jointPad_row_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointPad_row_covers

/-- info: 'ODELowerBoundExtensions.Padding.jointPad_col_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointPad_col_covers

/-- info: 'ODELowerBoundExtensions.Padding.jointPadFamily_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointPadFamily_matrix

/-- info: 'ODELowerBoundExtensions.Padding.jointPadFamily_zeroPad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointPadFamily_zeroPad

/-- info: 'ODELowerBoundExtensions.Padding.jointPadFamily_zeroPad_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointPadFamily_zeroPad_joint

/-- info: 'ODELowerBoundExtensions.Padding.jointPadFamily_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointPadFamily_T

/-- info: 'ODELowerBoundExtensions.Padding.jointPadSol_solves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointPadSol_solves

/-- info: 'ODELowerBoundExtensions.Padding.jointPadFamily_inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointPadFamily_inClass

/-- info: 'ODELowerBoundExtensions.Padding.jointPadFamily_sparsityAttained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointPadFamily_sparsityAttained

/-- info: 'ODELowerBoundExtensions.Padding.jointPadFamily_skew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointPadFamily_skew

/-- info: 'ODELowerBoundExtensions.Padding.jointPadFamily_dyadic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointPadFamily_dyadic

/-- info: 'ODELowerBoundExtensions.Padding.jointPadFamily_table_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointPadFamily_table_inl

/-- info: 'ODELowerBoundExtensions.Padding.jointPadFamily_table_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointPadFamily_table_off

/-- info: 'ODELowerBoundExtensions.Padding.implementsOn_jointPad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.implementsOn_jointPad

/-- info: 'ODELowerBoundExtensions.Padding.card_jointPadIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.card_jointPadIndex

/-! #### `ODELowerBoundExtensions.Padding.JointTheorem` -/

/-- info: 'ODELowerBoundExtensions.Padding.jointMu_le_padExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointMu_le_padExp

/-- info: 'ODELowerBoundExtensions.Padding.jointMu_le_jointPadBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointMu_le_jointPadBits

/-- info: 'ODELowerBoundExtensions.Padding.le_two_pow_jointPadBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.le_two_pow_jointPadBits

/-- info: 'ODELowerBoundExtensions.Padding.joint_forces_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.joint_forces_dense

/-- info: 'ODELowerBoundExtensions.Padding.joint_forces_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.joint_forces_pad

/-- info: 'ODELowerBoundExtensions.Padding.jointZeroPad_zeroPad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointZeroPad_zeroPad

/-- info: 'ODELowerBoundExtensions.Padding.jointZeroPad_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointZeroPad_table

/-- info: 'ODELowerBoundExtensions.Padding.jointDenseFamilyAt_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointDenseFamilyAt_props

/-- info: 'ODELowerBoundExtensions.Padding.jointDenseFamilyAt_g' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointDenseFamilyAt_g

/-- info: 'ODELowerBoundExtensions.Padding.jointPadFamilyAt_g' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.jointPadFamilyAt_g

/-- info: 'ODELowerBoundExtensions.Padding.joint_witness_dense' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.joint_witness_dense

/-- info: 'ODELowerBoundExtensions.Padding.joint_witness_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.joint_witness_pad

/-- info: 'ODELowerBoundExtensions.Padding.joint_common_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.joint_common_dimension

/-- info: 'ODELowerBoundExtensions.Padding.joint_qubit_register' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.joint_qubit_register

/-! #### `ODELowerBoundExtensions.Padding.Precision` -/

/-- info: 'ODELowerBoundExtensions.Padding.sparsityAttained_hamFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.sparsityAttained_hamFamily

/-- info: 'ODELowerBoundExtensions.Padding.timePadFamilyAt_zeroPad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.timePadFamilyAt_zeroPad

/-- info: 'ODELowerBoundExtensions.Padding.mixedPadFamilyAt_zeroPad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.mixedPadFamilyAt_zeroPad

/-- info: 'ODELowerBoundExtensions.Padding.precisionPadFamilyAt_zeroPad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.precisionPadFamilyAt_zeroPad

/-- info: 'ODELowerBoundExtensions.Padding.herald_instances_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.herald_instances_pad

/-- info: 'ODELowerBoundExtensions.Padding.herald_pad_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.herald_pad_props

/-- info: 'ODELowerBoundExtensions.Padding.time_forces_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.time_forces_pad

/-- info: 'ODELowerBoundExtensions.Padding.mixed_forces_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.mixed_forces_pad

/-- info: 'ODELowerBoundExtensions.Padding.precision_forces_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.precision_forces_pad

/-- info: 'ODELowerBoundExtensions.Padding.precision_forces_sqrt_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.precision_forces_sqrt_pad

/-- info: 'ODELowerBoundExtensions.Padding.herald_max_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.herald_max_pad

/-- info: 'ODELowerBoundExtensions.Padding.herald_witness_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.herald_witness_pad

/-- info: 'ODELowerBoundExtensions.Padding.precision_terms_witness_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.precision_terms_witness_pad

/-! #### `ODELowerBoundExtensions.Padding.Combined` -/

/-- info: 'ODELowerBoundExtensions.Padding.combined_max_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.combined_max_pad

/-- info: 'ODELowerBoundExtensions.Padding.combined_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.combined_pad

/-- info: 'ODELowerBoundExtensions.Padding.combined_pad_sparsityAttained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.combined_pad_sparsityAttained

/-- info: 'ODELowerBoundExtensions.Padding.card_le_of_combinedDim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.card_le_of_combinedDim

/-- info: 'ODELowerBoundExtensions.Padding.combined_max_common_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.combined_max_common_dimension

/-- info: 'ODELowerBoundExtensions.Padding.combined_common_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.combined_common_dimension

/-- info: 'ODELowerBoundExtensions.Padding.combined_qubit_register' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.combined_qubit_register

/-- info: 'ODELowerBoundExtensions.Padding.exists_qubit_register' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Padding.exists_qubit_register

/-! ### Retry protocols and the released solver (`ODELowerBoundExtensions.Release`) -/

/-! #### `ODELowerBoundExtensions.Release.Model` -/

/-- info: 'ODELowerBoundExtensions.Release.RetrySolver.readout_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.RetrySolver.readout_isometry

/-- info: 'ODELowerBoundExtensions.Release.RetrySolver.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.RetrySolver.success

/-- info: 'ODELowerBoundExtensions.Release.RetrySolver.accurate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.RetrySolver.accurate

/-- info: 'ODELowerBoundExtensions.Release.RetryWitnesses.inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.RetryWitnesses.inClass

/-- info: 'ODELowerBoundExtensions.Release.RetryWitnesses.time_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.RetryWitnesses.time_eq

/-- info: 'ODELowerBoundExtensions.Release.RetryWitnesses.forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.RetryWitnesses.forces

/-- info: 'ODELowerBoundExtensions.Release.RetryWitnesses.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.RetryWitnesses.mono

/-- info: 'ODELowerBoundExtensions.Release.maxCost_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.maxCost_mono

/-- info: 'ODELowerBoundExtensions.Release.worstCost_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.worstCost_mono

/-- info: 'ODELowerBoundExtensions.Release.program_cost_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.program_cost_mul

/-- info: 'ODELowerBoundExtensions.Release.maxCost_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.maxCost_mul

/-- info: 'ODELowerBoundExtensions.Release.worstCost_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.worstCost_mul

/-! #### `ODELowerBoundExtensions.Release.Refine` -/

/-- info: 'ODELowerBoundExtensions.Release.reindexData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.reindexData_matrix

/-- info: 'ODELowerBoundExtensions.Release.oracles_reindexData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.oracles_reindexData

/-- info: 'ODELowerBoundExtensions.Release.refineFamily_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.refineFamily_gen

/-- info: 'ODELowerBoundExtensions.Release.refineFamily_lenNat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.refineFamily_lenNat

/-- info: 'ODELowerBoundExtensions.Release.refineFamily_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.refineFamily_start

/-- info: 'ODELowerBoundExtensions.Release.sum_stageOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.sum_stageOf

/-- info: 'ODELowerBoundExtensions.Release.refineFamily_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.refineFamily_T

/-- info: 'ODELowerBoundExtensions.Release.refineFamily_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.refineFamily_mass

/-- info: 'ODELowerBoundExtensions.Release.refine_isMesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.refine_isMesh

/-- info: 'ODELowerBoundExtensions.Release.refine_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.refine_interval

/-- info: 'ODELowerBoundExtensions.Release.refine_meshMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.refine_meshMass

/-- info: 'ODELowerBoundExtensions.Release.refine_quadrature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.refine_quadrature

/-- info: 'ODELowerBoundExtensions.Release.refine_solves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.refine_solves

/-- info: 'ODELowerBoundExtensions.Release.refineFamily_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.refineFamily_access

/-- info: 'ODELowerBoundExtensions.Release.stageEmbed_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.stageEmbed_apply

/-- info: 'ODELowerBoundExtensions.Release.stageEmbed_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.stageEmbed_isometry

/-- info: 'ODELowerBoundExtensions.Release.access_stageEmbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.access_stageEmbed

/-- info: 'ODELowerBoundExtensions.Release.implementsOn_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.implementsOn_stage

/-! #### `ODELowerBoundExtensions.Release.Registers` -/

/-- info: 'ODELowerBoundExtensions.Release.jointFlatten_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.jointFlatten_apply

/-- info: 'ODELowerBoundExtensions.Release.diagonal_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.diagonal_conj

/-- info: 'ODELowerBoundExtensions.Release.diagonal_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.diagonal_fiber

/-- info: 'ODELowerBoundExtensions.Release.fiber_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.fiber_conj

/-- info: 'ODELowerBoundExtensions.Release.fiber_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.fiber_fiber

/-- info: 'ODELowerBoundExtensions.Release.isWrap_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.isWrap_fiber

/-- info: 'ODELowerBoundExtensions.Release.IsWrap.conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.IsWrap.conj

/-- info: 'ODELowerBoundExtensions.Release.IsWrap.precomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.IsWrap.precomp

/-- info: 'ODELowerBoundExtensions.Release.IsWrap.fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.IsWrap.fiber

/-- info: 'ODELowerBoundExtensions.Release.IsWrap.comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.IsWrap.comp

/-- info: 'ODELowerBoundExtensions.Release.IsWrap.masked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.IsWrap.masked

/-- info: 'ODELowerBoundExtensions.Release.IsWrap.diagonalConst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.IsWrap.diagonalConst

/-- info: 'ODELowerBoundExtensions.Release.IsWrap.spectator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.IsWrap.spectator

/-- info: 'ODELowerBoundExtensions.Release.IsWrap.diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.IsWrap.diagonal

/-- info: 'ODELowerBoundExtensions.Release.isWrap_spectator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.isWrap_spectator

/-! #### `ODELowerBoundExtensions.Release.Normal` -/

/-- info: 'ODELowerBoundExtensions.Release.PublicSources.initial_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.PublicSources.initial_unitary

/-- info: 'ODELowerBoundExtensions.Release.PublicSources.forcing_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.PublicSources.forcing_unitary

/-- info: 'ODELowerBoundExtensions.Release.PublicSources.initial_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.PublicSources.initial_const

/-- info: 'ODELowerBoundExtensions.Release.PublicSources.forcing_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.PublicSources.forcing_const

/-- info: 'ODELowerBoundExtensions.Release.isWrap_cayleyWrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.isWrap_cayleyWrap

/-- info: 'ODELowerBoundExtensions.Release.cayleyOracle_eq_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.cayleyOracle_eq_wrap

/-- info: 'ODELowerBoundExtensions.Release.isWrap_outerWrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.isWrap_outerWrap

/-- info: 'ODELowerBoundExtensions.Release.physicalOracle_inl_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.physicalOracle_inl_eq

/-- info: 'ODELowerBoundExtensions.Release.physicalOracle_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.physicalOracle_normal_form

/-- info: 'ODELowerBoundExtensions.Release.physicalOracle_inr_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.physicalOracle_inr_const

/-! #### `ODELowerBoundExtensions.Release.Access` -/

/-- info: 'ODELowerBoundExtensions.Release.searchGrowth_conj_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.searchGrowth_conj_fiber

/-- info: 'ODELowerBoundExtensions.Release.stageAccess_hamFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.stageAccess_hamFamily

/-- info: 'ODELowerBoundExtensions.Release.searchGrowth_release_ham' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.searchGrowth_release_ham

/-- info: 'ODELowerBoundExtensions.Release.comp_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.comp_isometry

/-- info: 'ODELowerBoundExtensions.Release.implementsOn_release_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.implementsOn_release_joint

/-! #### `ODELowerBoundExtensions.Release.Kernel` -/

/-- info: 'ODELowerBoundExtensions.Release.norm_trialKernel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.norm_trialKernel_le

/-- info: 'ODELowerBoundExtensions.Release.norm_kernel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.norm_kernel_le

/-- info: 'ODELowerBoundExtensions.Release.kernel_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.kernel_self

/-- info: 'ODELowerBoundExtensions.Release.inner_phase_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.inner_phase_sub

/-- info: 'ODELowerBoundExtensions.Release.sum_sum_sum_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.sum_sum_sum_comm

/-- info: 'ODELowerBoundExtensions.Release.abs_progressL_query_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.abs_progressL_query_sub_le

/-- info: 'ODELowerBoundExtensions.Release.abs_progressL_program_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.abs_progressL_program_sub_le

/-- info: 'ODELowerBoundExtensions.Release.abs_kernel_progress_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.abs_kernel_progress_le

/-! #### `ODELowerBoundExtensions.Release.Purify` -/

/-- info: 'ODELowerBoundExtensions.Release.inner_tens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.inner_tens

/-- info: 'ODELowerBoundExtensions.Release.norm_tens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.norm_tens

/-- info: 'ODELowerBoundExtensions.Release.norm_coordMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.norm_coordMatrix_le

/-- info: 'ODELowerBoundExtensions.Release.coordLift_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.coordLift_apply

/-- info: 'ODELowerBoundExtensions.Release.coordLift_tens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.coordLift_tens

/-- info: 'ODELowerBoundExtensions.Release.fiber_tens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.fiber_tens

/-- info: 'ODELowerBoundExtensions.Release.coordLift_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.coordLift_fiber

/-- info: 'ODELowerBoundExtensions.Release.coordLift_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.coordLift_comp

/-- info: 'ODELowerBoundExtensions.Release.inner_coordLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.inner_coordLift

/-- info: 'ODELowerBoundExtensions.Release.norm_coordLift_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.norm_coordLift_apply_le

/-- info: 'ODELowerBoundExtensions.Release.inner_trialVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.inner_trialVec

/-- info: 'ODELowerBoundExtensions.Release.inner_trialVec_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.inner_trialVec_fiber

/-- info: 'ODELowerBoundExtensions.Release.norm_trialVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.norm_trialVec

/-- info: 'ODELowerBoundExtensions.Release.purification_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.purification_step

/-- info: 'ODELowerBoundExtensions.Release.exists_purification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.exists_purification

/-! #### `ODELowerBoundExtensions.Release.Adversary` -/

/-- info: 'ODELowerBoundExtensions.Release.retry_decision_count_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.retry_decision_count_ge

/-! #### `ODELowerBoundExtensions.Release.Joint` -/

/-- info: 'ODELowerBoundExtensions.Release.outer_count_ge_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.outer_count_ge_retry

/-- info: 'ODELowerBoundExtensions.Release.joint_general_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.joint_general_retry

/-- info: 'ODELowerBoundExtensions.Release.joint_forces_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.joint_forces_retry

/-- info: 'ODELowerBoundExtensions.Release.joint_witness_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.joint_witness_retry

/-! #### `ODELowerBoundExtensions.Release.Herald` -/

/-- info: 'ODELowerBoundExtensions.Release.retryForces_of_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.retryForces_of_tree

/-- info: 'ODELowerBoundExtensions.Release.time_forces_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.time_forces_retry

/-- info: 'ODELowerBoundExtensions.Release.mixed_forces_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.mixed_forces_retry

/-- info: 'ODELowerBoundExtensions.Release.precision_forces_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.precision_forces_retry

/-- info: 'ODELowerBoundExtensions.Release.precision_forces_sqrt_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.precision_forces_sqrt_retry

/-! #### `ODELowerBoundExtensions.Release.Embed` -/

/-- info: 'ODELowerBoundExtensions.Release.norm_normSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.norm_normSeed

/-- info: 'ODELowerBoundExtensions.Release.heraldSpace_subtypeL_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.heraldSpace_subtypeL_isometry

/-- info: 'ODELowerBoundExtensions.Release.subtypeL_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.subtypeL_adjoint_apply

/-- info: 'ODELowerBoundExtensions.Release.toRetryReadout_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.toRetryReadout_isometry

/-- info: 'ODELowerBoundExtensions.Release.toTrial_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.toTrial_amplitude

/-- info: 'ODELowerBoundExtensions.Release.toTrial_meanSuccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.toTrial_meanSuccess

/-- info: 'ODELowerBoundExtensions.Release.toRetryProt_successMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.toRetryProt_successMass

/-- info: 'ODELowerBoundExtensions.Release.toRetry_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.toRetry_success

/-- info: 'ODELowerBoundExtensions.Release.toRetry_conditionalDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.toRetry_conditionalDensity

/-- info: 'ODELowerBoundExtensions.Release.toRetry_accurate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.toRetry_accurate

/-- info: 'ODELowerBoundExtensions.Release.toRetry_worstCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.toRetry_worstCost

/-- info: 'ODELowerBoundExtensions.Release.seed_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.seed_ne_zero

/-- info: 'ODELowerBoundExtensions.Release.retryForces_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.retryForces_forces

/-- info: 'ODELowerBoundExtensions.Release.retryWitnesses_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.retryWitnesses_witnesses

/-! #### `ODELowerBoundExtensions.Release.Theorem` -/

/-- info: 'ODELowerBoundExtensions.Release.forces_or_of_max_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.forces_or_of_max_retry

/-- info: 'ODELowerBoundExtensions.Release.herald_max_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.herald_max_retry

/-- info: 'ODELowerBoundExtensions.Release.herald_witness_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.herald_witness_retry

/-- info: 'ODELowerBoundExtensions.Release.precision_terms_witness_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.precision_terms_witness_retry

/-- info: 'ODELowerBoundExtensions.Release.combined_max_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.combined_max_retry

/-- info: 'ODELowerBoundExtensions.Release.combined_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.combined_retry

/-! #### `ODELowerBoundExtensions.Release.Bridge` -/

/-- info: 'ODELowerBoundExtensions.Release.matrixWeight_value_le' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.matrixWeight_value_le

/-- info: 'ODELowerBoundExtensions.Release.matrixWeight_hardCost' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.matrixWeight_hardCost

/-- info: 'ODELowerBoundExtensions.Release.worstCost_value_le_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.worstCost_value_le_matrix

/-- info: 'ODELowerBoundExtensions.Release.RetrySolver.accurate_ham' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.RetrySolver.accurate_ham

/-- info: 'ODELowerBoundExtensions.Release.joint_release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.joint_release

/-- info: 'ODELowerBoundExtensions.Release.mixed_release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.mixed_release

/-- info: 'ODELowerBoundExtensions.Release.precision_release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.precision_release

/-- info: 'ODELowerBoundExtensions.Release.combined_max_release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.combined_max_release

/-! #### `ODELowerBoundExtensions.Release.Strip` -/

/-- info: 'ODELowerBoundExtensions.Release.stripIdle_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.stripIdle_eval

/-- info: 'ODELowerBoundExtensions.Release.stripIdle_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.stripIdle_cost

/-- info: 'ODELowerBoundExtensions.Release.mapTrial_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.mapTrial_amplitude

/-- info: 'ODELowerBoundExtensions.Release.mapTrial_meanSuccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.mapTrial_meanSuccess

/-- info: 'ODELowerBoundExtensions.Release.mapTrial_oneTrialDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.mapTrial_oneTrialDensity

/-- info: 'ODELowerBoundExtensions.Release.mapTrial_maxCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.mapTrial_maxCost

/-- info: 'ODELowerBoundExtensions.Release.mapProtocol_failureMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.mapProtocol_failureMass

/-- info: 'ODELowerBoundExtensions.Release.mapProtocol_successDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.mapProtocol_successDensity

/-- info: 'ODELowerBoundExtensions.Release.mapProtocol_successMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.mapProtocol_successMass

/-- info: 'ODELowerBoundExtensions.Release.mapProtocol_conditionalDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.mapProtocol_conditionalDensity

/-- info: 'ODELowerBoundExtensions.Release.mapProtocol_worstCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.mapProtocol_worstCost

/-- info: 'ODELowerBoundExtensions.Release.certificate_densityAccurate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.certificate_densityAccurate

/-! #### `ODELowerBoundExtensions.Release.Instances` -/

/-- info: 'ODELowerBoundExtensions.Release.norm_seedVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.norm_seedVec

/-- info: 'ODELowerBoundExtensions.Release.prepUnitary_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.prepUnitary_unitary

/-- info: 'ODELowerBoundExtensions.Release.prepUnitary_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.prepUnitary_seed

/-- info: 'ODELowerBoundExtensions.Release.releaseSources_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.releaseSources_public

/-- info: 'ODELowerBoundExtensions.Release.releaseLog_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.releaseLog_eq

/-- info: 'ODELowerBoundExtensions.Release.ReleaseProtocol.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.ReleaseProtocol.success

/-- info: 'ODELowerBoundExtensions.Release.ReleaseProtocol.accurate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.ReleaseProtocol.accurate

/-- info: 'ODELowerBoundExtensions.Release.ReleaseProtocol.worstCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.ReleaseProtocol.worstCost_le

/-- info: 'ODELowerBoundExtensions.Release.exists_release_params' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.exists_release_params

/-- info: 'ODELowerBoundExtensions.Release.hamiltonianPart_I_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.hamiltonianPart_I_smul

/-- info: 'ODELowerBoundExtensions.Release.dissipativePart_I_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.dissipativePart_I_smul

/-- info: 'ODELowerBoundExtensions.Release.exists_releaseProtocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.exists_releaseProtocol

/-! #### `ODELowerBoundExtensions.Release.Theta` -/

/-- info: 'ODELowerBoundExtensions.Release.ReleaseRun.R_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.ReleaseRun.R_pos

/-- info: 'ODELowerBoundExtensions.Release.ReleaseRun.sources_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.ReleaseRun.sources_public

/-- info: 'ODELowerBoundExtensions.Release.ReleaseRun.release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.ReleaseRun.release

/-- info: 'ODELowerBoundExtensions.Release.ReleaseRun.valueQueries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.ReleaseRun.valueQueries_le

/-- info: 'ODELowerBoundExtensions.Release.queryShape_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.queryShape_le_mul

/-- info: 'ODELowerBoundExtensions.Release.queryShape_le_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.queryShape_le_of_le

/-- info: 'ODELowerBoundExtensions.Release.one_le_releaseLog_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.one_le_releaseLog_of

/-- info: 'ODELowerBoundExtensions.Release.ReleaseRun.matrixQueries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.ReleaseRun.matrixQueries_le

/-- info: 'ODELowerBoundExtensions.Release.releaseRun_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.releaseRun_nonempty

/-- info: 'ODELowerBoundExtensions.Release.joint_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.joint_nonempty

/-- info: 'ODELowerBoundExtensions.Release.one_le_releaseLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.one_le_releaseLog

/-- info: 'ODELowerBoundExtensions.Release.release_shape_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.release_shape_le

/-- info: 'ODELowerBoundExtensions.Release.release_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.release_theta

/-- info: 'ODELowerBoundExtensions.Release.release_theta_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.release_theta_exists

/-- info: 'ODELowerBoundExtensions.Release.release_theta_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.release_theta_bracket

/-- info: 'ODELowerBoundExtensions.Release.joint_release_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Release.joint_release_theta

/-! ### Lemma `odel:lem:dyson` (`ODELowerBoundExtensions.Dyson`) -/

/-! #### `ODELowerBoundExtensions.Dyson.Degree` -/

/-- info: 'ODELowerBoundExtensions.Dyson.hasSum_expTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.hasSum_expTail

/-- info: 'ODELowerBoundExtensions.Dyson.expTail_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.expTail_nonneg

/-- info: 'ODELowerBoundExtensions.Dyson.expTail_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.expTail_mono

/-- info: 'ODELowerBoundExtensions.Dyson.expTail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.expTail_le

/-- info: 'ODELowerBoundExtensions.Dyson.dysonLog_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.dysonLog_pos

/-- info: 'ODELowerBoundExtensions.Dyson.one_le_log_exp_one_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.one_le_log_exp_one_add

/-- info: 'ODELowerBoundExtensions.Dyson.le_mul_log_of_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.le_mul_log_of_gt

/-- info: 'ODELowerBoundExtensions.Dyson.expTail_truncDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.expTail_truncDegree_le

/-- info: 'ODELowerBoundExtensions.Dyson.truncDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.truncDegree_le

/-- info: 'ODELowerBoundExtensions.Dyson.cost_le_dysonBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.cost_le_dysonBound

/-! #### `ODELowerBoundExtensions.Dyson.Fixed` -/

/-- info: 'ODELowerBoundExtensions.Dyson.dysonLog_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.dysonLog_eq

/-- info: 'ODELowerBoundExtensions.Dyson.le_log_one_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.le_log_one_div

/-- info: 'ODELowerBoundExtensions.Dyson.dyson_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.dyson_fixed

/-- info: 'ODELowerBoundExtensions.Dyson.eventually_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.eventually_lt

/-! #### `ODELowerBoundExtensions.Dyson.Access` -/

/-- info: 'ODELowerBoundExtensions.Dyson.flatGate_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.flatGate_mul

/-- info: 'ODELowerBoundExtensions.Dyson.timeOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.timeOracle_unitary

/-- info: 'ODELowerBoundExtensions.Dyson.timeOracle_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.timeOracle_valid

/-- info: 'ODELowerBoundExtensions.Dyson.matrixOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.matrixOracle_unitary

/-- info: 'ODELowerBoundExtensions.Dyson.productFlatten_symm_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.productFlatten_symm_single

/-- info: 'ODELowerBoundExtensions.Dyson.matrix_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.matrix_valid

/-- info: 'ODELowerBoundExtensions.Dyson.timeSwap_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.timeSwap_unitary

/-- info: 'ODELowerBoundExtensions.Dyson.timeSwap_timeEmbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.timeSwap_timeEmbed

/-- info: 'ODELowerBoundExtensions.Dyson.flatGate_layout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.flatGate_layout

/-- info: 'ODELowerBoundExtensions.Dyson.payloadEncoding_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.payloadEncoding_isometry

/-- info: 'ODELowerBoundExtensions.Dyson.sampleOperator_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.sampleOperator_norm_le

/-- info: 'ODELowerBoundExtensions.Dyson.matrixOperator_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.matrixOperator_eq_smul

/-- info: 'ODELowerBoundExtensions.Dyson.slot_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.slot_compression

/-! #### `ODELowerBoundExtensions.Dyson.Flagged` -/

/-- info: 'ODELowerBoundExtensions.Dyson.flipEquiv_flipEquiv' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.flipEquiv_flipEquiv

/-- info: 'ODELowerBoundExtensions.Dyson.adjoint_apply_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.adjoint_apply_self

/-- info: 'ODELowerBoundExtensions.Dyson.encodedProjector_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.encodedProjector_idem

/-- info: 'ODELowerBoundExtensions.Dyson.encodedProjector_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.encodedProjector_adjoint

/-- info: 'ODELowerBoundExtensions.Dyson.one_sub_encodedProjector_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.one_sub_encodedProjector_adjoint

/-- info: 'ODELowerBoundExtensions.Dyson.flagSplit_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.flagSplit_apply

/-- info: 'ODELowerBoundExtensions.Dyson.flagSplit_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.flagSplit_adjoint

/-- info: 'ODELowerBoundExtensions.Dyson.flagSplit_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.flagSplit_mul_self

/-- info: 'ODELowerBoundExtensions.Dyson.flagSplit_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.flagSplit_unitary

/-- info: 'ODELowerBoundExtensions.Dyson.zeroFlags_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.zeroFlags_apply

/-- info: 'ODELowerBoundExtensions.Dyson.zeroFlags_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.zeroFlags_adjoint_apply

/-- info: 'ODELowerBoundExtensions.Dyson.zeroFlags_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.zeroFlags_isometry

/-- info: 'ODELowerBoundExtensions.Dyson.layer_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.layer_apply

/-- info: 'ODELowerBoundExtensions.Dyson.flagged_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.flagged_invariant

/-- info: 'ODELowerBoundExtensions.Dyson.flagged_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.flagged_compression

/-! #### `ODELowerBoundExtensions.Dyson.Series` -/

/-- info: 'ODELowerBoundExtensions.Dyson.Cfg.degree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.Cfg.degree_le

/-- info: 'ODELowerBoundExtensions.Dyson.Cfg.extend_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.Cfg.extend_last

/-- info: 'ODELowerBoundExtensions.Dyson.Cfg.extend_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.Cfg.extend_restrict

/-- info: 'ODELowerBoundExtensions.Dyson.Cfg.restrict_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.Cfg.restrict_extend

/-- info: 'ODELowerBoundExtensions.Dyson.Cfg.count_extend_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.Cfg.count_extend_self

/-- info: 'ODELowerBoundExtensions.Dyson.Cfg.count_extend_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.Cfg.count_extend_of_lt

/-- info: 'ODELowerBoundExtensions.Dyson.coef_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.coef_nonneg

/-- info: 'ODELowerBoundExtensions.Dyson.coef_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.coef_zero

/-- info: 'ODELowerBoundExtensions.Dyson.coef_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.coef_extend

/-- info: 'ODELowerBoundExtensions.Dyson.sum_coef_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.sum_coef_le_exp

/-- info: 'ODELowerBoundExtensions.Dyson.one_le_sum_coef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.one_le_sum_coef

/-- info: 'ODELowerBoundExtensions.Dyson.expTail_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.expTail_add

/-- info: 'ODELowerBoundExtensions.Dyson.opNorm_eq_zero_of_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.opNorm_eq_zero_of_subsingleton

/-- info: 'ODELowerBoundExtensions.Dyson.norm_pow_le_norm_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.norm_pow_le_norm_pow

/-- info: 'ODELowerBoundExtensions.Dyson.evolution_real_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.evolution_real_smul

/-- info: 'ODELowerBoundExtensions.Dyson.cfgProduct_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.cfgProduct_smul

/-- info: 'ODELowerBoundExtensions.Dyson.cfgProduct_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.cfgProduct_norm_le_one

/-- info: 'ODELowerBoundExtensions.Dyson.cfgProduct_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.cfgProduct_extend

/-- info: 'ODELowerBoundExtensions.Dyson.truncated_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.truncated_succ

/-- info: 'ODELowerBoundExtensions.Dyson.evolution_exp_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.evolution_exp_norm_le

/-- info: 'ODELowerBoundExtensions.Dyson.exp_sub_partial_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.exp_sub_partial_norm_le

/-- info: 'ODELowerBoundExtensions.Dyson.truncated_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.truncated_error

/-! #### `ODELowerBoundExtensions.Dyson.Slots` -/

/-- info: 'ODELowerBoundExtensions.Dyson.Cfg.start_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.Cfg.start_zero

/-- info: 'ODELowerBoundExtensions.Dyson.Cfg.start_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.Cfg.start_last

/-- info: 'ODELowerBoundExtensions.Dyson.Cfg.start_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.Cfg.start_mono

/-- info: 'ODELowerBoundExtensions.Dyson.Cfg.start_succ_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.Cfg.start_succ_sub

/-- info: 'ODELowerBoundExtensions.Dyson.Cfg.active_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.Cfg.active_iff

/-- info: 'ODELowerBoundExtensions.Dyson.Cfg.cell_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.Cfg.cell_spec

/-- info: 'ODELowerBoundExtensions.Dyson.Cfg.cell_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.Cfg.cell_eq

/-- info: 'ODELowerBoundExtensions.Dyson.slot_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.slot_product

/-! #### `ODELowerBoundExtensions.Dyson.Select` -/

/-- info: 'ODELowerBoundExtensions.Dyson.liftSlot_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.liftSlot_eval

/-- info: 'ODELowerBoundExtensions.Dyson.liftSlot_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.liftSlot_cost

/-- info: 'ODELowerBoundExtensions.Dyson.liftSlot_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.liftSlot_count

/-- info: 'ODELowerBoundExtensions.Dyson.timeGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.timeGate_unitary

/-- info: 'ODELowerBoundExtensions.Dyson.slotProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.slotProgram_eval

/-- info: 'ODELowerBoundExtensions.Dyson.selectUpTo_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.selectUpTo_eval

/-- info: 'ODELowerBoundExtensions.Dyson.logicalSelect_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.logicalSelect_eval

/-- info: 'ODELowerBoundExtensions.Dyson.timeSwap_comp_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.timeSwap_comp_self

/-- info: 'ODELowerBoundExtensions.Dyson.slotOperator_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.slotOperator_compression

/-- info: 'ODELowerBoundExtensions.Dyson.branchOperator_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.branchOperator_norm_le

/-- info: 'ODELowerBoundExtensions.Dyson.evolution_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.evolution_one

/-- info: 'ODELowerBoundExtensions.Dyson.logicalSelect_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.logicalSelect_compression

/-- info: 'ODELowerBoundExtensions.Dyson.slotProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.slotProgram_count

/-- info: 'ODELowerBoundExtensions.Dyson.slotProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.slotProgram_cost

/-- info: 'ODELowerBoundExtensions.Dyson.selectUpTo_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.selectUpTo_count

/-- info: 'ODELowerBoundExtensions.Dyson.selectUpTo_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.selectUpTo_cost

/-- info: 'ODELowerBoundExtensions.Dyson.logicalSelect_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.logicalSelect_count

/-- info: 'ODELowerBoundExtensions.Dyson.logicalSelect_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.logicalSelect_cost

/-! #### `ODELowerBoundExtensions.Dyson.Compile` -/

/-- info: 'ODELowerBoundExtensions.Dyson.encoding_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.encoding_isometry

/-- info: 'ODELowerBoundExtensions.Dyson.select_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.select_unitary

/-- info: 'ODELowerBoundExtensions.Dyson.select_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.select_compression

/-- info: 'ODELowerBoundExtensions.Dyson.select_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.select_count

/-- info: 'ODELowerBoundExtensions.Dyson.select_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.select_cost

/-- info: 'ODELowerBoundExtensions.Dyson.decoded_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.decoded_select

/-! #### `ODELowerBoundExtensions.Dyson.Helpers.TargetCoef` -/

/-- info: 'ODELowerBoundExtensions.Dyson.coef_mul_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.coef_mul_const

/-- info: 'ODELowerBoundExtensions.Dyson.truncated_eq_of_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.truncated_eq_of_smul

/-- info: 'ODELowerBoundExtensions.Dyson.norms_smul_eq_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.norms_smul_eq_sources

/-! #### `ODELowerBoundExtensions.Dyson.Helpers.TargetMesh` -/

/-- info: 'ODELowerBoundExtensions.Dyson.mesh_selected_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.mesh_selected_error

/-! #### `ODELowerBoundExtensions.Dyson.Target` -/

/-- info: 'ODELowerBoundExtensions.Dyson.branchRates_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.branchRates_nonneg

/-- info: 'ODELowerBoundExtensions.Dyson.norm_dysonCoeff_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.norm_dysonCoeff_inl

/-- info: 'ODELowerBoundExtensions.Dyson.coefficientMass_dysonCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.coefficientMass_dysonCoeff

/-- info: 'ODELowerBoundExtensions.Dyson.mass_le_lcuMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.mass_le_lcuMass

/-- info: 'ODELowerBoundExtensions.Dyson.lcuMass_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.lcuMass_le

/-- info: 'ODELowerBoundExtensions.Dyson.lcuTarget_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.lcuTarget_eq

/-- info: 'ODELowerBoundExtensions.Dyson.lcuTarget_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.lcuTarget_norm_le

/-- info: 'ODELowerBoundExtensions.Dyson.branch_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.branch_sum_eq

/-- info: 'ODELowerBoundExtensions.Dyson.lcuTarget_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.lcuTarget_error

/-! #### `ODELowerBoundExtensions.Dyson.Herald` -/

/-- info: 'ODELowerBoundExtensions.Dyson.herald_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.herald_bounds

/-! #### `ODELowerBoundExtensions.Dyson.Trials` -/

/-- info: 'ODELowerBoundExtensions.Dyson.certificate_of_herald' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.certificate_of_herald

/-- info: 'ODELowerBoundExtensions.Dyson.queryShape_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.queryShape_zero

/-! #### `ODELowerBoundExtensions.Dyson.Theorem` -/

/-- info: 'ODELowerBoundExtensions.Dyson.shape_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.shape_eq

/-- info: 'ODELowerBoundExtensions.Dyson.dyson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.dyson

/-! #### `ODELowerBoundExtensions.Dyson.Corollaries` -/

/-- info: 'ODELowerBoundExtensions.Dyson.quadrature_le_publicError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.quadrature_le_publicError

/-- info: 'ODELowerBoundExtensions.Dyson.dyson_release_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.dyson_release_class

/-- info: 'ODELowerBoundExtensions.Dyson.certificate_queries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.certificate_queries_le

/-- info: 'ODELowerBoundExtensions.Dyson.queries_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.queries_fixed

/-! #### `ODELowerBoundExtensions.Dyson.Family.Rescale` -/

/-- info: 'ODELowerBoundExtensions.Dyson.tail_matrix_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.tail_matrix_of_le

/-! #### `ODELowerBoundExtensions.Dyson.Family.Mesh` -/

/-- info: 'ODELowerBoundExtensions.Dyson.hasDerivWithinAt_Icc_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.hasDerivWithinAt_Icc_self

/-- info: 'ODELowerBoundExtensions.Dyson.zero_solves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.zero_solves

/-- info: 'ODELowerBoundExtensions.Dyson.mass_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.mass_nonneg

/-- info: 'ODELowerBoundExtensions.Dyson.mass_pos_of_inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.mass_pos_of_inClass

/-- info: 'ODELowerBoundExtensions.Dyson.entry_le_of_inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.entry_le_of_inClass

/-- info: 'ODELowerBoundExtensions.Dyson.exists_refinement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.exists_refinement

/-- info: 'ODELowerBoundExtensions.Dyson.dysonBound_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.dysonBound_nonneg

/-- info: 'ODELowerBoundExtensions.Dyson.dysonBound_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.dysonBound_pos

/-- info: 'ODELowerBoundExtensions.Dyson.sourceWeight_le_total' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.sourceWeight_le_total

/-! #### `ODELowerBoundExtensions.Dyson.Family.Transport` -/

/-- info: 'ODELowerBoundExtensions.Dyson.familyLayout_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.familyLayout_matrix

/-- info: 'ODELowerBoundExtensions.Dyson.knownSource_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.knownSource_unitary

/-- info: 'ODELowerBoundExtensions.Dyson.oracle_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.oracle_inr

/-- info: 'ODELowerBoundExtensions.Dyson.sourceFreeProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.sourceFreeProgram_eval

/-- info: 'ODELowerBoundExtensions.Dyson.sourceFreeProgram_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.sourceFreeProgram_matrix_cost

/-- info: 'ODELowerBoundExtensions.Dyson.sourceFreeProgram_source_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.sourceFreeProgram_source_cost

/-- info: 'ODELowerBoundExtensions.Dyson.certificate_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.certificate_transport

/-! #### `ODELowerBoundExtensions.Dyson.Family.Sources` -/

/-- info: 'ODELowerBoundExtensions.Dyson.exists_sourceFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.exists_sourceFree

/-! #### `ODELowerBoundExtensions.Dyson.Family.Theorem` -/

/-- info: 'ODELowerBoundExtensions.Dyson.family_dyson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.family_dyson

/-! #### `ODELowerBoundExtensions.Dyson.Family.Retry` -/

/-- info: 'ODELowerBoundExtensions.Dyson.retry_exists_isometric_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.retry_exists_isometric_readout

/-- info: 'ODELowerBoundExtensions.Dyson.retrySolver_dyson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.retrySolver_dyson

/-- info: 'ODELowerBoundExtensions.Dyson.retry_time_pos_of_mul_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.retry_time_pos_of_mul_eq

/-- info: 'ODELowerBoundExtensions.Dyson.retry_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.retry_fixed

/-- info: 'ODELowerBoundExtensions.Dyson.no_uniform_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.no_uniform_lower_bound

/-- info: 'ODELowerBoundExtensions.Dyson.no_retry_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ODELowerBoundExtensions.Dyson.no_retry_witnesses

end
