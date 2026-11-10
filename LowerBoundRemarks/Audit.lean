import LowerBoundRemarks.ParityAmplitude
import LowerBoundRemarks.LinearSystemPadding
import LowerBoundRemarks.HamiltonianPadding

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. Every report lists `propext`, `Classical.choice` and
`Quot.sound`, except for 6 lemmas, whose reports list a subset of these three axioms (or none).
The exceptions are `rfl` facts about the padded word table `padTable`, which depend on no
axiom. The audits cover every theorem of the library of remarks after the lower-bound theorems:
the structural remark on parity-amplitude reductions, beginning with its main theorems, then the
padding of the hard linear systems and the padding of the hard Hamiltonian-simulation families.
-/

/-! ### Parity-amplitude reductions (remark in Section `part:hsl`) -/

/-- info: 'LowerBoundRemarks.ParityAmplitude.moment_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.moment_eq_zero

/-- info: 'LowerBoundRemarks.ParityAmplitude.exp_correlation_le_tsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.exp_correlation_le_tsum

/-- info: 'LowerBoundRemarks.ParityAmplitude.exp_correlation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.exp_correlation_le

/-- info: 'LowerBoundRemarks.ParityAmplitude.matrix_exp_correlation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.matrix_exp_correlation_le

/-- info: 'LowerBoundRemarks.ParityAmplitude.hsl_moment_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.hsl_moment_eq_zero

/-- info: 'LowerBoundRemarks.ParityAmplitude.hsl_exp_correlation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.hsl_exp_correlation_le

/-- info: 'LowerBoundRemarks.ParityAmplitude.isBlockAffine_iff_membership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.isBlockAffine_iff_membership

/-- info: 'LowerBoundRemarks.ParityAmplitude.isBlockAffine_membership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.isBlockAffine_membership

/-- info: 'LowerBoundRemarks.ParityAmplitude.isBlockAffine_iff_entries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.isBlockAffine_iff_entries

/-- info: 'LowerBoundRemarks.ParityAmplitude.isBlockAffine_of_entries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.isBlockAffine_of_entries

/-- info: 'LowerBoundRemarks.ParityAmplitude.sum_smul_eq_zero_of_update_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.sum_smul_eq_zero_of_update_eq

/-- info: 'LowerBoundRemarks.ParityAmplitude.sum_parity_smul_eq_zero_of_dependsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.sum_parity_smul_eq_zero_of_dependsOn

/-- info: 'LowerBoundRemarks.ParityAmplitude.sum_parity_smul_eq_zero_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.sum_parity_smul_eq_zero_of_mem

/-- info: 'LowerBoundRemarks.ParityAmplitude.const_mem_blockSpan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.const_mem_blockSpan

/-- info: 'LowerBoundRemarks.ParityAmplitude.block_mem_blockSpan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.block_mem_blockSpan

/-- info: 'LowerBoundRemarks.ParityAmplitude.IsBlockAffine.mem_blockSpan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.IsBlockAffine.mem_blockSpan

/-- info: 'LowerBoundRemarks.ParityAmplitude.mul_mem_blockSpan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.mul_mem_blockSpan

/-- info: 'LowerBoundRemarks.ParityAmplitude.pow_mem_blockSpan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.pow_mem_blockSpan

/-- info: 'LowerBoundRemarks.ParityAmplitude.expect_moment_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.expect_moment_eq_zero

/-- info: 'LowerBoundRemarks.ParityAmplitude.tsum_tail_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.tsum_tail_le

/-- info: 'LowerBoundRemarks.ParityAmplitude.norm_average_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.norm_average_le

/-- info: 'LowerBoundRemarks.ParityAmplitude.moment_eq_zero_membership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.moment_eq_zero_membership

/-- info: 'LowerBoundRemarks.ParityAmplitude.exp_correlation_le_membership' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.exp_correlation_le_membership

/-- info: 'LowerBoundRemarks.ParityAmplitude.sum_hslSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.sum_hslSign

/-- info: 'LowerBoundRemarks.ParityAmplitude.abs_hslSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.abs_hslSign

/-- info: 'LowerBoundRemarks.ParityAmplitude.parity_hslSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.ParityAmplitude.parity_hslSign

/-! ### Padding the hard linear systems (remark after Theorem `qlsl:thm:main`) -/

/-- info: 'LowerBoundRemarks.LinearSystemPadding.bound_of_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.bound_of_access

/-- info: 'LowerBoundRemarks.LinearSystemPadding.emb_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.emb_inl

/-- info: 'LowerBoundRemarks.LinearSystemPadding.emb_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.emb_inr

/-- info: 'LowerBoundRemarks.LinearSystemPadding.norm_sq_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.norm_sq_split

/-- info: 'LowerBoundRemarks.LinearSystemPadding.inverse_apply_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.inverse_apply_self

/-- info: 'LowerBoundRemarks.LinearSystemPadding.apply_inverse_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.apply_inverse_self

/-- info: 'LowerBoundRemarks.LinearSystemPadding.isUnit_of_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.isUnit_of_lower

/-- info: 'LowerBoundRemarks.LinearSystemPadding.inlPart_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.inlPart_block

/-- info: 'LowerBoundRemarks.LinearSystemPadding.inrPart_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.inrPart_block

/-- info: 'LowerBoundRemarks.LinearSystemPadding.block_emb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.block_emb

/-- info: 'LowerBoundRemarks.LinearSystemPadding.block_promise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.block_promise

/-- info: 'LowerBoundRemarks.LinearSystemPadding.block_inverse_emb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.block_inverse_emb

/-- info: 'LowerBoundRemarks.LinearSystemPadding.unitDirection_emb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.unitDirection_emb

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padRhs_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padRhs_apply

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padRhs_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padRhs_norm

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padFamily_promise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padFamily_promise

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padFamily_real_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padFamily_real_symm

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padFamily_indefinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padFamily_indefinite

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padFamily_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padFamily_sparse

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padFamily_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padFamily_dimension

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padSolution_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padSolution_eq

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padTarget_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padTarget_eq

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padTarget_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padTarget_norm

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padDecoder_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padDecoder_norm_le

/-- info: 'LowerBoundRemarks.LinearSystemPadding.inner_padDecoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.inner_padDecoder

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padTarget_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padTarget_correlation

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padFamily_bitDetermined' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padFamily_bitDetermined

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padAccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padAccess

/-- info: 'LowerBoundRemarks.LinearSystemPadding.pad_lower_bound_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.pad_lower_bound_sharp

/-- info: 'LowerBoundRemarks.LinearSystemPadding.pad_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.pad_lower_bound

/-- info: 'LowerBoundRemarks.LinearSystemPadding.pad_lower_bound_sharp_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.pad_lower_bound_sharp_clean

/-- info: 'LowerBoundRemarks.LinearSystemPadding.coverPerm_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.coverPerm_cover

/-- info: 'LowerBoundRemarks.LinearSystemPadding.coverLoc_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.coverLoc_injective

/-- info: 'LowerBoundRemarks.LinearSystemPadding.enc_ne_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.enc_ne_five

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padDec_padEnc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padDec_padEnc

/-- info: 'LowerBoundRemarks.LinearSystemPadding.norm_padDec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.norm_padDec_le

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padFamily_entry_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padFamily_entry_cases

/-- info: 'LowerBoundRemarks.LinearSystemPadding.exists_pad_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.exists_pad_access

/-- info: 'LowerBoundRemarks.LinearSystemPadding.exists_pad_hardAccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.exists_pad_hardAccess

/-- info: 'LowerBoundRemarks.LinearSystemPadding.padReg_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.padReg_card

/-- info: 'LowerBoundRemarks.LinearSystemPadding.card_ind_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.card_ind_le

/-- info: 'LowerBoundRemarks.LinearSystemPadding.common_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.common_dimension

/-- info: 'LowerBoundRemarks.LinearSystemPadding.lower_bound_common_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.LinearSystemPadding.lower_bound_common_dimension

/-! ### Padding the hard Hamiltonian-simulation families (last clause of Theorem `hsl:thm:main`) -/

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padTable_addr_inl_inl' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padTable_addr_inl_inl

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padTable_addr_inl_inr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padTable_addr_inl_inr

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padTable_addr_inr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padTable_addr_inr

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padTable_value_inl_inl' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padTable_value_inl_inl

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padTable_value_inl_inr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padTable_value_inl_inr

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padTable_value_inr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padTable_value_inr

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padTable_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padTable_bound

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padLoc_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padLoc_row

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padLoc_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padLoc_col

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padTable_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padTable_decode

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padBitData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padBitData_matrix

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padBitData_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padBitData_table

/-- info: 'LowerBoundRemarks.HamiltonianPadding.implementsOn_padBitData_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.implementsOn_padBitData_spec

/-- info: 'LowerBoundRemarks.HamiltonianPadding.evolve_padMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.evolve_padMat

/-- info: 'LowerBoundRemarks.HamiltonianPadding.inner_inlOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.inner_inlOp

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padReadout_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padReadout_none

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padReadout_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padReadout_some

/-- info: 'LowerBoundRemarks.HamiltonianPadding.norm_padReadout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.norm_padReadout

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padReadout_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padReadout_isometry

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padReadout_comp_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padReadout_comp_isometry

/-- info: 'LowerBoundRemarks.HamiltonianPadding.inner_liftObs_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.inner_liftObs_apply

/-- info: 'LowerBoundRemarks.HamiltonianPadding.obsMat_blockObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.obsMat_blockObs

/-- info: 'LowerBoundRemarks.HamiltonianPadding.inner_padReadout_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.inner_padReadout_apply

/-- info: 'LowerBoundRemarks.HamiltonianPadding.inner_padReadout_liftObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.inner_padReadout_liftObs

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padReadout_adjoint_liftObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padReadout_adjoint_liftObs

/-- info: 'LowerBoundRemarks.HamiltonianPadding.outObs_padReadout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.outObs_padReadout

/-- info: 'LowerBoundRemarks.HamiltonianPadding.isSelfAdjoint_blockObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.isSelfAdjoint_blockObs

/-- info: 'LowerBoundRemarks.HamiltonianPadding.norm_blockObs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.norm_blockObs_le

/-- info: 'LowerBoundRemarks.HamiltonianPadding.obsMat_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.obsMat_apply

/-- info: 'LowerBoundRemarks.HamiltonianPadding.norm_obsMat_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.norm_obsMat_apply_le

/-- info: 'LowerBoundRemarks.HamiltonianPadding.blockObs_inlOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.blockObs_inlOp

/-- info: 'LowerBoundRemarks.HamiltonianPadding.accurate_padReadout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.accurate_padReadout

/-- info: 'LowerBoundRemarks.HamiltonianPadding.accurate_pad_evolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.accurate_pad_evolve

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padBitData_hardInstance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padBitData_hardInstance

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padSearchData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padSearchData_matrix

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padScalarData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padScalarData_matrix

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padSearchData_hardInstance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padSearchData_hardInstance

/-- info: 'LowerBoundRemarks.HamiltonianPadding.padScalarData_hardInstance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.padScalarData_hardInstance

/-- info: 'LowerBoundRemarks.HamiltonianPadding.implementsOn_padSearchData_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.implementsOn_padSearchData_spec

/-- info: 'LowerBoundRemarks.HamiltonianPadding.implementsOn_padScalarData_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.implementsOn_padScalarData_spec

/-- info: 'LowerBoundRemarks.HamiltonianPadding.time_pad_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.time_pad_spec

/-- info: 'LowerBoundRemarks.HamiltonianPadding.mixed_pad_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.mixed_pad_spec

/-- info: 'LowerBoundRemarks.HamiltonianPadding.precision_pad_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.precision_pad_spec

/-- info: 'LowerBoundRemarks.HamiltonianPadding.hard_instances_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.hard_instances_pad

/-- info: 'LowerBoundRemarks.HamiltonianPadding.time_main_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.time_main_pad

/-- info: 'LowerBoundRemarks.HamiltonianPadding.mixed_main_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.mixed_main_pad

/-- info: 'LowerBoundRemarks.HamiltonianPadding.precision_main_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.precision_main_pad

/-- info: 'LowerBoundRemarks.HamiltonianPadding.third_sum_le_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.third_sum_le_max

/-- info: 'LowerBoundRemarks.HamiltonianPadding.main_max_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.main_max_pad

/-- info: 'LowerBoundRemarks.HamiltonianPadding.card_padTo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.card_padTo

/-- info: 'LowerBoundRemarks.HamiltonianPadding.card_le_of_dim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.card_le_of_dim

/-- info: 'LowerBoundRemarks.HamiltonianPadding.main_max_common_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.main_max_common_dimension

/-- info: 'LowerBoundRemarks.HamiltonianPadding.main_exists_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.main_exists_pad

/-- info: 'LowerBoundRemarks.HamiltonianPadding.main_exists_common_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LowerBoundRemarks.HamiltonianPadding.main_exists_common_dimension
