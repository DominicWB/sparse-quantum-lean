import LinearSystemLowerBound.Theorem
import LinearSystemLowerBound.Readout
import LinearSystemLowerBound.Bridge
import LinearSystemLowerBound.XorLemma
import LinearSystemLowerBound.Matching

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 5 elementary lemmas, whose
reports list a subset of these three axioms.
The audits cover every theorem of the linear-system lower-bound library, beginning
with the main theorem. The library uses no result from another paper; `Bridge`
uses theorems of the `SparseLowerBounds` library of this package.
-/

/-! ### Theorem qlsl:thm:main and the hard family -/

/-- info: 'LinearSystemLowerBound.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.lower_bound

/-- info: 'LinearSystemLowerBound.lower_bound_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.lower_bound_sharp

/-- info: 'LinearSystemLowerBound.lower_bound_sharp_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.lower_bound_sharp_clean

/-- info: 'LinearSystemLowerBound.lower_bound_of_bias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.lower_bound_of_bias

/-- info: 'LinearSystemLowerBound.clock_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.clock_count

/-- info: 'LinearSystemLowerBound.family_promise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.family_promise

/-- info: 'LinearSystemLowerBound.family_real_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.family_real_symm

/-- info: 'LinearSystemLowerBound.family_indefinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.family_indefinite

/-- info: 'LinearSystemLowerBound.family_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.family_sparse

/-- info: 'LinearSystemLowerBound.family_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.family_dimension

/-- info: 'LinearSystemLowerBound.rhsVec_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.rhsVec_norm

/-- info: 'LinearSystemLowerBound.target_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.target_eq

/-- info: 'LinearSystemLowerBound.exists_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.exists_access

/-- info: 'LinearSystemLowerBound.target_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.target_correlation

/-! ### Theorem qlsl:thm:main for a readout of norm at most one -/

/-- info: 'LinearSystemLowerBound.lower_bound_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.lower_bound_readout

/-- info: 'LinearSystemLowerBound.lower_bound_sharp_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.lower_bound_sharp_readout

/-- info: 'LinearSystemLowerBound.corr_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.corr_readout

/-- info: 'LinearSystemLowerBound.norm_readout_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_readout_le

/-- info: 'LinearSystemLowerBound.readout_contraction_of_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.readout_contraction_of_isometry

/-- info: 'LinearSystemLowerBound.readout_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.readout_unitary

/-- info: 'LinearSystemLowerBound.tree_bias_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.tree_bias_readout

/-- info: 'LinearSystemLowerBound.lower_bound_sharp_via_readout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.lower_bound_sharp_via_readout

/-! ### Actual condition number and dimension, through SparseLowerBounds -/

/-- info: 'LinearSystemLowerBound.family_cond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.family_cond

/-- info: 'LinearSystemLowerBound.family_dimension_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.family_dimension_sharp

/-- info: 'LinearSystemLowerBound.family_dimension_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.family_dimension_le

/-- info: 'LinearSystemLowerBound.gadgetPos_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.gadgetPos_eq

/-- info: 'LinearSystemLowerBound.gadget_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.gadget_eq

/-- info: 'LinearSystemLowerBound.bridge_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.bridge_fst

/-- info: 'LinearSystemLowerBound.bridge_snd_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.bridge_snd_fst

/-- info: 'LinearSystemLowerBound.bridge_snd_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.bridge_snd_snd

/-- info: 'LinearSystemLowerBound.bridge_snd_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.bridge_snd_inj

/-- info: 'LinearSystemLowerBound.hardMatrix_eq_submatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.hardMatrix_eq_submatrix

/-- info: 'LinearSystemLowerBound.rpar_eq_clockRatio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.rpar_eq_clockRatio

/-- info: 'LinearSystemLowerBound.family_eq_submatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.family_eq_submatrix

/-- info: 'LinearSystemLowerBound.matrixOperator_submatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.matrixOperator_submatrix

/-- info: 'LinearSystemLowerBound.norm_conjStarAlgEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_conjStarAlgEquiv

/-- info: 'LinearSystemLowerBound.ringInverse_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.ringInverse_map

/-- info: 'LinearSystemLowerBound.norm_matrixOperator_submatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_matrixOperator_submatrix

/-- info: 'LinearSystemLowerBound.norm_inverse_matrixOperator_submatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_inverse_matrixOperator_submatrix

/-- info: 'LinearSystemLowerBound.log_64_ge_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.log_64_ge_four

/-- info: 'LinearSystemLowerBound.Rpar_le_two_npar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Rpar_le_two_npar

/-! ### Lemma qlsl:lem:xor -/

/-- info: 'LinearSystemLowerBound.Boolean.xor_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Boolean.xor_lemma

/-- info: 'LinearSystemLowerBound.Boolean.xor_lemma_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Boolean.xor_lemma_count

/-- info: 'LinearSystemLowerBound.Boolean.boolOracle_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Boolean.boolOracle_apply

/-- info: 'LinearSystemLowerBound.Boolean.bitDetermined_bit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Boolean.bitDetermined_bit

/-! ### The matching upper bound in the same model -/

/-- info: 'LinearSystemLowerBound.upper_meets_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.upper_meets_lower

/-- info: 'LinearSystemLowerBound.physOracle_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.physOracle_admissible

/-- info: 'LinearSystemLowerBound.Native.nativeCall_callOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.nativeCall_callOp

/-- info: 'LinearSystemLowerBound.Native.NativeCall.conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.NativeCall.conj

/-- info: 'LinearSystemLowerBound.Native.NativeCall.diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.NativeCall.diagonal

/-- info: 'LinearSystemLowerBound.Native.NativeCall.masked_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.NativeCall.masked_true

/-- info: 'LinearSystemLowerBound.Native.NativeCall.spectator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.NativeCall.spectator

/-- info: 'LinearSystemLowerBound.nativeCall_physOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.nativeCall_physOracle

/-! ### Parameters and the final count -/

/-- info: 'LinearSystemLowerBound.Params.floor_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.floor_ge

/-- info: 'LinearSystemLowerBound.Params.Rpar_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.Rpar_le

/-- info: 'LinearSystemLowerBound.Params.lt_Rpar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.lt_Rpar

/-- info: 'LinearSystemLowerBound.Params.sixteen_le_Rpar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.sixteen_le_Rpar

/-- info: 'LinearSystemLowerBound.Params.rpar_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.rpar_nonneg

/-- info: 'LinearSystemLowerBound.Params.rpar_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.rpar_lt_one

/-- info: 'LinearSystemLowerBound.Params.two_div_one_sub_rpar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.two_div_one_sub_rpar

/-- info: 'LinearSystemLowerBound.Params.mpar_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.mpar_le

/-- info: 'LinearSystemLowerBound.Params.lt_two_mpar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.lt_two_mpar

/-- info: 'LinearSystemLowerBound.Params.two_le_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.two_le_log

/-- info: 'LinearSystemLowerBound.Params.four_le_mpar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.four_le_mpar

/-- info: 'LinearSystemLowerBound.Params.mpar_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.mpar_even

/-- info: 'LinearSystemLowerBound.Params.sqrt_mpar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.sqrt_mpar

/-- info: 'LinearSystemLowerBound.Params.log_64_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.log_64_gt

/-- info: 'LinearSystemLowerBound.Params.L_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.L_ge

/-- info: 'LinearSystemLowerBound.Params.log16_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.log16_le

/-- info: 'LinearSystemLowerBound.Params.npar_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.npar_ge

/-- info: 'LinearSystemLowerBound.Params.npar_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.npar_le

/-- info: 'LinearSystemLowerBound.Params.npar_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.npar_pos

/-- info: 'LinearSystemLowerBound.Params.npar_ge_twoL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.npar_ge_twoL

/-- info: 'LinearSystemLowerBound.Params.npar_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.npar_gt

/-- info: 'LinearSystemLowerBound.Params.rpar_pow_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.rpar_pow_ge

/-- info: 'LinearSystemLowerBound.Params.answerProb_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.answerProb_ge

/-- info: 'LinearSystemLowerBound.Params.bias_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.bias_ge

/-- info: 'LinearSystemLowerBound.Params.q_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Params.q_bound

/-! ### Families over hidden inputs, Kronecker weights and splitting -/

/-- info: 'LinearSystemLowerBound.norm_sq_fam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_sq_fam

/-- info: 'LinearSystemLowerBound.inner_self_cpx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.inner_self_cpx

/-- info: 'LinearSystemLowerBound.inner_fam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.inner_fam

/-- info: 'LinearSystemLowerBound.act_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.act_apply

/-- info: 'LinearSystemLowerBound.act_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.act_add

/-- info: 'LinearSystemLowerBound.act_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.act_sub

/-- info: 'LinearSystemLowerBound.act_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.act_smul

/-- info: 'LinearSystemLowerBound.act_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.act_mul

/-- info: 'LinearSystemLowerBound.act_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.act_one

/-- info: 'LinearSystemLowerBound.act_add_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.act_add_matrix

/-- info: 'LinearSystemLowerBound.act_sub_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.act_sub_matrix

/-- info: 'LinearSystemLowerBound.act_smul_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.act_smul_matrix

/-- info: 'LinearSystemLowerBound.inner_act' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.inner_act

/-- info: 'LinearSystemLowerBound.norm_sq_act_eq_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_sq_act_eq_inner

/-- info: 'LinearSystemLowerBound.norm_act_of_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_act_of_unitary

/-- info: 'LinearSystemLowerBound.joint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.joint_apply

/-- info: 'LinearSystemLowerBound.joint_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.joint_comp

/-- info: 'LinearSystemLowerBound.act_joint_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.act_joint_const

/-- info: 'LinearSystemLowerBound.norm_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_joint

/-- info: 'LinearSystemLowerBound.scale_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.scale_apply

/-- info: 'LinearSystemLowerBound.joint_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.joint_scale

/-- info: 'LinearSystemLowerBound.norm_inner_fam_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_inner_fam_le

/-- info: 'LinearSystemLowerBound.kron_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.kron_apply

/-- info: 'LinearSystemLowerBound.kron_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.kron_mul

/-- info: 'LinearSystemLowerBound.kron_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.kron_one

/-- info: 'LinearSystemLowerBound.kron_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.kron_conjTranspose

/-- info: 'LinearSystemLowerBound.kron_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.kron_diagonal

/-- info: 'LinearSystemLowerBound.splitEquiv_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.splitEquiv_self

/-- info: 'LinearSystemLowerBound.splitEquiv_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.splitEquiv_rest

/-- info: 'LinearSystemLowerBound.rest_splitEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.rest_splitEquiv

/-- info: 'LinearSystemLowerBound.splitEquiv_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.splitEquiv_symm

/-- info: 'LinearSystemLowerBound.kron_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.kron_split

/-- info: 'LinearSystemLowerBound.kron_eq_splitMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.kron_eq_splitMat

/-- info: 'LinearSystemLowerBound.slice_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.slice_apply

/-- info: 'LinearSystemLowerBound.fiber_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.fiber_apply

/-- info: 'LinearSystemLowerBound.sum_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.sum_split

/-- info: 'LinearSystemLowerBound.norm_sq_eq_sum_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_sq_eq_sum_slice

/-- info: 'LinearSystemLowerBound.norm_sq_eq_sum_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_sq_eq_sum_fiber

/-- info: 'LinearSystemLowerBound.slice_act_splitMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.slice_act_splitMat

/-- info: 'LinearSystemLowerBound.norm_sq_act_splitMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_sq_act_splitMat

/-- info: 'LinearSystemLowerBound.sum_norm_sq_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.sum_norm_sq_inner

/-- info: 'LinearSystemLowerBound.card_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.card_rest

/-- info: 'LinearSystemLowerBound.norm_sq_act_kron_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_sq_act_kron_le

/-! ### One-coordinate estimates -/

/-- info: 'LinearSystemLowerBound.norm_sum_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_sum_sq_le

/-- info: 'LinearSystemLowerBound.norm_sum_indicator_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_sum_indicator_sq_le

/-- info: 'LinearSystemLowerBound.avg_mul_avg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.avg_mul_avg

/-- info: 'LinearSystemLowerBound.weight_mul_weightInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.weight_mul_weightInv

/-- info: 'LinearSystemLowerBound.weightInv_mul_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.weightInv_mul_weight

/-- info: 'LinearSystemLowerBound.avg_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.avg_conjTranspose

/-- info: 'LinearSystemLowerBound.weight_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.weight_conjTranspose

/-- info: 'LinearSystemLowerBound.weightInv_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.weightInv_conjTranspose

/-- info: 'LinearSystemLowerBound.sgn_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.sgn_sq

/-- info: 'LinearSystemLowerBound.sgn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.sgn_eq

/-- info: 'LinearSystemLowerBound.sum_neg_one_pow_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.sum_neg_one_pow_even

/-- info: 'LinearSystemLowerBound.sum_sgn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.sum_sgn

/-- info: 'LinearSystemLowerBound.act_avg_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.act_avg_apply

/-- info: 'LinearSystemLowerBound.act_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.act_weight

/-- info: 'LinearSystemLowerBound.act_weightInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.act_weightInv

/-- info: 'LinearSystemLowerBound.norm_sq_act_avg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_sq_act_avg

/-- info: 'LinearSystemLowerBound.inner_act_avg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.inner_act_avg

/-- info: 'LinearSystemLowerBound.norm_sq_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_sq_sum_le

/-- info: 'LinearSystemLowerBound.norm_sq_act_weightInv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_sq_act_weightInv_le

/-- info: 'LinearSystemLowerBound.bitOp_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.bitOp_apply

/-- info: 'LinearSystemLowerBound.joint_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.joint_sub

/-- info: 'LinearSystemLowerBound.joint_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.joint_smul

/-- info: 'LinearSystemLowerBound.commutator_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.commutator_apply

/-- info: 'LinearSystemLowerBound.norm_sq_commutator_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_sq_commutator_le

/-- info: 'LinearSystemLowerBound.weight_growth_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.weight_growth_bit

/-- info: 'LinearSystemLowerBound.act_parityMat_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.act_parityMat_apply

/-- info: 'LinearSystemLowerBound.act_parityKernel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.act_parityKernel_apply

/-- info: 'LinearSystemLowerBound.bessel_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.bessel_parity

/-- info: 'LinearSystemLowerBound.norm_sq_act_parityKernel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_sq_act_parityKernel_le

/-! ### Weight growth of oracle families and circuits -/

/-- info: 'LinearSystemLowerBound.growth_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.growth_const

/-- info: 'LinearSystemLowerBound.growth_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.growth_mono

/-- info: 'LinearSystemLowerBound.growth_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.growth_mul

/-- info: 'LinearSystemLowerBound.growth_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.growth_bit

/-- info: 'LinearSystemLowerBound.piLp_sum_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.piLp_sum_apply

/-- info: 'LinearSystemLowerBound.blk_act' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.blk_act

/-- info: 'LinearSystemLowerBound.norm_sq_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_sq_blk

/-- info: 'LinearSystemLowerBound.growth_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.growth_diagonal

/-- info: 'LinearSystemLowerBound.growth_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.growth_conj

/-- info: 'LinearSystemLowerBound.isUnitary_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.isUnitary_norm

/-- info: 'LinearSystemLowerBound.growth_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.growth_program

/-! ### Kernels, the potential and the parity bound -/

/-- info: 'LinearSystemLowerBound.norm_sq_act_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_sq_act_eq

/-- info: 'LinearSystemLowerBound.pot_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.pot_add

/-- info: 'LinearSystemLowerBound.pot_hadamard_gram_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.pot_hadamard_gram_eq

/-- info: 'LinearSystemLowerBound.exists_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.exists_factor

/-- info: 'LinearSystemLowerBound.pot_hadamard_gram_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.pot_hadamard_gram_nonneg

/-- info: 'LinearSystemLowerBound.onesKernel_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.onesKernel_posSemidef

/-- info: 'LinearSystemLowerBound.hadamard_gram_posSemidef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.hadamard_gram_posSemidef

/-- info: 'LinearSystemLowerBound.pot_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.pot_nonneg

/-- info: 'LinearSystemLowerBound.hadamard_gram_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.hadamard_gram_const

/-- info: 'LinearSystemLowerBound.pot_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.pot_growth

/-- info: 'LinearSystemLowerBound.gram_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.gram_split

/-- info: 'LinearSystemLowerBound.act_kron_parity_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.act_kron_parity_apply

/-- info: 'LinearSystemLowerBound.kron_weightInv_mul_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.kron_weightInv_mul_weight

/-- info: 'LinearSystemLowerBound.parity_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.parity_bound

/-- info: 'LinearSystemLowerBound.parity_kernel_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.parity_kernel_bound

/-! ### Adaptive protocols and the XOR bound -/

/-- info: 'LinearSystemLowerBound.corr_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.corr_add

/-- info: 'LinearSystemLowerBound.corr_smul_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.corr_smul_real

/-- info: 'LinearSystemLowerBound.corr_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.corr_zero

/-- info: 'LinearSystemLowerBound.corr_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.corr_sum

/-- info: 'LinearSystemLowerBound.corr_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.corr_pure

/-- info: 'LinearSystemLowerBound.parityFun_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.parityFun_add

/-- info: 'LinearSystemLowerBound.parityFun_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.parityFun_mul

/-- info: 'LinearSystemLowerBound.parityFun_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.parityFun_sum

/-- info: 'LinearSystemLowerBound.parityFun_hadamard_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.parityFun_hadamard_gram

/-- info: 'LinearSystemLowerBound.pot_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.pot_run

/-- info: 'LinearSystemLowerBound.pot_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.pot_split

/-- info: 'LinearSystemLowerBound.failure_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.failure_weight

/-- info: 'LinearSystemLowerBound.protocol_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.protocol_bound

/-- info: 'LinearSystemLowerBound.tree_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.tree_bound

/-- info: 'LinearSystemLowerBound.kron_row_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.kron_row_sum

/-- info: 'LinearSystemLowerBound.weight_row_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.weight_row_sum

/-- info: 'LinearSystemLowerBound.pot_onesKernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.pot_onesKernel

/-- info: 'LinearSystemLowerBound.tree_xor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.tree_xor

/-! ### The partial trace over a garbage register -/

/-- info: 'LinearSystemLowerBound.entry_eq_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.entry_eq_inner

/-- info: 'LinearSystemLowerBound.apply_eq_sum_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.apply_eq_sum_entry

/-- info: 'LinearSystemLowerBound.entry_matrixOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.entry_matrixOperator

/-- info: 'LinearSystemLowerBound.entry_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.entry_comp

/-- info: 'LinearSystemLowerBound.trace_eq_sum_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.trace_eq_sum_entry

/-- info: 'LinearSystemLowerBound.ext_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.ext_entry

/-- info: 'LinearSystemLowerBound.entry_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.entry_pure

/-- info: 'LinearSystemLowerBound.entry_ptrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.entry_ptrace

/-- info: 'LinearSystemLowerBound.trace_comp_ptrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.trace_comp_ptrace

/-- info: 'LinearSystemLowerBound.ptrace_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.ptrace_unique

/-- info: 'LinearSystemLowerBound.corr_ptrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.corr_ptrace

/-- info: 'LinearSystemLowerBound.ampl_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.ampl_apply

/-- info: 'LinearSystemLowerBound.norm_ampl_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_ampl_le

/-- info: 'LinearSystemLowerBound.ptrace_pure_tmul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.ptrace_pure_tmul

/-- info: 'LinearSystemLowerBound.corr_conjStarAlgEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.corr_conjStarAlgEquiv

/-- info: 'LinearSystemLowerBound.norm_conj_ampl_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.norm_conj_ampl_le

/-- info: 'LinearSystemLowerBound.unitGarbage_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.unitGarbage_apply

/-- info: 'LinearSystemLowerBound.unitGarbage_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.unitGarbage_symm_apply

/-- info: 'LinearSystemLowerBound.ptrace_unitGarbage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.ptrace_unitGarbage

/-! ### Trace distance and the bias -/

/-- info: 'LinearSystemLowerBound.corr_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.corr_sub

/-- info: 'LinearSystemLowerBound.abs_corr_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.abs_corr_sub_le

/-- info: 'LinearSystemLowerBound.tree_bias_of_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.tree_bias_of_close

/-- info: 'LinearSystemLowerBound.tree_bias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.tree_bias

/-- info: 'LinearSystemLowerBound.tree_bias_reduced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.tree_bias_reduced

/-- info: 'LinearSystemLowerBound.parSign_pm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.parSign_pm

/-- info: 'LinearSystemLowerBound.xor_lower_bound_of_bias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.xor_lower_bound_of_bias

/-- info: 'LinearSystemLowerBound.xor_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.xor_lower_bound

/-! ### The gadget -/

/-- info: 'LinearSystemLowerBound.Hard.neg_one_pow_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.neg_one_pow_mod

/-- info: 'LinearSystemLowerBound.Hard.sgn_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.sgn_add

/-- info: 'LinearSystemLowerBound.Hard.sgn_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.sgn_one

/-- info: 'LinearSystemLowerBound.Hard.sgn_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.sgn_sub

/-- info: 'LinearSystemLowerBound.Hard.sum_sgn_indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.sum_sgn_indicator

/-- info: 'LinearSystemLowerBound.Hard.shift_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.shift_iff

/-- info: 'LinearSystemLowerBound.Hard.shift_iff'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.shift_iff'

/-- info: 'LinearSystemLowerBound.Hard.gadget_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.gadget_col

/-- info: 'LinearSystemLowerBound.Hard.gadget_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.gadget_row

/-- info: 'LinearSystemLowerBound.Hard.gadget_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.gadget_conj

/-- info: 'LinearSystemLowerBound.Hard.sum_two_deltas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.sum_two_deltas

/-- info: 'LinearSystemLowerBound.Hard.gadget_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.gadget_unitary

/-- info: 'LinearSystemLowerBound.Hard.gadget_unitary'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.gadget_unitary'

/-- info: 'LinearSystemLowerBound.Hard.norm_sq_logical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.norm_sq_logical

/-- info: 'LinearSystemLowerBound.Hard.sum_logical_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.sum_logical_sq

/-- info: 'LinearSystemLowerBound.Hard.sum_sgn_logical_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.sum_sgn_logical_sq

/-- info: 'LinearSystemLowerBound.Hard.sum_logical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.sum_logical

/-- info: 'LinearSystemLowerBound.Hard.gadget_logical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.gadget_logical

/-! ### Clock, dilation and the history solution -/

/-- info: 'LinearSystemLowerBound.Hard.step_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.step_unitary

/-- info: 'LinearSystemLowerBound.Hard.step_unitary'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.step_unitary'

/-- info: 'LinearSystemLowerBound.Hard.prefixSign_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.prefixSign_zero

/-- info: 'LinearSystemLowerBound.Hard.prefixSign_pm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.prefixSign_pm

/-- info: 'LinearSystemLowerBound.Hard.prefixSign_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.prefixSign_succ

/-- info: 'LinearSystemLowerBound.Hard.prefixSign_succ_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.prefixSign_succ_of_le

/-- info: 'LinearSystemLowerBound.Hard.prefixSign_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.prefixSign_of_le

/-- info: 'LinearSystemLowerBound.Hard.step_logical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.step_logical

/-- info: 'LinearSystemLowerBound.Hard.sum_clock_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.sum_clock_succ

/-- info: 'LinearSystemLowerBound.Hard.sum_clock_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.sum_clock_zero

/-- info: 'LinearSystemLowerBound.Hard.sum_clock_castSucc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.sum_clock_castSucc

/-- info: 'LinearSystemLowerBound.Hard.sum_clock_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.sum_clock_last

/-- info: 'LinearSystemLowerBound.Hard.act_swapM_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.act_swapM_apply

/-- info: 'LinearSystemLowerBound.Hard.act_dil_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.act_dil_false

/-- info: 'LinearSystemLowerBound.Hard.act_dil_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.act_dil_true

/-- info: 'LinearSystemLowerBound.Hard.act_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.act_hard

/-- info: 'LinearSystemLowerBound.Hard.hard_mul_sol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.hard_mul_sol

/-! ### Norms, invertibility, symmetry, one-bit entries and support -/

/-- info: 'LinearSystemLowerBound.Hard.sum_norm_sq_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.sum_norm_sq_mulVec

/-- info: 'LinearSystemLowerBound.Hard.sum_norm_sq_vecMul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.sum_norm_sq_vecMul

/-- info: 'LinearSystemLowerBound.Hard.norm_act_dil_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.norm_act_dil_le

/-- info: 'LinearSystemLowerBound.Hard.norm_act_swapM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.norm_act_swapM

/-- info: 'LinearSystemLowerBound.Hard.hard_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.hard_norm_le

/-- info: 'LinearSystemLowerBound.Hard.hard_norm_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.hard_norm_ge

/-- info: 'LinearSystemLowerBound.Hard.matrixOperator_eq_act' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.matrixOperator_eq_act

/-- info: 'LinearSystemLowerBound.Hard.hard_opNorm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.hard_opNorm_le

/-- info: 'LinearSystemLowerBound.Hard.hard_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.hard_lower

/-- info: 'LinearSystemLowerBound.Hard.hard_isUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.hard_isUnit

/-- info: 'LinearSystemLowerBound.Hard.hard_inverse_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.hard_inverse_norm_le

/-- info: 'LinearSystemLowerBound.Hard.swapM_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.swapM_symm

/-- info: 'LinearSystemLowerBound.Hard.dil_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.dil_symm

/-- info: 'LinearSystemLowerBound.Hard.hard_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.hard_symm

/-- info: 'LinearSystemLowerBound.Hard.gadget_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.gadget_im

/-- info: 'LinearSystemLowerBound.Hard.step_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.step_im

/-- info: 'LinearSystemLowerBound.Hard.clock_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.clock_im

/-- info: 'LinearSystemLowerBound.Hard.hard_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.hard_im

/-- info: 'LinearSystemLowerBound.Hard.BitDetermined.comp' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.BitDetermined.comp

/-- info: 'LinearSystemLowerBound.Hard.bitDetermined_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.bitDetermined_clock

/-- info: 'LinearSystemLowerBound.Hard.bitDetermined_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.bitDetermined_hard

/-- info: 'LinearSystemLowerBound.Hard.hard_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.hard_support

/-- info: 'LinearSystemLowerBound.Hard.card_support_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.card_support_le

/-! ### Decoder and answer probability -/

/-- info: 'LinearSystemLowerBound.Hard.decoderEntry_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.decoderEntry_abs_le

/-- info: 'LinearSystemLowerBound.Hard.decoder_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.decoder_apply

/-- info: 'LinearSystemLowerBound.Hard.decoder_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.decoder_norm_le

/-- info: 'LinearSystemLowerBound.Hard.norm_sq_sol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.norm_sq_sol

/-- info: 'LinearSystemLowerBound.Hard.re_inner_decoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.re_inner_decoder

/-- info: 'LinearSystemLowerBound.Hard.inner_sol_decoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.inner_sol_decoder

/-- info: 'LinearSystemLowerBound.Hard.sum_clock_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.sum_clock_split

/-- info: 'LinearSystemLowerBound.Hard.answer_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.answer_correlation

/-! ### Weight growth of native queries and admissible labels -/

/-- info: 'LinearSystemLowerBound.Native.transl_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.transl_apply

/-- info: 'LinearSystemLowerBound.Native.norm_transl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.norm_transl

/-- info: 'LinearSystemLowerBound.Native.growth_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.growth_congr

/-- info: 'LinearSystemLowerBound.Native.growth_transl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.growth_transl

/-- info: 'LinearSystemLowerBound.Native.norm_sq_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.norm_sq_slot

/-- info: 'LinearSystemLowerBound.Native.slot_act' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.slot_act

/-- info: 'LinearSystemLowerBound.Native.slot_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.slot_lookup

/-- info: 'LinearSystemLowerBound.Native.slot_lookup_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.slot_lookup_star

/-- info: 'LinearSystemLowerBound.Native.growth_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.growth_slots

/-- info: 'LinearSystemLowerBound.Native.growth_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.growth_lookup

/-- info: 'LinearSystemLowerBound.Native.growth_lookup_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.growth_lookup_star

/-- info: 'LinearSystemLowerBound.Native.diagonal_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.diagonal_unitary

/-- info: 'LinearSystemLowerBound.Native.callOp_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.callOp_unitary

/-- info: 'LinearSystemLowerBound.Native.callOp_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.callOp_star

/-- info: 'LinearSystemLowerBound.Native.growth_oracles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.growth_oracles

/-- info: 'LinearSystemLowerBound.Native.growth_callOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.growth_callOp

/-- info: 'LinearSystemLowerBound.Native.growth_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Native.growth_admissible

/-! ### Native data for the hard family -/

/-- info: 'LinearSystemLowerBound.Hard.exists_perm_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.exists_perm_cover

/-- info: 'LinearSystemLowerBound.Hard.rowPerm_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.rowPerm_cover

/-- info: 'LinearSystemLowerBound.Hard.loc_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.loc_injective

/-- info: 'LinearSystemLowerBound.Hard.gadget_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.gadget_cases

/-- info: 'LinearSystemLowerBound.Hard.step_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.step_cases

/-- info: 'LinearSystemLowerBound.Hard.dil_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.dil_cases

/-- info: 'LinearSystemLowerBound.Hard.dil_of_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.dil_of_swap

/-- info: 'LinearSystemLowerBound.Hard.swap_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.swap_cases

/-- info: 'LinearSystemLowerBound.Hard.hard_entry_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.hard_entry_cases

/-- info: 'LinearSystemLowerBound.Hard.dec_enc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.dec_enc

/-- info: 'LinearSystemLowerBound.Hard.norm_dec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.norm_dec_le

/-- info: 'LinearSystemLowerBound.Hard.hardData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.hardData_matrix

/-- info: 'LinearSystemLowerBound.Hard.hardData_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.hardData_table

/-- info: 'LinearSystemLowerBound.Hard.hardData_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LinearSystemLowerBound.Hard.hardData_access
