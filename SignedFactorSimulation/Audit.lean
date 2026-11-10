import SignedFactorSimulation.Coefficients
import SignedFactorSimulation.Factor
import SignedFactorSimulation.FiniteTransfer
import SignedFactorSimulation.Cascade
import SignedFactorSimulation.Mesh
import SignedFactorSimulation.Amplify
import SignedFactorSimulation.Extension
import SignedFactorSimulation.LCU
import SignedFactorSimulation.Query
import SignedFactorSimulation.Core
import SignedFactorSimulation.Attenuation
import SignedFactorSimulation.Parameters
import SignedFactorSimulation.Theorem

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem of the library
(232 theorems) and every proof field of the structure `SignedFactorSimulation.Known`
(6 fields), beginning with Theorem `opt:thm:signed` and the main stages of its
proof, then in module order. Every report lists `propext`, `Classical.choice` and
`Quot.sound`, except for 2 lemmas, `brLen_ne_zero` and `brLen_le`, whose reports list a
strict subset of these three axioms. -/

/-! ### Final theorems: Theorem `opt:thm:signed` and the main stages of its proof -/

/-- info: 'SignedFactorSimulation.signed_factor_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.signed_factor_simulation

/-- info: 'SignedFactorSimulation.signed_factor_simulation_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.signed_factor_simulation_uniform

/-- info: 'SignedFactorSimulation.positive_time' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.positive_time

/-- info: 'SignedFactorSimulation.core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.core

/-- info: 'SignedFactorSimulation.norm_evolution_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.norm_evolution_sub_one_le

/-- info: 'SignedFactorSimulation.Known.transfer_cascade_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.transfer_cascade_factor

/-- info: 'SignedFactorSimulation.Known.finite_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.finite_mesh

/-- info: 'SignedFactorSimulation.cascade_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.cascade_block

/-- info: 'SignedFactorSimulation.select_implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.select_implements

/-- info: 'SignedFactorSimulation.amplified_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.amplified_error

/-- info: 'SignedFactorSimulation.tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.tail_bound

/-! ### The clock identity and the three-phase factor (`Coefficients`, `Factor`) -/

/-! #### `SignedFactorSimulation.Coefficients` -/

/-- info: 'SignedFactorSimulation.coeff_clm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.coeff_clm

/-- info: 'SignedFactorSimulation.ces_clm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.ces_clm

/-- info: 'SignedFactorSimulation.coeff_smul_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.coeff_smul_X

/-- info: 'SignedFactorSimulation.coeff_smul_X_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.coeff_smul_X_zero

/-- info: 'SignedFactorSimulation.coeff_const_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.coeff_const_vec

/-- info: 'SignedFactorSimulation.analyticAt_inverse_one_sub_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.analyticAt_inverse_one_sub_smul

/-- info: 'SignedFactorSimulation.coeff_inverse_one_sub_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.coeff_inverse_one_sub_smul

/-- info: 'SignedFactorSimulation.sandwich_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.sandwich_apply

/-- info: 'SignedFactorSimulation.analyticAt_resolventPart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.analyticAt_resolventPart

/-- info: 'SignedFactorSimulation.analyticAt_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.analyticAt_transfer

/-- info: 'SignedFactorSimulation.coeff_resolventPart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.coeff_resolventPart

/-- info: 'SignedFactorSimulation.coeff_transfer_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.coeff_transfer_zero

/-- info: 'SignedFactorSimulation.coeff_transfer_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.coeff_transfer_succ

/-- info: 'SignedFactorSimulation.coeff_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.coeff_transfer

/-- info: 'SignedFactorSimulation.sum_range_sum_range_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.sum_range_sum_range_succ

/-- info: 'SignedFactorSimulation.publicReuse_uniform_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.publicReuse_uniform_slot

/-- info: 'SignedFactorSimulation.successfulBlock_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.successfulBlock_eq_sum

/-- info: 'SignedFactorSimulation.successfulBlock_eq_ces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.successfulBlock_eq_ces

/-! #### `SignedFactorSimulation.Factor` -/

/-- info: 'SignedFactorSimulation.Known.E_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.E_isometry

/-- info: 'SignedFactorSimulation.Known.proj_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.proj_adjoint

/-- info: 'SignedFactorSimulation.Known.proj_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.proj_idem

/-- info: 'SignedFactorSimulation.Known.Z_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.Z_adjoint

/-- info: 'SignedFactorSimulation.Known.Z_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.Z_sq

/-- info: 'SignedFactorSimulation.Known.Z_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.Z_comm

/-- info: 'SignedFactorSimulation.Known.Dop_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.Dop_nonneg

/-- info: 'SignedFactorSimulation.Known.complex_two_inv_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.complex_two_inv_nonneg

/-- info: 'SignedFactorSimulation.Known.one_add_Z_isPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.one_add_Z_isPositive

/-- info: 'SignedFactorSimulation.Known.one_sub_Z_isPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.one_sub_Z_isPositive

/-- info: 'SignedFactorSimulation.Known.Dop_add_Cop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.Dop_add_Cop

/-- info: 'SignedFactorSimulation.Known.Dop_sub_Cop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.Dop_sub_Cop

/-- info: 'SignedFactorSimulation.Known.neg_Dop_le_Cop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.neg_Dop_le_Cop

/-- info: 'SignedFactorSimulation.Known.Cop_le_Dop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.Cop_le_Dop

/-- info: 'SignedFactorSimulation.Known.proj_Z_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.proj_Z_proj

/-- info: 'SignedFactorSimulation.Known.Z_proj_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.Z_proj_proj

/-- info: 'SignedFactorSimulation.Known.Z_proj_Z_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.Z_proj_Z_proj

/-- info: 'SignedFactorSimulation.Known.plus_mul_plus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.plus_mul_plus

/-- info: 'SignedFactorSimulation.Known.minus_mul_minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.minus_mul_minus

/-- info: 'SignedFactorSimulation.Known.plus_mul_minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.plus_mul_minus

/-- info: 'SignedFactorSimulation.Known.minus_mul_plus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.minus_mul_plus

/-- info: 'SignedFactorSimulation.Known.compl_mul_plus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.compl_mul_plus

/-- info: 'SignedFactorSimulation.Known.compl_mul_minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.compl_mul_minus

/-- info: 'SignedFactorSimulation.Known.plus_mul_compl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.plus_mul_compl

/-- info: 'SignedFactorSimulation.Known.minus_mul_compl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.minus_mul_compl

/-- info: 'SignedFactorSimulation.Known.compl_mul_compl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.compl_mul_compl

/-- info: 'SignedFactorSimulation.Known.plus_add_minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.plus_add_minus

/-- info: 'SignedFactorSimulation.Known.spec_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.spec_one

/-- info: 'SignedFactorSimulation.Known.spec_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.spec_mul

/-- info: 'SignedFactorSimulation.Known.spec_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.spec_add

/-- info: 'SignedFactorSimulation.Known.spec_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.spec_smul

/-- info: 'SignedFactorSimulation.Known.spec_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.spec_sub

/-- info: 'SignedFactorSimulation.Known.Zproj_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.Zproj_adjoint

/-- info: 'SignedFactorSimulation.Known.plus_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.plus_adjoint

/-- info: 'SignedFactorSimulation.Known.minus_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.minus_adjoint

/-- info: 'SignedFactorSimulation.Known.spec_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.spec_adjoint

/-- info: 'SignedFactorSimulation.Known.ofReal_sub_I_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.ofReal_sub_I_ne_zero

/-- info: 'SignedFactorSimulation.Known.neg_ofReal_sub_I_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.neg_ofReal_sub_I_ne_zero

/-- info: 'SignedFactorSimulation.Known.norm_zetaP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.norm_zetaP

/-- info: 'SignedFactorSimulation.Known.norm_zetaM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.norm_zetaM

/-- info: 'SignedFactorSimulation.Known.conj_mul_self_of_norm_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.conj_mul_self_of_norm_one

/-- info: 'SignedFactorSimulation.Known.phase_adjoint_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.phase_adjoint_mul

/-- info: 'SignedFactorSimulation.Known.phase_mul_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.phase_mul_adjoint

/-- info: 'SignedFactorSimulation.Known.phase_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.phase_isUnitary

/-- info: 'SignedFactorSimulation.Known.phase_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.phase_cayley

/-- info: 'SignedFactorSimulation.Known.one_sub_zeta_mul_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.one_sub_zeta_mul_ne_zero

/-- info: 'SignedFactorSimulation.Known.muP_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.muP_eq

/-- info: 'SignedFactorSimulation.Known.muM_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.muM_eq

/-- info: 'SignedFactorSimulation.Known.xi_eq_failure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.xi_eq_failure

/-- info: 'SignedFactorSimulation.Known.one_sub_smul_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.one_sub_smul_phase

/-- info: 'SignedFactorSimulation.Known.one_add_smul_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.one_add_smul_phase

/-- info: 'SignedFactorSimulation.Known.one_sub_smul_phase_mul_resolvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.one_sub_smul_phase_mul_resolvent

/-- info: 'SignedFactorSimulation.Known.resolvent_mul_one_sub_smul_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.resolvent_mul_one_sub_smul_phase

/-- info: 'SignedFactorSimulation.Known.one_add_smul_phase_mul_resolvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.one_add_smul_phase_mul_resolvent

/-- info: 'SignedFactorSimulation.Known.priv_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.priv_isUnitary

/-- info: 'SignedFactorSimulation.Known.compress_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.compress_add

/-- info: 'SignedFactorSimulation.Known.compress_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.compress_sub

/-- info: 'SignedFactorSimulation.Known.compress_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.compress_smul

/-- info: 'SignedFactorSimulation.Known.compress_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.compress_one

/-- info: 'SignedFactorSimulation.Known.compress_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.compress_proj

/-- info: 'SignedFactorSimulation.Known.compress_Zproj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.compress_Zproj

/-- info: 'SignedFactorSimulation.Known.compress_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.compress_spec

/-- info: 'SignedFactorSimulation.Known.omega_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.omega_eq

/-! ### The finite transfer and the finite mesh (`FiniteTransfer`, `Cascade`, `Mesh`) -/

/-! #### `SignedFactorSimulation.FiniteTransfer` -/

/-- info: 'SignedFactorSimulation.one_comp'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.one_comp'

/-- info: 'SignedFactorSimulation.comp_one'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.comp_one'

/-- info: 'SignedFactorSimulation.isUnit_one_add_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.isUnit_one_add_smul

/-- info: 'SignedFactorSimulation.chronologicalOperator_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.chronologicalOperator_smul

/-- info: 'SignedFactorSimulation.publicExit_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.publicExit_smul

/-- info: 'SignedFactorSimulation.localPrivateBlock_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.localPrivateBlock_smul

/-- info: 'SignedFactorSimulation.globalPrivateBlock_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.globalPrivateBlock_smul

/-- info: 'SignedFactorSimulation.norm_globalPrivateBlock_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.norm_globalPrivateBlock_le

/-- info: 'SignedFactorSimulation.cayley_scalars' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.cayley_scalars

/-- info: 'SignedFactorSimulation.resolvent_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.resolvent_split

/-- info: 'SignedFactorSimulation.omega_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.omega_split

/-- info: 'SignedFactorSimulation.private_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.private_step

/-- info: 'SignedFactorSimulation.local_catalyst_abstract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.local_catalyst_abstract

/-- info: 'SignedFactorSimulation.isUnit_one_sub_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.isUnit_one_sub_smul

/-- info: 'SignedFactorSimulation.transfer_cascade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.transfer_cascade

/-! #### `SignedFactorSimulation.Cascade` -/

/-- info: 'SignedFactorSimulation.differentiableOn_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.differentiableOn_transfer

/-- info: 'SignedFactorSimulation.norm_cascD_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.norm_cascD_le

/-- info: 'SignedFactorSimulation.differentiableOn_cascTransfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.differentiableOn_cascTransfer

/-- info: 'SignedFactorSimulation.successfulBlock_cascade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.successfulBlock_cascade

/-- info: 'SignedFactorSimulation.Known.one_sub_proj_isPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.one_sub_proj_isPositive

/-- info: 'SignedFactorSimulation.Known.one_sub_Dop_isPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.one_sub_Dop_isPositive

/-- info: 'SignedFactorSimulation.Known.Dop_add_Cop_isPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.Dop_add_Cop_isPositive

/-- info: 'SignedFactorSimulation.Known.Dop_sub_Cop_isPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.Dop_sub_Cop_isPositive

/-- info: 'SignedFactorSimulation.Known.priv_adjoint_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.priv_adjoint_comp

/-- info: 'SignedFactorSimulation.Known.gen_priv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.gen_priv

/-! #### `SignedFactorSimulation.Mesh` -/

/-- info: 'SignedFactorSimulation.norm_xi_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.norm_xi_le

/-- info: 'SignedFactorSimulation.norm_mobius_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.norm_mobius_le

/-- info: 'SignedFactorSimulation.Known.norm_spec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.norm_spec_le

/-- info: 'SignedFactorSimulation.Known.norm_compress_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.norm_compress_le

/-- info: 'SignedFactorSimulation.Known.norm_Omega_factor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.norm_Omega_factor_le

/-- info: 'SignedFactorSimulation.norm_one_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.norm_one_le_one

/-- info: 'SignedFactorSimulation.isUnit_one_add_of_norm_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.isUnit_one_add_of_norm_lt

/-- info: 'SignedFactorSimulation.norm_right_inverse_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.norm_right_inverse_le

/-- info: 'SignedFactorSimulation.cayley_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.cayley_remainder

/-- info: 'SignedFactorSimulation.exp_taylor_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.exp_taylor_two

/-- info: 'SignedFactorSimulation.norm_cayStep_sub_exp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.norm_cayStep_sub_exp_le

/-- info: 'SignedFactorSimulation.norm_cayStep_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.norm_cayStep_le_one

/-- info: 'SignedFactorSimulation.norm_exp_neg_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.norm_exp_neg_le_one

/-- info: 'SignedFactorSimulation.norm_pow_sub_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.norm_pow_sub_pow_le

/-- info: 'SignedFactorSimulation.exp_neg_eq_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.exp_neg_eq_pow

/-- info: 'SignedFactorSimulation.half_le_rho_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.half_le_rho_pow

/-- info: 'SignedFactorSimulation.Known.norm_cascTransfer_sub_Fop_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.norm_cascTransfer_sub_Fop_le

/-! ### Repeated amplification (`Amplify`) -/

/-! #### `SignedFactorSimulation.Amplify` -/

/-- info: 'SignedFactorSimulation.ampS_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.ampS_succ

/-- info: 'SignedFactorSimulation.ampS_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.ampS_top

/-- info: 'SignedFactorSimulation.ampS_arg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.ampS_arg_le

/-- info: 'SignedFactorSimulation.ampS_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.ampS_nonneg

/-- info: 'SignedFactorSimulation.ampS_le_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.ampS_le_half

/-- info: 'SignedFactorSimulation.ampS_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.ampS_zero_le

/-- info: 'SignedFactorSimulation.cubic_defect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.cubic_defect

/-- info: 'SignedFactorSimulation.amp_step_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.amp_step_error

/-- info: 'SignedFactorSimulation.ampIter_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.ampIter_isometry

/-- info: 'SignedFactorSimulation.ampIter_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.ampIter_block

/-- info: 'SignedFactorSimulation.ampIter_block_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.ampIter_block_error

/-- info: 'SignedFactorSimulation.full_output_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.full_output_error

/-! ### The signed LCU and its factor queries (`Extension`, `LCU`, `Query`) -/

/-! #### `SignedFactorSimulation.Extension` -/

/-- info: 'SignedFactorSimulation.isometry_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.isometry_adjoint_apply

/-- info: 'SignedFactorSimulation.compress_extA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.compress_extA

/-- info: 'SignedFactorSimulation.transferCoeff_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.transferCoeff_ext

/-- info: 'SignedFactorSimulation.successfulBlock_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.successfulBlock_ext

/-- info: 'SignedFactorSimulation.norm_map_of_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.norm_map_of_isometry

/-- info: 'SignedFactorSimulation.ext_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.ext_energy

/-! #### `SignedFactorSimulation.LCU` -/

/-- info: 'SignedFactorSimulation.brLen_ne_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.brLen_ne_zero

/-- info: 'SignedFactorSimulation.brLen_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.brLen_le

/-- info: 'SignedFactorSimulation.sum_fin_succ_eq_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.sum_fin_succ_eq_Icc

/-- info: 'SignedFactorSimulation.brInj_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.brInj_isometry

/-- info: 'SignedFactorSimulation.lcuCoeff_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.lcuCoeff_mass

/-- info: 'SignedFactorSimulation.lcuIn_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.lcuIn_isometry

/-- info: 'SignedFactorSimulation.lcuOut_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.lcuOut_isometry

/-- info: 'SignedFactorSimulation.lcu_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.lcu_block

/-- info: 'SignedFactorSimulation.lcuSign_comp_lcuOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.lcuSign_comp_lcuOut

/-- info: 'SignedFactorSimulation.lcuSign_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.lcuSign_adjoint

/-- info: 'SignedFactorSimulation.lcuSign_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.lcuSign_mul_self

/-- info: 'SignedFactorSimulation.lcuSign_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.lcuSign_unitary

/-! #### `SignedFactorSimulation.Query` -/

/-- info: 'SignedFactorSimulation.blockMap_diag_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.blockMap_diag_apply

/-- info: 'SignedFactorSimulation.blockMap_diag_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.blockMap_diag_comp

/-- info: 'SignedFactorSimulation.blockMap_diag_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.blockMap_diag_one

/-- info: 'SignedFactorSimulation.blockMap_diag_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.blockMap_diag_adjoint

/-- info: 'SignedFactorSimulation.diagonal_const_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.diagonal_const_adjoint

/-- info: 'SignedFactorSimulation.diagonal_const_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.diagonal_const_comp

/-- info: 'SignedFactorSimulation.diagonal_const_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.diagonal_const_one

/-- info: 'SignedFactorSimulation.liftBr_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.liftBr_adjoint

/-- info: 'SignedFactorSimulation.liftBr_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.liftBr_comp

/-- info: 'SignedFactorSimulation.liftBr_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.liftBr_one

/-- info: 'SignedFactorSimulation.liftBr_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.liftBr_conj

/-- info: 'SignedFactorSimulation.liftU_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.liftU_conj

/-- info: 'SignedFactorSimulation.liftU_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.liftU_unitary

/-- info: 'SignedFactorSimulation.actLayer_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.actLayer_unitary

/-- info: 'SignedFactorSimulation.diagonal_const_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.diagonal_const_unitary

/-- info: 'SignedFactorSimulation.wB_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.wB_eq

/-- info: 'SignedFactorSimulation.cascD_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.cascD_eq

/-- info: 'SignedFactorSimulation.coup_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.coup_energy

/-- info: 'SignedFactorSimulation.coupLayer_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.coupLayer_unitary

/-- info: 'SignedFactorSimulation.select_eq_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.select_eq_product

/-- info: 'SignedFactorSimulation.actLayer_implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.actLayer_implements

/-- info: 'SignedFactorSimulation.threeSelect_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.threeSelect_unitary

/-- info: 'SignedFactorSimulation.ampCirc_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.ampCirc_unitary

/-- info: 'SignedFactorSimulation.ampIter_eq_ampCirc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.ampIter_eq_ampCirc

/-- info: 'SignedFactorSimulation.ampCirc_implements' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.ampCirc_implements

/-! ### The circuit and the theorem (`Core`, `Attenuation`, `Parameters`, `Theorem`) -/

/-! #### `SignedFactorSimulation.Core` -/

/-- info: 'SignedFactorSimulation.flat_liftU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.flat_liftU

/-- info: 'SignedFactorSimulation.equiv_adjoint_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.equiv_adjoint_comp

/-- info: 'SignedFactorSimulation.embed_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.embed_isometry

/-- info: 'SignedFactorSimulation.embed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.embed_error

/-- info: 'SignedFactorSimulation.Implements.of_oracle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Implements.of_oracle_eq

/-- info: 'SignedFactorSimulation.norm_le_one_of_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.norm_le_one_of_isometry

/-- info: 'SignedFactorSimulation.Known.Cop_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.Cop_star

/-- info: 'SignedFactorSimulation.Known.evolution_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.evolution_unitary

/-- info: 'SignedFactorSimulation.ampS_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.ampS_mul_le

/-- info: 'SignedFactorSimulation.exists_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.exists_mesh

/-! #### `SignedFactorSimulation.Attenuation` -/

/-- info: 'SignedFactorSimulation.dbl_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.dbl_comp

/-- info: 'SignedFactorSimulation.dbl_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.dbl_adjoint

/-- info: 'SignedFactorSimulation.dbl_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.dbl_one

/-- info: 'SignedFactorSimulation.dbl_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.dbl_unitary

/-- info: 'SignedFactorSimulation.flagIn_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.flagIn_isometry

/-- info: 'SignedFactorSimulation.flagIncl_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.flagIncl_adjoint_apply

/-- info: 'SignedFactorSimulation.flagProj_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.flagProj_adjoint

/-- info: 'SignedFactorSimulation.flagProj_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.flagProj_idem

/-- info: 'SignedFactorSimulation.Known.atten_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.atten_factor

/-- info: 'SignedFactorSimulation.flagIncl_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.flagIncl_conj

/-- info: 'SignedFactorSimulation.flagIncl_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.flagIncl_isometry

/-- info: 'SignedFactorSimulation.sqrt_sq_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.sqrt_sq_complex

/-- info: 'SignedFactorSimulation.flagIncl_conj_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.flagIncl_conj_right

/-- info: 'SignedFactorSimulation.Known.atten_Cop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.atten_Cop

/-- info: 'SignedFactorSimulation.Known.atten_Dop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.atten_Dop

/-- info: 'SignedFactorSimulation.flat2_dbl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.flat2_dbl

/-! #### `SignedFactorSimulation.Parameters` -/

/-- info: 'SignedFactorSimulation.exp_one_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.exp_one_lt

/-- info: 'SignedFactorSimulation.exp_one_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.exp_one_gt

/-- info: 'SignedFactorSimulation.exp_two_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.exp_two_eq

/-- info: 'SignedFactorSimulation.exp_two_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.exp_two_lt

/-- info: 'SignedFactorSimulation.exp_two_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.exp_two_gt

/-- info: 'SignedFactorSimulation.four_lt_log_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.four_lt_log_64

/-- info: 'SignedFactorSimulation.log_le_two_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.log_le_two_sqrt

/-- info: 'SignedFactorSimulation.sqrt_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.sqrt_add_le

/-- info: 'SignedFactorSimulation.log_inv_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.log_inv_ge

/-- info: 'SignedFactorSimulation.one_lt_exp_one_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.one_lt_exp_one_add

/-- info: 'SignedFactorSimulation.log_exp_one_add_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.log_exp_one_add_pos

/-- info: 'SignedFactorSimulation.rb_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.rb_pos

/-- info: 'SignedFactorSimulation.rb_ge_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.rb_ge_half

/-- info: 'SignedFactorSimulation.order_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.order_ge

/-- info: 'SignedFactorSimulation.order_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.order_le

/-- info: 'SignedFactorSimulation.one_le_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.one_le_order

/-- info: 'SignedFactorSimulation.order_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.order_log

/-- info: 'SignedFactorSimulation.count_le_of_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.count_le_of_large

/-- info: 'SignedFactorSimulation.count_le_of_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.count_le_of_small

/-! #### `SignedFactorSimulation.Theorem` -/

/-- info: 'SignedFactorSimulation.Known.ham_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.ham_star

/-- info: 'SignedFactorSimulation.Known.norm_ham_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.Known.norm_ham_le

/-- info: 'SignedFactorSimulation.diagonal_unitary_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.diagonal_unitary_const

/-- info: 'SignedFactorSimulation.smul_le_smul_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignedFactorSimulation.smul_le_smul_one
