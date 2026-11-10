import GateOptimalBinary.Bounded
import GateOptimalBinary.FactorLayout
import GateOptimalBinary.FactorLocal
import GateOptimalBinary.SignedIface
import GateOptimalBinary.SignedNative
import GateOptimalBinary.ClipLocal
import GateOptimalBinary.ClipOps
import GateOptimalBinary.ClipLayout
import GateOptimalBinary.ClipIface
import GateOptimalBinary.ClipMoments
import GateOptimalBinary.ClipCore
import GateOptimalBinary.ClipTransfer
import GateOptimalBinary.ClipNative
import GateOptimalBinary.Main
import GateOptimalBinary.Tables

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (431 theorems), beginning
with the main theorems, then in module order. 401 reports list exactly `propext`, `Classical.choice`
and `Quot.sound`; the other 30 list a strict subset. -/

/-! ### Final theorems: Theorem `gate:thm:main` from binary sparse oracles, its total-error and
finite-gate-set forms, the clipped transfer, and the interfaces and native identities -/

/-- info: 'GateOptimalBinary.gate_optimal_binary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.gate_optimal_binary

/-- info: 'GateOptimalBinary.gate_optimal_binary_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.gate_optimal_binary_total

/-- info: 'GateOptimalBinary.gate_optimal_binary_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.gate_optimal_binary_synth

/-- info: 'GateOptimalBinary.gate_optimal_binary_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.gate_optimal_binary_tables

/-- info: 'GateOptimalBinary.gate_optimal_binary_synth_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.gate_optimal_binary_synth_tables

/-- info: 'GateOptimalBinary.factorWordArith_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.factorWordArith_exists

/-- info: 'GateOptimalBinary.clipArith_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clipArith_exists

/-- info: 'GateOptimalBinary.synthClaims_of_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.synthClaims_of_native

/-- info: 'GateOptimalBinary.gate_optimal_native_clip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.gate_optimal_native_clip

/-- info: 'GateOptimalBinary.gate_optimal_native_clip_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.gate_optimal_native_clip_total

/-- info: 'GateOptimalBinary.clip_claims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clip_claims

/-- info: 'GateOptimalBinary.clip_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clip_transfer

/-- info: 'GateOptimalBinary.ClipNative.pc_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ClipNative.pc_approx

/-- info: 'GateOptimalBinary.clip_coreData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clip_coreData

/-- info: 'GateOptimalBinary.clip_compress_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clip_compress_K

/-- info: 'GateOptimalBinary.clip_spectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clip_spectral

/-- info: 'GateOptimalBinary.clD_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clD_split

/-- info: 'GateOptimalBinary.clFO_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clFO_native

/-- info: 'GateOptimalBinary.clND_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clND_native

/-- info: 'GateOptimalBinary.sgFO_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sgFO_native

/-- info: 'GateOptimalBinary.sg_ham' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sg_ham

/-- info: 'GateOptimalBinary.sg_factor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sg_factor_le

/-- info: 'GateOptimalBinary.bdK_compress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.bdK_compress

/-- info: 'GateOptimalBinary.bdK_boundary_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.bdK_boundary_le

/-- info: 'GateOptimalBinary.bdPriv_elift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.bdPriv_elift

/-! ### The bounded regime (`Bounded`) -/

/-- info: 'GateOptimalBinary.elift_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.elift_smul

/-- info: 'GateOptimalBinary.elift_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.elift_add

/-- info: 'GateOptimalBinary.elift_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.elift_mul

/-- info: 'GateOptimalBinary.elift_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.elift_star

/-- info: 'GateOptimalBinary.matrixOperator_real_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.matrixOperator_real_smul

/-- info: 'GateOptimalBinary.bdK_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.bdK_self

/-- info: 'GateOptimalBinary.generator_norm_le_entry'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.generator_norm_le_entry'

/-- info: 'GateOptimalBinary.bdK_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.bdK_norm_le

/-- info: 'GateOptimalBinary.sqrt_sigma_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sqrt_sigma_eq

/-- info: 'GateOptimalBinary.bd_boundary_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.bd_boundary_lift

/-- info: 'GateOptimalBinary.adjoint_comp_self_of_sa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.adjoint_comp_self_of_sa

/-- info: 'GateOptimalBinary.bdScale_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.bdScale_pos

/-! ### The register of the signed factor (`FactorLayout`) -/

/-- info: 'GateOptimalBinary.fW_ne_zW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.fW_ne_zW

/-- info: 'GateOptimalBinary.cU_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cU_injective

/-- info: 'GateOptimalBinary.cU_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cU_val

/-- info: 'GateOptimalBinary.cU_ne_fW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cU_ne_fW

/-- info: 'GateOptimalBinary.cU_ne_zW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cU_ne_zW

/-- info: 'GateOptimalBinary.fin_cases_U' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.fin_cases_U

/-- info: 'GateOptimalBinary.ιU_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιU_injective

/-- info: 'GateOptimalBinary.ιU_inl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιU_inl

/-- info: 'GateOptimalBinary.ιU_inr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιU_inr

/-- info: 'GateOptimalBinary.ιU_ne_f' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιU_ne_f

/-- info: 'GateOptimalBinary.ιU_ne_z' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιU_ne_z

/-- info: 'GateOptimalBinary.out_ιU_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.out_ιU_iff

/-- info: 'GateOptimalBinary.ιU_oPR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιU_oPR

/-- info: 'GateOptimalBinary.extU_ιU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.extU_ιU

/-- info: 'GateOptimalBinary.extU_f' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.extU_f

/-- info: 'GateOptimalBinary.extU_z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.extU_z

/-- info: 'GateOptimalBinary.extU_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.extU_comp

/-- info: 'GateOptimalBinary.extU_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.extU_injective

/-- info: 'GateOptimalBinary.eq_extU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.eq_extU

/-- info: 'GateOptimalBinary.ι2_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ι2_apply

/-- info: 'GateOptimalBinary.ι2_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ι2_bas

/-- info: 'GateOptimalBinary.ι2_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ι2_adjoint_apply

/-- info: 'GateOptimalBinary.ι2_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ι2_isometry

/-- info: 'GateOptimalBinary.ι2_eq_put' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ι2_eq_put

/-- info: 'GateOptimalBinary.localOp_ι2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.localOp_ι2

/-- info: 'GateOptimalBinary.fl_iota0_ι2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.fl_iota0_ι2

/-- info: 'GateOptimalBinary.matOp_diagonal_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.matOp_diagonal_apply

/-- info: 'GateOptimalBinary.diag_comm_localOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.diag_comm_localOp

/-- info: 'GateOptimalBinary.diag_eq_localOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.diag_eq_localOp

/-- info: 'GateOptimalBinary.conj_dg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.conj_dg

/-- info: 'GateOptimalBinary.locU_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.locU_injective

/-- info: 'GateOptimalBinary.locU_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.locU_zero

/-- info: 'GateOptimalBinary.locU_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.locU_one

/-- info: 'GateOptimalBinary.locU_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.locU_two

/-- info: 'GateOptimalBinary.locU_ne_ixPR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.locU_ne_ixPR

/-- info: 'GateOptimalBinary.overwrite_locU_extU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.overwrite_locU_extU

/-- info: 'GateOptimalBinary.extU_locU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.extU_locU

/-- info: 'GateOptimalBinary.clearCfg_locU_extU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clearCfg_locU_extU

/-- info: 'GateOptimalBinary.sum_cfg3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sum_cfg3

/-- info: 'GateOptimalBinary.ι2_compress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ι2_compress

/-! ### The compressions of the stable signed factor (`FactorLocal`) -/

/-- info: 'GateOptimalBinary.uMat_pin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.uMat_pin

/-- info: 'GateOptimalBinary.uMat_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.uMat_col

/-- info: 'GateOptimalBinary.piP_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.piP_gram

/-- info: 'GateOptimalBinary.piM_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.piM_gram

/-- info: 'GateOptimalBinary.sqrt_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sqrt_norm_sq

/-- info: 'GateOptimalBinary.triple_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.triple_apply

/-- info: 'GateOptimalBinary.uMat_sign_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.uMat_sign_block

/-- info: 'GateOptimalBinary.uMat_weight_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.uMat_weight_block

/-! ### The signed-factor interface (`SignedIface`) -/

/-- info: 'GateOptimalBinary.unconj_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.unconj_conj

/-- info: 'GateOptimalBinary.unconj_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.unconj_eq

/-- info: 'GateOptimalBinary.iota0_unconj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.iota0_unconj

/-- info: 'GateOptimalBinary.iota0_unconj_ι2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.iota0_unconj_ι2

/-- info: 'GateOptimalBinary.gateOK_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.gateOK_map

/-- info: 'GateOptimalBinary.sgUJg_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sgUJg_ok

/-- info: 'GateOptimalBinary.sgUJg_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sgUJg_length

/-- info: 'GateOptimalBinary.gRun_sgUJg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.gRun_sgUJg

/-- info: 'GateOptimalBinary.norm_cvU_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.norm_cvU_le

/-- info: 'GateOptimalBinary.FuF_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.FuF_isUnitary

/-- info: 'GateOptimalBinary.blk_uMat_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.blk_uMat_unitary

/-- info: 'GateOptimalBinary.AuF_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.AuF_isUnitary

/-- info: 'GateOptimalBinary.UF_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.UF_isUnitary

/-- info: 'GateOptimalBinary.sgU_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sgU_isUnitary

/-- info: 'GateOptimalBinary.sgU_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sgU_eq

/-- info: 'GateOptimalBinary.UJop_eq_unconj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.UJop_eq_unconj

/-- info: 'GateOptimalBinary.sgUJ_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sgUJ_adj

/-- info: 'GateOptimalBinary.sg_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sg_factor

/-- info: 'GateOptimalBinary.unconj_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.unconj_sandwich

/-- info: 'GateOptimalBinary.sg_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sg_sandwich

/-- info: 'GateOptimalBinary.projF_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.projF_comm

/-- info: 'GateOptimalBinary.signF_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.signF_comm

/-- info: 'GateOptimalBinary.projF_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.projF_adjoint

/-- info: 'GateOptimalBinary.sg_X_ι2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sg_X_ι2

/-- info: 'GateOptimalBinary.projF_signF_projF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.projF_signF_projF

/-- info: 'GateOptimalBinary.projF_projF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.projF_projF

/-- info: 'GateOptimalBinary.blk_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.blk_diagonal

/-- info: 'GateOptimalBinary.AuF_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.AuF_sandwich

/-- info: 'GateOptimalBinary.cvU_clr_extU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cvU_clr_extU

/-- info: 'GateOptimalBinary.qmat_generator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.qmat_generator

/-- info: 'GateOptimalBinary.qmat_smul_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.qmat_smul_one

/-- info: 'GateOptimalBinary.sg_sign_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sg_sign_edge

/-- info: 'GateOptimalBinary.sg_weight_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sg_weight_edge

/-- info: 'GateOptimalBinary.conj_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.conj_mid

/-- info: 'GateOptimalBinary.FuF_comp_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.FuF_comp_adjoint

/-- info: 'GateOptimalBinary.sg_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sg_mid

/-- info: 'GateOptimalBinary.Y_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.Y_sandwich

/-- info: 'GateOptimalBinary.sg_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sg_tail

/-- info: 'GateOptimalBinary.sg_Cop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sg_Cop

/-- info: 'GateOptimalBinary.sg_Dop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sg_Dop

/-- info: 'GateOptimalBinary.qCop_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.qCop_eq

/-- info: 'GateOptimalBinary.qDop_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.qDop_eq

/-- info: 'GateOptimalBinary.matOp_diag_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.matOp_diag_le

/-- info: 'GateOptimalBinary.qlift_matrixOperator_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.qlift_matrixOperator_diagonal

/-- info: 'GateOptimalBinary.inv_sqrt_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.inv_sqrt_sigma

/-! ### The native signed factor (`SignedNative`) -/

/-- info: 'GateOptimalBinary.overwrite_update_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.overwrite_update_in

/-- info: 'GateOptimalBinary.flipCfg_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.flipCfg_map

/-- info: 'GateOptimalBinary.cfgRun_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cfgRun_map

/-- info: 'GateOptimalBinary.classical_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.classical_map

/-- info: 'GateOptimalBinary.ιS_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιS_injective

/-- info: 'GateOptimalBinary.ιF_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιF_injective

/-- info: 'GateOptimalBinary.ιE_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιE_injective

/-- info: 'GateOptimalBinary.ιB_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιB_injective

/-- info: 'GateOptimalBinary.vF_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.vF_injective

/-- info: 'GateOptimalBinary.locB_ne_vF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.locB_ne_vF

/-- info: 'GateOptimalBinary.valF_overwrite_locB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.valF_overwrite_locB

/-- info: 'GateOptimalBinary.sgFO_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sgFO_public

/-- info: 'GateOptimalBinary.sgFO_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sgFO_arith

/-- info: 'GateOptimalBinary.cleanEmb_put' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cleanEmb_put

/-- info: 'GateOptimalBinary.compute_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.compute_transport

/-- info: 'GateOptimalBinary.locBF_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.locBF_injective

/-- info: 'GateOptimalBinary.ιB_oB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιB_oB

/-- info: 'GateOptimalBinary.ιF_ne_locF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιF_ne_locF

/-- info: 'GateOptimalBinary.ιB_ne_locBF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιB_ne_locBF

/-- info: 'GateOptimalBinary.locBF_mem_range_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.locBF_mem_range_iff

/-- info: 'GateOptimalBinary.overwrite_locBF_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.overwrite_locBF_comp

/-- info: 'GateOptimalBinary.sigF_overwrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sigF_overwrite

/-- info: 'GateOptimalBinary.sigF_locBF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sigF_locBF

/-- info: 'GateOptimalBinary.sigF_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sigF_val

/-- info: 'GateOptimalBinary.locE_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.locE_injective

/-- info: 'GateOptimalBinary.ιFE_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιFE_injective

/-- info: 'GateOptimalBinary.liftE_FuF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.liftE_FuF

/-- info: 'GateOptimalBinary.edgeU_clear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.edgeU_clear

/-- info: 'GateOptimalBinary.liftE_AuF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.liftE_AuF

/-- info: 'GateOptimalBinary.selOp_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.selOp_const

/-- info: 'GateOptimalBinary.sel_liftA_sgU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sel_liftA_sgU

/-- info: 'GateOptimalBinary.put_sum_smul_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.put_sum_smul_bas

/-- info: 'GateOptimalBinary.edgeF_overwrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.edgeF_overwrite

/-- info: 'GateOptimalBinary.overwrite_locBF_elim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.overwrite_locBF_elim

/-- info: 'GateOptimalBinary.valF_overwrite_locBF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.valF_overwrite_locBF

/-- info: 'GateOptimalBinary.Udec_sgFO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.Udec_sgFO

/-- info: 'GateOptimalBinary.sgFO_compute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sgFO_compute

/-- info: 'GateOptimalBinary.sgFO_dec_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sgFO_dec_comm

/-! ### The local algebra of the clipped regime (`ClipLocal`) -/

/-- info: 'GateOptimalBinary.phase_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.phase_phase

/-- info: 'GateOptimalBinary.piP_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.piP_phase

/-- info: 'GateOptimalBinary.piM_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.piM_phase

/-- info: 'GateOptimalBinary.eMat_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.eMat_phase

/-- info: 'GateOptimalBinary.eMat_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.eMat_zero

/-- info: 'GateOptimalBinary.eMat_real_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.eMat_real_mul

/-- info: 'GateOptimalBinary.eMat_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.eMat_conjTranspose

/-- info: 'GateOptimalBinary.eMat_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.eMat_mul_self

/-- info: 'GateOptimalBinary.eMat_phase_mul_piP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.eMat_phase_mul_piP

/-- info: 'GateOptimalBinary.eMat_phase_mul_piM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.eMat_phase_mul_piM

/-- info: 'GateOptimalBinary.pinch_eMat_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.pinch_eMat_phase

/-- info: 'GateOptimalBinary.pinch_piP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.pinch_piP

/-- info: 'GateOptimalBinary.pinch_piM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.pinch_piM

/-- info: 'GateOptimalBinary.pinch_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.pinch_one

/-- info: 'GateOptimalBinary.pinch_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.pinch_zero

/-- info: 'GateOptimalBinary.cayley_mul_R1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cayley_mul_R1

/-- info: 'GateOptimalBinary.R1_mul_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.R1_mul_cayley

/-- info: 'GateOptimalBinary.fblk_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.fblk_apply

/-- info: 'GateOptimalBinary.fblk_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.fblk_mul

/-- info: 'GateOptimalBinary.fblk_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.fblk_conjTranspose

/-- info: 'GateOptimalBinary.fblk_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.fblk_one

/-- info: 'GateOptimalBinary.fblk_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.fblk_add

/-- info: 'GateOptimalBinary.fblk_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.fblk_sub

/-- info: 'GateOptimalBinary.fblk_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.fblk_smul

/-- info: 'GateOptimalBinary.uMat_col_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.uMat_col_apply

/-- info: 'GateOptimalBinary.piP_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.piP_conj

/-- info: 'GateOptimalBinary.piM_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.piM_conj

/-- info: 'GateOptimalBinary.sqrt_one_sub_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sqrt_one_sub_sq

/-- info: 'GateOptimalBinary.uMat_fblk_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.uMat_fblk_block

/-! ### Operator tools for the clipped regime (`ClipOps`) -/

/-- info: 'GateOptimalBinary.condOp_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.condOp_zero

/-- info: 'GateOptimalBinary.condOp_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.condOp_add

/-- info: 'GateOptimalBinary.condOp_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.condOp_sub

/-- info: 'GateOptimalBinary.condOp_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.condOp_smul

/-- info: 'GateOptimalBinary.condOp_one'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.condOp_one'

/-- info: 'GateOptimalBinary.norm_condOp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.norm_condOp_le

/-- info: 'GateOptimalBinary.condOp_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.condOp_inner

/-- info: 'GateOptimalBinary.condOp_one_fblk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.condOp_one_fblk

/-- info: 'GateOptimalBinary.condOp_eq_fblk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.condOp_eq_fblk

/-- info: 'GateOptimalBinary.conj_comp'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.conj_comp'

/-- info: 'GateOptimalBinary.conj_one'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.conj_one'

/-- info: 'GateOptimalBinary.spectral_conj'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.spectral_conj'

/-- info: 'GateOptimalBinary.conj_isometry'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.conj_isometry'

/-- info: 'GateOptimalBinary.norm_conj_le'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.norm_conj_le'

/-- info: 'GateOptimalBinary.R1_conj'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.R1_conj'

/-- info: 'GateOptimalBinary.bulk_conj'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.bulk_conj'

/-- info: 'GateOptimalBinary.norm_le_of_re_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.norm_le_of_re_inner

/-! ### The register of the clipped regime (`ClipLayout`) -/

/-- info: 'GateOptimalBinary.ιS_ne_gW' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιS_ne_gW

/-- info: 'GateOptimalBinary.out_ιS_iff' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.out_ιS_iff

/-- info: 'GateOptimalBinary.extG_ιS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.extG_ιS

/-- info: 'GateOptimalBinary.extG_g' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.extG_g

/-- info: 'GateOptimalBinary.extG_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.extG_comp

/-- info: 'GateOptimalBinary.eq_extG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.eq_extG

/-- info: 'GateOptimalBinary.extG_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.extG_injective

/-- info: 'GateOptimalBinary.extG_locF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.extG_locF

/-- info: 'GateOptimalBinary.locF_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.locF_apply

/-- info: 'GateOptimalBinary.overwrite_locF_extG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.overwrite_locF_extG

/-- info: 'GateOptimalBinary.clearCfg_locF_extG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clearCfg_locF_extG

/-- info: 'GateOptimalBinary.ιG0_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιG0_apply

/-- info: 'GateOptimalBinary.outPart_ιS_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.outPart_ιS_iff

/-- info: 'GateOptimalBinary.ιG0_eq_put' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιG0_eq_put

/-- info: 'GateOptimalBinary.localOp_ιG0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.localOp_ιG0

/-- info: 'GateOptimalBinary.ιG0_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιG0_bas

/-- info: 'GateOptimalBinary.ιGp_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιGp_apply

/-- info: 'GateOptimalBinary.ιGp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιGp_eq

/-- info: 'GateOptimalBinary.localOp_ιGp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.localOp_ιGp

/-- info: 'GateOptimalBinary.ιGp_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιGp_bas

/-- info: 'GateOptimalBinary.hamp_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.hamp_real

/-- info: 'GateOptimalBinary.hamp_mul_hamp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.hamp_mul_hamp

/-- info: 'GateOptimalBinary.ιGp_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιGp_adjoint_apply

/-- info: 'GateOptimalBinary.hadGate_ιG0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.hadGate_ιG0

/-- info: 'GateOptimalBinary.ιGp_compress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιGp_compress

/-- info: 'GateOptimalBinary.clUJg_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clUJg_ok

/-- info: 'GateOptimalBinary.clUJg_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clUJg_length

/-- info: 'GateOptimalBinary.gRun_clUJg_ιG0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.gRun_clUJg_ιG0

/-- info: 'GateOptimalBinary.fl_iota0_ιG0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.fl_iota0_ιG0

/-- info: 'GateOptimalBinary.clip_boundary_reduce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clip_boundary_reduce

/-- info: 'GateOptimalBinary.qmat_qop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.qmat_qop

/-- info: 'GateOptimalBinary.sg_boundary_compress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sg_boundary_compress

/-! ### The clipped interface operators (`ClipIface`) -/

/-- info: 'GateOptimalBinary.norm_cl2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.norm_cl2_le

/-- info: 'GateOptimalBinary.norm_cF_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.norm_cF_le

/-- info: 'GateOptimalBinary.AF_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.AF_isUnitary

/-- info: 'GateOptimalBinary.FL_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.FL_isUnitary

/-- info: 'GateOptimalBinary.WF_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.WF_isUnitary

/-- info: 'GateOptimalBinary.condOp_comp'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.condOp_comp'

/-- info: 'GateOptimalBinary.yCfg_suc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.yCfg_suc

/-- info: 'GateOptimalBinary.eMat_yC_piP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.eMat_yC_piP

/-- info: 'GateOptimalBinary.eMat_yC_piM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.eMat_yC_piM

/-- info: 'GateOptimalBinary.located_spectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.located_spectral

/-- info: 'GateOptimalBinary.LD_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.LD_isometry

/-- info: 'GateOptimalBinary.unconj_WF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.unconj_WF

/-- info: 'GateOptimalBinary.WFa_adj_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.WFa_adj_comp

/-- info: 'GateOptimalBinary.WFa_comp_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.WFa_comp_adj

/-- info: 'GateOptimalBinary.clD_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clD_isometry

/-- info: 'GateOptimalBinary.clD_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clD_isUnitary

/-- info: 'GateOptimalBinary.gW_ne_locF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.gW_ne_locF

/-- info: 'GateOptimalBinary.edge_ne_locF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.edge_ne_locF

/-- info: 'GateOptimalBinary.edgeC_overwrite_locF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.edgeC_overwrite_locF

/-- info: 'GateOptimalBinary.edgeC_update_locF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.edgeC_update_locF

/-- info: 'GateOptimalBinary.located_fblk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.located_fblk

/-- info: 'GateOptimalBinary.AF_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.AF_sandwich

/-- info: 'GateOptimalBinary.edgeC_extG_extU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.edgeC_extG_extU

/-- info: 'GateOptimalBinary.cF_extG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cF_extG

/-- info: 'GateOptimalBinary.clip_compress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clip_compress

/-! ### Edge compressions and row and column sums (`ClipMoments`) -/

/-- info: 'GateOptimalBinary.inner_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.inner_lift

/-- info: 'GateOptimalBinary.isSelfAdjoint_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.isSelfAdjoint_lift

/-- info: 'GateOptimalBinary.norm_edge_compress_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.norm_edge_compress_le

/-- info: 'GateOptimalBinary.qop_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.qop_smul

/-- info: 'GateOptimalBinary.qop_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.qop_one

/-- info: 'GateOptimalBinary.qop_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.qop_mul

/-- info: 'GateOptimalBinary.qop_isSelfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.qop_isSelfAdjoint

/-- info: 'GateOptimalBinary.quad_smul_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.quad_smul_one

/-- info: 'GateOptimalBinary.quad_smul_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.quad_smul_proj

/-- info: 'GateOptimalBinary.cl2_row_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cl2_row_le

/-- info: 'GateOptimalBinary.cl2_col_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cl2_col_le

/-- info: 'GateOptimalBinary.norm_cl1_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.norm_cl1_sq_le

/-- info: 'GateOptimalBinary.cl1_row_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cl1_row_le

/-- info: 'GateOptimalBinary.cl1_col_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cl1_col_le

/-! ### The core data and the clipped interface (`ClipCore`) -/

/-- info: 'GateOptimalBinary.cj_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cj_eq

/-- info: 'GateOptimalBinary.cj_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cj_comp

/-- info: 'GateOptimalBinary.cj_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cj_one

/-- info: 'GateOptimalBinary.cj_R1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cj_R1

/-- info: 'GateOptimalBinary.cj_bulk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cj_bulk

/-- info: 'GateOptimalBinary.norm_cj_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.norm_cj_le

/-- info: 'GateOptimalBinary.cj_compress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cj_compress

/-- info: 'GateOptimalBinary.norm_cj_compress_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.norm_cj_compress_le

/-- info: 'GateOptimalBinary.pinch_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.pinch_smul

/-- info: 'GateOptimalBinary.pinch_smul_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.pinch_smul_one

/-- info: 'GateOptimalBinary.eMat_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.eMat_add

/-- info: 'GateOptimalBinary.abs_mul_abs_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.abs_mul_abs_sq

/-- info: 'GateOptimalBinary.edgeOp_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.edgeOp_P

/-- info: 'GateOptimalBinary.edgeOp_M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.edgeOp_M

/-- info: 'GateOptimalBinary.edgeOp_KK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.edgeOp_KK

/-- info: 'GateOptimalBinary.edgeOp_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.edgeOp_B

/-- info: 'GateOptimalBinary.edgeOp_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.edgeOp_K

/-- info: 'GateOptimalBinary.LK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.LK_eq

/-- info: 'GateOptimalBinary.LP_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.LP_eq

/-- info: 'GateOptimalBinary.LM_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.LM_eq

/-- info: 'GateOptimalBinary.LKK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.LKK_eq

/-- info: 'GateOptimalBinary.Lbulk_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.Lbulk_eq

/-- info: 'GateOptimalBinary.LB_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.LB_eq

/-- info: 'GateOptimalBinary.LR1_bulk_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.LR1_bulk_eq

/-- info: 'GateOptimalBinary.clK_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clK_eq

/-- info: 'GateOptimalBinary.clPp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clPp_eq

/-- info: 'GateOptimalBinary.clPm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clPm_eq

/-- info: 'GateOptimalBinary.frob2_R1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.frob2_R1

/-- info: 'GateOptimalBinary.frob2_R1_bulk_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.frob2_R1_bulk_le

/-- info: 'GateOptimalBinary.clip_bulk_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clip_bulk_le

/-- info: 'GateOptimalBinary.norm_mul_self_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.norm_mul_self_comp

/-- info: 'GateOptimalBinary.smul_proj_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.smul_proj_conjTranspose

/-- info: 'GateOptimalBinary.clip_P_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clip_P_le

/-- info: 'GateOptimalBinary.clip_M_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clip_M_le

/-- info: 'GateOptimalBinary.smul_one_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.smul_one_conjTranspose

/-- info: 'GateOptimalBinary.clip_KK_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clip_KK_le

/-- info: 'GateOptimalBinary.clip_B_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clip_B_le

/-- info: 'GateOptimalBinary.clJ_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clJ_isometry

/-- info: 'GateOptimalBinary.clip_second_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clip_second_sq

/-- info: 'GateOptimalBinary.clip_isoP_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clip_isoP_sq

/-- info: 'GateOptimalBinary.clip_isoM_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clip_isoM_sq

/-- info: 'GateOptimalBinary.clip_moment_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clip_moment_sq

/-- info: 'GateOptimalBinary.le_of_sq_le_sq'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.le_of_sq_le_sq'

/-- info: 'GateOptimalBinary.qop_eMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.qop_eMat

/-! ### The factor-conjugated native private call (`ClipTransfer`) -/

/-- info: 'GateOptimalBinary.ClipNative.calls_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ClipNative.calls_eq

/-- info: 'GateOptimalBinary.ClipNative.pc_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ClipNative.pc_nGates

/-- info: 'GateOptimalBinary.ClipNative.pc_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ClipNative.pc_valid

/-- info: 'GateOptimalBinary.preserves_selPR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.preserves_selPR

/-- info: 'GateOptimalBinary.ideal_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ideal_conj

/-- info: 'GateOptimalBinary.selOp_const_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.selOp_const_comp

/-- info: 'GateOptimalBinary.selOp_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.selOp_split

/-- info: 'GateOptimalBinary.ClipNative.Usel_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ClipNative.Usel_isUnitary

/-- info: 'GateOptimalBinary.ClipNative.Csel_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ClipNative.Csel_isUnitary

/-- info: 'GateOptimalBinary.ClipNative.sel_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ClipNative.sel_split

/-! ### The native clipped private operation (`ClipNative`) -/

/-- info: 'GateOptimalBinary.gBF_ne_vF' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.gBF_ne_vF

/-- info: 'GateOptimalBinary.locBF_ne_gBF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.locBF_ne_gBF

/-- info: 'GateOptimalBinary.locBF_ne_vF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.locBF_ne_vF

/-- info: 'GateOptimalBinary.ιB_ne_gBF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιB_ne_gBF

/-- info: 'GateOptimalBinary.ιFin_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιFin_injective

/-- info: 'GateOptimalBinary.ιCin_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ιCin_injective

/-- info: 'GateOptimalBinary.locBF_ne_ιFin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.locBF_ne_ιFin

/-- info: 'GateOptimalBinary.locBF1_ne_ιCin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.locBF1_ne_ιCin

/-- info: 'GateOptimalBinary.inF_overwrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.inF_overwrite

/-- info: 'GateOptimalBinary.inC_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.inC_update

/-- info: 'GateOptimalBinary.norm_cfdec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.norm_cfdec_le

/-- info: 'GateOptimalBinary.clFO_locB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clFO_locB

/-- info: 'GateOptimalBinary.clFO_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clFO_public

/-- info: 'GateOptimalBinary.cfgRun_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cfgRun_placed

/-- info: 'GateOptimalBinary.clFO_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clFO_arith

/-- info: 'GateOptimalBinary.clND_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clND_public

/-- info: 'GateOptimalBinary.clND_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clND_arith

/-- info: 'GateOptimalBinary.conj_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.conj_split

/-- info: 'GateOptimalBinary.FL_comp_adj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.FL_comp_adj

/-- info: 'GateOptimalBinary.Uf_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.Uf_isUnitary

/-- info: 'GateOptimalBinary.LD_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.LD_isUnitary

/-- info: 'GateOptimalBinary.Cf_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.Cf_isUnitary

/-- info: 'GateOptimalBinary.clW_compute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clW_compute

/-- info: 'GateOptimalBinary.sigF_gBF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sigF_gBF

/-- info: 'GateOptimalBinary.cF_clear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cF_clear

/-- info: 'GateOptimalBinary.liftE_AF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.liftE_AF

/-- info: 'GateOptimalBinary.Udec_clFO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.Udec_clFO

/-- info: 'GateOptimalBinary.matrix_eq_gauss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.matrix_eq_gauss

/-- info: 'GateOptimalBinary.cfdec_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cfdec_sig

/-- info: 'GateOptimalBinary.clFO_dec_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clFO_dec_comm

/-- info: 'GateOptimalBinary.liftE_LD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.liftE_LD

/-- info: 'GateOptimalBinary.Rdec_clND' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.Rdec_clND

/-- info: 'GateOptimalBinary.update_locBF_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.update_locBF_eq

/-- info: 'GateOptimalBinary.sigF_update_o' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sigF_update_o

/-- info: 'GateOptimalBinary.sigF_o' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sigF_o

/-- info: 'GateOptimalBinary.ckdec_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ckdec_sig

/-- info: 'GateOptimalBinary.clND_rdec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.clND_rdec

/-- info: 'GateOptimalBinary.exists_zero_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.exists_zero_slot

/-! ### The binary endpoint (`Main`) -/

/-- info: 'GateOptimalBinary.SynthClaims.gates_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.SynthClaims.gates_log

/-- info: 'GateOptimalBinary.MainParams.μ_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.MainParams.μ_pos

/-- info: 'GateOptimalBinary.MainParams.η_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.MainParams.η_pos

/-- info: 'GateOptimalBinary.MainParams.σ_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.MainParams.σ_one

/-- info: 'GateOptimalBinary.sysH_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sysH_star

/-- info: 'GateOptimalBinary.zeroSlot_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.zeroSlot_spec

/-- info: 'GateOptimalBinary.computeV_calls_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.computeV_calls_total

/-- info: 'GateOptimalBinary.bdNativeCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.bdNativeCost_le

/-- info: 'GateOptimalBinary.binNB_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.binNB_calls

/-- info: 'GateOptimalBinary.binNB_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.binNB_cost

/-- info: 'GateOptimalBinary.binNS_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.binNS_calls

/-- info: 'GateOptimalBinary.binNS_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.binNS_cost

/-- info: 'GateOptimalBinary.binNC_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.binNC_calls

/-- info: 'GateOptimalBinary.binNC_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.binNC_cost

/-! ### Lookup-table arithmetic (`Tables`) -/

/-- info: 'GateOptimalBinary.andChain_cs_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.andChain_cs_length

/-- info: 'GateOptimalBinary.andLast_mem' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.andLast_mem

/-- info: 'GateOptimalBinary.mcGate_cs_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.mcGate_cs_length

/-- info: 'GateOptimalBinary.mcGate_classical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.mcGate_classical

/-- info: 'GateOptimalBinary.bas_one_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.bas_one_injective

/-- info: 'GateOptimalBinary.cfgRun_mcGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cfgRun_mcGate

/-- info: 'GateOptimalBinary.lits_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.lits_length

/-- info: 'GateOptimalBinary.mem_lits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.mem_lits

/-- info: 'GateOptimalBinary.ctrlOK_lits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ctrlOK_lits

/-- info: 'GateOptimalBinary.tableG_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.tableG_length_le

/-- info: 'GateOptimalBinary.TableOK.lit_ne_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.TableOK.lit_ne_out

/-- info: 'GateOptimalBinary.TableOK.lit_ne_fl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.TableOK.lit_ne_fl

/-- info: 'GateOptimalBinary.tableG_classical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.tableG_classical

/-- info: 'GateOptimalBinary.tableG_cs_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.tableG_cs_length

/-- info: 'GateOptimalBinary.cfgRun_tableG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.cfgRun_tableG

/-- info: 'GateOptimalBinary.mem_flW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.mem_flW

/-- info: 'GateOptimalBinary.tableOK_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.tableOK_arith

/-- info: 'GateOptimalBinary.mem_tablePairs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.mem_tablePairs

/-- info: 'GateOptimalBinary.tableC_compute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.tableC_compute

/-- info: 'GateOptimalBinary.tableC_classical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.tableC_classical

/-- info: 'GateOptimalBinary.tableC_elem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.tableC_elem

/-- info: 'GateOptimalBinary.tableC_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.tableC_length

/-- info: 'GateOptimalBinary.thetaVal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.thetaVal_eq

/-- info: 'GateOptimalBinary.phiVal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.phiVal_eq

/-- info: 'GateOptimalBinary.alphaVal_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.alphaVal_eq

/-- info: 'GateOptimalBinary.wval_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.wval_cons

/-- info: 'GateOptimalBinary.exists_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.exists_word

/-- info: 'GateOptimalBinary.roundW_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.roundW_spec

/-- info: 'GateOptimalBinary.div_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.div_pow_le

/-- info: 'GateOptimalBinary.sin_sq_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.sin_sq_sub_le

/-- info: 'GateOptimalBinary.phase_eq_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.phase_eq_exp

/-- info: 'GateOptimalBinary.phT_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.phT_mem

/-- info: 'GateOptimalBinary.exp_phT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.exp_phT

/-- info: 'GateOptimalBinary.fac_acc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.fac_acc

/-- info: 'GateOptimalBinary.th_acc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.th_acc

/-- info: 'GateOptimalBinary.ph_acc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.ph_acc

/-- info: 'GateOptimalBinary.norm_wdec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.norm_wdec_le

/-- info: 'GateOptimalBinary.card_VW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.card_VW

/-- info: 'GateOptimalBinary.card_FIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.card_FIn

/-- info: 'GateOptimalBinary.card_CIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalBinary.card_CIn
