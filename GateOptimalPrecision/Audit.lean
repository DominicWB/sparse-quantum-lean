import GateOptimalPrecision.Amplify
import GateOptimalPrecision.Reuse
import GateOptimalPrecision.SignedLayout
import GateOptimalPrecision.SignedExpand
import GateOptimalPrecision.SignedCore
import GateOptimalPrecision.SignedTheorem
import GateOptimalPrecision.ClippedCore
import GateOptimalPrecision.ClippedTheorem
import GateOptimalPrecision.Bounded
import GateOptimalPrecision.Combine
import GateOptimalPrecision.Main
import GateOptimalPrecision.LocalFactor
import GateOptimalPrecision.JointAlgebra
import GateOptimalPrecision.BlockOp
import GateOptimalPrecision.LocalGates
import GateOptimalPrecision.NativeCayley
import GateOptimalPrecision.NativeFactor
import GateOptimalPrecision.NativeSigned
import GateOptimalPrecision.NativeMain
import GateOptimalPrecision.ControlledLocator

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (431 theorems), beginning
with the main theorems, then in module order. 424 reports list exactly `propext`, `Classical.choice`
and `Quot.sound`; the other 7 list a strict subset. -/

/-! ### Final theorems: Theorem `gate:thm:main` and its single-norm case, Propositions `gate:prop:signed` and `gate:prop:core`, the native
transfers, Lemma `gate:lem:reuse` and Section `gate:sec:native` -/

/-- info: 'GateOptimalPrecision.gate_optimal_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.gate_optimal_simulation

/-- info: 'GateOptimalPrecision.gate_optimal_simulation_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.gate_optimal_simulation_single

/-- info: 'GateOptimalPrecision.gate_optimal_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.gate_optimal_native

/-- info: 'GateOptimalPrecision.gate_optimal_native_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.gate_optimal_native_single

/-- info: 'GateOptimalPrecision.gate_optimal_native_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.gate_optimal_native_total

/-- info: 'GateOptimalPrecision.gate_optimal_native_single_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.gate_optimal_native_single_total

/-- info: 'GateOptimalPrecision.signed_gate_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.signed_gate_simulation

/-- info: 'GateOptimalPrecision.signed_native_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.signed_native_simulation

/-- info: 'GateOptimalPrecision.clipped_gate_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.clipped_gate_simulation

/-- info: 'GateOptimalPrecision.clipped_gate_simulation_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.clipped_gate_simulation_neg

/-- info: 'GateOptimalPrecision.bounded_gate_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.bounded_gate_simulation

/-- info: 'GateOptimalPrecision.bounded_gate_simulation_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.bounded_gate_simulation_neg

/-- info: 'GateOptimalPrecision.native_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.native_transfer

/-- info: 'GateOptimalPrecision.signed_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.signed_transfer

/-- info: 'GateOptimalPrecision.cayley_claims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cayley_claims

/-- info: 'GateOptimalPrecision.factor_claims' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.factor_claims

/-- info: 'GateOptimalPrecision.factorMacro_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.factorMacro_approx

/-- info: 'GateOptimalPrecision.factorMacro_inv_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.factorMacro_inv_approx

/-- info: 'GateOptimalPrecision.lcu_ces_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.lcu_ces_pad

/-- info: 'GateOptimalPrecision.lcuI_ces_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.lcuI_ces_pad

/-- info: 'GateOptimalPrecision.ampOp_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ampOp_error

/-- info: 'GateOptimalPrecision.ctrlLoc_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ctrlLoc_agrees

/-- info: 'GateOptimalPrecision.ctrlLoc_inv_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ctrlLoc_inv_agrees

/-- info: 'GateOptimalPrecision.ctrlLoc0_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ctrlLoc0_agrees

/-- info: 'GateOptimalPrecision.ctrlLoc0_inv_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ctrlLoc0_inv_agrees

/-- info: 'GateOptimalPrecision.uMat_action' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.uMat_action

/-- info: 'GateOptimalPrecision.uMat_gates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.uMat_gates

/-- info: 'GateOptimalPrecision.norm_uMat_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_uMat_sub_one_le

/-- info: 'GateOptimalPrecision.norm_uMat_sub_le_of_accuracy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_uMat_sub_le_of_accuracy

/-- info: 'GateOptimalPrecision.norm_uMat_sub_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_uMat_sub_zero_le

/-- info: 'GateOptimalPrecision.uImpl_eq_uMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.uImpl_eq_uMat

/-- info: 'GateOptimalPrecision.norm_uImpl_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_uImpl_sub_le

/-- info: 'GateOptimalPrecision.gRun_locGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.gRun_locGates

/-- info: 'GateOptimalPrecision.edgeMat_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.edgeMat_cayley

/-- info: 'GateOptimalPrecision.hMat_edgeMat_hMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.hMat_edgeMat_hMat

/-- info: 'GateOptimalPrecision.clip_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.clip_split

/-! ### Iterated oblivious amplification (`Amplify`) -/

/-- info: 'GateOptimalPrecision.ampOp_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ampOp_zero

/-- info: 'GateOptimalPrecision.ampOp_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ampOp_succ

/-- info: 'GateOptimalPrecision.ampOp_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ampOp_isUnitary

/-- info: 'GateOptimalPrecision.pres2_ampOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.pres2_ampOp

/-- info: 'GateOptimalPrecision.phaseG_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.phaseG_valid

/-- info: 'GateOptimalPrecision.ampIt_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ampIt_valid

/-- info: 'GateOptimalPrecision.secOK_ampIt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.secOK_ampIt

/-- info: 'GateOptimalPrecision.phaseG_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.phaseG_agrees

/-- info: 'GateOptimalPrecision.ampIt_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ampIt_agrees

/-- info: 'GateOptimalPrecision.ampOp_io' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ampOp_io

/-- info: 'GateOptimalPrecision.norm_le_one_of_adjoint_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_le_one_of_adjoint_comp

/-- info: 'GateOptimalPrecision.ampIt_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ampIt_counts

/-- info: 'GateOptimalPrecision.ampIt_nGates_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ampIt_nGates_le

/-! ### Lemma `gate:lem:reuse`: compiled signed reuse (`Reuse`) -/

/-- info: 'GateOptimalPrecision.lcu_ces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.lcu_ces

/-- info: 'GateOptimalPrecision.netTransfer_cascade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.netTransfer_cascade

/-- info: 'GateOptimalPrecision.padMass_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.padMass_nonneg

/-- info: 'GateOptimalPrecision.padWt_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.padWt_mass

/-- info: 'GateOptimalPrecision.padLen_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.padLen_spec

/-- info: 'GateOptimalPrecision.pad_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.pad_sum

/-! ### The factor interface on the gate register (`SignedLayout`) -/

/-- info: 'GateOptimalPrecision.dg_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.dg_apply

/-- info: 'GateOptimalPrecision.dg_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.dg_comp

/-- info: 'GateOptimalPrecision.dg_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.dg_adjoint

/-- info: 'GateOptimalPrecision.dg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.dg_one

/-- info: 'GateOptimalPrecision.dg_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.dg_add

/-- info: 'GateOptimalPrecision.dg_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.dg_smul

/-- info: 'GateOptimalPrecision.dg_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.dg_sub

/-- info: 'GateOptimalPrecision.dg_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.dg_bas

/-- info: 'GateOptimalPrecision.star_projD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.star_projD

/-- info: 'GateOptimalPrecision.star_signD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.star_signD

/-- info: 'GateOptimalPrecision.projD_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.projD_mul_self

/-- info: 'GateOptimalPrecision.signD_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.signD_mul_self

/-- info: 'GateOptimalPrecision.incl_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.incl_apply

/-- info: 'GateOptimalPrecision.sum_cfg_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sum_cfg_succ

/-- info: 'GateOptimalPrecision.inner_incl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.inner_incl

/-- info: 'GateOptimalPrecision.norm_incl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_incl

/-- info: 'GateOptimalPrecision.incl_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.incl_isometry

/-- info: 'GateOptimalPrecision.tail_cons_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.tail_cons_zero

/-- info: 'GateOptimalPrecision.iota0_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.iota0_succ

/-- info: 'GateOptimalPrecision.overwrite_succ_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.overwrite_succ_zero

/-- info: 'GateOptimalPrecision.tail_overwrite_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.tail_overwrite_succ

/-- info: 'GateOptimalPrecision.liftA_incl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.liftA_incl

/-- info: 'GateOptimalPrecision.liftA_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.liftA_comp

/-- info: 'GateOptimalPrecision.liftA_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.liftA_adjoint

/-- info: 'GateOptimalPrecision.liftA_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.liftA_one

/-- info: 'GateOptimalPrecision.liftA_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.liftA_isUnitary

/-- info: 'GateOptimalPrecision.rotMat_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.rotMat_unitary

/-- info: 'GateOptimalPrecision.flagRot_incl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.flagRot_incl

/-- info: 'GateOptimalPrecision.flagRot_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.flagRot_isUnitary

/-- info: 'GateOptimalPrecision.attUJ_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.attUJ_isUnitary

/-- info: 'GateOptimalPrecision.attProj_incl_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.attProj_incl_false

/-- info: 'GateOptimalPrecision.attProj_incl_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.attProj_incl_true

/-- info: 'GateOptimalPrecision.attSign_incl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.attSign_incl

/-- info: 'GateOptimalPrecision.flagRot_incl_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.flagRot_incl_apply

/-- info: 'GateOptimalPrecision.liftA_incl_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.liftA_incl_apply

/-- info: 'GateOptimalPrecision.attProj_incl_false_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.attProj_incl_false_apply

/-- info: 'GateOptimalPrecision.attProj_incl_true_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.attProj_incl_true_apply

/-- info: 'GateOptimalPrecision.iota0_succ_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.iota0_succ_apply

/-- info: 'GateOptimalPrecision.incl_sign_incl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.incl_sign_incl

/-- info: 'GateOptimalPrecision.attKnown_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.attKnown_factor

/-- info: 'GateOptimalPrecision.sqrt_conj_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sqrt_conj_mul

/-- info: 'GateOptimalPrecision.attKnown_Cop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.attKnown_Cop

/-- info: 'GateOptimalPrecision.attKnown_Dop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.attKnown_Dop

/-! ### Expanding the private calls (`SignedExpand`) -/

/-- info: 'GateOptimalPrecision.attKnown_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.attKnown_phase

/-- info: 'GateOptimalPrecision.attKnown_priv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.attKnown_priv

/-- info: 'GateOptimalPrecision.dmat_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.dmat_unitary

/-- info: 'GateOptimalPrecision.dmat_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.dmat_conjTranspose

/-- info: 'GateOptimalPrecision.gateOp_dmat_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.gateOp_dmat_bas

/-- info: 'GateOptimalPrecision.put_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.put_smul

/-- info: 'GateOptimalPrecision.put_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.put_add

/-- info: 'GateOptimalPrecision.ctrlOK_sec'' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ctrlOK_sec'

/-- info: 'GateOptimalPrecision.clearCfg_anc_sec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.clearCfg_anc_sec

/-- info: 'GateOptimalPrecision.overwrite_anc_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.overwrite_anc_self

/-- info: 'GateOptimalPrecision.oracleOp_sec_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.oracleOp_sec_bas

/-- info: 'GateOptimalPrecision.oracleOp_dg_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.oracleOp_dg_bas

/-- info: 'GateOptimalPrecision.phaseGates_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.phaseGates_length

/-- info: 'GateOptimalPrecision.phaseGates_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.phaseGates_ok

/-- info: 'GateOptimalPrecision.gRun_phaseGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.gRun_phaseGates

/-- info: 'GateOptimalPrecision.oracleOp_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.oracleOp_nil

/-- info: 'GateOptimalPrecision.oracleOp_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.oracleOp_conj

/-- info: 'GateOptimalPrecision.run_privExpand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.run_privExpand

/-- info: 'GateOptimalPrecision.overwrite_anc_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.overwrite_anc_update

/-- info: 'GateOptimalPrecision.oracleOp_gate0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.oracleOp_gate0

/-- info: 'GateOptimalPrecision.eval_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eval_gate

/-- info: 'GateOptimalPrecision.eval_uj_sec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eval_uj_sec

/-- info: 'GateOptimalPrecision.eval_priv_sec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eval_priv_sec

/-- info: 'GateOptimalPrecision.oracleOp_sec_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.oracleOp_sec_comp

/-- info: 'GateOptimalPrecision.run_ujExpand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.run_ujExpand

/-- info: 'GateOptimalPrecision.run_expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.run_expand

/-- info: 'GateOptimalPrecision.expandI_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.expandI_counts

/-- info: 'GateOptimalPrecision.cons_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cons_counts

/-- info: 'GateOptimalPrecision.expand_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.expand_counts

/-- info: 'GateOptimalPrecision.expand_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.expand_valid

/-! ### The signed-factor gate circuit (`SignedCore`) -/

/-- info: 'GateOptimalPrecision.s0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.s0_pos

/-- info: 'GateOptimalPrecision.sigR_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sigR_spec

/-- info: 'GateOptimalPrecision.sigL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sigL

/-- info: 'GateOptimalPrecision.sigM_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sigM_spec

/-- info: 'GateOptimalPrecision.qM_le_sigN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.qM_le_sigN

/-- info: 'GateOptimalPrecision.one_le_sigN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.one_le_sigN

/-- info: 'GateOptimalPrecision.sigStep_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sigStep_nonneg

/-- info: 'GateOptimalPrecision.sig_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sig_unit

/-- info: 'GateOptimalPrecision.sigAmp_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sigAmp_valid

/-- info: 'GateOptimalPrecision.sigAmp_secOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sigAmp_secOK

/-- info: 'GateOptimalPrecision.sig_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sig_valid

/-- info: 'GateOptimalPrecision.sigBase_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sigBase_counts

/-- info: 'GateOptimalPrecision.sig_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sig_counts

/-- info: 'GateOptimalPrecision.sum_padded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sum_padded

/-- info: 'GateOptimalPrecision.sig_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sig_block

/-- info: 'GateOptimalPrecision.sigEta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sigEta_pos

/-- info: 'GateOptimalPrecision.sig_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sig_mesh

/-- info: 'GateOptimalPrecision.sig_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sig_core

/-! ### Proposition `gate:prop:signed` (`SignedTheorem`) -/

/-- info: 'GateOptimalPrecision.sg_params' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sg_params

/-- info: 'GateOptimalPrecision.sg_b_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sg_b_eq

/-- info: 'GateOptimalPrecision.sg_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sg_count_le

/-- info: 'GateOptimalPrecision.sig_gate_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sig_gate_bound

/-- info: 'GateOptimalPrecision.sigM_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sigM_le

/-- info: 'GateOptimalPrecision.err_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.err_inverse

/-! ### The large-sparsity core on a finer mesh (`ClippedCore`) -/

/-- info: 'GateOptimalPrecision.pointBound_mono_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.pointBound_mono_w

/-- info: 'GateOptimalPrecision.isoBound_mono_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.isoBound_mono_w

/-- info: 'GateOptimalPrecision.bulkBound_mono_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.bulkBound_mono_w

/-- info: 'GateOptimalPrecision.filter_estimate_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.filter_estimate_mesh

/-- info: 'GateOptimalPrecision.coreStep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.coreStep_spec

/-- info: 'GateOptimalPrecision.small_step_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.small_step_mesh

/-- info: 'GateOptimalPrecision.core_implementation_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.core_implementation_mesh

/-! ### Proposition `gate:prop:core` (`ClippedTheorem`) -/

/-- info: 'GateOptimalPrecision.clipM_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.clipM_spec

/-- info: 'GateOptimalPrecision.clipR_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.clipR_spec

/-- info: 'GateOptimalPrecision.clipL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.clipL

/-- info: 'GateOptimalPrecision.clipWt_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.clipWt_mass

/-- info: 'GateOptimalPrecision.clipLen_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.clipLen_spec

/-! ### The bounded-logarithm regime (`Bounded`) -/

/-- info: 'GateOptimalPrecision.isUnit_sub_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.isUnit_sub_I

/-- info: 'GateOptimalPrecision.isUnitary_of_star_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.isUnitary_of_star_mul_self

/-- info: 'GateOptimalPrecision.cayleyInv_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cayleyInv_right

/-- info: 'GateOptimalPrecision.cayleyInv_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cayleyInv_left

/-- info: 'GateOptimalPrecision.cayleyGate_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cayleyGate_isUnitary

/-- info: 'GateOptimalPrecision.bdGamma_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.bdGamma_spec

/-! ### The three regimes (`Combine`) -/

/-- info: 'GateOptimalPrecision.two_norm_params' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.two_norm_params

/-- info: 'GateOptimalPrecision.Qmu_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.Qmu_eq

/-- info: 'GateOptimalPrecision.Qmu_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.Qmu_nonneg

/-- info: 'GateOptimalPrecision.exp_rescale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.exp_rescale

/-- info: 'GateOptimalPrecision.err_rescale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.err_rescale

/-- info: 'GateOptimalPrecision.sqrt_le_one_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sqrt_le_one_add

/-- info: 'GateOptimalPrecision.tsteps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.tsteps_le

/-- info: 'GateOptimalPrecision.steps_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.steps_arith

/-- info: 'GateOptimalPrecision.clip_steps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.clip_steps_le

/-- info: 'GateOptimalPrecision.ite_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ite_counts

/-- info: 'GateOptimalPrecision.ite_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ite_valid

/-- info: 'GateOptimalPrecision.le_mul_X4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.le_mul_X4

/-- info: 'GateOptimalPrecision.bd_mesh_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.bd_mesh_le

/-- info: 'GateOptimalPrecision.bounded_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.bounded_branch

/-- info: 'GateOptimalPrecision.signed_params' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.signed_params

/-- info: 'GateOptimalPrecision.signed_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.signed_branch

/-- info: 'GateOptimalPrecision.clipped_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.clipped_branch

/-! ### Theorem `gate:thm:main` and its single-norm case (`Main`) -/

/-- info: 'GateOptimalPrecision.Qmu_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.Qmu_self

/-! ### The stable three-qubit factor (Section `gate:sec:native`) (`LocalFactor`) -/

/-- info: 'GateOptimalPrecision.eij_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eij_apply

/-- info: 'GateOptimalPrecision.sqrt2_inv_sq_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sqrt2_inv_sq_c

/-- info: 'GateOptimalPrecision.vMat_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.vMat_apply

/-- info: 'GateOptimalPrecision.piP_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.piP_eq

/-- info: 'GateOptimalPrecision.piM_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.piM_eq

/-- info: 'GateOptimalPrecision.piP_add_piM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.piP_add_piM

/-- info: 'GateOptimalPrecision.piP_mul_piP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.piP_mul_piP

/-- info: 'GateOptimalPrecision.piM_mul_piM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.piM_mul_piM

/-- info: 'GateOptimalPrecision.piP_mul_piM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.piP_mul_piM

/-- info: 'GateOptimalPrecision.piM_mul_piP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.piM_mul_piP

/-- info: 'GateOptimalPrecision.piP_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.piP_conjTranspose

/-- info: 'GateOptimalPrecision.piM_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.piM_conjTranspose

/-- info: 'GateOptimalPrecision.eMat_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eMat_eq

/-- info: 'GateOptimalPrecision.bP_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.bP_sq

/-- info: 'GateOptimalPrecision.bM_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.bM_sq

/-- info: 'GateOptimalPrecision.eij_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eij_conjTranspose

/-- info: 'GateOptimalPrecision.eij_add_eij' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eij_add_eij

/-- info: 'GateOptimalPrecision.xMat_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.xMat_mul_self

/-- info: 'GateOptimalPrecision.xMat_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.xMat_conjTranspose

/-- info: 'GateOptimalPrecision.xMat_mul_eij' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.xMat_mul_eij

/-- info: 'GateOptimalPrecision.jMat_mul_eij' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.jMat_mul_eij

/-- info: 'GateOptimalPrecision.jMat_conjTranspose_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.jMat_conjTranspose_mul_self

/-- info: 'GateOptimalPrecision.jMat_mul_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.jMat_mul_conjTranspose

/-- info: 'GateOptimalPrecision.vMat_mul_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.vMat_mul_conjTranspose

/-- info: 'GateOptimalPrecision.vMat_conjTranspose_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.vMat_conjTranspose_mul

/-- info: 'GateOptimalPrecision.sub_kronecker'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.sub_kronecker'

/-- info: 'GateOptimalPrecision.tMat_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.tMat_eq

/-- info: 'GateOptimalPrecision.tMat_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.tMat_mul_self

/-- info: 'GateOptimalPrecision.tMat_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.tMat_conjTranspose

/-- info: 'GateOptimalPrecision.aMat_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.aMat_conjTranspose

/-- info: 'GateOptimalPrecision.eR_ff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eR_ff

/-- info: 'GateOptimalPrecision.eR_ft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eR_ft

/-- info: 'GateOptimalPrecision.eR_tf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eR_tf

/-- info: 'GateOptimalPrecision.eR_tt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eR_tt

/-- info: 'GateOptimalPrecision.uMat_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.uMat_eq

/-- info: 'GateOptimalPrecision.rMat_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.rMat_unitary

/-- info: 'GateOptimalPrecision.aMat_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.aMat_mul_self

/-- info: 'GateOptimalPrecision.uMat_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.uMat_unitary

/-- info: 'GateOptimalPrecision.uMat_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.uMat_zero

/-- info: 'GateOptimalPrecision.tofMat_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.tofMat_conjTranspose

/-- info: 'GateOptimalPrecision.norm_one_kronecker_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_one_kronecker_le

/-- info: 'GateOptimalPrecision.norm_kronecker_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_kronecker_one_le

/-- info: 'GateOptimalPrecision.norm_kronecker_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_kronecker_le

/-- info: 'GateOptimalPrecision.jMat_kron_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.jMat_kron_unitary

/-- info: 'GateOptimalPrecision.self_le_sqrt_of_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.self_le_sqrt_of_le_one

/-- info: 'GateOptimalPrecision.kronecker_sub'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.kronecker_sub'

/-- info: 'GateOptimalPrecision.piP_sub_piP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.piP_sub_piP

/-- info: 'GateOptimalPrecision.piPM_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.piPM_unitary

/-- info: 'GateOptimalPrecision.norm_eMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_eMat

/-- info: 'GateOptimalPrecision.norm_xMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_xMat

/-- info: 'GateOptimalPrecision.norm_jMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_jMat

/-- info: 'GateOptimalPrecision.norm_tMat_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_tMat_sub_le

/-- info: 'GateOptimalPrecision.norm_uMat_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_uMat_sub_le

/-- info: 'GateOptimalPrecision.abs_sqrt_sub_sqrt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.abs_sqrt_sub_sqrt_le

/-! ### The joint private operation (Section `gate:sec:native`): clipping, Cayley and correction phases (`JointAlgebra`) -/

/-- info: 'GateOptimalPrecision.one_add_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.one_add_pos

/-- info: 'GateOptimalPrecision.clipE_add_corrE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.clipE_add_corrE

/-- info: 'GateOptimalPrecision.norm_corrE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_corrE

/-- info: 'GateOptimalPrecision.norm_corrE_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_corrE_le_one

/-- info: 'GateOptimalPrecision.norm_clipE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_clipE

/-- info: 'GateOptimalPrecision.norm_clipE_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_clipE_le

/-- info: 'GateOptimalPrecision.norm_bulk_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_bulk_le

/-- info: 'GateOptimalPrecision.mul_conj_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.mul_conj_norm

/-- info: 'GateOptimalPrecision.conj_mul_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.conj_mul_norm

/-- info: 'GateOptimalPrecision.one_add_norm_sq_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.one_add_norm_sq_ne

/-- info: 'GateOptimalPrecision.edgeMat_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.edgeMat_conjTranspose

/-- info: 'GateOptimalPrecision.edgeMat_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.edgeMat_unitary

/-- info: 'GateOptimalPrecision.edgeMat_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.edgeMat_zero

/-- info: 'GateOptimalPrecision.edgeMat_add_one_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.edgeMat_add_one_gram

/-- info: 'GateOptimalPrecision.norm_edgeMat_add_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_edgeMat_add_one_le

/-- info: 'GateOptimalPrecision.ofReal_add_I_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ofReal_add_I_ne

/-- info: 'GateOptimalPrecision.ofReal_sub_I_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ofReal_sub_I_ne

/-- info: 'GateOptimalPrecision.hMat_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.hMat_mul_self

/-- info: 'GateOptimalPrecision.hMat_xMat_hMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.hMat_xMat_hMat

/-- info: 'GateOptimalPrecision.edgeMat_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.edgeMat_real

/-- info: 'GateOptimalPrecision.one_add_sq_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.one_add_sq_eq

/-- info: 'GateOptimalPrecision.zetaP_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.zetaP_eq

/-- info: 'GateOptimalPrecision.zetaM_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.zetaM_eq

/-- info: 'GateOptimalPrecision.failure_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.failure_phase

/-! ### Three-qubit blocks on the gate register (`BlockOp`) -/

/-- info: 'GateOptimalPrecision.matOp_zero'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.matOp_zero'

/-- info: 'GateOptimalPrecision.matOp_add'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.matOp_add'

/-- info: 'GateOptimalPrecision.matOp_sub'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.matOp_sub'

/-- info: 'GateOptimalPrecision.matOp_smul'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.matOp_smul'

/-- info: 'GateOptimalPrecision.matOp_sum'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.matOp_sum'

/-- info: 'GateOptimalPrecision.norm_matOp_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_matOp_sq

/-- info: 'GateOptimalPrecision.norm_matOp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_matOp_le

/-- info: 'GateOptimalPrecision.blk_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.blk_mul

/-- info: 'GateOptimalPrecision.blk_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.blk_one

/-- info: 'GateOptimalPrecision.blk_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.blk_conjTranspose

/-- info: 'GateOptimalPrecision.blk_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.blk_sub

/-- info: 'GateOptimalPrecision.norm_matOp_blk_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_matOp_blk_le

/-- info: 'GateOptimalPrecision.matOp_bas'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.matOp_bas'

/-- info: 'GateOptimalPrecision.matOp_blk_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.matOp_blk_bas

/-- info: 'GateOptimalPrecision.eQ_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eQ_symm_apply

/-- info: 'GateOptimalPrecision.eQ_symm_update0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eQ_symm_update0

/-- info: 'GateOptimalPrecision.eQ_symm_update1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eQ_symm_update1

/-- info: 'GateOptimalPrecision.ext_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ext_bas

/-- info: 'GateOptimalPrecision.condOp_zero_eq_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.condOp_zero_eq_blk

/-- info: 'GateOptimalPrecision.condOp_one_eq_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.condOp_one_eq_blk

/-- info: 'GateOptimalPrecision.gateOp_tof_eq_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.gateOp_tof_eq_blk

/-- info: 'GateOptimalPrecision.condOp_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.condOp_outer

/-! ### The gates of the local factor (`LocalGates`) -/

/-- info: 'GateOptimalPrecision.alphaVal_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.alphaVal_nonneg

/-- info: 'GateOptimalPrecision.alphaVal_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.alphaVal_le

/-- info: 'GateOptimalPrecision.phMat_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.phMat_mul

/-- info: 'GateOptimalPrecision.phMat_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.phMat_zero

/-- info: 'GateOptimalPrecision.phMat_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.phMat_conjTranspose

/-- info: 'GateOptimalPrecision.phMat_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.phMat_unitary

/-- info: 'GateOptimalPrecision.rot2_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.rot2_mul

/-- info: 'GateOptimalPrecision.rot2_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.rot2_zero

/-- info: 'GateOptimalPrecision.rot2_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.rot2_conjTranspose

/-- info: 'GateOptimalPrecision.rot2_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.rot2_unitary

/-- info: 'GateOptimalPrecision.rot2_eq_rMat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.rot2_eq_rMat

/-- info: 'GateOptimalPrecision.hMat_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.hMat_conjTranspose

/-- info: 'GateOptimalPrecision.hMat_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.hMat_unitary

/-- info: 'GateOptimalPrecision.eij_ff_mul_ff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eij_ff_mul_ff

/-- info: 'GateOptimalPrecision.eij_tt_mul_tt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eij_tt_mul_tt

/-- info: 'GateOptimalPrecision.eij_ff_mul_tt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eij_ff_mul_tt

/-- info: 'GateOptimalPrecision.eij_tt_mul_ff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eij_tt_mul_ff

/-- info: 'GateOptimalPrecision.cnotMat_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cnotMat_mul_self

/-- info: 'GateOptimalPrecision.tofMat_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.tofMat_mul_self

/-- info: 'GateOptimalPrecision.kron_mid_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.kron_mid_mul

/-- info: 'GateOptimalPrecision.norm_cImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_cImpl

/-- info: 'GateOptimalPrecision.phase_cImpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.phase_cImpl

/-- info: 'GateOptimalPrecision.cImpl_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cImpl_zero

/-- info: 'GateOptimalPrecision.norm_uMat_sub_le_of_accuracy'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.norm_uMat_sub_le_of_accuracy'

/-- info: 'GateOptimalPrecision.locGates_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.locGates_length

/-- info: 'GateOptimalPrecision.locGates_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.locGates_ok

/-- info: 'GateOptimalPrecision.selProd_ph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.selProd_ph

/-- info: 'GateOptimalPrecision.selProd_ry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.selProd_ry

/-- info: 'GateOptimalPrecision.gRun_phGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.gRun_phGates

/-- info: 'GateOptimalPrecision.gRun_ryGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.gRun_ryGates

/-- info: 'GateOptimalPrecision.gRun_phGates_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.gRun_phGates_blk

/-- info: 'GateOptimalPrecision.gRun_ryGates_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.gRun_ryGates_blk

/-- info: 'GateOptimalPrecision.hGate_op_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.hGate_op_blk

/-- info: 'GateOptimalPrecision.tofGate_op_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.tofGate_op_blk

/-! ### Native macros for sector-controlled private calls (`NativeCayley`) -/

/-- info: 'GateOptimalPrecision.secOK_simCircuit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.secOK_simCircuit

/-- info: 'GateOptimalPrecision.secOK_bdSigned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.secOK_bdSigned

/-- info: 'GateOptimalPrecision.secOK_clipSigned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.secOK_clipSigned

/-! ### The native factor (`NativeFactor`) -/

/-- info: 'GateOptimalPrecision.put_eq_sum_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.put_eq_sum_bas

/-- info: 'GateOptimalPrecision.cleanA_overwrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cleanA_overwrite

/-- info: 'GateOptimalPrecision.arOut_overwrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.arOut_overwrite

/-- info: 'GateOptimalPrecision.arith_block_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.arith_block_agrees

/-- info: 'GateOptimalPrecision.FactorOp.locB_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.FactorOp.locB_injective

/-- info: 'GateOptimalPrecision.FactorOp.locW_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.FactorOp.locW_injective

/-- info: 'GateOptimalPrecision.factorMacro_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.factorMacro_nGates

/-- info: 'GateOptimalPrecision.factorMacro_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.factorMacro_nCalls

/-- info: 'GateOptimalPrecision.locW_ne_twW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.locW_ne_twW

/-- info: 'GateOptimalPrecision.locW_ne_pwW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.locW_ne_pwW

/-- info: 'GateOptimalPrecision.factorMacro_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.factorMacro_valid

/-- info: 'GateOptimalPrecision.arith_loc_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.arith_loc_agrees

/-- info: 'GateOptimalPrecision.Util_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.Util_approx

/-- info: 'GateOptimalPrecision.Uid_eq_localOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.Uid_eq_localOp

/-- info: 'GateOptimalPrecision.agrees_of_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.agrees_of_native

/-- info: 'GateOptimalPrecision.factor_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.factor_agrees

/-- info: 'GateOptimalPrecision.uncIdeal_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.uncIdeal_adjoint

/-! ### The native signed-factor circuit (`NativeSigned`) -/

/-- info: 'GateOptimalPrecision.fmacro_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.fmacro_nCalls

/-- info: 'GateOptimalPrecision.fcirc_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.fcirc_nCalls

/-- info: 'GateOptimalPrecision.fmacro_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.fmacro_nGates

/-- info: 'GateOptimalPrecision.fcirc_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.fcirc_nGates

/-- info: 'GateOptimalPrecision.fmacro_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.fmacro_valid

/-- info: 'GateOptimalPrecision.fcirc_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.fcirc_valid

/-- info: 'GateOptimalPrecision.evalF_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.evalF_isUnitary

/-- info: 'GateOptimalPrecision.evalF_wire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.evalF_wire

/-- info: 'GateOptimalPrecision.prodOps_evalF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.prodOps_evalF

/-- info: 'GateOptimalPrecision.liftB_conj_unc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.liftB_conj_unc

/-- info: 'GateOptimalPrecision.fmacro_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.fmacro_approx

/-- info: 'GateOptimalPrecision.fcirc_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.fcirc_approx

/-- info: 'GateOptimalPrecision.fcirc_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.fcirc_error

/-- info: 'GateOptimalPrecision.uncOK_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.uncOK_inv

/-- info: 'GateOptimalPrecision.uncOK_invList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.uncOK_invList

/-- info: 'GateOptimalPrecision.uncOK_expandI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.uncOK_expandI

/-- info: 'GateOptimalPrecision.uncOK_sigCircuit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.uncOK_sigCircuit

/-- info: 'GateOptimalPrecision.uncOK_sgCircuit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.uncOK_sgCircuit

/-- info: 'GateOptimalPrecision.shiftG_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.shiftG_length

/-- info: 'GateOptimalPrecision.shiftG_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.shiftG_ok

/-- info: 'GateOptimalPrecision.UJop_shiftG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.UJop_shiftG

/-! ### Theorem `gate:thm:main` and its single-norm case with native private calls (`NativeMain`) -/

/-- info: 'GateOptimalPrecision.NativeClaims.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.NativeClaims.mono

/-- info: 'GateOptimalPrecision.NativeClaims.weaken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.NativeClaims.weaken

/-- info: 'GateOptimalPrecision.rval_half_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.rval_half_le

/-- info: 'GateOptimalPrecision.Qmu_half_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.Qmu_half_le

/-- info: 'GateOptimalPrecision.Qone_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.Qone_nonneg

/-- info: 'GateOptimalPrecision.Qone_half_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.Qone_half_le

/-! ### Controls on native locators (Section `gate:sec:native`) (`ControlledLocator`) -/

/-- info: 'GateOptimalPrecision.card_LocW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.card_LocW

/-- info: 'GateOptimalPrecision.length_flatMap_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.length_flatMap_le

/-- info: 'GateOptimalPrecision.length_copyG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.length_copyG

/-- info: 'GateOptimalPrecision.length_swapG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.length_swapG

/-- info: 'GateOptimalPrecision.length_xorG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.length_xorG

/-- info: 'GateOptimalPrecision.nCallsN_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.nCallsN_call

/-- info: 'GateOptimalPrecision.nGatesN_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.nGatesN_call

/-- info: 'GateOptimalPrecision.ctrlLoc_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ctrlLoc_nCalls

/-- info: 'GateOptimalPrecision.ctrlLoc_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ctrlLoc_nGates

/-- info: 'GateOptimalPrecision.cx_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cx_ok

/-- info: 'GateOptimalPrecision.copyG_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.copyG_ok

/-- info: 'GateOptimalPrecision.swapG_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.swapG_ok

/-- info: 'GateOptimalPrecision.xorG_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.xorG_ok

/-- info: 'GateOptimalPrecision.ctrlLoc_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ctrlLoc_valid

/-- info: 'GateOptimalPrecision.cfgRun_apply_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cfgRun_apply_of_ne

/-- info: 'GateOptimalPrecision.cfgRun_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cfgRun_out

/-- info: 'GateOptimalPrecision.cfgRun_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cfgRun_agree

/-- info: 'GateOptimalPrecision.cfgRun_flatMap_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cfgRun_flatMap_some

/-- info: 'GateOptimalPrecision.cfgRun_flatMap_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cfgRun_flatMap_ctl

/-- info: 'GateOptimalPrecision.localTo_copy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.localTo_copy

/-- info: 'GateOptimalPrecision.localTo_xor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.localTo_xor

/-- info: 'GateOptimalPrecision.localTo_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.localTo_swap

/-- info: 'GateOptimalPrecision.cfgRun_copyG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cfgRun_copyG

/-- info: 'GateOptimalPrecision.cfgRun_xorG_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cfgRun_xorG_nil

/-- info: 'GateOptimalPrecision.cfgRun_xorG_ctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cfgRun_xorG_ctl

/-- info: 'GateOptimalPrecision.cfgRun_swapG_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cfgRun_swapG_true

/-- info: 'GateOptimalPrecision.cfgRun_swapG_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cfgRun_swapG_false

/-- info: 'GateOptimalPrecision.classical_of_cx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.classical_of_cx

/-- info: 'GateOptimalPrecision.copyG_classical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.copyG_classical

/-- info: 'GateOptimalPrecision.swapG_classical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.swapG_classical

/-- info: 'GateOptimalPrecision.xorG_classical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.xorG_classical

/-- info: 'GateOptimalPrecision.length_setG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.length_setG

/-- info: 'GateOptimalPrecision.setG_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.setG_ok

/-- info: 'GateOptimalPrecision.setG_classical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.setG_classical

/-- info: 'GateOptimalPrecision.localTo_set' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.localTo_set

/-- info: 'GateOptimalPrecision.cfgRun_setG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cfgRun_setG

/-- info: 'GateOptimalPrecision.cfgRun_setG_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cfgRun_setG_zero

/-- info: 'GateOptimalPrecision.cfgRun_setG_xs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.cfgRun_setG_xs

/-- info: 'GateOptimalPrecision.ctrlLoc0_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ctrlLoc0_nCalls

/-- info: 'GateOptimalPrecision.ctrlLoc0_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ctrlLoc0_nGates

/-- info: 'GateOptimalPrecision.ctrlLoc0_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ctrlLoc0_valid

/-- info: 'GateOptimalPrecision.put_add'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.put_add'

/-- info: 'GateOptimalPrecision.put_zero'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.put_zero'

/-- info: 'GateOptimalPrecision.put_finset_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.put_finset_sum

/-- info: 'GateOptimalPrecision.put_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.put_ref

/-- info: 'GateOptimalPrecision.put_tgt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.put_tgt

/-- info: 'GateOptimalPrecision.put_tgt_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.put_tgt_sum

/-- info: 'GateOptimalPrecision.eval_call_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eval_call_ref

/-- info: 'GateOptimalPrecision.eval_call_tgt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eval_call_tgt

/-- info: 'GateOptimalPrecision.ctrlU_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ctrlU_bas

/-- info: 'GateOptimalPrecision.adj_loc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.adj_loc

/-- info: 'GateOptimalPrecision.nrun_prepL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.nrun_prepL

/-- info: 'GateOptimalPrecision.xor_false_left' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.xor_false_left

/-- info: 'GateOptimalPrecision.xor_self'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.xor_self'

/-- info: 'GateOptimalPrecision.nrun_tail_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.nrun_tail_true

/-- info: 'GateOptimalPrecision.ctrlLoc_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ctrlLoc_bas

/-- info: 'GateOptimalPrecision.eq_mk_of_clean' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eq_mk_of_clean

/-- info: 'GateOptimalPrecision.ctrlU_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ctrlU_isUnitary

/-- info: 'GateOptimalPrecision.ctrlU_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.ctrlU_adjoint

/-- info: 'GateOptimalPrecision.preserves_ctrlU' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.preserves_ctrlU

/-- info: 'GateOptimalPrecision.eq_mk_of_zero' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.eq_mk_of_zero

/-- info: 'GateOptimalPrecision.preserves_ctrlU0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GateOptimalPrecision.preserves_ctrlU0
