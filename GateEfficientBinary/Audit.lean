import GateEfficientBinary.Reversible.Basic
import GateEfficientBinary.Reversible.Adder
import GateEfficientBinary.Reversible.Program
import GateEfficientBinary.Reversible.TwosComp
import GateEfficientBinary.Cordic.Real
import GateEfficientBinary.Cordic.Integer
import GateEfficientBinary.Cordic.Program
import GateEfficientBinary.Cordic.Semantics
import GateEfficientBinary.Cordic.Error
import GateEfficientBinary.Cordic.Params
import GateEfficientBinary.Reversible.Rename
import GateEfficientBinary.Cordic.Arith
import GateEfficientBinary.Sparse.Lift
import GateEfficientBinary.Sparse.Layout
import GateEfficientBinary.Sparse.Gadget
import GateEfficientBinary.Sparse.Oracles
import GateEfficientBinary.Sparse.Native
import GateEfficientBinary.Sparse.Boundary
import GateEfficientBinary.Sparse.LiftNorm
import GateEfficientBinary.Sparse.Simulation
import GateEfficientBinary.Sparse.Budget

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 148 lemmas, whose reports list a
strict subset of these three axioms (26 of them none). The audits cover every theorem
of the library of the gate-level construction from binary data, beginning with
Theorem `hs:thm:gates` for binary sparse oracles.
-/

/-! ### Theorem `hs:thm:gates` from binary data -/

/-- info: 'SparseHamiltonian.GateBinary.binary_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.binary_simulation

/-- info: 'SparseHamiltonian.GateBinary.binary_simulation_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.binary_simulation_budget

/-- info: 'SparseHamiltonian.GateBinary.qlift_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.qlift_smul

/-- info: 'SparseHamiltonian.GateBinary.qlift_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.qlift_add

/-- info: 'SparseHamiltonian.GateBinary.qlift_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.qlift_sub

/-- info: 'SparseHamiltonian.GateBinary.qlift_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.qlift_star

/-- info: 'SparseHamiltonian.GateBinary.elift_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.elift_comp

/-- info: 'SparseHamiltonian.GateBinary.elift_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.elift_one

/-- info: 'SparseHamiltonian.GateBinary.elift_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.elift_sub

/-- info: 'SparseHamiltonian.GateBinary.elift_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.elift_adjoint

/-- info: 'SparseHamiltonian.GateBinary.norm_elift_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.norm_elift_le

/-- info: 'SparseHamiltonian.GateBinary.elift_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.elift_isUnitary

/-- info: 'SparseHamiltonian.GateBinary.orientedAction_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.orientedAction_isUnitary

/-- info: 'SparseHamiltonian.GateBinary.fixedAction_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.fixedAction_isUnitary

/-- info: 'SparseHamiltonian.GateBinary.Dbin_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Dbin_isUnitary

/-- info: 'SparseHamiltonian.GateBinary.one_sub_Dbin_R1bin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.one_sub_Dbin_R1bin

/-- info: 'SparseHamiltonian.GateBinary.R1bin_one_sub_Dbin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.R1bin_one_sub_Dbin

/-- info: 'SparseHamiltonian.GateBinary.norm_R1bin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.norm_R1bin_le

/-- info: 'SparseHamiltonian.GateBinary.Hbin_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Hbin_self

/-- info: 'SparseHamiltonian.GateBinary.norm_Hbin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.norm_Hbin_le

/-- info: 'SparseHamiltonian.GateBinary.R1bin_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.R1bin_boundary

/-- info: 'SparseHamiltonian.GateBinary.adjoint_comp_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.adjoint_comp_comp

/-- info: 'SparseHamiltonian.GateBinary.R1bin_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.R1bin_endpoint

/-- info: 'SparseHamiltonian.GateBinary.Hbin_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Hbin_exponent

/-- info: 'SparseHamiltonian.GateBinary.card_SZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.card_SZ

/-! ### The native identity from binary sparse oracles -/

/-- info: 'SparseHamiltonian.GateBinary.nativeOK_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.nativeOK_of

/-- info: 'SparseHamiltonian.GateBinary.liftE_action' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.liftE_action

/-- info: 'SparseHamiltonian.GateBinary.sparse_nativeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.sparse_nativeOK

/-- info: 'SparseHamiltonian.GateBinary.xorEquiv_inl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.xorEquiv_inl

/-- info: 'SparseHamiltonian.GateBinary.xorEquiv_inr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.xorEquiv_inr

/-- info: 'SparseHamiltonian.GateBinary.xorEquiv_symm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.xorEquiv_symm

/-- info: 'SparseHamiltonian.GateBinary.comp_overwrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.comp_overwrite

/-- info: 'SparseHamiltonian.GateBinary.overwrite_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.overwrite_self

/-- info: 'SparseHamiltonian.GateBinary.overwrite_update_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.overwrite_update_out

/-- info: 'SparseHamiltonian.GateBinary.permOp_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.permOp_bas

/-- info: 'SparseHamiltonian.GateBinary.localOp_permOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.localOp_permOp

/-- info: 'SparseHamiltonian.GateBinary.ext_bas_clm'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ext_bas_clm'

/-- info: 'SparseHamiltonian.GateBinary.cleanEmb_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cleanEmb_bas

/-- info: 'SparseHamiltonian.GateBinary.liftB_comm_xor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.liftB_comm_xor

/-- info: 'SparseHamiltonian.GateBinary.tB_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.tB_injective

/-- info: 'SparseHamiltonian.GateBinary.dmB_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.dmB_injective

/-- info: 'SparseHamiltonian.GateBinary.rrB_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.rrB_injective

/-- info: 'SparseHamiltonian.GateBinary.rcB_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.rcB_injective

/-- info: 'SparseHamiltonian.GateBinary.vB_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.vB_injective

/-- info: 'SparseHamiltonian.GateBinary.tB_ne_oB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.tB_ne_oB

/-- info: 'SparseHamiltonian.GateBinary.tB_ne_dmB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.tB_ne_dmB

/-- info: 'SparseHamiltonian.GateBinary.tB_ne_rrB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.tB_ne_rrB

/-- info: 'SparseHamiltonian.GateBinary.tB_ne_rcB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.tB_ne_rcB

/-- info: 'SparseHamiltonian.GateBinary.tB_ne_vB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.tB_ne_vB

/-- info: 'SparseHamiltonian.GateBinary.dmB_ne_oB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.dmB_ne_oB

/-- info: 'SparseHamiltonian.GateBinary.rrB_ne_oB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.rrB_ne_oB

/-- info: 'SparseHamiltonian.GateBinary.rcB_ne_oB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.rcB_ne_oB

/-- info: 'SparseHamiltonian.GateBinary.vB_ne_oB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.vB_ne_oB

/-- info: 'SparseHamiltonian.GateBinary.dmB_ne_rrB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.dmB_ne_rrB

/-- info: 'SparseHamiltonian.GateBinary.dmB_ne_rcB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.dmB_ne_rcB

/-- info: 'SparseHamiltonian.GateBinary.rrB_ne_rcB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.rrB_ne_rcB

/-- info: 'SparseHamiltonian.GateBinary.rrB_ne_vB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.rrB_ne_vB

/-- info: 'SparseHamiltonian.GateBinary.rcB_ne_vB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.rcB_ne_vB

/-- info: 'SparseHamiltonian.GateBinary.dmB_ne_vB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.dmB_ne_vB

/-- info: 'SparseHamiltonian.GateBinary.bw_ext' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.bw_ext

/-- info: 'SparseHamiltonian.GateBinary.xorEquiv_update_inl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.xorEquiv_update_inl

/-- info: 'SparseHamiltonian.GateBinary.alongEquiv_apply_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.alongEquiv_apply_in

/-- info: 'SparseHamiltonian.GateBinary.alongEquiv_apply_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.alongEquiv_apply_out

/-- info: 'SparseHamiltonian.GateBinary.alongEquiv_update_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.alongEquiv_update_out

/-- info: 'SparseHamiltonian.GateBinary.prims_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.prims_row

/-- info: 'SparseHamiltonian.GateBinary.prims_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.prims_col

/-- info: 'SparseHamiltonian.GateBinary.prims_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.prims_val

/-- info: 'SparseHamiltonian.GateBinary.prims_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.prims_isUnitary

/-- info: 'SparseHamiltonian.GateBinary.computeV_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.computeV_valid

/-- info: 'SparseHamiltonian.GateBinary.twos_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.twos_update

/-- info: 'SparseHamiltonian.GateBinary.sparseOp_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.sparseOp_public

/-- info: 'SparseHamiltonian.GateBinary.computeV_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.computeV_nGates

/-- info: 'SparseHamiltonian.GateBinary.computeV_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.computeV_nCalls

/-- info: 'SparseHamiltonian.GateBinary.phiE_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.phiE_zero

/-- info: 'SparseHamiltonian.GateBinary.qlift_bas_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.qlift_bas_single

/-- info: 'SparseHamiltonian.GateBinary.row_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.row_zero

/-- info: 'SparseHamiltonian.GateBinary.col_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.col_zero

/-- info: 'SparseHamiltonian.GateBinary.eval_call_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.eval_call_edge

/-- info: 'SparseHamiltonian.GateBinary.localOp_bas_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.localOp_bas_clean

/-- info: 'SparseHamiltonian.GateBinary.refs_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.refs_cleanEmb

/-- info: 'SparseHamiltonian.GateBinary.gadgets_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.gadgets_agree

/-- info: 'SparseHamiltonian.GateBinary.Lfull_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Lfull_eq

/-- info: 'SparseHamiltonian.GateBinary.supp_sigRef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.supp_sigRef

/-- info: 'SparseHamiltonian.GateBinary.compute_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.compute_cleanEmb

/-- info: 'SparseHamiltonian.GateBinary.liftE_condOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.liftE_condOp

/-- info: 'SparseHamiltonian.GateBinary.Aq_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Aq_eq

/-- info: 'SparseHamiltonian.GateBinary.posT_ne_oB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.posT_ne_oB

/-- info: 'SparseHamiltonian.GateBinary.sigma_oB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.sigma_oB

/-- info: 'SparseHamiltonian.GateBinary.sigma_update_oB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.sigma_update_oB

/-- info: 'SparseHamiltonian.GateBinary.sigma_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.sigma_val

/-- info: 'SparseHamiltonian.GateBinary.rdec_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.rdec_sigma

/-- info: 'SparseHamiltonian.GateBinary.cfgRun_fredkinG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cfgRun_fredkinG

/-- info: 'SparseHamiltonian.GateBinary.fredkinG_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.fredkinG_target

/-- info: 'SparseHamiltonian.GateBinary.cfgRun_swapList_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cfgRun_swapList_out

/-- info: 'SparseHamiltonian.GateBinary.cfgRun_swapList_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cfgRun_swapList_of_ne

/-- info: 'SparseHamiltonian.GateBinary.cfgRun_swapList_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cfgRun_swapList_eq

/-- info: 'SparseHamiltonian.GateBinary.cfgRun_cswapG_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cfgRun_cswapG_out

/-- info: 'SparseHamiltonian.GateBinary.cfgRun_cswapG_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cfgRun_cswapG_of_ne

/-- info: 'SparseHamiltonian.GateBinary.cfgRun_cswapG_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cfgRun_cswapG_T

/-- info: 'SparseHamiltonian.GateBinary.cfgRun_cswapG_Dm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cfgRun_cswapG_Dm

/-- info: 'SparseHamiltonian.GateBinary.cfgRun_xorList_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cfgRun_xorList_out

/-- info: 'SparseHamiltonian.GateBinary.cfgRun_xorList_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cfgRun_xorList_of_ne

/-- info: 'SparseHamiltonian.GateBinary.cfgRun_xorList_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cfgRun_xorList_eq

/-- info: 'SparseHamiltonian.GateBinary.cfgRun_cxorG_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cfgRun_cxorG_out

/-- info: 'SparseHamiltonian.GateBinary.cfgRun_cxorG_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cfgRun_cxorG_of_ne

/-- info: 'SparseHamiltonian.GateBinary.cfgRun_cxorG_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cfgRun_cxorG_T

/-- info: 'SparseHamiltonian.GateBinary.cnot_of_mem_cswapG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cnot_of_mem_cswapG

/-- info: 'SparseHamiltonian.GateBinary.cnot_of_mem_cxorG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cnot_of_mem_cxorG

/-- info: 'SparseHamiltonian.GateBinary.classical_cswapG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.classical_cswapG

/-- info: 'SparseHamiltonian.GateBinary.classical_cxorG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.classical_cxorG

/-- info: 'SparseHamiltonian.GateBinary.gateOK_cswapG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.gateOK_cswapG

/-- info: 'SparseHamiltonian.GateBinary.gateOK_cxorG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.gateOK_cxorG

/-- info: 'SparseHamiltonian.GateBinary.length_cswapG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.length_cswapG

/-- info: 'SparseHamiltonian.GateBinary.length_cxorG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.length_cxorG

/-- info: 'SparseHamiltonian.GateBinary.cfgRun_gadget_inactive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cfgRun_gadget_inactive

/-- info: 'SparseHamiltonian.GateBinary.agrees_one_of_cfgRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.agrees_one_of_cfgRun

/-- info: 'SparseHamiltonian.GateBinary.supp_put_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.supp_put_out

/-- info: 'SparseHamiltonian.GateBinary.gadget_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.gadget_agrees

/-- info: 'SparseHamiltonian.GateBinary.gadget_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.gadget_preserves

/-- info: 'SparseHamiltonian.GateBinary.gadget_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.gadget_valid

/-- info: 'SparseHamiltonian.GateBinary.gadget_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.gadget_nGates

/-- info: 'SparseHamiltonian.GateBinary.gadget_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.gadget_nCalls

/-! ### The boundary preparation from Hadamard gates -/

/-- info: 'SparseHamiltonian.GateBinary.hadC_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.hadC_false

/-- info: 'SparseHamiltonian.GateBinary.hadGate_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.hadGate_ok

/-- info: 'SparseHamiltonian.GateBinary.hadGate_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.hadGate_bas

/-- info: 'SparseHamiltonian.GateBinary.gRun_hadList_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.gRun_hadList_bas

/-- info: 'SparseHamiltonian.GateBinary.slotWire_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.slotWire_injective

/-- info: 'SparseHamiltonian.GateBinary.hadWires_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.hadWires_nodup

/-- info: 'SparseHamiltonian.GateBinary.hadUJ_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.hadUJ_ok

/-- info: 'SparseHamiltonian.GateBinary.hadUJ_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.hadUJ_length

/-- info: 'SparseHamiltonian.GateBinary.mem_hadWires' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.mem_hadWires

/-- info: 'SparseHamiltonian.GateBinary.exists_lowWord_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.exists_lowWord_iff

/-- info: 'SparseHamiltonian.GateBinary.embQ_apply_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.embQ_apply_inl

/-- info: 'SparseHamiltonian.GateBinary.embQ_apply_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.embQ_apply_inr

/-- info: 'SparseHamiltonian.GateBinary.embQ_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.embQ_single

/-- info: 'SparseHamiltonian.GateBinary.embQ_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.embQ_adjoint_apply

/-- info: 'SparseHamiltonian.GateBinary.embQ_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.embQ_isometry

/-- info: 'SparseHamiltonian.GateBinary.fixedBoundary_single_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.fixedBoundary_single_inl

/-- info: 'SparseHamiltonian.GateBinary.fixedBoundary_single_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.fixedBoundary_single_inr

/-- info: 'SparseHamiltonian.GateBinary.iota0_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.iota0_bas

/-- info: 'SparseHamiltonian.GateBinary.fl_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.fl_bas

/-- info: 'SparseHamiltonian.GateBinary.phiPR_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.phiPR_zero

/-- info: 'SparseHamiltonian.GateBinary.iota0_unconj_qlift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.iota0_unconj_qlift

/-- info: 'SparseHamiltonian.GateBinary.bdryP_embQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.bdryP_embQ

/-- info: 'SparseHamiltonian.GateBinary.embQ_adjoint_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.embQ_adjoint_single

/-- info: 'SparseHamiltonian.GateBinary.off_hadWires_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.off_hadWires_iff

/-- info: 'SparseHamiltonian.GateBinary.hamp_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.hamp_pow

/-- info: 'SparseHamiltonian.GateBinary.hadUJ_iota0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.hadUJ_iota0

/-- info: 'SparseHamiltonian.GateBinary.hadUJ_iota0_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.hadUJ_iota0_adjoint

/-- info: 'SparseHamiltonian.GateBinary.unconj_qlift_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.unconj_qlift_sandwich

/-- info: 'SparseHamiltonian.GateBinary.iota0_bdryP_compress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.iota0_bdryP_compress

/-- info: 'SparseHamiltonian.GateBinary.boundary_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.boundary_lift

/-! ### Qubit lifts of edge operators -/

/-- info: 'SparseHamiltonian.GateBinary.euclid_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.euclid_eq_sum

/-- info: 'SparseHamiltonian.GateBinary.toMat_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.toMat_comp

/-- info: 'SparseHamiltonian.GateBinary.toMat_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.toMat_one

/-- info: 'SparseHamiltonian.GateBinary.toMat_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.toMat_adjoint

/-- info: 'SparseHamiltonian.GateBinary.toMat_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.toMat_add

/-- info: 'SparseHamiltonian.GateBinary.toMat_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.toMat_smul

/-- info: 'SparseHamiltonian.GateBinary.matOp_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.matOp_add

/-- info: 'SparseHamiltonian.GateBinary.matOp_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.matOp_smul

/-- info: 'SparseHamiltonian.GateBinary.qlift_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.qlift_eq

/-- info: 'SparseHamiltonian.GateBinary.qlift_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.qlift_comp

/-- info: 'SparseHamiltonian.GateBinary.qlift_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.qlift_one

/-- info: 'SparseHamiltonian.GateBinary.qlift_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.qlift_adjoint

/-- info: 'SparseHamiltonian.GateBinary.qlift_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.qlift_isUnitary

/-- info: 'SparseHamiltonian.GateBinary.qlift_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.qlift_bas

/-- info: 'SparseHamiltonian.GateBinary.norm_qlift_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.norm_qlift_le

/-- info: 'SparseHamiltonian.GateBinary.ixPR_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ixPR_injective

/-- info: 'SparseHamiltonian.GateBinary.ixPR_ne_o' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ixPR_ne_o

/-- info: 'SparseHamiltonian.GateBinary.mkPR_o' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.mkPR_o

/-- info: 'SparseHamiltonian.GateBinary.mkPR_ix' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.mkPR_ix

/-- info: 'SparseHamiltonian.GateBinary.mkPR_eta' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.mkPR_eta

/-- info: 'SparseHamiltonian.GateBinary.mkPR_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.mkPR_eq_iff

/-- info: 'SparseHamiltonian.GateBinary.overwrite_ixPR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.overwrite_ixPR

/-- info: 'SparseHamiltonian.GateBinary.update_oPR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.update_oPR

/-- info: 'SparseHamiltonian.GateBinary.phiE_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.phiE_apply

/-- info: 'SparseHamiltonian.GateBinary.phiPR_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.phiPR_apply

/-- info: 'SparseHamiltonian.GateBinary.qlift_bas_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.qlift_bas_apply

/-- info: 'SparseHamiltonian.GateBinary.slice_ixPR_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.slice_ixPR_bas

/-- info: 'SparseHamiltonian.GateBinary.leftPart_single_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.leftPart_single_inl

/-- info: 'SparseHamiltonian.GateBinary.leftPart_single_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.leftPart_single_inr

/-- info: 'SparseHamiltonian.GateBinary.rightPart_single_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.rightPart_single_inl

/-- info: 'SparseHamiltonian.GateBinary.rightPart_single_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.rightPart_single_inr

/-- info: 'SparseHamiltonian.GateBinary.qlift_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.qlift_block

/-- info: 'SparseHamiltonian.GateBinary.regroup_single_phiPR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.regroup_single_phiPR

/-- info: 'SparseHamiltonian.GateBinary.qlift_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.qlift_lift

/-- info: 'SparseHamiltonian.GateBinary.qmat_action' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.qmat_action

/-- info: 'SparseHamiltonian.GateBinary.conj_unconj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.conj_unconj

/-- info: 'SparseHamiltonian.GateBinary.unconj_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.unconj_comp

/-- info: 'SparseHamiltonian.GateBinary.unconj_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.unconj_one

/-- info: 'SparseHamiltonian.GateBinary.unconj_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.unconj_sub

/-- info: 'SparseHamiltonian.GateBinary.unconj_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.unconj_adjoint

/-- info: 'SparseHamiltonian.GateBinary.unconj_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.unconj_isUnitary

/-- info: 'SparseHamiltonian.GateBinary.norm_unconj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.norm_unconj_apply

/-- info: 'SparseHamiltonian.GateBinary.norm_unconj_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.norm_unconj_le

/-- info: 'SparseHamiltonian.GateBinary.liftE_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.liftE_comp

/-- info: 'SparseHamiltonian.GateBinary.liftE_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.liftE_adjoint

/-- info: 'SparseHamiltonian.GateBinary.liftE_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.liftE_isUnitary

/-- info: 'SparseHamiltonian.GateBinary.selOp_unconj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.selOp_unconj

/-! ### The CORDIC angle arithmetic -/

/-- info: 'SparseHamiltonian.GateBinary.cfgRun_map_toGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cfgRun_map_toGate

/-- info: 'SparseHamiltonian.GateBinary.classical_map_toGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.classical_map_toGate

/-- info: 'SparseHamiltonian.GateBinary.embW_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.embW_injective

/-- info: 'SparseHamiltonian.GateBinary.embW_ne_tWire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.embW_ne_tWire

/-- info: 'SparseHamiltonian.GateBinary.embW_ne_pWire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.embW_ne_pWire

/-- info: 'SparseHamiltonian.GateBinary.progG_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.progG_proper

/-- info: 'SparseHamiltonian.GateBinary.progW_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.progW_proper

/-- info: 'SparseHamiltonian.GateBinary.progW_cs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.progW_cs

/-- info: 'SparseHamiltonian.GateBinary.cpy_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cpy_t

/-- info: 'SparseHamiltonian.GateBinary.cpy_cs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cpy_cs

/-- info: 'SparseHamiltonian.GateBinary.copyG_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.copyG_mem

/-- info: 'SparseHamiltonian.GateBinary.copyG_controls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.copyG_controls

/-- info: 'SparseHamiltonian.GateBinary.copyG_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.copyG_proper

/-- info: 'SparseHamiltonian.GateBinary.flatMap_ite_self' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.flatMap_ite_self

/-- info: 'SparseHamiltonian.GateBinary.copyG_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.copyG_filter

/-- info: 'SparseHamiltonian.GateBinary.init_comp_embW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.init_comp_embW

/-- info: 'SparseHamiltonian.GateBinary.progW_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.progW_run

/-- info: 'SparseHamiltonian.GateBinary.bool_clamp' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.bool_clamp

/-- info: 'SparseHamiltonian.GateBinary.circW_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.circW_run

/-- info: 'SparseHamiltonian.GateBinary.binDec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.binDec_eq

/-- info: 'SparseHamiltonian.GateBinary.circW_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.circW_proper

/-- info: 'SparseHamiltonian.GateBinary.circW_cs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.circW_cs

/-- info: 'SparseHamiltonian.GateBinary.cordicArith_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cordicArith_ok

/-- info: 'SparseHamiltonian.GateBinary.card_RN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.card_RN

/-- info: 'SparseHamiltonian.GateBinary.length_copyG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.length_copyG

/-- info: 'SparseHamiltonian.GateBinary.params_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.params_fields

/-- info: 'SparseHamiltonian.GateBinary.cordicArith_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cordicArith_counts

/-- info: 'SparseHamiltonian.GateBinary.Cordic.abs_floor_add_half_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.abs_floor_add_half_sub_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.abs_round_mul_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.abs_round_mul_sub_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.two_le_nOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.two_le_nOf

/-- info: 'SparseHamiltonian.GateBinary.Cordic.sixteen_le_mul_two_pow_nOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.sixteen_le_mul_two_pow_nOf

/-- info: 'SparseHamiltonian.GateBinary.Cordic.thirtytwo_le_mul_two_pow_nOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.thirtytwo_le_mul_two_pow_nOf

/-- info: 'SparseHamiltonian.GateBinary.Cordic.alpha_nOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.alpha_nOf_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.le_two_pow_wordOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.le_two_pow_wordOf

/-- info: 'SparseHamiltonian.GateBinary.Cordic.le_mul_two_pow_wordOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.le_mul_two_pow_wordOf

/-- info: 'SparseHamiltonian.GateBinary.Cordic.nOf_mul_pi_div_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.nOf_mul_pi_div_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.pi_div_two_pow_wordOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.pi_div_two_pow_wordOf_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.params_U_ge_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.params_U_ge_nat

/-- info: 'SparseHamiltonian.GateBinary.Cordic.params_U_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.params_U_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.wordOf_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.wordOf_pos

/-- info: 'SparseHamiltonian.GateBinary.Cordic.params_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.params_w2

/-- info: 'SparseHamiltonian.GateBinary.Cordic.params_c1_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.params_c1_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.params_c1_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.params_c1_lt

/-- info: 'SparseHamiltonian.GateBinary.Cordic.params_c2_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.params_c2_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.params_acc2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.params_acc2

/-- info: 'SparseHamiltonian.GateBinary.Cordic.params_OK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.params_OK

/-- info: 'SparseHamiltonian.GateBinary.Cordic.params_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.params_c1

/-- info: 'SparseHamiltonian.GateBinary.Cordic.params_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.params_c2

/-- info: 'SparseHamiltonian.GateBinary.Cordic.params_U' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.params_U

/-- info: 'SparseHamiltonian.GateBinary.Cordic.params_U_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.params_U_ge

/-- info: 'SparseHamiltonian.GateBinary.Cordic.params_phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.params_phi

/-- info: 'SparseHamiltonian.GateBinary.Cordic.params_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.params_theta

/-- info: 'SparseHamiltonian.GateBinary.Cordic.sum_rev_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.sum_rev_bits

/-- info: 'SparseHamiltonian.GateBinary.Cordic.clamp_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.clamp_error

/-- info: 'SparseHamiltonian.GateBinary.Cordic.toC_p1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.toC_p1

/-- info: 'SparseHamiltonian.GateBinary.Cordic.norm_toC_p1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.norm_toC_p1

/-- info: 'SparseHamiltonian.GateBinary.Cordic.toC_p1_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.toC_p1_ne_zero

/-- info: 'SparseHamiltonian.GateBinary.Cordic.re_toC_p1_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.re_toC_p1_nonneg

/-- info: 'SparseHamiltonian.GateBinary.Cordic.phi_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.phi_error

/-- info: 'SparseHamiltonian.GateBinary.Cordic.citer_zero_point' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.citer_zero_point

/-- info: 'SparseHamiltonian.GateBinary.Cordic.p1_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.p1_eq_zero

/-- info: 'SparseHamiltonian.GateBinary.Cordic.arg_toC_p2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.arg_toC_p2

/-- info: 'SparseHamiltonian.GateBinary.Cordic.theta_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.theta_error

/-- info: 'SparseHamiltonian.GateBinary.Cordic.CParams.OK.w0' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.CParams.OK.w0

/-- info: 'SparseHamiltonian.GateBinary.Cordic.mem_prog_init1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.mem_prog_init1

/-- info: 'SparseHamiltonian.GateBinary.Cordic.mem_prog_iter1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.mem_prog_iter1

/-- info: 'SparseHamiltonian.GateBinary.Cordic.mem_prog_init2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.mem_prog_init2

/-- info: 'SparseHamiltonian.GateBinary.Cordic.mem_prog_iter2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.mem_prog_iter2

/-- info: 'SparseHamiltonian.GateBinary.Cordic.mem_prog_clamp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.mem_prog_clamp

/-- info: 'SparseHamiltonian.GateBinary.Cordic.abs_inX_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.abs_inX_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.abs_inY_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.abs_inY_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.dvd_p1' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.dvd_p1

/-- info: 'SparseHamiltonian.GateBinary.Cordic.norm_p1_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.norm_p1_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.citer_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.citer_range

/-- info: 'SparseHamiltonian.GateBinary.Cordic.norm_p1_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.norm_p1_lt

/-- info: 'SparseHamiltonian.GateBinary.Cordic.stage1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.stage1

/-- info: 'SparseHamiltonian.GateBinary.Cordic.toInt_bmod_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.toInt_bmod_self

/-- info: 'SparseHamiltonian.GateBinary.Cordic.acc1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.acc1

/-- info: 'SparseHamiltonian.GateBinary.Cordic.xOut_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.xOut_nonneg

/-- info: 'SparseHamiltonian.GateBinary.Cordic.xOut_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.xOut_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.dvd_p2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.dvd_p2

/-- info: 'SparseHamiltonian.GateBinary.Cordic.norm_p2_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.norm_p2_lt

/-- info: 'SparseHamiltonian.GateBinary.Cordic.stage2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.stage2

/-- info: 'SparseHamiltonian.GateBinary.Cordic.regs_a2_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.regs_a2_zero

/-- info: 'SparseHamiltonian.GateBinary.Cordic.abs_cacc_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.abs_cacc_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.abs_c2Z_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.abs_c2Z_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.abs_cacc2_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.abs_cacc2_lt

/-- info: 'SparseHamiltonian.GateBinary.Cordic.acc2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.acc2

/-- info: 'SparseHamiltonian.GateBinary.Cordic.regs_dc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.regs_dc

/-- info: 'SparseHamiltonian.GateBinary.Cordic.sum_low_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.sum_low_bits

/-- info: 'SparseHamiltonian.GateBinary.Cordic.sum_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.sum_two_pow

/-- info: 'SparseHamiltonian.GateBinary.Cordic.phi_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.phi_word

/-- info: 'SparseHamiltonian.GateBinary.Cordic.a2_msb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.a2_msb

/-- info: 'SparseHamiltonian.GateBinary.Cordic.dc_msb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.dc_msb

/-- info: 'SparseHamiltonian.GateBinary.Cordic.theta_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.theta_word

/-- info: 'SparseHamiltonian.GateBinary.Cordic.length_prog' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.length_prog

/-- info: 'SparseHamiltonian.GateBinary.Cordic.ix_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.ix_val

/-- info: 'SparseHamiltonian.GateBinary.Cordic.readable_regW' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.readable_regW

/-- info: 'SparseHamiltonian.GateBinary.Cordic.readable_inW' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.readable_inW

/-- info: 'SparseHamiltonian.GateBinary.Cordic.readable_zW' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.readable_zW

/-- info: 'SparseHamiltonian.GateBinary.Cordic.stageLv1' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.stageLv1

/-- info: 'SparseHamiltonian.GateBinary.Cordic.stageLv2' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.stageLv2

/-- info: 'SparseHamiltonian.GateBinary.Cordic.iterOps_levels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.iterOps_levels

/-- info: 'SparseHamiltonian.GateBinary.Cordic.iterOps_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.iterOps_pairwise

/-- info: 'SparseHamiltonian.GateBinary.Cordic.iterOps_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.iterOps_ok

/-- info: 'SparseHamiltonian.GateBinary.Cordic.stage_levels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.stage_levels

/-- info: 'SparseHamiltonian.GateBinary.Cordic.stage_pairwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.stage_pairwise

/-- info: 'SparseHamiltonian.GateBinary.Cordic.stage_ok' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.stage_ok

/-- info: 'SparseHamiltonian.GateBinary.Cordic.init1_levels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.init1_levels

/-- info: 'SparseHamiltonian.GateBinary.Cordic.init2_levels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.init2_levels

/-- info: 'SparseHamiltonian.GateBinary.Cordic.readable_inpS' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.readable_inpS

/-- info: 'SparseHamiltonian.GateBinary.Cordic.readable_signX' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.readable_signX

/-- info: 'SparseHamiltonian.GateBinary.Cordic.progOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.progOK

/-- info: 'SparseHamiltonian.GateBinary.Cordic.regs_dst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.regs_dst

/-- info: 'SparseHamiltonian.GateBinary.Cordic.cfg_inW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.cfg_inW

/-- info: 'SparseHamiltonian.GateBinary.Cordic.cfg_regW' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.cfg_regW

/-- info: 'SparseHamiltonian.GateBinary.Cordic.readBV_zW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.readBV_zW

/-- info: 'SparseHamiltonian.GateBinary.Cordic.ofBits_cstS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.ofBits_cstS

/-- info: 'SparseHamiltonian.GateBinary.Cordic.msb_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.msb_val

/-- info: 'SparseHamiltonian.GateBinary.Cordic.ofBits_shrS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.ofBits_shrS

/-- info: 'SparseHamiltonian.GateBinary.Cordic.val_iter_x' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.val_iter_x

/-- info: 'SparseHamiltonian.GateBinary.Cordic.val_iter_y' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.val_iter_y

/-- info: 'SparseHamiltonian.GateBinary.Cordic.val_iter_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.val_iter_a

/-- info: 'SparseHamiltonian.GateBinary.Cordic.abs_toInt_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.abs_toInt_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.ofBits_inpS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.ofBits_inpS

/-- info: 'SparseHamiltonian.GateBinary.Cordic.signX_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.signX_val

/-- info: 'SparseHamiltonian.GateBinary.Cordic.val_x1_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.val_x1_init

/-- info: 'SparseHamiltonian.GateBinary.Cordic.val_y1_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.val_y1_init

/-- info: 'SparseHamiltonian.GateBinary.Cordic.val_of_const_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.val_of_const_false

/-- info: 'SparseHamiltonian.GateBinary.Cordic.bv_zero_add' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.bv_zero_add

/-- info: 'SparseHamiltonian.GateBinary.Cordic.val_a1_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.val_a1_init

/-- info: 'SparseHamiltonian.GateBinary.Cordic.val_x2_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.val_x2_init

/-- info: 'SparseHamiltonian.GateBinary.Cordic.val_y2_init' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.val_y2_init

/-- info: 'SparseHamiltonian.GateBinary.Cordic.val_dc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.val_dc

/-- info: 'SparseHamiltonian.GateBinary.Cordic.citer_succ' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.citer_succ

/-- info: 'SparseHamiltonian.GateBinary.Cordic.cacc_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.cacc_succ

/-- info: 'SparseHamiltonian.GateBinary.Cordic.toC_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.toC_re

/-- info: 'SparseHamiltonian.GateBinary.Cordic.toC_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.toC_im

/-- info: 'SparseHamiltonian.GateBinary.Cordic.isgn_eq_sgn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.isgn_eq_sgn

/-- info: 'SparseHamiltonian.GateBinary.Cordic.step_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.step_re

/-- info: 'SparseHamiltonian.GateBinary.Cordic.step_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.step_im

/-- info: 'SparseHamiltonian.GateBinary.Cordic.cast_ediv_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.cast_ediv_two_pow

/-- info: 'SparseHamiltonian.GateBinary.Cordic.two_pow_dvd_ediv' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.two_pow_dvd_ediv

/-- info: 'SparseHamiltonian.GateBinary.Cordic.toC_cstep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.toC_cstep

/-- info: 'SparseHamiltonian.GateBinary.Cordic.citer_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.citer_aux

/-- info: 'SparseHamiltonian.GateBinary.Cordic.toC_citer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.toC_citer

/-- info: 'SparseHamiltonian.GateBinary.Cordic.abs_citer_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.abs_citer_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.isgn_citer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.isgn_citer

/-- info: 'SparseHamiltonian.GateBinary.Cordic.cacc_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.cacc_error

/-- info: 'SparseHamiltonian.GateBinary.Cordic.citer_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.citer_fst

/-- info: 'SparseHamiltonian.GateBinary.Cordic.citer_fst_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.citer_fst_nonneg

/-- info: 'SparseHamiltonian.GateBinary.Cordic.iter_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.iter_succ

/-- info: 'SparseHamiltonian.GateBinary.Cordic.acc_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.acc_succ

/-- info: 'SparseHamiltonian.GateBinary.Cordic.arctan_le_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.arctan_le_self

/-- info: 'SparseHamiltonian.GateBinary.Cordic.abs_arctan_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.abs_arctan_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.alpha_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.alpha_nonneg

/-- info: 'SparseHamiltonian.GateBinary.Cordic.alpha_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.alpha_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.alpha_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.alpha_zero

/-- info: 'SparseHamiltonian.GateBinary.Cordic.alpha_le_pi_div_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.alpha_le_pi_div_four

/-- info: 'SparseHamiltonian.GateBinary.Cordic.alpha_le_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.alpha_le_two_mul

/-- info: 'SparseHamiltonian.GateBinary.Cordic.alpha_le_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.alpha_le_tail

/-- info: 'SparseHamiltonian.GateBinary.Cordic.alpha_le_tail_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.alpha_le_tail_sum

/-- info: 'SparseHamiltonian.GateBinary.Cordic.sgn_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.sgn_eq

/-- info: 'SparseHamiltonian.GateBinary.Cordic.abs_sgn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.abs_sgn

/-- info: 'SparseHamiltonian.GateBinary.Cordic.arctan_sgn_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.arctan_sgn_mul

/-- info: 'SparseHamiltonian.GateBinary.Cordic.sgn_mul_arg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.sgn_mul_arg

/-- info: 'SparseHamiltonian.GateBinary.Cordic.norm_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.norm_step

/-- info: 'SparseHamiltonian.GateBinary.Cordic.norm_iter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.norm_iter

/-- info: 'SparseHamiltonian.GateBinary.Cordic.gain_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.gain_pos

/-- info: 'SparseHamiltonian.GateBinary.Cordic.one_le_gain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.one_le_gain

/-- info: 'SparseHamiltonian.GateBinary.Cordic.prod_le_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.prod_le_three

/-- info: 'SparseHamiltonian.GateBinary.Cordic.gain_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.gain_sq

/-- info: 'SparseHamiltonian.GateBinary.Cordic.gain_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.gain_le_two

/-- info: 'SparseHamiltonian.GateBinary.Cordic.iter_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.iter_ne_zero

/-- info: 'SparseHamiltonian.GateBinary.Cordic.arg_ofReal_add_mul_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.arg_ofReal_add_mul_I

/-- info: 'SparseHamiltonian.GateBinary.Cordic.abs_arctan_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.abs_arctan_sub_le

/-- info: 'SparseHamiltonian.GateBinary.Cordic.arg_neg_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.arg_neg_eq

/-- info: 'SparseHamiltonian.GateBinary.Cordic.step_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.step_eq

/-- info: 'SparseHamiltonian.GateBinary.Cordic.arg_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.arg_step

/-- info: 'SparseHamiltonian.GateBinary.Cordic.abs_arg_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.abs_arg_step

/-- info: 'SparseHamiltonian.GateBinary.Cordic.converge_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.converge_aux

/-- info: 'SparseHamiltonian.GateBinary.Cordic.converge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.Cordic.converge

/-! ### Reversible arithmetic -/

/-- info: 'SparseHamiltonian.GateBinary.crun_nil' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_nil

/-- info: 'SparseHamiltonian.GateBinary.crun_cons' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_cons

/-- info: 'SparseHamiltonian.GateBinary.crun_append' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_append

/-- info: 'SparseHamiltonian.GateBinary.lits_congr' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.lits_congr

/-- info: 'SparseHamiltonian.GateBinary.CGate.run_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.CGate.run_run

/-- info: 'SparseHamiltonian.GateBinary.crun_reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_reverse

/-- info: 'SparseHamiltonian.GateBinary.CGate.run_apply_of_ne' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.CGate.run_apply_of_ne

/-- info: 'SparseHamiltonian.GateBinary.crun_apply_of_not' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_apply_of_not

/-- info: 'SparseHamiltonian.GateBinary.CGate.run_congr' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.CGate.run_congr

/-- info: 'SparseHamiltonian.GateBinary.crun_congr' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_congr

/-- info: 'SparseHamiltonian.GateBinary.crun_override' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_override

/-- info: 'SparseHamiltonian.GateBinary.proper_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.proper_append

/-- info: 'SparseHamiltonian.GateBinary.getLsbD_ofBits' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.getLsbD_ofBits

/-- info: 'SparseHamiltonian.GateBinary.ofBits_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ofBits_congr

/-- info: 'SparseHamiltonian.GateBinary.ofBits_getLsbD' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ofBits_getLsbD

/-- info: 'SparseHamiltonian.GateBinary.getLsbD_readBV' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.getLsbD_readBV

/-- info: 'SparseHamiltonian.GateBinary.readBV_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.readBV_congr

/-- info: 'SparseHamiltonian.GateBinary.BSrc.val_congr' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.BSrc.val_congr

/-- info: 'SparseHamiltonian.GateBinary.BSrc.length_gates_le' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.BSrc.length_gates_le

/-- info: 'SparseHamiltonian.GateBinary.BSrc.crun_gates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.BSrc.crun_gates

/-- info: 'SparseHamiltonian.GateBinary.BSrc.proper_gates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.BSrc.proper_gates

/-- info: 'SparseHamiltonian.GateBinary.BSrc.within_gates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.BSrc.within_gates

/-- info: 'SparseHamiltonian.GateBinary.BSrc.cs_length_gates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.BSrc.cs_length_gates

/-- info: 'SparseHamiltonian.GateBinary.BSrc.t_gates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.BSrc.t_gates

/-- info: 'SparseHamiltonian.GateBinary.CGate.run_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.CGate.run_eq

/-- info: 'SparseHamiltonian.GateBinary.crun_same_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_same_target

/-- info: 'SparseHamiltonian.GateBinary.crun_majG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_majG

/-- info: 'SparseHamiltonian.GateBinary.fwdG_succ' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.fwdG_succ

/-- info: 'SparseHamiltonian.GateBinary.sumG_succ' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.sumG_succ

/-- info: 'SparseHamiltonian.GateBinary.length_majG' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.length_majG

/-- info: 'SparseHamiltonian.GateBinary.length_fwdG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.length_fwdG

/-- info: 'SparseHamiltonian.GateBinary.length_sumG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.length_sumG

/-- info: 'SparseHamiltonian.GateBinary.length_adderG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.length_adderG

/-- info: 'SparseHamiltonian.GateBinary.AdderOK.c_ne' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.AdderOK.c_ne

/-- info: 'SparseHamiltonian.GateBinary.crun_fwdG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_fwdG

/-- info: 'SparseHamiltonian.GateBinary.crun_sumG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_sumG

/-- info: 'SparseHamiltonian.GateBinary.proper_fwdG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.proper_fwdG

/-- info: 'SparseHamiltonian.GateBinary.within_fwdG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.within_fwdG

/-- info: 'SparseHamiltonian.GateBinary.crun_adderG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_adderG

/-- info: 'SparseHamiltonian.GateBinary.proper_adderG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.proper_adderG

/-- info: 'SparseHamiltonian.GateBinary.cs_adderG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.cs_adderG

/-- info: 'SparseHamiltonian.GateBinary.card_CW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.card_CW

/-- info: 'SparseHamiltonian.GateBinary.tbW_of_lt' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.tbW_of_lt

/-- info: 'SparseHamiltonian.GateBinary.tcW_of_lt' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.tcW_of_lt

/-- info: 'SparseHamiltonian.GateBinary.regW_of_lt' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.regW_of_lt

/-- info: 'SparseHamiltonian.GateBinary.readBV_regW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.readBV_regW

/-- info: 'SparseHamiltonian.GateBinary.readable_ne_tb' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.readable_ne_tb

/-- info: 'SparseHamiltonian.GateBinary.readable_ne_tc' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.readable_ne_tc

/-- info: 'SparseHamiltonian.GateBinary.readable_ne_reg' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.readable_ne_reg

/-- info: 'SparseHamiltonian.GateBinary.BSrc.On.mono' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.BSrc.On.mono

/-- info: 'SparseHamiltonian.GateBinary.crun_prep_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_prep_bits

/-- info: 'SparseHamiltonian.GateBinary.crun_prepG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_prepG

/-- info: 'SparseHamiltonian.GateBinary.prepCfg_tb' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.prepCfg_tb

/-- info: 'SparseHamiltonian.GateBinary.prepCfg_of_not_tb' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.prepCfg_of_not_tb

/-- info: 'SparseHamiltonian.GateBinary.readable_cfg_update' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.readable_cfg_update

/-- info: 'SparseHamiltonian.GateBinary.ROp.adderOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ROp.adderOK

/-- info: 'SparseHamiltonian.GateBinary.ofBits_xor_fill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ofBits_xor_fill

/-- info: 'SparseHamiltonian.GateBinary.ROp.crun_gates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ROp.crun_gates

/-- info: 'SparseHamiltonian.GateBinary.ROp.val_congr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ROp.val_congr

/-- info: 'SparseHamiltonian.GateBinary.ProgOK.tail' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ProgOK.tail

/-- info: 'SparseHamiltonian.GateBinary.ProgOK.head_lt' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ProgOK.head_lt

/-- info: 'SparseHamiltonian.GateBinary.runOps_of_forall_ne' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.runOps_of_forall_ne

/-- info: 'SparseHamiltonian.GateBinary.crun_progG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_progG

/-- info: 'SparseHamiltonian.GateBinary.runOps_dst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.runOps_dst

/-- info: 'SparseHamiltonian.GateBinary.ROp.proper_gates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ROp.proper_gates

/-- info: 'SparseHamiltonian.GateBinary.ROp.cs_gates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ROp.cs_gates

/-- info: 'SparseHamiltonian.GateBinary.ROp.length_prepG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ROp.length_prepG

/-- info: 'SparseHamiltonian.GateBinary.ROp.length_gates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ROp.length_gates

/-- info: 'SparseHamiltonian.GateBinary.ROp.target_gates' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ROp.target_gates

/-- info: 'SparseHamiltonian.GateBinary.length_progG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.length_progG

/-- info: 'SparseHamiltonian.GateBinary.bmod_two_pow_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.bmod_two_pow_of_le

/-- info: 'SparseHamiltonian.GateBinary.bmod_two_pow_of_nonneg' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.bmod_two_pow_of_nonneg

/-- info: 'SparseHamiltonian.GateBinary.bmod_two_pow_eq_self' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.bmod_two_pow_eq_self

/-- info: 'SparseHamiltonian.GateBinary.xor_fill_add_ofBool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.xor_fill_add_ofBool

/-- info: 'SparseHamiltonian.GateBinary.toInt_add_xor_fill' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.toInt_add_xor_fill

/-- info: 'SparseHamiltonian.GateBinary.getLsbD_last_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.getLsbD_last_eq

/-- info: 'SparseHamiltonian.GateBinary.ofBits_shiftRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.ofBits_shiftRight

/-- info: 'SparseHamiltonian.GateBinary.toInt_ofBits_shiftRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.toInt_ofBits_shiftRight

/-- info: 'SparseHamiltonian.GateBinary.toInt_shiftLeft_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.toInt_shiftLeft_eq

/-- info: 'SparseHamiltonian.GateBinary.toInt_ofBits_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.toInt_ofBits_extend

/-- info: 'SparseHamiltonian.GateBinary.toInt_ofBits_shiftLeft' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.toInt_ofBits_shiftLeft

/-- info: 'SparseHamiltonian.GateBinary.toInt_ofNat_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.toInt_ofNat_of_lt

/-- info: 'SparseHamiltonian.GateBinary.toNat_mod_eq_toInt_emod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.toNat_mod_eq_toInt_emod

/-- info: 'SparseHamiltonian.GateBinary.toNat_ofBits_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.toNat_ofBits_eq_sum

/-- info: 'SparseHamiltonian.GateBinary.toNat_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.toNat_eq_sum

/-- info: 'SparseHamiltonian.GateBinary.toNat_ofBits_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.toNat_ofBits_single

/-- info: 'SparseHamiltonian.GateBinary.lits_map' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.lits_map

/-- info: 'SparseHamiltonian.GateBinary.CGate.run_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.CGate.run_map

/-- info: 'SparseHamiltonian.GateBinary.CGate.run_map_of_not_mem' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.CGate.run_map_of_not_mem

/-- info: 'SparseHamiltonian.GateBinary.crun_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_map

/-- info: 'SparseHamiltonian.GateBinary.crun_map_of_not_mem' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_map_of_not_mem

/-- info: 'SparseHamiltonian.GateBinary.CGate.proper_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.CGate.proper_map

/-- info: 'SparseHamiltonian.GateBinary.crun_xor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinary.crun_xor
