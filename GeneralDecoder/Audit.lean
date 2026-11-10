import GeneralDecoder.Native
import GeneralDecoder.Simulation
import GeneralDecoder.Budget
import GeneralDecoder.Arith
import GeneralDecoder.Flag
import GeneralDecoder.MainNative
import GeneralDecoder.MainEndpoint
import GeneralDecoder.FlagGen
import GeneralDecoder.PadArith
import GeneralDecoder.Tables

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (141 theorems), beginning
with the main theorems, then in module order. 131 reports list exactly `propext`, `Classical.choice`
and `Quot.sound`; the other 10 list a strict subset. -/

/-! ### Final theorems: the native identities and endpoints with the decoder of the data, the
wrappers with the validity of the index pair, the arithmetic of the padded data and the
lookup tables -/

/-- info: 'SparseHamiltonian.GeneralDecoder.sparse_nativeOKD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.sparse_nativeOKD

/-- info: 'SparseHamiltonian.GeneralDecoder.binary_simulationD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.binary_simulationD

/-- info: 'SparseHamiltonian.GeneralDecoder.binary_simulation_budgetD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.binary_simulation_budgetD

/-- info: 'SparseHamiltonian.GeneralDecoder.sgFOD_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.sgFOD_native

/-- info: 'SparseHamiltonian.GeneralDecoder.clFOD_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.clFOD_native

/-- info: 'SparseHamiltonian.GeneralDecoder.clNDD_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.clNDD_native

/-- info: 'SparseHamiltonian.GeneralDecoder.gate_optimal_binaryD_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.gate_optimal_binaryD_total

/-- info: 'SparseHamiltonian.GeneralDecoder.gate_optimal_binaryD_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.gate_optimal_binaryD_synth

/-- info: 'SparseHamiltonian.GeneralDecoder.RotWordArith.flagLift_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.RotWordArith.flagLift_ok

/-- info: 'SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_compute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_compute

/-- info: 'SparseHamiltonian.GeneralDecoder.flagLiftG_factorOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.flagLiftG_factorOK

/-- info: 'SparseHamiltonian.GeneralDecoder.flagLiftG_rotOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.flagLiftG_rotOK

/-- info: 'SparseHamiltonian.GeneralDecoder.sgFOD_padDataE_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.sgFOD_padDataE_ok

/-- info: 'SparseHamiltonian.GeneralDecoder.clFOD_padDataE_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.clFOD_padDataE_ok

/-- info: 'SparseHamiltonian.GeneralDecoder.clNDD_padDataE_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.clNDD_padDataE_ok

/-- info: 'SparseHamiltonian.GeneralDecoder.pdecode_flag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.pdecode_flag

/-- info: 'SparseHamiltonian.GeneralDecoder.wrap_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.wrap_cost_le

/-- info: 'SparseHamiltonian.GeneralDecoder.rotWordArith_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.rotWordArith_exists

/-- info: 'SparseHamiltonian.GeneralDecoder.sgWordArith_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.sgWordArith_exists

/-- info: 'SparseHamiltonian.GeneralDecoder.clipWordArith_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.clipWordArith_exists

/-! ### The native operation of `hs:thm:gates` with the decoder of the data (`Native`) -/

/-- info: 'SparseHamiltonian.GeneralDecoder.vword_update_oB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.vword_update_oB

/-- info: 'SparseHamiltonian.GeneralDecoder.eword_update_oB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.eword_update_oB

/-- info: 'SparseHamiltonian.GeneralDecoder.sparseOpD_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.sparseOpD_public

/-- info: 'SparseHamiltonian.GeneralDecoder.sparseOpD_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.sparseOpD_V

/-- info: 'SparseHamiltonian.GeneralDecoder.sigma_tB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.sigma_tB

/-- info: 'SparseHamiltonian.GeneralDecoder.rdec_sigmaD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.rdec_sigmaD

/-! ### Rotation arithmetic of the value word and the validity of the index pair (`Arith`, `Flag`) -/

/-- info: 'SparseHamiltonian.GeneralDecoder.vB_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.vB_injective

/-- info: 'SparseHamiltonian.GeneralDecoder.RotWordArith.lift_bT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.RotWordArith.lift_bT

/-- info: 'SparseHamiltonian.GeneralDecoder.RotWordArith.lift_bP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.RotWordArith.lift_bP

/-- info: 'SparseHamiltonian.GeneralDecoder.RotWordArith.lift_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.RotWordArith.lift_A

/-- info: 'SparseHamiltonian.GeneralDecoder.RotWordArith.lift_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.RotWordArith.lift_length

/-- info: 'SparseHamiltonian.GeneralDecoder.RotWordArith.lift_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.RotWordArith.lift_ok

/-- info: 'SparseHamiltonian.GeneralDecoder.flipCfg_update'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.flipCfg_update'

/-- info: 'SparseHamiltonian.GeneralDecoder.classical_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.classical_reverse

/-- info: 'SparseHamiltonian.GeneralDecoder.classical_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.classical_append

/-- info: 'SparseHamiltonian.GeneralDecoder.cfgRun_copies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.cfgRun_copies

/-- info: 'SparseHamiltonian.GeneralDecoder.classical_copies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.classical_copies

/-- info: 'SparseHamiltonian.GeneralDecoder.cfgRun_map_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.cfgRun_map_apply

/-- info: 'SparseHamiltonian.GeneralDecoder.cfgRun_map_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.cfgRun_map_out

/-- info: 'SparseHamiltonian.GeneralDecoder.WF.layoutA' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.WF.layoutA

/-- info: 'SparseHamiltonian.GeneralDecoder.WF.layoutB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.WF.layoutB

/-- info: 'SparseHamiltonian.GeneralDecoder.classical_validC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.classical_validC

/-- info: 'SparseHamiltonian.GeneralDecoder.gateOK_validC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.gateOK_validC

/-- info: 'SparseHamiltonian.GeneralDecoder.length_validC_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.length_validC_le

/-- info: 'SparseHamiltonian.GeneralDecoder.cfgRun_validC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.cfgRun_validC

/-- info: 'SparseHamiltonian.GeneralDecoder.card_FW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.card_FW

/-- info: 'SparseHamiltonian.GeneralDecoder.sAW_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.sAW_injective

/-- info: 'SparseHamiltonian.GeneralDecoder.sFW_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.sFW_injective

/-- info: 'SparseHamiltonian.GeneralDecoder.sAW_ne_sFW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.sAW_ne_sFW

/-- info: 'SparseHamiltonian.GeneralDecoder.ιA_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.ιA_injective

/-- info: 'SparseHamiltonian.GeneralDecoder.ιF_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.ιF_injective

/-- info: 'SparseHamiltonian.GeneralDecoder.ιA_ne_ιF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.ιA_ne_ιF

/-- info: 'SparseHamiltonian.GeneralDecoder.RotWordArith.flagLift_bT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.RotWordArith.flagLift_bT

/-- info: 'SparseHamiltonian.GeneralDecoder.RotWordArith.flagLift_bP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.RotWordArith.flagLift_bP

/-- info: 'SparseHamiltonian.GeneralDecoder.RotWordArith.flagLift_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.RotWordArith.flagLift_A

/-- info: 'SparseHamiltonian.GeneralDecoder.length_flagCopies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.length_flagCopies

/-- info: 'SparseHamiltonian.GeneralDecoder.RotWordArith.flagLift_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.RotWordArith.flagLift_length

/-- info: 'SparseHamiltonian.GeneralDecoder.cpTgt_ne_ιF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.cpTgt_ne_ιF

/-- info: 'SparseHamiltonian.GeneralDecoder.cpTgt_ne_ιA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.cpTgt_ne_ιA

/-- info: 'SparseHamiltonian.GeneralDecoder.cpTgt_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.cpTgt_injective

/-- info: 'SparseHamiltonian.GeneralDecoder.cpSrc_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.cpSrc_eq

/-! ### The native data of `gate:thm:main` with the decoder of the data (`MainNative`, `MainEndpoint`) -/

/-- info: 'SparseHamiltonian.GeneralDecoder.sparseOpD_normD_dec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.sparseOpD_normD_dec

/-- info: 'SparseHamiltonian.GeneralDecoder.edgeBF_overwrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.edgeBF_overwrite

/-- info: 'SparseHamiltonian.GeneralDecoder.sigF_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.sigF_edge

/-- info: 'SparseHamiltonian.GeneralDecoder.entD_overwrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.entD_overwrite

/-- info: 'SparseHamiltonian.GeneralDecoder.entD_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.entD_update

/-- info: 'SparseHamiltonian.GeneralDecoder.entD_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.entD_sig

/-- info: 'SparseHamiltonian.GeneralDecoder.sgFOD_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.sgFOD_public

/-- info: 'SparseHamiltonian.GeneralDecoder.Udec_sgFOD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.Udec_sgFOD

/-- info: 'SparseHamiltonian.GeneralDecoder.sgDec_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.sgDec_sig

/-- info: 'SparseHamiltonian.GeneralDecoder.sgFOD_dec_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.sgFOD_dec_comm

/-- info: 'SparseHamiltonian.GeneralDecoder.norm_cfdecD_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.norm_cfdecD_le

/-- info: 'SparseHamiltonian.GeneralDecoder.clFOD_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.clFOD_public

/-- info: 'SparseHamiltonian.GeneralDecoder.clNDD_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.clNDD_public

/-- info: 'SparseHamiltonian.GeneralDecoder.Udec_clFOD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.Udec_clFOD

/-- info: 'SparseHamiltonian.GeneralDecoder.cfdecD_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.cfdecD_sig

/-- info: 'SparseHamiltonian.GeneralDecoder.clFOD_dec_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.clFOD_dec_comm

/-- info: 'SparseHamiltonian.GeneralDecoder.Rdec_clNDD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.Rdec_clNDD

/-- info: 'SparseHamiltonian.GeneralDecoder.ckdecD_sig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.ckdecD_sig

/-- info: 'SparseHamiltonian.GeneralDecoder.clNDD_rdec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.clNDD_rdec

/-- info: 'SparseHamiltonian.GeneralDecoder.binNBD_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.binNBD_calls

/-- info: 'SparseHamiltonian.GeneralDecoder.binNBD_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.binNBD_cost

/-- info: 'SparseHamiltonian.GeneralDecoder.binNSD_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.binNSD_calls

/-- info: 'SparseHamiltonian.GeneralDecoder.binNSD_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.binNSD_cost

/-- info: 'SparseHamiltonian.GeneralDecoder.binNCD_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.binNCD_calls

/-- info: 'SparseHamiltonian.GeneralDecoder.binNCD_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.binNCD_cost

/-! ### Word arithmetic with the validity of the index pair (`FlagGen`) -/

/-- info: 'SparseHamiltonian.GeneralDecoder.alphaVal_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.alphaVal_false

/-- info: 'SparseHamiltonian.GeneralDecoder.thetaVal_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.thetaVal_false

/-- info: 'SparseHamiltonian.GeneralDecoder.phiVal_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.phiVal_false

/-- info: 'SparseHamiltonian.GeneralDecoder.gA_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.gA_injective

/-- info: 'SparseHamiltonian.GeneralDecoder.gF_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.gF_injective

/-- info: 'SparseHamiltonian.GeneralDecoder.gA_ne_gF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.gA_ne_gF

/-- info: 'SparseHamiltonian.GeneralDecoder.gA_ne_gFT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.gA_ne_gFT

/-- info: 'SparseHamiltonian.GeneralDecoder.gF_ne_gFT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.gF_ne_gFT

/-- info: 'SparseHamiltonian.GeneralDecoder.tgtT_ne_gA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.tgtT_ne_gA

/-- info: 'SparseHamiltonian.GeneralDecoder.tgtP_ne_gA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.tgtP_ne_gA

/-- info: 'SparseHamiltonian.GeneralDecoder.tgtT_ne_gF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.tgtT_ne_gF

/-- info: 'SparseHamiltonian.GeneralDecoder.tgtP_ne_gF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.tgtP_ne_gF

/-- info: 'SparseHamiltonian.GeneralDecoder.tgtT_ne_gFT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.tgtT_ne_gFT

/-- info: 'SparseHamiltonian.GeneralDecoder.tgtP_ne_gFT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.tgtP_ne_gFT

/-- info: 'SparseHamiltonian.GeneralDecoder.tgtT_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.tgtT_injective

/-- info: 'SparseHamiltonian.GeneralDecoder.tgtP_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.tgtP_injective

/-- info: 'SparseHamiltonian.GeneralDecoder.tgtT_ne_tgtP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.tgtT_ne_tgtP

/-- info: 'SparseHamiltonian.GeneralDecoder.gBit_comp' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.gBit_comp

/-- info: 'SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_bT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_bT

/-- info: 'SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_bP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_bP

/-- info: 'SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_A

/-- info: 'SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_tw_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_tw_congr

/-- info: 'SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_pw_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_pw_congr

/-- info: 'SparseHamiltonian.GeneralDecoder.length_ftGates_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.length_ftGates_le

/-- info: 'SparseHamiltonian.GeneralDecoder.length_copiesG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.length_copiesG

/-- info: 'SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_length

/-- info: 'SparseHamiltonian.GeneralDecoder.cfgRun_ftGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.cfgRun_ftGates

/-- info: 'SparseHamiltonian.GeneralDecoder.cfgRun_ftGates_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.cfgRun_ftGates_reverse

/-- info: 'SparseHamiltonian.GeneralDecoder.classical_ftGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.classical_ftGates

/-- info: 'SparseHamiltonian.GeneralDecoder.gateOK_ftGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.gateOK_ftGates

/-- info: 'SparseHamiltonian.GeneralDecoder.classical_copiesG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.classical_copiesG

/-- info: 'SparseHamiltonian.GeneralDecoder.gateOK_copiesG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.gateOK_copiesG

/-- info: 'SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_elem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_elem

/-- info: 'SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_classical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.WordArith.flagLiftG_classical

/-! ### The arithmetic of the padded data with a validity decoder (`PadArith`) -/

/-- info: 'SparseHamiltonian.GeneralDecoder.evalidW_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.evalidW_iff

/-- info: 'SparseHamiltonian.GeneralDecoder.clip_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.clip_zero

/-- info: 'SparseHamiltonian.GeneralDecoder.cclip_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.cclip_zero

/-- info: 'SparseHamiltonian.GeneralDecoder.ccorr_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.ccorr_zero

/-- info: 'SparseHamiltonian.GeneralDecoder.ιEF_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.ιEF_injective

/-- info: 'SparseHamiltonian.GeneralDecoder.ιEF_ne_vF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.ιEF_ne_vF

/-- info: 'SparseHamiltonian.GeneralDecoder.ιEF_ne_gBF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.ιEF_ne_gBF

/-- info: 'SparseHamiltonian.GeneralDecoder.ιEF_ne_locBF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.ιEF_ne_locBF

/-- info: 'SparseHamiltonian.GeneralDecoder.ιEF_ne_ιFin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.ιEF_ne_ιFin

/-- info: 'SparseHamiltonian.GeneralDecoder.ιEF_ne_ιCin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.ιEF_ne_ιCin

/-- info: 'SparseHamiltonian.GeneralDecoder.entD_padDataE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.entD_padDataE

/-- info: 'SparseHamiltonian.GeneralDecoder.sgDec_padDataE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.sgDec_padDataE

/-- info: 'SparseHamiltonian.GeneralDecoder.cfdecD_padDataE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.cfdecD_padDataE

/-- info: 'SparseHamiltonian.GeneralDecoder.ckdecD_padDataE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.ckdecD_padDataE

/-! ### Lookup tables for the arithmetic of a general decoder (`Tables`) -/

/-- info: 'SparseHamiltonian.GeneralDecoder.WordArith.table_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.WordArith.table_length

/-- info: 'SparseHamiltonian.GeneralDecoder.factorAcc_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.factorAcc_table

/-- info: 'SparseHamiltonian.GeneralDecoder.rotAcc_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.rotAcc_table

/-- info: 'SparseHamiltonian.GeneralDecoder.norm_cfVal_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.norm_cfVal_le

/-- info: 'SparseHamiltonian.GeneralDecoder.bitsFor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.bitsFor_le

/-- info: 'SparseHamiltonian.GeneralDecoder.bitsFor_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.bitsFor_words

/-- info: 'SparseHamiltonian.GeneralDecoder.table_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralDecoder.table_cost_le
