import GateEfficientBinaryODETime.Synth

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 17 lemmas, whose reports list a
strict subset of these three axioms (2 of them none). The audits cover every
theorem of the library of the time-dependent dissipative solver from time-indexed
binary data, beginning with the time-dependent part of Theorem `ode:thm:gates` for
time-indexed binary sparse oracles. The loading and weight-preparation circuits,
the source, path and target conditions of the instance and, for the finite-gate-set
form, the synthesis hypothesis (`GateSynth.Synthesis`) are hypotheses, not axioms.
-/

/-! ### Theorem `ode:thm:gates` (time-dependent part) from time-indexed binary data -/

/-- info: 'SparseHamiltonian.GateBinaryODETime.binary_ode_time_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.binary_ode_time_solver

/-- info: 'SparseHamiltonian.GateBinaryODETime.binary_ode_time_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.binary_ode_time_counts

/-- info: 'SparseHamiltonian.GateBinaryODETime.binary_ode_time_gate_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.binary_ode_time_gate_count

/-- info: 'SparseHamiltonian.GateBinaryODETime.binary_ode_time_solver_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.binary_ode_time_solver_synth

/-! ### The public data and the instance conditions -/

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.sqrt4s_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.sqrt4s_pos

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.radius_pos

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.rho_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.rho_pos

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.lam_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.lam_sum

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.tau_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.tau_eq

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.params_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.params_ok

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.TD_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.TD_nonneg

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.ε_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.ε_le_one

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.lay_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.lay_ok

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.kap_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.kap_pos

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.nd_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.nd_public

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.ar_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.ar_ok

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.ar_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.ar_counts

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.nativeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.nativeOK

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.sqrt_le_lam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.sqrt_le_lam

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.selectHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.selectHyp

/-- info: 'SparseHamiltonian.GateBinaryODETime.PubT.instanceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.PubT.instanceOK

/-! ### The clock promises at every label and slot -/

/-- info: 'SparseHamiltonian.GateBinaryODETime.clock_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.clock_at

/-- info: 'SparseHamiltonian.GateBinaryODETime.HsT_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.HsT_of_lt

/-- info: 'SparseHamiltonian.GateBinaryODETime.LsT_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.LsT_of_lt

/-- info: 'SparseHamiltonian.GateBinaryODETime.gensT_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.gensT_eq

/-- info: 'SparseHamiltonian.GateBinaryODETime.mask_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.mask_mem

/-- info: 'SparseHamiltonian.GateBinaryODETime.clockT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.clockT

/-! ### The native private operation, its decoder and its native identity -/

/-- info: 'SparseHamiltonian.GateBinaryODETime.inpT4_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.inpT4_avoids

/-- info: 'SparseHamiltonian.GateBinaryODETime.odeOpT_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.odeOpT_public

/-- info: 'SparseHamiltonian.GateBinaryODETime.odeArT_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.odeArT_ok

/-- info: 'SparseHamiltonian.GateBinaryODETime.odeOpT_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.odeOpT_nGates

/-- info: 'SparseHamiltonian.GateBinaryODETime.odeOpT_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.odeOpT_nCalls

/-- info: 'SparseHamiltonian.GateBinaryODETime.twos_ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.twos_ext

/-- info: 'SparseHamiltonian.GateBinaryODETime.decOK_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.decOK_T

/-- info: 'SparseHamiltonian.GateBinaryODETime.privFamT_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.privFamT_word

/-- info: 'SparseHamiltonian.GateBinaryODETime.privFamT_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.privFamT_isUnitary

/-- info: 'SparseHamiltonian.GateBinaryODETime.nativeOK_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.nativeOK_T

/-- info: 'SparseHamiltonian.GateBinaryODETime.gridP_J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.gridP_J

/-- info: 'SparseHamiltonian.GateBinaryODETime.gridP_l' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.gridP_l

/-- info: 'SparseHamiltonian.GateBinaryODETime.gridP_nodeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.gridP_nodeW

/-- info: 'SparseHamiltonian.GateBinaryODETime.nodeWT_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.nodeWT_eq

/-- info: 'SparseHamiltonian.GateBinaryODETime.layT_kq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.layT_kq

/-- info: 'SparseHamiltonian.GateBinaryODETime.kapT_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.kapT_pos

/-- info: 'SparseHamiltonian.GateBinaryODETime.gridP_g' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.gridP_g

/-- info: 'SparseHamiltonian.GateBinaryODETime.gridP_ε' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.gridP_ε

/-- info: 'SparseHamiltonian.GateBinaryODETime.gridP_ε1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.gridP_ε1

/-- info: 'SparseHamiltonian.GateBinaryODETime.hStepT_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.hStepT_pos

/-- info: 'SparseHamiltonian.GateBinaryODETime.layT_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.layT_ok

/-- info: 'SparseHamiltonian.GateBinaryODETime.rhoLT_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.rhoLT_close

/-- info: 'SparseHamiltonian.GateBinaryODETime.hRoundT_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.hRoundT_ne

/-! ### The slot comparator and the angle arithmetic -/

/-- info: 'SparseHamiltonian.GateBinaryODETime.cLay_w' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.cLay_w

/-- info: 'SparseHamiltonian.GateBinaryODETime.cmpOK' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.cmpOK

/-- info: 'SparseHamiltonian.GateBinaryODETime.cregs_dst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.cregs_dst

/-- info: 'SparseHamiltonian.GateBinaryODETime.ofBits_uB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.ofBits_uB

/-- info: 'SparseHamiltonian.GateBinaryODETime.m_le_w' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.m_le_w

/-- info: 'SparseHamiltonian.GateBinaryODETime.v_cdu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.v_cdu

/-- info: 'SparseHamiltonian.GateBinaryODETime.v_cde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.v_cde

/-- info: 'SparseHamiltonian.GateBinaryODETime.msb_cde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.msb_cde

/-- info: 'SparseHamiltonian.GateBinaryODETime.InpT.lift_avoids' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.InpT.lift_avoids

/-- info: 'SparseHamiltonian.GateBinaryODETime.ext_ini' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.ext_ini

/-- info: 'SparseHamiltonian.GateBinaryODETime.dv_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.dv_lift

/-- info: 'SparseHamiltonian.GateBinaryODETime.eC_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.eC_injective

/-- info: 'SparseHamiltonian.GateBinaryODETime.eO_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.eO_injective

/-- info: 'SparseHamiltonian.GateBinaryODETime.cfgOf_zero_eC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.cfgOf_zero_eC

/-- info: 'SparseHamiltonian.GateBinaryODETime.eC_ne_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.eC_ne_word

/-- info: 'SparseHamiltonian.GateBinaryODETime.eC_ne_work' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.eC_ne_work

/-- info: 'SparseHamiltonian.GateBinaryODETime.cmp_proper' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.cmp_proper

/-- info: 'SparseHamiltonian.GateBinaryODETime.circT_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.circT_run

/-- info: 'SparseHamiltonian.GateBinaryODETime.cregs_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.cregs_update

/-- info: 'SparseHamiltonian.GateBinaryODETime.ext_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.ext_update

/-- info: 'SparseHamiltonian.GateBinaryODETime.decT_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.decT_update

/-- info: 'SparseHamiltonian.GateBinaryODETime.circT_cs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.circT_cs

/-- info: 'SparseHamiltonian.GateBinaryODETime.circT_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.circT_proper

/-- info: 'SparseHamiltonian.GateBinaryODETime.arithT_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.arithT_ok

/-- info: 'SparseHamiltonian.GateBinaryODETime.arithT_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.arithT_counts

/-! ### The slot transfer with label selection wires -/

/-- info: 'SparseHamiltonian.GateBinaryODETime.baseW2_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.baseW2_injective

/-- info: 'SparseHamiltonian.GateBinaryODETime.selW2_ne_baseW2' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.selW2_ne_baseW2

/-- info: 'SparseHamiltonian.GateBinaryODETime.slotOf2_glue2' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.slotOf2_glue2

/-- info: 'SparseHamiltonian.GateBinaryODETime.baseOf2_glue2' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.baseOf2_glue2

/-- info: 'SparseHamiltonian.GateBinaryODETime.glue2_slotOf2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.glue2_slotOf2

/-- info: 'SparseHamiltonian.GateBinaryODETime.glue2_apply_baseW2' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.glue2_apply_baseW2

/-- info: 'SparseHamiltonian.GateBinaryODETime.cases_W2' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.cases_W2

/-- info: 'SparseHamiltonian.GateBinaryODETime.glue2_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.glue2_update

/-- info: 'SparseHamiltonian.GateBinaryODETime.slotOf2_overwrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.slotOf2_overwrite

/-- info: 'SparseHamiltonian.GateBinaryODETime.slotOf2_clearCfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.slotOf2_clearCfg

/-- info: 'SparseHamiltonian.GateBinaryODETime.eval_slotInstr2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.eval_slotInstr2

/-- info: 'SparseHamiltonian.GateBinaryODETime.nrun_slot2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.nrun_slot2

/-- info: 'SparseHamiltonian.GateBinaryODETime.localOp_condOp_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.localOp_condOp_slot

/-- info: 'SparseHamiltonian.GateBinaryODETime.Rdec_slot2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.Rdec_slot2

/-- info: 'SparseHamiltonian.GateBinaryODETime.selSlice2_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.selSlice2_apply

/-- info: 'SparseHamiltonian.GateBinaryODETime.slice_cleanEmb2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.slice_cleanEmb2

/-- info: 'SparseHamiltonian.GateBinaryODETime.nativeOK_slot2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.nativeOK_slot2

/-- info: 'SparseHamiltonian.GateBinaryODETime.nGatesN_slot2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.nGatesN_slot2

/-- info: 'SparseHamiltonian.GateBinaryODETime.nCallsN_slot2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.nCallsN_slot2

/-- info: 'SparseHamiltonian.GateBinaryODETime.valid_slot2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.valid_slot2

/-- info: 'SparseHamiltonian.GateBinaryODETime.slotOp2_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.slotOp2_public

/-- info: 'SparseHamiltonian.GateBinaryODETime.atSlot2_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODETime.atSlot2_public
