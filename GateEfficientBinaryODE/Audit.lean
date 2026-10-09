import GateEfficientBinaryODE.Synth

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 90 lemmas, whose reports list a
strict subset of these three axioms (19 of them none). The audits cover every
theorem of the library of the dissipative solver from binary data, beginning
with Theorem `ode:thm:gates` for binary sparse oracles. The source circuits
and, for the finite-gate-set form, the synthesis hypothesis
(`GateSynth.Synthesis`) are hypotheses, not axioms.
-/

/-! ### Theorem `ode:thm:gates` from binary data -/

/-- info: 'SparseHamiltonian.GateBinaryODE.binary_ode_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.binary_ode_solver

/-- info: 'SparseHamiltonian.GateBinaryODE.binary_ode_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.binary_ode_counts

/-- info: 'SparseHamiltonian.GateBinaryODE.binary_ode_gate_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.binary_ode_gate_count

/-- info: 'SparseHamiltonian.GateBinaryODE.binary_ode_solver_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.binary_ode_solver_synth

/-- info: 'SparseHamiltonian.GateBinaryODE.Pub.sqrt4s_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Pub.sqrt4s_pos

/-- info: 'SparseHamiltonian.GateBinaryODE.Pub.rho_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Pub.rho_pos

/-- info: 'SparseHamiltonian.GateBinaryODE.Pub.lam_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Pub.lam_sum

/-- info: 'SparseHamiltonian.GateBinaryODE.Pub.tau_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Pub.tau_eq

/-- info: 'SparseHamiltonian.GateBinaryODE.Pub.params_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Pub.params_ok

/-- info: 'SparseHamiltonian.GateBinaryODE.Pub.TD_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Pub.TD_nonneg

/-- info: 'SparseHamiltonian.GateBinaryODE.Pub.step_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Pub.step_pos

/-- info: 'SparseHamiltonian.GateBinaryODE.Pub.lay_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Pub.lay_ok

/-- info: 'SparseHamiltonian.GateBinaryODE.Pub.kap_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Pub.kap_pos

/-- info: 'SparseHamiltonian.GateBinaryODE.Pub.nd_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Pub.nd_public

/-- info: 'SparseHamiltonian.GateBinaryODE.Pub.ar_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Pub.ar_ok

/-- info: 'SparseHamiltonian.GateBinaryODE.Pub.nativeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Pub.nativeOK

/-- info: 'SparseHamiltonian.GateBinaryODE.Pub.sqrt_le_lam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Pub.sqrt_le_lam

/-- info: 'SparseHamiltonian.GateBinaryODE.Pub.selectHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Pub.selectHyp

/-- info: 'SparseHamiltonian.GateBinaryODE.Pub.instanceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Pub.instanceOK

/-- info: 'SparseHamiltonian.GateBinaryODE.Pub.ar_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Pub.ar_counts

/-- info: 'SparseHamiltonian.GateBinaryODE.card_SZ4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.card_SZ4

/-! ### The rounded LCHS step and the clock promises -/

/-- info: 'SparseHamiltonian.GateBinaryODE.exp_pi_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.exp_pi_le

/-- info: 'SparseHamiltonian.GateBinaryODE.hStep_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.hStep_pos

/-- info: 'SparseHamiltonian.GateBinaryODE.hStep_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.hStep_le_one

/-- info: 'SparseHamiltonian.GateBinaryODE.fOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.fOf_spec

/-- info: 'SparseHamiltonian.GateBinaryODE.round_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.round_bounds

/-- info: 'SparseHamiltonian.GateBinaryODE.hRound_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.hRound_bounds

/-- info: 'SparseHamiltonian.GateBinaryODE.hRound_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.hRound_ge

/-- info: 'SparseHamiltonian.GateBinaryODE.rhoL_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.rhoL_close

/-- info: 'SparseHamiltonian.GateBinaryODE.hRound_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.hRound_lt

/-- info: 'SparseHamiltonian.GateBinaryODE.layOf_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.layOf_ok

/-- info: 'SparseHamiltonian.GateBinaryODE.width_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.width_mono

/-- info: 'SparseHamiltonian.GateBinaryODE.moment_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.moment_mono

/-- info: 'SparseHamiltonian.GateBinaryODE.re_inner_qlift_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.re_inner_qlift_nonneg

/-- info: 'SparseHamiltonian.GateBinaryODE.norm_matrixOperator_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.norm_matrixOperator_le

/-- info: 'SparseHamiltonian.GateBinaryODE.gen_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.gen_lift

/-- info: 'SparseHamiltonian.GateBinaryODE.target_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.target_lift

/-- info: 'SparseHamiltonian.GateBinaryODE.clock4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.clock4

/-! ### The compute circuit, the native identity and the boundary -/

/-- info: 'SparseHamiltonian.GateBinaryODE.swE_swE' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.swE_swE

/-- info: 'SparseHamiltonian.GateBinaryODE.swE_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.swE_injective

/-- info: 'SparseHamiltonian.GateBinaryODE.xB4_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.xB4_injective

/-- info: 'SparseHamiltonian.GateBinaryODE.dm4_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.dm4_injective

/-- info: 'SparseHamiltonian.GateBinaryODE.rr4_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.rr4_injective

/-- info: 'SparseHamiltonian.GateBinaryODE.rc4_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.rc4_injective

/-- info: 'SparseHamiltonian.GateBinaryODE.v14_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v14_injective

/-- info: 'SparseHamiltonian.GateBinaryODE.v24_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v24_injective

/-- info: 'SparseHamiltonian.GateBinaryODE.xB4_ne_oB4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.xB4_ne_oB4

/-- info: 'SparseHamiltonian.GateBinaryODE.xB4_ne_tB4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.xB4_ne_tB4

/-- info: 'SparseHamiltonian.GateBinaryODE.xB4_ne_pB4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.xB4_ne_pB4

/-- info: 'SparseHamiltonian.GateBinaryODE.xB4_ne_lB4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.xB4_ne_lB4

/-- info: 'SparseHamiltonian.GateBinaryODE.xB4_ne_dm4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.xB4_ne_dm4

/-- info: 'SparseHamiltonian.GateBinaryODE.xB4_ne_rr4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.xB4_ne_rr4

/-- info: 'SparseHamiltonian.GateBinaryODE.xB4_ne_rc4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.xB4_ne_rc4

/-- info: 'SparseHamiltonian.GateBinaryODE.xB4_ne_v14' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.xB4_ne_v14

/-- info: 'SparseHamiltonian.GateBinaryODE.xB4_ne_v24' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.xB4_ne_v24

/-- info: 'SparseHamiltonian.GateBinaryODE.dm4_ne_tB4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.dm4_ne_tB4

/-- info: 'SparseHamiltonian.GateBinaryODE.dm4_ne_oB4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.dm4_ne_oB4

/-- info: 'SparseHamiltonian.GateBinaryODE.dm4_ne_rr4' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.dm4_ne_rr4

/-- info: 'SparseHamiltonian.GateBinaryODE.dm4_ne_rc4' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.dm4_ne_rc4

/-- info: 'SparseHamiltonian.GateBinaryODE.rr4_ne_rc4' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.rr4_ne_rc4

/-- info: 'SparseHamiltonian.GateBinaryODE.rr4_ne_v14' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.rr4_ne_v14

/-- info: 'SparseHamiltonian.GateBinaryODE.rc4_ne_v14' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.rc4_ne_v14

/-- info: 'SparseHamiltonian.GateBinaryODE.oB4_ne_tB4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.oB4_ne_tB4

/-- info: 'SparseHamiltonian.GateBinaryODE.gateOK_cnot4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.gateOK_cnot4

/-- info: 'SparseHamiltonian.GateBinaryODE.computeV4_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.computeV4_valid

/-- info: 'SparseHamiltonian.GateBinaryODE.computeV4_nGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.computeV4_nGates

/-- info: 'SparseHamiltonian.GateBinaryODE.computeV4_nCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.computeV4_nCalls

/-- info: 'SparseHamiltonian.GateBinaryODE.inp4_avoids' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.inp4_avoids

/-- info: 'SparseHamiltonian.GateBinaryODE.odeOp_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.odeOp_public

/-- info: 'SparseHamiltonian.GateBinaryODE.odeAr_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.odeAr_ok

/-- info: 'SparseHamiltonian.GateBinaryODE.permOp_localOp_permOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.permOp_localOp_permOp

/-- info: 'SparseHamiltonian.GateBinaryODE.localOp_inr_condOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.localOp_inr_condOp

/-- info: 'SparseHamiltonian.GateBinaryODE.preserves_permOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.preserves_permOp

/-- info: 'SparseHamiltonian.GateBinaryODE.eval_call_edge4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.eval_call_edge4

/-- info: 'SparseHamiltonian.GateBinaryODE.bw4_ext' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.bw4_ext

/-- info: 'SparseHamiltonian.GateBinaryODE.refs4_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.refs4_cleanEmb

/-- info: 'SparseHamiltonian.GateBinaryODE.supp_sigRef4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.supp_sigRef4

/-- info: 'SparseHamiltonian.GateBinaryODE.gadgets4_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.gadgets4_agree

/-- info: 'SparseHamiltonian.GateBinaryODE.tB4_not_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.tB4_not_mem

/-- info: 'SparseHamiltonian.GateBinaryODE.flip4_symm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.flip4_symm

/-- info: 'SparseHamiltonian.GateBinaryODE.nrun_cnot4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.nrun_cnot4

/-- info: 'SparseHamiltonian.GateBinaryODE.flip4_overwrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.flip4_overwrite

/-- info: 'SparseHamiltonian.GateBinaryODE.flip4_apply_tB4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.flip4_apply_tB4

/-- info: 'SparseHamiltonian.GateBinaryODE.flip4_apply_out' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.flip4_apply_out

/-- info: 'SparseHamiltonian.GateBinaryODE.loc_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.loc_agree

/-- info: 'SparseHamiltonian.GateBinaryODE.F4_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.F4_isUnitary

/-- info: 'SparseHamiltonian.GateBinaryODE.Lfull4_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Lfull4_eq

/-- info: 'SparseHamiltonian.GateBinaryODE.compute4_cleanEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.compute4_cleanEmb

/-- info: 'SparseHamiltonian.GateBinaryODE.val4_update_oW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.val4_update_oW

/-- info: 'SparseHamiltonian.GateBinaryODE.qlift4_actS4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.qlift4_actS4

/-- info: 'SparseHamiltonian.GateBinaryODE.A4_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.A4_eq

/-- info: 'SparseHamiltonian.GateBinaryODE.posT4_ne_oB4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.posT4_ne_oB4

/-- info: 'SparseHamiltonian.GateBinaryODE.posS4_ne_oB4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.posS4_ne_oB4

/-- info: 'SparseHamiltonian.GateBinaryODE.sigma4_oB4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.sigma4_oB4

/-- info: 'SparseHamiltonian.GateBinaryODE.sigma4_update_oB4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.sigma4_update_oB4

/-- info: 'SparseHamiltonian.GateBinaryODE.rdec_sigma4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.rdec_sigma4

/-- info: 'SparseHamiltonian.GateBinaryODE.selOp_unconj_fam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.selOp_unconj_fam

/-- info: 'SparseHamiltonian.GateBinaryODE.labFam_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.labFam_false

/-- info: 'SparseHamiltonian.GateBinaryODE.nativeOK4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.nativeOK4

/-- info: 'SparseHamiltonian.GateBinaryODE.tagZero_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.tagZero_eq

/-- info: 'SparseHamiltonian.GateBinaryODE.tagOne_swap_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.tagOne_swap_eq

/-- info: 'SparseHamiltonian.GateBinaryODE.gauss_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.gauss_eq_zero

/-- info: 'SparseHamiltonian.GateBinaryODE.ctC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ctC_eq

/-- info: 'SparseHamiltonian.GateBinaryODE.core_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.core_identity

/-- info: 'SparseHamiltonian.GateBinaryODE.alongEquiv_xor_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.alongEquiv_xor_in

/-- info: 'SparseHamiltonian.GateBinaryODE.alongEquiv_xor_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.alongEquiv_xor_out

/-- info: 'SparseHamiltonian.GateBinaryODE.sigma4_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.sigma4_inl

/-- info: 'SparseHamiltonian.GateBinaryODE.sigma4_v14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.sigma4_v14

/-- info: 'SparseHamiltonian.GateBinaryODE.sigma4_v24' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.sigma4_v24

/-- info: 'SparseHamiltonian.GateBinaryODE.phiE_swE' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.phiE_swE

/-- info: 'SparseHamiltonian.GateBinaryODE.nodeW_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.nodeW_eq

/-- info: 'SparseHamiltonian.GateBinaryODE.dur_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.dur_div

/-- info: 'SparseHamiltonian.GateBinaryODE.scale_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.scale_eq

/-- info: 'SparseHamiltonian.GateBinaryODE.twos_sigma4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.twos_sigma4

/-- info: 'SparseHamiltonian.GateBinaryODE.decOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.decOK

/-- info: 'SparseHamiltonian.GateBinaryODE.slotWire4_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.slotWire4_injective

/-- info: 'SparseHamiltonian.GateBinaryODE.hadWires4_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.hadWires4_nodup

/-- info: 'SparseHamiltonian.GateBinaryODE.hadUJ4_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.hadUJ4_ok

/-- info: 'SparseHamiltonian.GateBinaryODE.hadUJ4_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.hadUJ4_length

/-- info: 'SparseHamiltonian.GateBinaryODE.mem_hadWires4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.mem_hadWires4

/-- info: 'SparseHamiltonian.GateBinaryODE.embQ4_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.embQ4_apply

/-- info: 'SparseHamiltonian.GateBinaryODE.embQ4_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.embQ4_single

/-- info: 'SparseHamiltonian.GateBinaryODE.embQ4_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.embQ4_adjoint_apply

/-- info: 'SparseHamiltonian.GateBinaryODE.embQ4_adjoint_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.embQ4_adjoint_single

/-- info: 'SparseHamiltonian.GateBinaryODE.embQ4_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.embQ4_isometry

/-- info: 'SparseHamiltonian.GateBinaryODE.iota0_bas4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.iota0_bas4

/-- info: 'SparseHamiltonian.GateBinaryODE.phi4_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.phi4_zero

/-- info: 'SparseHamiltonian.GateBinaryODE.iota0_unconj_qlift4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.iota0_unconj_qlift4

/-- info: 'SparseHamiltonian.GateBinaryODE.bdryP4_embQ4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.bdryP4_embQ4

/-- info: 'SparseHamiltonian.GateBinaryODE.off_hadWires4_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.off_hadWires4_iff

/-- info: 'SparseHamiltonian.GateBinaryODE.hamp_pow4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.hamp_pow4

/-- info: 'SparseHamiltonian.GateBinaryODE.fixedBoundary4_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.fixedBoundary4_single

/-- info: 'SparseHamiltonian.GateBinaryODE.hadUJ4_iota0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.hadUJ4_iota0

/-- info: 'SparseHamiltonian.GateBinaryODE.boundary_lift4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.boundary_lift4

/-! ### The four-sector private operation on qubits -/

/-- info: 'SparseHamiltonian.GateBinaryODE.dg_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.dg_mul

/-- info: 'SparseHamiltonian.GateBinaryODE.dg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.dg_one

/-- info: 'SparseHamiltonian.GateBinaryODE.dg_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.dg_add

/-- info: 'SparseHamiltonian.GateBinaryODE.dg_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.dg_sub

/-- info: 'SparseHamiltonian.GateBinaryODE.dg_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.dg_smul

/-- info: 'SparseHamiltonian.GateBinaryODE.smul_one_eq_dg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.smul_one_eq_dg

/-- info: 'SparseHamiltonian.GateBinaryODE.dg_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.dg_adjoint

/-- info: 'SparseHamiltonian.GateBinaryODE.dg_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.dg_unitary

/-- info: 'SparseHamiltonian.GateBinaryODE.partK_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.partK_false

/-- info: 'SparseHamiltonian.GateBinaryODE.partK_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.partK_true

/-- info: 'SparseHamiltonian.GateBinaryODE.partK_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.partK_isHermitian

/-- info: 'SparseHamiltonian.GateBinaryODE.partK_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.partK_eq_zero

/-- info: 'SparseHamiltonian.GateBinaryODE.partK_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.partK_add

/-- info: 'SparseHamiltonian.GateBinaryODE.partK_row_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.partK_row_energy

/-- info: 'SparseHamiltonian.GateBinaryODE.partK_col_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.partK_col_energy

/-- info: 'SparseHamiltonian.GateBinaryODE.rhoP_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.rhoP_le

/-- info: 'SparseHamiltonian.GateBinaryODE.rhoP_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.rhoP_nonneg

/-- info: 'SparseHamiltonian.GateBinaryODE.rhoP_sq_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.rhoP_sq_sum_le

/-- info: 'SparseHamiltonian.GateBinaryODE.sqrt_two_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.sqrt_two_mul_sqrt

/-- info: 'SparseHamiltonian.GateBinaryODE.scalar4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.scalar4

/-- info: 'SparseHamiltonian.GateBinaryODE.scaled_gen4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.scaled_gen4

/-- info: 'SparseHamiltonian.GateBinaryODE.inv4_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.inv4_right

/-- info: 'SparseHamiltonian.GateBinaryODE.inv4_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.inv4_left

/-- info: 'SparseHamiltonian.GateBinaryODE.act4_eq_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.act4_eq_cayley

/-- info: 'SparseHamiltonian.GateBinaryODE.act4_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.act4_unitary

/-- info: 'SparseHamiltonian.GateBinaryODE.gen4_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.gen4_adjoint

/-- info: 'SparseHamiltonian.GateBinaryODE.gen4_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.gen4_star

/-- info: 'SparseHamiltonian.GateBinaryODE.bdry4_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.bdry4_isometry

/-- info: 'SparseHamiltonian.GateBinaryODE.gen4_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.gen4_norm

/-- info: 'SparseHamiltonian.GateBinaryODE.sector_bdry_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.sector_bdry_sq

/-- info: 'SparseHamiltonian.GateBinaryODE.gen4_bdry4_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.gen4_bdry4_norm

/-- info: 'SparseHamiltonian.GateBinaryODE.compression4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.compression4

/-- info: 'SparseHamiltonian.GateBinaryODE.one_sub_act4_res4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.one_sub_act4_res4

/-- info: 'SparseHamiltonian.GateBinaryODE.res4_one_sub_act4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.res4_one_sub_act4

/-- info: 'SparseHamiltonian.GateBinaryODE.norm_res4_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.norm_res4_le

/-- info: 'SparseHamiltonian.GateBinaryODE.res4_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.res4_compression

/-- info: 'SparseHamiltonian.GateBinaryODE.norm_res4_bdry4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.norm_res4_bdry4

/-- info: 'SparseHamiltonian.GateBinaryODE.swapTag_swapTag' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.swapTag_swapTag

/-- info: 'SparseHamiltonian.GateBinaryODE.tagSwapT_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.tagSwapT_apply

/-- info: 'SparseHamiltonian.GateBinaryODE.tagSwap_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.tagSwap_apply

/-- info: 'SparseHamiltonian.GateBinaryODE.tagSwap_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.tagSwap_mul_self

/-- info: 'SparseHamiltonian.GateBinaryODE.tagSwap_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.tagSwap_unitary

/-- info: 'SparseHamiltonian.GateBinaryODE.tagSwap_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.tagSwap_adjoint

/-- info: 'SparseHamiltonian.GateBinaryODE.coordinateSwap_comp_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.coordinateSwap_comp_self

/-- info: 'SparseHamiltonian.GateBinaryODE.swap_locator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.swap_locator

/-- info: 'SparseHamiltonian.GateBinaryODE.locS_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.locS_unitary

/-- info: 'SparseHamiltonian.GateBinaryODE.actS_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.actS_eq

/-- info: 'SparseHamiltonian.GateBinaryODE.actS_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.actS_unitary

/-- info: 'SparseHamiltonian.GateBinaryODE.action_eq_locS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.action_eq_locS

/-- info: 'SparseHamiltonian.GateBinaryODE.loc4_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.loc4_unitary

/-- info: 'SparseHamiltonian.GateBinaryODE.actS4_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.actS4_unitary

/-- info: 'SparseHamiltonian.GateBinaryODE.act4_eq_loc4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.act4_eq_loc4

/-- info: 'SparseHamiltonian.GateBinaryODE.ix4_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ix4_injective

/-- info: 'SparseHamiltonian.GateBinaryODE.ix4_ne_oW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ix4_ne_oW

/-- info: 'SparseHamiltonian.GateBinaryODE.ix4_ne_tW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ix4_ne_tW

/-- info: 'SparseHamiltonian.GateBinaryODE.ix4_ne_pW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ix4_ne_pW

/-- info: 'SparseHamiltonian.GateBinaryODE.oW_ne_tW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.oW_ne_tW

/-- info: 'SparseHamiltonian.GateBinaryODE.oW_ne_pW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.oW_ne_pW

/-- info: 'SparseHamiltonian.GateBinaryODE.tW_ne_pW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.tW_ne_pW

/-- info: 'SparseHamiltonian.GateBinaryODE.mk4_oW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.mk4_oW

/-- info: 'SparseHamiltonian.GateBinaryODE.mk4_tW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.mk4_tW

/-- info: 'SparseHamiltonian.GateBinaryODE.mk4_pW' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.mk4_pW

/-- info: 'SparseHamiltonian.GateBinaryODE.mk4_ix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.mk4_ix

/-- info: 'SparseHamiltonian.GateBinaryODE.cfg4_ext' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.cfg4_ext

/-- info: 'SparseHamiltonian.GateBinaryODE.mk4_eta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.mk4_eta

/-- info: 'SparseHamiltonian.GateBinaryODE.te_ofTe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.te_ofTe

/-- info: 'SparseHamiltonian.GateBinaryODE.ofTe_te' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ofTe_te

/-- info: 'SparseHamiltonian.GateBinaryODE.pW_ofTe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.pW_ofTe

/-- info: 'SparseHamiltonian.GateBinaryODE.oW_ofTe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.oW_ofTe

/-- info: 'SparseHamiltonian.GateBinaryODE.phi4_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.phi4_apply

/-- info: 'SparseHamiltonian.GateBinaryODE.update_oW_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.update_oW_eq_iff

/-- info: 'SparseHamiltonian.GateBinaryODE.flat4_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.flat4_apply

/-- info: 'SparseHamiltonian.GateBinaryODE.flat4_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.flat4_symm_apply

/-- info: 'SparseHamiltonian.GateBinaryODE.qlift4_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.qlift4_eq

/-- info: 'SparseHamiltonian.GateBinaryODE.qlift4_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.qlift4_mul

/-- info: 'SparseHamiltonian.GateBinaryODE.qlift4_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.qlift4_comp

/-- info: 'SparseHamiltonian.GateBinaryODE.qlift4_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.qlift4_one

/-- info: 'SparseHamiltonian.GateBinaryODE.qlift4_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.qlift4_sub

/-- info: 'SparseHamiltonian.GateBinaryODE.qlift4_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.qlift4_add

/-- info: 'SparseHamiltonian.GateBinaryODE.qlift4_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.qlift4_smul

/-- info: 'SparseHamiltonian.GateBinaryODE.qlift4_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.qlift4_adjoint

/-- info: 'SparseHamiltonian.GateBinaryODE.qlift4_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.qlift4_isUnitary

/-- info: 'SparseHamiltonian.GateBinaryODE.norm_conj_flat4_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.norm_conj_flat4_le

/-- info: 'SparseHamiltonian.GateBinaryODE.norm_qlift4_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.norm_qlift4_le

/-- info: 'SparseHamiltonian.GateBinaryODE.elift4_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.elift4_comp

/-- info: 'SparseHamiltonian.GateBinaryODE.elift4_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.elift4_one

/-- info: 'SparseHamiltonian.GateBinaryODE.elift4_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.elift4_sub

/-- info: 'SparseHamiltonian.GateBinaryODE.elift4_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.elift4_adjoint

/-- info: 'SparseHamiltonian.GateBinaryODE.norm_elift4_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.norm_elift4_le

/-- info: 'SparseHamiltonian.GateBinaryODE.elift4_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.elift4_isUnitary

/-- info: 'SparseHamiltonian.GateBinaryODE.flat4_symm_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.flat4_symm_single

/-- info: 'SparseHamiltonian.GateBinaryODE.qlift4_bas_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.qlift4_bas_apply

/-- info: 'SparseHamiltonian.GateBinaryODE.regroup_flat4_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.regroup_flat4_single

/-- info: 'SparseHamiltonian.GateBinaryODE.qlift4_dg_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.qlift4_dg_lift

/-- info: 'SparseHamiltonian.GateBinaryODE.te_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.te_eq_iff

/-- info: 'SparseHamiltonian.GateBinaryODE.block_single_inl_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.block_single_inl_inl

/-- info: 'SparseHamiltonian.GateBinaryODE.block_single_inl_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.block_single_inl_inr

/-- info: 'SparseHamiltonian.GateBinaryODE.block_single_inr_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.block_single_inr_inl

/-- info: 'SparseHamiltonian.GateBinaryODE.block_single_inr_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.block_single_inr_inr

/-- info: 'SparseHamiltonian.GateBinaryODE.slice_ix4_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.slice_ix4_bas

/-- info: 'SparseHamiltonian.GateBinaryODE.qlift4_loc4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.qlift4_loc4

/-! ### The angle arithmetic -/

/-- info: 'SparseHamiltonian.GateBinaryODE.readable_regW'' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.readable_regW'

/-- info: 'SparseHamiltonian.GateBinaryODE.readable_zA' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.readable_zA

/-- info: 'SparseHamiltonian.GateBinaryODE.readable_rA' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.readable_rA

/-- info: 'SparseHamiltonian.GateBinaryODE.readable_shA' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.readable_shA

/-- info: 'SparseHamiltonian.GateBinaryODE.readable_inA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.readable_inA

/-- info: 'SparseHamiltonian.GateBinaryODE.readable_uA' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.readable_uA

/-- info: 'SparseHamiltonian.GateBinaryODE.on_rB' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.on_rB

/-- info: 'SparseHamiltonian.GateBinaryODE.on_shB' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.on_shB

/-- info: 'SparseHamiltonian.GateBinaryODE.on_inB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.on_inB

/-- info: 'SparseHamiltonian.GateBinaryODE.on_cB' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.on_cB

/-- info: 'SparseHamiltonian.GateBinaryODE.on_msbO' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.on_msbO

/-- info: 'SparseHamiltonian.GateBinaryODE.on_negS' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.on_negS

/-- info: 'SparseHamiltonian.GateBinaryODE.chain_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.chain_ok

/-- info: 'SparseHamiltonian.GateBinaryODE.lvO_hc' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.lvO_hc

/-- info: 'SparseHamiltonian.GateBinaryODE.lvO_cc' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.lvO_cc

/-- info: 'SparseHamiltonian.GateBinaryODE.lvO_ec' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.lvO_ec

/-- info: 'SparseHamiltonian.GateBinaryODE.lvO_xc' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.lvO_xc

/-- info: 'SparseHamiltonian.GateBinaryODE.lvO_yc' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.lvO_yc

/-- info: 'SparseHamiltonian.GateBinaryODE.chainB_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.chainB_ok

/-- info: 'SparseHamiltonian.GateBinaryODE.chainD_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.chainD_ok

/-- info: 'SparseHamiltonian.GateBinaryODE.chainE_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.chainE_ok

/-- info: 'SparseHamiltonian.GateBinaryODE.chainF_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.chainF_ok

/-- info: 'SparseHamiltonian.GateBinaryODE.chainG_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.chainG_ok

/-- info: 'SparseHamiltonian.GateBinaryODE.opsA_dsts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.opsA_dsts

/-- info: 'SparseHamiltonian.GateBinaryODE.opsA_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.opsA_ok

/-- info: 'SparseHamiltonian.GateBinaryODE.opsC_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.opsC_ok

/-- info: 'SparseHamiltonian.GateBinaryODE.progOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.progOK

/-- info: 'SparseHamiltonian.GateBinaryODE.length_prog' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.length_prog

/-- info: 'SparseHamiltonian.GateBinaryODE.ofInt_add'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ofInt_add'

/-- info: 'SparseHamiltonian.GateBinaryODE.ofInt_mul'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ofInt_mul'

/-- info: 'SparseHamiltonian.GateBinaryODE.ofInt_neg'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ofInt_neg'

/-- info: 'SparseHamiltonian.GateBinaryODE.ofInt_zero'' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ofInt_zero'

/-- info: 'SparseHamiltonian.GateBinaryODE.twoPow_eq_ofInt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.twoPow_eq_ofInt

/-- info: 'SparseHamiltonian.GateBinaryODE.shiftLeft_eq_ofInt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.shiftLeft_eq_ofInt

/-- info: 'SparseHamiltonian.GateBinaryODE.ofInt_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ofInt_eq_iff

/-- info: 'SparseHamiltonian.GateBinaryODE.toInt_ofInt_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.toInt_ofInt_of

/-- info: 'SparseHamiltonian.GateBinaryODE.msb_ofInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.msb_ofInt

/-- info: 'SparseHamiltonian.GateBinaryODE.digits_ofInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.digits_ofInt

/-- info: 'SparseHamiltonian.GateBinaryODE.readBV_zA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.readBV_zA

/-- info: 'SparseHamiltonian.GateBinaryODE.readBV_rA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.readBV_rA

/-- info: 'SparseHamiltonian.GateBinaryODE.cfgOf_regW' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.cfgOf_regW

/-- info: 'SparseHamiltonian.GateBinaryODE.readBV_shA' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.readBV_shA

/-- info: 'SparseHamiltonian.GateBinaryODE.ofBits_rB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ofBits_rB

/-- info: 'SparseHamiltonian.GateBinaryODE.ofBits_shB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ofBits_shB

/-- info: 'SparseHamiltonian.GateBinaryODE.ofBits_cB' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ofBits_cB

/-- info: 'SparseHamiltonian.GateBinaryODE.readBV_inA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.readBV_inA

/-- info: 'SparseHamiltonian.GateBinaryODE.readBV_uA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.readBV_uA

/-- info: 'SparseHamiltonian.GateBinaryODE.readBV_b0A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.readBV_b0A

/-- info: 'SparseHamiltonian.GateBinaryODE.ofBits_b0B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ofBits_b0B

/-- info: 'SparseHamiltonian.GateBinaryODE.ofBits_inB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ofBits_inB

/-- info: 'SparseHamiltonian.GateBinaryODE.val_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.val_eq

/-- info: 'SparseHamiltonian.GateBinaryODE.val_ofInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.val_ofInt

/-- info: 'SparseHamiltonian.GateBinaryODE.msbO_val' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.msbO_val

/-- info: 'SparseHamiltonian.GateBinaryODE.inMsb_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.inMsb_val

/-- info: 'SparseHamiltonian.GateBinaryODE.lit_inl_val' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.lit_inl_val

/-- info: 'SparseHamiltonian.GateBinaryODE.negS_val' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.negS_val

/-- info: 'SparseHamiltonian.GateBinaryODE.chain_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.chain_last

/-- info: 'SparseHamiltonian.GateBinaryODE.twos_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.twos_abs_le

/-- info: 'SparseHamiltonian.GateBinaryODE.sum_testBit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.sum_testBit

/-- info: 'SparseHamiltonian.GateBinaryODE.chi_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.chi_eq

/-- info: 'SparseHamiltonian.GateBinaryODE.chi_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.chi_mem

/-- info: 'SparseHamiltonian.GateBinaryODE.Inp.ct_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Inp.ct_nonneg

/-- info: 'SparseHamiltonian.GateBinaryODE.Inp.ct_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Inp.ct_le

/-- info: 'SparseHamiltonian.GateBinaryODE.Inp.dv_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Inp.dv_nonneg

/-- info: 'SparseHamiltonian.GateBinaryODE.Inp.dv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Inp.dv_le

/-- info: 'SparseHamiltonian.GateBinaryODE.Inp.nv_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Inp.nv_abs_le

/-- info: 'SparseHamiltonian.GateBinaryODE.Inp.mu_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Inp.mu_abs_le

/-- info: 'SparseHamiltonian.GateBinaryODE.Inp.ax_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Inp.ax_abs_le

/-- info: 'SparseHamiltonian.GateBinaryODE.Inp.ay_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Inp.ay_abs_le

/-- info: 'SparseHamiltonian.GateBinaryODE.Inp.zx_abs_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Inp.zx_abs_lt

/-- info: 'SparseHamiltonian.GateBinaryODE.Inp.zy_abs_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Inp.zy_abs_lt

/-- info: 'SparseHamiltonian.GateBinaryODE.regsO_dst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.regsO_dst

/-- info: 'SparseHamiltonian.GateBinaryODE.memA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.memA

/-- info: 'SparseHamiltonian.GateBinaryODE.memB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.memB

/-- info: 'SparseHamiltonian.GateBinaryODE.memC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.memC

/-- info: 'SparseHamiltonian.GateBinaryODE.memD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.memD

/-- info: 'SparseHamiltonian.GateBinaryODE.memE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.memE

/-- info: 'SparseHamiltonian.GateBinaryODE.memF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.memF

/-- info: 'SparseHamiltonian.GateBinaryODE.memG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.memG

/-- info: 'SparseHamiltonian.GateBinaryODE.memA_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.memA_get

/-- info: 'SparseHamiltonian.GateBinaryODE.memC_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.memC_get

/-- info: 'SparseHamiltonian.GateBinaryODE.w_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.w_pos

/-- info: 'SparseHamiltonian.GateBinaryODE.val_mk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.val_mk

/-- info: 'SparseHamiltonian.GateBinaryODE.cfg_inl' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.cfg_inl

/-- info: 'SparseHamiltonian.GateBinaryODE.v_ax1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_ax1

/-- info: 'SparseHamiltonian.GateBinaryODE.v_ax2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_ax2

/-- info: 'SparseHamiltonian.GateBinaryODE.v_n1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_n1

/-- info: 'SparseHamiltonian.GateBinaryODE.v_n2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_n2

/-- info: 'SparseHamiltonian.GateBinaryODE.v_z1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_z1

/-- info: 'SparseHamiltonian.GateBinaryODE.v_z2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_z2

/-- info: 'SparseHamiltonian.GateBinaryODE.msb_z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.msb_z

/-- info: 'SparseHamiltonian.GateBinaryODE.chi1_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.chi1_bit

/-- info: 'SparseHamiltonian.GateBinaryODE.chi2_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.chi2_bit

/-- info: 'SparseHamiltonian.GateBinaryODE.ite_chi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ite_chi

/-- info: 'SparseHamiltonian.GateBinaryODE.v_q0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_q0

/-- info: 'SparseHamiltonian.GateBinaryODE.v_q1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_q1

/-- info: 'SparseHamiltonian.GateBinaryODE.v_du' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_du

/-- info: 'SparseHamiltonian.GateBinaryODE.v_de' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_de

/-- info: 'SparseHamiltonian.GateBinaryODE.v_dd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_dd

/-- info: 'SparseHamiltonian.GateBinaryODE.v_nw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_nw

/-- info: 'SparseHamiltonian.GateBinaryODE.v_rg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_rg

/-- info: 'SparseHamiltonian.GateBinaryODE.msb_rg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.msb_rg

/-- info: 'SparseHamiltonian.GateBinaryODE.v_nn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_nn

/-- info: 'SparseHamiltonian.GateBinaryODE.v_hx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_hx

/-- info: 'SparseHamiltonian.GateBinaryODE.v_hy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_hy

/-- info: 'SparseHamiltonian.GateBinaryODE.v_lx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_lx

/-- info: 'SparseHamiltonian.GateBinaryODE.v_ly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_ly

/-- info: 'SparseHamiltonian.GateBinaryODE.v_sx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_sx

/-- info: 'SparseHamiltonian.GateBinaryODE.v_ex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_ex

/-- info: 'SparseHamiltonian.GateBinaryODE.v_ax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_ax

/-- info: 'SparseHamiltonian.GateBinaryODE.v_sy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_sy

/-- info: 'SparseHamiltonian.GateBinaryODE.v_ey' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_ey

/-- info: 'SparseHamiltonian.GateBinaryODE.v_ay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_ay

/-- info: 'SparseHamiltonian.GateBinaryODE.v_ayt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_ayt

/-- info: 'SparseHamiltonian.GateBinaryODE.v_hc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_hc

/-- info: 'SparseHamiltonian.GateBinaryODE.v_md' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_md

/-- info: 'SparseHamiltonian.GateBinaryODE.v_me' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_me

/-- info: 'SparseHamiltonian.GateBinaryODE.v_mu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_mu

/-- info: 'SparseHamiltonian.GateBinaryODE.abs_mu8_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.abs_mu8_lt

/-- info: 'SparseHamiltonian.GateBinaryODE.msb_mu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.msb_mu

/-- info: 'SparseHamiltonian.GateBinaryODE.v_am' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_am

/-- info: 'SparseHamiltonian.GateBinaryODE.v_axs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_axs

/-- info: 'SparseHamiltonian.GateBinaryODE.v_ays' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_ays

/-- info: 'SparseHamiltonian.GateBinaryODE.bit1_small' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.bit1_small

/-- info: 'SparseHamiltonian.GateBinaryODE.q0_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.q0_bit

/-- info: 'SparseHamiltonian.GateBinaryODE.q1_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.q1_bit

/-- info: 'SparseHamiltonian.GateBinaryODE.v_cc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_cc

/-- info: 'SparseHamiltonian.GateBinaryODE.v_ec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_ec

/-- info: 'SparseHamiltonian.GateBinaryODE.ec_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ec_lt

/-- info: 'SparseHamiltonian.GateBinaryODE.sum_ec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.sum_ec

/-- info: 'SparseHamiltonian.GateBinaryODE.v_xc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_xc

/-- info: 'SparseHamiltonian.GateBinaryODE.v_yc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.v_yc

/-- info: 'SparseHamiltonian.GateBinaryODE.toInt_xc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.toInt_xc

/-- info: 'SparseHamiltonian.GateBinaryODE.toInt_yc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.toInt_yc

/-- info: 'SparseHamiltonian.GateBinaryODE.twos_update'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.twos_update'

/-- info: 'SparseHamiltonian.GateBinaryODE.word_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.word_update

/-- info: 'SparseHamiltonian.GateBinaryODE.Inp.zx_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Inp.zx_update

/-- info: 'SparseHamiltonian.GateBinaryODE.Inp.zy_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.Inp.zy_update

/-- info: 'SparseHamiltonian.GateBinaryODE.xy_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.xy_injective

/-- info: 'SparseHamiltonian.GateBinaryODE.embA_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.embA_injective

/-- info: 'SparseHamiltonian.GateBinaryODE.embP_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.embP_injective

/-- info: 'SparseHamiltonian.GateBinaryODE.prog_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.prog_proper

/-- info: 'SparseHamiltonian.GateBinaryODE.cfgOf_zero_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.cfgOf_zero_comp

/-- info: 'SparseHamiltonian.GateBinaryODE.inBits_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.inBits_eq

/-- info: 'SparseHamiltonian.GateBinaryODE.embP_ne_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.embP_ne_word

/-- info: 'SparseHamiltonian.GateBinaryODE.embP_ne_cordic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.embP_ne_cordic

/-- info: 'SparseHamiltonian.GateBinaryODE.circO_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.circO_run

/-- info: 'SparseHamiltonian.GateBinaryODE.ofBits_inBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.ofBits_inBits

/-- info: 'SparseHamiltonian.GateBinaryODE.zIn_inBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.zIn_inBits

/-- info: 'SparseHamiltonian.GateBinaryODE.decO_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.decO_eq

/-- info: 'SparseHamiltonian.GateBinaryODE.inBits_update' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.inBits_update

/-- info: 'SparseHamiltonian.GateBinaryODE.circO_cs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.circO_cs

/-- info: 'SparseHamiltonian.GateBinaryODE.circO_proper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.circO_proper

/-- info: 'SparseHamiltonian.GateBinaryODE.odeArith_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.odeArith_ok

/-- info: 'SparseHamiltonian.GateBinaryODE.card_RO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.card_RO

/-- info: 'SparseHamiltonian.GateBinaryODE.odeArith_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryODE.odeArith_counts
