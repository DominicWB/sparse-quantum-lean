import GateEfficientSynthesisTrials.Binary

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for one lemma (`andLast_cases`), whose
report lists none of them. The audits cover every theorem of the library of
synthesised trials with exact reflections, beginning with Theorem `ode:thm:gates`
over a finite gate set (a partial formalisation, under this package's format hypotheses, of its
finite-set statement) with the per-trial claim. Single-qubit synthesis and
the decomposition of controlled gates (`GateSynth.Synthesis`), the adjoint closure of
the gate set (`AdjClosed`) and the kinds of the exact zero tests (`zeroTestKinds`)
are hypotheses, not axioms; `extra_hyps` meets the last two
over `closeKinds 𝒢₀`, and the gate counts are then over that set.
-/

/-! ### Theorem `ode:thm:gates` over a finite gate set (partial formalisation, under this package's
format hypotheses, of its finite-set statement), trial by trial -/

/-- info: 'SparseHamiltonian.GateSynthTrials.native_ode_solver_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.native_ode_solver_trials

/-- info: 'SparseHamiltonian.GateSynthTrials.native_ode_time_solver_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.native_ode_time_solver_trials

/-- info: 'SparseHamiltonian.GateSynthTrials.binary_ode_solver_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.binary_ode_solver_trials

/-- info: 'SparseHamiltonian.GateSynthTrials.binary_ode_time_solver_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.binary_ode_time_solver_trials

/-! ### The certificate and the counts of the synthesised protocol -/

/-- info: 'SparseHamiltonian.GateSynthTrials.output_certificate10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.output_certificate10

/-- info: 'SparseHamiltonian.GateSynthTrials.trial_bounds_of_vec10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.trial_bounds_of_vec10

/-- info: 'SparseHamiltonian.GateSynthTrials.vector_error10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.vector_error10

/-- info: 'SparseHamiltonian.GateSynthTrials.native_trial_bounds10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.native_trial_bounds10

/-- info: 'SparseHamiltonian.GateSynthTrials.noutcome10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.noutcome10

/-- info: 'SparseHamiltonian.GateSynthTrials.synth_noutcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.synth_noutcome

/-- info: 'SparseHamiltonian.GateSynthTrials.card_SWO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.card_SWO

/-- info: 'SparseHamiltonian.GateSynthTrials.card_SWO_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.card_SWO_eq

/-- info: 'SparseHamiltonian.GateSynthTrials.card_tested' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.card_tested

/-- info: 'SparseHamiltonian.GateSynthTrials.synth_protocol_worst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.synth_protocol_worst

/-- info: 'SparseHamiltonian.GateSynthTrials.synth_protocol_worst_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.synth_protocol_worst_log

/-! ### The trial register and the synthesised preparation -/

/-- info: 'SparseHamiltonian.GateSynthTrials.embFun_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.embFun_injective

/-- info: 'SparseHamiltonian.GateSynthTrials.embS_not_refl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.embS_not_refl

/-- info: 'SparseHamiltonian.GateSynthTrials.hnP_SWO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.hnP_SWO

/-- info: 'SparseHamiltonian.GateSynthTrials.mem_map_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.mem_map_gate

/-- info: 'SparseHamiltonian.GateSynthTrials.mem_nGatesOf_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.mem_nGatesOf_gate

/-- info: 'SparseHamiltonian.GateSynthTrials.synthPrep_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.synthPrep_valid

/-- info: 'SparseHamiltonian.GateSynthTrials.synthPrep_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.synthPrep_counts

/-- info: 'SparseHamiltonian.GateSynthTrials.synthPrep_gateOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.synthPrep_gateOf

/-- info: 'SparseHamiltonian.GateSynthTrials.synthPrep_inv_gateOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.synthPrep_inv_gateOf

/-- info: 'SparseHamiltonian.GateSynthTrials.synthPrep_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.synthPrep_pres

/-- info: 'SparseHamiltonian.GateSynthTrials.trialS_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.trialS_valid

/-- info: 'SparseHamiltonian.GateSynthTrials.trialS_gateOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.trialS_gateOf

/-- info: 'SparseHamiltonian.GateSynthTrials.approxOn_trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.approxOn_trans

/-- info: 'SparseHamiltonian.GateSynthTrials.approxOn_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.approxOn_restrict

/-- info: 'SparseHamiltonian.GateSynthTrials.liftB_embS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.liftB_embS

/-- info: 'SparseHamiltonian.GateSynthTrials.synthPrep_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.synthPrep_approx

/-! ### Gate sets for exact zero tests and actual inverses -/

/-- info: 'SparseHamiltonian.GateSynthTrials.mem_zeroTestKinds_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.mem_zeroTestKinds_not

/-- info: 'SparseHamiltonian.GateSynthTrials.mem_zeroTestKinds_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.mem_zeroTestKinds_phase

/-- info: 'SparseHamiltonian.GateSynthTrials.mem_zeroTestKinds_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.mem_zeroTestKinds_sign

/-- info: 'SparseHamiltonian.GateSynthTrials.GateOf.inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.GateOf.inv

/-- info: 'SparseHamiltonian.GateSynthTrials.andChain_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.andChain_shape

/-- info: 'SparseHamiltonian.GateSynthTrials.andLast_cases' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.andLast_cases

/-- info: 'SparseHamiltonian.GateSynthTrials.gateOf_mcGate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.gateOf_mcGate

/-- info: 'SparseHamiltonian.GateSynthTrials.zeroLitsN_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.zeroLitsN_nodup

/-- info: 'SparseHamiltonian.GateSynthTrials.seedLitsN_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.seedLitsN_nodup

/-- info: 'SparseHamiltonian.GateSynthTrials.two_le_zeroLitsN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.two_le_zeroLitsN

/-- info: 'SparseHamiltonian.GateSynthTrials.gateOf_rgoodNG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.gateOf_rgoodNG

/-- info: 'SparseHamiltonian.GateSynthTrials.gateOf_rseedNG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.gateOf_rseedNG

/-- info: 'SparseHamiltonian.GateSynthTrials.gateOf_negGateN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.gateOf_negGateN

/-- info: 'SparseHamiltonian.GateSynthTrials.zeroTestKinds_adjClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.zeroTestKinds_adjClosed

/-- info: 'SparseHamiltonian.GateSynthTrials.zeroTestKinds_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.zeroTestKinds_finite

/-- info: 'SparseHamiltonian.GateSynthTrials.closeKinds_adjClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.closeKinds_adjClosed

/-- info: 'SparseHamiltonian.GateSynthTrials.synthesis_closeKinds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.synthesis_closeKinds

/-- info: 'SparseHamiltonian.GateSynthTrials.extra_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynthTrials.extra_hyps
