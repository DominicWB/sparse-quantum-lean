import ZeroTimeGateODE.Grover
import ZeroTimeGateODE.Certificate
import ZeroTimeGateODE.Assembly
import ZeroTimeGateODE.Constant
import ZeroTimeGateODE.Combined
import ZeroTimeGateODE.TimeAssembly
import ZeroTimeGateODE.Time
import ZeroTimeGateODE.TimeCombined
import ZeroTimeGateODE.Synth
import ZeroTimeGateODE.Binary
import ZeroTimeGateODE.BinaryTime
import ZeroTimeGateODE.SynthCombined
import ZeroTimeGateODE.BinarySynth
import ZeroTimeGateODE.ExactCircuit
import ZeroTimeGateODE.Exact
import ZeroTimeGateODE.ExactTime
import ZeroTimeGateODE.ExactTimeSolver
import ZeroTimeGateODE.ExactCombined

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and
`Quot.sound`, except for 3 lemmas, whose reports list a subset of these three axioms (or none).
The audits cover every theorem of the library of the gate-level remark of Theorem
`ode:thm:gates` on zero time and a known zero generator, beginning with the native solver in
the zero case (`native_ode_solver_zero`) and for every `T ≥ 0` (`native_ode_solver_nonneg`).
-/

/-! ### Theorem `ode:thm:gates`, native gates, constant coefficients -/

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.native_ode_solver_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.native_ode_solver_zero

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.native_ode_solver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.native_ode_solver_nonneg

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.card_ZNW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.card_ZNW

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.nw_eq_znw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.nw_eq_znw

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zero_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zero_target

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.generator_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.generator_zero

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.srcRot_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.srcRot_decoded

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.native_zero_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.native_zero_outcome

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.publicOK0_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.publicOK0_of

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.publicOK_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.publicOK_of

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zeroCase_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zeroCase_iff

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zInstanceOK_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zInstanceOK_of

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.target_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.target_zero

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.native_zero_outcome_params' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.native_zero_outcome_params

/-! ### Theorem `ode:thm:gates`, native gates, time-dependent coefficients -/

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.recurrence_step_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.recurrence_step_zero

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.recurrence_gen_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.recurrence_gen_zero

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.ttarget_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.ttarget_zero

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zsrc_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zsrc_sum

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tz_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tz_decoded

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzInstanceOK_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzInstanceOK_of

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzero_samples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzero_samples

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.native_time_zero_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.native_time_zero_outcome

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.native_ode_time_solver_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.native_ode_time_solver_zero

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tpublicOK0_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tpublicOK0_of

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tpublicOK_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tpublicOK_of

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.mesh_of_zeroCase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.mesh_of_zeroCase

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.native_ode_time_solver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.native_ode_time_solver_nonneg

/-! ### Theorem `ode:thm:gates`, exact gates (constant and time-dependent coefficients) -/

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zprepE_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zprepE_counts

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zstepE_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zstepE_counts

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.ztrialE_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.ztrialE_counts

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zprepE_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zprepE_valid

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zstepE_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zstepE_valid

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.ztrialE_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.ztrialE_valid

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.run_eq_srcOracles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.run_eq_srcOracles

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.ztrialE_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.ztrialE_isUnitary

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zprepE_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zprepE_isUnitary

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.pres2_zprepE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.pres2_zprepE

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zstepE_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zstepE_agrees

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.pres_zgroverStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.pres_zgroverStep

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zsteps_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zsteps_agree

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.ztrialE_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.ztrialE_seed

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zprepE_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zprepE_decoded

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zprogram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zprogram_eval

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zprogram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zprogram_cost

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zprotocol_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zprotocol_eq

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.ztrials_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.ztrials_eval

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.ztrials_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.ztrials_output

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.ztrials_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.ztrials_seed

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.ztrials_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.ztrials_amplitude

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.ztrial_cost_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.ztrial_cost_bound

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zprotocol_worst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zprotocol_worst

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.ztrial_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.ztrial_bounds

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zoutcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zoutcome

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.exact_ode_solver_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.exact_ode_solver_zero

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzprepE_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzprepE_counts

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzstepE_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzstepE_counts

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tztrialE_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tztrialE_counts

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzprepE_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzprepE_valid

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzstepE_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzstepE_valid

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tztrialE_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tztrialE_valid

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.trun_eq_srcOracles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.trun_eq_srcOracles

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tztrialE_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tztrialE_isUnitary

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzprepE_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzprepE_isUnitary

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.pres2_tzprepE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.pres2_tzprepE

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzstepE_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzstepE_agrees

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.pres_tzgroverStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.pres_tzgroverStep

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzsteps_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzsteps_agree

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tztrialE_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tztrialE_seed

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzprogram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzprogram_eval

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzprogram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzprogram_cost

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzprotocol_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzprotocol_eq

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tztrials_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tztrials_eval

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tztrials_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tztrials_output

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tztrials_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tztrials_seed

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tztrials_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tztrials_amplitude

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tztrial_cost_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tztrial_cost_bound

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzprotocol_worst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzprotocol_worst

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tztrial_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tztrial_bounds

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzoutcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzoutcome

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.exact_ode_time_solver_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.exact_ode_time_solver_zero

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.sizes_of_publicOK0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.sizes_of_publicOK0

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.exact_ode_solver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.exact_ode_solver_nonneg

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tsizes_of_publicOK0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tsizes_of_publicOK0

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.exact_ode_time_solver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.exact_ode_time_solver_nonneg

/-! ### Finite gate sets with the per-trial claim -/

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.native_ode_solver_zero_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.native_ode_solver_zero_trials

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.native_ode_time_solver_zero_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.native_ode_time_solver_zero_trials

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.native_ode_solver_nonneg_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.native_ode_solver_nonneg_trials

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.native_ode_time_solver_nonneg_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.native_ode_time_solver_nonneg_trials

/-! ### Binary and time-indexed binary sparse data -/

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.bpublicOK0_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.bpublicOK0_of

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.bpublicOK_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.bpublicOK_of

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.binary_target_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.binary_target_zero

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.binary_zero_no_matrix_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.binary_zero_no_matrix_calls

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.binary_ode_solver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.binary_ode_solver_nonneg

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.btpublicOK0_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.btpublicOK0_of

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.btpublicOK_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.btpublicOK_of

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.btparams_ok0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.btparams_ok0

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.btzeroCase_params' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.btzeroCase_params

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.sqrt_le_lam0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.sqrt_le_lam0

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.binary_tzInstanceOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.binary_tzInstanceOK

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.binary_time_zero_no_matrix_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.binary_time_zero_no_matrix_calls

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.binary_ode_time_solver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.binary_ode_time_solver_nonneg

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.binary_ode_solver_nonneg_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.binary_ode_solver_nonneg_trials

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.binary_ode_time_solver_nonneg_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.binary_ode_time_solver_nonneg_trials

/-! ### Direct source assembly: circuits, agreement and decoded vectors -/

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zprepC_eq_flatMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zprepC_eq_flatMap

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.srcRot_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.srcRot_unitary

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.srcMat_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.srcMat_zero

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.unitaryMat_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.unitaryMat_conjTranspose

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zprepC_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zprepC_valid

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.srcPl_not_refl' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.srcPl_not_refl

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zprepC_not_touches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zprepC_not_touches

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zprepC_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zprepC_counts

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zprepC_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zprepC_pres

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zmacro_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zmacro_gate

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zmacro_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zmacro_src

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.macro_flatMap_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.macro_flatMap_approx

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zprepC_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zprepC_approx

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.iniCfg_ne' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.iniCfg_ne

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.gate_ini_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.gate_ini_zero

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.gate_ini_apply_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.gate_ini_apply_zero

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.zrelC_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.zrelC_decoded

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzprepC_eq_flatMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzprepC_eq_flatMap

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzprepC_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzprepC_valid

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzprepC_not_touches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzprepC_not_touches

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzprepC_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzprepC_counts

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzprepC_pres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzprepC_pres

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzmacro_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzmacro_approx

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzprepC_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzprepC_approx

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.srcCfg_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.srcCfg_injective

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.wprep_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.wprep_zero

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.wprep_adj_apply_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.wprep_adj_apply_zero

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.tzrelC_decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.tzrelC_decoded

/-! ### The direct certificate and amplification for amplitudes up to one -/

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.output_certificate_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.output_certificate_direct

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.trial_bounds_of_vec_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.trial_bounds_of_vec_direct

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.native_trial_bounds_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.native_trial_bounds_direct

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.noutcome_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.noutcome_direct

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.noutcome_direct_retarget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.noutcome_direct_retarget

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.vector_error_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.vector_error_direct

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.noutcome_of_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.noutcome_of_released

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.sin_four_mul_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.sin_four_mul_eq

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.sin_four_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.sin_four_mul_le

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.meanSuccess_high' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.meanSuccess_high

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.promised_amplitude_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.promised_amplitude_full

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.norm_adjoint_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.norm_adjoint_apply_le

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.amplitude_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.amplitude_le_one

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.angle_geometry_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.angle_geometry_lt_one

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.trial_projected_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.trial_projected_lt_one

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.trial_probability_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.trial_probability_lt_one

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.decoded_multiple_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.decoded_multiple_lt_one

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.prepared_good_of_amplitude_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.prepared_good_of_amplitude_one

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.grover_apply_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.grover_apply_fixed

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.trial_of_amplitude_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.trial_of_amplitude_one

/-- info: 'SparseHamiltonian.ZeroTimeGateODE.randomized_certificate_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ZeroTimeGateODE.randomized_certificate_full
