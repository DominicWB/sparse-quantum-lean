import GateEfficientSynthesis.Parts
import GateEfficientSynthesis.Binary
import GateEfficientSynthesis.ODESolver

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 3 lemmas, whose reports list a
strict subset of these three axioms. The audits cover every theorem of the
library of synthesis over a finite gate set, beginning with Theorem
`hs:thm:gates` over a finite gate set. Single-qubit synthesis and the
decomposition of controlled gates are hypotheses (`Synthesis`,
`OneQubitSynthesis`, `ControlDecomposition`), not axioms.
-/

/-! ### Theorem `hs:thm:gates` over a finite gate set -/

/-- info: 'SparseHamiltonian.GateSynth.native_simulation_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.native_simulation_synth

/-- info: 'SparseHamiltonian.GateSynth.native_simulation_signed_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.native_simulation_signed_synth

/-- info: 'SparseHamiltonian.GateSynth.native_time_simulation_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.native_time_simulation_synth

/-- info: 'SparseHamiltonian.GateSynth.binary_simulation_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.binary_simulation_synth

/-- info: 'SparseHamiltonian.GateSynth.binary_time_simulation_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.binary_time_simulation_synth

/-- info: 'SparseHamiltonian.GateSynth.binary_simulation_budget_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.binary_simulation_budget_synth

/-- info: 'SparseHamiltonian.GateSynth.binary_time_simulation_budget_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.binary_time_simulation_budget_synth

/-- info: 'SparseHamiltonian.GateSynth.synthBudget_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.synthBudget_spec

/-- info: 'SparseHamiltonian.GateSynth.synthBudget_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.synthBudget_error

/-- info: 'SparseHamiltonian.GateSynth.gates_log_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.gates_log_le

/-! ### Theorem `ode:thm:gates` over a finite gate set -/

/-- info: 'SparseHamiltonian.GateSynth.native_ode_solver_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.native_ode_solver_synth

/-- info: 'SparseHamiltonian.GateSynth.native_ode_time_solver_synth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.native_ode_time_solver_synth

/-- info: 'SparseHamiltonian.GateSynth.norm_sseed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.norm_sseed

/-- info: 'SparseHamiltonian.GateSynth.sgood_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.sgood_isometry

/-- info: 'SparseHamiltonian.GateSynth.sprotocol_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.sprotocol_valid

/-- info: 'SparseHamiltonian.GateSynth.sprogram_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.sprogram_counts

/-- info: 'SparseHamiltonian.GateSynth.sprotocol_worst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.sprotocol_worst

/-- info: 'SparseHamiltonian.GateSynth.sprotocol_worst_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.sprotocol_worst_log

/-- info: 'SparseHamiltonian.GateSynth.norm_adjoint_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.norm_adjoint_apply_le

/-- info: 'SparseHamiltonian.GateSynth.strials_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.strials_eval

/-- info: 'SparseHamiltonian.GateSynth.strials_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.strials_amplitude

/-- info: 'SparseHamiltonian.GateSynth.strials_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.strials_close

/-- info: 'SparseHamiltonian.GateSynth.ntrials_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.ntrials_mean

/-- info: 'SparseHamiltonian.GateSynth.soutcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.soutcome

/-- info: 'SparseHamiltonian.GateSynth.norm_smul_unitDirection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.norm_smul_unitDirection

/-- info: 'SparseHamiltonian.GateSynth.norm_smul_sub_norm_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.norm_smul_sub_norm_smul

/-- info: 'SparseHamiltonian.GateSynth.exists_phase_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.exists_phase_le

/-- info: 'SparseHamiltonian.GateSynth.branch_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.branch_le

/-- info: 'SparseHamiltonian.GateSynth.perturb_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.perturb_four

/-! ### The synthesis hypothesis from its parts -/

/-- info: 'SparseHamiltonian.GateSynth.pols_nil' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.pols_nil

/-- info: 'SparseHamiltonian.GateSynth.partRep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.partRep_spec

/-- info: 'SparseHamiltonian.GateSynth.replace_nGatesOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.replace_nGatesOf

/-- info: 'SparseHamiltonian.GateSynth.gate_map_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.gate_map_map

/-- info: 'SparseHamiltonian.GateSynth.localOp_assoc_liftB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.localOp_assoc_liftB

/-- info: 'SparseHamiltonian.GateSynth.Synthesis.of_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.Synthesis.of_parts

/-- info: 'SparseHamiltonian.GateSynth.of_parts_len_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.of_parts_len_le

/-- info: 'SparseHamiltonian.GateSynth.kind_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.kind_map

/-- info: 'SparseHamiltonian.GateSynth.GateOf.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.GateOf.map

/-! ### Synthesis of circuits, placed gates and payloads -/

/-- info: 'SparseHamiltonian.GateSynth.replace_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.replace_valid

/-- info: 'SparseHamiltonian.GateSynth.mem_replace_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.mem_replace_gate

/-- info: 'SparseHamiltonian.GateSynth.nGatesN_replace_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.nGatesN_replace_le

/-- info: 'SparseHamiltonian.GateSynth.nCallsN_replace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.nCallsN_replace

/-- info: 'SparseHamiltonian.GateSynth.eval_call_inlE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.eval_call_inlE

/-- info: 'SparseHamiltonian.GateSynth.approxOn_replace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.approxOn_replace

/-- info: 'SparseHamiltonian.GateSynth.synthRep_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.synthRep_spec

/-- info: 'SparseHamiltonian.GateSynth.synthC_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.synthC_spec

/-- info: 'SparseHamiltonian.GateSynth.synthC_approxOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.synthC_approxOn

/-- info: 'SparseHamiltonian.GateSynth.synthC_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.synthC_error

/-- info: 'SparseHamiltonian.GateSynth.ctrlOK_conflict' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.ctrlOK_conflict

/-- info: 'SparseHamiltonian.GateSynth.ctrlOK_dedup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.ctrlOK_dedup

/-- info: 'SparseHamiltonian.GateSynth.nodup_fst_dedup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.nodup_fst_dedup

/-- info: 'SparseHamiltonian.GateSynth.gateOp_conflict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.gateOp_conflict

/-- info: 'SparseHamiltonian.GateSynth.gateOp_dedup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.gateOp_dedup

/-- info: 'SparseHamiltonian.GateSynth.place_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.place_injective

/-- info: 'SparseHamiltonian.GateSynth.map_canon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.map_canon

/-- info: 'SparseHamiltonian.GateSynth.gateOK_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.gateOK_map

/-- info: 'SparseHamiltonian.GateSynth.localOp_liftB_canon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.localOp_liftB_canon

/-- info: 'SparseHamiltonian.GateSynth.approxOn_place' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.approxOn_place

/-- info: 'SparseHamiltonian.GateSynth.exists_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.exists_rep

/-- info: 'SparseHamiltonian.GateSynth.liftB_op_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.liftB_op_eq

/-- info: 'SparseHamiltonian.GateSynth.approxOn_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.approxOn_rep

/-- info: 'SparseHamiltonian.GateSynth.matOp_sub_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.matOp_sub_gen

/-- info: 'SparseHamiltonian.GateSynth.gateOp_eq_matOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.gateOp_eq_matOp

/-- info: 'SparseHamiltonian.GateSynth.gRun_eq_matOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.gRun_eq_matOp

/-- info: 'SparseHamiltonian.GateSynth.projS_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.projS_apply

/-- info: 'SparseHamiltonian.GateSynth.projS_supp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.projS_supp

/-- info: 'SparseHamiltonian.GateSynth.supp_projS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.supp_projS

/-- info: 'SparseHamiltonian.GateSynth.norm_projS_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.norm_projS_le

/-- info: 'SparseHamiltonian.GateSynth.toMat_matOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.toMat_matOp

/-- info: 'SparseHamiltonian.GateSynth.approxOn_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.approxOn_payload

/-- info: 'SparseHamiltonian.GateSynth.approxOn_gRun_payload' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSynth.approxOn_gRun_payload
