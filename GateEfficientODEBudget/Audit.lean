import GateEfficientODEBudget.Synth
import GateEfficientODEBudget.Words

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`. The audits cover every theorem of the library
of the asymptotic gate budget, beginning with equations `ode:eq:gate-main` and
`ode:eq:gate-space` of Theorem `ode:thm:gates` for the dissipative solvers from binary
data. The public rescaling `γ = gammaOf …` is a hypothesis of the endpoints; for the
finite-gate-set forms, single-qubit synthesis and the decomposition of controlled gates
(`GateSynth.Synthesis`), the adjoint closure of the gate set (`AdjClosed`) and the kinds
of the exact zero tests (`zeroTestKinds`) are hypotheses, not axioms; the last two are
without loss of generality (`GateSynthTrials.extra_hyps`).
-/

/-! ### Equations `ode:eq:gate-main` and `ode:eq:gate-space` for the solvers from binary data -/

/-- info: 'SparseHamiltonian.GateODEBudget.binary_ode_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.binary_ode_budget

/-- info: 'SparseHamiltonian.GateODEBudget.binary_ode_time_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.binary_ode_time_budget

/-- info: 'SparseHamiltonian.GateODEBudget.binary_ode_budget_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.binary_ode_budget_words

/-- info: 'SparseHamiltonian.GateODEBudget.binary_ode_time_budget_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.binary_ode_time_budget_words

/-- info: 'SparseHamiltonian.GateODEBudget.binary_ode_budget_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.binary_ode_budget_trials

/-- info: 'SparseHamiltonian.GateODEBudget.binary_ode_time_budget_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.binary_ode_time_budget_trials

/-- info: 'SparseHamiltonian.GateODEBudget.binary_ode_sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.binary_ode_sizes

/-- info: 'SparseHamiltonian.GateODEBudget.binary_ode_time_sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.binary_ode_time_sizes

/-- info: 'SparseHamiltonian.GateODEBudget.pub_shapeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.pub_shapeOK

/-- info: 'SparseHamiltonian.GateODEBudget.gate_budget_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.gate_budget_arith

/-- info: 'SparseHamiltonian.GateODEBudget.gate_budget_arith'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.gate_budget_arith'

/-- info: 'SparseHamiltonian.GateODEBudget.call_budget_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.call_budget_arith

/-- info: 'SparseHamiltonian.GateODEBudget.pubT_shapeOK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.pubT_shapeOK

/-- info: 'SparseHamiltonian.GateODEBudget.clog_two_add_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.clog_two_add_two_le

/-- info: 'SparseHamiltonian.GateODEBudget.wordOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.wordOf_le

/-- info: 'SparseHamiltonian.GateODEBudget.arith_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.arith_poly

/-- info: 'SparseHamiltonian.GateODEBudget.arith_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.arith_words

/-- info: 'SparseHamiltonian.GateODEBudget.words_gate_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.words_gate_arith

/-- info: 'SparseHamiltonian.GateODEBudget.binary_arith_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.binary_arith_words

/-- info: 'SparseHamiltonian.GateODEBudget.binary_time_arith_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.binary_time_arith_words

/-- info: 'SparseHamiltonian.GateODEBudget.prep_budget_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.prep_budget_arith

/-- info: 'SparseHamiltonian.GateODEBudget.prep_budget_arith'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.prep_budget_arith'

/-- info: 'SparseHamiltonian.GateODEBudget.card_XW_SZ4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.card_XW_SZ4

/-- info: 'SparseHamiltonian.GateODEBudget.card_SX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.card_SX

/-! ### The public rescaling and the size bounds -/

/-- info: 'SparseHamiltonian.GateODEBudget.key_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.key_div

/-- info: 'SparseHamiltonian.GateODEBudget.key_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.key_mul

/-- info: 'SparseHamiltonian.GateODEBudget.key_dis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.key_dis

/-- info: 'SparseHamiltonian.GateODEBudget.gam_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.gam_pos

/-- info: 'SparseHamiltonian.GateODEBudget.gam_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.gam_le_one

/-- info: 'SparseHamiltonian.GateODEBudget.gam_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.gam_eq

/-- info: 'SparseHamiltonian.GateODEBudget.gam_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.gam_cases

/-- info: 'SparseHamiltonian.GateODEBudget.gam_div_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.gam_div_le

/-- info: 'SparseHamiltonian.GateODEBudget.gam_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.gam_mul_le

/-- info: 'SparseHamiltonian.GateODEBudget.gam_dis_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.gam_dis_le

/-- info: 'SparseHamiltonian.GateODEBudget.gammaOf_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.gammaOf_le_one

/-- info: 'SparseHamiltonian.GateODEBudget.sqrt_four_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.sqrt_four_mul

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.ell_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.ell_ge

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.ell_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.ell_pos

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.theta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.theta_pos

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.sum_le_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.sum_le_theta

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.dis_le_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.dis_le_theta

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.gammaOf_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.gammaOf_pos

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.sqrt_le_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.sqrt_le_q

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.ell_le_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.ell_le_q

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.one_le_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.one_le_q

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.q_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.q_pos

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.tau_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.tau_le

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.log_three_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.log_three_le

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.log_512_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.log_512_le

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.width_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.width_mul_le

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.degree_shape_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.degree_shape_le

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.lamD_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.lamD_le

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.lam_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.lam_le

/-- info: 'SparseHamiltonian.GateODEBudget.ShapeOK.grid_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.ShapeOK.grid_le

/-- info: 'SparseHamiltonian.GateODEBudget.steps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODEBudget.steps_le
