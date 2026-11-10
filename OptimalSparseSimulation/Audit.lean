import OptimalSparseSimulation.Spectator
import OptimalSparseSimulation.Forms
import OptimalSparseSimulation.Regimes
import OptimalSparseSimulation.Optimal
import OptimalSparseSimulation.Unitary
import OptimalSparseSimulation.UnitaryBound

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (64 theorems), beginning
with the main theorems, then in module order. Every report lists exactly `propext`,
`Classical.choice` and `Quot.sound`. -/

/-! ### Final theorems: Theorem `hs:thm:optimal`, the corollary and the main steps -/

/-- info: 'OptimalSparseSimulation.optimal_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.optimal_simulation

/-- info: 'OptimalSparseSimulation.optimal_simulation_with_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.optimal_simulation_with_reference

/-- info: 'OptimalSparseSimulation.unitary_optimal_inexact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.unitary_optimal_inexact

/-- info: 'OptimalSparseSimulation.unitary_optimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.unitary_optimal

/-- info: 'OptimalSparseSimulation.unitary_optimal_inexact_with_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.unitary_optimal_inexact_with_reference

/-- info: 'OptimalSparseSimulation.unitary_optimal_with_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.unitary_optimal_with_reference

/-- info: 'OptimalSparseSimulation.unitary_bound_inexact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.unitary_bound_inexact

/-- info: 'OptimalSparseSimulation.unitary_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.unitary_bound

/-- info: 'OptimalSparseSimulation.unitary_bound_inexact_with_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.unitary_bound_inexact_with_reference

/-- info: 'OptimalSparseSimulation.unitary_bound_with_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.unitary_bound_with_reference

/-- info: 'OptimalSparseSimulation.simulates_of_spectatorForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.simulates_of_spectatorForm

/-- info: 'OptimalSparseSimulation.implements_of_spectatorForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.implements_of_spectatorForm

/-- info: 'OptimalSparseSimulation.cayleyActive_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.cayleyActive_form

/-- info: 'OptimalSparseSimulation.improved_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.improved_form

/-- info: 'OptimalSparseSimulation.bounded_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.bounded_bound

/-- info: 'OptimalSparseSimulation.signed_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.signed_bound

/-- info: 'OptimalSparseSimulation.unitary_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.unitary_budget

/-! ### Native calls with spectator registers (`Spectator`) -/

/-- info: 'OptimalSparseSimulation.SpectatorForm.diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.SpectatorForm.diagonal

/-- info: 'OptimalSparseSimulation.SpectatorForm.spectator_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.SpectatorForm.spectator_conj

/-- info: 'OptimalSparseSimulation.masked_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.masked_true

/-- info: 'OptimalSparseSimulation.count_ofEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.count_ofEq

/-- info: 'OptimalSparseSimulation.cost_ofEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.cost_ofEq

/-- info: 'OptimalSparseSimulation.eval_ofEq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.eval_ofEq

/-- info: 'OptimalSparseSimulation.isometry_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.isometry_comp

/-- info: 'OptimalSparseSimulation.conj_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.conj_error

/-- info: 'OptimalSparseSimulation.simulates_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.simulates_iff

/-- info: 'OptimalSparseSimulation.SpectatorForm.oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.SpectatorForm.oracle

/-! ### The released oracles in the common form (`Forms`) -/

/-- info: 'OptimalSparseSimulation.cayleyActive_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.cayleyActive_eq

/-! ### The three regimes (`Regimes`) -/

/-- info: 'OptimalSparseSimulation.rval_eq_rb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.rval_eq_rb

/-- info: 'OptimalSparseSimulation.L_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.L_pos

/-- info: 'OptimalSparseSimulation.one_le_h' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.one_le_h

/-- info: 'OptimalSparseSimulation.h_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.h_pos

/-- info: 'OptimalSparseSimulation.r_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.r_pos

/-- info: 'OptimalSparseSimulation.L_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.L_eq

/-- info: 'OptimalSparseSimulation.aux_regime' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.aux_regime

/-- info: 'OptimalSparseSimulation.pow_four_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.pow_four_le_exp

/-- info: 'OptimalSparseSimulation.two_h_le_exp_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.two_h_le_exp_half

/-- info: 'OptimalSparseSimulation.cube_le_x' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.cube_le_x

/-- info: 'OptimalSparseSimulation.h_exp_half_le_x' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.h_exp_half_le_x

/-- info: 'OptimalSparseSimulation.b_le_r' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.b_le_r

/-- info: 'OptimalSparseSimulation.exp_quarter_le_L_div_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.exp_quarter_le_L_div_b

/-- info: 'OptimalSparseSimulation.quarter_le_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.quarter_le_log

/-- info: 'OptimalSparseSimulation.rb_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.rb_le

/-! ### Theorem `hs:thm:optimal` (`Optimal`) -/

/-! ### Corollary `hs:cor:unitary-optimal` (`Unitary`) -/

/-- info: 'OptimalSparseSimulation.delta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.delta_pos

/-- info: 'OptimalSparseSimulation.delta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.delta_le

/-- info: 'OptimalSparseSimulation.delta_le_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.delta_le_half

/-- info: 'OptimalSparseSimulation.half_le_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.half_le_rho

/-- info: 'OptimalSparseSimulation.L_delta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.L_delta_le

/-- info: 'OptimalSparseSimulation.log_delta_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.log_delta_ge

/-- info: 'OptimalSparseSimulation.rb_delta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.rb_delta_le

/-- info: 'OptimalSparseSimulation.lift_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.lift_mul

/-- info: 'OptimalSparseSimulation.lift_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.lift_unitary

/-- info: 'OptimalSparseSimulation.entryOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.entryOracle_unitary

/-- info: 'OptimalSparseSimulation.physOracle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.physOracle_eq

/-- info: 'OptimalSparseSimulation.letter_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.letter_eval

/-- info: 'OptimalSparseSimulation.compile_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.compile_eval

/-- info: 'OptimalSparseSimulation.compile_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.compile_count_le

/-! ### The bound of Corollary `hs:cor:unitary` (`UnitaryBound`) -/

/-- info: 'OptimalSparseSimulation.log_inv_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.log_inv_nonneg

/-- info: 'OptimalSparseSimulation.one_le_log_exp_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.one_le_log_exp_add

/-- info: 'OptimalSparseSimulation.rho_le_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.rho_le_log

/-- info: 'OptimalSparseSimulation.div_nat_le_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.div_nat_le_self

/-- info: 'OptimalSparseSimulation.rho_le_hybrid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.rho_le_hybrid

/-- info: 'OptimalSparseSimulation.optimal_shape_le_unitary_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.optimal_shape_le_unitary_shape

/-- info: 'OptimalSparseSimulation.count_le_unitary_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms OptimalSparseSimulation.count_le_unitary_shape
