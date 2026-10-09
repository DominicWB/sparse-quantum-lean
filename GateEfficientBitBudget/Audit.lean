import GateEfficientBitBudget.Bits
import GateEfficientBitBudget.Scale
import GateEfficientBitBudget.Sizes
import GateEfficientBitBudget.Constant
import GateEfficientBitBudget.Time
import GateEfficientBitBudget.Witness
import GateEfficientBitBudget.Hamiltonian
import GateEfficientBitBudget.HamiltonianGates
import GateEfficientBitBudget.HamiltonianBudget
import GateEfficientBitBudget.NonVacuity
import GateEfficientBitBudget.SynthWords
import GateEfficientBitBudget.Synth
import GateEfficientBitBudget.SynthHamiltonian

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 2 lemmas (`twos_inl_zero`, `twos_inr_zero`,
proved by `decide`), whose reports list the strict subset `propext`, `Quot.sound`. The audits
cover every theorem of the library of the gate budgets in the bit-length parameter `𝔟`,
beginning with equations `ode:eq:gate-main` and `ode:eq:gate-space` of Theorem `ode:thm:gates`
(equation `ode:eq:gate-word-budget`) and equation `hs:eq:gate-binary` of Theorem `hs:thm:gates`
for the constructions from binary data. The public rescaling `γ = gammaOf …`, the lower bound of
the arithmetic accuracy and the bit lengths of the public parameters (`HasBits`) are hypotheses
of the endpoints (jointly satisfiable, the data hypotheses included: `bits_witness`,
`bits_witnessT`, `ode_all_hyps`, `ode_time_all_hyps`, `hs_all_hyps`, `hsT_all_hyps`); for the
finite-gate-set forms, single-qubit synthesis and the decomposition of controlled gates
(`GateSynth.Synthesis`), the adjoint closure of the gate set (`AdjClosed`) and the kinds of the
exact zero tests (`zeroTestKinds`) are hypotheses, not axioms.
-/

/-! ### The endpoints: `ode:eq:gate-main`, `ode:eq:gate-space`, `hs:eq:gate-binary` in `𝔟` -/

/-- info: 'SparseHamiltonian.GateBitBudget.binary_ode_budget_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.binary_ode_budget_bits

/-- info: 'SparseHamiltonian.GateBitBudget.binary_ode_time_budget_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.binary_ode_time_budget_bits

/-- info: 'SparseHamiltonian.GateBitBudget.binary_simulation_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.binary_simulation_bits

/-- info: 'SparseHamiltonian.GateBitBudget.binary_time_simulation_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.binary_time_simulation_bits

/-- info: 'SparseHamiltonian.GateBitBudget.words_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.words_le

/-- info: 'SparseHamiltonian.GateBitBudget.words_le_bitB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.words_le_bitB

/-- info: 'SparseHamiltonian.GateBitBudget.wordsT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.wordsT_le

/-- info: 'SparseHamiltonian.GateBitBudget.zetaOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.zetaOf_spec

/-- info: 'SparseHamiltonian.GateBitBudget.withChoice_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.withChoice_spec

/-- info: 'SparseHamiltonian.GateBitBudget.withChoiceT_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.withChoiceT_spec

/-- info: 'SparseHamiltonian.GateBitBudget.logBudget_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.logBudget_two

/-- info: 'SparseHamiltonian.GateBitBudget.qOf_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.qOf_two_le

/-- info: 'SparseHamiltonian.GateBitBudget.bitB_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.bitB_two_le

/-- info: 'SparseHamiltonian.GateBitBudget.time_budget_user' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.time_budget_user

/-- info: 'SparseHamiltonian.GateBitBudget.binary_ode_time_budget_bits_user' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.binary_ode_time_budget_bits_user

/-! ### The hypotheses are satisfiable and the endpoints are not vacuous -/

/-- info: 'SparseHamiltonian.GateBitBudget.exists_common_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.exists_common_bits

/-- info: 'SparseHamiltonian.GateBitBudget.withChoice_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.withChoice_bits

/-- info: 'SparseHamiltonian.GateBitBudget.withChoiceT_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.withChoiceT_bits

/-- info: 'SparseHamiltonian.GateBitBudget.pointPub_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.pointPub_ok

/-- info: 'SparseHamiltonian.GateBitBudget.pointPubT_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.pointPubT_ok

/-- info: 'SparseHamiltonian.GateBitBudget.bits_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.bits_witness

/-- info: 'SparseHamiltonian.GateBitBudget.bits_witnessT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.bits_witnessT

/-- info: 'SparseHamiltonian.GateBitBudget.twos_inl_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.twos_inl_zero

/-- info: 'SparseHamiltonian.GateBitBudget.twos_inr_zero' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.twos_inr_zero

/-- info: 'SparseHamiltonian.GateBitBudget.gauss_zero_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.gauss_zero_word

/-- info: 'SparseHamiltonian.GateBitBudget.pointData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.pointData_matrix

/-- info: 'SparseHamiltonian.GateBitBudget.pointData_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.pointData_range

/-- info: 'SparseHamiltonian.GateBitBudget.ode_all_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.ode_all_hyps

/-- info: 'SparseHamiltonian.GateBitBudget.ode_time_all_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.ode_time_all_hyps

/-- info: 'SparseHamiltonian.GateBitBudget.hs_all_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.hs_all_hyps

/-- info: 'SparseHamiltonian.GateBitBudget.hsT_all_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.hsT_all_hyps

/-! ### Over a finite gate set -/

/-- info: 'SparseHamiltonian.GateBitBudget.inner_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.inner_le

/-- info: 'SparseHamiltonian.GateBitBudget.log_prep_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.log_prep_le

/-- info: 'SparseHamiltonian.GateBitBudget.log_three_div_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.log_three_div_le

/-- info: 'SparseHamiltonian.GateBitBudget.log_q_cube_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.log_q_cube_le

/-- info: 'SparseHamiltonian.GateBitBudget.prepBound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.prepBound_le

/-- info: 'SparseHamiltonian.GateBitBudget.log_factor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.log_factor_le

/-- info: 'SparseHamiltonian.GateBitBudget.tested_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.tested_le

/-- info: 'SparseHamiltonian.GateBitBudget.prepBoundT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.prepBoundT_le

/-- info: 'SparseHamiltonian.GateBitBudget.log_factorT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.log_factorT_le

/-- info: 'SparseHamiltonian.GateBitBudget.testedT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.testedT_le

/-- info: 'SparseHamiltonian.GateBitBudget.synth_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.synth_arith

/-- info: 'SparseHamiltonian.GateBitBudget.binary_ode_budget_trials_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.binary_ode_budget_trials_bits

/-- info: 'SparseHamiltonian.GateBitBudget.binary_ode_time_budget_trials_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.binary_ode_time_budget_trials_bits

/-- info: 'SparseHamiltonian.GateBitBudget.hs_log_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.hs_log_le

/-- info: 'SparseHamiltonian.GateBitBudget.hs_synth_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.hs_synth_arith

/-- info: 'SparseHamiltonian.GateBitBudget.binary_simulation_budget_synth_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.binary_simulation_budget_synth_bits

/-- info: 'SparseHamiltonian.GateBitBudget.binary_time_simulation_budget_synth_bits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.binary_time_simulation_budget_synth_bits

/-! ### Bit lengths and the word budget `𝔟` -/

/-- info: 'SparseHamiltonian.GateBitBudget.hasBits_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.hasBits_iff

/-- info: 'SparseHamiltonian.GateBitBudget.HasBits.abs_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.HasBits.abs_lt

/-- info: 'SparseHamiltonian.GateBitBudget.HasBits.lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.HasBits.lt

/-- info: 'SparseHamiltonian.GateBitBudget.HasBits.one_le_mul_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.HasBits.one_le_mul_abs

/-- info: 'SparseHamiltonian.GateBitBudget.HasBits.one_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.HasBits.one_le_mul

/-- info: 'SparseHamiltonian.GateBitBudget.HasBits.abs_logb_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.HasBits.abs_logb_le

/-- info: 'SparseHamiltonian.GateBitBudget.HasBits.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.HasBits.mono

/-- info: 'SparseHamiltonian.GateBitBudget.hasBits_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.hasBits_zero

/-- info: 'SparseHamiltonian.GateBitBudget.hasBits_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.hasBits_fixed

/-- info: 'SparseHamiltonian.GateBitBudget.hasBits_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.hasBits_int

/-- info: 'SparseHamiltonian.GateBitBudget.exists_hasBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.exists_hasBits

/-- info: 'SparseHamiltonian.GateBitBudget.bitH_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.bitH_eq

/-- info: 'SparseHamiltonian.GateBitBudget.logb_succ_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.logb_succ_nonneg

/-- info: 'SparseHamiltonian.GateBitBudget.bitB_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.bitB_mono

/-- info: 'SparseHamiltonian.GateBitBudget.bitB_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.bitB_nonneg

/-- info: 'SparseHamiltonian.GateBitBudget.bitH_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.bitH_nonneg

/-- info: 'SparseHamiltonian.GateBitBudget.log_le_logb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.log_le_logb

/-- info: 'SparseHamiltonian.GateBitBudget.clog_ceil_le_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.clog_ceil_le_nat

/-- info: 'SparseHamiltonian.GateBitBudget.clog_ceil_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.clog_ceil_le

/-- info: 'SparseHamiltonian.GateBitBudget.clog_ceil_le_logb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.clog_ceil_le_logb

/-- info: 'SparseHamiltonian.GateBitBudget.logb_two_pow_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.logb_two_pow_mul_pow

/-- info: 'SparseHamiltonian.GateBitBudget.logb_le_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.logb_le_mul_pow

/-- info: 'SparseHamiltonian.GateBitBudget.nat_le_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.nat_le_mul_pow

/-- info: 'SparseHamiltonian.GateBitBudget.clog_le_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.clog_le_mul_pow

/-- info: 'SparseHamiltonian.GateBitBudget.nat_le_logb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.nat_le_logb

/-- info: 'SparseHamiltonian.GateBitBudget.cube_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.cube_le

/-- info: 'SparseHamiltonian.GateBitBudget.budget_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.budget_mono

/-! ### The public scales and the register words -/

/-- info: 'SparseHamiltonian.GateBitBudget.one_le_mul_eta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.one_le_mul_eta

/-- info: 'SparseHamiltonian.GateBitBudget.one_le_mul_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.one_le_mul_theta

/-- info: 'SparseHamiltonian.GateBitBudget.gam_inv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.gam_inv_le

/-- info: 'SparseHamiltonian.GateBitBudget.gammaOf_inv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.gammaOf_inv_le

/-- info: 'SparseHamiltonian.GateBitBudget.logb_inv_gammaOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.logb_inv_gammaOf_le

/-- info: 'SparseHamiltonian.GateBitBudget.one_le_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.one_le_radius

/-- info: 'SparseHamiltonian.GateBitBudget.rho_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.rho_le

/-- info: 'SparseHamiltonian.GateBitBudget.one_le_mul_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.one_le_mul_rho

/-- info: 'SparseHamiltonian.GateBitBudget.step_inv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.step_inv_le

/-- info: 'SparseHamiltonian.GateBitBudget.four_div_step_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.four_div_step_le

/-- info: 'SparseHamiltonian.GateBitBudget.sqrt_le_self_of_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.sqrt_le_self_of_one_le

/-- info: 'SparseHamiltonian.GateBitBudget.kap_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.kap_le

/-- info: 'SparseHamiltonian.GateBitBudget.kap_inv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.kap_inv_le

/-- info: 'SparseHamiltonian.GateBitBudget.shape_one_le_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.shape_one_le_X

/-- info: 'SparseHamiltonian.GateBitBudget.shape_q_le_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.shape_q_le_X

/-- info: 'SparseHamiltonian.GateBitBudget.shape_div_le_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.shape_div_le_X

/-- info: 'SparseHamiltonian.GateBitBudget.shape_inv_precision_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.shape_inv_precision_le

/-- info: 'SparseHamiltonian.GateBitBudget.shape_ell_le_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.shape_ell_le_X

/-- info: 'SparseHamiltonian.GateBitBudget.shape_ell_le_logb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.shape_ell_le_logb

/-- info: 'SparseHamiltonian.GateBitBudget.logb_X_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.logb_X_two_le

/-- info: 'SparseHamiltonian.GateBitBudget.r_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.r_word

/-- info: 'SparseHamiltonian.GateBitBudget.l_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.l_word

/-- info: 'SparseHamiltonian.GateBitBudget.m_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.m_word

/-- info: 'SparseHamiltonian.GateBitBudget.k_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.k_word

/-- info: 'SparseHamiltonian.GateBitBudget.inv_zeta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.inv_zeta_le

/-- info: 'SparseHamiltonian.GateBitBudget.F_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.F_word

/-- info: 'SparseHamiltonian.GateBitBudget.nOf_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.nOf_word

/-- info: 'SparseHamiltonian.GateBitBudget.kap_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.kap_words

/-! ### The per-call cost and the gate counts of the binary simulations -/

/-- info: 'SparseHamiltonian.GateBitBudget.cordic_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.cordic_words

/-- info: 'SparseHamiltonian.GateBitBudget.privGates_binary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.privGates_binary

/-- info: 'SparseHamiltonian.GateBitBudget.privGates_binaryT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.privGates_binaryT

/-- info: 'SparseHamiltonian.GateBitBudget.hs_zeta_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.hs_zeta_spec

/-- info: 'SparseHamiltonian.GateBitBudget.le_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.le_shape

/-- info: 'SparseHamiltonian.GateBitBudget.hs_zeta_shape_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.hs_zeta_shape_spec

/-- info: 'SparseHamiltonian.GateBitBudget.hs_zeta_shape_specT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.hs_zeta_shape_specT

/-- info: 'SparseHamiltonian.GateBitBudget.cordicWords_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.cordicWords_le

/-- info: 'SparseHamiltonian.GateBitBudget.hs_final_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.hs_final_arith

/-- info: 'SparseHamiltonian.GateBitBudget.simM_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.simM_word

/-- info: 'SparseHamiltonian.GateBitBudget.simR_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.simR_word

/-- info: 'SparseHamiltonian.GateBitBudget.hs_gates_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.hs_gates_le

/-- info: 'SparseHamiltonian.GateBitBudget.hs_gatesT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBitBudget.hs_gatesT_le
