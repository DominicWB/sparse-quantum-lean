import GateEfficientRemarks.AbstractTransfer
import GateEfficientRemarks.Abstract
import GateEfficientRemarks.AbstractScalar
import GateEfficientRemarks.AbstractIsometry
import GateEfficientRemarks.AbstractBinary
import GateEfficientRemarks.QubitWords
import GateEfficientRemarks.Qubits
import GateEfficientRemarks.QubitsSynth
import GateEfficientRemarks.ZeroBinary
import GateEfficientRemarks.ZeroSynth
import GateEfficientRemarks.ZeroSynthBinary
import GateEfficientRemarks.ODE.Absorb
import GateEfficientRemarks.ODE.Poly
import GateEfficientRemarks.ODE.PolySynth
import GateEfficientRemarks.ODE.SynthZero
import GateEfficientRemarks.ODE.SynthCombined
import GateEfficientRemarks.ODE.SynthBinary
import GateEfficientRemarks.ODE.SynthBinaryTime
import GateEfficientRemarks.ODE.MinRegister
import GateEfficientRemarks.ODE.ZeroBudget
import GateEfficientRemarks.ODE.ZeroBudgetTime
import GateEfficientRemarks.ODE.ZeroTrials
import GateEfficientRemarks.ODE.ZeroTrialsTime
import GateEfficientRemarks.ODE.ZeroWords
import GateEfficientRemarks.ODE.ZeroWordsSum
import GateEfficientRemarks.ODE.ZeroReleased
import GateEfficientRemarks.ODE.ZeroWordsT
import GateEfficientRemarks.ODE.ZeroReleasedTime
import GateEfficientRemarks.ODE.ZeroReleasedTrials
import GateEfficientRemarks.ODE.ZeroReleasedTrialsTime
import GateEfficientRemarks.ODE.PolyNonneg
import GateEfficientRemarks.ODE.NonVacuity

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`. The audits cover every theorem of the library
of the remarks on the gate-level theorems, beginning with Lemma `hs:lem:abstract` for every real
time (`abstract_simulation`) and for an arbitrary isometry on a finite-dimensional system
(`abstract_simulation_isometry`), and continuing with the ODE part (namespace
`SparseHamiltonian.GateRemarks.ODE`) from the section on source costs polynomial in `𝔟`.
-/

/-! ### Lemma `hs:lem:abstract`: the general boundary-resolvent simulation lemma -/

/-- info: 'SparseHamiltonian.GateRemarks.abstract_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.abstract_simulation

/-- info: 'SparseHamiltonian.GateRemarks.abstract_simulation_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.abstract_simulation_isometry

/-- info: 'SparseHamiltonian.GateRemarks.isGate_flipD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.isGate_flipD

/-- info: 'SparseHamiltonian.GateRemarks.isUJ_flipD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.isUJ_flipD

/-- info: 'SparseHamiltonian.GateRemarks.isPriv_flipD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.isPriv_flipD

/-- info: 'SparseHamiltonian.GateRemarks.nGates_flipDs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.nGates_flipDs

/-- info: 'SparseHamiltonian.GateRemarks.nUJ_flipDs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.nUJ_flipDs

/-- info: 'SparseHamiltonian.GateRemarks.nPriv_flipDs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.nPriv_flipDs

/-- info: 'SparseHamiltonian.GateRemarks.valid_flipDs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.valid_flipDs

/-- info: 'SparseHamiltonian.GateRemarks.run_flipDs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.run_flipDs

/-- info: 'SparseHamiltonian.GateRemarks.resolvent_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.resolvent_adjoint

/-- info: 'SparseHamiltonian.GateRemarks.transfer_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.transfer_unitary

/-- info: 'SparseHamiltonian.GateRemarks.transfer_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.transfer_right

/-- info: 'SparseHamiltonian.GateRemarks.transfer_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.transfer_left

/-- info: 'SparseHamiltonian.GateRemarks.transfer_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.transfer_norm

/-- info: 'SparseHamiltonian.GateRemarks.transfer_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.transfer_boundary

/-- info: 'SparseHamiltonian.GateRemarks.transfer_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.transfer_moment

/-- info: 'SparseHamiltonian.GateRemarks.transfer_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.transfer_endpoint

/-- info: 'SparseHamiltonian.GateRemarks.re_inner_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.re_inner_moment

/-- info: 'SparseHamiltonian.GateRemarks.adjoint_comp_self_le_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.adjoint_comp_self_le_iff

/-- info: 'SparseHamiltonian.GateRemarks.second_moment_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.second_moment_iff

/-- info: 'SparseHamiltonian.GateRemarks.one_add_log_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.one_add_log_le

/-- info: 'SparseHamiltonian.GateRemarks.abstract_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.abstract_cost_le

/-- info: 'SparseHamiltonian.GateRemarks.exponent_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.exponent_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.exponent_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.exponent_neg

/-- info: 'SparseHamiltonian.GateRemarks.smul_one_comp_smul_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.smul_one_comp_smul_one

/-- info: 'SparseHamiltonian.GateRemarks.abstract_simulation_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.abstract_simulation_scalar

/-- info: 'SparseHamiltonian.GateRemarks.exists_unitary_extension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.exists_unitary_extension

/-- info: 'SparseHamiltonian.GateRemarks.interface_binary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.interface_binary

/-- info: 'SparseHamiltonian.GateRemarks.abstract_simulation_binary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.abstract_simulation_binary

/-! ### Theorem `hs:thm:gates`: the qubits of `hs:eq:gate-total` in the bit lengths -/

/-- info: 'SparseHamiltonian.GateRemarks.card_binary_register' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.card_binary_register

/-- info: 'SparseHamiltonian.GateRemarks.card_binary_registerT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.card_binary_registerT

/-- info: 'SparseHamiltonian.GateRemarks.cordic_register_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.cordic_register_le

/-- info: 'SparseHamiltonian.GateRemarks.half_le_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.half_le_shape

/-- info: 'SparseHamiltonian.GateRemarks.binary_register_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.binary_register_le

/-- info: 'SparseHamiltonian.GateRemarks.binary_registerT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.binary_registerT_le

/-- info: 'SparseHamiltonian.GateRemarks.cordic_A_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.cordic_A_ge

/-- info: 'SparseHamiltonian.GateRemarks.nOf_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.nOf_ge

/-- info: 'SparseHamiltonian.GateRemarks.binArith_A_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.binArith_A_ge

/-- info: 'SparseHamiltonian.GateRemarks.binary_simulation_bits_qubits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.binary_simulation_bits_qubits

/-- info: 'SparseHamiltonian.GateRemarks.binary_time_simulation_bits_qubits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.binary_time_simulation_bits_qubits

/-- info: 'SparseHamiltonian.GateRemarks.binary_simulation_budget_synth_bits_qubits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.binary_simulation_budget_synth_bits_qubits

/-- info: 'SparseHamiltonian.GateRemarks.binary_time_simulation_budget_synth_bits_qubits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.binary_time_simulation_budget_synth_bits_qubits

/-! ### Theorem `hs:thm:gates` at zero time: binary sparse data -/

/-- info: 'SparseHamiltonian.GateRemarks.binary_simulation_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.binary_simulation_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.binary_simulation_budget_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.binary_simulation_budget_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.binary_time_simulation_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.binary_time_simulation_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.binary_time_simulation_budget_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.binary_time_simulation_budget_nonneg

/-! ### Theorem `hs:thm:gates` at zero time over a finite gate set -/

/-- info: 'SparseHamiltonian.GateRemarks.synthBudget_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.synthBudget_nil

/-- info: 'SparseHamiltonian.GateRemarks.native_simulation_synth_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.native_simulation_synth_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.native_simulation_signed_synth_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.native_simulation_signed_synth_zero

/-- info: 'SparseHamiltonian.GateRemarks.native_time_simulation_synth_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.native_time_simulation_synth_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.binary_simulation_synth_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.binary_simulation_synth_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.binary_time_simulation_synth_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.binary_time_simulation_synth_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.binary_simulation_budget_synth_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.binary_simulation_budget_synth_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.binary_time_simulation_budget_synth_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.binary_time_simulation_budget_synth_nonneg

/-! ### Theorem `ode:thm:gates`: source costs polynomial in `𝔟` -/

/-- info: 'SparseHamiltonian.GateRemarks.ODE.nonneg_of_le_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.nonneg_of_le_mul_pow

/-- info: 'SparseHamiltonian.GateRemarks.ODE.gates_absorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.gates_absorb

/-- info: 'SparseHamiltonian.GateRemarks.ODE.space_absorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.space_absorb

/-- info: 'SparseHamiltonian.GateRemarks.ODE.log_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.log_succ_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.synth_factor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.synth_factor_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.synth_absorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.synth_absorb

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_poly

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_poly

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_poly_user' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_poly_user

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_trials_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_trials_poly

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_trials_poly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_trials_poly

/-! ### Zero time or a known zero generator, every trial synthesised: native gates -/

/-- info: 'SparseHamiltonian.GateRemarks.ODE.native_ode_solver_synth_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.native_ode_solver_synth_zero

/-- info: 'SparseHamiltonian.GateRemarks.ODE.native_ode_time_solver_synth_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.native_ode_time_solver_synth_zero

/-- info: 'SparseHamiltonian.GateRemarks.ODE.native_ode_solver_synth_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.native_ode_solver_synth_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.ODE.native_ode_time_solver_synth_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.native_ode_time_solver_synth_nonneg

/-! ### Zero time or a known zero generator, every trial synthesised: binary data -/

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_solver_synth_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_solver_synth_zero

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_solver_synth_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_solver_synth_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_time_solver_synth_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_time_solver_synth_zero

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_time_solver_synth_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_time_solver_synth_nonneg

/-! ### Zero time or a known zero generator: `ode:eq:gate-main`, `ode:eq:gate-space` in `𝔟` -/

/-- info: 'SparseHamiltonian.GateRemarks.ODE.card_AW_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.card_AW_min

/-- info: 'SparseHamiltonian.GateRemarks.ODE.card_XW_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.card_XW_min

/-- info: 'SparseHamiltonian.GateRemarks.ODE.card_MinW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.card_MinW

/-- info: 'SparseHamiltonian.GateRemarks.ODE.tested_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.tested_min

/-- info: 'SparseHamiltonian.GateRemarks.ODE.card_MinSW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.card_MinSW

/-- info: 'SparseHamiltonian.GateRemarks.ODE.tested_minS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.tested_minS

/-- info: 'SparseHamiltonian.GateRemarks.ODE.one_le_qOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.one_le_qOf

/-- info: 'SparseHamiltonian.GateRemarks.ODE.qOf_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.qOf_zero

/-- info: 'SparseHamiltonian.GateRemarks.ODE.logb_X_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.logb_X_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.ODE.kx_le_bitB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.kx_le_bitB

/-- info: 'SparseHamiltonian.GateRemarks.ODE.kx_add_le_bitB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.kx_add_le_bitB

/-- info: 'SparseHamiltonian.GateRemarks.ODE.log_le_bitB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.log_le_bitB

/-- info: 'SparseHamiltonian.GateRemarks.ODE.log_trial_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.log_trial_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.log_trialT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.log_trialT_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.lin_le_cube' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.lin_le_cube

/-- info: 'SparseHamiltonian.GateRemarks.ODE.lin_le_cube_space' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.lin_le_cube_space

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_bits_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_bits_zero

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_bits_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_bits_zero

/-! ### Zero time or a known zero generator: the budgets in `𝔟` over a finite gate set -/

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_trials_bits_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_trials_bits_zero

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_trials_bits_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_trials_bits_zero

/-! ### Zero time or a known zero generator: the released register, every `T ≥ 0` -/

/-- info: 'SparseHamiltonian.GateRemarks.ODE.env_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.env_one_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.env_q_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.env_q_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.env_div_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.env_div_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.env_inv_precision_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.env_inv_precision_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.env_ell_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.env_ell_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.env_ell_le_logb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.env_ell_le_logb

/-- info: 'SparseHamiltonian.GateRemarks.ODE.env_radius_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.env_radius_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.width_le_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.width_le_of

/-- info: 'SparseHamiltonian.GateRemarks.ODE.r_word_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.r_word_of

/-- info: 'SparseHamiltonian.GateRemarks.ODE.J_le_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.J_le_of

/-- info: 'SparseHamiltonian.GateRemarks.ODE.kap_words_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.kap_words_of

/-- info: 'SparseHamiltonian.GateRemarks.ODE.hasBits_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.hasBits_one

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_TlamD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_TlamD

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_TlamHD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_TlamHD

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_tau

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_m' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_m

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_k

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_degree

/-- info: 'SparseHamiltonian.GateRemarks.ODE.width_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.width_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_r_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_r_word

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_J_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_J_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_kap_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_kap_words

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_words_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_words_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.card_NW_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.card_NW_eq

/-- info: 'SparseHamiltonian.GateRemarks.ODE.card_NW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.card_NW_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.count_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.count_arith

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_count_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_count_zero

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_bits_zero_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_bits_zero_released

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_bits_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_bits_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.ODE.logBudget_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.logBudget_two_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.bitB_le_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.bitB_le_succ

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zeroT_TlamD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zeroT_TlamD

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zeroT_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zeroT_tau

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zeroT_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zeroT_degree

/-- info: 'SparseHamiltonian.GateRemarks.ODE.widthT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.widthT_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zeroT_r_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zeroT_r_word

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zeroT_J_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zeroT_J_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zeroT_kap_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zeroT_kap_words

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_wordsT_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_wordsT_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.card_TNW_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.card_TNW_eq

/-- info: 'SparseHamiltonian.GateRemarks.ODE.card_TNW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.card_TNW_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.count_arithT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.count_arithT

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_count_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_count_zero

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_bits_zero_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_bits_zero_released

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_bits_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_bits_nonneg

/-! ### Zero time or a known zero generator: the released trial register, every `T ≥ 0` -/

/-- info: 'SparseHamiltonian.GateRemarks.ODE.trial_budget_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.trial_budget_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.card_trial_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.card_trial_released

/-- info: 'SparseHamiltonian.GateRemarks.ODE.trial_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.trial_count_le

/-- info: 'SparseHamiltonian.GateRemarks.ODE.prepBound_le_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.prepBound_le_zero

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_gates_le_prepBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_gates_le_prepBound

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_trials_bits_zero_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_trials_bits_zero_released

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_trials_bits_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_trials_bits_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.ODE.card_trialT_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.card_trialT_released

/-- info: 'SparseHamiltonian.GateRemarks.ODE.prepBoundT_le_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.prepBoundT_le_zero

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_gates_le_prepBoundT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_gates_le_prepBoundT

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_trials_bits_zero_released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_trials_bits_zero_released

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_trials_bits_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_trials_bits_nonneg

/-! ### Source costs polynomial in `𝔟` for every `T ≥ 0` -/

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_poly_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_poly_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_poly_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_poly_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_poly_user_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_poly_user_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_trials_poly_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_budget_trials_poly_nonneg

/-- info: 'SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_trials_poly_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.binary_ode_time_budget_trials_poly_nonneg

/-! ### Zero time or a known zero generator: satisfiability of the hypotheses -/

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zeroPub_ok0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zeroPub_ok0

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zeroPub_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zeroPub_zero

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zeroPubT_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zeroPubT_mesh

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zeroPubT_ok0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zeroPubT_ok0

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zeroPubT_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zeroPubT_zero

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_all_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_all_hyps

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_time_all_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_time_all_hyps

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zeroPubZ_q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zeroPubZ_q

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zeroPubZ_nu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zeroPubZ_nu

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zeroPubZ_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zeroPubZ_spec

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zeroPubZ_ok0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zeroPubZ_ok0

/-- info: 'SparseHamiltonian.GateRemarks.ODE.approx_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.approx_empty

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_instance_all_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_instance_all_hyps

/-- info: 'SparseHamiltonian.GateRemarks.ODE.zero_instance_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRemarks.ODE.zero_instance_outcome
