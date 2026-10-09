import GateEfficientSigned.Basic
import GateEfficientSigned.Binary
import GateEfficientSigned.Synth
import GateEfficientSigned.Zero
import GateEfficientSigned.NonVacuity

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 2 lemmas, whose reports list a
subset of these three axioms (the two's complement word lemmas `twos_inl_oneWord`
and `twos_inr_oneWord`). The audits cover every theorem of the library of Theorem
`hs:thm:gates` for every real time from binary sparse oracles, beginning with the
native endpoint `binary_simulation_signed` and ending with the signed circuits.
-/

/-! ### Theorem `hs:thm:gates` from binary sparse data for every real time -/

/-- info: 'SparseHamiltonian.GateSigned.binary_simulation_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.binary_simulation_signed

/-- info: 'SparseHamiltonian.GateSigned.binary_simulation_budget_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.binary_simulation_budget_signed

/-- info: 'SparseHamiltonian.GateSigned.binary_simulation_bits_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.binary_simulation_bits_signed

/-- info: 'SparseHamiltonian.GateSigned.binary_simulation_bits_qubits_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.binary_simulation_bits_qubits_signed

/-! ### Theorem `hs:thm:gates` over a finite gate set for every real time -/

/-- info: 'SparseHamiltonian.GateSigned.binary_simulation_synth_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.binary_simulation_synth_signed

/-- info: 'SparseHamiltonian.GateSigned.binary_simulation_budget_synth_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.binary_simulation_budget_synth_signed

/-- info: 'SparseHamiltonian.GateSigned.binary_simulation_budget_synth_bits_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.binary_simulation_budget_synth_bits_signed

/-- info: 'SparseHamiltonian.GateSigned.binary_simulation_budget_synth_bits_qubits_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.binary_simulation_budget_synth_bits_qubits_signed

/-! ### The identity circuit at `t = 0` -/

/-- info: 'SparseHamiltonian.GateSigned.binary_simulation_signed_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.binary_simulation_signed_zero

/-- info: 'SparseHamiltonian.GateSigned.binary_simulation_budget_signed_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.binary_simulation_budget_signed_zero

/-- info: 'SparseHamiltonian.GateSigned.binary_simulation_synth_signed_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.binary_simulation_synth_signed_zero

/-- info: 'SparseHamiltonian.GateSigned.binary_simulation_budget_synth_signed_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.binary_simulation_budget_synth_signed_zero

/-! ### Non-vacuity at a negative time -/

/-- info: 'SparseHamiltonian.GateSigned.twos_inl_oneWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.twos_inl_oneWord

/-- info: 'SparseHamiltonian.GateSigned.twos_inr_oneWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.twos_inr_oneWord

/-- info: 'SparseHamiltonian.GateSigned.gauss_oneWord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.gauss_oneWord

/-- info: 'SparseHamiltonian.GateSigned.wordData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.wordData_matrix

/-- info: 'SparseHamiltonian.GateSigned.wordData_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.wordData_range

/-- info: 'SparseHamiltonian.GateSigned.matrixOperator_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.matrixOperator_one

/-- info: 'SparseHamiltonian.GateSigned.wordData_hamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.wordData_hamiltonian

/-- info: 'SparseHamiltonian.GateSigned.exp_smul_one_reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.exp_smul_one_reg

/-- info: 'SparseHamiltonian.GateSigned.error_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.error_sep

/-- info: 'SparseHamiltonian.GateSigned.one_lt_norm_exp_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.one_lt_norm_exp_sub

/-- info: 'SparseHamiltonian.GateSigned.binarySim_error_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.binarySim_error_ge

/-- info: 'SparseHamiltonian.GateSigned.hs_signed_all_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.hs_signed_all_hyps

/-! ### Signed circuits -/

/-- info: 'SparseHamiltonian.GateSigned.signed_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.signed_of_nonneg

/-- info: 'SparseHamiltonian.GateSigned.signed_of_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.signed_of_neg

/-- info: 'SparseHamiltonian.GateSigned.nGatesN_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.nGatesN_signed

/-- info: 'SparseHamiltonian.GateSigned.nCallsN_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.nCallsN_signed

/-- info: 'SparseHamiltonian.GateSigned.valid_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.valid_signed

/-- info: 'SparseHamiltonian.GateSigned.err_signed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.err_signed

/-- info: 'SparseHamiltonian.GateSigned.qlift_matrixOperator_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.qlift_matrixOperator_self

/-- info: 'SparseHamiltonian.GateSigned.binarySimSigned_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.binarySimSigned_of_nonneg

/-- info: 'SparseHamiltonian.GateSigned.binarySimSigned_of_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.binarySimSigned_of_neg

/-- info: 'SparseHamiltonian.GateSigned.nGatesN_binarySimSigned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.nGatesN_binarySimSigned

/-- info: 'SparseHamiltonian.GateSigned.nCallsN_binarySimSigned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSigned.nCallsN_binarySimSigned
