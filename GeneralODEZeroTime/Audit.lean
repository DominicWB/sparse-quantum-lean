import GeneralODEZeroTime.Theorem

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`. The audits cover every theorem of the
library of Theorem `ode:thm:general` at `T = 0` (direct state preparation),
beginning with `general_zero` and with Theorem `ode:thm:general` for every
`T ≥ 0`, `general_nonneg`.
-/

/-! ### Theorem `ode:thm:general` at `T = 0` (direct state preparation) -/

/-- info: 'SparseHamiltonian.GeneralODE.general_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.general_zero

/-- info: 'SparseHamiltonian.GeneralODE.general_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.general_nonneg

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.unitDirection_of_norm_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.unitDirection_of_norm_eq_one

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.oracle_branch_packet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.oracle_branch_packet

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.slotControlled_ketL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.slotControlled_ketL

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.sourceOracle_false_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.sourceOracle_false_embed

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.physicalOracle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.physicalOracle_eq

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.maskedOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.maskedOracle_unitary

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.decoder_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.decoder_apply

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.decoder_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.decoder_isometry

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.norm_decoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.norm_decoder

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.decoder_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.decoder_adjoint_apply

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.query_decoder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.query_decoder

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.prepare_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.prepare_count

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.prepare_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.prepare_cost

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.norm_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.norm_seed

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.protocol_worstCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.protocol_worstCost_le

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.protocol_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.protocol_matrix

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.protocol_forcing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.protocol_forcing

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.protocol_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.protocol_initial

/-- info: 'SparseHamiltonian.GeneralODE.ZeroTime.protocol_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.ZeroTime.protocol_outcome

/-- info: 'SparseHamiltonian.GeneralODE.nonempty_of_norm_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralODE.nonempty_of_norm_seed
