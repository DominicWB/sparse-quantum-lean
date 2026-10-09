import AdaptiveUnitaryLowerBound.Statements

set_option autoImplicit false

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem of the library for the
unitary `Ω(√N)` lower bound against adaptive algorithms and controlled calls (41 theorems), in
module order. Every report lists `propext`, `Classical.choice` and `Quot.sound`. -/

/-! ### Entry oracles as phase oracles and the pair observable (`Oracles`, `Observable`) -/

/-! #### `AdaptiveUnitaryLowerBound.Oracles` -/

/-- info: 'AdaptiveUnitaryLowerBound.Oracles.lookup_eq_phase_marked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Oracles.lookup_eq_phase_marked

/-- info: 'AdaptiveUnitaryLowerBound.Oracles.entry_oracle_eq_phase_marked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Oracles.entry_oracle_eq_phase_marked

/-- info: 'AdaptiveUnitaryLowerBound.Oracles.implementsOn_phase_of_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Oracles.implementsOn_phase_of_entry

/-- info: 'AdaptiveUnitaryLowerBound.Oracles.implementsOn_phase_of_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Oracles.implementsOn_phase_of_lookup

/-! #### `AdaptiveUnitaryLowerBound.Observable` -/

/-- info: 'AdaptiveUnitaryLowerBound.Observable.isSelfAdjoint_pairObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Observable.isSelfAdjoint_pairObs

/-- info: 'AdaptiveUnitaryLowerBound.Observable.norm_pairObs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Observable.norm_pairObs_le

/-- info: 'AdaptiveUnitaryLowerBound.Observable.pairObs_expect_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Observable.pairObs_expect_left

/-- info: 'AdaptiveUnitaryLowerBound.Observable.pairObs_expect_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Observable.pairObs_expect_right

/-! ### Unstructured search for adaptive protocols (`Kernel`, `Correlation`, `Accuracy`) -/

/-! #### `AdaptiveUnitaryLowerBound.Kernel` -/

/-- info: 'AdaptiveUnitaryLowerBound.Kernel.treeKernel_re_le_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Kernel.treeKernel_re_le_of_gap

/-- info: 'AdaptiveUnitaryLowerBound.Kernel.tree_search_count_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Kernel.tree_search_count_ge

/-- info: 'AdaptiveUnitaryLowerBound.Kernel.tree_search_count_ge_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Kernel.tree_search_count_ge_of_gap

/-! #### `AdaptiveUnitaryLowerBound.Correlation` -/

/-- info: 'AdaptiveUnitaryLowerBound.Correlation.tree_bias_of_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Correlation.tree_bias_of_mass

/-- info: 'AdaptiveUnitaryLowerBound.Correlation.norm_outObs_pairObs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Correlation.norm_outObs_pairObs_le

/-- info: 'AdaptiveUnitaryLowerBound.Correlation.pair_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Correlation.pair_gap

/-! #### `AdaptiveUnitaryLowerBound.Accuracy` -/

/-- info: 'AdaptiveUnitaryLowerBound.Accuracy.tree_search_count_ge_of_accurate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Accuracy.tree_search_count_ge_of_accurate

/-! ### Corollary `hs:cor:unitary`, lower half, for adaptive algorithms and controlled calls
(`Theorem`, `Entry`, `Lookup`) -/

/-! #### `AdaptiveUnitaryLowerBound.Theorem` -/

/-- info: 'AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_tree

/-- info: 'AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_calls_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_calls_tree

/-- info: 'AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_program

/-- info: 'AdaptiveUnitaryLowerBound.Theorem.program_search_count_ge_of_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Theorem.program_search_count_ge_of_error

/-- info: 'AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_program_of_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_program_of_error

/-- info: 'AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_calls_program_of_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Theorem.implementation_count_ge_calls_program_of_error

/-! #### `AdaptiveUnitaryLowerBound.Entry` -/

/-- info: 'AdaptiveUnitaryLowerBound.Entry.entryOracles_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Entry.entryOracles_unitary

/-- info: 'AdaptiveUnitaryLowerBound.Entry.one_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Entry.one_isometry

/-- info: 'AdaptiveUnitaryLowerBound.Entry.entryOracles_implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Entry.entryOracles_implementsOn

/-- info: 'AdaptiveUnitaryLowerBound.Entry.le_nine_of_two_thirds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Entry.le_nine_of_two_thirds

/-- info: 'AdaptiveUnitaryLowerBound.Entry.heralded_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Entry.heralded_tree

/-- info: 'AdaptiveUnitaryLowerBound.Entry.unheralded_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Entry.unheralded_tree

/-- info: 'AdaptiveUnitaryLowerBound.Entry.heralded_calls_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Entry.heralded_calls_tree

/-- info: 'AdaptiveUnitaryLowerBound.Entry.unheralded_calls_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Entry.unheralded_calls_tree

/-- info: 'AdaptiveUnitaryLowerBound.Entry.calls_program_of_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Entry.calls_program_of_error

/-! #### `AdaptiveUnitaryLowerBound.Lookup` -/

/-- info: 'AdaptiveUnitaryLowerBound.Lookup.entry_count_ge_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Lookup.entry_count_ge_tree

/-- info: 'AdaptiveUnitaryLowerBound.Lookup.entry_count_ge_calls_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Lookup.entry_count_ge_calls_tree

/-- info: 'AdaptiveUnitaryLowerBound.Lookup.entry_count_ge_program_of_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Lookup.entry_count_ge_program_of_error

/-- info: 'AdaptiveUnitaryLowerBound.Lookup.entry_count_ge_calls_program_of_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.Lookup.entry_count_ge_calls_program_of_error

/-! ### Non-vacuity: the released circuit as an adaptive protocol (`NonVacuity`) -/

/-! #### `AdaptiveUnitaryLowerBound.NonVacuity` -/

/-- info: 'AdaptiveUnitaryLowerBound.NonVacuity.single_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.NonVacuity.single_hyps

/-- info: 'AdaptiveUnitaryLowerBound.NonVacuity.released' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.NonVacuity.released

/-- info: 'AdaptiveUnitaryLowerBound.NonVacuity.released_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.NonVacuity.released_tree

/-- info: 'AdaptiveUnitaryLowerBound.NonVacuity.count_plainLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.NonVacuity.count_plainLift

/-- info: 'AdaptiveUnitaryLowerBound.NonVacuity.plain_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.NonVacuity.plain_calls

/-- info: 'AdaptiveUnitaryLowerBound.NonVacuity.released_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.NonVacuity.released_calls

/-- info: 'AdaptiveUnitaryLowerBound.NonVacuity.released_calls_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveUnitaryLowerBound.NonVacuity.released_calls_bounds
