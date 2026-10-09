import UnitaryImplementationPrecision.Exact
import UnitaryImplementationPrecision.Uniform

set_option autoImplicit false

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for two lemmas (`Table.card_opposite` and
`Table.flag_eq_of_not_mem_opposite`), whose reports list only `propext` and `Quot.sound`.
The audits cover every theorem of the library of Corollary `hs:cor:unitary` at every
precision and with inexact entries, beginning with the endpoints for exact entries
(`implementation`, `implementation_with_reference`, `implementation_two_term`) and for
inexact entries (`implementation_inexact`, `implementation_inexact_uniform`,
`implementation_inexact_with_reference`, `implementation_inexact_two_term`).
-/

/-! ### Corollary `hs:cor:unitary` at every precision, with exact and inexact entries -/

/-- info: 'SparseHamiltonian.UnitaryPrecision.implementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.implementation

/-- info: 'SparseHamiltonian.UnitaryPrecision.implementation_with_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.implementation_with_reference

/-- info: 'SparseHamiltonian.UnitaryPrecision.implementation_two_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.implementation_two_term

/-- info: 'SparseHamiltonian.UnitaryPrecision.implementation_inexact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.implementation_inexact

/-- info: 'SparseHamiltonian.UnitaryPrecision.implementation_inexact_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.implementation_inexact_uniform

/-- info: 'SparseHamiltonian.UnitaryPrecision.implementation_inexact_with_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.implementation_inexact_with_reference

/-- info: 'SparseHamiltonian.UnitaryPrecision.implementation_inexact_two_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.implementation_inexact_two_term

/-- info: 'SparseHamiltonian.UnitaryPrecision.native_implementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.native_implementation

/-- info: 'SparseHamiltonian.UnitaryPrecision.reference_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.reference_error

/-- info: 'SparseHamiltonian.UnitaryPrecision.duhamel_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.duhamel_step

/-- info: 'SparseHamiltonian.UnitaryPrecision.native_implementation_inexact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.native_implementation_inexact

/-- info: 'SparseHamiltonian.UnitaryPrecision.reference_error_inexact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.reference_error_inexact

/-- info: 'SparseHamiltonian.UnitaryPrecision.reindex_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.reindex_eval

/-- info: 'SparseHamiltonian.UnitaryPrecision.reindex_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.reindex_count

/-! ### The inexact entry model: tables, their dilation and the entrywise promise -/

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.dilationDecode_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.dilationDecode_bound

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.dilationDecoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.dilationDecoded

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.dilation_hermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.dilation_hermitian

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.dilation_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.dilation_diag

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.ofData_dilationMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.ofData_dilationMatrix

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.ofData_dilationTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.ofData_dilationTable

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.ofData_dilationDecode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.ofData_dilationDecode

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.row_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.row_covers

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.toNative_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.toNative_matrix

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.toNative_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.toNative_table

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.toNative_ofData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.toNative_ofData

/-- info: 'SparseHamiltonian.UnitaryPrecision.unitary_entry_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.unitary_entry_norm_le_one

/-- info: 'SparseHamiltonian.UnitaryPrecision.exactData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.exactData_matrix

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.dilation_row_energy_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.dilation_row_energy_two

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.dilation_column_energy_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.dilation_column_energy_two

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.card_opposite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.card_opposite

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.flag_eq_of_not_mem_opposite' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.flag_eq_of_not_mem_opposite

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.dilation_sub_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.dilation_sub_norm_le

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.dilation_evolution_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.dilation_evolution_error_le

/-! ### Entry-only compilation for tables -/

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.flatEntry_ofData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.flatEntry_ofData

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.flatEntry_eq_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.flatEntry_eq_original

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.flatEntry_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.flatEntry_unitary

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.value_routing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.value_routing

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.flat_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.flat_row

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.flat_column' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.flat_column

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.oracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.oracle_unitary

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.oracle_ofData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.oracle_ofData

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.nativeOracle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.nativeOracle_eq

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.letter_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.letter_eval

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.compile_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.compile_eval

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.compile_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.compile_count

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.compile_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.compile_count_le

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.letter_ofData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.letter_ofData

/-- info: 'SparseHamiltonian.UnitaryPrecision.Table.compile_ofData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.Table.compile_ofData

/-! ### Query-count arithmetic -/

/-- info: 'SparseHamiltonian.UnitaryPrecision.log_two_le_log_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.log_two_le_log_one

/-- info: 'SparseHamiltonian.UnitaryPrecision.log_one_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.log_one_nonneg

/-- info: 'SparseHamiltonian.UnitaryPrecision.exact_shape_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.exact_shape_le

/-- info: 'SparseHamiltonian.UnitaryPrecision.inexact_shape_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.inexact_shape_le

/-- info: 'SparseHamiltonian.UnitaryPrecision.sqrt_le_absorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.sqrt_le_absorb

/-- info: 'SparseHamiltonian.UnitaryPrecision.three_term_le_two_term' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.three_term_le_two_term

/-- info: 'SparseHamiltonian.UnitaryPrecision.three_term_le_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.three_term_le_root

/-- info: 'SparseHamiltonian.UnitaryPrecision.two_term_le_hybrid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.two_term_le_hybrid

/-- info: 'SparseHamiltonian.UnitaryPrecision.duhamel_term_eq_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.duhamel_term_eq_half

/-- info: 'SparseHamiltonian.UnitaryPrecision.card_mul_sq_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.card_mul_sq_le_one

/-- info: 'SparseHamiltonian.UnitaryPrecision.energy_le_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryPrecision.energy_le_four
