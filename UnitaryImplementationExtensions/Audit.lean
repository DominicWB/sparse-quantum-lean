import UnitaryImplementationExtensions.Statements

set_option autoImplicit false

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem of the black-box
unitary-implementation extensions (76 theorems) and every `Prop`-valued field of the structure
`ApproxData.Data` (3 fields), in module order. Every report lists `propext`, `Classical.choice`
and `Quot.sound`, except for 1 lemma, `SearchFamily.searchTable_eq_one_iff`, whose report lists
a subset of these three axioms. -/

/-! ### Inexact entry tables (`ApproxData`, `ApproxNorm`, `ApproxOracle`) -/

/-! #### `UnitaryImplementationExtensions.ApproxData` -/

/-- info: 'UnitaryImplementationExtensions.ApproxData.Data.target_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.Data.target_unitary

/-- info: 'UnitaryImplementationExtensions.ApproxData.Data.scale_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.Data.scale_pos

/-- info: 'UnitaryImplementationExtensions.ApproxData.Data.decode_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.Data.decode_bound

/-- info: 'UnitaryImplementationExtensions.ApproxData.ofExact_represented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.ofExact_represented

/-- info: 'UnitaryImplementationExtensions.ApproxData.target_entry_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.target_entry_le_one

/-- info: 'UnitaryImplementationExtensions.ApproxData.dilationMatrix_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.dilationMatrix_eq

/-- info: 'UnitaryImplementationExtensions.ApproxData.target_dilation_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.target_dilation_eq

/-- info: 'UnitaryImplementationExtensions.ApproxData.dilation_hermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.dilation_hermitian

/-- info: 'UnitaryImplementationExtensions.ApproxData.dilation_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.dilation_sub

/-- info: 'UnitaryImplementationExtensions.ApproxData.dilationDecode_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.dilationDecode_bound

/-- info: 'UnitaryImplementationExtensions.ApproxData.dilationDecoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.dilationDecoded

/-- info: 'UnitaryImplementationExtensions.ApproxData.dilationTable_ofExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.dilationTable_ofExact

/-- info: 'UnitaryImplementationExtensions.ApproxData.dilationDecode_ofExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.dilationDecode_ofExact

/-- info: 'UnitaryImplementationExtensions.ApproxData.row_covers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.row_covers

/-- info: 'UnitaryImplementationExtensions.ApproxData.toNative_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.toNative_matrix

/-- info: 'UnitaryImplementationExtensions.ApproxData.toNative_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.toNative_table

/-- info: 'UnitaryImplementationExtensions.ApproxData.toNative_rowOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.toNative_rowOracle

/-- info: 'UnitaryImplementationExtensions.ApproxData.toNative_columnOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.toNative_columnOracle

/-- info: 'UnitaryImplementationExtensions.ApproxData.toNative_ofExact_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxData.toNative_ofExact_matrix

/-! #### `UnitaryImplementationExtensions.ApproxNorm` -/

/-- info: 'UnitaryImplementationExtensions.ApproxNorm.norm_dilation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxNorm.norm_dilation_le

/-- info: 'UnitaryImplementationExtensions.ApproxNorm.star_matrixOperator_dilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxNorm.star_matrixOperator_dilation

/-- info: 'UnitaryImplementationExtensions.ApproxNorm.norm_target_dilation_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxNorm.norm_target_dilation_le_one

/-- info: 'UnitaryImplementationExtensions.ApproxNorm.dilation_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxNorm.dilation_error_le

/-- info: 'UnitaryImplementationExtensions.ApproxNorm.norm_represented_dilation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxNorm.norm_represented_dilation_le

/-! #### `UnitaryImplementationExtensions.ApproxOracle` -/

/-- info: 'UnitaryImplementationExtensions.ApproxOracle.flatEntry_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxOracle.flatEntry_unitary

/-- info: 'UnitaryImplementationExtensions.ApproxOracle.oracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxOracle.oracle_unitary

/-- info: 'UnitaryImplementationExtensions.ApproxOracle.oracle_ofExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxOracle.oracle_ofExact

/-- info: 'UnitaryImplementationExtensions.ApproxOracle.nativeOracle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxOracle.nativeOracle_eq

/-- info: 'UnitaryImplementationExtensions.ApproxOracle.value_routing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxOracle.value_routing

/-- info: 'UnitaryImplementationExtensions.ApproxOracle.flat_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxOracle.flat_row

/-- info: 'UnitaryImplementationExtensions.ApproxOracle.flat_column' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxOracle.flat_column

/-- info: 'UnitaryImplementationExtensions.ApproxOracle.letter_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxOracle.letter_eval

/-- info: 'UnitaryImplementationExtensions.ApproxOracle.compile_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxOracle.compile_eval

/-- info: 'UnitaryImplementationExtensions.ApproxOracle.compile_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.ApproxOracle.compile_count_le

/-! ### Corollary `hs:cor:unitary`: inexact entries and general precision (`Inexact`, `General`) -/

/-! #### `UnitaryImplementationExtensions.Inexact` -/

/-- info: 'UnitaryImplementationExtensions.Inexact.inexactConstant_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.Inexact.inexactConstant_pos

/-- info: 'UnitaryImplementationExtensions.Inexact.inexact_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.Inexact.inexact_budget

/-- info: 'UnitaryImplementationExtensions.Inexact.simulation_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.Inexact.simulation_transfer

/-- info: 'UnitaryImplementationExtensions.Inexact.native_implementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.Inexact.native_implementation

/-- info: 'UnitaryImplementationExtensions.Inexact.implementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.Inexact.implementation

/-- info: 'UnitaryImplementationExtensions.Inexact.reference_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.Inexact.reference_error

/-- info: 'UnitaryImplementationExtensions.Inexact.implementation_ofExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.Inexact.implementation_ofExact

/-! #### `UnitaryImplementationExtensions.General` -/

/-- info: 'UnitaryImplementationExtensions.General.exactConstant_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.General.exactConstant_pos

/-- info: 'UnitaryImplementationExtensions.General.exact_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.General.exact_budget

/-- info: 'UnitaryImplementationExtensions.General.oracle_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.General.oracle_quarter

/-- info: 'UnitaryImplementationExtensions.General.input_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.General.input_quarter

/-- info: 'UnitaryImplementationExtensions.General.implementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.General.implementation

/-- info: 'UnitaryImplementationExtensions.General.reference_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.General.reference_error

/-! ### Entry lookups as phase oracles (`PhaseBridge`, `LiftPhase`) -/

/-! #### `UnitaryImplementationExtensions.PhaseBridge` -/

/-- info: 'UnitaryImplementationExtensions.PhaseBridge.phase_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.PhaseBridge.phase_map

/-- info: 'UnitaryImplementationExtensions.PhaseBridge.bitFlip_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.PhaseBridge.bitFlip_apply

/-- info: 'UnitaryImplementationExtensions.PhaseBridge.addressIndicator_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.PhaseBridge.addressIndicator_apply

/-- info: 'UnitaryImplementationExtensions.PhaseBridge.indicator_flip_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.PhaseBridge.indicator_flip_apply

/-- info: 'UnitaryImplementationExtensions.PhaseBridge.indicator_mul_bitFlip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.PhaseBridge.indicator_mul_bitFlip

/-- info: 'UnitaryImplementationExtensions.PhaseBridge.indicator_flip_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.PhaseBridge.indicator_flip_mul_self

/-- info: 'UnitaryImplementationExtensions.PhaseBridge.indicator_flip_mul_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.PhaseBridge.indicator_flip_mul_of_ne

/-- info: 'UnitaryImplementationExtensions.PhaseBridge.lookup_eq_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.PhaseBridge.lookup_eq_phase

/-! #### `UnitaryImplementationExtensions.LiftPhase` -/

/-- info: 'UnitaryImplementationExtensions.LiftPhase.lift_eq_liftStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.LiftPhase.lift_eq_liftStar

/-- info: 'UnitaryImplementationExtensions.LiftPhase.liftHom_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.LiftPhase.liftHom_apply

/-- info: 'UnitaryImplementationExtensions.LiftPhase.oracle_eq_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.LiftPhase.oracle_eq_phase

/-! ### Constant-error search and the `Θ(√N)` statements (`Search`, `SearchFamily`, `LowerBound`) -/

/-! #### `UnitaryImplementationExtensions.Search` -/

/-- info: 'UnitaryImplementationExtensions.Search.schurCert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.Search.schurCert

/-- info: 'UnitaryImplementationExtensions.Search.count_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.Search.count_ge

/-- info: 'UnitaryImplementationExtensions.Search.norm_sub_proj_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.Search.norm_sub_proj_le

/-- info: 'UnitaryImplementationExtensions.Search.norm_sq_proj_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.Search.norm_sq_proj_add

/-- info: 'UnitaryImplementationExtensions.Search.norm_sub_proj_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.Search.norm_sub_proj_apply_le

/-- info: 'UnitaryImplementationExtensions.Search.norm_inner_le_of_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.Search.norm_inner_le_of_near

/-- info: 'UnitaryImplementationExtensions.Search.near_factor_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.Search.near_factor_pos

/-- info: 'UnitaryImplementationExtensions.Search.norm_inner_le_of_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.Search.norm_inner_le_of_success

/-- info: 'UnitaryImplementationExtensions.Search.search_count_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.Search.search_count_ge

/-! #### `UnitaryImplementationExtensions.SearchFamily` -/

/-- info: 'UnitaryImplementationExtensions.SearchFamily.matrixOperator_eq_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.SearchFamily.matrixOperator_eq_reflect

/-- info: 'UnitaryImplementationExtensions.SearchFamily.searchMatrix_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.SearchFamily.searchMatrix_unitary

/-- info: 'UnitaryImplementationExtensions.SearchFamily.searchTable_eq_one_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.SearchFamily.searchTable_eq_one_iff

/-- info: 'UnitaryImplementationExtensions.SearchFamily.searchMatrix_single_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.SearchFamily.searchMatrix_single_zero

/-- info: 'UnitaryImplementationExtensions.SearchFamily.count_ge_of_outputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.SearchFamily.count_ge_of_outputs

/-- info: 'UnitaryImplementationExtensions.SearchFamily.count_ge_of_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.SearchFamily.count_ge_of_phase

/-! #### `UnitaryImplementationExtensions.LowerBound` -/

/-- info: 'UnitaryImplementationExtensions.LowerBound.entry_count_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.LowerBound.entry_count_ge

/-- info: 'UnitaryImplementationExtensions.LowerBound.implementation_count_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.LowerBound.implementation_count_ge

/-- info: 'UnitaryImplementationExtensions.LowerBound.sqrt_le_sqrt_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.LowerBound.sqrt_le_sqrt_two_mul

/-- info: 'UnitaryImplementationExtensions.LowerBound.theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.LowerBound.theta

/-- info: 'UnitaryImplementationExtensions.LowerBound.theta_of_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.LowerBound.theta_of_error

/-- info: 'UnitaryImplementationExtensions.LowerBound.theta_inexact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms UnitaryImplementationExtensions.LowerBound.theta_inexact
