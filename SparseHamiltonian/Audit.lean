import SparseHamiltonian.All

/-! Checked axiom dependencies for the published proof declarations. -/

/-- info: 'SparseHamiltonian.SharpFilterSchedule.schedule_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SharpFilterSchedule.schedule_spec

/-- info: 'SparseHamiltonian.SharpGlobalFilter.global_filter_precision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SharpGlobalFilter.global_filter_precision

/-- info: 'SparseHamiltonian.SharpClockQuery.evolution_query_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SharpClockQuery.evolution_query_certificate

/-- info: 'SparseHamiltonian.ImprovedPrecisionBudget.exists_rescaling_for_precision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedPrecisionBudget.exists_rescaling_for_precision

/-- info: 'SparseHamiltonian.ImprovedCayleyMoments.rescaled_boundary_norm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedCayleyMoments.rescaled_boundary_norm_sq_le

/-- info: 'SparseHamiltonian.ExactEdgeCayley.action_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ExactEdgeCayley.action_unitary

/-- info: 'SparseHamiltonian.ExactEdgeCayley.action_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ExactEdgeCayley.action_zero

/-- info: 'SparseHamiltonian.SparseEdgeMoments.native_moment_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SparseEdgeMoments.native_moment_certificate

/-- info: 'SparseHamiltonian.ExactEdgeValueQuery.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ExactEdgeValueQuery.program_intertwines

/-- info: 'SparseHamiltonian.CayleyClockInterface.exists_optimized_implementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CayleyClockInterface.exists_optimized_implementation

/-- info: 'SparseHamiltonian.CayleyClockInterface.query_certificate_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CayleyClockInterface.query_certificate_of_moments

/-- info: 'SparseHamiltonian.OrientedEdgeCayley.inverse_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.OrientedEdgeCayley.inverse_right

/-- info: 'SparseHamiltonian.OrientedEdgeCayley.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.OrientedEdgeCayley.program_intertwines

/-- info: 'SparseHamiltonian.NativeCayleySimulation.exists_precise_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeCayleySimulation.exists_precise_simulation

/-- info: 'SparseHamiltonian.SharpLabeledActiveClockQuery.clockLayer_implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SharpLabeledActiveClockQuery.clockLayer_implementsOn

/-- info: 'SparseHamiltonian.SharpLabeledActiveClockQuery.layer_implementation_query_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SharpLabeledActiveClockQuery.layer_implementation_query_certificate

/-- info: 'SparseHamiltonian.SharpLabeledActiveClockQuery.implementation_query_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SharpLabeledActiveClockQuery.implementation_query_certificate

/-- info: 'SparseHamiltonian.SharpLabeledActiveClockQuery.evolution_query_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SharpLabeledActiveClockQuery.evolution_query_certificate

/-- info: 'SparseHamiltonian.FixedLocatorConjugation.locator_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FixedLocatorConjugation.locator_unitary

/-- info: 'SparseHamiltonian.FixedLocatorConjugation.fixedBoundary_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FixedLocatorConjugation.fixedBoundary_isometry

/-- info: 'SparseHamiltonian.FixedLocatorConjugation.locator_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FixedLocatorConjugation.locator_boundary

/-- info: 'SparseHamiltonian.UnitaryCayleyTransport.moment_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryCayleyTransport.moment_certificate

/-- info: 'SparseHamiltonian.UnitaryCayleyTransport.inverse_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryCayleyTransport.inverse_right

/-- info: 'SparseHamiltonian.UnitaryCayleyTransport.cayleyAction_conjugate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryCayleyTransport.cayleyAction_conjugate

/-- info: 'SparseHamiltonian.FixedNativeCayleySimulation.inverse_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FixedNativeCayleySimulation.inverse_right

/-- info: 'SparseHamiltonian.FixedNativeCayleySimulation.action_eq_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FixedNativeCayleySimulation.action_eq_cayley

/-- info: 'SparseHamiltonian.FixedNativeCayleySimulation.exists_uniform_precise_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FixedNativeCayleySimulation.exists_uniform_precise_simulation

/-- info: 'SparseHamiltonian.NativeWholeProgramMask.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeWholeProgramMask.program_intertwines

/-- info: 'SparseHamiltonian.NativeWholeProgramActive.all_active_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeWholeProgramActive.all_active_certificate

/-- info: 'SparseHamiltonian.NativeCleanConjugation.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeCleanConjugation.program_intertwines

/-- info: 'SparseHamiltonian.NativeSparseWholeProgram.active_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeSparseWholeProgram.active_certificate

/-- info: 'SparseHamiltonian.CleanChronologicalEmbedding.active_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanChronologicalEmbedding.active_intertwines

/-- info: 'SparseHamiltonian.NativeWholeProgramActive.clean_implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeWholeProgramActive.clean_implementsOn

/-- info: 'SparseHamiltonian.FixedNativeCayleyQuery.query_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FixedNativeCayleyQuery.query_certificate

/-- info: 'SparseHamiltonian.OrientedNativeValue.gate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.OrientedNativeValue.gate_unitary

/-- info: 'SparseHamiltonian.OrientedNativeValue.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.OrientedNativeValue.program_intertwines

/-- info: 'SparseHamiltonian.OrientedNativeValue.program_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.OrientedNativeValue.program_cost

/-- info: 'SparseHamiltonian.NativeCayleyProgram.logicalProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeCayleyProgram.logicalProgram_intertwines

/-- info: 'SparseHamiltonian.NativeCayleyProgram.compiledProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeCayleyProgram.compiledProgram_intertwines

/-- info: 'SparseHamiltonian.NativeCayleyProgram.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeCayleyProgram.valid

/-- info: 'SparseHamiltonian.NativeCayleyProgram.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeCayleyProgram.program_intertwines

/-- info: 'SparseHamiltonian.NativeCayleyProgram.program_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeCayleyProgram.program_cost

/-- info: 'SparseHamiltonian.NativeCayleyProgram.program_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeCayleyProgram.program_count

/-- info: 'SparseHamiltonian.OrientedNativeLayout.locatorProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.OrientedNativeLayout.locatorProgram_intertwines

/-- info: 'SparseHamiltonian.FlatMaskedAccess.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FlatMaskedAccess.valid

/-- info: 'SparseHamiltonian.FlatMaskedAccess.flatten_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FlatMaskedAccess.flatten_intertwines

/-- info: 'SparseHamiltonian.SingletonPrivateEncoding.intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SingletonPrivateEncoding.intertwines

/-- info: 'SparseHamiltonian.NativeCayleyProgram.program_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeCayleyProgram.program_unitary

/-- info: 'SparseHamiltonian.NativeCayleyProgram.program_row_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeCayleyProgram.program_row_count

/-- info: 'SparseHamiltonian.NativeCayleyProgram.program_column_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeCayleyProgram.program_column_count

/-- info: 'SparseHamiltonian.NativeCayleyProgram.program_value_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeCayleyProgram.program_value_count

/-- info: 'SparseHamiltonian.NativeCayleyActive.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeCayleyActive.program_intertwines

/-- info: 'SparseHamiltonian.NativeCayleyActive.program_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeCayleyActive.program_cost

/-- info: 'SparseHamiltonian.NativeCayleyActive.implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeCayleyActive.implementsOn

/-- info: 'SparseHamiltonian.ImprovedNativeSimulation.active_implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedNativeSimulation.active_implementsOn

/-- info: 'SparseHamiltonian.ImprovedNativeSimulation.exists_native_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedNativeSimulation.exists_native_simulation

/-- info: 'SparseHamiltonian.ScaledNativeSimulation.exists_positive_time_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ScaledNativeSimulation.exists_positive_time_simulation

/-- info: 'SparseHamiltonian.ScaledNativeSimulation.exists_native_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ScaledNativeSimulation.exists_native_simulation

/-- info: 'SparseHamiltonian.ScaledNativeSimulation.exists_native_simulation_of_spectral_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ScaledNativeSimulation.exists_native_simulation_of_spectral_bound

/-- info: 'SparseHamiltonian.CleanOutputAlignment.completion_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanOutputAlignment.completion_unitary

/-- info: 'SparseHamiltonian.CleanOutputAlignment.align_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanOutputAlignment.align_output

/-- info: 'SparseHamiltonian.CleanOutputAlignment.align_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanOutputAlignment.align_error

/-- info: 'SparseHamiltonian.AlignedMultiOracleProgram.diagonalProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.AlignedMultiOracleProgram.diagonalProgram_eval

/-- info: 'SparseHamiltonian.AlignedMultiOracleProgram.program_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.AlignedMultiOracleProgram.program_error

/-- info: 'SparseHamiltonian.AlignedMultiOracleProgram.exists_aligned_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.AlignedMultiOracleProgram.exists_aligned_program

/-- info: 'SparseHamiltonian.NativeSparseRescaling.normalize_hermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeSparseRescaling.normalize_hermitian

/-- info: 'SparseHamiltonian.NativeSparseRescaling.normalized_row_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeSparseRescaling.normalized_row_energy

/-- info: 'SparseHamiltonian.NativeSparseRescaling.normalized_column_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeSparseRescaling.normalized_column_energy

/-- info: 'SparseHamiltonian.NativeSparseRescaling.exponent_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeSparseRescaling.exponent_cancel

/-- info: 'SparseHamiltonian.NativeSparseRescaling.oracle_normalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeSparseRescaling.oracle_normalize

/-- info: 'SparseHamiltonian.NativeSparseRescaling.input_normalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeSparseRescaling.input_normalize

/-- info: 'SparseHamiltonian.NativeSparseRescaling.output_normalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeSparseRescaling.output_normalize

/-- info: 'SparseHamiltonian.FiniteReferenceLift.norm_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FiniteReferenceLift.norm_error_le

/-- info: 'SparseHamiltonian.FiniteReferenceLift.normalized_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FiniteReferenceLift.normalized_error_le

/-- info: 'SparseHamiltonian.FiniteReferenceLift.lift_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FiniteReferenceLift.lift_isometry

/-- info: 'SparseHamiltonian.FiniteReferenceLift.lift_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FiniteReferenceLift.lift_unitary

/-- info: 'SparseHamiltonian.ImprovedZeroSimulation.zero_time_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedZeroSimulation.zero_time_certificate

/-- info: 'SparseHamiltonian.ImprovedZeroSimulation.zero_energy_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedZeroSimulation.zero_energy_certificate

/-- info: 'SparseHamiltonian.ImprovedZeroSimulation.zero_spectral_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedZeroSimulation.zero_spectral_certificate

/-- info: 'SparseHamiltonian.ImprovedSparseHamiltonian.simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedSparseHamiltonian.simulation

/-- info: 'SparseHamiltonian.ImprovedSparseHamiltonian.simulation_spectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedSparseHamiltonian.simulation_spectral

/-- info: 'SparseHamiltonian.ImprovedSparseHamiltonian.reference_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedSparseHamiltonian.reference_error

/-- info: 'SparseHamiltonian.ImprovedSparseHamiltonian.simulation_with_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedSparseHamiltonian.simulation_with_reference

/-- info: 'SparseHamiltonian.ImprovedSparseHamiltonian.simulation_log_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedSparseHamiltonian.simulation_log_one

/-- info: 'SparseHamiltonian.ImprovedSparseHamiltonian.simulation_spectral_log_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedSparseHamiltonian.simulation_spectral_log_one

/-- info: 'SparseHamiltonian.ImprovedSparseHamiltonian.simulation_with_reference_log_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedSparseHamiltonian.simulation_with_reference_log_one

/-! Additional endpoint and operational-semantics audits. -/

/-- info: 'SparseHamiltonian.UnitaryEntryData.dilation_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryEntryData.dilation_sq

/-- info: 'SparseHamiltonian.UnitaryDilationTransfer.exp_quarter_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryDilationTransfer.exp_quarter_turn

/-- info: 'SparseHamiltonian.UnitaryEntryOracle.flatEntry_eq_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryEntryOracle.flatEntry_eq_original

/-- info: 'SparseHamiltonian.UnitaryEntryOracle.compile_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryEntryOracle.compile_eval

/-- info: 'SparseHamiltonian.UnitaryImplementation.implementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.UnitaryImplementation.implementation

-- Direct audits of the controlled-oracle declarations (axiom sets determined by compiling).

/-- info: 'SparseHamiltonian.ControlledLookup.controlled_two_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ControlledLookup.controlled_two_queries

/-- info: 'SparseHamiltonian.ControlledLookup.circuit_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ControlledLookup.circuit_clean

/-- info: 'SparseHamiltonian.ControlledLookup.circuit_clean_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ControlledLookup.circuit_clean_apply

/-- info: 'SparseHamiltonian.NativeControlledOracle.three_query_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeControlledOracle.three_query_control

/-- info: 'SparseHamiltonian.NativeControlledOracle.three_query_inverse_control' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeControlledOracle.three_query_inverse_control

/-- info: 'SparseHamiltonian.NativeControlledOracle.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.NativeControlledOracle.certificate
