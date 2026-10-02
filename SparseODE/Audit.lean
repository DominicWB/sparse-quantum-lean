import SparseODE.All


/-! Additional endpoint and operational-semantics audits. -/

/-- info: 'SparseHamiltonian.ODEMixedOutput.ensemble_trace_distance_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEMixedOutput.ensemble_trace_distance_le

/-- info: 'SparseHamiltonian.ODEMixedOutput.ode_ensemble_trace_distance_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEMixedOutput.ode_ensemble_trace_distance_le

/-- info: 'SparseHamiltonian.ODERepeatProtocol.TrialFamily.oneTrialDensity_eq_kraus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODERepeatProtocol.TrialFamily.oneTrialDensity_eq_kraus

/-- info: 'SparseHamiltonian.ODERepeatProtocol.fourTrials_conditionalDensity_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODERepeatProtocol.fourTrials_conditionalDensity_eq

/-- info: 'SparseHamiltonian.ODECompleteTrial.of_trialCertificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECompleteTrial.of_trialCertificate

/-- info: 'SparseHamiltonian.ODECompleteEndpoint.solver_of_nonempty_promise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECompleteEndpoint.solver_of_nonempty_promise

/-- info: 'SparseHamiltonian.ODECompleteEndpoint.solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECompleteEndpoint.solver
/-! Checked axiom dependencies for the published proof declarations. -/

/-- info: 'SparseHamiltonian.ODEMatrixEnergy.lchsHamiltonian_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEMatrixEnergy.lchsHamiltonian_isHermitian

/-- info: 'SparseHamiltonian.ODEMatrixEnergy.lchsHamiltonian_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEMatrixEnergy.lchsHamiltonian_entry

/-- info: 'SparseHamiltonian.ODEMatrixEnergy.lchsHamiltonian_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEMatrixEnergy.lchsHamiltonian_support

/-- info: 'SparseHamiltonian.ODEMatrixEnergy.lchs_energies_le_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEMatrixEnergy.lchs_energies_le_radius

/-- info: 'SparseHamiltonian.ODEMatrixEnergy.matrixOperator_lchsHamiltonian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEMatrixEnergy.matrixOperator_lchsHamiltonian

/-- info: 'SparseHamiltonian.ODETaggedSupport.tag_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedSupport.tag_sum

/-- info: 'SparseHamiltonian.ODETaggedSupport.tag_energy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedSupport.tag_energy_le

/-- info: 'SparseHamiltonian.ODETaggedSupport.native_frame_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedSupport.native_frame_certificate

/-- info: 'SparseHamiltonian.ODETaggedSupport.native_boundary_energy_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedSupport.native_boundary_energy_certificate

/-- info: 'SparseHamiltonian.ODETaggedLCHS.native_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedLCHS.native_overlap

/-- info: 'SparseHamiltonian.ODETaggedLCHS.native_energy_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedLCHS.native_energy_certificate

/-- info: 'SparseHamiltonian.ODESourceQuadrature.partialSum_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceQuadrature.partialSum_error

/-- info: 'SparseHamiltonian.ODESourceQuadrature.forcingSum_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceQuadrature.forcingSum_error

/-- info: 'SparseHamiltonian.ODESourceQuadrature.exists_finiteDuhamel_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceQuadrature.exists_finiteDuhamel_certificate

/-- info: 'SparseHamiltonian.ImprovedODEQueryBudget.gaussian_radius_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedODEQueryBudget.gaussian_radius_le

/-- info: 'SparseHamiltonian.ImprovedODEQueryBudget.selected_shape_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedODEQueryBudget.selected_shape_le

/-- info: 'SparseHamiltonian.ImprovedODEQueryBudget.amplified_query_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedODEQueryBudget.amplified_query_bound

/-- info: 'SparseHamiltonian.ImprovedODEQueryBudget.common_shape_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedODEQueryBudget.common_shape_le

/-- info: 'SparseHamiltonian.ImprovedODEOutput.six_tolerance_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedODEOutput.six_tolerance_error_le

/-- info: 'SparseHamiltonian.ImprovedODEOutput.output_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedODEOutput.output_certificate

/-- info: 'SparseHamiltonian.ImprovedODEOutput.finite_lchs_output_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedODEOutput.finite_lchs_output_certificate

/-- info: 'SparseHamiltonian.ImprovedODESourceOutput.exists_discretized_output_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedODESourceOutput.exists_discretized_output_certificate

/-- info: 'SparseHamiltonian.ODETaggedMoments.boundary_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedMoments.boundary_isometry

/-- info: 'SparseHamiltonian.ODETaggedMoments.generator_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedMoments.generator_compression

/-- info: 'SparseHamiltonian.ODETaggedMoments.generator_boundary_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedMoments.generator_boundary_norm_le

/-- info: 'SparseHamiltonian.ODETaggedMoments.native_moment_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedMoments.native_moment_certificate

/-- info: 'SparseHamiltonian.ODETaggedMoments.native_lchs_moment_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedMoments.native_lchs_moment_certificate

/-- info: 'SparseHamiltonian.ODETaggedCayley.lift_generator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedCayley.lift_generator

/-- info: 'SparseHamiltonian.ODETaggedCayley.scaled_generator_eq_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedCayley.scaled_generator_eq_lift

/-- info: 'SparseHamiltonian.ODETaggedCayley.inverse_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedCayley.inverse_right

/-- info: 'SparseHamiltonian.ODETaggedCayley.inverse_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedCayley.inverse_left

/-- info: 'SparseHamiltonian.ODETaggedCayley.action_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedCayley.action_unitary

/-- info: 'SparseHamiltonian.ODETaggedCayley.action_eq_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedCayley.action_eq_cayley

/-- info: 'SparseHamiltonian.ODETaggedCayley.one_sub_action_mul_resolvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedCayley.one_sub_action_mul_resolvent

/-- info: 'SparseHamiltonian.ODETaggedCayley.resolvent_mul_one_sub_action' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedCayley.resolvent_mul_one_sub_action

/-- info: 'SparseHamiltonian.ODEPairedValueQuery.oracle_original_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPairedValueQuery.oracle_original_intertwines

/-- info: 'SparseHamiltonian.ODEPairedValueQuery.program_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPairedValueQuery.program_count

/-- info: 'SparseHamiltonian.ODEPairedValueQuery.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPairedValueQuery.program_intertwines

/-- info: 'SparseHamiltonian.ODEPairedValueQuery.implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPairedValueQuery.implementsOn

/-- info: 'SparseHamiltonian.ODETaggedLocators.locator_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedLocators.locator_unitary

/-- info: 'SparseHamiltonian.ODETaggedLocators.fixedBoundary_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedLocators.fixedBoundary_isometry

/-- info: 'SparseHamiltonian.ODETaggedLocators.locator_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedLocators.locator_boundary

/-- info: 'SparseHamiltonian.ODETaggedLocators.native_locator_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedLocators.native_locator_certificate

/-- info: 'SparseHamiltonian.ODEFixedTaggedMoments.native_moment_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFixedTaggedMoments.native_moment_certificate

/-- info: 'SparseHamiltonian.ODEFixedTaggedMoments.inverse_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFixedTaggedMoments.inverse_right

/-- info: 'SparseHamiltonian.ODEFixedTaggedMoments.inverse_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFixedTaggedMoments.inverse_left

/-- info: 'SparseHamiltonian.ODEFixedTaggedMoments.action_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFixedTaggedMoments.action_unitary

/-- info: 'SparseHamiltonian.ODEFixedTaggedMoments.action_eq_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFixedTaggedMoments.action_eq_cayley

/-- info: 'SparseHamiltonian.ODEFixedTaggedMoments.physical_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFixedTaggedMoments.physical_exponent

/-- info: 'SparseHamiltonian.ODEFixedTaggedMoments.lchs_moment_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFixedTaggedMoments.lchs_moment_certificate

/-- info: 'SparseHamiltonian.ODETaggedValueDecoder.decodedEntry_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedValueDecoder.decodedEntry_correct

/-- info: 'SparseHamiltonian.ODETaggedValueDecoder.gates_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedValueDecoder.gates_correct

/-- info: 'SparseHamiltonian.ODETaggedValueProgram.program_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedValueProgram.program_count

/-- info: 'SparseHamiltonian.ODETaggedValueProgram.program_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedValueProgram.program_unitary

/-- info: 'SparseHamiltonian.ODETaggedValueProgram.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedValueProgram.program_intertwines

/-- info: 'SparseHamiltonian.ODETaggedValueProgram.implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedValueProgram.implementsOn

/-- info: 'SparseHamiltonian.ODETaggedValueOracle.oracle_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedValueOracle.oracle_intertwines

/-- info: 'SparseHamiltonian.ODETaggedValueOracle.oracle_adjoint_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedValueOracle.oracle_adjoint_intertwines

/-- info: 'SparseHamiltonian.ODETaggedValueOracle.program_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedValueOracle.program_count

/-- info: 'SparseHamiltonian.ODETaggedValueOracle.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedValueOracle.program_intertwines

/-- info: 'SparseHamiltonian.ODETaggedValueOracle.implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODETaggedValueOracle.implementsOn

/-- info: 'SparseHamiltonian.ODENativeLayout.logicalOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeLayout.logicalOracle_unitary

/-- info: 'SparseHamiltonian.ODENativeLayout.valueEmbedding_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeLayout.valueEmbedding_isometry

/-- info: 'SparseHamiltonian.ODENativeLayout.value_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeLayout.value_intertwines

/-- info: 'SparseHamiltonian.ODENativeLayout.clean_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeLayout.clean_apply

/-- info: 'SparseHamiltonian.ODENativeLayout.clean_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeLayout.clean_isometry

/-- info: 'SparseHamiltonian.ODENativeLocator.freeSwap_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeLocator.freeSwap_unitary

/-- info: 'SparseHamiltonian.ODENativeLocator.locatorProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeLocator.locatorProgram_cost

/-- info: 'SparseHamiltonian.ODENativeLocator.locatorProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeLocator.locatorProgram_intertwines

/-- info: 'SparseHamiltonian.ODENativeLocator.locatorProgram_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeLocator.locatorProgram_unitary

/-- info: 'SparseHamiltonian.ODENativeValue.singleProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeValue.singleProgram_intertwines

/-- info: 'SparseHamiltonian.ODENativeValue.program_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeValue.program_count

/-- info: 'SparseHamiltonian.ODENativeValue.program_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeValue.program_cost

/-- info: 'SparseHamiltonian.ODENativeValue.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeValue.program_intertwines

/-- info: 'SparseHamiltonian.ODENativeValue.adjoint_program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeValue.adjoint_program_intertwines

/-- info: 'SparseHamiltonian.FlatBranchNativeAccess.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FlatBranchNativeAccess.valid

/-- info: 'SparseHamiltonian.FlatBranchNativeAccess.flatten_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FlatBranchNativeAccess.flatten_intertwines

/-- info: 'SparseHamiltonian.FlatBranchNativeAccess.program_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FlatBranchNativeAccess.program_cost

/-- info: 'SparseHamiltonian.FlatBranchNativeAccess.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.FlatBranchNativeAccess.program_intertwines

/-- info: 'SparseHamiltonian.ODENativeCayley.logicalProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeCayley.logicalProgram_intertwines

/-- info: 'SparseHamiltonian.ODENativeCayley.compiledProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeCayley.compiledProgram_intertwines

/-- info: 'SparseHamiltonian.ODENativeCayley.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeCayley.valid

/-- info: 'SparseHamiltonian.ODENativeCayley.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeCayley.program_intertwines

/-- info: 'SparseHamiltonian.ODENativeCayley.program_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeCayley.program_cost

/-- info: 'SparseHamiltonian.ODENativeCayley.program_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeCayley.program_count

/-- info: 'SparseHamiltonian.ODENativeActive.program_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeActive.program_count

/-- info: 'SparseHamiltonian.ODENativeActive.program_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeActive.program_cost

/-- info: 'SparseHamiltonian.ODENativeActive.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeActive.program_intertwines

/-- info: 'SparseHamiltonian.ODENativeActive.implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeActive.implementsOn

/-- info: 'SparseHamiltonian.ODECommonDuration.native_moment_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECommonDuration.native_moment_certificate

/-- info: 'SparseHamiltonian.ODECommonDuration.inverse_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECommonDuration.inverse_right

/-- info: 'SparseHamiltonian.ODECommonDuration.inverse_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECommonDuration.inverse_left

/-- info: 'SparseHamiltonian.ODECommonDuration.action_eq_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECommonDuration.action_eq_cayley

/-- info: 'SparseHamiltonian.ODECommonDuration.physical_duration_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECommonDuration.physical_duration_exponent

/-- info: 'SparseHamiltonian.ODECommonDuration.lchs_duration_moment_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECommonDuration.lchs_duration_moment_certificate

/-- info: 'SparseHamiltonian.ODEFixedTaggedQuery.query_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFixedTaggedQuery.query_certificate

/-- info: 'SparseHamiltonian.ODENativeSimulation.active_implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeSimulation.active_implementsOn

/-- info: 'SparseHamiltonian.ODENativeSimulation.native_at_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeSimulation.native_at_scale

/-- info: 'SparseHamiltonian.ODENativeSimulation.exists_uniform_lchs_simulations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeSimulation.exists_uniform_lchs_simulations

/-- info: 'SparseHamiltonian.CommonQueryShape.exists_schedule' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CommonQueryShape.exists_schedule

/-- info: 'SparseHamiltonian.ODECoherentCayley.program_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentCayley.program_shape

/-- info: 'SparseHamiltonian.ODECoherentCayley.program_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentCayley.program_count

/-- info: 'SparseHamiltonian.ODECoherentCayley.program_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentCayley.program_cost

/-- info: 'SparseHamiltonian.ODECoherentCayley.program_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentCayley.program_unitary

/-- info: 'SparseHamiltonian.ODECoherentCayley.clean_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentCayley.clean_isometry

/-- info: 'SparseHamiltonian.ODECoherentCayley.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentCayley.program_intertwines

/-- info: 'SparseHamiltonian.ODECoherentActive.program_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentActive.program_shape

/-- info: 'SparseHamiltonian.ODECoherentActive.program_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentActive.program_count

/-- info: 'SparseHamiltonian.ODECoherentActive.program_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentActive.program_cost

/-- info: 'SparseHamiltonian.ODECoherentActive.embedding_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentActive.embedding_isometry

/-- info: 'SparseHamiltonian.ODECoherentActive.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentActive.program_intertwines

/-- info: 'SparseHamiltonian.ODECoherentActive.implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentActive.implementsOn

/-- info: 'SparseHamiltonian.ODECoherentMoments.rectangular_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentMoments.rectangular_adjoint

/-- info: 'SparseHamiltonian.ODECoherentMoments.moment_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentMoments.moment_certificate

/-- info: 'SparseHamiltonian.ODECoherentMoments.physical_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentMoments.physical_exponent

/-- info: 'SparseHamiltonian.ODECoherentMoments.lchs_duration_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentMoments.lchs_duration_certificate

/-- info: 'SparseHamiltonian.CoherentDiagonalExp.exp_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CoherentDiagonalExp.exp_diagonal

/-- info: 'SparseHamiltonian.CoherentDiagonalExp.exp_smul_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CoherentDiagonalExp.exp_smul_diagonal

/-- info: 'SparseHamiltonian.ODEJointNative.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointNative.valid

/-- info: 'SparseHamiltonian.ODEJointNative.cayleyProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointNative.cayleyProgram_count

/-- info: 'SparseHamiltonian.ODEJointNative.cayleyProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointNative.cayleyProgram_intertwines

/-- info: 'SparseHamiltonian.ODEJointNative.boundary_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointNative.boundary_isometry

/-- info: 'SparseHamiltonian.ODEJointNative.embedding_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointNative.embedding_isometry

/-- info: 'SparseHamiltonian.ODEJointNative.program_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointNative.program_count

/-- info: 'SparseHamiltonian.ODEJointNative.program_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointNative.program_cost

/-- info: 'SparseHamiltonian.ODEJointNative.program_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointNative.program_intertwines

/-- info: 'SparseHamiltonian.ODEJointNative.implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointNative.implementsOn

/-- info: 'SparseHamiltonian.ODEJointCayley.inverse_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointCayley.inverse_right

/-- info: 'SparseHamiltonian.ODEJointCayley.inverse_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointCayley.inverse_left

/-- info: 'SparseHamiltonian.ODEJointCayley.action_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointCayley.action_unitary

/-- info: 'SparseHamiltonian.ODEJointCayley.action_eq_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointCayley.action_eq_cayley

/-- info: 'SparseHamiltonian.ODEJointCayley.moment_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointCayley.moment_certificate

/-- info: 'SparseHamiltonian.ODEJointCayley.physical_exponent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointCayley.physical_exponent

/-- info: 'SparseHamiltonian.ODEJointCayley.query_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointCayley.query_certificate

/-- info: 'SparseHamiltonian.ODEJointSimulation.active_implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointSimulation.active_implementsOn

/-- info: 'SparseHamiltonian.ODEJointSimulation.native_at_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointSimulation.native_at_scale

/-- info: 'SparseHamiltonian.ODEJointSimulation.exists_coherent_native_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointSimulation.exists_coherent_native_simulation

/-- info: 'SparseHamiltonian.ODECoherentSimulation.oracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentSimulation.oracle_unitary

/-- info: 'SparseHamiltonian.ODECoherentSimulation.simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoherentSimulation.simulation

/-- info: 'SparseHamiltonian.ODEJointLCU.input_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointLCU.input_isometry

/-- info: 'SparseHamiltonian.ODEJointLCU.output_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointLCU.output_isometry

/-- info: 'SparseHamiltonian.ODEJointLCU.compression_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointLCU.compression_error

/-- info: 'SparseHamiltonian.ODEJointLCU.scaled_compression_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointLCU.scaled_compression_error

/-- info: 'SparseHamiltonian.ODEJointLCU.lchs_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointLCU.lchs_error

/-- info: 'SparseHamiltonian.ODENativeLCU.finite_lcu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeLCU.finite_lcu

/-- info: 'SparseHamiltonian.ODECoefficientPadding.coefficientMass_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoefficientPadding.coefficientMass_eq

/-- info: 'SparseHamiltonian.ODECoefficientPadding.padded_weighted_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoefficientPadding.padded_weighted_sum

/-- info: 'SparseHamiltonian.ODECoefficientPadding.branchEvolution_eq_paddedOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoefficientPadding.branchEvolution_eq_paddedOperator

/-- info: 'SparseHamiltonian.ODECoefficientPadding.finiteSum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoefficientPadding.finiteSum_eq

/-- info: 'SparseHamiltonian.ODECoefficientPadding.normalizedTarget_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoefficientPadding.normalizedTarget_eq

/-- info: 'SparseHamiltonian.ODEFinitePropagator.query_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinitePropagator.query_bound

/-- info: 'SparseHamiltonian.ODEFinitePropagator.finite_lchs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinitePropagator.finite_lchs

/-- info: 'SparseHamiltonian.ODEHeraldedSuccess.unitDirection_pos_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEHeraldedSuccess.unitDirection_pos_smul

/-- info: 'SparseHamiltonian.ODEHeraldedSuccess.successProjector_isOrthogonalProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEHeraldedSuccess.successProjector_isOrthogonalProjection

/-- info: 'SparseHamiltonian.ODEHeraldedSuccess.successfulComponent_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEHeraldedSuccess.successfulComponent_norm

/-- info: 'SparseHamiltonian.ODEHeraldedSuccess.actual_preparation_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEHeraldedSuccess.actual_preparation_certificate

/-- info: 'SparseHamiltonian.ODEJointSourceLCU.input_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointSourceLCU.input_isometry

/-- info: 'SparseHamiltonian.ODEJointSourceLCU.physical_unit_vectors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointSourceLCU.physical_unit_vectors

/-- info: 'SparseHamiltonian.ODEJointSourceLCU.compression_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointSourceLCU.compression_error

/-- info: 'SparseHamiltonian.ODEJointSourceLCU.scaled_compression_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointSourceLCU.scaled_compression_error

/-- info: 'SparseHamiltonian.ODEJointSourceLCU.actual_vector_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointSourceLCU.actual_vector_error

/-- info: 'SparseHamiltonian.ODEJointSourceLCU.actual_unit_vector_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEJointSourceLCU.actual_unit_vector_error

/-- info: 'SparseHamiltonian.ODESourceCoefficients.coefficientMass_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceCoefficients.coefficientMass_product

/-- info: 'SparseHamiltonian.ODESourceCoefficients.coefficientMass_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceCoefficients.coefficientMass_normalized

/-- info: 'SparseHamiltonian.ODESourceCoefficients.target_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceCoefficients.target_sum

/-- info: 'SparseHamiltonian.ODESourceCoefficients.uniform_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceCoefficients.uniform_error

/-- info: 'SparseHamiltonian.ODESourceCoefficients.scaled_uniform_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceCoefficients.scaled_uniform_error

/-- info: 'SparseHamiltonian.ODESourceBranches.sum_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceBranches.sum_probability

/-- info: 'SparseHamiltonian.ODESourceBranches.norm_smul_unitDirection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceBranches.norm_smul_unitDirection

/-- info: 'SparseHamiltonian.ODESourceBranches.rescaled_preparedSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceBranches.rescaled_preparedSum

/-- info: 'SparseHamiltonian.ODESourceBranches.mass_sourceVector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceBranches.mass_sourceVector

/-- info: 'SparseHamiltonian.ODESourceBranches.source_sum_eq_finiteDuhamel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceBranches.source_sum_eq_finiteDuhamel

/-- info: 'SparseHamiltonian.ODESourceBranches.prepared_source_eq_finiteDuhamel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceBranches.prepared_source_eq_finiteDuhamel

/-- info: 'SparseHamiltonian.ODESourceBranches.exists_constant_forcing_branches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceBranches.exists_constant_forcing_branches

/-- info: 'SparseHamiltonian.ODESourcePreparations.branch_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourcePreparations.branch_isometry

/-- info: 'SparseHamiltonian.ODESourcePreparations.branch_prepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourcePreparations.branch_prepares

/-- info: 'SparseHamiltonian.ODENativeSourceLCU.finite_lcu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeSourceLCU.finite_lcu

/-- info: 'SparseHamiltonian.ODENativeSourceLCU.native_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeSourceLCU.native_selected

/-- info: 'SparseHamiltonian.ODEActualSourceError.coefficientMass_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEActualSourceError.coefficientMass_eq

/-- info: 'SparseHamiltonian.ODEActualSourceError.six_tolerance_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEActualSourceError.six_tolerance_error

/-- info: 'SparseHamiltonian.ODEActualSourceError.actual_source_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEActualSourceError.actual_source_certificate

/-- info: 'SparseHamiltonian.ODENativeSourceCertificate.native_source_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeSourceCertificate.native_source_certificate

/-- info: 'SparseHamiltonian.ODEGroverRay.ray_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverRay.ray_isometry

/-- info: 'SparseHamiltonian.ODEGroverRay.projector_isOrthogonalProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverRay.projector_isOrthogonalProjection

/-- info: 'SparseHamiltonian.ODEGroverRay.projector_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverRay.projector_self

/-- info: 'SparseHamiltonian.ODEGroverRay.ray_adjoint_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverRay.ray_adjoint_good

/-- info: 'SparseHamiltonian.ODEGroverRay.projector_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverRay.projector_good

/-- info: 'SparseHamiltonian.ODEGroverRay.projector_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverRay.projector_transport

/-- info: 'SparseHamiltonian.ODEGroverPlane.grover_stateAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverPlane.grover_stateAt

/-- info: 'SparseHamiltonian.ODEGroverPlane.power_action' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverPlane.power_action

/-- info: 'SparseHamiltonian.ODEGroverPlane.projected_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverPlane.projected_power

/-- info: 'SparseHamiltonian.ODEGroverPlane.success_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverPlane.success_probability

/-- info: 'SparseHamiltonian.ODEGroverAverage.successProbability_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverAverage.successProbability_bounds

/-- info: 'SparseHamiltonian.ODEGroverAverage.sum_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverAverage.sum_identity

/-- info: 'SparseHamiltonian.ODEGroverAverage.meanSuccess_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverAverage.meanSuccess_lower

/-- info: 'SparseHamiltonian.ODEGroverAverage.meanSuccess_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverAverage.meanSuccess_bounds

/-- info: 'SparseHamiltonian.ODEGroverAverage.amplitude_le_sin_two_arcsin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverAverage.amplitude_le_sin_two_arcsin

/-- info: 'SparseHamiltonian.ODEGroverAverage.chosenIterations_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverAverage.chosenIterations_bounds

/-- info: 'SparseHamiltonian.ODEGroverAverage.promised_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverAverage.promised_amplitude

/-- info: 'SparseHamiltonian.ODEGroverDirection.real_multiple_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverDirection.real_multiple_phase

/-- info: 'SparseHamiltonian.ODEGroverDirection.decode_real_multiple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverDirection.decode_real_multiple

/-- info: 'SparseHamiltonian.ODEGroverDirection.direction_error_of_real_multiple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverDirection.direction_error_of_real_multiple

/-- info: 'SparseHamiltonian.ODEGroverProgram.operator_eq_conjugated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverProgram.operator_eq_conjugated

/-- info: 'SparseHamiltonian.ODEGroverProgram.amplified_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverProgram.amplified_eval

/-- info: 'SparseHamiltonian.ODEGroverProgram.amplified_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverProgram.amplified_cost

/-- info: 'SparseHamiltonian.ODEGroverProgram.amplified_labelCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverProgram.amplified_labelCount

/-- info: 'SparseHamiltonian.ODEGroverProgram.amplified_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverProgram.amplified_unitary

/-- info: 'SparseHamiltonian.ODEGroverProgram.amplified_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverProgram.amplified_cost_le

/-- info: 'SparseHamiltonian.ODEGroverActual.angle_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverActual.angle_geometry

/-- info: 'SparseHamiltonian.ODEGroverActual.trial_projected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverActual.trial_projected

/-- info: 'SparseHamiltonian.ODEGroverActual.trial_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverActual.trial_probability

/-- info: 'SparseHamiltonian.ODEGroverActual.decoded_multiple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverActual.decoded_multiple

/-- info: 'SparseHamiltonian.ODEGroverActual.randomized_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGroverActual.randomized_certificate

/-- info: 'SparseHamiltonian.ODECountedAmplification.state_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECountedAmplification.state_eq

/-- info: 'SparseHamiltonian.ODECountedAmplification.cost_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECountedAmplification.cost_eq

/-- info: 'SparseHamiltonian.ODECountedAmplification.randomized_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECountedAmplification.randomized_certificate

/-- info: 'SparseHamiltonian.ODECountedAmplification.selected_query_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECountedAmplification.selected_query_bound

/-- info: 'SparseHamiltonian.ODESourceAmplification.source_randomized_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceAmplification.source_randomized_certificate

/-- info: 'SparseHamiltonian.ODESourceAmplification.counted_source_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceAmplification.counted_source_certificate

/-- info: 'SparseHamiltonian.ODESourceControls.initial_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceControls.initial_unitary

/-- info: 'SparseHamiltonian.ODESourceControls.forcing_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceControls.forcing_unitary

/-- info: 'SparseHamiltonian.ODESourceControls.combined_eq_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceControls.combined_eq_diagonal

/-- info: 'SparseHamiltonian.ODESourceControls.combined_inputEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceControls.combined_inputEmbedding

/-- info: 'SparseHamiltonian.ODESourceTransport.route_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceTransport.route_unitary

/-- info: 'SparseHamiltonian.ODESourceTransport.route_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceTransport.route_source

/-- info: 'SparseHamiltonian.ODESourceTransport.route_encoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceTransport.route_encoded

/-- info: 'SparseHamiltonian.ODESourceTransport.matrixProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceTransport.matrixProgram_eval

/-- info: 'SparseHamiltonian.ODESourceTransport.matrixProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceTransport.matrixProgram_cost

/-- info: 'SparseHamiltonian.ODESourceTransport.routed_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceTransport.routed_source

/-- info: 'SparseHamiltonian.ODESourceQueryBudget.preparation_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceQueryBudget.preparation_eval

/-- info: 'SparseHamiltonian.ODESourceQueryBudget.preparation_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceQueryBudget.preparation_cost

/-- info: 'SparseHamiltonian.ODESourceQueryBudget.trial_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceQueryBudget.trial_matrix_cost

/-- info: 'SparseHamiltonian.ODESourceQueryBudget.trial_source_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceQueryBudget.trial_source_cost

/-- info: 'SparseHamiltonian.ODESourceQueryBudget.trial_source_total_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceQueryBudget.trial_source_total_bound

/-- info: 'SparseHamiltonian.ODESourceQueryBudget.selected_matrix_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceQueryBudget.selected_matrix_bound

/-- info: 'SparseHamiltonian.ODESourceHeraldLift.output_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceHeraldLift.output_isometry

/-- info: 'SparseHamiltonian.ODESourceHeraldLift.decode_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceHeraldLift.decode_lift

/-- info: 'SparseHamiltonian.ODESourceHeraldLift.projected_norm_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceHeraldLift.projected_norm_lift

/-- info: 'SparseHamiltonian.ODESourceHeraldLift.randomized_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourceHeraldLift.randomized_lift

/-- info: 'SparseHamiltonian.ODECompiledSource.oracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECompiledSource.oracle_unitary

/-- info: 'SparseHamiltonian.ODECompiledSource.program_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECompiledSource.program_state

/-- info: 'SparseHamiltonian.ODECompiledSource.seed_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECompiledSource.seed_unit

/-- info: 'SparseHamiltonian.ODECompiledSource.output_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECompiledSource.output_isometry

/-- info: 'SparseHamiltonian.ODECompiledSource.decoded_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECompiledSource.decoded_eq

/-- info: 'SparseHamiltonian.ODECompiledSource.program_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECompiledSource.program_matrix_cost

/-- info: 'SparseHamiltonian.ODECompiledSource.program_source_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECompiledSource.program_source_cost

/-- info: 'SparseHamiltonian.ODECountedSourceCertificate.compiled_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECountedSourceCertificate.compiled_geometry

/-- info: 'SparseHamiltonian.ODECountedSourceCertificate.counted_source_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECountedSourceCertificate.counted_source_certificate

/-- info: 'SparseHamiltonian.ODESectorCoordinates.matrix_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESectorCoordinates.matrix_intertwines

/-- info: 'SparseHamiltonian.ODESectorCoordinates.source_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESectorCoordinates.source_intertwines

/-- info: 'SparseHamiltonian.ODESectorCoordinates.compile_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESectorCoordinates.compile_cost

/-- info: 'SparseHamiltonian.ODESectorCoordinates.compile_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESectorCoordinates.compile_eval

/-- info: 'SparseHamiltonian.ODESectorTensor.input_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESectorTensor.input_isometry

/-- info: 'SparseHamiltonian.ODESectorTensor.sourcePhysical_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESectorTensor.sourcePhysical_unitary

/-- info: 'SparseHamiltonian.ODESectorTensor.source_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESectorTensor.source_intertwines

/-- info: 'SparseHamiltonian.ODEPrimitiveControlBudget.matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPrimitiveControlBudget.matrix_cost

/-- info: 'SparseHamiltonian.ODEPrimitiveControlBudget.source_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPrimitiveControlBudget.source_cost

/-- info: 'SparseHamiltonian.ODEPrimitiveControlBudget.source_total_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPrimitiveControlBudget.source_total_cost

/-- info: 'SparseHamiltonian.ODEPrimitiveControlBudget.state_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPrimitiveControlBudget.state_eq

/-- info: 'SparseHamiltonian.ODEPrimitiveControlBudget.decoded_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPrimitiveControlBudget.decoded_eq

/-- info: 'SparseHamiltonian.ODEPrimitiveControlBudget.projected_norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPrimitiveControlBudget.projected_norm_eq

/-- info: 'SparseHamiltonian.ODEPrimitiveControlBudget.transfer_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPrimitiveControlBudget.transfer_certificate

/-- info: 'SparseHamiltonian.ODESectorNativeControl.matrixProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESectorNativeControl.matrixProgram_count

/-- info: 'SparseHamiltonian.ODESectorNativeControl.matrixProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESectorNativeControl.matrixProgram_intertwines

/-- info: 'SparseHamiltonian.ODESectorNativeControl.physicalOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESectorNativeControl.physicalOracle_unitary

/-- info: 'SparseHamiltonian.ODESectorNativeControl.letter_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESectorNativeControl.letter_intertwines

/-- info: 'SparseHamiltonian.ODESectorNativeControl.compile_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESectorNativeControl.compile_eval

/-- info: 'SparseHamiltonian.ODESectorNativeControl.compile_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESectorNativeControl.compile_unitary

/-- info: 'SparseHamiltonian.ODESectorNativeControl.compile_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESectorNativeControl.compile_cost

/-- info: 'SparseHamiltonian.ODESectorNativeControl.compile_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESectorNativeControl.compile_matrix_cost

/-- info: 'SparseHamiltonian.ODEFinalNativeBasis.alignedOracle_eq_spectator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeBasis.alignedOracle_eq_spectator

/-- info: 'SparseHamiltonian.ODEFinalNativeBasis.flatOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeBasis.flatOracle_unitary

/-- info: 'SparseHamiltonian.ODEFinalNativeBasis.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeBasis.valid

/-- info: 'SparseHamiltonian.ODEFinalNativeBasis.transportProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeBasis.transportProgram_eval

/-- info: 'SparseHamiltonian.ODEFinalNativeBasis.transportProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeBasis.transportProgram_count

/-- info: 'SparseHamiltonian.ODEFinalNativeBasis.transportProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeBasis.transportProgram_cost

/-- info: 'SparseHamiltonian.ODECoordinateNativeControl.input_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoordinateNativeControl.input_isometry

/-- info: 'SparseHamiltonian.ODECoordinateNativeControl.letter_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoordinateNativeControl.letter_intertwines

/-- info: 'SparseHamiltonian.ODECoordinateNativeControl.compile_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoordinateNativeControl.compile_eval

/-- info: 'SparseHamiltonian.ODECoordinateNativeControl.compile_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoordinateNativeControl.compile_matrix_cost

/-- info: 'SparseHamiltonian.ODECoordinateNativeControl.projected_norm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoordinateNativeControl.projected_norm_eq

/-- info: 'SparseHamiltonian.ODECoordinateNativeControl.transfer_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODECoordinateNativeControl.transfer_certificate

/-- info: 'SparseHamiltonian.ODEPrimitiveSourceJoin.sourceFamily_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPrimitiveSourceJoin.sourceFamily_unitary

/-- info: 'SparseHamiltonian.ODEPrimitiveSourceJoin.primitive_source_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPrimitiveSourceJoin.primitive_source_certificate

/-- info: 'SparseHamiltonian.ODEFinalNativeSource.matrix_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeSource.matrix_valid

/-- info: 'SparseHamiltonian.ODEFinalNativeSource.physicalOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeSource.physicalOracle_unitary

/-- info: 'SparseHamiltonian.ODEFinalNativeSource.compile_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeSource.compile_eval

/-- info: 'SparseHamiltonian.ODEFinalNativeSource.preparation_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeSource.preparation_state

/-- info: 'SparseHamiltonian.ODEFinalNativeSource.preparation_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeSource.preparation_matrix_cost

/-- info: 'SparseHamiltonian.ODEFinalNativeSource.preparation_source_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeSource.preparation_source_cost

/-- info: 'SparseHamiltonian.ODEFinalNativeSource.preparation_source_total_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeSource.preparation_source_total_cost

/-- info: 'SparseHamiltonian.ODEFinalNativeSource.primitive_source_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeSource.primitive_source_certificate

/-- info: 'SparseHamiltonian.ODENativeSourceCertificate.native_source_certificate_with_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODENativeSourceCertificate.native_source_certificate_with_isometry

/-- info: 'SparseHamiltonian.ODEPrimitiveEndpoint.native_ode_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPrimitiveEndpoint.native_ode_trials

/-- info: 'SparseHamiltonian.ODESourcePadding.weighted_node_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourcePadding.weighted_node_sum_eq

/-- info: 'SparseHamiltonian.ODESourcePadding.finite_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourcePadding.finite_sum_eq

/-- info: 'SparseHamiltonian.ODESourcePadding.branch_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourcePadding.branch_sum_eq

/-- info: 'SparseHamiltonian.ODEPublicSourceMesh.norm_generator_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPublicSourceMesh.norm_generator_le

/-- info: 'SparseHamiltonian.ODEPublicSourceMesh.generator_dissipative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPublicSourceMesh.generator_dissipative

/-- info: 'SparseHamiltonian.ODEPublicSourceMesh.meshSize_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPublicSourceMesh.meshSize_bound

/-- info: 'SparseHamiltonian.ODEPublicSourceMesh.approximation_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPublicSourceMesh.approximation_error

/-- info: 'SparseHamiltonian.ODEPublicSourceMesh.branches_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPublicSourceMesh.branches_certificate

/-- info: 'SparseHamiltonian.ODEActualPrimitiveEndpoint.actual_ode_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEActualPrimitiveEndpoint.actual_ode_trials

/-- info: 'SparseHamiltonian.ODEUniformQuadrature.interval_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEUniformQuadrature.interval_error

/-- info: 'SparseHamiltonian.ODEUniformQuadrature.uniformSum_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEUniformQuadrature.uniformSum_error

/-- info: 'SparseHamiltonian.ODEUniformQuadrature.coefficient_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEUniformQuadrature.coefficient_mass_le

/-- info: 'SparseHamiltonian.ODEUniformQuadrature.family_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEUniformQuadrature.family_certificate

/-- info: 'SparseHamiltonian.ODEUniformQuadrature.weightedSum_eq_uniformSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEUniformQuadrature.weightedSum_eq_uniformSum

/-- info: 'SparseHamiltonian.ODEWeightedLCHS.frequency_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEWeightedLCHS.frequency_error

/-- info: 'SparseHamiltonian.ODEWeightedLCHS.weighted_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEWeightedLCHS.weighted_error

/-- info: 'SparseHamiltonian.ODEWeightedLCHS.nativeEvolution_eq_branchEvolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEWeightedLCHS.nativeEvolution_eq_branchEvolution

/-- info: 'SparseHamiltonian.ODEWeightedLCHS.native_dissipative_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEWeightedLCHS.native_dissipative_norm_le

/-- info: 'SparseHamiltonian.ODEWeightedLCHS.native_weighted_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEWeightedLCHS.native_weighted_continuous

/-- info: 'SparseHamiltonian.ODEWeightedLCHS.native_weighted_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEWeightedLCHS.native_weighted_error

/-- info: 'SparseHamiltonian.ODEFiniteLCHSConstruction.frequencyBudget_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFiniteLCHSConstruction.frequencyBudget_nonneg

/-- info: 'SparseHamiltonian.ODEFiniteLCHSConstruction.public_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFiniteLCHSConstruction.public_table

/-- info: 'SparseHamiltonian.ODEGaussianKernel.norm_kernel_eq_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianKernel.norm_kernel_eq_amplitude

/-- info: 'SparseHamiltonian.ODEGaussianKernel.norm_kernel_le_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianKernel.norm_kernel_le_cauchy

/-- info: 'SparseHamiltonian.ODEGaussianKernel.norm_kernel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianKernel.norm_kernel_le

/-- info: 'SparseHamiltonian.ODEGaussianKernel.norm_kernel_le_exterior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianKernel.norm_kernel_le_exterior

/-- info: 'SparseHamiltonian.ODEGaussianKernel.norm_kernel_le_width_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianKernel.norm_kernel_le_width_tail

/-- info: 'SparseHamiltonian.ODEGaussianKernel.kernel_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianKernel.kernel_continuous

/-- info: 'SparseHamiltonian.ODEGaussianMass.cauchy_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianMass.cauchy_integral

/-- info: 'SparseHamiltonian.ODEGaussianMass.kernel_mass_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianMass.kernel_mass_le_exp

/-- info: 'SparseHamiltonian.ODEGaussianMass.kernel_mass_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianMass.kernel_mass_budget

/-- info: 'SparseHamiltonian.ODEGaussianKernel.amplitude_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianKernel.amplitude_hasDerivAt

/-- info: 'SparseHamiltonian.ODEGaussianKernel.amplitudeDerivative_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianKernel.amplitudeDerivative_bound

/-- info: 'SparseHamiltonian.ODEGaussianKernel.kernel_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianKernel.kernel_hasDerivAt

/-- info: 'SparseHamiltonian.ODEGaussianKernel.kernel_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianKernel.kernel_lipschitz

/-- info: 'SparseHamiltonian.ODEGaussianParameters.width_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianParameters.width_ge_one

/-- info: 'SparseHamiltonian.ODEGaussianParameters.cutoff_le_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianParameters.cutoff_le_radius

/-- info: 'SparseHamiltonian.ODEGaussianParameters.residual_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianParameters.residual_factor

/-- info: 'SparseHamiltonian.ODEGaussianFiniteTable.public_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFiniteTable.public_table

/-- info: 'SparseHamiltonian.ODEGaussianParameters.width_ge_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianParameters.width_ge_two

/-- info: 'SparseHamiltonian.ODEGaussianParameters.integral_error_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianParameters.integral_error_budget

/-- info: 'SparseHamiltonian.ODEGaussianTail.integrable_cauchy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianTail.integrable_cauchy

/-- info: 'SparseHamiltonian.ODEGaussianTail.cauchy_integral_univ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianTail.cauchy_integral_univ

/-- info: 'SparseHamiltonian.ODEGaussianTail.integrable_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianTail.integrable_kernel

/-- info: 'SparseHamiltonian.ODEGaussianTail.cauchy_exterior_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianTail.cauchy_exterior_le

/-- info: 'SparseHamiltonian.ODEGaussianTail.exterior_mass_le_radius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianTail.exterior_mass_le_radius

/-- info: 'SparseHamiltonian.ODEGaussianTail.exterior_mass_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianTail.exterior_mass_bound

/-- info: 'SparseHamiltonian.ODEGaussianIntegral.weighted_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianIntegral.weighted_integrable

/-- info: 'SparseHamiltonian.ODEGaussianIntegral.truncation_error_le_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianIntegral.truncation_error_le_tail

/-- info: 'SparseHamiltonian.ODEGaussianIntegral.truncation_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianIntegral.truncation_error

/-- info: 'SparseHamiltonian.ODEGaussianIntegral.truncated_error_of_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianIntegral.truncated_error_of_full

/-- info: 'SparseHamiltonian.ODEGaussianIntegral.native_weighted_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianIntegral.native_weighted_integrable

/-- info: 'SparseHamiltonian.ODEGaussianIntegral.native_truncation_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianIntegral.native_truncation_error

/-- info: 'SparseHamiltonian.ODEGaussianIntegral.native_truncated_error_of_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianIntegral.native_truncated_error_of_full

/-- info: 'SparseHamiltonian.ODEComplexFrequency.generator_real_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEComplexFrequency.generator_real_inner

/-- info: 'SparseHamiltonian.ODEComplexFrequency.generator_dissipative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEComplexFrequency.generator_dissipative

/-- info: 'SparseHamiltonian.ODEComplexFrequency.evolution_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEComplexFrequency.evolution_norm_le_one

/-- info: 'SparseHamiltonian.ODEComplexFrequency.evolution_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEComplexFrequency.evolution_ofReal

/-- info: 'SparseHamiltonian.ODEComplexFrequency.shifted_evolution_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEComplexFrequency.shifted_evolution_norm_le_one

/-- info: 'SparseHamiltonian.ODEComplexFrequency.parts_evolution_neg_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEComplexFrequency.parts_evolution_neg_I

/-- info: 'SparseHamiltonian.ODEComplexFrequency.evolution_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEComplexFrequency.evolution_continuous

/-- info: 'SparseHamiltonian.ODEGaussianFiniteTable.truncated_error_of_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFiniteTable.truncated_error_of_full

/-- info: 'SparseHamiltonian.ODEGaussianFiniteTable.public_table_of_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFiniteTable.public_table_of_full

/-- info: 'SparseHamiltonian.ODEGaussianComplex.kernel_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianComplex.kernel_ofReal

/-- info: 'SparseHamiltonian.ODEGaussianComplex.numerator_neg_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianComplex.numerator_neg_I

/-- info: 'SparseHamiltonian.ODEGaussianComplex.shifted_exponent_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianComplex.shifted_exponent_re

/-- info: 'SparseHamiltonian.ODEGaussianComplex.shifted_kernel_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianComplex.shifted_kernel_norm_le

/-- info: 'SparseHamiltonian.ODEGaussianComplex.shifted_kernel_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianComplex.shifted_kernel_continuous

/-- info: 'SparseHamiltonian.ODEComplexFrequency.generator_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEComplexFrequency.generator_analyticAt

/-- info: 'SparseHamiltonian.ODEComplexFrequency.evolution_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEComplexFrequency.evolution_analyticAt

/-- info: 'SparseHamiltonian.ODEComplexFrequency.evolution_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEComplexFrequency.evolution_differentiable

/-- info: 'SparseHamiltonian.ODEComplexFrequency.evolution_analyticOnNhd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEComplexFrequency.evolution_analyticOnNhd

/-- info: 'SparseHamiltonian.ODEComplexFrequency.evolution_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEComplexFrequency.evolution_differentiableOn

/-- info: 'SparseHamiltonian.ODEGaussianComplex.exponent_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianComplex.exponent_analyticAt

/-- info: 'SparseHamiltonian.ODEGaussianComplex.numerator_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianComplex.numerator_analyticAt

/-- info: 'SparseHamiltonian.ODEGaussianComplex.kernel_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianComplex.kernel_analyticAt

/-- info: 'SparseHamiltonian.ODEGaussianComplex.kernel_differentiableAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianComplex.kernel_differentiableAt

/-- info: 'SparseHamiltonian.ODEGaussianAnalytic.regularizedFactor_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianAnalytic.regularizedFactor_analyticAt

/-- info: 'SparseHamiltonian.ODEGaussianAnalytic.weightedRegular_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianAnalytic.weightedRegular_analyticAt

/-- info: 'SparseHamiltonian.ODEGaussianAnalytic.weightedRegular_analyticOnNhd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianAnalytic.weightedRegular_analyticOnNhd

/-- info: 'SparseHamiltonian.ODEGaussianAnalytic.weightedRegular_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianAnalytic.weightedRegular_differentiableOn

/-- info: 'SparseHamiltonian.ODEGaussianShiftedIntegral.weighted_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianShiftedIntegral.weighted_continuous

/-- info: 'SparseHamiltonian.ODEGaussianShiftedIntegral.weighted_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianShiftedIntegral.weighted_integrable

/-- info: 'SparseHamiltonian.ODEGaussianShiftedIntegral.integral_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianShiftedIntegral.integral_norm_le

/-- info: 'SparseHamiltonian.ODEGaussianShiftedIntegral.native_weighted_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianShiftedIntegral.native_weighted_integrable

/-- info: 'SparseHamiltonian.ODEGaussianShiftedIntegral.native_integral_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianShiftedIntegral.native_integral_norm_le

/-- info: 'SparseHamiltonian.ODEGaussianVertical.pole_product_norm_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianVertical.pole_product_norm_lower

/-- info: 'SparseHamiltonian.ODEGaussianVertical.exponent_re_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianVertical.exponent_re_le_one

/-- info: 'SparseHamiltonian.ODEGaussianVertical.kernel_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianVertical.kernel_norm_le

/-- info: 'SparseHamiltonian.ODEGaussianVertical.weighted_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianVertical.weighted_norm_le

/-- info: 'SparseHamiltonian.ODEGaussianVertical.vertical_integral_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianVertical.vertical_integral_norm_le

/-- info: 'SparseHamiltonian.ODEContourRectangle.regularized_eq_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEContourRectangle.regularized_eq_sub

/-- info: 'SparseHamiltonian.ODEContourRectangle.regularized_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEContourRectangle.regularized_differentiableOn

/-- info: 'SparseHamiltonian.ODEContourRectangle.regularized_boundary_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEContourRectangle.regularized_boundary_eq_zero

/-- info: 'SparseHamiltonian.ODEContourRectangle.regularized_horizontal_difference_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEContourRectangle.regularized_horizontal_difference_eq

/-- info: 'SparseHamiltonian.ODEContourRectangle.horizontal_difference_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEContourRectangle.horizontal_difference_norm_le

/-- info: 'SparseHamiltonian.ODEGaussianResidue.kernel_factorization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianResidue.kernel_factorization

/-- info: 'SparseHamiltonian.ODEGaussianResidue.regularizedFactor_neg_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianResidue.regularizedFactor_neg_I

/-- info: 'SparseHamiltonian.ODEGaussianResidue.weighted_eq_poleQuotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianResidue.weighted_eq_poleQuotient

/-- info: 'SparseHamiltonian.ODEGaussianResidue.parts_weightedRegular_neg_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianResidue.parts_weightedRegular_neg_I

/-- info: 'SparseHamiltonian.ODEGaussianResidue.weighted_pole_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianResidue.weighted_pole_decomposition

/-- info: 'SparseHamiltonian.ODEGaussianResidue.regularized_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianResidue.regularized_differentiableOn

/-- info: 'SparseHamiltonian.ODEGaussianResidue.regularized_boundary_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianResidue.regularized_boundary_eq_zero

/-- info: 'SparseHamiltonian.ODEReciprocalLine.reciprocal_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEReciprocalLine.reciprocal_continuous

/-- info: 'SparseHamiltonian.ODEReciprocalLine.reciprocal_intervalIntegrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEReciprocalLine.reciprocal_intervalIntegrable

/-- info: 'SparseHamiltonian.ODEReciprocalLine.reciprocal_eq_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEReciprocalLine.reciprocal_eq_coordinates

/-- info: 'SparseHamiltonian.ODEReciprocalLine.primitive_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEReciprocalLine.primitive_hasDerivAt

/-- info: 'SparseHamiltonian.ODEReciprocalLine.integral_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEReciprocalLine.integral_symm

/-- info: 'SparseHamiltonian.ODEReciprocalLine.integral_symm_tendsto_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEReciprocalLine.integral_symm_tendsto_pos

/-- info: 'SparseHamiltonian.ODEReciprocalLine.integral_symm_tendsto_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEReciprocalLine.integral_symm_tendsto_neg

/-- info: 'SparseHamiltonian.ODEReciprocalLine.horizontal_difference_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEReciprocalLine.horizontal_difference_tendsto

/-- info: 'SparseHamiltonian.ODEGaussianLimits.symmetric_integral_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianLimits.symmetric_integral_tendsto

/-- info: 'SparseHamiltonian.ODEGaussianLimits.topWeighted_eq_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianLimits.topWeighted_eq_complex

/-- info: 'SparseHamiltonian.ODEGaussianLimits.top_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianLimits.top_integrable

/-- info: 'SparseHamiltonian.ODEGaussianLimits.top_integral_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianLimits.top_integral_tendsto

/-- info: 'SparseHamiltonian.ODEGaussianLimits.shifted_integral_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianLimits.shifted_integral_tendsto

/-- info: 'SparseHamiltonian.ODEGaussianLimits.horizontal_difference_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianLimits.horizontal_difference_tendsto

/-- info: 'SparseHamiltonian.ODEGaussianEdges.principalPart_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianEdges.principalPart_norm_le

/-- info: 'SparseHamiltonian.ODEGaussianEdges.regularized_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianEdges.regularized_norm_le

/-- info: 'SparseHamiltonian.ODEGaussianEdges.horizontal_difference_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianEdges.horizontal_difference_norm_le

/-- info: 'SparseHamiltonian.ODEGaussianEdges.edge_bound_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianEdges.edge_bound_tendsto_zero

/-- info: 'SparseHamiltonian.ODEGaussianEdges.horizontal_difference_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianEdges.horizontal_difference_tendsto_zero

/-- info: 'SparseHamiltonian.ODEGaussianFiniteContour.regularized_line_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFiniteContour.regularized_line_continuous

/-- info: 'SparseHamiltonian.ODEGaussianFiniteContour.line_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFiniteContour.line_decomposition

/-- info: 'SparseHamiltonian.ODEGaussianFiniteContour.weighted_line_intervalIntegrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFiniteContour.weighted_line_intervalIntegrable

/-- info: 'SparseHamiltonian.ODEGaussianFiniteContour.horizontal_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFiniteContour.horizontal_decomposition

/-- info: 'SparseHamiltonian.ODEGaussianFiniteContour.top_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFiniteContour.top_decomposition

/-- info: 'SparseHamiltonian.ODEGaussianFiniteContour.shifted_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFiniteContour.shifted_decomposition

/-- info: 'SparseHamiltonian.ODEGaussianFiniteContour.horizontal_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFiniteContour.horizontal_difference

/-- info: 'SparseHamiltonian.ODEGaussianFull.residue_scalar_normalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFull.residue_scalar_normalization

/-- info: 'SparseHamiltonian.ODEGaussianFull.residue_normalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFull.residue_normalization

/-- info: 'SparseHamiltonian.ODEGaussianFull.finite_difference_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFull.finite_difference_tendsto

/-- info: 'SparseHamiltonian.ODEGaussianFull.integral_difference_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFull.integral_difference_eq

/-- info: 'SparseHamiltonian.ODEGaussianFull.full_line_error_eq_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFull.full_line_error_eq_residual

/-- info: 'SparseHamiltonian.ODEGaussianFull.full_line_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFull.full_line_error

/-- info: 'SparseHamiltonian.ODEGaussianFull.nativeWeighted_eq_topWeighted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFull.nativeWeighted_eq_topWeighted

/-- info: 'SparseHamiltonian.ODEGaussianFull.native_full_line_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFull.native_full_line_error

/-- info: 'SparseHamiltonian.ODEGaussianFiniteTable.truncated_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFiniteTable.truncated_error

/-- info: 'SparseHamiltonian.ODEGaussianFiniteTable.public_table_from_dissipativity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEGaussianFiniteTable.public_table_from_dissipativity

/-- info: 'SparseHamiltonian.ODEPublicGaussianEndpoint.gridSize_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPublicGaussianEndpoint.gridSize_pos

/-- info: 'SparseHamiltonian.ODEPublicGaussianEndpoint.table_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPublicGaussianEndpoint.table_certificate

/-- info: 'SparseHamiltonian.ODEPublicGaussianEndpoint.actual_ode_trials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPublicGaussianEndpoint.actual_ode_trials

/-- info: 'SparseHamiltonian.ODEPublicGaussianEndpoint.outcome_of_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPublicGaussianEndpoint.outcome_of_scale

/-- info: 'SparseHamiltonian.ODEPublicGaussianEndpoint.positive_time_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPublicGaussianEndpoint.positive_time_solver

/-- info: 'SparseHamiltonian.ODEPrimitiveSourceJoin.logicalTrials_input_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPrimitiveSourceJoin.logicalTrials_input_independent

/-- info: 'SparseHamiltonian.ODEFinalNativeSource.trials_input_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeSource.trials_input_independent

/-- info: 'SparseHamiltonian.ODEZeroEnergy.parts_zero_of_effective_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEZeroEnergy.parts_zero_of_effective_zero

/-- info: 'SparseHamiltonian.ODEZeroEnergy.matrix_zero_of_effective_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEZeroEnergy.matrix_zero_of_effective_energy

/-- info: 'SparseHamiltonian.ODEZeroEnergy.solution_zero_generator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEZeroEnergy.solution_zero_generator

/-- info: 'SparseHamiltonian.ODEZeroEnergy.propagation_zero_generator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEZeroEnergy.propagation_zero_generator

/-- info: 'SparseHamiltonian.ODEZeroEnergy.native_generator_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEZeroEnergy.native_generator_zero

/-- info: 'SparseHamiltonian.ODEZeroEnergy.native_solution_of_zero_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEZeroEnergy.native_solution_of_zero_energy

/-- info: 'SparseHamiltonian.ODEZeroEnergy.branchEvolution_eq_one_of_matrix_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEZeroEnergy.branchEvolution_eq_one_of_matrix_zero

/-- info: 'SparseHamiltonian.ODEZeroTime.program_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEZeroTime.program_unitary

/-- info: 'SparseHamiltonian.ODEZeroTime.program_costs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEZeroTime.program_costs

/-- info: 'SparseHamiltonian.ODEZeroTime.success_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEZeroTime.success_probability

/-- info: 'SparseHamiltonian.ODEZeroTime.source_trial_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEZeroTime.source_trial_certificate

/-- info: 'SparseHamiltonian.ODEZeroTime.zero_time_trial_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEZeroTime.zero_time_trial_certificate

/-- info: 'SparseHamiltonian.ODEDegenerateSource.actual_coefficients_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEDegenerateSource.actual_coefficients_eq

/-- info: 'SparseHamiltonian.ODEDegenerateSource.exact_source_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEDegenerateSource.exact_source_certificate

/-- info: 'SparseHamiltonian.ODEDegenerateSource.publicSeed_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEDegenerateSource.publicSeed_unit

/-- info: 'SparseHamiltonian.ODEDegenerateSource.publicOutput_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEDegenerateSource.publicOutput_isometry

/-- info: 'SparseHamiltonian.ODEDegenerateSource.preparation_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEDegenerateSource.preparation_matrix_cost

/-- info: 'SparseHamiltonian.ODEDegenerateSource.public_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEDegenerateSource.public_geometry

/-- info: 'SparseHamiltonian.ODEDegenerateSource.counted_pointwise_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEDegenerateSource.counted_pointwise_correct

/-- info: 'SparseHamiltonian.ODEDegenerateSource.randomized_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEDegenerateSource.randomized_solver

/-- info: 'SparseHamiltonian.ODEMainEndpoint.zero_time_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEMainEndpoint.zero_time_solver

/-- info: 'SparseHamiltonian.ODEMainEndpoint.parameter_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEMainEndpoint.parameter_cases

/-- info: 'SparseHamiltonian.ODEMainEndpoint.source_only_trial_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEMainEndpoint.source_only_trial_certificate

/-- info: 'SparseHamiltonian.ODEMainEndpoint.zero_energy_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEMainEndpoint.zero_energy_solver

/-- info: 'SparseHamiltonian.ODEMainEndpoint.solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEMainEndpoint.solver

/-- info: 'SparseHamiltonian.ODESourcePublicNorms.mass_eq_of_norms_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourcePublicNorms.mass_eq_of_norms_eq

/-- info: 'SparseHamiltonian.ODESourcePublicNorms.probability_eq_of_norms_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourcePublicNorms.probability_eq_of_norms_eq

/-- info: 'SparseHamiltonian.ODESourcePublicNorms.coefficients_eq_of_norms_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourcePublicNorms.coefficients_eq_of_norms_eq

/-- info: 'SparseHamiltonian.ODESourcePublicNorms.publicProbability_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourcePublicNorms.publicProbability_nonneg

/-- info: 'SparseHamiltonian.ODESourcePublicNorms.sum_publicProbability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourcePublicNorms.sum_publicProbability

/-- info: 'SparseHamiltonian.ODESourcePublicNorms.publicCoefficients_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourcePublicNorms.publicCoefficients_mass

/-- info: 'SparseHamiltonian.ODESourcePublicNorms.actual_probability_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourcePublicNorms.actual_probability_eq

/-- info: 'SparseHamiltonian.ODESourcePublicNorms.actual_coefficients_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourcePublicNorms.actual_coefficients_eq

/-- info: 'SparseHamiltonian.ODESourcePublicNorms.source_coefficients_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODESourcePublicNorms.source_coefficients_eq

/-- info: 'SparseHamiltonian.ODEPrimitiveSourceJoin.logicalTrials_eq_publicLogicalTrials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEPrimitiveSourceJoin.logicalTrials_eq_publicLogicalTrials

/-- info: 'SparseHamiltonian.ODEFinalNativeSource.trials_eq_publicTrials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeSource.trials_eq_publicTrials

/-- info: 'SparseHamiltonian.ODEFinalNativeSource.seed_eq_of_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeSource.seed_eq_of_coefficients

/-- info: 'SparseHamiltonian.ODEFinalNativeSource.output_eq_of_coefficients' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEFinalNativeSource.output_eq_of_coefficients

/-- info: 'SparseHamiltonian.ODEUniformNativeSource.coefficient_trial_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEUniformNativeSource.coefficient_trial_certificate

/-- info: 'SparseHamiltonian.ODEUniformPositiveEndpoint.positive_time_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEUniformPositiveEndpoint.positive_time_solver

/-- info: 'SparseHamiltonian.ODEUniformBoundary.zero_energy_positive_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEUniformBoundary.zero_energy_positive_mass

/-- info: 'SparseHamiltonian.ODEUniformBoundary.zero_energy_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEUniformBoundary.zero_energy_solver

/-- info: 'SparseHamiltonian.ODEUniformBoundary.zero_time_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEUniformBoundary.zero_time_solver

/-- info: 'SparseHamiltonian.ODEUniformMain.source_mass_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEUniformMain.source_mass_pos

/-- info: 'SparseHamiltonian.ODEUniformMain.solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEUniformMain.solver

/-- info: 'SparseHamiltonian.ImprovedSparseODE.ratio_budget_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedSparseODE.ratio_budget_iff

/-- info: 'SparseHamiltonian.ImprovedSparseODE.solver_of_nonempty_promise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedSparseODE.solver_of_nonempty_promise

/-- info: 'SparseHamiltonian.ImprovedSparseODE.solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ImprovedSparseODE.solver

/-- info: 'SparseHamiltonian.ODEOperationalBounds.operational_guarantees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEOperationalBounds.operational_guarantees

/-- info: 'SparseHamiltonian.ODEOperationalBounds.common_energy_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.ODEOperationalBounds.common_energy_queries
