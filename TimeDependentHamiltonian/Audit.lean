import TimeDependentHamiltonian.Corollaries

/-! ## Axiom audits

Each audit fails to compile if the declaration depends on an axiom other than
`propext`, `Classical.choice` and `Quot.sound`. The audits cover every
theorem of the time-dependent library, beginning with the final theorem and
its corollaries. -/

/-! ### Final theorem and corollaries -/

/-- info: 'SparseHamiltonian.TimeDependent.simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.simulation

/-- info: 'SparseHamiltonian.TimeDependent.simulation_propagator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.simulation_propagator

/-- info: 'SparseHamiltonian.TimeDependent.simulation_with_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.simulation_with_reference

/-- info: 'SparseHamiltonian.TimeDependent.zero_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.zero_certificate

/-- info: 'SparseHamiltonian.TimeDependent.input_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.input_isometry

/-- info: 'SparseHamiltonian.TimeDependent.meshSize_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.meshSize_spec

/-- info: 'SparseHamiltonian.TimeDependent.zero_path_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.zero_path_identity

/-- info: 'SparseHamiltonian.TimeDependent.oracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.oracle_unitary

/-- info: 'SparseHamiltonian.TimeDependent.step_le_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.step_le_quarter

/-- info: 'SparseHamiltonian.TimeDependent.count_le_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.count_le_shape

/-- info: 'SparseHamiltonian.TimeDependent.sampledEvolution_normalize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.sampledEvolution_normalize

/-! ### Slot-dependent chronological operator, inverse and resolvent -/

/-- info: 'SparseHamiltonian.TimeDependent.orderedProduct_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.orderedProduct_zero

/-- info: 'SparseHamiltonian.TimeDependent.orderedProduct_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.orderedProduct_succ

/-- info: 'SparseHamiltonian.TimeDependent.orderedProduct_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.orderedProduct_const

/-- info: 'SparseHamiltonian.TimeDependent.orderedProduct_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.orderedProduct_norm_le

/-- info: 'SparseHamiltonian.TimeDependent.forcedState_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.forcedState_zero

/-- info: 'SparseHamiltonian.TimeDependent.forcedState_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.forcedState_succ

/-- info: 'SparseHamiltonian.TimeDependent.forcedState_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.forcedState_eq_sum

/-- info: 'SparseHamiltonian.TimeDependent.block_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.block_diagonal

/-- info: 'SparseHamiltonian.TimeDependent.block_below' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.block_below

/-- info: 'SparseHamiltonian.TimeDependent.block_above' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.block_above

/-- info: 'SparseHamiltonian.TimeDependent.privateState_eq_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.privateState_eq_blocks

/-- info: 'SparseHamiltonian.TimeDependent.operator_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.operator_apply

/-- info: 'SparseHamiltonian.TimeDependent.operator_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.operator_norm_le

/-- info: 'SparseHamiltonian.TimeDependent.inverse_public_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.inverse_public_state

/-- info: 'SparseHamiltonian.TimeDependent.forward_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.forward_inverse

/-- info: 'SparseHamiltonian.TimeDependent.forwardResponse_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.forwardResponse_injective

/-- info: 'SparseHamiltonian.TimeDependent.inverse_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.inverse_forward

/-- info: 'SparseHamiltonian.TimeDependent.forwardOperator_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.forwardOperator_restrict

/-- info: 'SparseHamiltonian.TimeDependent.inverseOperator_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.inverseOperator_restrict

/-- info: 'SparseHamiltonian.TimeDependent.forwardOperator_resolvent_denominator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.forwardOperator_resolvent_denominator

/-- info: 'SparseHamiltonian.TimeDependent.forwardOperator_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.forwardOperator_inverse

/-- info: 'SparseHamiltonian.TimeDependent.inverseOperator_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.inverseOperator_forward

/-- info: 'SparseHamiltonian.TimeDependent.resolvent_two_sided_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.resolvent_two_sided_inverse

/-- info: 'SparseHamiltonian.TimeDependent.exists_resolvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.exists_resolvent

/-! ### Slot-dependent clock colligation, catalyst and filter precision -/

/-- info: 'SparseHamiltonian.TimeDependent.forcedPublicState_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.forcedPublicState_slot

/-- info: 'SparseHamiltonian.TimeDependent.restrict_eq_toLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.restrict_eq_toLp

/-- info: 'SparseHamiltonian.TimeDependent.evolution_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.evolution_zero

/-- info: 'SparseHamiltonian.TimeDependent.evolution_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.evolution_succ

/-- info: 'SparseHamiltonian.TimeDependent.evolution_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.evolution_norm

/-- info: 'SparseHamiltonian.TimeDependent.stackedV_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.stackedV_apply

/-- info: 'SparseHamiltonian.TimeDependent.stackedV_eq_toLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.stackedV_eq_toLp

/-- info: 'SparseHamiltonian.TimeDependent.publicStateV_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.publicStateV_eq

/-- info: 'SparseHamiltonian.TimeDependent.catalyst_publicStateV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.catalyst_publicStateV

/-- info: 'SparseHamiltonian.TimeDependent.forcedState_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.forcedState_congr

/-- info: 'SparseHamiltonian.TimeDependent.operator_apply_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.operator_apply_restrict

/-- info: 'SparseHamiltonian.TimeDependent.stackedV_eq_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.stackedV_eq_restrict

/-- info: 'SparseHamiltonian.TimeDependent.stackedV_norm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.stackedV_norm_sq_le

/-- info: 'SparseHamiltonian.TimeDependent.slotAction_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.slotAction_apply

/-- info: 'SparseHamiltonian.TimeDependent.extend_slotAction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.extend_slotAction

/-- info: 'SparseHamiltonian.TimeDependent.slotAction_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.slotAction_norm

/-- info: 'SparseHamiltonian.TimeDependent.colligation_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.colligation_energy

/-- info: 'SparseHamiltonian.TimeDependent.privateV_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.privateV_norm_le_one

/-- info: 'SparseHamiltonian.TimeDependent.privateV_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.privateV_eq

/-- info: 'SparseHamiltonian.TimeDependent.exitV_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.exitV_apply

/-- info: 'SparseHamiltonian.TimeDependent.evolution_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.evolution_unitary

/-- info: 'SparseHamiltonian.TimeDependent.colligation_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.colligation_public

/-- info: 'SparseHamiltonian.TimeDependent.colligation_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.colligation_private

/-- info: 'SparseHamiltonian.TimeDependent.exitV_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.exitV_identity

/-- info: 'SparseHamiltonian.TimeDependent.exists_privateV_resolvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.exists_privateV_resolvent

/-- info: 'SparseHamiltonian.TimeDependent.filter_precisionV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.filter_precisionV

/-- info: 'SparseHamiltonian.TimeDependent.evolution_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.evolution_norm_le_one

/-- info: 'SparseHamiltonian.TimeDependent.evolution_sub_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.evolution_sub_norm_le

/-- info: 'SparseHamiltonian.TimeDependent.evolution_sub_norm_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.evolution_sub_norm_le_mul

/-! ### Amplified simulation and query certificate -/

/-- info: 'SparseHamiltonian.TimeDependent.step_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.step_energy

/-- info: 'SparseHamiltonian.TimeDependent.exists_precise_implementationV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.exists_precise_implementationV

/-- info: 'SparseHamiltonian.TimeDependent.layerV_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.layerV_factor

/-- info: 'SparseHamiltonian.TimeDependent.layerV_implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.layerV_implementsOn

/-- info: 'SparseHamiltonian.TimeDependent.implementationV_query_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.implementationV_query_certificate

/-! ### Coherent sampled-time oracles and the native layer -/

/-- info: 'SparseHamiltonian.TimeDependent.timeIndexed_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.timeIndexed_apply

/-- info: 'SparseHamiltonian.TimeDependent.timeIndexed_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.timeIndexed_mul

/-- info: 'SparseHamiltonian.TimeDependent.timeIndexed_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.timeIndexed_star

/-- info: 'SparseHamiltonian.TimeDependent.timeIndexed_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.timeIndexed_one

/-- info: 'SparseHamiltonian.TimeDependent.timeIndexed_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.timeIndexed_unitary

/-- info: 'SparseHamiltonian.TimeDependent.slotInject_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.slotInject_apply

/-- info: 'SparseHamiltonian.TimeDependent.timeEmbed_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.timeEmbed_apply

/-- info: 'SparseHamiltonian.TimeDependent.timeEmbed_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.timeEmbed_symm_apply

/-- info: 'SparseHamiltonian.TimeDependent.timeIndexed_timeEmbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.timeIndexed_timeEmbed

/-- info: 'SparseHamiltonian.TimeDependent.timeEmbed_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.timeEmbed_single

/-- info: 'SparseHamiltonian.TimeDependent.timeOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.timeOracle_unitary

/-- info: 'SparseHamiltonian.TimeDependent.liftProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.liftProgram_count

/-- info: 'SparseHamiltonian.TimeDependent.liftProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.liftProgram_cost

/-- info: 'SparseHamiltonian.TimeDependent.liftProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.liftProgram_eval

/-- info: 'SparseHamiltonian.TimeDependent.timeOracle_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.timeOracle_valid

/-- info: 'SparseHamiltonian.TimeDependent.sampledOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.sampledOracle_unitary

/-- info: 'SparseHamiltonian.TimeDependent.sampledProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.sampledProgram_count

/-- info: 'SparseHamiltonian.TimeDependent.sampledProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.sampledProgram_cost

/-- info: 'SparseHamiltonian.TimeDependent.sampledProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.sampledProgram_intertwines

/-- info: 'SparseHamiltonian.TimeDependent.sampledOracle_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.sampledOracle_valid

/-- info: 'SparseHamiltonian.TimeDependent.activeClock_eq_activeClockV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.activeClock_eq_activeClockV

/-- info: 'SparseHamiltonian.TimeDependent.active_intertwinesV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.active_intertwinesV

/-- info: 'SparseHamiltonian.TimeDependent.program_clean_intertwinesV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.program_clean_intertwinesV

/-- info: 'SparseHamiltonian.TimeDependent.clean_implementsOnV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.clean_implementsOnV

/-- info: 'SparseHamiltonian.TimeDependent.Sampled.oracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.Sampled.oracle_unitary

/-- info: 'SparseHamiltonian.TimeDependent.Sampled.program_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.Sampled.program_count

/-- info: 'SparseHamiltonian.TimeDependent.Sampled.implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.Sampled.implementsOn

/-- info: 'SparseHamiltonian.TimeDependent.Sampled.step_smul_compressed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.Sampled.step_smul_compressed

/-- info: 'SparseHamiltonian.TimeDependent.Sampled.isometry_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.Sampled.isometry_comp

/-- info: 'SparseHamiltonian.TimeDependent.Sampled.sampled_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.Sampled.sampled_core

/-- info: 'SparseHamiltonian.TimeDependent.Sampled.exists_sampled_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.Sampled.exists_sampled_simulation

/-! ### Propagator, discretisation and existence -/

/-- info: 'SparseHamiltonian.TimeDependent.SolvesOn.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.SolvesOn.mono

/-- info: 'SparseHamiltonian.TimeDependent.SolvesOn.norm_apply_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.SolvesOn.norm_apply_eq

/-- info: 'SparseHamiltonian.TimeDependent.SolvesOn.norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.SolvesOn.norm_le_one

/-- info: 'SparseHamiltonian.TimeDependent.real_smul_skew' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.real_smul_skew

/-- info: 'SparseHamiltonian.TimeDependent.duhamel_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.duhamel_step

/-- info: 'SparseHamiltonian.TimeDependent.propagator_telescope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.propagator_telescope

/-- info: 'SparseHamiltonian.TimeDependent.mesh_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.mesh_error

/-- info: 'SparseHamiltonian.TimeDependent.exists_local_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.exists_local_solution

/-- info: 'SparseHamiltonian.TimeDependent.exists_solvesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.exists_solvesOn

/-- info: 'SparseHamiltonian.TimeDependent.exists_solvesOn_of_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependent.exists_solvesOn_of_lipschitz
