import GateEfficientHamiltonian.Circuit.Theorem

/-! ## Axiom audits

Each audit fails to compile if the declaration depends on an axiom other than
`propext`, `Classical.choice` and `Quot.sound`.  The first group covers the
milestone development, the second the gate-level simulator and its final
theorem. -/

/-- info: 'SparseHamiltonian.GateKnownControl.run_circuit_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateKnownControl.run_circuit_clean

/-- info: 'SparseHamiltonian.GateKnownControl.run_circuit_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateKnownControl.run_circuit_inverse


/-- info: 'SparseHamiltonian.GateFilterTree.signCircuit_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterTree.signCircuit_intertwines

/-- info: 'SparseHamiltonian.GateFilterTree.signedCoefficientCircuit_prepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterTree.signedCoefficientCircuit_prepares

/-- info: 'SparseHamiltonian.GateFilterTree.signedCoefficientCircuit_unprepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterTree.signedCoefficientCircuit_unprepares

/-- info: 'SparseHamiltonian.GateFilterHilbert.signedTableCircuit_prepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterHilbert.signedTableCircuit_prepares

/-- info: 'SparseHamiltonian.GateFilterHilbert.signedTableCircuit_unprepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterHilbert.signedTableCircuit_unprepares

/-- info: 'SparseHamiltonian.GateFilterHilbert.reference_signedTableCircuit_prepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterHilbert.reference_signedTableCircuit_prepares

/-- info: 'SparseHamiltonian.GateReuseFilterPhysical.output_original_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateReuseFilterPhysical.output_original_amplitude

/-- info: 'SparseHamiltonian.GateReuseFilterPhysical.paired_preparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateReuseFilterPhysical.paired_preparation


/-- info: 'SparseHamiltonian.GateReuseFilterPhysical.physical_preparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateReuseFilterPhysical.physical_preparation

/-- info: 'SparseHamiltonian.GateReuseFilterPhysical.prepares_original_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateReuseFilterPhysical.prepares_original_amplitude


/-- info: 'SparseHamiltonian.GateFilterTree.MassTree.compile_full_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterTree.MassTree.compile_full_table

/-- info: 'SparseHamiltonian.GateFilterTree.MassTree.compile_full_table_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterTree.MassTree.compile_full_table_inverse

/-- info: 'SparseHamiltonian.GateFilterHilbert.gate_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterHilbert.gate_intertwines

/-- info: 'SparseHamiltonian.GateFilterHilbert.run_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterHilbert.run_inverse

/-- info: 'SparseHamiltonian.GateFilterHilbert.compile_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterHilbert.compile_unitary

/-- info: 'SparseHamiltonian.GateFilterHilbert.reference_compile_coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterHilbert.reference_compile_coordinates

/-- info: 'SparseHamiltonian.GateFilterHilbert.tableCircuit_prepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterHilbert.tableCircuit_prepares

/-- info: 'SparseHamiltonian.GateFilterHilbert.tableCircuit_adjoint_unprepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterHilbert.tableCircuit_adjoint_unprepares

/-- info: 'SparseHamiltonian.GateFilterHilbert.tableState_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterHilbert.tableState_norm

/-- info: 'SparseHamiltonian.GateFilterHilbert.reference_tableCircuit_prepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterHilbert.reference_tableCircuit_prepares

/-- info: 'SparseHamiltonian.GateFilterTable.massTree_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterTable.massTree_mass

/-- info: 'SparseHamiltonian.GateFilterTable.smoothing_operator_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterTable.smoothing_operator_eq

/-- info: 'SparseHamiltonian.GateFilterTable.circuit_length_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterTable.circuit_length_lt



/-- info: 'SparseHamiltonian.GateDyadicBoundary.chronological_eq_compressed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateDyadicBoundary.chronological_eq_compressed

/-- info: 'SparseHamiltonian.GateDyadicBoundary.chronological_sqrt_eq_compressed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateDyadicBoundary.chronological_sqrt_eq_compressed

/-- info: 'SparseHamiltonian.GatePrefixCircuit.circuit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePrefixCircuit.circuit_correct

/-- info: 'SparseHamiltonian.GatePrefixInverse.run_inverse_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePrefixInverse.run_inverse_comp

/-- info: 'SparseHamiltonian.GatePrefixInverse.run_comp_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePrefixInverse.run_comp_inverse

/-- info: 'SparseHamiltonian.GateDyadicPrefixBridge.input_circuit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateDyadicPrefixBridge.input_circuit_correct

/-- info: 'SparseHamiltonian.GateDyadicPrefixBridge.output_circuit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateDyadicPrefixBridge.output_circuit_correct

/-- info: 'SparseHamiltonian.GateDyadicUnitary.inputCoefficients_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateDyadicUnitary.inputCoefficients_unitary

/-- info: 'SparseHamiltonian.GateDyadicUnitary.outputCoefficients_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateDyadicUnitary.outputCoefficients_unitary

/-- info: 'SparseHamiltonian.GateDyadicUnitary.input_inverse_circuit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateDyadicUnitary.input_inverse_circuit_correct

/-- info: 'SparseHamiltonian.GateCentralBoundary.circuit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCentralBoundary.circuit_correct

/-- info: 'SparseHamiltonian.GatePrivateControl.program_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePrivateControl.program_apply

/-- info: 'SparseHamiltonian.GatePrivateControl.program_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePrivateControl.program_unitary

/-- info: 'SparseHamiltonian.GateBinaryReuse.run_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryReuse.run_invariant

/-- info: 'SparseHamiltonian.GateBinaryReuse.successfulOutput_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBinaryReuse.successfulOutput_eq

/-- info: 'SparseHamiltonian.GateUniformRange.amplified_initial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateUniformRange.amplified_initial

/-- info: 'SparseHamiltonian.GateUniformRange.rangeProgram_prepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateUniformRange.rangeProgram_prepares

/-- info: 'SparseHamiltonian.GatePhysicalBoundary.run_lift_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePhysicalBoundary.run_lift_true

/-- info: 'SparseHamiltonian.GatePhysicalBoundary.run_lift_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePhysicalBoundary.run_lift_false

/-- info: 'SparseHamiltonian.GatePhysicalBoundary.inputInverseCircuit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePhysicalBoundary.inputInverseCircuit_correct

/-- info: 'SparseHamiltonian.GatePhysicalBoundary.outputCircuit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePhysicalBoundary.outputCircuit_correct

/-- info: 'SparseHamiltonian.GatePhysicalBoundary.inputInverseCircuit_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePhysicalBoundary.inputInverseCircuit_valid

/-- info: 'SparseHamiltonian.GatePhysicalBoundary.outputCircuit_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePhysicalBoundary.outputCircuit_valid

/-- info: 'SparseHamiltonian.GatePhysicalBoundary.central_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePhysicalBoundary.central_intertwines

/-- info: 'SparseHamiltonian.GatePhysicalBoundary.centralCircuit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePhysicalBoundary.centralCircuit_correct

/-- info: 'SparseHamiltonian.GatePhysicalBoundary.boundaryCircuit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePhysicalBoundary.boundaryCircuit_correct

/-- info: 'SparseHamiltonian.GatePhysicalBoundary.boundaryCircuit_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePhysicalBoundary.boundaryCircuit_valid

/-- info: 'SparseHamiltonian.GatePrivatePointer.incrementCircuit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePrivatePointer.incrementCircuit_correct

/-- info: 'SparseHamiltonian.GatePrivatePointer.circuitLinear_reverse_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePrivatePointer.circuitLinear_reverse_comp

/-- info: 'SparseHamiltonian.GatePointerEncoding.wordFin_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GatePointerEncoding.wordFin_bijective

/-- info: 'SparseHamiltonian.GateConstantCompare.compareCircuit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateConstantCompare.compareCircuit_correct

/-- info: 'SparseHamiltonian.GateConstantCompare.circuitLinear_reverse_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateConstantCompare.circuitLinear_reverse_comp

/-- info: 'SparseHamiltonian.GateControlledCompare.rangeCompareCircuit_kickback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateControlledCompare.rangeCompareCircuit_kickback

/-- info: 'SparseHamiltonian.GateControlledCompare.circuitLinear_reverse_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateControlledCompare.circuitLinear_reverse_comp

/-- info: 'SparseHamiltonian.GateControlledCompare.acceptedCompareCircuit_kickback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateControlledCompare.acceptedCompareCircuit_kickback

/-- info: 'SparseHamiltonian.GateControlledCompare.zeroStateReflectionCircuit_kickback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateControlledCompare.zeroStateReflectionCircuit_kickback

/-- info: 'SparseHamiltonian.GateWalshWords.half_pow_eq_uniformAmplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateWalshWords.half_pow_eq_uniformAmplitude

/-- info: 'SparseHamiltonian.GateWalshWords.relabelCoordinates_prepares_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateWalshWords.relabelCoordinates_prepares_uniform

/-- info: 'SparseHamiltonian.GateWalshInverse.circuit_inverse_and_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateWalshInverse.circuit_inverse_and_counts

/-- info: 'SparseHamiltonian.GateConstantCompare.rangeCompareCircuit_kickback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateConstantCompare.rangeCompareCircuit_kickback

/-- info: 'SparseHamiltonian.GateWalshHilbert.uniformWords_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateWalshHilbert.uniformWords_unitary

/-- info: 'SparseHamiltonian.GateWalshHilbert.uniformWords_prepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateWalshHilbert.uniformWords_prepares

/-- info: 'SparseHamiltonian.GateWalshHilbert.actual_rangeProgram_prepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateWalshHilbert.actual_rangeProgram_prepares

/-- info: 'SparseHamiltonian.GateWalshHilbert.actual_rangeProgram_flag_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateWalshHilbert.actual_rangeProgram_flag_clean

/-- info: 'SparseHamiltonian.GateWalshHilbert.signedGate_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateWalshHilbert.signedGate_apply

/-- info: 'SparseHamiltonian.GateWalshHilbert.wordTransform_adjoint_implementation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateWalshHilbert.wordTransform_adjoint_implementation

/-- info: 'SparseHamiltonian.GateUniformRange.goodPhase_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateUniformRange.goodPhase_word

/-- info: 'SparseHamiltonian.GateWalshHilbert.zeroReflection_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateWalshHilbert.zeroReflection_word

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.rangeUnitary_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.rangeUnitary_unitary

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.normalizedKickback_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.normalizedKickback_norm

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.acceptedCompare_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.acceptedCompare_normalized

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.zeroReflection_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.zeroReflection_normalized

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.minusPreparation_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.minusPreparation_clean

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.minusPreparation_adjoint_minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.minusPreparation_adjoint_minus

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.markedGate_layout_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.markedGate_layout_apply

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.prepareMinus_adjoint_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.prepareMinus_adjoint_comp

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.packet_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.packet_norm

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.prepareMinus_cleanPacket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.prepareMinus_cleanPacket

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.prepareMinus_adjoint_minusPacket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.prepareMinus_adjoint_minusPacket

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.physicalMinusPreparationCircuit_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.physicalMinusPreparationCircuit_eval

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.markedLayout_normalizedKickback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.markedLayout_normalizedKickback

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.normalizedKickback_eq_minusPacket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.normalizedKickback_eq_minusPacket

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.prepareMinus_cleanComputational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.prepareMinus_cleanComputational

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.prepareMinus_adjoint_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.prepareMinus_adjoint_normalized

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.minusUnpreparationCircuit_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.minusUnpreparationCircuit_eval

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.physicalMinusUnpreparationCircuit_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.physicalMinusUnpreparationCircuit_eval

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.normalizedKickback_threshold_independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.normalizedKickback_threshold_independent

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.reflectionPair_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.reflectionPair_unitary

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.reflectionPair_normalized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.reflectionPair_normalized

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.fixedBasisEmbedding_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.fixedBasisEmbedding_apply

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.payloadEmbedding_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.payloadEmbedding_apply

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.logicalEmbedding_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.logicalEmbedding_norm

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.markedLayout_logicalEmbedding_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.markedLayout_logicalEmbedding_apply

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.logicalEmbedding_basis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.logicalEmbedding_basis

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.acceptedCompare_logicalBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.acceptedCompare_logicalBasis

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.zeroReflection_logicalBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.zeroReflection_logicalBasis

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.acceptedCompare_basis_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.acceptedCompare_basis_intertwines

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.zeroReflection_basis_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.zeroReflection_basis_intertwines

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.acceptedCompare_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.acceptedCompare_intertwines

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.zeroReflection_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.zeroReflection_intertwines

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.cleanLogicalEmbedding_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.cleanLogicalEmbedding_norm

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.markedLayout_cleanLogicalEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.markedLayout_cleanLogicalEmbedding

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.cleanLogicalEmbedding_cleanInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.cleanLogicalEmbedding_cleanInput

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.logicalLift_intertwines_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.logicalLift_intertwines_apply

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.physicalWordGate_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.physicalWordGate_apply

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.physicalAttenuation_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.physicalAttenuation_apply

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.physicalAttenuation_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.physicalAttenuation_adjoint_apply

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.physicalRangeCircuit_prepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.physicalRangeCircuit_prepares

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.physicalRangeCircuit_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.physicalRangeCircuit_unitary

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.preparationInverse_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.preparationInverse_eval

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.physicalRangeCircuit_unprepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.physicalRangeCircuit_unprepares

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.physicalRangeCircuit_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.physicalRangeCircuit_amplitude

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.physicalRangeCircuit_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.physicalRangeCircuit_reference

/-- info: 'SparseHamiltonian.GateRangeHilbertTransport.physicalRangePreparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateRangeHilbertTransport.physicalRangePreparation

/-- info: 'SparseHamiltonian.GateTableSplit.coefficients_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateTableSplit.coefficients_unitary

/-- info: 'SparseHamiltonian.GateTableSplit.coefficients_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateTableSplit.coefficients_split

/-- info: 'SparseHamiltonian.GateFilterTree.compile_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterTree.compile_intertwines

/-- info: 'SparseHamiltonian.GateFilterTree.MassTree.rotations_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterTree.MassTree.rotations_valid

/-- info: 'SparseHamiltonian.GateFilterTree.idealStep_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterTree.idealStep_apply

/-- info: 'SparseHamiltonian.GateFilterTree.run_inverse_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterTree.run_inverse_comp

/-- info: 'SparseHamiltonian.GateFilterTree.run_comp_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateFilterTree.run_comp_inverse

/-! ## Axiom audits for the gate-level simulator -/

/-- info: 'SparseHamiltonian.GateCircuit.Sim.gate_efficient_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.Sim.gate_efficient_simulation

/-- info: 'SparseHamiltonian.GateCircuit.Sim.amp_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.Sim.amp_error

/-- info: 'SparseHamiltonian.GateCircuit.Sim.amp_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.Sim.amp_agrees

/-- info: 'SparseHamiltonian.GateCircuit.Sim.ampI_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.Sim.ampI_counts

/-- info: 'SparseHamiltonian.GateCircuit.Sim.ampI_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.Sim.ampI_valid

/-- info: 'SparseHamiltonian.GateCircuit.Sim.lcu_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.Sim.lcu_block

/-- info: 'SparseHamiltonian.GateCircuit.Sim.select_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.Sim.select_block

/-- info: 'SparseHamiltonian.GateCircuit.Sim.chron_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.Sim.chron_boundary

/-- info: 'SparseHamiltonian.GateCircuit.Dyadic.chron_eq_compressed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.Dyadic.chron_eq_compressed

/-- info: 'SparseHamiltonian.GateBlockTransfer.amplified_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateBlockTransfer.amplified_error_le

/-- info: 'SparseHamiltonian.GateCircuit.Sim.net_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.Sim.net_agrees

/-- info: 'SparseHamiltonian.GateCircuit.Sim.inc_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.Sim.inc_agrees

/-- info: 'SparseHamiltonian.GateCircuit.Sim.range_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.Sim.range_agrees

/-- info: 'SparseHamiltonian.GateCircuit.Sim.prep_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.Sim.prep_agrees

/-- info: 'SparseHamiltonian.GateCircuit.Sim.zr_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.Sim.zr_agrees

/-- info: 'SparseHamiltonian.GateCircuit.Sim.card_simWire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateCircuit.Sim.card_simWire
