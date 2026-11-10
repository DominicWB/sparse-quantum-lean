import GeneralSourceODE.Durations
import GeneralSourceODE.Branch
import GeneralSourceODE.Weights
import GeneralSourceODE.Compiled
import GeneralSourceODE.Counted
import GeneralSourceODE.Primitive
import GeneralSourceODE.Native
import GeneralSourceODE.Target
import GeneralSourceODE.Duhamel
import GeneralSourceODE.Oracles
import GeneralSourceODE.Theorem
import GeneralSourceODE.Corollaries

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (118 theorems), beginning
with the main theorems, then in module order. Every report lists exactly `propext`,
`Classical.choice` and `Quot.sound`. -/

/-! ### Final theorems: Theorem `ode:thm:time` with the general source interface, Duhamel's formula,
the propagated target and the separate source counts -/

/-- info: 'SparseHamiltonian.GeneralSourceODE.solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.solver

/-- info: 'SparseHamiltonian.GeneralSourceODE.propagated_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.propagated_solver

/-- info: 'SparseHamiltonian.GeneralSourceODE.duhamel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.duhamel

/-- info: 'SparseHamiltonian.GeneralSourceODE.exists_isPropagator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.exists_isPropagator

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.actual_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.actual_certificate

/-- info: 'SparseHamiltonian.GeneralSourceODE.target_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.target_error

/-- info: 'SparseHamiltonian.GeneralSourceODE.branch_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.branch_error

/-- info: 'SparseHamiltonian.GeneralSourceODE.Native.trial_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Native.trial_certificate

/-! ### Clipped clock, durations and the LCHS product family (`Durations`) -/

/-- info: 'SparseHamiltonian.GeneralSourceODE.clip_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.clip_zero

/-- info: 'SparseHamiltonian.GeneralSourceODE.le_clip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.le_clip

/-- info: 'SparseHamiltonian.GeneralSourceODE.slot_le_clip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.slot_le_clip

/-- info: 'SparseHamiltonian.GeneralSourceODE.slot_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.slot_mono

/-- info: 'SparseHamiltonian.GeneralSourceODE.clip_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.clip_mono

/-- info: 'SparseHamiltonian.GeneralSourceODE.width_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.width_nonneg

/-- info: 'SparseHamiltonian.GeneralSourceODE.slot_succ_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.slot_succ_sub

/-- info: 'SparseHamiltonian.GeneralSourceODE.width_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.width_le

/-- info: 'SparseHamiltonian.GeneralSourceODE.slot_le_of_width_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.slot_le_of_width_pos

/-- info: 'SparseHamiltonian.GeneralSourceODE.mem_slot_of_width_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.mem_slot_of_width_pos

/-- info: 'SparseHamiltonian.GeneralSourceODE.clip_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.clip_le

/-- info: 'SparseHamiltonian.GeneralSourceODE.clip_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.clip_last

/-- info: 'SparseHamiltonian.GeneralSourceODE.startTime_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.startTime_nonneg

/-- info: 'SparseHamiltonian.GeneralSourceODE.startTime_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.startTime_le

/-- info: 'SparseHamiltonian.GeneralSourceODE.durations_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.durations_nonneg

/-- info: 'SparseHamiltonian.GeneralSourceODE.durations_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.durations_le

/-- info: 'SparseHamiltonian.GeneralSourceODE.nodePropagator_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.nodePropagator_norm_le_one

/-- info: 'SparseHamiltonian.GeneralSourceODE.slotTimes_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.slotTimes_nonneg

/-- info: 'SparseHamiltonian.GeneralSourceODE.slotTimes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.slotTimes_eq

/-- info: 'SparseHamiltonian.GeneralSourceODE.slotTimes_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.slotTimes_le

/-- info: 'SparseHamiltonian.GeneralSourceODE.family_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.family_analyticAt

/-- info: 'SparseHamiltonian.GeneralSourceODE.family_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.family_norm_le_one

/-- info: 'SparseHamiltonian.GeneralSourceODE.family_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.family_lipschitz

/-- info: 'SparseHamiltonian.GeneralSourceODE.family_neg_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.family_neg_I

/-- info: 'SparseHamiltonian.GeneralSourceODE.branchEvolution_eq_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.branchEvolution_eq_family

/-! ### Propagation error of one branch (`Branch`) -/

/-- info: 'SparseHamiltonian.GeneralSourceODE.homogeneous_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.homogeneous_norm_le

/-! ### Label operators and the weight identities (`Weights`) -/

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.sum_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.sum_single

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.apply_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.apply_eq_sum

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.amp_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.amp_mul

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.amp_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.amp_one

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.amp_eq_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.amp_eq_inner

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.amp_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.amp_adjoint

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.act_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.act_apply

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.act_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.act_mul

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.act_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.act_one

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.act_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.act_adjoint

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.act_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.act_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.pointWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.pointWeight_nonneg

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.pointWeight_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.pointWeight_self

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.pointWeight_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.pointWeight_sum

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.coefficientPhase_real_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.coefficientPhase_real_mul

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.probability_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.probability_product

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.act_coefficientInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.act_coefficientInput

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.act_comp_coefficientOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.act_comp_coefficientOutput

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.loader_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.loader_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.phaseGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.phaseGate_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.Weights.phase_loader_coefficientInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Weights.phase_loader_coefficientInput

/-! ### The compiled preparation circuit (`Compiled`) -/

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.prep_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.prep_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.adjoint_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.adjoint_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.sourceFamily_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.sourceFamily_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.program_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.program_eval

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.program_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.program_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.program_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.program_matrix_cost

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.program_source_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.program_source_cost

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.program_source_total_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.program_source_total_cost

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.decoded_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.decoded_eq

/-! ### Counted amplification (`Counted`) -/

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.seedCoefficients_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.seedCoefficients_mass

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.decoded_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.decoded_actual

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.compiled_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.compiled_geometry

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.counted_source_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.counted_source_certificate

/-! ### Primitive compilation and public trials (`Primitive`) -/

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.trialCertificate_of_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.trialCertificate_of_transfer

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.logicalTrials_eq_publicLogicalTrials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.logicalTrials_eq_publicLogicalTrials

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.primitive_source_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.primitive_source_certificate

/-- info: 'SparseHamiltonian.GeneralSourceODE.Compiled.public_source_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Compiled.public_source_certificate

/-! ### Native coordinates (`Native`) -/

/-- info: 'SparseHamiltonian.GeneralSourceODE.Native.matrixOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Native.matrixOracle_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.Native.matrix_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Native.matrix_valid

/-- info: 'SparseHamiltonian.GeneralSourceODE.Native.input_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Native.input_isometry

/-- info: 'SparseHamiltonian.GeneralSourceODE.Native.physicalOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Native.physicalOracle_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.Native.seed_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Native.seed_unit

/-- info: 'SparseHamiltonian.GeneralSourceODE.Native.output_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Native.output_isometry

/-! ### Source vectors, phases and the propagated target (`Target`) -/

/-- info: 'SparseHamiltonian.GeneralSourceODE.phases_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.phases_norm

/-- info: 'SparseHamiltonian.GeneralSourceODE.mass_sources' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.mass_sources

/-- info: 'SparseHamiltonian.GeneralSourceODE.unitDirection_complex_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.unitDirection_complex_smul

/-- info: 'SparseHamiltonian.GeneralSourceODE.phased_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.phased_isometry

/-- info: 'SparseHamiltonian.GeneralSourceODE.phased_prepares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.phased_prepares

/-- info: 'SparseHamiltonian.GeneralSourceODE.nodeTarget_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.nodeTarget_norm_le

/-! ### Duhamel's formula (`Duhamel`) -/

/-- info: 'SparseHamiltonian.GeneralSourceODE.solvesODE_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.solvesODE_sub

/-- info: 'SparseHamiltonian.GeneralSourceODE.solvesODE_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.solvesODE_smul

/-- info: 'SparseHamiltonian.GeneralSourceODE.solvesODE_sub_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.solvesODE_sub_const

/-- info: 'SparseHamiltonian.GeneralSourceODE.solvesODE_zero_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.solvesODE_zero_sub

/-- info: 'SparseHamiltonian.GeneralSourceODE.homogeneous_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.homogeneous_unique

/-- info: 'SparseHamiltonian.GeneralSourceODE.solvesODE_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.solvesODE_norm_le

/-- info: 'SparseHamiltonian.GeneralSourceODE.accretive_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.accretive_sub

/-- info: 'SparseHamiltonian.GeneralSourceODE.IsPropagator.lincomb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.IsPropagator.lincomb

/-- info: 'SparseHamiltonian.GeneralSourceODE.IsPropagator.sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.IsPropagator.sub

/-- info: 'SparseHamiltonian.GeneralSourceODE.IsPropagator.norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.IsPropagator.norm_le

/-- info: 'SparseHamiltonian.GeneralSourceODE.IsPropagator.cocycle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.IsPropagator.cocycle

/-- info: 'SparseHamiltonian.GeneralSourceODE.IsPropagator.move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.IsPropagator.move

/-- info: 'SparseHamiltonian.GeneralSourceODE.forced_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.forced_move

/-- info: 'SparseHamiltonian.GeneralSourceODE.duhamel_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.duhamel_lipschitz

/-- info: 'SparseHamiltonian.GeneralSourceODE.forcing_move' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.forcing_move

/-- info: 'SparseHamiltonian.GeneralSourceODE.forcing_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.forcing_continuousOn

/-- info: 'SparseHamiltonian.GeneralSourceODE.duhamel_hasDerivWithinAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.duhamel_hasDerivWithinAt

/-! ### Separate counts of the supplied source operations (`Oracles`) -/

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.cost_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.cost_add

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.sourceOperation_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.sourceOperation_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.actualOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.actualOracle_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.phaseGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.phaseGate_unitary

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.sourcePhysical_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.sourcePhysical_mul

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.implementation_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.implementation_eval

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.implementation_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.implementation_matrix

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.implementation_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.implementation_weight

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.implementation_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.implementation_load

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.implementation_unweight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.implementation_unweight

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.implementation_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.implementation_source

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.ofCircuits_meanSuccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.ofCircuits_meanSuccess

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.ofCircuits_oneTrialDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.ofCircuits_oneTrialDensity

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.fourTrials_successMass_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.fourTrials_successMass_congr

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.repeat_successDensity_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.repeat_successDensity_congr

/-- info: 'SparseHamiltonian.GeneralSourceODE.Oracles.fourTrials_conditionalDensity_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.Oracles.fourTrials_conditionalDensity_congr

/-! ### Theorem `ode:thm:time` with the general source interface (`Theorem`) -/

/-! ### Existence of the propagator (`Corollaries`) -/

/-- info: 'SparseHamiltonian.GeneralSourceODE.solvesODE_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GeneralSourceODE.solvesODE_shift
