import DysonFullClass.Perturb
import DysonFullClass.Clip
import DysonFullClass.Select
import DysonFullClass.Atten
import DysonFullClass.Target
import DysonFullClass.Herald
import DysonFullClass.Theorem
import DysonFullClass.Single
import DysonFullClass.Approx
import DysonFullClass.Corollaries
import DysonFullClass.Coverage
import DysonFullClass.Examples

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (140 theorems), beginning
with the main theorems, then in module order. Every report lists exactly `propext`,
`Classical.choice` and `Quot.sound`. -/

/-! ### Final theorems: Lemma `odel:lem:dyson` on the full time-dependent class, its
fixed-parameter corollaries and the main steps -/

/-- info: 'DysonFullClass.full_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.full_single

/-- info: 'DysonFullClass.full_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.full_approx

/-- info: 'DysonFullClass.full_actual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.full_actual

/-- info: 'DysonFullClass.full_dyson_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.full_dyson_shape

/-- info: 'DysonFullClass.full_dyson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.full_dyson

/-- info: 'DysonFullClass.full_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.full_bound

/-- info: 'DysonFullClass.full_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.full_fixed

/-- info: 'DysonFullClass.full_no_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.full_no_uniform

/-- info: 'DysonFullClass.approx_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.approx_fixed

/-- info: 'DysonFullClass.approx_no_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.approx_no_uniform

/-- info: 'DysonFullClass.fDecoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fDecoded

/-- info: 'DysonFullClass.dysonTarget_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.dysonTarget_error

/-- info: 'DysonFullClass.propagator_perturb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.propagator_perturb

/-- info: 'DysonFullClass.clip_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.clip_sub_le

/-- info: 'DysonFullClass.fullValidAt_of_raw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullValidAt_of_raw

/-- info: 'DysonFullClass.fullValidAt_of_clipped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullValidAt_of_clipped

/-- info: 'DysonFullClass.fullActualOracleW_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullActualOracleW_clean

/-- info: 'DysonFullClass.fullImplementation_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullImplementation_eval

/-! ### The perturbation lemma (`Perturb`) -/

/-- info: 'DysonFullClass.integral_mul_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.integral_mul_exp

/-- info: 'DysonFullClass.integral_exp_weight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.integral_exp_weight_le

/-- info: 'DysonFullClass.accretive_add_smul_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.accretive_add_smul_one

/-- info: 'DysonFullClass.exp_norm_le_of_reLower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.exp_norm_le_of_reLower

/-- info: 'DysonFullClass.reLower_of_accretive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.reLower_of_accretive

/-- info: 'DysonFullClass.cell_perturb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.cell_perturb

/-- info: 'DysonFullClass.node_perturb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.node_perturb

/-! ### Radial clipping on the original access (`Clip`) -/

/-- info: 'DysonFullClass.radialClip_of_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.radialClip_of_norm_le

/-- info: 'DysonFullClass.radialClip_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.radialClip_zero

/-- info: 'DysonFullClass.norm_radialClip_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.norm_radialClip_le

/-- info: 'DysonFullClass.radialClip_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.radialClip_eq_zero_iff

/-- info: 'DysonFullClass.norm_radialClip_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.norm_radialClip_sub_le

/-- info: 'DysonFullClass.oracles_clipData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.oracles_clipData

/-- info: 'DysonFullClass.clipData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.clipData_matrix

/-- info: 'DysonFullClass.clipData_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.clipData_scale

/-- info: 'DysonFullClass.clipData_matrix_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.clipData_matrix_of_le

/-- info: 'DysonFullClass.matrixOperator_opMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.matrixOperator_opMatrix

/-- info: 'DysonFullClass.norm_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.norm_entry_le

/-- info: 'DysonFullClass.norm_entry_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.norm_entry_sub_le

/-- info: 'DysonFullClass.data_row_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.data_row_sparse

/-- info: 'DysonFullClass.data_column_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.data_column_sparse

/-! ### The Dyson SELECT on arbitrary branch labels (`Select`) -/

/-- info: 'DysonFullClass.gLiftSlot_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gLiftSlot_eval

/-- info: 'DysonFullClass.gLiftSlot_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gLiftSlot_cost

/-- info: 'DysonFullClass.gLiftSlot_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gLiftSlot_count

/-- info: 'DysonFullClass.gTimeGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gTimeGate_unitary

/-- info: 'DysonFullClass.gSlotProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gSlotProgram_eval

/-- info: 'DysonFullClass.gSelectUpTo_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gSelectUpTo_eval

/-- info: 'DysonFullClass.gSlotOperator_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gSlotOperator_compression

/-- info: 'DysonFullClass.gBranchOperator_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gBranchOperator_norm_le

/-- info: 'DysonFullClass.gLogicalSelect_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gLogicalSelect_compression

/-- info: 'DysonFullClass.gSelectUpTo_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gSelectUpTo_count

/-- info: 'DysonFullClass.gSelectUpTo_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gSelectUpTo_cost

/-- info: 'DysonFullClass.gEncoding_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gEncoding_isometry

/-- info: 'DysonFullClass.gSelect_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gSelect_unitary

/-- info: 'DysonFullClass.gSelect_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gSelect_compression

/-- info: 'DysonFullClass.gSelect_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gSelect_count

/-- info: 'DysonFullClass.gSelect_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gSelect_cost

/-! ### The label-dependent attenuation (`Atten`) -/

/-- info: 'DysonFullClass.rotGate_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.rotGate_false

/-- info: 'DysonFullClass.rotGate_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.rotGate_true

/-- info: 'DysonFullClass.rotGate_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.rotGate_mul

/-- info: 'DysonFullClass.rotGate_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.rotGate_adjoint

/-- info: 'DysonFullClass.attGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.attGate_unitary

/-- info: 'DysonFullClass.attTable_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.attTable_mass

/-- info: 'DysonFullClass.atten_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.atten_compression

/-- info: 'DysonFullClass.lift_comp_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.lift_comp_self

/-- info: 'DysonFullClass.decoded_atten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.decoded_atten

/-! ### The node series, the table and the assembled target (`Target`) -/

/-- info: 'DysonFullClass.cellRatio_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.cellRatio_nonneg

/-- info: 'DysonFullClass.cellRatio_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.cellRatio_le_one

/-- info: 'DysonFullClass.length_mul_cellRatio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.length_mul_cellRatio

/-- info: 'DysonFullClass.cfgAtten_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.cfgAtten_nonneg

/-- info: 'DysonFullClass.cfgAtten_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.cfgAtten_le_one

/-- info: 'DysonFullClass.coef_mul_cfgAtten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.coef_mul_cfgAtten

/-- info: 'DysonFullClass.cellMass_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.cellMass_nonneg

/-- info: 'DysonFullClass.cellMass_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.cellMass_le

/-- info: 'DysonFullClass.dysonTable_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.dysonTable_mass

/-- info: 'DysonFullClass.cos_dysonAngle_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.cos_dysonAngle_inl

/-- info: 'DysonFullClass.nodeSeries_eq_lcu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.nodeSeries_eq_lcu

/-- info: 'DysonFullClass.nodeSeries_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.nodeSeries_error

/-- info: 'DysonFullClass.nodeSeries_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.nodeSeries_norm_le

/-- info: 'DysonFullClass.table_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.table_sum_eq

/-- info: 'DysonFullClass.cellGen_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.cellGen_fin

/-- info: 'DysonFullClass.cellGen_eq_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.cellGen_eq_smul

/-- info: 'DysonFullClass.cellGen_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.cellGen_norm_le

/-- info: 'DysonFullClass.sampleSeq_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.sampleSeq_norm_le

/-- info: 'DysonFullClass.cellError_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.cellError_nonneg

/-- info: 'DysonFullClass.dysonTarget_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.dysonTarget_norm_le

/-- info: 'DysonFullClass.herald_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.herald_window

/-! ### The herald window and the certificate (`Herald`) -/

/-- info: 'DysonFullClass.herald_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.herald_geometry

/-- info: 'DysonFullClass.herald_counted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.herald_counted

/-- info: 'DysonFullClass.herald_trial_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.herald_trial_certificate

/-- info: 'DysonFullClass.herald_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.herald_certificate

/-! ### The full-class theorem (`Theorem`) -/

/-- info: 'DysonFullClass.zParam_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.zParam_pos

/-- info: 'DysonFullClass.one_le_fullAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.one_le_fullAmp

/-- info: 'DysonFullClass.fTable_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fTable_mass

/-- info: 'DysonFullClass.fProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fProgram_count

/-- info: 'DysonFullClass.fProgram_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fProgram_compression

/-- info: 'DysonFullClass.gBranchOperator_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.gBranchOperator_false

/-- info: 'DysonFullClass.meshScale_pos_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.meshScale_pos_of_valid

/-! ### One heralded program and the separate source primitives (`Single`) -/

/-- info: 'DysonFullClass.fullOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullOracle_unitary

/-- info: 'DysonFullClass.fullActualOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullActualOracle_unitary

/-- info: 'DysonFullClass.fullPhaseGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullPhaseGate_unitary

/-- info: 'DysonFullClass.fullImplementation_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullImplementation_matrix

/-- info: 'DysonFullClass.fullImplementation_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullImplementation_weight

/-- info: 'DysonFullClass.fullImplementation_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullImplementation_load

/-- info: 'DysonFullClass.fullImplementation_unweight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullImplementation_unweight

/-- info: 'DysonFullClass.fullImplementation_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullImplementation_source

/-! ### Approximate preparations on temporary work registers (`Approx`) -/

/-- info: 'DysonFullClass.fullActualOracleW_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullActualOracleW_unitary

/-- info: 'DysonFullClass.fullActualOracle_pullback_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.fullActualOracle_pullback_matrix

/-- info: 'DysonFullClass.FullValidAt.target_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.FullValidAt.target_ne_zero

/-! ### The fixed-parameter comparison (`Corollaries`) -/

/-- info: 'DysonFullClass.log_cq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.log_cq_le

/-! ### Coverage from the paper clauses (`Coverage`) -/

/-- info: 'DysonFullClass.exp_sub_one_le_of_le_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.exp_sub_one_le_of_le_log

/-- info: 'DysonFullClass.entry_le_of_opNorm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.entry_le_of_opNorm_le

/-- info: 'DysonFullClass.entry_le_of_row_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.entry_le_of_row_norm

/-- info: 'DysonFullClass.opNorm_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.opNorm_add_le

/-- info: 'DysonFullClass.cellError_clip_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.cellError_clip_le

/-- info: 'DysonFullClass.cell_lipschitz_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.cell_lipschitz_le

/-- info: 'DysonFullClass.cellError_le_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.cellError_le_lipschitz

/-! ### Acceptance checks (`Examples`) -/

/-- info: 'DysonFullClass.Examples.zero_accretive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.zero_accretive

/-- info: 'DysonFullClass.Examples.growC_not_accretive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.growC_not_accretive

/-- info: 'DysonFullClass.Examples.norm_growC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.norm_growC

/-- info: 'DysonFullClass.Examples.zero_true_cell' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.zero_true_cell

/-- info: 'DysonFullClass.Examples.exp_smul_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.exp_smul_one

/-- info: 'DysonFullClass.Examples.exp_growC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.exp_growC

/-- info: 'DysonFullClass.Examples.zero_true_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.zero_true_sharp

/-- info: 'DysonFullClass.Examples.const_error_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.const_error_eq

/-- info: 'DysonFullClass.Examples.exMesh_isMesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.exMesh_isMesh

/-- info: 'DysonFullClass.Examples.exMesh_widths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.exMesh_widths

/-- info: 'DysonFullClass.Examples.meshWidth_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.meshWidth_end

/-- info: 'DysonFullClass.Examples.evolution_ones' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.evolution_ones

/-- info: 'DysonFullClass.Examples.truncated_of_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.truncated_of_zero

/-- info: 'DysonFullClass.Examples.nodeSeries_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.nodeSeries_end

/-- info: 'DysonFullClass.Examples.exPhases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.exPhases

/-- info: 'DysonFullClass.Examples.exMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.exMass

/-- info: 'DysonFullClass.Examples.exAssembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.exAssembly

/-- info: 'DysonFullClass.Examples.cfgProduct_cfg11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.cfgProduct_cfg11

/-- info: 'DysonFullClass.Examples.meshNodeProduct_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.meshNodeProduct_two

/-- info: 'DysonFullClass.Examples.eLower_eRaise_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.eLower_eRaise_ne

/-- info: 'DysonFullClass.Examples.meshWidth_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.meshWidth_left

/-- info: 'DysonFullClass.Examples.meshWidth_zero_start' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.meshWidth_zero_start

/-- info: 'DysonFullClass.Examples.left_endpoint_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.left_endpoint_mass

/-- info: 'DysonFullClass.Examples.clipData_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.clipData_decode

/-- info: 'DysonFullClass.Examples.numerator_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonFullClass.Examples.numerator_charge
