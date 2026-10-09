import SparseLowerBounds.Statements

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 19 elementary lemmas, whose reports
list a subset of these three axioms (6 of them depend on no axiom).
The audits cover every theorem of the library (1023) and every field of the
`Prop` structures `HSRange`, `HardInstance` and `LinearSystems.HardRange` (24),
beginning with Theorem `hsl:thm:main`. The library uses no result from another paper.
-/

/-! ### Theorem hsl:thm:main (`Hamiltonian/Theorem`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.main_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.main_max

/-- info: 'SparseLowerBounds.Hamiltonian.main_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.main_exists

/-- info: 'SparseLowerBounds.Hamiltonian.time_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.time_main

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_main

/-- info: 'SparseLowerBounds.Hamiltonian.precision_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precision_main

/-- info: 'SparseLowerBounds.Hamiltonian.time_main_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.time_main_native

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_main_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_main_native

/-- info: 'SparseLowerBounds.Hamiltonian.precision_main_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precision_main_native

/-- info: 'SparseLowerBounds.Hamiltonian.hard_instances' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.hard_instances

/-- info: 'SparseLowerBounds.Hamiltonian.fixedtime_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.fixedtime_sum

/-- info: 'SparseLowerBounds.Hamiltonian.HardInstance.transpose_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardInstance.transpose_eq

/-- info: 'SparseLowerBounds.Hamiltonian.HardInstance.real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardInstance.real

/-- info: 'SparseLowerBounds.Hamiltonian.HardInstance.isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardInstance.isHermitian

/-- info: 'SparseLowerBounds.Hamiltonian.HardInstance.norm_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardInstance.norm_eq_one

/-- info: 'SparseLowerBounds.Hamiltonian.HardInstance.row_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardInstance.row_norm_le

/-- info: 'SparseLowerBounds.Hamiltonian.HardInstance.col_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardInstance.col_norm_le

/-- info: 'SparseLowerBounds.Hamiltonian.HardInstance.row_norm_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardInstance.row_norm_attained

/-- info: 'SparseLowerBounds.Hamiltonian.HardInstance.col_norm_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardInstance.col_norm_attained

/-- info: 'SparseLowerBounds.Hamiltonian.HardInstance.row_sparsity_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardInstance.row_sparsity_le

/-- info: 'SparseLowerBounds.Hamiltonian.HardInstance.col_sparsity_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardInstance.col_sparsity_le

/-- info: 'SparseLowerBounds.Hamiltonian.HardInstance.row_sparsity_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardInstance.row_sparsity_attained

/-- info: 'SparseLowerBounds.Hamiltonian.HardInstance.col_sparsity_attained' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardInstance.col_sparsity_attained

/-- info: 'SparseLowerBounds.Hamiltonian.HardInstance.scale_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardInstance.scale_eq

/-- info: 'SparseLowerBounds.Hamiltonian.HardInstance.decode_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardInstance.decode_eq

/-- info: 'SparseLowerBounds.Hamiltonian.HardInstance.dyadic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardInstance.dyadic

/-- info: 'SparseLowerBounds.Hamiltonian.HardInstance.locators_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardInstance.locators_const

/-- info: 'SparseLowerBounds.Hamiltonian.entry_symm_of_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.entry_symm_of_transpose

/-- info: 'SparseLowerBounds.Hamiltonian.isHermitian_of_realSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.isHermitian_of_realSymmetric

/-- info: 'SparseLowerBounds.Hamiltonian.searchData_hardInstance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchData_hardInstance

/-- info: 'SparseLowerBounds.Hamiltonian.scalarData_hardInstance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarData_hardInstance

/-- info: 'SparseLowerBounds.Hamiltonian.timeN_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.timeN_le

/-! ### Theorem hsl:thm:main without a spectator register (`Hamiltonian/NativeMax`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.main_max_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.main_max_native

/-! ### Corollary hsl:cor:power (`Hamiltonian/Power`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.cor_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.cor_power

/-- info: 'SparseLowerBounds.Hamiltonian.cor_power_not_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.cor_power_not_uniform

/-- info: 'SparseLowerBounds.Hamiltonian.power_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.power_separation

/-- info: 'SparseLowerBounds.Hamiltonian.power_params' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.power_params

/-- info: 'SparseLowerBounds.Hamiltonian.power_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.power_asymptotic

/-! ### Lemma odel:lem:herald (`Hamiltonian/Herald`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.main_max_herald' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.main_max_herald

/-- info: 'SparseLowerBounds.Hamiltonian.time_herald' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.time_herald

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_herald' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_herald

/-- info: 'SparseLowerBounds.Hamiltonian.precision_herald' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precision_herald

/-- info: 'SparseLowerBounds.Hamiltonian.norm_heraldObs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_heraldObs_le

/-- info: 'SparseLowerBounds.Hamiltonian.time_herald_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.time_herald_general

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_herald_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_herald_general

/-- info: 'SparseLowerBounds.Hamiltonian.precision_herald_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precision_herald_general

/-- info: 'SparseLowerBounds.Hamiltonian.time_herald_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.time_herald_native

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_herald_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_herald_native

/-- info: 'SparseLowerBounds.Hamiltonian.precision_herald_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precision_herald_native

/-! ### The released endpoint error (`Hamiltonian/ReleaseForm`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.main_max_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.main_max_endpoint

/-- info: 'SparseLowerBounds.Hamiltonian.accurate_of_endpoint_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.accurate_of_endpoint_program

/-- info: 'SparseLowerBounds.Hamiltonian.time_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.time_endpoint

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_endpoint

/-- info: 'SparseLowerBounds.Hamiltonian.precision_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precision_endpoint

/-- info: 'SparseLowerBounds.Hamiltonian.time_endpoint_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.time_endpoint_native

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_endpoint_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_endpoint_native

/-- info: 'SparseLowerBounds.Hamiltonian.precision_endpoint_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precision_endpoint_native

/-- info: 'SparseLowerBounds.Hamiltonian.hard_data_meet_release_hypotheses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.hard_data_meet_release_hypotheses

/-- info: 'SparseLowerBounds.Hamiltonian.release_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.release_upper

/-! ### The released simulator: the bracket (`Hamiltonian/ReleaseTheta`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.release_theta_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.release_theta_bracket

/-- info: 'SparseLowerBounds.Hamiltonian.release_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.release_theta

/-- info: 'SparseLowerBounds.Hamiltonian.release_theta_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.release_theta_exists

/-- info: 'SparseLowerBounds.Hamiltonian.exists_releaseSimulates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.exists_releaseSimulates

/-- info: 'SparseLowerBounds.Hamiltonian.release_shape_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.release_shape_eq

/-- info: 'SparseLowerBounds.Hamiltonian.release_shape_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.release_shape_le

/-! ### The released simulator: lower bounds over its oracle family (`Hamiltonian/ReleaseBridge`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.main_max_release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.main_max_release

/-- info: 'SparseLowerBounds.Hamiltonian.main_max_release_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.main_max_release_cost

/-- info: 'SparseLowerBounds.Hamiltonian.time_release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.time_release

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_release

/-- info: 'SparseLowerBounds.Hamiltonian.precision_release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precision_release

/-! ### The released simulator: Boolean implementability of its oracles (`Hamiltonian/ReleaseAccess`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.time_release_implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.time_release_implementsOn

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_release_implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_release_implementsOn

/-- info: 'SparseLowerBounds.Hamiltonian.precision_release_implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precision_release_implementsOn

/-- info: 'SparseLowerBounds.Hamiltonian.release_oracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.release_oracle_unitary

/-! ### Boolean oracles in phase form (`Query/PhaseOracle`) -/

/-- info: 'SparseLowerBounds.ProjFamily.proj_mul_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ProjFamily.proj_mul_proj

/-- info: 'SparseLowerBounds.ProjFamily.proj_mul_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ProjFamily.proj_mul_sum

/-- info: 'SparseLowerBounds.ProjFamily.sum_mul_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ProjFamily.sum_mul_proj

/-- info: 'SparseLowerBounds.ProjFamily.isSelfAdjoint_sum_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ProjFamily.isSelfAdjoint_sum_proj

/-- info: 'SparseLowerBounds.ProjFamily.sum_proj_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ProjFamily.sum_proj_mul_self

/-- info: 'SparseLowerBounds.ProjFamily.isStarProjection_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ProjFamily.isStarProjection_sum

/-- info: 'SparseLowerBounds.ProjFamily.one_sub_two_smul_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ProjFamily.one_sub_two_smul_mul_self

/-- info: 'SparseLowerBounds.ProjFamily.isSelfAdjoint_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ProjFamily.isSelfAdjoint_phase

/-- info: 'SparseLowerBounds.ProjFamily.phase_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ProjFamily.phase_mul_self

/-- info: 'SparseLowerBounds.ProjFamily.isUnitary_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ProjFamily.isUnitary_phase

/-- info: 'SparseLowerBounds.ProjFamily.star_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ProjFamily.star_phase

/-- info: 'SparseLowerBounds.ProjFamily.isStarProjection_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ProjFamily.isStarProjection_rest

/-- info: 'SparseLowerBounds.ProjFamily.proj_mul_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ProjFamily.proj_mul_rest

/-- info: 'SparseLowerBounds.ProjFamily.rest_mul_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ProjFamily.rest_mul_proj

/-- info: 'SparseLowerBounds.oneHotOracle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.oneHotOracle_eq

/-- info: 'SparseLowerBounds.isUnitary_oneHotOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.isUnitary_oneHotOracle

/-- info: 'SparseLowerBounds.star_oneHotOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.star_oneHotOracle

/-- info: 'SparseLowerBounds.parity_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.parity_eq_prod

/-- info: 'SparseLowerBounds.abs_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.abs_parity

/-! ### Amplification of matrix norm bounds to Hilbert-space valued vectors (`Helpers/Joint/Amplify`) -/

/-- info: 'SparseLowerBounds.Helpers.Joint.sum_norm_sq_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Joint.sum_norm_sq_mulVec_le

/-- info: 'SparseLowerBounds.Helpers.Joint.sum_swapReg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Joint.sum_swapReg

/-- info: 'SparseLowerBounds.Helpers.Joint.sum_norm_sq_onReg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Joint.sum_norm_sq_onReg_le

/-! ### Tensor products of single-register matrices (`Helpers/Joint/ProdMat`) -/

/-- info: 'SparseLowerBounds.Helpers.Joint.prodMat_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Joint.prodMat_apply

/-- info: 'SparseLowerBounds.Helpers.Joint.prodMat_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Joint.prodMat_mul

/-- info: 'SparseLowerBounds.Helpers.Joint.exists_ne_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Joint.exists_ne_of_ne

/-- info: 'SparseLowerBounds.Helpers.Joint.prodMat_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Joint.prodMat_one

/-- info: 'SparseLowerBounds.Helpers.Joint.prodMat_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Joint.prodMat_conjTranspose

/-- info: 'SparseLowerBounds.Helpers.Joint.prodMat_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Joint.prodMat_diagonal

/-- info: 'SparseLowerBounds.Helpers.Joint.prodMatHom_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Joint.prodMatHom_apply

/-- info: 'SparseLowerBounds.Helpers.Joint.sum_prodMat_update_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Joint.sum_prodMat_update_smul

/-- info: 'SparseLowerBounds.Helpers.Joint.ofFn_prod_eq_of_eq_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Joint.ofFn_prod_eq_of_eq_one

/-- info: 'SparseLowerBounds.Helpers.Joint.ofFn_update_one_prod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Joint.ofFn_update_one_prod

/-! ### The joint hidden-input and workspace space (`Query/Joint`) -/

/-- info: 'SparseLowerBounds.Joint.proj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.proj_apply

/-- info: 'SparseLowerBounds.Joint.mk_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.mk_apply

/-- info: 'SparseLowerBounds.Joint.const_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.const_apply

/-- info: 'SparseLowerBounds.Joint.norm_const_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.norm_const_sq

/-- info: 'SparseLowerBounds.Joint.fiber_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.fiber_apply

/-- info: 'SparseLowerBounds.Joint.fiber_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.fiber_mul

/-- info: 'SparseLowerBounds.Joint.fiber_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.fiber_add

/-- info: 'SparseLowerBounds.Joint.fiber_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.fiber_one

/-- info: 'SparseLowerBounds.Joint.star_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.star_fiber

/-- info: 'SparseLowerBounds.Joint.norm_fiber_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.norm_fiber_le

/-- info: 'SparseLowerBounds.Joint.norm_fiber_apply_of_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.norm_fiber_apply_of_isometry

/-- info: 'SparseLowerBounds.Joint.kernel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.kernel_apply

/-- info: 'SparseLowerBounds.Joint.kernel_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.kernel_mul

/-- info: 'SparseLowerBounds.Joint.kernel_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.kernel_one

/-- info: 'SparseLowerBounds.Joint.star_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.star_kernel

/-- info: 'SparseLowerBounds.Joint.norm_kernel_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.norm_kernel_le

/-- info: 'SparseLowerBounds.Joint.kernel_comm_fiber_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.kernel_comm_fiber_const

/-- info: 'SparseLowerBounds.Joint.kernel_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.kernel_diagonal

/-- info: 'SparseLowerBounds.Joint.onReg_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.onReg_apply

/-- info: 'SparseLowerBounds.Joint.onReg_eq_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.onReg_eq_kernel

/-- info: 'SparseLowerBounds.Joint.update_one_mul_update_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.update_one_mul_update_one

/-- info: 'SparseLowerBounds.Joint.onReg_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.onReg_mul

/-- info: 'SparseLowerBounds.Joint.onReg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.onReg_one

/-- info: 'SparseLowerBounds.Joint.star_onReg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.star_onReg

/-- info: 'SparseLowerBounds.Joint.norm_onReg_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.norm_onReg_le

/-- info: 'SparseLowerBounds.Joint.onReg_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.onReg_comm

/-- info: 'SparseLowerBounds.Joint.onReg_comm_fiber_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.onReg_comm_fiber_const

/-- info: 'SparseLowerBounds.Joint.onReg_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.onReg_diagonal

/-- info: 'SparseLowerBounds.Joint.tensorPow_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.tensorPow_apply

/-- info: 'SparseLowerBounds.Joint.tensorPow_eq_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.tensorPow_eq_kernel

/-- info: 'SparseLowerBounds.Joint.tensorPow_eq_prod_onReg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.tensorPow_eq_prod_onReg

/-- info: 'SparseLowerBounds.Joint.tensorPow_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.tensorPow_mul

/-- info: 'SparseLowerBounds.Joint.tensorPow_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.tensorPow_one

/-- info: 'SparseLowerBounds.Joint.star_tensorPow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.star_tensorPow

/-- info: 'SparseLowerBounds.Joint.norm_tensorPow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.norm_tensorPow_le

/-- info: 'SparseLowerBounds.Joint.tensorPow_comm_fiber_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.tensorPow_comm_fiber_const

/-- info: 'SparseLowerBounds.Joint.tensorPow_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.tensorPow_diagonal

/-- info: 'SparseLowerBounds.Joint.tensorPow_mul_onReg_mul_tensorPow_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.tensorPow_mul_onReg_mul_tensorPow_inv

/-- info: 'SparseLowerBounds.Joint.tensorPow_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Joint.tensorPow_const

/-! ### Pythagoras for a resolution of the identity by star projections (`Helpers/Adversary/ProjNorm`) -/

/-- info: 'SparseLowerBounds.Helpers.Adversary.re_inner_apply_self_of_isStarProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Adversary.re_inner_apply_self_of_isStarProjection

/-- info: 'SparseLowerBounds.Helpers.Adversary.norm_sq_eq_add_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Adversary.norm_sq_eq_add_sum

/-- info: 'SparseLowerBounds.Helpers.Adversary.norm_sq_add_sum_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Adversary.norm_sq_add_sum_apply

/-! ### The generic multiplicative adversary (`Query/Adversary`) -/

/-- info: 'SparseLowerBounds.Adversary.joint_sum_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adversary.joint_sum_apply

/-- info: 'SparseLowerBounds.Adversary.tensorPow_inv_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adversary.tensorPow_inv_mul

/-- info: 'SparseLowerBounds.Adversary.tensorPow_mul_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adversary.tensorPow_mul_inv

/-- info: 'SparseLowerBounds.Adversary.tensorPow_Z_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adversary.tensorPow_Z_apply

/-- info: 'SparseLowerBounds.Adversary.fiber_oneHotOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adversary.fiber_oneHotOracle

/-- info: 'SparseLowerBounds.Adversary.norm_block_apply_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adversary.norm_block_apply_le

/-- info: 'SparseLowerBounds.Adversary.conj_fiber_oneHotOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adversary.conj_fiber_oneHotOracle

/-- info: 'SparseLowerBounds.Adversary.norm_tensorPow_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adversary.norm_tensorPow_query

/-- info: 'SparseLowerBounds.Adversary.norm_tensorPow_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adversary.norm_tensorPow_fixed

/-- info: 'SparseLowerBounds.Adversary.norm_tensorPow_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adversary.norm_tensorPow_program

/-- info: 'SparseLowerBounds.Adversary.correlation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adversary.correlation_le

/-- info: 'SparseLowerBounds.Adversary.norm_tensorPow_const_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adversary.norm_tensorPow_const_sq

/-- info: 'SparseLowerBounds.Adversary.program_correlation_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adversary.program_correlation_le

/-! ### Matrix facts for `SparseLowerBounds.Query.XorWeight` (`Helpers/XorWeight/Matrix`) -/

/-- info: 'SparseLowerBounds.Helpers.XorWeight.two_sub_mul_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.two_sub_mul_inv

/-- info: 'SparseLowerBounds.Helpers.XorWeight.inv_mul_two_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.inv_mul_two_sub

/-- info: 'SparseLowerBounds.Helpers.XorWeight.conj_sq_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.conj_sq_eq

/-- info: 'SparseLowerBounds.Helpers.XorWeight.idem_eq' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.idem_eq

/-- info: 'SparseLowerBounds.Helpers.XorWeight.P_mul_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.P_mul_P

/-- info: 'SparseLowerBounds.Helpers.XorWeight.star_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.star_P

/-- info: 'SparseLowerBounds.Helpers.XorWeight.isStarProjection_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.isStarProjection_P

/-- info: 'SparseLowerBounds.Helpers.XorWeight.norm_P_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.norm_P_le

/-- info: 'SparseLowerBounds.Helpers.XorWeight.norm_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.norm_one_le

/-- info: 'SparseLowerBounds.Helpers.XorWeight.P_mulVec_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.P_mulVec_one

/-- info: 'SparseLowerBounds.Helpers.XorWeight.norm_wInv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.norm_wInv_le

/-- info: 'SparseLowerBounds.Helpers.XorWeight.norm_D_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.norm_D_le

/-- info: 'SparseLowerBounds.Helpers.XorWeight.norm_Z_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.norm_Z_le

/-- info: 'SparseLowerBounds.Helpers.XorWeight.norm_le_of_sum_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.norm_le_of_sum_sq

/-- info: 'SparseLowerBounds.Helpers.XorWeight.norm_commutator_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.norm_commutator_le

/-- info: 'SparseLowerBounds.Helpers.XorWeight.Z_mul_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.Z_mul_Z

/-- info: 'SparseLowerBounds.Helpers.XorWeight.star_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.star_Z

/-- info: 'SparseLowerBounds.Helpers.XorWeight.sum_neg_one_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.sum_neg_one_pow

/-- info: 'SparseLowerBounds.Helpers.XorWeight.P_Z_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.P_Z_P

/-- info: 'SparseLowerBounds.Helpers.XorWeight.norm_conj_Z_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.XorWeight.norm_conj_Z_le

/-! ### The XOR weight and Lemma `qlsl:lem:xor` (`Query/XorWeight`) -/

/-- info: 'SparseLowerBounds.XorWeight.isHermitian_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.XorWeight.isHermitian_w

/-- info: 'SparseLowerBounds.XorWeight.w_mul_wInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.XorWeight.w_mul_wInv

/-- info: 'SparseLowerBounds.XorWeight.wInv_mul_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.XorWeight.wInv_mul_w

/-- info: 'SparseLowerBounds.XorWeight.isUnit_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.XorWeight.isUnit_w

/-- info: 'SparseLowerBounds.XorWeight.inv_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.XorWeight.inv_w

/-- info: 'SparseLowerBounds.XorWeight.w_mulVec_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.XorWeight.w_mulVec_one

/-- info: 'SparseLowerBounds.XorWeight.norm_commutator_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.XorWeight.norm_commutator_le

/-- info: 'SparseLowerBounds.XorWeight.norm_wInv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.XorWeight.norm_wInv_le

/-- info: 'SparseLowerBounds.XorWeight.norm_conj_D_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.XorWeight.norm_conj_D_le

/-- info: 'SparseLowerBounds.XorWeight.norm_conj_Z_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.XorWeight.norm_conj_Z_le

/-- info: 'SparseLowerBounds.XorWeight.lam_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.XorWeight.lam_pow_le

/-- info: 'SparseLowerBounds.XorWeight.final_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.XorWeight.final_of_bound

/-- info: 'SparseLowerBounds.XorWeight.mixture_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.XorWeight.mixture_bound

/-- info: 'SparseLowerBounds.XorWeight.xor_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.XorWeight.xor_lemma

/-- info: 'SparseLowerBounds.XorWeight.xor_lemma_mixture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.XorWeight.xor_lemma_mixture

/-! ### Projector algebra for `SparseLowerBounds.Query.SearchWeight` (`Helpers/SearchWeight/Proj`) -/

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.orth_combo_mul3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.orth_combo_mul3

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.Z_P_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.Z_P_Z

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.Z_V_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.Z_V_Z

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.Z_mul_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.Z_mul_P

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.Z_mul_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.Z_mul_V

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.V_mul_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.V_mul_V

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.P_mul_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.P_mul_V

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.V_mul_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.V_mul_P

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.star_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.star_V

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.P_add_V_add_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.P_add_V_add_R

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.P_mul_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.P_mul_R

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.R_mul_P' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.R_mul_P

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.V_mul_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.V_mul_R

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.R_mul_V' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.R_mul_V

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.R_mul_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.R_mul_R

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.star_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.star_R

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.V_mulVec_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.V_mulVec_one

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.R_mulVec_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.R_mulVec_one

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.Z_mul_R' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.Z_mul_R

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.combo_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.combo_mul

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.W_mul_WInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.W_mul_WInv

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.WInv_mul_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.WInv_mul_W

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.inv_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.inv_W

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.star_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.star_ofReal

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.star_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.star_W

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.star_WInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.star_WInv

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.W_mulVec_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.W_mulVec_one

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.WInv_Z_WInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.WInv_Z_WInv

/-! ### Ancilla, spectator and native-label bookkeeping (`Query/Ancilla`) -/

/-- info: 'SparseLowerBounds.minusProj_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.minusProj_mul_self

/-- info: 'SparseLowerBounds.minusProj_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.minusProj_conjTranspose

/-- info: 'SparseLowerBounds.isStarProjection_kernel_minusProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.isStarProjection_kernel_minusProj

/-- info: 'SparseLowerBounds.fiber_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.fiber_zero

/-- info: 'SparseLowerBounds.isStarProjection_fiber_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.isStarProjection_fiber_const

/-- info: 'SparseLowerBounds.ancillaEmbed_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ancillaEmbed_apply

/-- info: 'SparseLowerBounds.ancillaEmbed_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.ancillaEmbed_isometry

/-- info: 'SparseLowerBounds.specOracles_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.specOracles_unitary

/-- info: 'SparseLowerBounds.cost_hardCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.cost_hardCost

/-- info: 'SparseLowerBounds.labelCount_le_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.labelCount_le_count

/-! ### Output readout and accuracy in observable form (`Query/Readout`) -/

/-- info: 'SparseLowerBounds.Readout.liftObs_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Readout.liftObs_apply

/-- info: 'SparseLowerBounds.Readout.norm_liftObs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Readout.norm_liftObs_le

/-- info: 'SparseLowerBounds.Readout.isSelfAdjoint_liftObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Readout.isSelfAdjoint_liftObs

/-- info: 'SparseLowerBounds.Readout.norm_outObs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Readout.norm_outObs_le

/-- info: 'SparseLowerBounds.Readout.inner_liftObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Readout.inner_liftObs

/-- info: 'SparseLowerBounds.Readout.inner_outObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Readout.inner_outObs

/-- info: 'SparseLowerBounds.Readout.heralded_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Readout.heralded_correlation

/-! ### Vector facts for `SparseLowerBounds.Query.SearchWeight` (`Helpers/SearchWeight/Vectors`) -/

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.norm_toLp_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.norm_toLp_star

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.norm_toLp_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.norm_toLp_single

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.norm_toLp_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.norm_toLp_sq

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.norm_vecMulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.norm_vecMulVec_le

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.sum_neg_one_pow_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.sum_neg_one_pow_real

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.norm_alt_combo_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.norm_alt_combo_sq

/-! ### The one-bit gadget `U_j` (`LinearSystems/Gadget`) -/

/-- info: 'SparseLowerBounds.LinearSystems.gadgetPos_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.gadgetPos_spec

/-- info: 'SparseLowerBounds.LinearSystems.gadgetPos_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.gadgetPos_eq_iff

/-- info: 'SparseLowerBounds.LinearSystems.gadgetPos_inj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.gadgetPos_inj

/-- info: 'SparseLowerBounds.LinearSystems.gadgetPos_mod_two' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.gadgetPos_mod_two

/-- info: 'SparseLowerBounds.LinearSystems.sum_parity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.sum_parity

/-- info: 'SparseLowerBounds.LinearSystems.sum_sub_ite_mul_sub_ite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.sum_sub_ite_mul_sub_ite

/-- info: 'SparseLowerBounds.LinearSystems.star_gadget_apply_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.star_gadget_apply_aux

/-- info: 'SparseLowerBounds.LinearSystems.gadget_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.gadget_mem_unitaryGroup

/-- info: 'SparseLowerBounds.LinearSystems.star_gadget_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.star_gadget_apply

/-- info: 'SparseLowerBounds.LinearSystems.norm_logical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.norm_logical

/-- info: 'SparseLowerBounds.LinearSystems.gadget_mulVec_logical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.gadget_mulVec_logical

/-- info: 'SparseLowerBounds.LinearSystems.gadget_apply_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.gadget_apply_ne_zero

/-! ### Reduction of labelled-oracle algorithms to Boolean programs (`Query/Reduction`) -/

/-- info: 'SparseLowerBounds.Reduction.exists_boolean_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Reduction.exists_boolean_program

/-- info: 'SparseLowerBounds.Reduction.norm_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Reduction.norm_encode

/-- info: 'SparseLowerBounds.Reduction.norm_encodeObs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Reduction.norm_encodeObs_le

/-- info: 'SparseLowerBounds.Reduction.inner_encodeObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Reduction.inner_encodeObs

/-- info: 'SparseLowerBounds.Reduction.exists_boolean_program_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Reduction.exists_boolean_program_inner

/-! ### The conjugated query block for `SparseLowerBounds.Query.SearchWeight` (`Helpers/SearchWeight/Query`) -/

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.E_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.E_eq

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.F_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.F_eq

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.combo_mulVec_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.combo_mulVec_single

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.norm_combo_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.norm_combo_sq

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.norm_combo_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.norm_combo_le

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.norm_inv_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.norm_inv_sub_one_le

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.norm_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.norm_sub_one_le

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.norm_E_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.norm_E_le

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.norm_F_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.norm_F_le

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.D_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.D_eq

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.star_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.star_single

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.conj_D_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.conj_D_eq

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.norm_conj_D_le_fine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.norm_conj_D_le_fine

/-! ### Real arithmetic for `SparseLowerBounds.Query.SearchWeight` (`Helpers/SearchWeight/Arith`) -/

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.fine_le_twelve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.fine_le_twelve

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.lam_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.lam_pow_le

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.searchA_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.searchA_sq

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.one_le_searchA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.one_le_searchA

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.searchA_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.searchA_le_sqrt

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.searchA_sq_inv_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.searchA_sq_inv_pow

/-- info: 'SparseLowerBounds.Helpers.SearchWeight.search_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SearchWeight.search_final

/-! ### Parameters of the linear-system lower bound (`LinearSystems/Parameters`) -/

/-- info: 'SparseLowerBounds.LinearSystems.HardRange.kappa_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.HardRange.kappa_ge

/-- info: 'SparseLowerBounds.LinearSystems.HardRange.s_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.HardRange.s_ge

/-- info: 'SparseLowerBounds.LinearSystems.HardRange.eps_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.HardRange.eps_pos

/-- info: 'SparseLowerBounds.LinearSystems.HardRange.eps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.HardRange.eps_le

/-- info: 'SparseLowerBounds.LinearSystems.two_thirds_lt_log_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.two_thirds_lt_log_two

/-- info: 'SparseLowerBounds.LinearSystems.sixteen_le_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.sixteen_le_floor

/-- info: 'SparseLowerBounds.LinearSystems.four_le_hardRho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.four_le_hardRho

/-- info: 'SparseLowerBounds.LinearSystems.six_log_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.six_log_two_le

/-- info: 'SparseLowerBounds.LinearSystems.log_sixteen_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.log_sixteen_eq

/-- info: 'SparseLowerBounds.LinearSystems.four_le_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.four_le_log

/-- info: 'SparseLowerBounds.LinearSystems.log_sixteen_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.log_sixteen_nonneg

/-- info: 'SparseLowerBounds.LinearSystems.log_sixteen_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.log_sixteen_le

/-- info: 'SparseLowerBounds.LinearSystems.sixteen_le_hardR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.sixteen_le_hardR

/-- info: 'SparseLowerBounds.LinearSystems.sixteen_le_hardR_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.sixteen_le_hardR_real

/-- info: 'SparseLowerBounds.LinearSystems.kappa_div_four_lt_hardR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.kappa_div_four_lt_hardR

/-- info: 'SparseLowerBounds.LinearSystems.hardR_le_kappa_div_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.hardR_le_kappa_div_two

/-- info: 'SparseLowerBounds.LinearSystems.two_hardR_le_kappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.two_hardR_le_kappa

/-- info: 'SparseLowerBounds.LinearSystems.two_le_hardMu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.two_le_hardMu

/-- info: 'SparseLowerBounds.LinearSystems.four_le_hardM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.four_le_hardM

/-- info: 'SparseLowerBounds.LinearSystems.even_hardM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.even_hardM

/-- info: 'SparseLowerBounds.LinearSystems.hardM_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.hardM_le

/-- info: 'SparseLowerBounds.LinearSystems.s_le_two_hardM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.s_le_two_hardM

/-- info: 'SparseLowerBounds.LinearSystems.s_div_four_lt_hardM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.s_div_four_lt_hardM

/-- info: 'SparseLowerBounds.LinearSystems.hardM_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.hardM_succ_le

/-- info: 'SparseLowerBounds.LinearSystems.log_div_three_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.log_div_three_le

/-- info: 'SparseLowerBounds.LinearSystems.hardN_le_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.hardN_le_real

/-- info: 'SparseLowerBounds.LinearSystems.lt_hardN_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.lt_hardN_add_one

/-- info: 'SparseLowerBounds.LinearSystems.nrange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.nrange

/-- info: 'SparseLowerBounds.LinearSystems.two_log_le_hardN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.two_log_le_hardN

/-- info: 'SparseLowerBounds.LinearSystems.hardR_le_two_hardN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.hardR_le_two_hardN

/-- info: 'SparseLowerBounds.LinearSystems.hardN_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.hardN_pos

/-- info: 'SparseLowerBounds.LinearSystems.s_le_dim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.s_le_dim

/-- info: 'SparseLowerBounds.LinearSystems.dim_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.dim_bounds

/-- info: 'SparseLowerBounds.LinearSystems.one_le_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.one_le_two_pow

/-- info: 'SparseLowerBounds.LinearSystems.clockRatio_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.clockRatio_nonneg

/-- info: 'SparseLowerBounds.LinearSystems.clockRatio_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.clockRatio_lt_one

/-- info: 'SparseLowerBounds.LinearSystems.neg_inv_le_log_clockRatio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.neg_inv_le_log_clockRatio

/-- info: 'SparseLowerBounds.LinearSystems.sixteen_eps_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.sixteen_eps_le_pow

/-- info: 'SparseLowerBounds.LinearSystems.answerProb_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.answerProb_ge

/-- info: 'SparseLowerBounds.LinearSystems.two_eps_le_answerProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.two_eps_le_answerProb

/-- info: 'SparseLowerBounds.LinearSystems.eps_le_bias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.eps_le_bias

/-- info: 'SparseLowerBounds.LinearSystems.final_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.final_bound

/-! ### The search weight and Lemma `hsl:lem:search` (`Query/SearchWeight`) -/

/-- info: 'SparseLowerBounds.SearchWeight.orth_combo_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.orth_combo_mul

/-- info: 'SparseLowerBounds.SearchWeight.isHermitian_Pv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.isHermitian_Pv

/-- info: 'SparseLowerBounds.SearchWeight.Pv_mul_Pv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.Pv_mul_Pv

/-- info: 'SparseLowerBounds.SearchWeight.Pu_mul_Pv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.Pu_mul_Pv

/-- info: 'SparseLowerBounds.SearchWeight.Pv_mul_Pu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.Pv_mul_Pu

/-- info: 'SparseLowerBounds.SearchWeight.Pu_mul_Rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.Pu_mul_Rest

/-- info: 'SparseLowerBounds.SearchWeight.Rest_mul_Pu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.Rest_mul_Pu

/-- info: 'SparseLowerBounds.SearchWeight.Pv_mul_Rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.Pv_mul_Rest

/-- info: 'SparseLowerBounds.SearchWeight.Rest_mul_Pv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.Rest_mul_Pv

/-- info: 'SparseLowerBounds.SearchWeight.Rest_mul_Rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.Rest_mul_Rest

/-- info: 'SparseLowerBounds.SearchWeight.isHermitian_Rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.isHermitian_Rest

/-- info: 'SparseLowerBounds.SearchWeight.Pv_mulVec_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.Pv_mulVec_one

/-- info: 'SparseLowerBounds.SearchWeight.Rest_mulVec_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.Rest_mulVec_one

/-- info: 'SparseLowerBounds.SearchWeight.parityZ_mul_parityZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.parityZ_mul_parityZ

/-- info: 'SparseLowerBounds.SearchWeight.parityZ_mul_Pu_mul_parityZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.parityZ_mul_Pu_mul_parityZ

/-- info: 'SparseLowerBounds.SearchWeight.parityZ_mul_Pv_mul_parityZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.parityZ_mul_Pv_mul_parityZ

/-- info: 'SparseLowerBounds.SearchWeight.parityZ_mul_Pu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.parityZ_mul_Pu

/-- info: 'SparseLowerBounds.SearchWeight.parityZ_mul_Pv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.parityZ_mul_Pv

/-- info: 'SparseLowerBounds.SearchWeight.parityZ_mul_Rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.parityZ_mul_Rest

/-- info: 'SparseLowerBounds.SearchWeight.isHermitian_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.isHermitian_w

/-- info: 'SparseLowerBounds.SearchWeight.w_mul_wInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.w_mul_wInv

/-- info: 'SparseLowerBounds.SearchWeight.wInv_mul_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.wInv_mul_w

/-- info: 'SparseLowerBounds.SearchWeight.isHermitian_wInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.isHermitian_wInv

/-- info: 'SparseLowerBounds.SearchWeight.isUnit_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.isUnit_w

/-- info: 'SparseLowerBounds.SearchWeight.inv_w' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.inv_w

/-- info: 'SparseLowerBounds.SearchWeight.w_mulVec_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.w_mulVec_one

/-- info: 'SparseLowerBounds.SearchWeight.conj_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.conj_Z

/-- info: 'SparseLowerBounds.SearchWeight.norm_conj_Z_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.norm_conj_Z_le

/-- info: 'SparseLowerBounds.SearchWeight.eVec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.eVec_eq

/-- info: 'SparseLowerBounds.SearchWeight.fVec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.fVec_eq

/-- info: 'SparseLowerBounds.SearchWeight.norm_combo_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.norm_combo_sq

/-- info: 'SparseLowerBounds.SearchWeight.norm_e_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.norm_e_le

/-- info: 'SparseLowerBounds.SearchWeight.norm_f_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.norm_f_le

/-- info: 'SparseLowerBounds.SearchWeight.norm_toLp_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.norm_toLp_star

/-- info: 'SparseLowerBounds.SearchWeight.norm_vecMulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.norm_vecMulVec_le

/-- info: 'SparseLowerBounds.SearchWeight.conj_D_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.conj_D_eq

/-- info: 'SparseLowerBounds.SearchWeight.norm_conj_D_le_fine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.norm_conj_D_le_fine

/-- info: 'SparseLowerBounds.SearchWeight.fine_le_twelve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.fine_le_twelve

/-- info: 'SparseLowerBounds.SearchWeight.norm_conj_D_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.norm_conj_D_le

/-- info: 'SparseLowerBounds.SearchWeight.lam_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.lam_pow_le

/-- info: 'SparseLowerBounds.SearchWeight.pos_of_hmβ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.pos_of_hmβ

/-- info: 'SparseLowerBounds.SearchWeight.searchA_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.searchA_sq

/-- info: 'SparseLowerBounds.SearchWeight.one_le_searchA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.one_le_searchA

/-- info: 'SparseLowerBounds.SearchWeight.searchA_le_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.searchA_le_sqrt

/-- info: 'SparseLowerBounds.SearchWeight.searchA_sq_inv_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.searchA_sq_inv_pow

/-- info: 'SparseLowerBounds.SearchWeight.search_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.search_final

/-- info: 'SparseLowerBounds.SearchWeight.le_avg_of_forall_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.le_avg_of_forall_le

/-- info: 'SparseLowerBounds.SearchWeight.avg_re_le_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.avg_re_le_norm

/-- info: 'SparseLowerBounds.SearchWeight.avg_corr_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.avg_corr_le_one

/-- info: 'SparseLowerBounds.SearchWeight.avg_corr_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.avg_corr_le

/-- info: 'SparseLowerBounds.SearchWeight.search_lemma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.search_lemma

/-- info: 'SparseLowerBounds.SearchWeight.search_lemma_worst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.SearchWeight.search_lemma_worst

/-! ### Helper: the query–gate–unquery circuit on the clean-ancilla encoding (`Helpers/CompileReduction/AncillaCircuit`) -/

/-- info: 'SparseLowerBounds.Helpers.CompileReduction.joint_sum_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.CompileReduction.joint_sum_apply

/-- info: 'SparseLowerBounds.Helpers.CompileReduction.hitProj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.CompileReduction.hitProj_apply

/-- info: 'SparseLowerBounds.Helpers.CompileReduction.oneHotOracle_eq_hitProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.CompileReduction.oneHotOracle_eq_hitProj

/-- info: 'SparseLowerBounds.Helpers.CompileReduction.withAncilla_proj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.CompileReduction.withAncilla_proj_apply

/-- info: 'SparseLowerBounds.Helpers.CompileReduction.hitProj_withAncilla_apply_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.CompileReduction.hitProj_withAncilla_apply_zero

/-- info: 'SparseLowerBounds.Helpers.CompileReduction.hitProj_withAncilla_apply_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.CompileReduction.hitProj_withAncilla_apply_one

/-- info: 'SparseLowerBounds.Helpers.CompileReduction.oneHot_withAncilla_apply_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.CompileReduction.oneHot_withAncilla_apply_zero

/-- info: 'SparseLowerBounds.Helpers.CompileReduction.oneHot_withAncilla_apply_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.CompileReduction.oneHot_withAncilla_apply_one

/-- info: 'SparseLowerBounds.Helpers.CompileReduction.hitProj_spectate_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.CompileReduction.hitProj_spectate_apply

/-- info: 'SparseLowerBounds.Helpers.CompileReduction.ancillaEmbed_apply_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.CompileReduction.ancillaEmbed_apply_zero

/-- info: 'SparseLowerBounds.Helpers.CompileReduction.ancillaEmbed_apply_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.CompileReduction.ancillaEmbed_apply_one

/-- info: 'SparseLowerBounds.Helpers.CompileReduction.isUnitary_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.CompileReduction.isUnitary_fiber

/-- info: 'SparseLowerBounds.Helpers.CompileReduction.circuit_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.CompileReduction.circuit_intertwines

/-- info: 'SparseLowerBounds.Helpers.CompileReduction.implementsOn_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.CompileReduction.implementsOn_const

/-! ### Fourier degree of Boolean bit-oracle programs (`Query/BitDegree`) -/

/-- info: 'SparseLowerBounds.BitDegree.bitParity_eq_chi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.bitParity_eq_chi

/-- info: 'SparseLowerBounds.BitDegree.abs_bitParity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.abs_bitParity

/-- info: 'SparseLowerBounds.BitDegree.chi_eq_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.chi_eq_prod

/-- info: 'SparseLowerBounds.BitDegree.chi_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.chi_empty

/-- info: 'SparseLowerBounds.BitDegree.chi_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.chi_single

/-- info: 'SparseLowerBounds.BitDegree.star_chi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.star_chi

/-- info: 'SparseLowerBounds.BitDegree.chi_mul_chi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.chi_mul_chi

/-- info: 'SparseLowerBounds.BitDegree.chi_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.chi_mul_self

/-- info: 'SparseLowerBounds.BitDegree.card_symmDiff_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.card_symmDiff_le

/-- info: 'SparseLowerBounds.BitDegree.sum_chi_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.sum_chi_eq_zero

/-- info: 'SparseLowerBounds.BitDegree.sum_chi_mul_chi_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.sum_chi_mul_chi_eq_zero

/-- info: 'SparseLowerBounds.BitDegree.sum_bitParity_mul_chi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.sum_bitParity_mul_chi

/-- info: 'SparseLowerBounds.BitDegree.chi_smul_mem_degLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.chi_smul_mem_degLE

/-- info: 'SparseLowerBounds.BitDegree.const_mem_degLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.const_mem_degLE

/-- info: 'SparseLowerBounds.BitDegree.degLE_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.degLE_mono

/-- info: 'SparseLowerBounds.BitDegree.map_degLE_of_generators' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.map_degLE_of_generators

/-- info: 'SparseLowerBounds.BitDegree.mul_chi_mem_degLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.mul_chi_mem_degLE

/-- info: 'SparseLowerBounds.BitDegree.mul_chi_single_mem_degLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.mul_chi_single_mem_degLE

/-- info: 'SparseLowerBounds.BitDegree.map_mem_degLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.map_mem_degLE

/-- info: 'SparseLowerBounds.BitDegree.clm_apply_mem_degLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.clm_apply_mem_degLE

/-- info: 'SparseLowerBounds.BitDegree.bitOracle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.bitOracle_eq

/-- info: 'SparseLowerBounds.BitDegree.star_bitOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.star_bitOracle

/-- info: 'SparseLowerBounds.BitDegree.query_mem_degLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.query_mem_degLE

/-- info: 'SparseLowerBounds.BitDegree.eval_apply_mem_degLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.eval_apply_mem_degLE

/-- info: 'SparseLowerBounds.BitDegree.program_mem_degLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.program_mem_degLE

/-- info: 'SparseLowerBounds.BitDegree.inner_chi_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.inner_chi_smul

/-- info: 'SparseLowerBounds.BitDegree.inner_chi_smul_mem_degLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.inner_chi_smul_mem_degLE

/-- info: 'SparseLowerBounds.BitDegree.inner_mem_degLE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.inner_mem_degLE

/-- info: 'SparseLowerBounds.BitDegree.sum_bitParity_mul_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.sum_bitParity_mul_eq_zero

/-- info: 'SparseLowerBounds.BitDegree.program_correlation_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.program_correlation_eq_zero

/-- info: 'SparseLowerBounds.BitDegree.le_two_mul_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.le_two_mul_count

/-- info: 'SparseLowerBounds.BitDegree.le_two_mul_count_avg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.BitDegree.le_two_mul_count_avg

/-! ### Helper: lifting a uniform program to an untouched spectator register (`Helpers/Adaptive/Access/LiftProgram`) -/

/-- info: 'SparseLowerBounds.Helpers.Adaptive.Access.eval_liftProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Adaptive.Access.eval_liftProgram

/-- info: 'SparseLowerBounds.Helpers.Adaptive.Access.count_liftProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Adaptive.Access.count_liftProgram

/-! ### Generic facts about the `L²` operator norm of square matrices (`Helpers/OpenClock/MatrixNorm`) -/

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.norm_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.norm_one_le

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.norm_toLp_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.norm_toLp_mulVec_le

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.norm_toLp_mulVec_le_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.norm_toLp_mulVec_le_self

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.norm_le_of_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.norm_le_of_mulVec

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.norm_pow_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.norm_pow_le_one

/-! ### Boolean access certificates and their transport (`Adaptive/Access`) -/

/-- info: 'SparseLowerBounds.Adaptive.Access.jointMap_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adaptive.Access.jointMap_apply

/-- info: 'SparseLowerBounds.Adaptive.Access.jointMap_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adaptive.Access.jointMap_adjoint

/-- info: 'SparseLowerBounds.Adaptive.Access.jointMap_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adaptive.Access.jointMap_isometry

/-- info: 'SparseLowerBounds.Adaptive.Access.fiber_comp_jointMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adaptive.Access.fiber_comp_jointMap

/-- info: 'SparseLowerBounds.Adaptive.Access.jointMap_comp_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adaptive.Access.jointMap_comp_fiber

/-- info: 'SparseLowerBounds.Adaptive.Access.oneHotOracle_spectate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adaptive.Access.oneHotOracle_spectate

/-- info: 'SparseLowerBounds.Adaptive.Access.implementsOn_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adaptive.Access.implementsOn_conj

/-- info: 'SparseLowerBounds.Adaptive.Access.implementsOn_spectate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adaptive.Access.implementsOn_spectate

/-- info: 'SparseLowerBounds.Adaptive.Access.implementsOn_spectate_oneHot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Adaptive.Access.implementsOn_spectate_oneHot

/-! ### The open computation clock and its Hermitian dilation (`LinearSystems/OpenClock`) -/

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.clockShift_pow_apply_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.clockShift_pow_apply_eq_zero

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.clockShift_mulVec_atClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.clockShift_mulVec_atClock

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.norm_sq_eq_sum_blk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.norm_sq_eq_sum_blk

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.blk_clockShift_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.blk_clockShift_zero

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.blk_clockShift_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.blk_clockShift_succ

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.norm_toLp_clockShift_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.norm_toLp_clockShift_mulVec_le

/-- info: 'SparseLowerBounds.LinearSystems.clockShift_pow_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.clockShift_pow_self

/-- info: 'SparseLowerBounds.LinearSystems.clockShift_pow_mulVec_atClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.clockShift_pow_mulVec_atClock

/-- info: 'SparseLowerBounds.LinearSystems.norm_clockShift_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.norm_clockShift_le

/-- info: 'SparseLowerBounds.LinearSystems.norm_clockMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.norm_clockMatrix_le

/-- info: 'SparseLowerBounds.LinearSystems.le_norm_one_sub_smul_clockShift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.le_norm_one_sub_smul_clockShift

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.one_sub_mul_neumann' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.one_sub_mul_neumann

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.clockMatrix_mul_neumann' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.clockMatrix_mul_neumann

/-- info: 'SparseLowerBounds.LinearSystems.inv_clockMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.inv_clockMatrix

/-- info: 'SparseLowerBounds.LinearSystems.isUnit_clockMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.isUnit_clockMatrix

/-- info: 'SparseLowerBounds.LinearSystems.norm_inv_clockMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.norm_inv_clockMatrix_le

/-- info: 'SparseLowerBounds.LinearSystems.history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.history

/-- info: 'SparseLowerBounds.LinearSystems.norm_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.norm_walk

/-- info: 'SparseLowerBounds.LinearSystems.answer_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.answer_weight

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.sectorVec_eta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.sectorVec_eta

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.dilation_mulVec_sectorVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.dilation_mulVec_sectorVec

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.norm_sq_sectorVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.norm_sq_sectorVec

/-- info: 'SparseLowerBounds.LinearSystems.OpenClock.dilation_mul_dilation_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.OpenClock.dilation_mul_dilation_inv

/-- info: 'SparseLowerBounds.LinearSystems.isHermitian_dilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.isHermitian_dilation

/-- info: 'SparseLowerBounds.LinearSystems.norm_dilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.norm_dilation

/-- info: 'SparseLowerBounds.LinearSystems.isUnit_dilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.isUnit_dilation

/-- info: 'SparseLowerBounds.LinearSystems.inv_dilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.inv_dilation

/-- info: 'SparseLowerBounds.LinearSystems.norm_inv_dilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.norm_inv_dilation

/-- info: 'SparseLowerBounds.LinearSystems.inv_dilation_mulVec_sectorVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.inv_dilation_mulVec_sectorVec

/-! ### The query–gate–unquery circuit for arbitrary Boolean strings (`Query/PhaseCircuit`) -/

/-- info: 'SparseLowerBounds.PhaseCircuit.joint_sum_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.joint_sum_apply

/-- info: 'SparseLowerBounds.PhaseCircuit.hitProj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.hitProj_apply

/-- info: 'SparseLowerBounds.PhaseCircuit.phase_eq_hitProj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.phase_eq_hitProj

/-- info: 'SparseLowerBounds.PhaseCircuit.oneHotOracle_eq_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.oneHotOracle_eq_phase

/-- info: 'SparseLowerBounds.PhaseCircuit.bitOracle_eq_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.bitOracle_eq_phase

/-- info: 'SparseLowerBounds.PhaseCircuit.withAncilla_proj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.withAncilla_proj_apply

/-- info: 'SparseLowerBounds.PhaseCircuit.hitProj_withAncilla_apply_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.hitProj_withAncilla_apply_zero

/-- info: 'SparseLowerBounds.PhaseCircuit.hitProj_withAncilla_apply_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.hitProj_withAncilla_apply_one

/-- info: 'SparseLowerBounds.PhaseCircuit.phase_withAncilla_apply_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.phase_withAncilla_apply_zero

/-- info: 'SparseLowerBounds.PhaseCircuit.phase_withAncilla_apply_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.phase_withAncilla_apply_one

/-- info: 'SparseLowerBounds.PhaseCircuit.hitProj_spectate_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.hitProj_spectate_apply

/-- info: 'SparseLowerBounds.PhaseCircuit.ancillaEmbed_apply_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.ancillaEmbed_apply_zero

/-- info: 'SparseLowerBounds.PhaseCircuit.ancillaEmbed_apply_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.ancillaEmbed_apply_one

/-- info: 'SparseLowerBounds.PhaseCircuit.isUnitary_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.isUnitary_fiber

/-- info: 'SparseLowerBounds.PhaseCircuit.circuit_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.circuit_intertwines

/-- info: 'SparseLowerBounds.PhaseCircuit.implementsOn_circuit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.implementsOn_circuit

/-- info: 'SparseLowerBounds.PhaseCircuit.implementsOn_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.implementsOn_const

/-- info: 'SparseLowerBounds.PhaseCircuit.implementsOn_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.PhaseCircuit.implementsOn_of_eq

/-! ### Helper: the release's spectator wrappers are `1_Ω ⊗ ·` (`Helpers/Adaptive/Access/Wrappers`) -/

/-- info: 'SparseLowerBounds.Helpers.Adaptive.Access.diagonal_const_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Adaptive.Access.diagonal_const_eq_fiber

/-- info: 'SparseLowerBounds.Helpers.Adaptive.Access.masked_true_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Adaptive.Access.masked_true_eq_fiber

/-- info: 'SparseLowerBounds.Helpers.Adaptive.Access.spectator_eq_conj_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Adaptive.Access.spectator_eq_conj_fiber

/-! ### Helper: clock vectors and the actual conditioning of the open clock (`Helpers/InstanceDecoder/Clock`) -/

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.clockShift_mulVec_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.clockShift_mulVec_apply

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.sum_atClock_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.sum_atClock_apply

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.sum_atClock_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.sum_atClock_eq

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.norm_sq_clockVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.norm_sq_clockVec

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.norm_atClock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.norm_atClock

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.norm_sq_sectorVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.norm_sq_sectorVec

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.norm_sectorVec_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.norm_sectorVec_zero_left

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.norm_sectorVec_zero_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.norm_sectorVec_zero_right

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.dilation_mulVec_sectorVec_zero_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.dilation_mulVec_sectorVec_zero_left

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.ringInverse_toEuclideanCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.ringInverse_toEuclideanCLM

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.norm_le_one_of_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.norm_le_one_of_mem_unitaryGroup

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.lt_norm_ringInverse_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.lt_norm_ringInverse_of

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.sum_sq_one_sub_pow_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.sum_sq_one_sub_pow_gt

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.clockMatrix_mulVec_ramp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.clockMatrix_mulVec_ramp

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.lt_norm_ringInverse_dilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.lt_norm_ringInverse_dilation

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.half_le_norm_dilation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.half_le_norm_dilation

/-! ### Parameters of Theorem `hsl:thm:main` (`Hamiltonian/Parameters`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.HSRange.one_le_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HSRange.one_le_tau

/-- info: 'SparseLowerBounds.Hamiltonian.HSRange.s_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HSRange.s_ge

/-- info: 'SparseLowerBounds.Hamiltonian.HSRange.eps_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HSRange.eps_pos

/-- info: 'SparseLowerBounds.Hamiltonian.HSRange.eps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HSRange.eps_le

/-- info: 'SparseLowerBounds.Hamiltonian.hsMu_add_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.hsMu_add_one

/-- info: 'SparseLowerBounds.Hamiltonian.two_pow_hsMu_succ_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.two_pow_hsMu_succ_le

/-- info: 'SparseLowerBounds.Hamiltonian.lt_two_pow_hsMu_add_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.lt_two_pow_hsMu_add_two

/-- info: 'SparseLowerBounds.Hamiltonian.four_le_hsMu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.four_le_hsMu

/-- info: 'SparseLowerBounds.Hamiltonian.one_le_hsMu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.one_le_hsMu

/-- info: 'SparseLowerBounds.Hamiltonian.two_mul_hsM_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.two_mul_hsM_le

/-- info: 'SparseLowerBounds.Hamiltonian.hsM_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.hsM_range

/-- info: 'SparseLowerBounds.Hamiltonian.one_le_timeN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.one_le_timeN

/-- info: 'SparseLowerBounds.Hamiltonian.hsL_eq_neg_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.hsL_eq_neg_log

/-- info: 'SparseLowerBounds.Hamiltonian.exp_neg_hsL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.exp_neg_hsL

/-- info: 'SparseLowerBounds.Hamiltonian.HSRange.tau_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HSRange.tau_pos

/-- info: 'SparseLowerBounds.Hamiltonian.HSRange.log_64_le_hsL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HSRange.log_64_le_hsL

/-- info: 'SparseLowerBounds.Hamiltonian.HSRange.four_le_hsL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HSRange.four_le_hsL

/-- info: 'SparseLowerBounds.Hamiltonian.HSRange.hsL_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HSRange.hsL_pos

/-- info: 'SparseLowerBounds.Hamiltonian.HSRange.one_le_hsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HSRange.one_le_hsH

/-- info: 'SparseLowerBounds.Hamiltonian.HSRange.hsH_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HSRange.hsH_pos

/-- info: 'SparseLowerBounds.Hamiltonian.HSRange.hsR_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HSRange.hsR_pos

/-- info: 'SparseLowerBounds.Hamiltonian.HSRange.hsR_le_hsL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HSRange.hsR_le_hsL

/-- info: 'SparseLowerBounds.Hamiltonian.HSRange.hsR_mul_hsH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HSRange.hsR_mul_hsH

/-- info: 'SparseLowerBounds.Hamiltonian.HSRange.precN_le_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HSRange.precN_le_quarter

/-- info: 'SparseLowerBounds.Hamiltonian.c0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.c0_pos

/-- info: 'SparseLowerBounds.Hamiltonian.cT_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.cT_pos

/-! ### Helper: shape of the dilated open clock (`Helpers/InstanceDecoder/Shape`) -/

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.star_clockMatrix_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.star_clockMatrix_apply

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.dilation_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.dilation_transpose

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.star_dilation_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.star_dilation_apply

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.clockMatrix_apply_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.clockMatrix_apply_ne_zero

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.dilation_clockMatrix_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.dilation_clockMatrix_ne_zero

/-- info: 'SparseLowerBounds.Helpers.InstanceDecoder.dilation_clockMatrix_row_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.InstanceDecoder.dilation_clockMatrix_row_sparse

/-! ### Numeric facts for the three hard families (`Hamiltonian/Numerics`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.half_le_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.half_le_floor

/-- info: 'SparseLowerBounds.Hamiltonian.sin_ge_half_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sin_ge_half_mul

/-- info: 'SparseLowerBounds.Hamiltonian.half_lt_sin_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.half_lt_sin_one

/-- info: 'SparseLowerBounds.Hamiltonian.quarter_rpow_neg_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.quarter_rpow_neg_inv

/-- info: 'SparseLowerBounds.Hamiltonian.four_rpow_inv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.four_rpow_inv_le

/-- info: 'SparseLowerBounds.Hamiltonian.quarter_rpow_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.quarter_rpow_root

/-- info: 'SparseLowerBounds.Hamiltonian.half_le_two_rpow_neg_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.half_le_two_rpow_neg_inv

/-- info: 'SparseLowerBounds.Hamiltonian.two_rpow_inv_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.two_rpow_inv_le_two

/-- info: 'SparseLowerBounds.Hamiltonian.inv_sqrt_two_le_two_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.inv_sqrt_two_le_two_rpow

/-- info: 'SparseLowerBounds.Hamiltonian.pow_div_two_rpow_neg_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.pow_div_two_rpow_neg_inv

/-- info: 'SparseLowerBounds.Hamiltonian.pow_div_two_rpow_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.pow_div_two_rpow_root

/-- info: 'SparseLowerBounds.Hamiltonian.quarter_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.quarter_hyp

/-- info: 'SparseLowerBounds.Hamiltonian.quarter_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.quarter_root

/-- info: 'SparseLowerBounds.Hamiltonian.timeN_eq_one_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.timeN_eq_one_of_lt

/-- info: 'SparseLowerBounds.Hamiltonian.timeC_eq_one_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.timeC_eq_one_of_lt

/-- info: 'SparseLowerBounds.Hamiltonian.timeN_eq_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.timeN_eq_floor

/-- info: 'SparseLowerBounds.Hamiltonian.timeC_mul_div_timeN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.timeC_mul_div_timeN

/-- info: 'SparseLowerBounds.Hamiltonian.tau_div_pi_le_timeN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.tau_div_pi_le_timeN

/-- info: 'SparseLowerBounds.Hamiltonian.timeC_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.timeC_pos

/-- info: 'SparseLowerBounds.Hamiltonian.timeC_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.timeC_le_one

/-- info: 'SparseLowerBounds.Hamiltonian.half_le_timeAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.half_le_timeAmp

/-- info: 'SparseLowerBounds.Hamiltonian.sqrt_div_two_lt_sqrt_hsM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sqrt_div_two_lt_sqrt_hsM

/-- info: 'SparseLowerBounds.Hamiltonian.time_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.time_final

/-- info: 'SparseLowerBounds.Hamiltonian.sin_div_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sin_div_pos

/-- info: 'SparseLowerBounds.Hamiltonian.amp_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.amp_ge

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_hyp

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_root

/-- info: 'SparseLowerBounds.Hamiltonian.log_exp_add_sixtyfour_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.log_exp_add_sixtyfour_le

/-- info: 'SparseLowerBounds.Hamiltonian.log_exp_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.log_exp_add_le

/-- info: 'SparseLowerBounds.Hamiltonian.HSRange.hsH_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HSRange.hsH_le

/-- info: 'SparseLowerBounds.Hamiltonian.hsR_ge_eight_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.hsR_ge_eight_tau

/-- info: 'SparseLowerBounds.Hamiltonian.precN_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precN_range

/-- info: 'SparseLowerBounds.Hamiltonian.hsR_le_eight_precN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.hsR_le_eight_precN

/-- info: 'SparseLowerBounds.Hamiltonian.two_precN_div_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.two_precN_div_le

/-- info: 'SparseLowerBounds.Hamiltonian.log_two_precN_div_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.log_two_precN_div_le

/-- info: 'SparseLowerBounds.Hamiltonian.precision_exp_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precision_exp_bound

/-- info: 'SparseLowerBounds.Hamiltonian.exp_neg_quarter_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.exp_neg_quarter_le_pow

/-- info: 'SparseLowerBounds.Hamiltonian.exp_neg_quarter_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.exp_neg_quarter_ge

/-- info: 'SparseLowerBounds.Hamiltonian.sixteen_eps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sixteen_eps_le

/-- info: 'SparseLowerBounds.Hamiltonian.rbound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.rbound

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_m_cond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_m_cond

/-- info: 'SparseLowerBounds.Hamiltonian.s_mul_hsR_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.s_mul_hsR_le

/-- info: 'SparseLowerBounds.Hamiltonian.mixrbound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixrbound

/-- info: 'SparseLowerBounds.Hamiltonian.s_mul_hsR_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.s_mul_hsR_lt

/-- info: 'SparseLowerBounds.Hamiltonian.failedmix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.failedmix

/-! ### The hard linear systems `A_X x = b` (`LinearSystems/Instance`) -/

/-- info: 'SparseLowerBounds.LinearSystems.card_hardIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.card_hardIndex

/-- info: 'SparseLowerBounds.LinearSystems.matrixOperator_eq_toEuclideanCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.matrixOperator_eq_toEuclideanCLM

/-- info: 'SparseLowerBounds.LinearSystems.norm_matrixOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.norm_matrixOperator

/-- info: 'SparseLowerBounds.LinearSystems.hardTransition_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.hardTransition_mem_unitaryGroup

/-- info: 'SparseLowerBounds.LinearSystems.norm_hardRHS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.norm_hardRHS

/-- info: 'SparseLowerBounds.LinearSystems.star_hardTransition_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.star_hardTransition_apply

/-- info: 'SparseLowerBounds.LinearSystems.star_hardC_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.star_hardC_apply

/-- info: 'SparseLowerBounds.LinearSystems.star_hardMatrix_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.star_hardMatrix_apply

/-- info: 'SparseLowerBounds.LinearSystems.hardMatrix_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.hardMatrix_transpose

/-- info: 'SparseLowerBounds.LinearSystems.hardMatrix_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.hardMatrix_isHermitian

/-- info: 'SparseLowerBounds.LinearSystems.hardMatrix_indefinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.hardMatrix_indefinite

/-- info: 'SparseLowerBounds.LinearSystems.hardMatrix_row_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.hardMatrix_row_sparse

/-- info: 'SparseLowerBounds.LinearSystems.hardMatrix_column_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.hardMatrix_column_sparse

/-- info: 'SparseLowerBounds.LinearSystems.norm_hardMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.norm_hardMatrix_le

/-- info: 'SparseLowerBounds.LinearSystems.isUnit_hardMatrix_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.isUnit_hardMatrix_matrix

/-- info: 'SparseLowerBounds.LinearSystems.isUnit_hardMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.isUnit_hardMatrix

/-- info: 'SparseLowerBounds.LinearSystems.norm_inverse_hardMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.norm_inverse_hardMatrix_le

/-- info: 'SparseLowerBounds.LinearSystems.quarter_lt_cond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.quarter_lt_cond

/-- info: 'SparseLowerBounds.LinearSystems.inverse_hardRHS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.LinearSystems.inverse_hardRHS

/-! ### Assembly of the three family bounds (`Hamiltonian/Assembly`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.c0_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.c0_le

/-- info: 'SparseLowerBounds.Hamiltonian.three_mul_c0_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.three_mul_c0_le

/-- info: 'SparseLowerBounds.Hamiltonian.log_two_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.log_two_le_one

/-- info: 'SparseLowerBounds.Hamiltonian.sqrt_two_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sqrt_two_le_two

/-- info: 'SparseLowerBounds.Hamiltonian.two_mul_sqrt_two_lt_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.two_mul_sqrt_two_lt_pi

/-- info: 'SparseLowerBounds.Hamiltonian.cT_le_inv_32' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.cT_le_inv_32

/-- info: 'SparseLowerBounds.Hamiltonian.cT_le_mixConst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.cT_le_mixConst

/-- info: 'SparseLowerBounds.Hamiltonian.cT_le_failedConst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.cT_le_failedConst

/-- info: 'SparseLowerBounds.Hamiltonian.sixtyfour_le_twelve_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sixtyfour_le_twelve_sqrt

/-- info: 'SparseLowerBounds.Hamiltonian.hsR_lt_of_small_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.hsR_lt_of_small_L

/-- info: 'SparseLowerBounds.Hamiltonian.sqrt_mul_hsR_le_of_small_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sqrt_mul_hsR_le_of_small_L

/-- info: 'SparseLowerBounds.Hamiltonian.hsR_le_of_small_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.hsR_le_of_small_L

/-- info: 'SparseLowerBounds.Hamiltonian.sum_le_of_small_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sum_le_of_small_L

/-- info: 'SparseLowerBounds.Hamiltonian.assembly_small_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.assembly_small_L

/-- info: 'SparseLowerBounds.Hamiltonian.third_cT_mul_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.third_cT_mul_sum_le

/-- info: 'SparseLowerBounds.Hamiltonian.assembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.assembly

/-! ### The Schrödinger flow `exp(-iτX)` (`Helpers/SpinChain/Flow`) -/

/-- info: 'SparseLowerBounds.Helpers.SpinChain.hasDerivAt_clm_apply_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.hasDerivAt_clm_apply_real

/-- info: 'SparseLowerBounds.Helpers.SpinChain.flow_eq_exp_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.flow_eq_exp_smul

/-- info: 'SparseLowerBounds.Helpers.SpinChain.flow_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.flow_smul

/-- info: 'SparseLowerBounds.Helpers.SpinChain.flow_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.flow_zero

/-- info: 'SparseLowerBounds.Helpers.SpinChain.flow_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.flow_add

/-- info: 'SparseLowerBounds.Helpers.SpinChain.hasDerivAt_flow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.hasDerivAt_flow

/-- info: 'SparseLowerBounds.Helpers.SpinChain.flow_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.flow_mem_unitary

/-- info: 'SparseLowerBounds.Helpers.SpinChain.hasDerivAt_flow_neg_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.hasDerivAt_flow_neg_apply

/-- info: 'SparseLowerBounds.Helpers.SpinChain.flow_apply_eq_of_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.flow_apply_eq_of_hasDerivAt

/-! ### The Schur test for the `L²` operator norm of a matrix (`Helpers/SpinChain/Schur`) -/

/-- info: 'SparseLowerBounds.Helpers.SpinChain.toEuclideanCLM_apply_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.toEuclideanCLM_apply_apply

/-- info: 'SparseLowerBounds.Helpers.SpinChain.sq_sum_le_of_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.sq_sum_le_of_weight

/-- info: 'SparseLowerBounds.Helpers.SpinChain.norm_le_of_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.norm_le_of_schur

/-- info: 'SparseLowerBounds.Helpers.SpinChain.one_le_norm_of_mulVec_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.one_le_norm_of_mulVec_eq

/-! ### Row sums of a tridiagonal (path) pattern on `Fin (n+1)` (`Helpers/SpinChain/PathSum`) -/

/-- info: 'SparseLowerBounds.Helpers.SpinChain.sum_ite_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.sum_ite_pred

/-- info: 'SparseLowerBounds.Helpers.SpinChain.sum_ite_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.sum_ite_succ

/-- info: 'SparseLowerBounds.Helpers.SpinChain.sum_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.sum_path

/-! ### Derivative of a trigonometric monomial (`Helpers/SpinChain/Solution`) -/

/-- info: 'SparseLowerBounds.Helpers.SpinChain.hasDerivAt_trigMonomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.hasDerivAt_trigMonomial

/-! ### Spin-chain weights `b_k = √((k+1)(n-k))/n` (`Helpers/SpinChain/Weight`) -/

/-- info: 'SparseLowerBounds.Helpers.SpinChain.weight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.weight_nonneg

/-- info: 'SparseLowerBounds.Helpers.SpinChain.weight_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.weight_le_one

/-- info: 'SparseLowerBounds.Helpers.SpinChain.weight_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.weight_pos

/-- info: 'SparseLowerBounds.Helpers.SpinChain.inv_sqrt_le_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.inv_sqrt_le_weight

/-- info: 'SparseLowerBounds.Helpers.SpinChain.weight_sq_add_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.weight_sq_add_sq_le

/-- info: 'SparseLowerBounds.Helpers.SpinChain.weight_mul_sqrt_choose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.weight_mul_sqrt_choose

/-- info: 'SparseLowerBounds.Helpers.SpinChain.weight_mul_sqrt_choose_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.weight_mul_sqrt_choose_succ

/-- info: 'SparseLowerBounds.Helpers.SpinChain.binom_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.binom_row

/-- info: 'SparseLowerBounds.Helpers.SpinChain.ladder_succ_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.ladder_succ_real

/-- info: 'SparseLowerBounds.Helpers.SpinChain.ladder_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.ladder_real

/-- info: 'SparseLowerBounds.Helpers.SpinChain.spin_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.SpinChain.spin_row

/-! ### The public spin chain `B_n` (`Hamiltonian/SpinChain`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.matrixOperator_eq_toEuclideanCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.matrixOperator_eq_toEuclideanCLM

/-- info: 'SparseLowerBounds.Hamiltonian.norm_matrixOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_matrixOperator

/-- info: 'SparseLowerBounds.Hamiltonian.star_matrixOperator_of_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.star_matrixOperator_of_isHermitian

/-- info: 'SparseLowerBounds.Hamiltonian.evolve_eq_exp_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.evolve_eq_exp_smul

/-- info: 'SparseLowerBounds.Hamiltonian.evolve_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.evolve_zero

/-- info: 'SparseLowerBounds.Hamiltonian.evolve_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.evolve_add

/-- info: 'SparseLowerBounds.Hamiltonian.hasDerivAt_evolve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.hasDerivAt_evolve

/-- info: 'SparseLowerBounds.Hamiltonian.evolve_mem_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.evolve_mem_unitary

/-- info: 'SparseLowerBounds.Hamiltonian.evolve_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.evolve_smul

/-- info: 'SparseLowerBounds.Hamiltonian.hasDerivAt_evolve_neg_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.hasDerivAt_evolve_neg_apply

/-- info: 'SparseLowerBounds.Hamiltonian.evolve_apply_eq_of_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.evolve_apply_eq_of_hasDerivAt

/-- info: 'SparseLowerBounds.Hamiltonian.norm_le_of_schur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_le_of_schur

/-- info: 'SparseLowerBounds.Hamiltonian.pathMatrix_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.pathMatrix_smul

/-- info: 'SparseLowerBounds.Hamiltonian.pathMatrix_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.pathMatrix_sub

/-- info: 'SparseLowerBounds.Hamiltonian.spinWeight_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.spinWeight_nonneg

/-- info: 'SparseLowerBounds.Hamiltonian.spinWeight_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.spinWeight_le_one

/-- info: 'SparseLowerBounds.Hamiltonian.spinWeight_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.spinWeight_pos

/-- info: 'SparseLowerBounds.Hamiltonian.inv_sqrt_le_spinWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.inv_sqrt_le_spinWeight

/-- info: 'SparseLowerBounds.Hamiltonian.spinWeight_sq_add_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.spinWeight_sq_add_sq_le

/-- info: 'SparseLowerBounds.Hamiltonian.spinWeight_mul_sqrt_choose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.spinWeight_mul_sqrt_choose

/-- info: 'SparseLowerBounds.Hamiltonian.spinWeight_mul_sqrt_choose_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.spinWeight_mul_sqrt_choose_succ

/-- info: 'SparseLowerBounds.Hamiltonian.isHermitian_pathMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.isHermitian_pathMatrix

/-- info: 'SparseLowerBounds.Hamiltonian.norm_evolve_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_evolve_apply

/-- info: 'SparseLowerBounds.Hamiltonian.norm_pathMatrix_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_pathMatrix_apply

/-- info: 'SparseLowerBounds.Hamiltonian.norm_pathMatrix_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_pathMatrix_symm

/-- info: 'SparseLowerBounds.Hamiltonian.sum_norm_pathMatrix_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sum_norm_pathMatrix_mul

/-- info: 'SparseLowerBounds.Hamiltonian.spinSolution_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.spinSolution_zero

/-- info: 'SparseLowerBounds.Hamiltonian.spinSolution_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.spinSolution_last

/-- info: 'SparseLowerBounds.Hamiltonian.hasDerivAt_spinSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.hasDerivAt_spinSolution

/-- info: 'SparseLowerBounds.Hamiltonian.endAmp_scaled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.endAmp_scaled

/-- info: 'SparseLowerBounds.Hamiltonian.binomVec_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.binomVec_pos

/-- info: 'SparseLowerBounds.Hamiltonian.sum_norm_spinMatrix_mul_binomVec_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sum_norm_spinMatrix_mul_binomVec_aux

/-- info: 'SparseLowerBounds.Hamiltonian.spinMatrix_mulVec_binomVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.spinMatrix_mulVec_binomVec

/-- info: 'SparseLowerBounds.Hamiltonian.sum_norm_spinMatrix_mul_binomVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sum_norm_spinMatrix_mul_binomVec

/-- info: 'SparseLowerBounds.Hamiltonian.norm_spinMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_spinMatrix

/-- info: 'SparseLowerBounds.Hamiltonian.norm_pathMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_pathMatrix_le

/-- info: 'SparseLowerBounds.Hamiltonian.sum_norm_pathMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sum_norm_pathMatrix_le

/-- info: 'SparseLowerBounds.Hamiltonian.norm_pathMatrix_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_pathMatrix_sub_le

/-! ### Exact dyadic weights (`Hamiltonian/Rounding`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.roundNum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.roundNum_le

/-- info: 'SparseLowerBounds.Hamiltonian.roundNum_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.roundNum_le_mul

/-- info: 'SparseLowerBounds.Hamiltonian.sub_roundNum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sub_roundNum_le

/-- info: 'SparseLowerBounds.Hamiltonian.two_pow_roundBits_inv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.two_pow_roundBits_inv_le

/-- info: 'SparseLowerBounds.Hamiltonian.chainDelta_le_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.chainDelta_le_left

/-- info: 'SparseLowerBounds.Hamiltonian.chainDelta_le_amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.chainDelta_le_amp

/-- info: 'SparseLowerBounds.Hamiltonian.chainDelta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.chainDelta_pos

/-- info: 'SparseLowerBounds.Hamiltonian.chainNum_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.chainNum_lt

/-- info: 'SparseLowerBounds.Hamiltonian.chainWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.chainWeight_le

/-- info: 'SparseLowerBounds.Hamiltonian.norm_pathMatrix_chainWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_pathMatrix_chainWeight_le

/-- info: 'SparseLowerBounds.Hamiltonian.chainWeight_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.chainWeight_pos

/-- info: 'SparseLowerBounds.Hamiltonian.norm_evolve_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_evolve_sub_le

/-- info: 'SparseLowerBounds.Hamiltonian.norm_endAmp_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_endAmp_sub_le

/-- info: 'SparseLowerBounds.Hamiltonian.norm_pathMatrix_sub_chainWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_pathMatrix_sub_chainWeight_le

/-- info: 'SparseLowerBounds.Hamiltonian.norm_evolve_sub_chainWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_evolve_sub_chainWeight_le

/-- info: 'SparseLowerBounds.Hamiltonian.norm_endAmp_chainWeight_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_endAmp_chainWeight_sub_le

/-! ### The search gadget `U_x` of `part:hsl` (`Hamiltonian/Gadget`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.Gadget.gadgetPos_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Gadget.gadgetPos_spec

/-- info: 'SparseLowerBounds.Hamiltonian.Gadget.gadgetPos_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Gadget.gadgetPos_eq_iff

/-- info: 'SparseLowerBounds.Hamiltonian.Gadget.neg_one_pow_eq_of_mod_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Gadget.neg_one_pow_eq_of_mod_two

/-- info: 'SparseLowerBounds.Hamiltonian.Gadget.sum_range_neg_one_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Gadget.sum_range_neg_one_pow

/-- info: 'SparseLowerBounds.Hamiltonian.star_alt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.star_alt

/-- info: 'SparseLowerBounds.Hamiltonian.sum_alt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sum_alt

/-- info: 'SparseLowerBounds.Hamiltonian.alt_gadgetPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.alt_gadgetPos

/-- info: 'SparseLowerBounds.Hamiltonian.gadget_mulVec_alt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.gadget_mulVec_alt

/-- info: 'SparseLowerBounds.Hamiltonian.conjTranspose_gadget_mulVec_alt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.conjTranspose_gadget_mulVec_alt

/-- info: 'SparseLowerBounds.Hamiltonian.norm_alt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_alt

/-! ### Helpers for `Hamiltonian/Chains`: operators of matrices, `B ⊗ I`, conjugation (`Helpers/Chains/Kron`) -/

/-- info: 'SparseLowerBounds.Helpers.Chains.mO_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.mO_eq

/-- info: 'SparseLowerBounds.Helpers.Chains.mO_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.mO_mul

/-- info: 'SparseLowerBounds.Helpers.Chains.mO_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.mO_conjTranspose

/-- info: 'SparseLowerBounds.Helpers.Chains.mO_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.mO_one

/-- info: 'SparseLowerBounds.Helpers.Chains.kron_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.kron_eq

/-- info: 'SparseLowerBounds.Helpers.Chains.mO_kronecker_one_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.mO_kronecker_one_apply

/-- info: 'SparseLowerBounds.Helpers.Chains.kronOne_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.kronOne_apply

/-- info: 'SparseLowerBounds.Helpers.Chains.kronOne_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.kronOne_smul

/-- info: 'SparseLowerBounds.Helpers.Chains.continuous_kronOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.continuous_kronOne

/-- info: 'SparseLowerBounds.Helpers.Chains.kronOne_mO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.kronOne_mO

/-- info: 'SparseLowerBounds.Helpers.Chains.evolve_kronecker_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.evolve_kronecker_one

/-- info: 'SparseLowerBounds.Helpers.Chains.slice_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.slice_apply

/-- info: 'SparseLowerBounds.Helpers.Chains.norm_sq_eq_sum_slice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.norm_sq_eq_sum_slice

/-- info: 'SparseLowerBounds.Helpers.Chains.norm_mO_kronecker_one_apply_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.norm_mO_kronecker_one_apply_sq

/-- info: 'SparseLowerBounds.Helpers.Chains.norm_kronecker_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.norm_kronecker_one

/-- info: 'SparseLowerBounds.Helpers.Chains.evolve_kronecker_one_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.evolve_kronecker_one_apply

/-- info: 'SparseLowerBounds.Helpers.Chains.evolve_unitary_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.evolve_unitary_conj

/-- info: 'SparseLowerBounds.Helpers.Chains.norm_unitary_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.norm_unitary_conj

/-! ### Helpers for `Hamiltonian/Chains`: block matrices on `clock × register` (`Helpers/Chains/Block`) -/

/-- info: 'SparseLowerBounds.Helpers.Chains.comp_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.comp_mul

/-- info: 'SparseLowerBounds.Helpers.Chains.comp_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.comp_conjTranspose

/-- info: 'SparseLowerBounds.Helpers.Chains.of_conjTranspose_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.of_conjTranspose_diagonal

/-- info: 'SparseLowerBounds.Helpers.Chains.conj_comp_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.conj_comp_diagonal

/-- info: 'SparseLowerBounds.Helpers.Chains.comp_diagonal_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.comp_diagonal_conj

/-- info: 'SparseLowerBounds.Helpers.Chains.comp_diagonal_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.comp_diagonal_mem_unitaryGroup

/-- info: 'SparseLowerBounds.Helpers.Chains.kronecker_one_eq_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.kronecker_one_eq_comp

/-- info: 'SparseLowerBounds.Helpers.Chains.prod_filter_lt_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.prod_filter_lt_zero

/-- info: 'SparseLowerBounds.Helpers.Chains.prod_filter_lt_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.prod_filter_lt_of_le

/-- info: 'SparseLowerBounds.Helpers.Chains.prod_filter_lt_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.prod_filter_lt_succ

/-! ### Helpers for `Hamiltonian/Chains`: the gauge computations (`Helpers/Chains/Gauge`) -/

/-- info: 'SparseLowerBounds.Helpers.Chains.cvec_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.cvec_apply

/-- info: 'SparseLowerBounds.Helpers.Chains.norm_cvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.norm_cvec

/-- info: 'SparseLowerBounds.Helpers.Chains.inner_cvec_evolve_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.inner_cvec_evolve_kronecker

/-- info: 'SparseLowerBounds.Helpers.Chains.blockDiag_eq_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.blockDiag_eq_comp

/-- info: 'SparseLowerBounds.Helpers.Chains.conjTranspose_blockDiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.conjTranspose_blockDiag

/-- info: 'SparseLowerBounds.Helpers.Chains.blockDiag_cvec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.blockDiag_cvec

/-- info: 'SparseLowerBounds.Helpers.Chains.conjTranspose_gadget_mul_gadget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.conjTranspose_gadget_mul_gadget

/-- info: 'SparseLowerBounds.Helpers.Chains.transpose_gadget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.transpose_gadget

/-- info: 'SparseLowerBounds.Helpers.Chains.gauge_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.gauge_block

/-- info: 'SparseLowerBounds.Helpers.Chains.mO_diagonal_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.mO_diagonal_apply

/-- info: 'SparseLowerBounds.Helpers.Chains.mO_diagonal_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.mO_diagonal_single

/-- info: 'SparseLowerBounds.Helpers.Chains.conjTranspose_mulVec_of_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.conjTranspose_mulVec_of_mulVec

/-- info: 'SparseLowerBounds.Helpers.Chains.signedPath_eq_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Helpers.Chains.signedPath_eq_conj

/-! ### Decorated chains and their parity amplitudes (`Hamiltonian/Chains`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.searchChain_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchChain_transpose

/-- info: 'SparseLowerBounds.Hamiltonian.star_searchChain_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.star_searchChain_apply

/-- info: 'SparseLowerBounds.Hamiltonian.scalarChain_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarChain_transpose

/-- info: 'SparseLowerBounds.Hamiltonian.Chains.star_bitSign'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Chains.star_bitSign'

/-- info: 'SparseLowerBounds.Hamiltonian.star_scalarChain_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.star_scalarChain_apply

/-- info: 'SparseLowerBounds.Hamiltonian.norm_chainVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_chainVec

/-- info: 'SparseLowerBounds.Hamiltonian.isHermitian_searchChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.isHermitian_searchChain

/-- info: 'SparseLowerBounds.Hamiltonian.isHermitian_scalarChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.isHermitian_scalarChain

/-- info: 'SparseLowerBounds.Hamiltonian.evolve_unitary_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.evolve_unitary_conj

/-- info: 'SparseLowerBounds.Hamiltonian.norm_unitary_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_unitary_conj

/-- info: 'SparseLowerBounds.Hamiltonian.norm_kronecker_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_kronecker_one

/-- info: 'SparseLowerBounds.Hamiltonian.evolve_kronecker_one_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.evolve_kronecker_one_apply

/-- info: 'SparseLowerBounds.Hamiltonian.inner_chainVec_evolve_kronecker' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.inner_chainVec_evolve_kronecker

/-- info: 'SparseLowerBounds.Hamiltonian.Chains.gaugeBlock_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Chains.gaugeBlock_zero

/-- info: 'SparseLowerBounds.Hamiltonian.Chains.gaugeBlock_succ_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Chains.gaugeBlock_succ_of_lt

/-- info: 'SparseLowerBounds.Hamiltonian.Chains.gaugeBlock_succ_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Chains.gaugeBlock_succ_of_le

/-- info: 'SparseLowerBounds.Hamiltonian.Chains.gaugeSign_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Chains.gaugeSign_succ

/-- info: 'SparseLowerBounds.Hamiltonian.Chains.gaugeSign_succ_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Chains.gaugeSign_succ_of_le

/-- info: 'SparseLowerBounds.Hamiltonian.gaugeBlock_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.gaugeBlock_mem_unitaryGroup

/-- info: 'SparseLowerBounds.Hamiltonian.gaugeSign_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.gaugeSign_zero

/-- info: 'SparseLowerBounds.Hamiltonian.gaugeSign_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.gaugeSign_of_le

/-- info: 'SparseLowerBounds.Hamiltonian.star_gaugeSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.star_gaugeSign

/-- info: 'SparseLowerBounds.Hamiltonian.gaugeSign_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.gaugeSign_mul_self

/-- info: 'SparseLowerBounds.Hamiltonian.gaugeBlock_mulVec_alt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.gaugeBlock_mulVec_alt

/-- info: 'SparseLowerBounds.Hamiltonian.Chains.conjTranspose_gaugeBlock_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Chains.conjTranspose_gaugeBlock_mul

/-- info: 'SparseLowerBounds.Hamiltonian.Chains.searchChain_eq_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Chains.searchChain_eq_comp

/-- info: 'SparseLowerBounds.Hamiltonian.searchGauge_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchGauge_mem_unitaryGroup

/-- info: 'SparseLowerBounds.Hamiltonian.searchGauge_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchGauge_conj

/-- info: 'SparseLowerBounds.Hamiltonian.searchChain_eq_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchChain_eq_conj

/-- info: 'SparseLowerBounds.Hamiltonian.searchGauge_chainVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchGauge_chainVec

/-- info: 'SparseLowerBounds.Hamiltonian.conjTranspose_searchGauge_chainVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.conjTranspose_searchGauge_chainVec

/-- info: 'SparseLowerBounds.Hamiltonian.bitSign_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitSign_mul_self

/-- info: 'SparseLowerBounds.Hamiltonian.star_bitSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.star_bitSign

/-- info: 'SparseLowerBounds.Hamiltonian.Chains.bitGaugeSign_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Chains.bitGaugeSign_mul_self

/-- info: 'SparseLowerBounds.Hamiltonian.bitGaugeSign_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitGaugeSign_zero

/-- info: 'SparseLowerBounds.Hamiltonian.bitGaugeSign_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitGaugeSign_of_le

/-- info: 'SparseLowerBounds.Hamiltonian.signGauge_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.signGauge_conjTranspose

/-- info: 'SparseLowerBounds.Hamiltonian.signGauge_mem_unitaryGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.signGauge_mem_unitaryGroup

/-- info: 'SparseLowerBounds.Hamiltonian.scalarChain_eq_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarChain_eq_conj

/-- info: 'SparseLowerBounds.Hamiltonian.searchChain_amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchChain_amp

/-- info: 'SparseLowerBounds.Hamiltonian.scalarChain_amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarChain_amp

/-- info: 'SparseLowerBounds.Hamiltonian.norm_searchChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_searchChain

/-- info: 'SparseLowerBounds.Hamiltonian.norm_scalarChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_scalarChain

/-! ### Block-diagonal matrices: norm and Schrödinger evolution (`Helpers/HsInstance/Blocks`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.norm_toLp_mulVec_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.norm_toLp_mulVec_le

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.norm_le_of_mulVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.norm_le_of_mulVec

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.norm_toLp_sum_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.norm_toLp_sum_sq

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.norm_toLp_sumElim_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.norm_toLp_sumElim_zero

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.norm_toLp_zero_sumElim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.norm_toLp_zero_sumElim

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.norm_fromBlocks_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.norm_fromBlocks_zero

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.evolve_matrixOperator_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.evolve_matrixOperator_apply

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.hasDerivAt_evolve_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.hasDerivAt_evolve_apply

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.inlOp_apply_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.inlOp_apply_inl

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.inlOp_apply_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.inlOp_apply_inr

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.inrOp_apply_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.inrOp_apply_inl

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.inrOp_apply_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.inrOp_apply_inr

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.evolve_fromBlocks_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.evolve_fromBlocks_zero

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.evolve_apply_of_matrixOperator_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.evolve_apply_of_matrixOperator_eq_zero

/-! ### Rows, columns and sparsity of block-diagonal matrices (`Helpers/HsInstance/BlockRows`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_fromBlocks_row_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_fromBlocks_row_inl

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_fromBlocks_row_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_fromBlocks_row_inr

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_fromBlocks_col_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_fromBlocks_col_inl

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_fromBlocks_col_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_fromBlocks_col_inr

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_fromBlocks_row_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_fromBlocks_row_le

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_fromBlocks_col_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_fromBlocks_col_le

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.card_fromBlocks_row_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.card_fromBlocks_row_inl

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.card_fromBlocks_row_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.card_fromBlocks_row_inr

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.card_fromBlocks_col_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.card_fromBlocks_col_inl

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.card_fromBlocks_col_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.card_fromBlocks_col_inr

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.card_fromBlocks_row_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.card_fromBlocks_row_le

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.card_fromBlocks_col_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.card_fromBlocks_col_le

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.star_fromBlocks_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.star_fromBlocks_apply

/-! ### Row masses and sparsity of the decorated chains (`Helpers/HsInstance/ChainRows`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.sum_norm_sq_row_of_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.sum_norm_sq_row_of_unitary

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.sum_norm_sq_col_of_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.sum_norm_sq_col_of_unitary

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.edge_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.edge_mass_le

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.sum_ite_eq_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.sum_ite_eq_succ

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.sum_ite_succ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.sum_ite_succ_eq

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.norm_bitSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.norm_bitSign

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_searchChain_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_searchChain_row

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_searchChain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_searchChain_le

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.sq_scalarChain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.sq_scalarChain

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_scalarChain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.sum_sq_scalarChain_le

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.card_neighbours_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.card_neighbours_le

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.card_row_searchChain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.card_row_searchChain_le

/-- info: 'SparseLowerBounds.Hamiltonian.HsInstance.card_row_scalarChain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsInstance.card_row_scalarChain_le

/-! ### The hard Hamiltonians (`Hamiltonian/Instance`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.evolve_fromBlocks_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.evolve_fromBlocks_zero

/-- info: 'SparseLowerBounds.Hamiltonian.norm_fromBlocks_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_fromBlocks_zero

/-- info: 'SparseLowerBounds.Hamiltonian.le_two_pow_padExp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.le_two_pow_padExp

/-- info: 'SparseLowerBounds.Hamiltonian.padBlock_apply_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.padBlock_apply_ne_zero

/-- info: 'SparseLowerBounds.Hamiltonian.norm_padBlock_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_padBlock_le

/-- info: 'SparseLowerBounds.Hamiltonian.norm_refBlock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_refBlock

/-- info: 'SparseLowerBounds.Hamiltonian.evolve_refBlock_single_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.evolve_refBlock_single_zero

/-- info: 'SparseLowerBounds.Hamiltonian.padBlock_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.padBlock_transpose

/-- info: 'SparseLowerBounds.Hamiltonian.sum_sq_padBlock_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sum_sq_padBlock_le

/-- info: 'SparseLowerBounds.Hamiltonian.sum_sq_padBlock_col_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sum_sq_padBlock_col_le

/-- info: 'SparseLowerBounds.Hamiltonian.card_padBlock_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.card_padBlock_row

/-- info: 'SparseLowerBounds.Hamiltonian.card_padBlock_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.card_padBlock_col

/-- info: 'SparseLowerBounds.Hamiltonian.sum_sq_refBlock_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sum_sq_refBlock_le

/-- info: 'SparseLowerBounds.Hamiltonian.sum_sq_refBlock_col_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sum_sq_refBlock_col_le

/-- info: 'SparseLowerBounds.Hamiltonian.card_refBlock_row_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.card_refBlock_row_le

/-- info: 'SparseLowerBounds.Hamiltonian.card_refBlock_col_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.card_refBlock_col_le

/-- info: 'SparseLowerBounds.Hamiltonian.norm_fullMatrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_fullMatrix

/-- info: 'SparseLowerBounds.Hamiltonian.evolve_fullMatrix_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.evolve_fullMatrix_core

/-- info: 'SparseLowerBounds.Hamiltonian.fullMatrix_transpose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.fullMatrix_transpose

/-- info: 'SparseLowerBounds.Hamiltonian.star_fullMatrix_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.star_fullMatrix_apply

/-- info: 'SparseLowerBounds.Hamiltonian.sum_sq_fullMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sum_sq_fullMatrix_le

/-- info: 'SparseLowerBounds.Hamiltonian.sum_sq_fullMatrix_col_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sum_sq_fullMatrix_col_le

/-- info: 'SparseLowerBounds.Hamiltonian.sum_sq_fullMatrix_refOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sum_sq_fullMatrix_refOne

/-- info: 'SparseLowerBounds.Hamiltonian.card_row_fullMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.card_row_fullMatrix_le

/-- info: 'SparseLowerBounds.Hamiltonian.card_col_fullMatrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.card_col_fullMatrix_le

/-- info: 'SparseLowerBounds.Hamiltonian.card_row_fullMatrix_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.card_row_fullMatrix_pad

/-- info: 'SparseLowerBounds.Hamiltonian.card_col_fullMatrix_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.card_col_fullMatrix_pad

/-- info: 'SparseLowerBounds.Hamiltonian.sum_sq_searchChain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sum_sq_searchChain_le

/-- info: 'SparseLowerBounds.Hamiltonian.sum_sq_scalarChain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.sum_sq_scalarChain_le

/-- info: 'SparseLowerBounds.Hamiltonian.card_row_searchChain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.card_row_searchChain_le

/-- info: 'SparseLowerBounds.Hamiltonian.card_row_scalarChain_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.card_row_scalarChain_le

/-- info: 'SparseLowerBounds.Hamiltonian.card_searchIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.card_searchIndex

/-- info: 'SparseLowerBounds.Hamiltonian.card_scalarIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.card_scalarIndex

/-- info: 'SparseLowerBounds.Hamiltonian.searchHam_realSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchHam_realSymmetric

/-- info: 'SparseLowerBounds.Hamiltonian.scalarHam_realSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarHam_realSymmetric

/-- info: 'SparseLowerBounds.Hamiltonian.fullMatrix_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.fullMatrix_props

/-- info: 'SparseLowerBounds.Hamiltonian.searchHam_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchHam_props

/-- info: 'SparseLowerBounds.Hamiltonian.scalarHam_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarHam_props

/-! ### Reading the amplitude as a correlation (`Hamiltonian/Amplitude`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.coreVec_apply_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.coreVec_apply_inl

/-- info: 'SparseLowerBounds.Hamiltonian.coreVec_apply_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.coreVec_apply_inr

/-- info: 'SparseLowerBounds.Hamiltonian.inner_coreVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.inner_coreVec

/-- info: 'SparseLowerBounds.Hamiltonian.norm_coreVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_coreVec

/-- info: 'SparseLowerBounds.Hamiltonian.inner_single_refZero_coreVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.inner_single_refZero_coreVec

/-- info: 'SparseLowerBounds.Hamiltonian.evolve_coreVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.evolve_coreVec

/-- info: 'SparseLowerBounds.Hamiltonian.evolve_refZero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.evolve_refZero

/-- info: 'SparseLowerBounds.Hamiltonian.evolve_readoutInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.evolve_readoutInput

/-- info: 'SparseLowerBounds.Hamiltonian.readoutObs_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.readoutObs_apply

/-- info: 'SparseLowerBounds.Hamiltonian.inner_readoutObs_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.inner_readoutObs_self

/-- info: 'SparseLowerBounds.Hamiltonian.isSelfAdjoint_readoutObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.isSelfAdjoint_readoutObs

/-- info: 'SparseLowerBounds.Hamiltonian.norm_readoutObs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_readoutObs_le

/-- info: 'SparseLowerBounds.Hamiltonian.norm_readoutInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_readoutInput

/-- info: 'SparseLowerBounds.Hamiltonian.readout_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.readout_expectation

/-- info: 'SparseLowerBounds.Hamiltonian.norm_searchInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_searchInput

/-- info: 'SparseLowerBounds.Hamiltonian.norm_scalarInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_scalarInput

/-- info: 'SparseLowerBounds.Hamiltonian.searchObs_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchObs_contraction

/-- info: 'SparseLowerBounds.Hamiltonian.scalarObs_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarObs_contraction

/-- info: 'SparseLowerBounds.Hamiltonian.seven_eighths_le_re_I_pow_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.seven_eighths_le_re_I_pow_mul

/-- info: 'SparseLowerBounds.Hamiltonian.search_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.search_expectation

/-- info: 'SparseLowerBounds.Hamiltonian.scalar_expectation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalar_expectation

/-- info: 'SparseLowerBounds.Hamiltonian.Amplitude.mul_re_I_pow_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Amplitude.mul_re_I_pow_sign

/-- info: 'SparseLowerBounds.Hamiltonian.search_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.search_corr

/-- info: 'SparseLowerBounds.Hamiltonian.scalar_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalar_corr

/-! ### Accuracy, readout correlation and the endpoint form (`Hamiltonian/Accuracy`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.corr_of_accurate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.corr_of_accurate

/-- info: 'SparseLowerBounds.Hamiltonian.norm_inner_sub_inner_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_inner_sub_inner_le

/-- info: 'SparseLowerBounds.Hamiltonian.abs_inner_sub_inner_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.abs_inner_sub_inner_le

/-- info: 'SparseLowerBounds.Hamiltonian.endpointReadout_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.endpointReadout_apply

/-- info: 'SparseLowerBounds.Hamiltonian.Accuracy.adjoint_apply_iota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Accuracy.adjoint_apply_iota

/-- info: 'SparseLowerBounds.Hamiltonian.Accuracy.inner_iota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Accuracy.inner_iota

/-- info: 'SparseLowerBounds.Hamiltonian.Accuracy.inner_iota_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Accuracy.inner_iota_single

/-- info: 'SparseLowerBounds.Hamiltonian.Accuracy.inner_iota_compl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Accuracy.inner_iota_compl

/-- info: 'SparseLowerBounds.Hamiltonian.Accuracy.inner_compl_iota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Accuracy.inner_compl_iota

/-- info: 'SparseLowerBounds.Hamiltonian.Accuracy.inner_compl_compl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Accuracy.inner_compl_compl

/-- info: 'SparseLowerBounds.Hamiltonian.Accuracy.norm_iota_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Accuracy.norm_iota_le

/-- info: 'SparseLowerBounds.Hamiltonian.Accuracy.inner_endpointReadout_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.Accuracy.inner_endpointReadout_apply

/-- info: 'SparseLowerBounds.Hamiltonian.inner_endpointReadout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.inner_endpointReadout

/-- info: 'SparseLowerBounds.Hamiltonian.endpointReadout_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.endpointReadout_isometry

/-- info: 'SparseLowerBounds.Hamiltonian.endpointReadout_apply_iota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.endpointReadout_apply_iota

/-- info: 'SparseLowerBounds.Hamiltonian.inner_endpointReadout_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.inner_endpointReadout_lift

/-- info: 'SparseLowerBounds.Hamiltonian.inner_outObs_endpointReadout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.inner_outObs_endpointReadout

/-- info: 'SparseLowerBounds.Hamiltonian.accurate_of_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.accurate_of_endpoint

/-! ### Native sparse data from one-bit word tables (`Hamiltonian/DataBuilder`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.word_valMinAbs_intCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.word_valMinAbs_intCast

/-- info: 'SparseLowerBounds.Hamiltonian.wordDecode_intCast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.wordDecode_intCast

/-- info: 'SparseLowerBounds.Hamiltonian.norm_wordDecode_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.norm_wordDecode_le

/-- info: 'SparseLowerBounds.Hamiltonian.BitTable.bit_of_addr_none' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.BitTable.bit_of_addr_none

/-- info: 'SparseLowerBounds.Hamiltonian.BitTable.bit_of_addr_some' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.BitTable.bit_of_addr_some

/-- info: 'SparseLowerBounds.Hamiltonian.BitTable.bit_eq_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.BitTable.bit_eq_true_iff

/-- info: 'SparseLowerBounds.Hamiltonian.BitTable.value_of_addr_none' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.BitTable.value_of_addr_none

/-- info: 'SparseLowerBounds.Hamiltonian.BitTable.value_of_addr_some' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.BitTable.value_of_addr_some

/-- info: 'SparseLowerBounds.Hamiltonian.slotPerm_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.slotPerm_slot

/-- info: 'SparseLowerBounds.Hamiltonian.rowEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.rowEquiv_apply

/-- info: 'SparseLowerBounds.Hamiltonian.colEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.colEquiv_apply

/-- info: 'SparseLowerBounds.Hamiltonian.rowEquiv_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.rowEquiv_slot

/-- info: 'SparseLowerBounds.Hamiltonian.colEquiv_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.colEquiv_slot

/-- info: 'SparseLowerBounds.Hamiltonian.permCLM_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.permCLM_apply

/-- info: 'SparseLowerBounds.Hamiltonian.permCLM_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.permCLM_single

/-- info: 'SparseLowerBounds.Hamiltonian.isUnitary_permCLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.isUnitary_permCLM

/-- info: 'SparseLowerBounds.Hamiltonian.bitData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitData_matrix

/-- info: 'SparseLowerBounds.Hamiltonian.bitData_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitData_table

/-- info: 'SparseLowerBounds.Hamiltonian.bitData_locators_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitData_locators_const

/-- info: 'SparseLowerBounds.Hamiltonian.bitData_rowOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitData_rowOracle

/-- info: 'SparseLowerBounds.Hamiltonian.bitData_columnOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitData_columnOracle

/-- info: 'SparseLowerBounds.Hamiltonian.bitData_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitData_decode

/-! ### Native primitives of one-bit data from Boolean queries (`Hamiltonian/Compile`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.bitAddressFamily_proj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitAddressFamily_proj_apply

/-- info: 'SparseLowerBounds.Hamiltonian.hitProj_bitAddress_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.hitProj_bitAddress_apply

/-- info: 'SparseLowerBounds.Hamiltonian.bitWordGate_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitWordGate_apply

/-- info: 'SparseLowerBounds.Hamiltonian.bitWordGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitWordGate_unitary

/-- info: 'SparseLowerBounds.Hamiltonian.bitBranchGate_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitBranchGate_zero

/-- info: 'SparseLowerBounds.Hamiltonian.bitBranchGate_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitBranchGate_one

/-- info: 'SparseLowerBounds.Hamiltonian.bitBranchGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitBranchGate_unitary

/-- info: 'SparseLowerBounds.Hamiltonian.oracles_bitData_rowLocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.oracles_bitData_rowLocation

/-- info: 'SparseLowerBounds.Hamiltonian.oracles_bitData_columnLocation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.oracles_bitData_columnLocation

/-- info: 'SparseLowerBounds.Hamiltonian.oracles_bitData_value_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.oracles_bitData_value_apply

/-- info: 'SparseLowerBounds.Hamiltonian.oracles_bitData_value_apply_eq_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.oracles_bitData_value_apply_eq_gate

/-- info: 'SparseLowerBounds.Hamiltonian.bitValue_branch_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitValue_branch_zero

/-- info: 'SparseLowerBounds.Hamiltonian.bitValue_branch_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitValue_branch_one

/-- info: 'SparseLowerBounds.Hamiltonian.bitValue_spec_branch_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitValue_spec_branch_zero

/-- info: 'SparseLowerBounds.Hamiltonian.bitValue_spec_branch_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.bitValue_spec_branch_one

/-- info: 'SparseLowerBounds.Hamiltonian.implementsOn_bitData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.implementsOn_bitData

/-- info: 'SparseLowerBounds.Hamiltonian.implementsOn_bitData_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.implementsOn_bitData_spec

/-! ### Entry formulas of the hard Hamiltonians (`Hamiltonian/HardDataEntries`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.fullMatrix_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.fullMatrix_core

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.fullMatrix_core_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.fullMatrix_core_side

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.fullMatrix_side_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.fullMatrix_side_core

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.fullMatrix_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.fullMatrix_ref

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.fullMatrix_ref_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.fullMatrix_ref_pad

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.fullMatrix_pad_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.fullMatrix_pad_ref

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.fullMatrix_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.fullMatrix_pad

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.searchChain_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.searchChain_succ

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.searchChain_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.searchChain_pred

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.searchChain_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.searchChain_far

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.scalarChain_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.scalarChain_succ

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.scalarChain_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.scalarChain_pred

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.scalarChain_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.scalarChain_far

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.searchWord_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.searchWord_div

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.scalarWord_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.scalarWord_div

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.padWord_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.padWord_div

/-- info: 'SparseLowerBounds.Hamiltonian.HardData.topWord_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardData.topWord_div

/-! ### Hard data, part 1: shared locators and the signed scalar family (`Hamiltonian/HardDataScalar`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.HardDataScalar.mod_of_lt_two_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardDataScalar.mod_of_lt_two_mul

/-- info: 'SparseLowerBounds.Hamiltonian.HardDataScalar.succ_mod_ne_add_mod' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HardDataScalar.succ_mod_ne_add_mod

/-- info: 'SparseLowerBounds.Hamiltonian.scalarLocFun_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarLocFun_injective

/-- info: 'SparseLowerBounds.Hamiltonian.padSlot_apply' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.padSlot_apply

/-- info: 'SparseLowerBounds.Hamiltonian.refLoc_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.refLoc_zero

/-- info: 'SparseLowerBounds.Hamiltonian.ref_mem_range_fullLoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.ref_mem_range_fullLoc

/-- info: 'SparseLowerBounds.Hamiltonian.pad_mem_range_fullLoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.pad_mem_range_fullLoc

/-- info: 'SparseLowerBounds.Hamiltonian.scalarLocFun_zero' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarLocFun_zero

/-- info: 'SparseLowerBounds.Hamiltonian.scalarLocFun_one' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarLocFun_one

/-- info: 'SparseLowerBounds.Hamiltonian.scalarLoc_adj_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarLoc_adj_mem

/-- info: 'SparseLowerBounds.Hamiltonian.scalarTable_value_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarTable_value_succ

/-- info: 'SparseLowerBounds.Hamiltonian.scalarTable_value_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarTable_value_pred

/-- info: 'SparseLowerBounds.Hamiltonian.scalarTable_value_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarTable_value_far

/-- info: 'SparseLowerBounds.Hamiltonian.scalarTable_value_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarTable_value_ref

/-- info: 'SparseLowerBounds.Hamiltonian.scalarTable_value_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarTable_value_pad

/-- info: 'SparseLowerBounds.Hamiltonian.scalarTable_value_core_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarTable_value_core_side

/-- info: 'SparseLowerBounds.Hamiltonian.scalarTable_value_side_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarTable_value_side_core

/-- info: 'SparseLowerBounds.Hamiltonian.scalarTable_value_ref_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarTable_value_ref_pad

/-- info: 'SparseLowerBounds.Hamiltonian.scalarTable_value_pad_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarTable_value_pad_ref

/-- info: 'SparseLowerBounds.Hamiltonian.scalarTable_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarTable_bound

/-- info: 'SparseLowerBounds.Hamiltonian.scalarTable_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarTable_decode

/-- info: 'SparseLowerBounds.Hamiltonian.scalarLoc_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarLoc_row

/-- info: 'SparseLowerBounds.Hamiltonian.scalarLoc_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarLoc_col

/-- info: 'SparseLowerBounds.Hamiltonian.scalarData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarData_matrix

/-- info: 'SparseLowerBounds.Hamiltonian.scalarData_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarData_table

/-- info: 'SparseLowerBounds.Hamiltonian.scalarData_rowloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarData_rowloc

/-- info: 'SparseLowerBounds.Hamiltonian.scalarData_locators_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.scalarData_locators_const

/-! ### The hard families as release sparse-access data (`Hamiltonian/HardData`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.searchLocFun_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchLocFun_injective

/-- info: 'SparseLowerBounds.Hamiltonian.searchLocFun_of_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchLocFun_of_lt

/-- info: 'SparseLowerBounds.Hamiltonian.searchLocFun_of_lt_two_mul' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchLocFun_of_lt_two_mul

/-- info: 'SparseLowerBounds.Hamiltonian.searchLoc_succ_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchLoc_succ_mem

/-- info: 'SparseLowerBounds.Hamiltonian.searchLoc_pred_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchLoc_pred_mem

/-- info: 'SparseLowerBounds.Hamiltonian.searchLoc_adj_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchLoc_adj_mem

/-- info: 'SparseLowerBounds.Hamiltonian.searchTable_value_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchTable_value_succ

/-- info: 'SparseLowerBounds.Hamiltonian.searchTable_value_pred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchTable_value_pred

/-- info: 'SparseLowerBounds.Hamiltonian.searchTable_value_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchTable_value_far

/-- info: 'SparseLowerBounds.Hamiltonian.searchTable_value_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchTable_value_ref

/-- info: 'SparseLowerBounds.Hamiltonian.searchTable_value_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchTable_value_pad

/-- info: 'SparseLowerBounds.Hamiltonian.searchTable_value_core_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchTable_value_core_side

/-- info: 'SparseLowerBounds.Hamiltonian.searchTable_value_side_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchTable_value_side_core

/-- info: 'SparseLowerBounds.Hamiltonian.searchTable_value_ref_pad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchTable_value_ref_pad

/-- info: 'SparseLowerBounds.Hamiltonian.searchTable_value_pad_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchTable_value_pad_ref

/-- info: 'SparseLowerBounds.Hamiltonian.searchTable_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchTable_bound

/-- info: 'SparseLowerBounds.Hamiltonian.gadget_oneHotBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.gadget_oneHotBits

/-- info: 'SparseLowerBounds.Hamiltonian.searchTable_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchTable_decode

/-- info: 'SparseLowerBounds.Hamiltonian.pos_of_two_mul_two_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.pos_of_two_mul_two_pow_le

/-- info: 'SparseLowerBounds.Hamiltonian.searchLoc_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchLoc_row

/-- info: 'SparseLowerBounds.Hamiltonian.searchLoc_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchLoc_col

/-- info: 'SparseLowerBounds.Hamiltonian.searchData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchData_matrix

/-- info: 'SparseLowerBounds.Hamiltonian.searchData_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchData_table

/-- info: 'SparseLowerBounds.Hamiltonian.searchData_rowloc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchData_rowloc

/-- info: 'SparseLowerBounds.Hamiltonian.searchData_locators_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.searchData_locators_const

/-! ### The search-decorated families: time and mixed lower bounds (`Hamiltonian/SearchFamily`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.search_cost_of_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.search_cost_of_corr

/-- info: 'SparseLowerBounds.Hamiltonian.outObs_searchObs_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.outObs_searchObs_contraction

/-- info: 'SparseLowerBounds.Hamiltonian.time_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.time_corr

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_corr

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_one_le_mu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_one_le_mu

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_cost_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_cost_arith

/-- info: 'SparseLowerBounds.Hamiltonian.time_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.time_general

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_general

/-! ### The signed scalar family: precision lower bound (`Hamiltonian/PrecisionFamily`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.precision_cost_of_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precision_cost_of_corr

/-- info: 'SparseLowerBounds.Hamiltonian.precision_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precision_corr

/-- info: 'SparseLowerBounds.Hamiltonian.precision_corr_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precision_corr_pos

/-- info: 'SparseLowerBounds.Hamiltonian.precision_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precision_general

/-! ### The three family bounds for the release's native primitives (`Hamiltonian/Native`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.implementsOn_searchData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.implementsOn_searchData

/-- info: 'SparseLowerBounds.Hamiltonian.implementsOn_searchData_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.implementsOn_searchData_spec

/-- info: 'SparseLowerBounds.Hamiltonian.implementsOn_scalarData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.implementsOn_scalarData

/-- info: 'SparseLowerBounds.Hamiltonian.implementsOn_scalarData_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.implementsOn_scalarData_spec

/-- info: 'SparseLowerBounds.Hamiltonian.native_bound_of_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.native_bound_of_cost

/-- info: 'SparseLowerBounds.Hamiltonian.time_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.time_native

/-- info: 'SparseLowerBounds.Hamiltonian.time_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.time_spec

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_native

/-- info: 'SparseLowerBounds.Hamiltonian.mixed_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.mixed_spec

/-- info: 'SparseLowerBounds.Hamiltonian.precision_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precision_native

/-- info: 'SparseLowerBounds.Hamiltonian.precision_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.precision_spec

/-! ### Helper: Boolean phase-oracle access certificates for any hidden input (`Helpers/HsRelease/PhaseAccess`) -/

/-- info: 'SparseLowerBounds.Hamiltonian.HsRelease.phase_spectate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsRelease.phase_spectate

/-- info: 'SparseLowerBounds.Hamiltonian.HsRelease.PhaseAccess.implementsOn_oneHot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsRelease.PhaseAccess.implementsOn_oneHot

/-- info: 'SparseLowerBounds.Hamiltonian.HsRelease.PhaseAccess.implementsOn_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLowerBounds.Hamiltonian.HsRelease.PhaseAccess.implementsOn_bit
