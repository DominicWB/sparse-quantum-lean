import AdaptiveHamiltonianLowerBound.Theorem

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. Every report lists `propext`, `Classical.choice`
and `Quot.sound`, except for 2 lemmas, whose reports list a subset of these three axioms
(or none). The audits cover every theorem of the adaptive Hamiltonian-simulation
lower-bound library, beginning with Theorem `hsl:thm:main` for adaptive algorithms and
its non-adaptive special cases.
-/

/-! ### Theorem `hsl:thm:main` for adaptive algorithms and non-adaptive special cases -/

/-- info: 'AdaptiveHamiltonianLowerBound.main_max_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.main_max_tree

/-- info: 'AdaptiveHamiltonianLowerBound.main_exists_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.main_exists_tree

/-- info: 'AdaptiveHamiltonianLowerBound.main_max_programs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.main_max_programs

/-- info: 'AdaptiveHamiltonianLowerBound.cost_valueWeight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.cost_valueWeight

/-- info: 'AdaptiveHamiltonianLowerBound.main_max_spec_programs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.main_max_spec_programs

/-! ### The three hard families -/

/-- info: 'AdaptiveHamiltonianLowerBound.abs_parSign_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.abs_parSign_le

/-- info: 'AdaptiveHamiltonianLowerBound.even_two_pow_hsMu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.even_two_pow_hsMu

/-- info: 'AdaptiveHamiltonianLowerBound.cast_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.cast_two_pow

/-- info: 'AdaptiveHamiltonianLowerBound.time_tree_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.time_tree_general

/-- info: 'AdaptiveHamiltonianLowerBound.mixed_tree_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.mixed_tree_general

/-- info: 'AdaptiveHamiltonianLowerBound.precision_tree_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.precision_tree_general

/-- info: 'AdaptiveHamiltonianLowerBound.time_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.time_tree

/-- info: 'AdaptiveHamiltonianLowerBound.mixed_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.mixed_tree

/-- info: 'AdaptiveHamiltonianLowerBound.precision_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.precision_tree

/-! ### Cost bounds from a uniform parity correlation -/

/-- info: 'AdaptiveHamiltonianLowerBound.searchGrowth_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.searchGrowth_admissible

/-- info: 'AdaptiveHamiltonianLowerBound.search_tree_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.search_tree_cost

/-- info: 'AdaptiveHamiltonianLowerBound.search_tree_cost_worst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.search_tree_cost_worst

/-- info: 'AdaptiveHamiltonianLowerBound.precision_tree_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.precision_tree_cost

/-! ### Accuracy, heralded correlation and signs -/

/-- info: 'AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff

/-- info: 'AdaptiveHamiltonianLowerBound.outObs_contraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.outObs_contraction

/-- info: 'AdaptiveHamiltonianLowerBound.tree_bias_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.tree_bias_general

/-- info: 'AdaptiveHamiltonianLowerBound.tree_correlation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.tree_correlation

/-- info: 'AdaptiveHamiltonianLowerBound.parity_eq_parSign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.parity_eq_parSign

/-- info: 'AdaptiveHamiltonianLowerBound.bitParity_toBits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.bitParity_toBits

/-! ### Admissible labels and the hard data -/

/-- info: 'AdaptiveHamiltonianLowerBound.Access.bitTable_value_bit' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.bitTable_value_bit

/-- info: 'AdaptiveHamiltonianLowerBound.Access.hardAccess_searchData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.hardAccess_searchData

/-- info: 'AdaptiveHamiltonianLowerBound.Access.hardAccess_timeData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.hardAccess_timeData

/-- info: 'AdaptiveHamiltonianLowerBound.Access.hardAccess_mixedMainData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.hardAccess_mixedMainData

/-- info: 'AdaptiveHamiltonianLowerBound.Access.hardAccess_scalarData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.hardAccess_scalarData

/-- info: 'AdaptiveHamiltonianLowerBound.Access.hardAccess_precisionMainData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.hardAccess_precisionMainData

/-- info: 'AdaptiveHamiltonianLowerBound.Access.valueWeight_eq' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.valueWeight_eq

/-- info: 'AdaptiveHamiltonianLowerBound.Access.admissible_oracles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.admissible_oracles

/-- info: 'AdaptiveHamiltonianLowerBound.Access.admissible_specOracles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.admissible_specOracles

/-- info: 'AdaptiveHamiltonianLowerBound.Access.callOp_eq_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.callOp_eq_native

/-- info: 'AdaptiveHamiltonianLowerBound.Access.admissible_iff_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.admissible_iff_native

/-- info: 'AdaptiveHamiltonianLowerBound.Access.callOp_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.callOp_unitary

/-- info: 'AdaptiveHamiltonianLowerBound.Access.callOp_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.callOp_star

/-- info: 'AdaptiveHamiltonianLowerBound.Access.admissible_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.admissible_unitary

/-- info: 'AdaptiveHamiltonianLowerBound.Access.wgrowth_const_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.wgrowth_const_of_eq

/-- info: 'AdaptiveHamiltonianLowerBound.Access.one_le_searchLam_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.one_le_searchLam_sq

/-- info: 'AdaptiveHamiltonianLowerBound.Access.wgrowth_transl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.wgrowth_transl

/-- info: 'AdaptiveHamiltonianLowerBound.Access.wgrowth_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.wgrowth_slots

/-- info: 'AdaptiveHamiltonianLowerBound.Access.wgrowth_lookup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.wgrowth_lookup

/-- info: 'AdaptiveHamiltonianLowerBound.Access.wgrowth_lookup_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.wgrowth_lookup_star

/-- info: 'AdaptiveHamiltonianLowerBound.Access.wgrowth_oracles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.wgrowth_oracles

/-- info: 'AdaptiveHamiltonianLowerBound.Access.wgrowth_callOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.wgrowth_callOp

/-- info: 'AdaptiveHamiltonianLowerBound.Access.wgrowth_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Access.wgrowth_admissible

/-! ### The search weight -/

/-- info: 'AdaptiveHamiltonianLowerBound.one_le_searchLam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.one_le_searchLam

/-- info: 'AdaptiveHamiltonianLowerBound.searchLam_le_twelve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.searchLam_le_twelve

/-- info: 'AdaptiveHamiltonianLowerBound.searchLam_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.searchLam_two_le

/-- info: 'AdaptiveHamiltonianLowerBound.parityMat_eq_parityZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.parityMat_eq_parityZ

/-- info: 'AdaptiveHamiltonianLowerBound.norm_conj_reflect_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.norm_conj_reflect_sub_le

/-- info: 'AdaptiveHamiltonianLowerBound.joint_add_fam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.joint_add_fam

/-- info: 'AdaptiveHamiltonianLowerBound.act_reflect_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.act_reflect_apply

/-- info: 'AdaptiveHamiltonianLowerBound.joint_bitOp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.joint_bitOp_eq

/-- info: 'AdaptiveHamiltonianLowerBound.norm_half_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.norm_half_sub_le

/-- info: 'AdaptiveHamiltonianLowerBound.norm_act_w_joint_bitOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.norm_act_w_joint_bitOp

/-- info: 'AdaptiveHamiltonianLowerBound.wgrowth_bit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wgrowth_bit

/-- info: 'AdaptiveHamiltonianLowerBound.search_tree_xor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.search_tree_xor

/-! ### Kernel potentials for any one-coordinate weight -/

/-- info: 'AdaptiveHamiltonianLowerBound.wgrowth_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wgrowth_const

/-- info: 'AdaptiveHamiltonianLowerBound.wgrowth_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wgrowth_mono

/-- info: 'AdaptiveHamiltonianLowerBound.wgrowth_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wgrowth_congr

/-- info: 'AdaptiveHamiltonianLowerBound.wgrowth_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wgrowth_mul

/-- info: 'AdaptiveHamiltonianLowerBound.wgrowth_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wgrowth_diagonal

/-- info: 'AdaptiveHamiltonianLowerBound.wgrowth_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wgrowth_conj

/-- info: 'AdaptiveHamiltonianLowerBound.wgrowth_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wgrowth_program

/-- info: 'AdaptiveHamiltonianLowerBound.wpot_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wpot_add

/-- info: 'AdaptiveHamiltonianLowerBound.wpot_hadamard_gram_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wpot_hadamard_gram_eq

/-- info: 'AdaptiveHamiltonianLowerBound.wpot_hadamard_gram_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wpot_hadamard_gram_nonneg

/-- info: 'AdaptiveHamiltonianLowerBound.wpot_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wpot_nonneg

/-- info: 'AdaptiveHamiltonianLowerBound.wpot_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wpot_growth

/-- info: 'AdaptiveHamiltonianLowerBound.wpot_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wpot_run

/-- info: 'AdaptiveHamiltonianLowerBound.wpot_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wpot_split

/-- info: 'AdaptiveHamiltonianLowerBound.wpot_onesKernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wpot_onesKernel

/-- info: 'AdaptiveHamiltonianLowerBound.norm_act_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.norm_act_le

/-- info: 'AdaptiveHamiltonianLowerBound.wparity_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wparity_bound

/-- info: 'AdaptiveHamiltonianLowerBound.wparity_kernel_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wparity_kernel_bound

/-- info: 'AdaptiveHamiltonianLowerBound.wprotocol_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wprotocol_bound

/-- info: 'AdaptiveHamiltonianLowerBound.wtree_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wtree_bound

/-- info: 'AdaptiveHamiltonianLowerBound.wtree_xor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.wtree_xor

/-! ### Programs as protocols and reindexing -/

/-- info: 'AdaptiveHamiltonianLowerBound.Single.worstCost_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Single.worstCost_tree

/-- info: 'AdaptiveHamiltonianLowerBound.Single.meanSuccess_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Single.meanSuccess_trial

/-- info: 'AdaptiveHamiltonianLowerBound.Single.successMass_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Single.successMass_tree

/-- info: 'AdaptiveHamiltonianLowerBound.Single.successDensity_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Single.successDensity_tree

/-- info: 'AdaptiveHamiltonianLowerBound.Single.conditionalDensity_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Single.conditionalDensity_tree

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.eval_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.eval_program

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.cost_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.cost_program

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.probability_testRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.probability_testRun

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.amplitude_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.amplitude_trial

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.probability_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.probability_trial

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.meanSuccess_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.meanSuccess_trial

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.oneTrialDensity_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.oneTrialDensity_trial

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.maxCost_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.maxCost_trial

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.failureMass_protocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.failureMass_protocol

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.successMass_protocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.successMass_protocol

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.successDensity_protocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.successDensity_protocol

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.worstCost_protocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.worstCost_protocol

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.expect_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.expect_tree

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.successMass_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.successMass_tree

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.successDensity_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.successDensity_tree

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.conditionalDensity_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.conditionalDensity_tree

/-- info: 'AdaptiveHamiltonianLowerBound.Reindex.worstCost_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveHamiltonianLowerBound.Reindex.worstCost_tree
