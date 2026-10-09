import ChebyshevLinearSystem.Main

set_option autoImplicit false

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`. The audits cover every theorem of the
library of Theorem `qls:thm:main` with the positive Chebyshev filter, beginning with the
endpoints `main` and `main_exists`.
-/

/-! ### Theorem `qls:thm:main` with the positive Chebyshev filter -/

/-- info: 'ChebyshevLinearSystem.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.main

/-- info: 'ChebyshevLinearSystem.main_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.main_exists

/-- info: 'ChebyshevLinearSystem.test_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.test_bounds

/-- info: 'ChebyshevLinearSystem.final_good_arith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.final_good_arith

/-- info: 'ChebyshevLinearSystem.finalLeaf_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.finalLeaf_good

/-- info: 'ChebyshevLinearSystem.correctness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.correctness

/-- info: 'ChebyshevLinearSystem.log_two_hundred_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.log_two_hundred_le

/-- info: 'ChebyshevLinearSystem.log_two_thousand_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.log_two_thousand_le

/-- info: 'ChebyshevLinearSystem.dTest_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.dTest_le

/-- info: 'ChebyshevLinearSystem.dFin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.dFin_le

/-- info: 'ChebyshevLinearSystem.walkStepsC_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.walkStepsC_le

/-- info: 'ChebyshevLinearSystem.finalLeaf_worstCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.finalLeaf_worstCost

/-- info: 'ChebyshevLinearSystem.algorithm_worstCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.algorithm_worstCost

/-- info: 'ChebyshevLinearSystem.algorithm_matrix_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.algorithm_matrix_queries

/-- info: 'ChebyshevLinearSystem.algorithm_source_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.algorithm_source_queries

/-! ### Lemma `qls:lem:signedwalk` for the released walk -/

/-- info: 'ChebyshevLinearSystem.signedLog_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.signedLog_unitary

/-- info: 'ChebyshevLinearSystem.parO_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parO_unitary

/-- info: 'ChebyshevLinearSystem.reflectionO_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.reflectionO_unitary

/-- info: 'ChebyshevLinearSystem.flipO_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.flipO_unitary

/-- info: 'ChebyshevLinearSystem.flipGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.flipGate_unitary

/-- info: 'ChebyshevLinearSystem.signed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.signed_eq

/-- info: 'ChebyshevLinearSystem.signedStepProg_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.signedStepProg_intertwines

/-- info: 'ChebyshevLinearSystem.signedStepProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.signedStepProg_cost

/-- info: 'ChebyshevLinearSystem.signedStepProg_cost_mat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.signedStepProg_cost_mat

/-- info: 'ChebyshevLinearSystem.signedStepProg_cost_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.signedStepProg_cost_src

/-- info: 'ChebyshevLinearSystem.signed_walk_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.signed_walk_step

/-! ### The chiral symmetry of the walk -/

/-- info: 'ChebyshevLinearSystem.cayley_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.cayley_neg

/-- info: 'ChebyshevLinearSystem.cayley_chiral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.cayley_chiral

/-- info: 'ChebyshevLinearSystem.walk_reverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.walk_reverse

/-- info: 'ChebyshevLinearSystem.parOr_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parOr_inl

/-- info: 'ChebyshevLinearSystem.parOr_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parOr_inr

/-- info: 'ChebyshevLinearSystem.parOr_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parOr_adjoint

/-- info: 'ChebyshevLinearSystem.parOr_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parOr_mul_self

/-- info: 'ChebyshevLinearSystem.parOr_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parOr_block

/-- info: 'ChebyshevLinearSystem.parOr_entryGenerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parOr_entryGenerator

/-- info: 'ChebyshevLinearSystem.smul_anti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.smul_anti

/-- info: 'ChebyshevLinearSystem.parOr_generator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parOr_generator

/-- info: 'ChebyshevLinearSystem.neg_blockMap_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.neg_blockMap_diag

/-- info: 'ChebyshevLinearSystem.par_offDiag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.par_offDiag

/-- info: 'ChebyshevLinearSystem.neg_wdiagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.neg_wdiagonal

/-- info: 'ChebyshevLinearSystem.blockMap_anti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.blockMap_anti

/-- info: 'ChebyshevLinearSystem.wdiag_anti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.wdiag_anti

/-- info: 'ChebyshevLinearSystem.four_anti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.four_anti

/-- info: 'ChebyshevLinearSystem.parP0_K0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parP0_K0

/-- info: 'ChebyshevLinearSystem.parPub_T1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parPub_T1

/-- info: 'ChebyshevLinearSystem.parPub_T2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parPub_T2

/-- info: 'ChebyshevLinearSystem.parPriv_Kw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parPriv_Kw

/-- info: 'ChebyshevLinearSystem.parOr_diag_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parOr_diag_adjoint

/-- info: 'ChebyshevLinearSystem.parP0_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parP0_adjoint

/-- info: 'ChebyshevLinearSystem.parPub_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parPub_adjoint

/-- info: 'ChebyshevLinearSystem.parPriv_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parPriv_adjoint

/-- info: 'ChebyshevLinearSystem.parP0_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parP0_mul_self

/-- info: 'ChebyshevLinearSystem.parPub_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parPub_mul_self

/-- info: 'ChebyshevLinearSystem.parPriv_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parPriv_mul_self

/-- info: 'ChebyshevLinearSystem.parO_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parO_adjoint

/-- info: 'ChebyshevLinearSystem.parO_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parO_mul_self

/-- info: 'ChebyshevLinearSystem.parO_Kw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.parO_Kw

/-- info: 'ChebyshevLinearSystem.KwO_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.KwO_selfAdjoint

/-- info: 'ChebyshevLinearSystem.WwO_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.WwO_walk

/-- info: 'ChebyshevLinearSystem.flip_WwO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.flip_WwO

/-! ### The LCU circuit on the counter register and the runs -/

/-- info: 'ChebyshevLinearSystem.sum_powT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.sum_powT

/-- info: 'ChebyshevLinearSystem.sum_powT_of_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.sum_powT_of_support

/-- info: 'ChebyshevLinearSystem.sum_filterCoeff_powT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.sum_filterCoeff_powT

/-- info: 'ChebyshevLinearSystem.dirOp_comp_wpow_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.dirOp_comp_wpow_pow

/-- info: 'ChebyshevLinearSystem.signedStepsT_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.signedStepsT_eq

/-- info: 'ChebyshevLinearSystem.seedT_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.seedT_isometry

/-- info: 'ChebyshevLinearSystem.lcuT_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.lcuT_compression

/-- info: 'ChebyshevLinearSystem.seedT_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.seedT_two_mul

/-- info: 'ChebyshevLinearSystem.signedStepsT_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.signedStepsT_two_mul

/-- info: 'ChebyshevLinearSystem.lcuT_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.lcuT_apply

/-- info: 'ChebyshevLinearSystem.runLog_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.runLog_eval

/-- info: 'ChebyshevLinearSystem.runLog_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.runLog_count

/-- info: 'ChebyshevLinearSystem.runPhys_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.runPhys_intertwines

/-- info: 'ChebyshevLinearSystem.runPhys_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.runPhys_unitary

/-- info: 'ChebyshevLinearSystem.runPhys_cost_mat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.runPhys_cost_mat

/-- info: 'ChebyshevLinearSystem.runPhys_cost_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.runPhys_cost_src

/-- info: 'ChebyshevLinearSystem.seedT_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.seedT_norm

/-- info: 'ChebyshevLinearSystem.seedVec_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.seedVec_norm

/-- info: 'ChebyshevLinearSystem.testFlag_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.testFlag_isometry

/-- info: 'ChebyshevLinearSystem.finalOutput_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.finalOutput_isometry

/-- info: 'ChebyshevLinearSystem.run_success_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.run_success_block

/-- info: 'ChebyshevLinearSystem.chebyshev_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.chebyshev_run

/-- info: 'ChebyshevLinearSystem.test_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.test_amplitude

/-- info: 'ChebyshevLinearSystem.final_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.final_amplitude

/-! ### The protocol -/

/-- info: 'ChebyshevLinearSystem.test_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.test_fits

/-- info: 'ChebyshevLinearSystem.final_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.final_fits

/-- info: 'ChebyshevLinearSystem.bLow_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.bLow_mem

/-- info: 'ChebyshevLinearSystem.augmented_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.augmented_run

/-- info: 'ChebyshevLinearSystem.testRun_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.testRun_unitary

/-- info: 'ChebyshevLinearSystem.testRun_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.testRun_probability

/-- info: 'ChebyshevLinearSystem.finalCircuit_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.finalCircuit_unitary

/-- info: 'ChebyshevLinearSystem.finalAmp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.finalAmp_eq

/-- info: 'ChebyshevLinearSystem.finalLeaf_successMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.finalLeaf_successMass

/-- info: 'ChebyshevLinearSystem.finalLeaf_leafDir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.finalLeaf_leafDir

/-- info: 'ChebyshevLinearSystem.finalLeaf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.finalLeaf_spec

/-- info: 'ChebyshevLinearSystem.finalAmp_norm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ChebyshevLinearSystem.finalAmp_norm_sq_le
