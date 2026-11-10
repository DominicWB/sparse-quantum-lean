import CleanWorkODE.Work
import CleanWorkODE.Registers
import CleanWorkODE.Oracles
import CleanWorkODE.Theorem

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (49 theorems), beginning
with the main theorems, then in module order. Every report lists exactly `propext`,
`Classical.choice` and `Quot.sound`. -/

/-! ### Final theorems: the general source interface with preparations on temporary work registers
and clean-input errors -/

/-- info: 'SparseHamiltonian.CleanWorkODE.work_approx_solver_nonneg_regular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.work_approx_solver_nonneg_regular

/-- info: 'SparseHamiltonian.CleanWorkODE.work_approx_solver_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.work_approx_solver_nonneg

/-- info: 'SparseHamiltonian.CleanWorkODE.work_approx_build' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.work_approx_build

/-- info: 'SparseHamiltonian.CleanWorkODE.actualOracleW_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.actualOracleW_clean

/-- info: 'SparseHamiltonian.CleanWorkODE.work_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.work_certificate

/-- info: 'SparseHamiltonian.CleanWorkODE.perturbed_four_work' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.perturbed_four_work

/-- info: 'SparseHamiltonian.CleanWorkODE.eval_workRecast_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.eval_workRecast_clean

/-- info: 'SparseHamiltonian.CleanWorkODE.liftAct_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.liftAct_clean

/-- info: 'SparseHamiltonian.CleanWorkODE.sourcePhysical_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.sourcePhysical_clean

/-- info: 'SparseHamiltonian.CleanWorkODE.CleanErr.adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.CleanErr.adjoint

/-! ### Clean-input errors of programs and the four-attempt protocol (`Work`) -/

/-- info: 'SparseHamiltonian.CleanWorkODE.CleanErr.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.CleanErr.mono

/-- info: 'SparseHamiltonian.CleanWorkODE.CleanErr.of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.CleanErr.of_comp

/-- info: 'SparseHamiltonian.CleanWorkODE.unitary_norm_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.unitary_norm_map

/-- info: 'SparseHamiltonian.CleanWorkODE.unitary_star_norm_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.unitary_star_norm_map

/-- info: 'SparseHamiltonian.CleanWorkODE.CleanErr.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.CleanErr.mul

/-- info: 'SparseHamiltonian.CleanWorkODE.WorkEmbedding.clean_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.WorkEmbedding.clean_norm

/-- info: 'SparseHamiltonian.CleanWorkODE.WorkEmbedding.clean_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.WorkEmbedding.clean_unit

/-- info: 'SparseHamiltonian.CleanWorkODE.WorkEmbedding.adjoint_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.WorkEmbedding.adjoint_clean

/-- info: 'SparseHamiltonian.CleanWorkODE.WorkEmbedding.output_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.WorkEmbedding.output_isometry

/-- info: 'SparseHamiltonian.CleanWorkODE.cost_workRecast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.cost_workRecast

/-! ### The work register and spectator registers (`Registers`) -/

/-- info: 'SparseHamiltonian.CleanWorkODE.workSplit_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.workSplit_apply

/-- info: 'SparseHamiltonian.CleanWorkODE.workSplit_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.workSplit_symm_apply

/-- info: 'SparseHamiltonian.CleanWorkODE.workSplit_cleanPi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.workSplit_cleanPi

/-- info: 'SparseHamiltonian.CleanWorkODE.cleanPi_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.cleanPi_apply

/-- info: 'SparseHamiltonian.CleanWorkODE.cleanPi_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.cleanPi_norm

/-- info: 'SparseHamiltonian.CleanWorkODE.cleanPi_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.cleanPi_isometry

/-- info: 'SparseHamiltonian.CleanWorkODE.liftPi_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.liftPi_unitary

/-- info: 'SparseHamiltonian.CleanWorkODE.workSplit_liftPi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.workSplit_liftPi

/-- info: 'SparseHamiltonian.CleanWorkODE.liftPi_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.liftPi_clean

/-- info: 'SparseHamiltonian.CleanWorkODE.piWork_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.piWork_clean

/-- info: 'SparseHamiltonian.CleanWorkODE.CleanErr.liftPi_of_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.CleanErr.liftPi_of_norm

/-- info: 'SparseHamiltonian.CleanWorkODE.transpose_cleanPi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.transpose_cleanPi

/-- info: 'SparseHamiltonian.CleanWorkODE.transpose_sourcePhysical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.transpose_sourcePhysical

/-- info: 'SparseHamiltonian.CleanWorkODE.actLayout_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.actLayout_apply

/-- info: 'SparseHamiltonian.CleanWorkODE.sliceLayout_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.sliceLayout_apply

/-- info: 'SparseHamiltonian.CleanWorkODE.liftAct_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.liftAct_unitary

/-- info: 'SparseHamiltonian.CleanWorkODE.actLayout_liftAct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.actLayout_liftAct

/-- info: 'SparseHamiltonian.CleanWorkODE.actLayout_cleanPi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.actLayout_cleanPi

/-- info: 'SparseHamiltonian.CleanWorkODE.ctrlL_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.ctrlL_unitary

/-- info: 'SparseHamiltonian.CleanWorkODE.ctrlL_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.ctrlL_apply

/-- info: 'SparseHamiltonian.CleanWorkODE.norm_ctrlL_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.norm_ctrlL_sub_le

/-- info: 'SparseHamiltonian.CleanWorkODE.slice_act' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.slice_act

/-- info: 'SparseHamiltonian.CleanWorkODE.slice_loader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.slice_loader

/-! ### The actual oracles with a work register (`Oracles`) -/

/-- info: 'SparseHamiltonian.CleanWorkODE.isUnitary_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.isUnitary_star

/-- info: 'SparseHamiltonian.CleanWorkODE.sourceOpW_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.sourceOpW_unitary

/-- info: 'SparseHamiltonian.CleanWorkODE.actualOracleW_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.actualOracleW_unitary

/-- info: 'SparseHamiltonian.CleanWorkODE.actualOracleW_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.actualOracleW_inl

/-- info: 'SparseHamiltonian.CleanWorkODE.actualOracleW_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.actualOracleW_inr

/-- info: 'SparseHamiltonian.CleanWorkODE.actualOracle_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.CleanWorkODE.actualOracle_inr
