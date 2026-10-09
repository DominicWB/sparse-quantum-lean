import DeferredMeasurementLowerBounds.Statements

set_option autoImplicit false

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem of the library for
measured algorithms with measurements inside a run (263 theorems) and every `Prop`-valued field
of the structures `Access.InverseConj`, `Deferral.Sched`, `Corollaries.MeasuredSolver` and
`Corollaries.MeasuredWitnesses` (10 fields), in module order. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 4 lemmas, `Deferral.Rec.fresh_succ`,
`Deferral.selWeight_liftLabel`, `Deferral.Sched.prod_ofFn_eq_single`, `Access.formSel_eq_some`,
whose reports list a subset of these three axioms. -/

/-! ### The measured model and the containment of adaptive protocols (`Model`) -/

/-! #### `DeferredMeasurementLowerBounds.Model.Measured` -/

/-- info: 'DeferredMeasurementLowerBounds.Model.queryOp_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.queryOp_unitary

/-- info: 'DeferredMeasurementLowerBounds.Model.Measured.successMass_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.Measured.successMass_nonneg

/-- info: 'DeferredMeasurementLowerBounds.Model.Measured.successDensity_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.Measured.successDensity_smul

/-- info: 'DeferredMeasurementLowerBounds.Model.Measured.successMass_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.Measured.successMass_smul

/-- info: 'DeferredMeasurementLowerBounds.Model.Measured.worstCost_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.Measured.worstCost_mono

/-- info: 'DeferredMeasurementLowerBounds.Model.worstCost_countWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.worstCost_countWeight_le

/-! #### `DeferredMeasurementLowerBounds.Helpers.TreeContainment.Steps` -/

/-- info: 'DeferredMeasurementLowerBounds.Model.finsetSup_add_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.finsetSup_add_const

/-- info: 'DeferredMeasurementLowerBounds.Model.successDensity_instrument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.successDensity_instrument

/-- info: 'DeferredMeasurementLowerBounds.Model.successMass_instrument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.successMass_instrument

/-- info: 'DeferredMeasurementLowerBounds.Model.worstCost_instrument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.worstCost_instrument

/-- info: 'DeferredMeasurementLowerBounds.Model.successDensity_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.successDensity_output

/-- info: 'DeferredMeasurementLowerBounds.Model.successMass_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.successMass_output

/-- info: 'DeferredMeasurementLowerBounds.Model.worstCost_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.worstCost_output

/-- info: 'DeferredMeasurementLowerBounds.Model.herald_norms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.herald_norms

/-- info: 'DeferredMeasurementLowerBounds.Model.norm_eval_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.norm_eval_seed

/-- info: 'DeferredMeasurementLowerBounds.Model.tree_successDensity_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.tree_successDensity_test

/-- info: 'DeferredMeasurementLowerBounds.Model.tree_successMass_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.tree_successMass_test

/-! #### `DeferredMeasurementLowerBounds.Model.Embed` -/

/-- info: 'DeferredMeasurementLowerBounds.Model.unitaryStep_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.unitaryStep_complete

/-- info: 'DeferredMeasurementLowerBounds.Model.resetKraus_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.resetKraus_complete

/-- info: 'DeferredMeasurementLowerBounds.Model.heraldKraus_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.heraldKraus_complete

/-- info: 'DeferredMeasurementLowerBounds.Model.coinKraus_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.coinKraus_complete

/-- info: 'DeferredMeasurementLowerBounds.Model.successDensity_ofProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.successDensity_ofProgram

/-- info: 'DeferredMeasurementLowerBounds.Model.successMass_ofProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.successMass_ofProgram

/-- info: 'DeferredMeasurementLowerBounds.Model.worstCost_ofProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.worstCost_ofProgram

/-- info: 'DeferredMeasurementLowerBounds.Model.successDensity_reset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.successDensity_reset

/-- info: 'DeferredMeasurementLowerBounds.Model.successMass_reset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.successMass_reset

/-- info: 'DeferredMeasurementLowerBounds.Model.worstCost_reset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.worstCost_reset

/-- info: 'DeferredMeasurementLowerBounds.Model.successDensity_herald' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.successDensity_herald

/-- info: 'DeferredMeasurementLowerBounds.Model.successMass_herald' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.successMass_herald

/-- info: 'DeferredMeasurementLowerBounds.Model.worstCost_herald' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.worstCost_herald

/-- info: 'DeferredMeasurementLowerBounds.Model.norm_sq_coinKraus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.norm_sq_coinKraus

/-- info: 'DeferredMeasurementLowerBounds.Model.successDensity_ofProtocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.successDensity_ofProtocol

/-- info: 'DeferredMeasurementLowerBounds.Model.successMass_ofProtocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.successMass_ofProtocol

/-- info: 'DeferredMeasurementLowerBounds.Model.worstCost_ofProtocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.worstCost_ofProtocol

/-- info: 'DeferredMeasurementLowerBounds.Model.successDensity_ofTree_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.successDensity_ofTree_smul

/-- info: 'DeferredMeasurementLowerBounds.Model.successMass_ofTree_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.successMass_ofTree_smul

/-- info: 'DeferredMeasurementLowerBounds.Model.successMass_ofTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.successMass_ofTree

/-- info: 'DeferredMeasurementLowerBounds.Model.successDensity_ofTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.successDensity_ofTree

/-- info: 'DeferredMeasurementLowerBounds.Model.conditionalDensity_ofTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.conditionalDensity_ofTree

/-- info: 'DeferredMeasurementLowerBounds.Model.worstCost_ofTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.worstCost_ofTree

/-- info: 'DeferredMeasurementLowerBounds.Model.exists_unit_of_successMass_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Model.exists_unit_of_successMass_pos

/-! ### Record registers and the deferral theorem (`Deferral`) -/

/-! #### `DeferredMeasurementLowerBounds.Deferral.Registers` -/

/-- info: 'DeferredMeasurementLowerBounds.Deferral.split_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.split_apply

/-- info: 'DeferredMeasurementLowerBounds.Deferral.adjoint_proj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.adjoint_proj_apply

/-- info: 'DeferredMeasurementLowerBounds.Deferral.proj_comp_adjoint_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.proj_comp_adjoint_proj

/-- info: 'DeferredMeasurementLowerBounds.Deferral.freshInj_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.freshInj_isometry

/-- info: 'DeferredMeasurementLowerBounds.Deferral.freshInj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.freshInj_apply

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Rec.fresh_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Rec.fresh_succ

/-- info: 'DeferredMeasurementLowerBounds.Deferral.split_freshInj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.split_freshInj

/-- info: 'DeferredMeasurementLowerBounds.Deferral.krausMap_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.krausMap_none

/-- info: 'DeferredMeasurementLowerBounds.Deferral.krausMap_some' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.krausMap_some

/-- info: 'DeferredMeasurementLowerBounds.Deferral.krausMap_some_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.krausMap_some_of_le

/-- info: 'DeferredMeasurementLowerBounds.Deferral.krausMap_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.krausMap_isometry

/-- info: 'DeferredMeasurementLowerBounds.Deferral.adjoint_halmosForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.adjoint_halmosForm

/-- info: 'DeferredMeasurementLowerBounds.Deferral.halmosForm_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.halmosForm_mul_self

/-- info: 'DeferredMeasurementLowerBounds.Deferral.halmos_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.halmos_unitary

/-- info: 'DeferredMeasurementLowerBounds.Deferral.halmos_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.halmos_fresh

/-- info: 'DeferredMeasurementLowerBounds.Deferral.fiber_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.fiber_complete

/-- info: 'DeferredMeasurementLowerBounds.Deferral.dilation_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.dilation_unitary

/-- info: 'DeferredMeasurementLowerBounds.Deferral.dilation_freshInj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.dilation_freshInj

/-! #### `DeferredMeasurementLowerBounds.Deferral.Selection` -/

/-- info: 'DeferredMeasurementLowerBounds.Deferral.callOpt_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.callOpt_unitary

/-- info: 'DeferredMeasurementLowerBounds.Deferral.masked_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.masked_eq_fiber

/-- info: 'DeferredMeasurementLowerBounds.Deferral.patOp_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.patOp_unitary

/-- info: 'DeferredMeasurementLowerBounds.Deferral.selFamily_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.selFamily_unitary

/-- info: 'DeferredMeasurementLowerBounds.Deferral.eval_seqAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.eval_seqAll

/-- info: 'DeferredMeasurementLowerBounds.Deferral.cost_seqAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.cost_seqAll

/-- info: 'DeferredMeasurementLowerBounds.Deferral.split_symm_coord' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.split_symm_coord

/-- info: 'DeferredMeasurementLowerBounds.Deferral.patOp_liftPat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.patOp_liftPat

/-- info: 'DeferredMeasurementLowerBounds.Deferral.selWeight_liftLabel' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.selWeight_liftLabel

/-- info: 'DeferredMeasurementLowerBounds.Deferral.selFamily_liftLabel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.selFamily_liftLabel

/-! #### `DeferredMeasurementLowerBounds.Deferral.Schedule` -/

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.seg_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.seg_free

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.cost_prog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.cost_prog

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.eval_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.eval_empty

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.eval_consSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.eval_consSlot

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.eval_prependFree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.eval_prependFree

/-! #### `DeferredMeasurementLowerBounds.Deferral.Align` -/

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.conj_masked_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.conj_masked_unitary

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.eval_liftProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.eval_liftProgram

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.cost_liftProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.cost_liftProgram

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.len_align' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.len_align

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.sect_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.sect_mul

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.prod_ofFn_eq_single' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.prod_ofFn_eq_single

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.conj_fiber_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.conj_fiber_apply

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.prod_conj_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.prod_conj_fiber

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.prod_ofFn_ite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.prod_ofFn_ite

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.eval_align_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.eval_align_seg

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.selFamily_alignSlot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.selFamily_alignSlot

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.padEval_eq_go' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.padEval_eq_go

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.padEval_eq_prog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.padEval_eq_prog

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.eval_align_go' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.eval_align_go

/-- info: 'DeferredMeasurementLowerBounds.Deferral.Sched.eval_align' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.Sched.eval_align

/-! #### `DeferredMeasurementLowerBounds.Deferral.Defer` -/

/-- info: 'DeferredMeasurementLowerBounds.Deferral.fiber_const_freshInj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.fiber_const_freshInj

/-- info: 'DeferredMeasurementLowerBounds.Deferral.patOp_const_freshInj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.patOp_const_freshInj

/-- info: 'DeferredMeasurementLowerBounds.Deferral.len_defer_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.len_defer_le

/-- info: 'DeferredMeasurementLowerBounds.Deferral.cost_defer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.cost_defer

/-- info: 'DeferredMeasurementLowerBounds.Deferral.eval_defer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.eval_defer

/-! #### `DeferredMeasurementLowerBounds.Deferral.Output` -/

/-- info: 'DeferredMeasurementLowerBounds.Deferral.deferOutput_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.deferOutput_apply

/-- info: 'DeferredMeasurementLowerBounds.Deferral.norm_leafOut' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.norm_leafOut

/-- info: 'DeferredMeasurementLowerBounds.Deferral.sum_outRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.sum_outRec

/-- info: 'DeferredMeasurementLowerBounds.Deferral.deferOutput_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.deferOutput_isometry

/-- info: 'DeferredMeasurementLowerBounds.Deferral.adjoint_deferOutput_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.adjoint_deferOutput_apply

/-- info: 'DeferredMeasurementLowerBounds.Deferral.leafAt_instrument_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.leafAt_instrument_cons

/-- info: 'DeferredMeasurementLowerBounds.Deferral.purify_instrument_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.purify_instrument_cons

/-- info: 'DeferredMeasurementLowerBounds.Deferral.recordTerm_instrument_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.recordTerm_instrument_cons

/-- info: 'DeferredMeasurementLowerBounds.Deferral.sum_fin_dite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.sum_fin_dite

/-- info: 'DeferredMeasurementLowerBounds.Deferral.sum_recordTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.sum_recordTerm

/-- info: 'DeferredMeasurementLowerBounds.Deferral.recordTerm_outRec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.recordTerm_outRec

/-- info: 'DeferredMeasurementLowerBounds.Deferral.recordTerm_of_isSome_eq_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.recordTerm_of_isSome_eq_false

/-- info: 'DeferredMeasurementLowerBounds.Deferral.sum_deferOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.sum_deferOutput

/-- info: 'DeferredMeasurementLowerBounds.Deferral.successDensity_eq_transcriptSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.successDensity_eq_transcriptSum

/-- info: 'DeferredMeasurementLowerBounds.Deferral.successMass_eq_transcriptSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.successMass_eq_transcriptSum

/-- info: 'DeferredMeasurementLowerBounds.Deferral.sum_pure_deferOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.sum_pure_deferOutput

/-- info: 'DeferredMeasurementLowerBounds.Deferral.norm_sq_deferOutput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.norm_sq_deferOutput

/-! #### `DeferredMeasurementLowerBounds.Deferral.Theorem` -/

/-- info: 'DeferredMeasurementLowerBounds.Deferral.norm_deferredSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.norm_deferredSeed

/-- info: 'DeferredMeasurementLowerBounds.Deferral.deferredOutput_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.deferredOutput_isometry

/-- info: 'DeferredMeasurementLowerBounds.Deferral.deferredProgram_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.deferredProgram_unitary

/-- info: 'DeferredMeasurementLowerBounds.Deferral.cost_deferredProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.cost_deferredProgram

/-- info: 'DeferredMeasurementLowerBounds.Deferral.sum_pure_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.sum_pure_amplitude

/-- info: 'DeferredMeasurementLowerBounds.Deferral.norm_sq_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.norm_sq_amplitude

/-- info: 'DeferredMeasurementLowerBounds.Deferral.deferral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.deferral

/-- info: 'DeferredMeasurementLowerBounds.Deferral.amplitude_deferredTrial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.amplitude_deferredTrial

/-- info: 'DeferredMeasurementLowerBounds.Deferral.meanSuccess_deferredTrial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.meanSuccess_deferredTrial

/-- info: 'DeferredMeasurementLowerBounds.Deferral.successMass_deferredTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.successMass_deferredTree

/-- info: 'DeferredMeasurementLowerBounds.Deferral.successDensity_deferredTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.successDensity_deferredTree

/-- info: 'DeferredMeasurementLowerBounds.Deferral.conditionalDensity_deferredTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.conditionalDensity_deferredTree

/-- info: 'DeferredMeasurementLowerBounds.Deferral.worstCost_deferredTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Deferral.worstCost_deferredTree

/-! ### Readouts with the record register in the garbage (`Readout`) -/

/-! #### `DeferredMeasurementLowerBounds.Readout.Density` -/

/-- info: 'DeferredMeasurementLowerBounds.Readout.liftReadout_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Readout.liftReadout_apply

/-- info: 'DeferredMeasurementLowerBounds.Readout.adjoint_comp_jointSwap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Readout.adjoint_comp_jointSwap

/-- info: 'DeferredMeasurementLowerBounds.Readout.liftReadout_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Readout.liftReadout_isometry

/-- info: 'DeferredMeasurementLowerBounds.Readout.trace_outObs_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Readout.trace_outObs_pure

/-- info: 'DeferredMeasurementLowerBounds.Readout.reducedDensity_liftReadout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Readout.reducedDensity_liftReadout

/-- info: 'DeferredMeasurementLowerBounds.Readout.trace_outObs_liftReadout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Readout.trace_outObs_liftReadout

/-- info: 'DeferredMeasurementLowerBounds.Readout.densityAccurate_liftReadout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Readout.densityAccurate_liftReadout

/-! #### `DeferredMeasurementLowerBounds.Readout.Trace` -/

/-- info: 'DeferredMeasurementLowerBounds.Readout.liftEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Readout.liftEquiv_apply

/-- info: 'DeferredMeasurementLowerBounds.Readout.conjStarAlgEquiv_pureOperator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Readout.conjStarAlgEquiv_pureOperator

/-- info: 'DeferredMeasurementLowerBounds.Readout.entry_smul_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Readout.entry_smul_pure

/-- info: 'DeferredMeasurementLowerBounds.Readout.entry_smul_sum_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Readout.entry_smul_sum_pure

/-- info: 'DeferredMeasurementLowerBounds.Readout.ptrace_liftEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Readout.ptrace_liftEquiv

/-! ### Access models: native, controlled, phase and sampled-time calls (`Access`) -/

/-! #### `DeferredMeasurementLowerBounds.Access.Native` -/

/-- info: 'DeferredMeasurementLowerBounds.Access.nativeCall_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.nativeCall_star

/-- info: 'DeferredMeasurementLowerBounds.Access.nativeCall_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.nativeCall_one

/-- info: 'DeferredMeasurementLowerBounds.Access.nativeCall_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.nativeCall_fiber

/-- info: 'DeferredMeasurementLowerBounds.Access.one_le_of_nativeCounted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.one_le_of_nativeCounted

/-- info: 'DeferredMeasurementLowerBounds.Access.nativeCall_of_nativeCounted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.nativeCall_of_nativeCounted

/-- info: 'DeferredMeasurementLowerBounds.Access.nativeCall_callOpt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.nativeCall_callOpt

/-- info: 'DeferredMeasurementLowerBounds.Access.admissible_selFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.admissible_selFamily

/-- info: 'DeferredMeasurementLowerBounds.Access.native_admissible_selFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.native_admissible_selFamily

/-! #### `DeferredMeasurementLowerBounds.Access.Control` -/

/-- info: 'DeferredMeasurementLowerBounds.Access.sectorFlip_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.sectorFlip_apply

/-- info: 'DeferredMeasurementLowerBounds.Access.sectorFlip_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.sectorFlip_unitary

/-- info: 'DeferredMeasurementLowerBounds.Access.masked_by_ctrl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.masked_by_ctrl

/-- info: 'DeferredMeasurementLowerBounds.Access.InverseConj.unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.InverseConj.unitary

/-- info: 'DeferredMeasurementLowerBounds.Access.InverseConj.star_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.InverseConj.star_eq

/-- info: 'DeferredMeasurementLowerBounds.Access.dirCount_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.dirCount_le_two

/-- info: 'DeferredMeasurementLowerBounds.Access.dirCount_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.dirCount_le_one

/-- info: 'DeferredMeasurementLowerBounds.Access.dirCount_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.dirCount_eq_zero

/-- info: 'DeferredMeasurementLowerBounds.Access.maskedUnitary_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.maskedUnitary_unitary

/-- info: 'DeferredMeasurementLowerBounds.Access.fiber_const_comp_activeEmbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.fiber_const_comp_activeEmbed

/-- info: 'DeferredMeasurementLowerBounds.Access.fixed_comp_activeEmbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.fixed_comp_activeEmbed

/-- info: 'DeferredMeasurementLowerBounds.Access.seq_comp_activeEmbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.seq_comp_activeEmbed

/-- info: 'DeferredMeasurementLowerBounds.Access.maskedCall_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.maskedCall_eval

/-- info: 'DeferredMeasurementLowerBounds.Access.optCall_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.optCall_eval

/-- info: 'DeferredMeasurementLowerBounds.Access.labelCircuit_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.labelCircuit_eval

/-- info: 'DeferredMeasurementLowerBounds.Access.seqAll_labelCircuit_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.seqAll_labelCircuit_eval

/-- info: 'DeferredMeasurementLowerBounds.Access.maskedCall_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.maskedCall_cost

/-- info: 'DeferredMeasurementLowerBounds.Access.labelCircuit_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.labelCircuit_cost

/-- info: 'DeferredMeasurementLowerBounds.Access.seqAll_labelCircuit_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.seqAll_labelCircuit_cost

/-- info: 'DeferredMeasurementLowerBounds.Access.selCircuit_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.selCircuit_eval

/-- info: 'DeferredMeasurementLowerBounds.Access.selCircuit_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.selCircuit_cost

/-- info: 'DeferredMeasurementLowerBounds.Access.selCircuit_cost_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.selCircuit_cost_single

/-! #### `DeferredMeasurementLowerBounds.Access.Transport` -/

/-- info: 'DeferredMeasurementLowerBounds.Access.amplitude_compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.amplitude_compiled

/-- info: 'DeferredMeasurementLowerBounds.Access.amplitude_compiledTrial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.amplitude_compiledTrial

/-- info: 'DeferredMeasurementLowerBounds.Access.meanSuccess_compiledTrial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.meanSuccess_compiledTrial

/-- info: 'DeferredMeasurementLowerBounds.Access.successMass_compiledTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.successMass_compiledTree

/-- info: 'DeferredMeasurementLowerBounds.Access.successDensity_compiledTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.successDensity_compiledTree

/-- info: 'DeferredMeasurementLowerBounds.Access.conditionalDensity_compiledTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.conditionalDensity_compiledTree

/-- info: 'DeferredMeasurementLowerBounds.Access.worstCost_compiledTree_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.worstCost_compiledTree_mul

/-- info: 'DeferredMeasurementLowerBounds.Access.worstCost_compiledTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.worstCost_compiledTree

/-! #### `DeferredMeasurementLowerBounds.Access.ControlTree` -/

/-- info: 'DeferredMeasurementLowerBounds.Access.ctrlCircuits_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.ctrlCircuits_eval

/-- info: 'DeferredMeasurementLowerBounds.Access.ctrlCircuits_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.ctrlCircuits_cost

/-- info: 'DeferredMeasurementLowerBounds.Access.ctrlCircuits_cost_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.ctrlCircuits_cost_conj

/-- info: 'DeferredMeasurementLowerBounds.Access.worstCost_ctrlTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.worstCost_ctrlTree

/-- info: 'DeferredMeasurementLowerBounds.Access.worstCost_ctrlTree_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.worstCost_ctrlTree_conj

/-- info: 'DeferredMeasurementLowerBounds.Access.ctrlCircuits_cost_le_card' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.ctrlCircuits_cost_le_card

/-- info: 'DeferredMeasurementLowerBounds.Access.worstCost_ctrlTreeOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.worstCost_ctrlTreeOf

/-! #### `DeferredMeasurementLowerBounds.Access.Phase` -/

/-- info: 'DeferredMeasurementLowerBounds.Access.phase_ctrlSpectate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.phase_ctrlSpectate

/-- info: 'DeferredMeasurementLowerBounds.Access.phaseCircuit_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.phaseCircuit_eval

/-- info: 'DeferredMeasurementLowerBounds.Access.phaseCircuit_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.phaseCircuit_count

/-- info: 'DeferredMeasurementLowerBounds.Access.phaseCircuit_count_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.phaseCircuit_count_none

/-- info: 'DeferredMeasurementLowerBounds.Access.phaseCircuits_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.phaseCircuits_eval

/-- info: 'DeferredMeasurementLowerBounds.Access.phaseCircuits_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.phaseCircuits_count

/-! #### `DeferredMeasurementLowerBounds.Helpers.OdeAccess.Calls` -/

/-- info: 'DeferredMeasurementLowerBounds.Access.callOpt_fiber_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.callOpt_fiber_apply

/-- info: 'DeferredMeasurementLowerBounds.Access.isoEquiv_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.isoEquiv_isometry

/-- info: 'DeferredMeasurementLowerBounds.Access.comp_three_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.comp_three_isometry

/-- info: 'DeferredMeasurementLowerBounds.Access.patOp_subtype' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.patOp_subtype

/-! #### `DeferredMeasurementLowerBounds.Access.TimeAccess` -/

/-- info: 'DeferredMeasurementLowerBounds.Access.access_eq_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.access_eq_conj

/-- info: 'DeferredMeasurementLowerBounds.Access.access_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.access_apply

/-- info: 'DeferredMeasurementLowerBounds.Access.star_access_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.star_access_apply

/-- info: 'DeferredMeasurementLowerBounds.Access.callOpt_access_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.callOpt_access_apply

/-- info: 'DeferredMeasurementLowerBounds.Access.negValue_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.negValue_unitary

/-- info: 'DeferredMeasurementLowerBounds.Access.star_access_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.star_access_value

/-- info: 'DeferredMeasurementLowerBounds.Access.plainEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.plainEquiv_apply

/-- info: 'DeferredMeasurementLowerBounds.Access.patOp_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.patOp_plain

/-- info: 'DeferredMeasurementLowerBounds.Access.callOpt_callFamily_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.callOpt_callFamily_apply

/-- info: 'DeferredMeasurementLowerBounds.Access.callEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.callEquiv_apply

/-- info: 'DeferredMeasurementLowerBounds.Access.patOp_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.patOp_call

/-! #### `DeferredMeasurementLowerBounds.Access.TimeCircuits` -/

/-- info: 'DeferredMeasurementLowerBounds.Access.targetEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.targetEquiv_apply

/-- info: 'DeferredMeasurementLowerBounds.Access.ctrlTarget_eq_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.ctrlTarget_eq_conj

/-- info: 'DeferredMeasurementLowerBounds.Access.plainEnc_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.plainEnc_isometry

/-- info: 'DeferredMeasurementLowerBounds.Access.callEnc_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.callEnc_isometry

/-- info: 'DeferredMeasurementLowerBounds.Access.plain_selFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.plain_selFamily

/-- info: 'DeferredMeasurementLowerBounds.Access.call_selFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.call_selFamily

/-- info: 'DeferredMeasurementLowerBounds.Access.eval_query_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.eval_query_target

/-- info: 'DeferredMeasurementLowerBounds.Access.plainCircuit_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.plainCircuit_eval

/-- info: 'DeferredMeasurementLowerBounds.Access.callCircuit_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.callCircuit_eval

/-- info: 'DeferredMeasurementLowerBounds.Access.formSel_eq_some' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.formSel_eq_some

/-- info: 'DeferredMeasurementLowerBounds.Access.selCircuit_cost_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.selCircuit_cost_value

/-- info: 'DeferredMeasurementLowerBounds.Access.plainCircuit_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.plainCircuit_cost

/-- info: 'DeferredMeasurementLowerBounds.Access.callCircuit_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Access.callCircuit_cost

/-! ### Theorems `hsl:thm:main` and `qlsl:thm:main` for measured algorithms -/

/-! #### `DeferredMeasurementLowerBounds.Corollaries.Hamiltonian` -/

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.worstCost_deferredTree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.worstCost_deferredTree_le

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.deferred_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.deferred_admissible

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.main_max_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.main_max_measured

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.main_exists_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.main_exists_measured

/-! #### `DeferredMeasurementLowerBounds.Corollaries.LinearSystem` -/

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.lower_bound_sharp_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.lower_bound_sharp_measured

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.lower_bound_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.lower_bound_measured

/-! ### Theorem `odel:thm:combined` for measured solvers -/

/-! #### `DeferredMeasurementLowerBounds.Corollaries.ODESolver` -/

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver.seed_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver.seed_unit

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver.readout_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver.readout_isometry

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver.success

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver.accurate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver.accurate

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.MeasuredWitnesses.inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.MeasuredWitnesses.inClass

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.MeasuredWitnesses.time_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.MeasuredWitnesses.time_eq

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.MeasuredWitnesses.forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.MeasuredWitnesses.forces

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.worstCost_plainTreeSolver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.worstCost_plainTreeSolver

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.worstCost_callTreeSolver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.worstCost_callTreeSolver

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.measuredForces_of_treeForces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.measuredForces_of_treeForces

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.measuredWitnesses_of_treeWitnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.measuredWitnesses_of_treeWitnesses

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.treeForces_of_measuredForces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.treeForces_of_measuredForces

/-! #### `DeferredMeasurementLowerBounds.Corollaries.ODE` -/

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.combined_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.combined_measured

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.combined_max_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.combined_max_measured

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.joint_witness_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.joint_witness_measured

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.precision_terms_witness_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.precision_terms_witness_measured

/-! ### The unitary lower half of Corollary `hs:cor:unitary` for measured algorithms -/

/-! #### `DeferredMeasurementLowerBounds.Helpers.SearchReadout.Overlap` -/

/-- info: 'DeferredMeasurementLowerBounds.SearchReadout.inner_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.SearchReadout.inner_isometry

/-- info: 'DeferredMeasurementLowerBounds.SearchReadout.inner_eq_isometry_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.SearchReadout.inner_eq_isometry_add

/-- info: 'DeferredMeasurementLowerBounds.SearchReadout.norm_sq_eq_isometry_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.SearchReadout.norm_sq_eq_isometry_add

/-- info: 'DeferredMeasurementLowerBounds.SearchReadout.inner_eq_proj_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.SearchReadout.inner_eq_proj_add

/-- info: 'DeferredMeasurementLowerBounds.SearchReadout.re_inner_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.SearchReadout.re_inner_proj

/-- info: 'DeferredMeasurementLowerBounds.SearchReadout.add_mul_le_sqrt_mul_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.SearchReadout.add_mul_le_sqrt_mul_sqrt

/-- info: 'DeferredMeasurementLowerBounds.SearchReadout.overlap_real_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.SearchReadout.overlap_real_le

/-- info: 'DeferredMeasurementLowerBounds.SearchReadout.norm_inner_le_of_reads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.SearchReadout.norm_inner_le_of_reads

/-- info: 'DeferredMeasurementLowerBounds.SearchReadout.sel_isStarProjection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.SearchReadout.sel_isStarProjection

/-- info: 'DeferredMeasurementLowerBounds.SearchReadout.norm_sq_sel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.SearchReadout.norm_sq_sel

/-- info: 'DeferredMeasurementLowerBounds.SearchReadout.norm_sq_sel_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.SearchReadout.norm_sq_sel_add_le

/-- info: 'DeferredMeasurementLowerBounds.SearchReadout.liftObs_pure_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.SearchReadout.liftObs_pure_single

/-- info: 'DeferredMeasurementLowerBounds.SearchReadout.liftObs_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.SearchReadout.liftObs_reflect

/-! #### `DeferredMeasurementLowerBounds.Corollaries.UnitaryReadout` -/

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.norm_sq_sel_liftReadout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.norm_sq_sel_liftReadout

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.corr_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.corr_reflect

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.corr_one_successDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.corr_one_successDensity

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.one_sub_le_readProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.one_sub_le_readProb

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.one_sub_le_readProb_of_accurate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.one_sub_le_readProb_of_accurate

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.readProb_successDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.readProb_successDensity

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.corr_one_conditionalDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.corr_one_conditionalDensity

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.le_readProb_of_heralded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.le_readProb_of_heralded

/-! #### `DeferredMeasurementLowerBounds.Corollaries.Unitary` -/

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.search_count_ge_measured_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.search_count_ge_measured_sharp

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.search_count_ge_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.search_count_ge_measured

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.search_count_ge_measured_heralded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.search_count_ge_measured_heralded

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.entry_count_ge_measured_heralded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.entry_count_ge_measured_heralded

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.entry_count_ge_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.entry_count_ge_measured

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.implementation_count_ge_measured_heralded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.implementation_count_ge_measured_heralded

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.implementation_count_ge_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.implementation_count_ge_measured

/-! ### Theorem `hsl:thm:main` for measured algorithms over the time-dependent access -/

/-! #### `DeferredMeasurementLowerBounds.Corollaries.TimeDependent` -/

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.main_max_measured_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.main_max_measured_access

/-- info: 'DeferredMeasurementLowerBounds.Corollaries.main_max_measured_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.Corollaries.main_max_measured_calls

/-! ### Non-vacuity of the deferral and of the measured lower bounds (`NonVacuity`) -/

/-! #### `DeferredMeasurementLowerBounds.NonVacuity` -/

/-- info: 'DeferredMeasurementLowerBounds.NonVacuity.midRunOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.NonVacuity.midRunOracle_unitary

/-- info: 'DeferredMeasurementLowerBounds.NonVacuity.midRun_worstCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.NonVacuity.midRun_worstCost

/-- info: 'DeferredMeasurementLowerBounds.NonVacuity.freshVec_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.NonVacuity.freshVec_unit

/-- info: 'DeferredMeasurementLowerBounds.NonVacuity.deferral_midRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.NonVacuity.deferral_midRun

/-- info: 'DeferredMeasurementLowerBounds.NonVacuity.released_linear_system_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.NonVacuity.released_linear_system_measured

/-- info: 'DeferredMeasurementLowerBounds.NonVacuity.released_unitary_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DeferredMeasurementLowerBounds.NonVacuity.released_unitary_measured
