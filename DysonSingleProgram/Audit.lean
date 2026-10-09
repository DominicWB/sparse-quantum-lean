import DysonSingleProgram.Statements

set_option autoImplicit false

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem of the single heralded
program for the Dyson solver (93 theorems) and every `Prop`-valued field of the structures
`GroverShape` and `Parallel.Stage.Good` (10 fields), 103 audits in module order. Every report
lists `propext`, `Classical.choice` and `Quot.sound`. -/

/-! ### Amplitude-amplification trial families (`DysonSingleProgram.Shape`) -/

/-- info: 'DysonSingleProgram.GroverShape.unitary₁' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.GroverShape.unitary₁

/-- info: 'DysonSingleProgram.GroverShape.unitary₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.GroverShape.unitary₂

/-- info: 'DysonSingleProgram.GroverShape.unitary₃' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.GroverShape.unitary₃

/-- info: 'DysonSingleProgram.GroverShape.eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.GroverShape.eval_eq

/-- info: 'DysonSingleProgram.GroverShape.cost_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.GroverShape.cost_eq

/-- info: 'DysonSingleProgram.GroverShape.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.GroverShape.map

/-! ### Spectator registers (`DysonSingleProgram.Register.Fiber`) -/

/-- info: 'DysonSingleProgram.Register.eval_spectate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Register.eval_spectate

/-- info: 'DysonSingleProgram.Register.cost_spectate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Register.cost_spectate

/-- info: 'DysonSingleProgram.Register.count_spectate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Register.count_spectate

/-- info: 'DysonSingleProgram.Register.labelCount_spectate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Register.labelCount_spectate

/-- info: 'DysonSingleProgram.Register.eval_reflatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Register.eval_reflatten

/-- info: 'DysonSingleProgram.Register.count_reflatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Register.count_reflatten

/-- info: 'DysonSingleProgram.Register.labelCount_reflatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Register.labelCount_reflatten

/-- info: 'DysonSingleProgram.Register.access_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Register.access_prod

/-- info: 'DysonSingleProgram.Register.eval_toAccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Register.eval_toAccess

/-- info: 'DysonSingleProgram.Register.count_toAccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Register.count_toAccess

/-- info: 'DysonSingleProgram.Register.labelCount_toAccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Register.labelCount_toAccess

/-! ### The compiled amplified trials (`DysonSingleProgram.Explicit.Compile`) -/

/-- info: 'DysonSingleProgram.Explicit.eval_compile_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Explicit.eval_compile_adjoint

/-- info: 'DysonSingleProgram.Explicit.groverShape_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Explicit.groverShape_compile

/-! ### One attempt with a coherent cutoff register (`DysonSingleProgram.Coherent`) -/

/-- info: 'DysonSingleProgram.Coherent.ctrl_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Coherent.ctrl_unitary

/-- info: 'DysonSingleProgram.Coherent.ctrl_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Coherent.ctrl_apply

/-- info: 'DysonSingleProgram.Coherent.steps_eval_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Coherent.steps_eval_apply

/-- info: 'DysonSingleProgram.Coherent.trial_eval_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Coherent.trial_eval_apply

/-- info: 'DysonSingleProgram.Coherent.count_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Coherent.count_steps

/-- info: 'DysonSingleProgram.Coherent.labelCount_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Coherent.labelCount_steps

/-- info: 'DysonSingleProgram.Coherent.count_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Coherent.count_trial

/-- info: 'DysonSingleProgram.Coherent.labelCount_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Coherent.labelCount_trial

/-- info: 'DysonSingleProgram.Coherent.norm_labelSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Coherent.norm_labelSeed

/-- info: 'DysonSingleProgram.Coherent.trial_eval_labelSeed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Coherent.trial_eval_labelSeed

/-! ### Parking an attempt register (`DysonSingleProgram.Parallel.Swap`) -/

/-- info: 'DysonSingleProgram.Parallel.coordV_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.coordV_apply

/-- info: 'DysonSingleProgram.Parallel.coordV_basisV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.coordV_basisV

/-- info: 'DysonSingleProgram.Parallel.inner_basisV_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.inner_basisV_left

/-- info: 'DysonSingleProgram.Parallel.sum_coordV_smul_basisV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.sum_coordV_smul_basisV

/-- info: 'DysonSingleProgram.Parallel.swapMain_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.swapMain_apply

/-- info: 'DysonSingleProgram.Parallel.swapMain_swapMain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.swapMain_swapMain

/-- info: 'DysonSingleProgram.Parallel.inner_basisV_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.inner_basisV_right

/-- info: 'DysonSingleProgram.Parallel.inner_swapMain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.inner_swapMain

/-- info: 'DysonSingleProgram.Parallel.swapMain_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.swapMain_unitary

/-- info: 'DysonSingleProgram.Parallel.swapMain_tens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.swapMain_tens

/-! ### Lemma `odel:lem:dyson` with the amplification shape (`DysonSingleProgram.Explicit.Dyson`) -/

/-- info: 'DysonSingleProgram.Explicit.dyson_grover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Explicit.dyson_grover

/-- info: 'DysonSingleProgram.Explicit.bound_le_dysonBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Explicit.bound_le_dysonBound

/-- info: 'DysonSingleProgram.Explicit.outcome_of_groverOutcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Explicit.outcome_of_groverOutcome

/-- info: 'DysonSingleProgram.Explicit.dyson_of_grover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Explicit.dyson_of_grover

/-! ### The Dyson trials on the ODE lower-bound class (`DysonSingleProgram.Explicit.Family`) -/

/-- info: 'DysonSingleProgram.Explicit.sourceFree_grover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Explicit.sourceFree_grover

/-- info: 'DysonSingleProgram.Explicit.family_dyson_grover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Explicit.family_dyson_grover

/-- info: 'DysonSingleProgram.Explicit.family_dyson_of_grover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Explicit.family_dyson_of_grover

/-! ### Attempts on separate registers (`DysonSingleProgram.Parallel.Stage`) -/

/-- info: 'DysonSingleProgram.Parallel.Stage.count_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.Stage.count_step

/-- info: 'DysonSingleProgram.Parallel.Stage.labelCount_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.Stage.labelCount_step

/-- info: 'DysonSingleProgram.Parallel.Stage.eval_step_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.Stage.eval_step_seed

/-! ### The first-success herald and readout (`DysonSingleProgram.Parallel.ReadoutSupport`) -/

/-- info: 'DysonSingleProgram.Parallel.coordLift_sub_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.coordLift_sub_apply

/-- info: 'DysonSingleProgram.Parallel.coordLift_one_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.coordLift_one_apply

/-- info: 'DysonSingleProgram.Parallel.coordLift_zero_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.coordLift_zero_apply

/-- info: 'DysonSingleProgram.Parallel.inner_coordLift_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.inner_coordLift_symm

/-- info: 'DysonSingleProgram.Parallel.inner_fiber_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.inner_fiber_fiber

/-- info: 'DysonSingleProgram.Parallel.inner_fiber_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.inner_fiber_symm

/-- info: 'DysonSingleProgram.Parallel.apply_eq_sum_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.apply_eq_sum_single

/-- info: 'DysonSingleProgram.Parallel.liftObs_apply_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.liftObs_apply_apply

/-- info: 'DysonSingleProgram.Parallel.succRead_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.succRead_apply

/-- info: 'DysonSingleProgram.Parallel.failRead_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.failRead_eq

/-- info: 'DysonSingleProgram.Parallel.failRead_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.failRead_apply

/-- info: 'DysonSingleProgram.Parallel.outStep_apply_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.outStep_apply_inl

/-- info: 'DysonSingleProgram.Parallel.outStep_apply_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.outStep_apply_inr

/-- info: 'DysonSingleProgram.Parallel.liftObs_one_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.liftObs_one_apply

/-- info: 'DysonSingleProgram.Parallel.liftObs_succRead_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.liftObs_succRead_apply

/-- info: 'DysonSingleProgram.Parallel.inner_succRead_liftObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.inner_succRead_liftObs

/-- info: 'DysonSingleProgram.Parallel.liftObs_failRead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.liftObs_failRead

/-- info: 'DysonSingleProgram.Parallel.inner_failRead' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.inner_failRead

/-- info: 'DysonSingleProgram.Parallel.inner_failRead_liftObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.inner_failRead_liftObs

/-- info: 'DysonSingleProgram.Parallel.inner_outStep_liftObs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.inner_outStep_liftObs

/-- info: 'DysonSingleProgram.Parallel.outObs_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.outObs_one

/-- info: 'DysonSingleProgram.Parallel.norm_outStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.norm_outStep

/-- info: 'DysonSingleProgram.Parallel.isStarProjection_heraldStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.isStarProjection_heraldStep

/-! ### Stages reproducing the released retry protocols (`DysonSingleProgram.Parallel.Readout`) -/

/-- info: 'DysonSingleProgram.Parallel.Stage.Good.weight_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.Stage.Good.weight_norm

/-- info: 'DysonSingleProgram.Parallel.Stage.Good.herald_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.Stage.Good.herald_proj

/-- info: 'DysonSingleProgram.Parallel.Stage.Good.out_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.Stage.Good.out_isometry

/-- info: 'DysonSingleProgram.Parallel.Stage.Good.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.Stage.Good.success

/-- info: 'DysonSingleProgram.Parallel.Stage.Good.corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.Stage.Good.corr

/-- info: 'DysonSingleProgram.Parallel.Stage.norm_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.Stage.norm_seed

/-- info: 'DysonSingleProgram.Parallel.Stage.good_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.Stage.good_base

/-- info: 'DysonSingleProgram.Parallel.Stage.good_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.Stage.good_step

/-! ### Four attempts in one program (`DysonSingleProgram.Parallel.Four`) -/

/-- info: 'DysonSingleProgram.Parallel.Stage.count_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.Stage.count_four

/-- info: 'DysonSingleProgram.Parallel.Stage.labelCount_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.Stage.labelCount_four

/-- info: 'DysonSingleProgram.Parallel.Stage.good_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.Stage.good_four

/-! ### Heralded accuracy of the single program (`DysonSingleProgram.Accuracy`) -/

/-- info: 'DysonSingleProgram.outObs_endpointReadout_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.outObs_endpointReadout_one

/-- info: 'DysonSingleProgram.certificate_observable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.certificate_observable

/-- info: 'DysonSingleProgram.heraldedAccurate_of_corr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.heraldedAccurate_of_corr

/-! ### A single heralded program from an amplified trial family (`DysonSingleProgram.Solver`) -/

/-- info: 'DysonSingleProgram.adjoint_comp_isometryEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.adjoint_comp_isometryEquiv_apply

/-- info: 'DysonSingleProgram.outObs_comp_isometryEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.outObs_comp_isometryEquiv_apply

/-- info: 'DysonSingleProgram.comp_isometryEquiv_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.comp_isometryEquiv_isometry

/-- info: 'DysonSingleProgram.heraldedAccurate_isometryEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.heraldedAccurate_isometryEquiv

/-- info: 'DysonSingleProgram.isStarProjection_conj_isometryEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.isStarProjection_conj_isometryEquiv

/-- info: 'DysonSingleProgram.Parallel.Stage.eval_toAccessProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.Stage.eval_toAccessProg

/-- info: 'DysonSingleProgram.Parallel.Stage.count_toAccessProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.Parallel.Stage.count_toAccessProg

/-- info: 'DysonSingleProgram.exists_solver_of_stage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.exists_solver_of_stage

/-- info: 'DysonSingleProgram.exists_solver_of_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.exists_solver_of_good

/-- info: 'DysonSingleProgram.exists_solver_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.exists_solver_of_shape

/-! ### Lemma `odel:lem:dyson` for single heralded programs (`DysonSingleProgram.Theorem`) -/

/-- info: 'DysonSingleProgram.exists_solver_of_isEmpty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.exists_solver_of_isEmpty

/-- info: 'DysonSingleProgram.solver_dyson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.solver_dyson

/-- info: 'DysonSingleProgram.solver_dyson_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.solver_dyson_joint

/-! ### Eq. `odel:eq:fixed` and its consequence for single programs (`DysonSingleProgram.Fixed`) -/

/-- info: 'DysonSingleProgram.solver_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.solver_fixed

/-- info: 'DysonSingleProgram.no_uniform_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.no_uniform_lower_bound

/-- info: 'DysonSingleProgram.no_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.no_witnesses

/-- info: 'DysonSingleProgram.no_tree_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonSingleProgram.no_tree_witnesses
