import DysonGeneralAccess.Statements

set_option autoImplicit false

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem of the single heralded
program for the Dyson solver on its general access (31 theorems), every definition carrying
proof obligations (8 definitions: `Model.HeraldedSolver.mono`, `Model.HeraldedSolver.map`,
`Model.HeraldedSolver.trivial`, `Model.ofSolver`, `Model.toSolver`, `Assemble.ofStage`,
`Assemble.ofGood`, `Core.single`) and every `Prop`-valued field of the structure
`Model.HeraldedSolver` (5 fields), 44 audits in module order. Every report lists `propext`,
`Classical.choice` and `Quot.sound`. -/

/-! ### Single-program class over a general access (`DysonGeneralAccess.Model`) -/

/-- info: 'DysonGeneralAccess.Model.HeraldedSolver.seed_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Model.HeraldedSolver.seed_norm_le

/-- info: 'DysonGeneralAccess.Model.HeraldedSolver.out_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Model.HeraldedSolver.out_isometry

/-- info: 'DysonGeneralAccess.Model.HeraldedSolver.herald_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Model.HeraldedSolver.herald_proj

/-- info: 'DysonGeneralAccess.Model.HeraldedSolver.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Model.HeraldedSolver.success

/-- info: 'DysonGeneralAccess.Model.HeraldedSolver.accurate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Model.HeraldedSolver.accurate

/-- info: 'DysonGeneralAccess.Model.HeraldedSolver.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Model.HeraldedSolver.mono

/-- info: 'DysonGeneralAccess.Model.HeraldedSolver.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Model.HeraldedSolver.map

/-- info: 'DysonGeneralAccess.Model.HeraldedSolver.map_prog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Model.HeraldedSolver.map_prog

/-- info: 'DysonGeneralAccess.Model.HeraldedSolver.trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Model.HeraldedSolver.trivial

/-- info: 'DysonGeneralAccess.Model.HeraldedSolver.trivial_prog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Model.HeraldedSolver.trivial_prog

/-- info: 'DysonGeneralAccess.Model.ofSolver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Model.ofSolver

/-- info: 'DysonGeneralAccess.Model.toSolver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Model.toSolver

/-- info: 'DysonGeneralAccess.Model.toSolver_prog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Model.toSolver_prog

/-! ### Query counts (`DysonGeneralAccess.Cost`) -/

/-- info: 'DysonGeneralAccess.Cost.cost_reflatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Cost.cost_reflatten

/-- info: 'DysonGeneralAccess.Cost.cost_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Cost.cost_steps

/-- info: 'DysonGeneralAccess.Cost.cost_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Cost.cost_trial

/-- info: 'DysonGeneralAccess.Cost.cost_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Cost.cost_step

/-- info: 'DysonGeneralAccess.Cost.cost_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Cost.cost_four

/-! ### Flattened stage programs (`DysonGeneralAccess.Assemble`) -/

/-- info: 'DysonGeneralAccess.Assemble.eval_flatProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Assemble.eval_flatProg

/-- info: 'DysonGeneralAccess.Assemble.cost_flatProg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Assemble.cost_flatProg

/-- info: 'DysonGeneralAccess.Assemble.flatProg_eval_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Assemble.flatProg_eval_symm

/-- info: 'DysonGeneralAccess.Assemble.herald_conj_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Assemble.herald_conj_symm

/-- info: 'DysonGeneralAccess.Assemble.ofStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Assemble.ofStage

/-- info: 'DysonGeneralAccess.Assemble.ofStage_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Assemble.ofStage_success

/-- info: 'DysonGeneralAccess.Assemble.ofGood' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Assemble.ofGood

/-- info: 'DysonGeneralAccess.Assemble.ofGood_prog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Assemble.ofGood_prog

/-- info: 'DysonGeneralAccess.Assemble.ofGood_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Assemble.ofGood_success

/-! ### The general construction (`DysonGeneralAccess.Core`) -/

/-- info: 'DysonGeneralAccess.Core.cost_attempts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Core.cost_attempts

/-- info: 'DysonGeneralAccess.Core.good_attempts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Core.good_attempts

/-- info: 'DysonGeneralAccess.Core.single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Core.single

/-- info: 'DysonGeneralAccess.Core.single_prog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Core.single_prog

/-- info: 'DysonGeneralAccess.Core.single_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Core.single_cost

/-- info: 'DysonGeneralAccess.Core.single_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Core.single_success

/-- info: 'DysonGeneralAccess.Core.single_matrix_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Core.single_matrix_le

/-! ### Valid instances (`DysonGeneralAccess.Valid`) -/

/-- info: 'DysonGeneralAccess.Dyson.oracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Dyson.oracle_unitary

/-- info: 'DysonGeneralAccess.Dyson.exists_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Dyson.exists_shape

/-! ### Lemma `odel:lem:dyson` as one program (`DysonGeneralAccess.Theorem`) -/

/-- info: 'DysonGeneralAccess.Dyson.single_dyson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Dyson.single_dyson

/-! ### Corollaries (`DysonGeneralAccess.Corollaries`) -/

/-- info: 'DysonGeneralAccess.Dyson.releaseValid_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Dyson.releaseValid_valid

/-- info: 'DysonGeneralAccess.Dyson.single_release_class' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Dyson.single_release_class

/-- info: 'DysonGeneralAccess.Dyson.single_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Dyson.single_fixed

/-- info: 'DysonGeneralAccess.Dyson.single_no_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Dyson.single_no_uniform

/-! ### The ODE lower-bound class (`DysonGeneralAccess.Family`) -/

/-- info: 'DysonGeneralAccess.Family.fourAttempts_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Family.fourAttempts_eq

/-- info: 'DysonGeneralAccess.Family.solver_dyson_of_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Family.solver_dyson_of_core

/-- info: 'DysonGeneralAccess.Family.heralded_dyson_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms DysonGeneralAccess.Family.heralded_dyson_family
