import ConstantODELowerBound.Statements

set_option autoImplicit false

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem of the ODE lower bounds
for the released constant-coefficient solver (47 theorems) and every `Prop`-valued field of the
structure `Runs.ConstRun` (2 fields), 49 audits in module order. Every report lists `propext`,
`Classical.choice` and `Quot.sound`. -/

/-! ### The released solver's oracle on a one-stage family (`ConstantODELowerBound.Oracle`) -/

/-- info: 'ConstantODELowerBound.Oracle.constData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Oracle.constData_matrix

/-- info: 'ConstantODELowerBound.Oracle.oracles_constData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Oracle.oracles_constData

/-- info: 'ConstantODELowerBound.Oracle.oracles_constData_ham' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Oracle.oracles_constData_ham

/-- info: 'ConstantODELowerBound.Oracle.oracles_constData_heat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Oracle.oracles_constData_heat

/-- info: 'ConstantODELowerBound.Oracle.hardAccess_constData_ham' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Oracle.hardAccess_constData_ham

/-- info: 'ConstantODELowerBound.Oracle.hardAccess_constData_heat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Oracle.hardAccess_constData_heat

/-- info: 'ConstantODELowerBound.Oracle.constOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Oracle.constOracle_unitary

/-! ### The released oracle in normal form (`ConstantODELowerBound.Normal`) -/

/-- info: 'ConstantODELowerBound.Normal.isWrap_constWrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Normal.isWrap_constWrap

/-- info: 'ConstantODELowerBound.Normal.physicalOracle_inl_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Normal.physicalOracle_inl_eq

/-- info: 'ConstantODELowerBound.Normal.physicalOracle_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Normal.physicalOracle_normal_form

/-- info: 'ConstantODELowerBound.Normal.physicalOracle_inr_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Normal.physicalOracle_inr_const

/-! ### One-stage families as constant-coefficient equations (`ConstantODELowerBound.Solution`) -/

/-- info: 'ConstantODELowerBound.Solution.oneStage_T' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Solution.oneStage_T

/-- info: 'ConstantODELowerBound.Solution.oneStage_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Solution.oneStage_mass

/-- info: 'ConstantODELowerBound.Solution.generator_constData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Solution.generator_constData

/-- info: 'ConstantODELowerBound.Solution.constSolution_solves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Solution.constSolution_solves

/-- info: 'ConstantODELowerBound.Solution.endpoint_eq_constSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Solution.endpoint_eq_constSolution

/-- info: 'ConstantODELowerBound.Solution.hamiltonianPart_of_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Solution.hamiltonianPart_of_isHermitian

/-- info: 'ConstantODELowerBound.Solution.dissipativePart_of_isHermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Solution.dissipativePart_of_isHermitian

/-- info: 'ConstantODELowerBound.Solution.dissipativePart_nonneg_of_accretive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Solution.dissipativePart_nonneg_of_accretive

/-! ### Search-weight growth of the released oracle on hard data (`ConstantODELowerBound.Access`) -/

/-- info: 'ConstantODELowerBound.Access.searchGrowth_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Access.searchGrowth_const

/-- info: 'ConstantODELowerBound.Access.searchGrowth_const_ham' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Access.searchGrowth_const_ham

/-- info: 'ConstantODELowerBound.Access.searchGrowth_const_heat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Access.searchGrowth_const_heat

/-! ### Released constant-coefficient protocols as solvers (`ConstantODELowerBound.Protocol`) -/

/-- info: 'ConstantODELowerBound.Protocol.ConstProtocol.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Protocol.ConstProtocol.success

/-- info: 'ConstantODELowerBound.Protocol.ConstProtocol.accurate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Protocol.ConstProtocol.accurate

/-- info: 'ConstantODELowerBound.Protocol.ConstProtocol.worstCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Protocol.ConstProtocol.worstCost_le

/-- info: 'ConstantODELowerBound.Protocol.ConstProtocol.worstCost_toTreeSolver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Protocol.ConstProtocol.worstCost_toTreeSolver

/-! ### The released solver on a family of the class (`ConstantODELowerBound.Solver`) -/

/-- info: 'ConstantODELowerBound.Solver.exists_constProtocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Solver.exists_constProtocol

/-- info: 'ConstantODELowerBound.Solver.constProtocol_of_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Solver.constProtocol_of_certificate

/-! ### Eq. `odel:eq:hsbound` over the released oracle (`ConstantODELowerBound.Herald`) -/

/-- info: 'ConstantODELowerBound.Herald.time_const_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Herald.time_const_tree

/-- info: 'ConstantODELowerBound.Herald.mixed_const_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Herald.mixed_const_tree

/-- info: 'ConstantODELowerBound.Herald.precision_const_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Herald.precision_const_tree

/-- info: 'ConstantODELowerBound.Herald.herald_max_const_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Herald.herald_max_const_tree

/-- info: 'ConstantODELowerBound.Herald.herald_max_const_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Herald.herald_max_const_retry

/-! ### Theorem `odel:thm:psd` over the released oracle (`ConstantODELowerBound.Psd`) -/

/-- info: 'ConstantODELowerBound.Psd.psd_search_const_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Psd.psd_search_const_tree

/-- info: 'ConstantODELowerBound.Psd.psd_scalar_const_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Psd.psd_scalar_const_tree

/-- info: 'ConstantODELowerBound.Psd.psd_max_const_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Psd.psd_max_const_tree

/-- info: 'ConstantODELowerBound.Psd.psd_max_const_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Psd.psd_max_const_retry

/-! ### Runs of the released solver and their two-sided bounds (`ConstantODELowerBound.Runs`) -/

/-- info: 'ConstantODELowerBound.Runs.ConstRun.sources_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Runs.ConstRun.sources_public

/-- info: 'ConstantODELowerBound.Runs.ConstRun.release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Runs.ConstRun.release

/-- info: 'ConstantODELowerBound.Runs.ConstRun.valueQueries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Runs.ConstRun.valueQueries_le

/-- info: 'ConstantODELowerBound.Runs.ConstRun.matrixQueries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Runs.ConstRun.matrixQueries_le

/-- info: 'ConstantODELowerBound.Runs.herald_const_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Runs.herald_const_bounds

/-- info: 'ConstantODELowerBound.Runs.psd_const_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Runs.psd_const_bounds

/-! ### Existence of runs on the hard families (`ConstantODELowerBound.Instances`) -/

/-- info: 'ConstantODELowerBound.Instances.constRun_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Instances.constRun_nonempty

/-- info: 'ConstantODELowerBound.Instances.hamRun_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Instances.hamRun_nonempty

/-- info: 'ConstantODELowerBound.Instances.heatRun_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Instances.heatRun_nonempty

/-- info: 'ConstantODELowerBound.Instances.herald_const_runs_exist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Instances.herald_const_runs_exist

/-- info: 'ConstantODELowerBound.Instances.herald_const_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Instances.herald_const_bracket

/-- info: 'ConstantODELowerBound.Instances.psd_const_runs_exist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ConstantODELowerBound.Instances.psd_const_runs_exist
