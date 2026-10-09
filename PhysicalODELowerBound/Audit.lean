import PhysicalODELowerBound.Statements

set_option autoImplicit false

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem of the ODE lower bounds
over the released solvers' physical oracles (96 theorems) and every `Prop`-valued field of the
structures `Mesh.MeshWitnesses` and `Const.ConstWitnesses` (6 fields), 102 audits in module
order. Every report lists `propext`, `Classical.choice` and `Quot.sound`. -/

/-! ### Search-weight growth of the call forms (`PhysicalODELowerBound.Access.Growth`) -/

/-- info: 'PhysicalODELowerBound.Access.wgrowth_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Access.wgrowth_fiber

/-- info: 'PhysicalODELowerBound.Access.wgrowth_ctrlOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Access.wgrowth_ctrlOp

/-- info: 'PhysicalODELowerBound.Access.searchGrowth_callFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Access.searchGrowth_callFamily

/-! ### Boolean certificates for the general-mesh physical oracle
(`PhysicalODELowerBound.Access.MeshBoolean`) -/

/-- info: 'PhysicalODELowerBound.Access.stageEncoding_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Access.stageEncoding_isometry

/-- info: 'PhysicalODELowerBound.Access.implementsOn_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Access.implementsOn_mesh

/-- info: 'PhysicalODELowerBound.Access.implementsOn_mesh_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Access.implementsOn_mesh_calls

/-! ### Search-weight growth of the general-mesh physical oracle on one-stage families
(`PhysicalODELowerBound.Access.MeshGrowth`) -/

/-- info: 'PhysicalODELowerBound.Access.stageAccess_oneStage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Access.stageAccess_oneStage

/-- info: 'PhysicalODELowerBound.Access.searchGrowth_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Access.searchGrowth_mesh

/-- info: 'PhysicalODELowerBound.Access.searchGrowth_mesh_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Access.searchGrowth_mesh_calls

/-! ### The `g = 1` families over any oracle with search-weight growth
(`PhysicalODELowerBound.Families.Herald`) -/

/-- info: 'PhysicalODELowerBound.Families.time_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Families.time_solver

/-- info: 'PhysicalODELowerBound.Families.mixed_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Families.mixed_solver

/-- info: 'PhysicalODELowerBound.Families.precision_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Families.precision_solver

/-- info: 'PhysicalODELowerBound.Families.time_pad_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Families.time_pad_solver

/-- info: 'PhysicalODELowerBound.Families.mixed_pad_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Families.mixed_pad_solver

/-- info: 'PhysicalODELowerBound.Families.precision_pad_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Families.precision_pad_solver

/-! ### The time-dependent families over any Boolean-implemented oracle
(`PhysicalODELowerBound.Families.Joint`) -/

/-- info: 'PhysicalODELowerBound.Families.joint_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Families.joint_solver

/-- info: 'PhysicalODELowerBound.Families.hom_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Families.hom_solver

/-- info: 'PhysicalODELowerBound.Families.joint_pad_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Families.joint_pad_solver

/-! ### The positive semidefinite families over any oracle with search-weight growth
(`PhysicalODELowerBound.Families.Psd`) -/

/-- info: 'PhysicalODELowerBound.Families.psd_search_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Families.psd_search_solver

/-- info: 'PhysicalODELowerBound.Families.psd_scalar_solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Families.psd_scalar_solver

/-! ### Forcing over the general-mesh physical oracle (`PhysicalODELowerBound.Mesh.Model`) -/

/-- info: 'PhysicalODELowerBound.Mesh.MeshWitnesses.inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.MeshWitnesses.inClass

/-- info: 'PhysicalODELowerBound.Mesh.MeshWitnesses.time_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.MeshWitnesses.time_eq

/-- info: 'PhysicalODELowerBound.Mesh.MeshWitnesses.forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.MeshWitnesses.forces

/-- info: 'PhysicalODELowerBound.Mesh.MeshCost.of_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.MeshCost.of_tree

/-- info: 'PhysicalODELowerBound.Mesh.MeshForces.le_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.MeshForces.le_cost

/-- info: 'PhysicalODELowerBound.Mesh.meshForces_of_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.meshForces_of_cost

/-- info: 'PhysicalODELowerBound.Mesh.MeshWitnesses.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.MeshWitnesses.mono

/-- info: 'PhysicalODELowerBound.Mesh.MeshForces.retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.MeshForces.retry

/-- info: 'PhysicalODELowerBound.Mesh.MeshForces.retry_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.MeshForces.retry_calls

/-- info: 'PhysicalODELowerBound.Mesh.MeshForces.releaseRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.MeshForces.releaseRun

/-- info: 'PhysicalODELowerBound.Mesh.MeshForces.releaseProtocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.MeshForces.releaseProtocol

/-! ### Transfers to the general-mesh physical oracle (`PhysicalODELowerBound.Mesh.Transfer`) -/

/-- info: 'PhysicalODELowerBound.Mesh.meshForces_of_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.meshForces_of_growth

/-- info: 'PhysicalODELowerBound.Mesh.meshForces_of_boolean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.meshForces_of_boolean

/-! ### Eq. `odel:eq:hsbound` over the general-mesh physical oracle
(`PhysicalODELowerBound.Mesh.Herald`) -/

/-- info: 'PhysicalODELowerBound.Mesh.time_forces_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.time_forces_mesh

/-- info: 'PhysicalODELowerBound.Mesh.mixed_forces_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.mixed_forces_mesh

/-- info: 'PhysicalODELowerBound.Mesh.precision_forces_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.precision_forces_mesh

/-- info: 'PhysicalODELowerBound.Mesh.precision_forces_sqrt_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.precision_forces_sqrt_mesh

/-- info: 'PhysicalODELowerBound.Mesh.herald_max_cost_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.herald_max_cost_mesh

/-- info: 'PhysicalODELowerBound.Mesh.herald_witness_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.herald_witness_mesh

/-- info: 'PhysicalODELowerBound.Mesh.precision_terms_witness_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.precision_terms_witness_mesh

/-! ### The padded `g = 1` families over the general-mesh physical oracle
(`PhysicalODELowerBound.Mesh.HeraldPad`) -/

/-- info: 'PhysicalODELowerBound.Mesh.time_forces_pad_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.time_forces_pad_mesh

/-- info: 'PhysicalODELowerBound.Mesh.mixed_forces_pad_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.mixed_forces_pad_mesh

/-- info: 'PhysicalODELowerBound.Mesh.precision_forces_pad_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.precision_forces_pad_mesh

/-- info: 'PhysicalODELowerBound.Mesh.precision_forces_sqrt_pad_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.precision_forces_sqrt_pad_mesh

/-- info: 'PhysicalODELowerBound.Mesh.herald_max_cost_pad_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.herald_max_cost_pad_mesh

/-- info: 'PhysicalODELowerBound.Mesh.herald_witness_pad_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.herald_witness_pad_mesh

/-- info: 'PhysicalODELowerBound.Mesh.precision_terms_witness_pad_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.precision_terms_witness_pad_mesh

/-! ### Theorem `odel:thm:psd` over the general-mesh physical oracle
(`PhysicalODELowerBound.Mesh.Psd`) -/

/-- info: 'PhysicalODELowerBound.Mesh.psd_search_forces_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.psd_search_forces_mesh

/-- info: 'PhysicalODELowerBound.Mesh.psd_scalar_forces_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.psd_scalar_forces_mesh

/-- info: 'PhysicalODELowerBound.Mesh.psd_scalar_forces_sqrt_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.psd_scalar_forces_sqrt_mesh

/-- info: 'PhysicalODELowerBound.Mesh.psd_max_cost_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.psd_max_cost_mesh

/-- info: 'PhysicalODELowerBound.Mesh.psd_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.psd_mesh

/-! ### Theorem `odel:thm:joint` and Remark `odel:rem:homogeneous` over the general-mesh physical
oracle (`PhysicalODELowerBound.Mesh.Joint`) -/

/-- info: 'PhysicalODELowerBound.Mesh.joint_forces_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.joint_forces_mesh

/-- info: 'PhysicalODELowerBound.Mesh.joint_witness_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.joint_witness_mesh

/-- info: 'PhysicalODELowerBound.Mesh.hom_forces_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.hom_forces_mesh

/-- info: 'PhysicalODELowerBound.Mesh.hom_witness_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.hom_witness_mesh

/-! ### The padded joint families over the general-mesh physical oracle
(`PhysicalODELowerBound.Mesh.JointPad`) -/

/-- info: 'PhysicalODELowerBound.Mesh.joint_forces_pad_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.joint_forces_pad_mesh

/-- info: 'PhysicalODELowerBound.Mesh.joint_witness_pad_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.joint_witness_pad_mesh

/-- info: 'PhysicalODELowerBound.Mesh.joint_common_dimension_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.joint_common_dimension_mesh

/-- info: 'PhysicalODELowerBound.Mesh.joint_qubit_register_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.joint_qubit_register_mesh

/-! ### Theorem `odel:thm:combined` over the general-mesh physical oracle
(`PhysicalODELowerBound.Mesh.Combined`) -/

/-- info: 'PhysicalODELowerBound.Mesh.combined_max_cost_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.combined_max_cost_mesh

/-- info: 'PhysicalODELowerBound.Mesh.combined_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.combined_mesh

/-- info: 'PhysicalODELowerBound.Mesh.combined_max_cost_pad_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.combined_max_cost_pad_mesh

/-- info: 'PhysicalODELowerBound.Mesh.combined_pad_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.combined_pad_mesh

/-- info: 'PhysicalODELowerBound.Mesh.combined_common_dimension_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.combined_common_dimension_mesh

/-- info: 'PhysicalODELowerBound.Mesh.combined_qubit_register_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.combined_qubit_register_mesh

/-- info: 'PhysicalODELowerBound.Mesh.combined_max_release_tree_of_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Mesh.combined_max_release_tree_of_mesh

/-! ### Forcing over the constant-coefficient physical oracle
(`PhysicalODELowerBound.Const.Model`) -/

/-- info: 'PhysicalODELowerBound.Const.ConstWitnesses.inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.ConstWitnesses.inClass

/-- info: 'PhysicalODELowerBound.Const.ConstWitnesses.time_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.ConstWitnesses.time_eq

/-- info: 'PhysicalODELowerBound.Const.ConstWitnesses.forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.ConstWitnesses.forces

/-- info: 'PhysicalODELowerBound.Const.ConstCost.of_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.ConstCost.of_tree

/-- info: 'PhysicalODELowerBound.Const.ConstForces.le_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.ConstForces.le_cost

/-- info: 'PhysicalODELowerBound.Const.constForces_of_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.constForces_of_cost

/-- info: 'PhysicalODELowerBound.Const.ConstWitnesses.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.ConstWitnesses.mono

/-- info: 'PhysicalODELowerBound.Const.ConstForces.retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.ConstForces.retry

/-- info: 'PhysicalODELowerBound.Const.ConstForces.retry_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.ConstForces.retry_calls

/-- info: 'PhysicalODELowerBound.Const.ConstForces.constRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.ConstForces.constRun

/-! ### Transfers to the constant-coefficient physical oracle
(`PhysicalODELowerBound.Const.Transfer`) -/

/-- info: 'PhysicalODELowerBound.Const.searchGrowth_const_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.searchGrowth_const_calls

/-- info: 'PhysicalODELowerBound.Const.constForces_of_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.constForces_of_growth

/-! ### Eq. `odel:eq:hsbound` over the constant-coefficient physical oracle
(`PhysicalODELowerBound.Const.Herald`) -/

/-- info: 'PhysicalODELowerBound.Const.time_forces_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.time_forces_const

/-- info: 'PhysicalODELowerBound.Const.mixed_forces_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.mixed_forces_const

/-- info: 'PhysicalODELowerBound.Const.precision_forces_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.precision_forces_const

/-- info: 'PhysicalODELowerBound.Const.precision_forces_sqrt_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.precision_forces_sqrt_const

/-- info: 'PhysicalODELowerBound.Const.herald_max_cost_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.herald_max_cost_const

/-- info: 'PhysicalODELowerBound.Const.herald_witness_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.herald_witness_const

/-- info: 'PhysicalODELowerBound.Const.time_forces_pad_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.time_forces_pad_const

/-- info: 'PhysicalODELowerBound.Const.mixed_forces_pad_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.mixed_forces_pad_const

/-- info: 'PhysicalODELowerBound.Const.precision_forces_pad_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.precision_forces_pad_const

/-- info: 'PhysicalODELowerBound.Const.precision_forces_sqrt_pad_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.precision_forces_sqrt_pad_const

/-- info: 'PhysicalODELowerBound.Const.herald_max_cost_pad_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.herald_max_cost_pad_const

/-- info: 'PhysicalODELowerBound.Const.herald_witness_pad_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.herald_witness_pad_const

/-- info: 'PhysicalODELowerBound.Const.herald_common_dimension_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.herald_common_dimension_const

/-- info: 'PhysicalODELowerBound.Const.herald_qubit_register_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.herald_qubit_register_const

/-- info: 'PhysicalODELowerBound.Const.herald_max_const_tree_of_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.herald_max_const_tree_of_const

/-- info: 'PhysicalODELowerBound.Const.precision_terms_witness_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.precision_terms_witness_const

/-- info: 'PhysicalODELowerBound.Const.precision_terms_witness_pad_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.precision_terms_witness_pad_const

/-! ### Theorem `odel:thm:psd` over the constant-coefficient physical oracle
(`PhysicalODELowerBound.Const.Psd`) -/

/-- info: 'PhysicalODELowerBound.Const.psd_search_forces_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.psd_search_forces_const

/-- info: 'PhysicalODELowerBound.Const.psd_scalar_forces_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.psd_scalar_forces_const

/-- info: 'PhysicalODELowerBound.Const.psd_scalar_forces_sqrt_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.psd_scalar_forces_sqrt_const

/-- info: 'PhysicalODELowerBound.Const.psd_max_cost_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.psd_max_cost_const

/-- info: 'PhysicalODELowerBound.Const.psd_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.psd_const

/-- info: 'PhysicalODELowerBound.Const.psd_max_const_tree_of_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhysicalODELowerBound.Const.psd_max_const_tree_of_const
