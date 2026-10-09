import ReleasedODESolverLowerBounds.Statements

set_option autoImplicit false

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem of the library of the ODE
lower bounds for algorithms with measurements inside a run over the physical oracles of the
released solvers of Theorems `ode:thm:main` and `ode:thm:time`, and of the runs of the released
general-mesh solver on the positive semidefinite and homogeneous families (131 theorems), in
module order, and every `Prop`-valued field of the structures `Transport.Absorbs`,
`Mesh.MeasuredMeshWitnesses`, `Const.MeasuredConstWitnesses` and `Runs.MeshRun` (11 fields), 142
audits. Definitions, including the `Prop`-valued predicates `MeasuredMeshForces`,
`MeasuredMeshCost`, `MeasuredConstForces` and `MeasuredConstCost`, are covered through the
theorems that use them. Every report lists `propext`, `Classical.choice` and
`Quot.sound`, except `Transport.formSel_eq_formSelOf` (`Quot.sound` only),
`Transport.formSelOf_eq_some` (`propext` only) and `Mesh.countWeight_value` (`propext` and
`Quot.sound`).
-/

/-! ### Absorption of spectator registers (`Access.Absorb`) -/

/-- info: 'ReleasedODESolverLowerBounds.Access.restrictMap_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.restrictMap_apply

/-- info: 'ReleasedODESolverLowerBounds.Access.padMap_eq_padOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.padMap_eq_padOf

/-- info: 'ReleasedODESolverLowerBounds.Access.padMap_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.padMap_apply

/-- info: 'ReleasedODESolverLowerBounds.Access.padMap_apply_emb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.padMap_apply_emb

/-- info: 'ReleasedODESolverLowerBounds.Access.padMap_apply_of_not' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.padMap_apply_of_not

/-- info: 'ReleasedODESolverLowerBounds.Access.padMap_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.padMap_isometry

/-- info: 'ReleasedODESolverLowerBounds.Access.fiber_comp_padMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.fiber_comp_padMap

/-- info: 'ReleasedODESolverLowerBounds.Access.finrank_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.finrank_joint

/-- info: 'ReleasedODESolverLowerBounds.Access.exists_absorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.exists_absorb

/-- info: 'ReleasedODESolverLowerBounds.Access.SpectatorForm.nonempty_inverseConj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.SpectatorForm.nonempty_inverseConj

/-! ### Dimensions of the released solvers' physical workspaces (`Access.Dimension`) -/

/-- info: 'ReleasedODESolverLowerBounds.Access.card_meshMatrixBasis_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.card_meshMatrixBasis_le

/-- info: 'ReleasedODESolverLowerBounds.Access.card_constMatrixBasis_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.card_constMatrixBasis_le

/-- info: 'ReleasedODESolverLowerBounds.Access.finrank_sectorPhysical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.finrank_sectorPhysical

/-- info: 'ReleasedODESolverLowerBounds.Access.card_mul_finrank_sectorPhysical_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.card_mul_finrank_sectorPhysical_le

/-- info: 'ReleasedODESolverLowerBounds.Access.card_mul_finrank_meshPhysical_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.card_mul_finrank_meshPhysical_le

/-- info: 'ReleasedODESolverLowerBounds.Access.card_mul_finrank_constPhysical_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.card_mul_finrank_constPhysical_le

/-! ### The inverse value call as a conjugated value call (`Access.ValueConj`) -/

/-- info: 'ReleasedODESolverLowerBounds.Access.negPrim_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.negPrim_unitary

/-- info: 'ReleasedODESolverLowerBounds.Access.negValue_eq_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.negValue_eq_fiber

/-- info: 'ReleasedODESolverLowerBounds.Access.star_oracles_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.star_oracles_value

/-- info: 'ReleasedODESolverLowerBounds.Access.star_labelOracle_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.star_labelOracle_value

/-! ### The general-mesh oracle in spectator form (`Access.MeshForm`) -/

/-- info: 'ReleasedODESolverLowerBounds.Access.fiber_labelOracle_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.fiber_labelOracle_eq

/-- info: 'ReleasedODESolverLowerBounds.Access.meshOracle_spectatorForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.meshOracle_spectatorForm

/-- info: 'ReleasedODESolverLowerBounds.Access.meshOracle_absorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.meshOracle_absorb

/-- info: 'ReleasedODESolverLowerBounds.Access.meshOracle_valueConj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.meshOracle_valueConj

/-! ### The constant-coefficient oracle in spectator form (`Access.ConstForm`) -/

/-- info: 'ReleasedODESolverLowerBounds.Access.constOracle_spectatorForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.constOracle_spectatorForm

/-- info: 'ReleasedODESolverLowerBounds.Access.constOracle_absorb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.constOracle_absorb

/-- info: 'ReleasedODESolverLowerBounds.Access.constOracle_valueConj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Access.constOracle_valueConj

/-! ### Absorbing oracles and compiled programs (`Transport.Encode`) -/

/-- info: 'ReleasedODESolverLowerBounds.Transport.Absorbs.emb_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.Absorbs.emb_isometry

/-- info: 'ReleasedODESolverLowerBounds.Transport.Absorbs.intertwine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.Absorbs.intertwine

/-- info: 'ReleasedODESolverLowerBounds.Transport.Absorbs.enc_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.Absorbs.enc_isometry

/-- info: 'ReleasedODESolverLowerBounds.Transport.ctrlTarget_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.ctrlTarget_unitary

/-- info: 'ReleasedODESolverLowerBounds.Transport.formOp_comp_jointMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.formOp_comp_jointMap

/-- info: 'ReleasedODESolverLowerBounds.Transport.Absorbs.circuit_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.Absorbs.circuit_eval

/-- info: 'ReleasedODESolverLowerBounds.Transport.Absorbs.circuit_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.Absorbs.circuit_cost

/-- info: 'ReleasedODESolverLowerBounds.Transport.Absorbs.compileProg_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.Absorbs.compileProg_eval

/-- info: 'ReleasedODESolverLowerBounds.Transport.Absorbs.compileProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.Absorbs.compileProg_cost

/-! ### Measured solvers over a physical oracle: the plain shape (`Transport.Plain`) -/

/-- info: 'ReleasedODESolverLowerBounds.Transport.singleConj_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.singleConj_isSome

/-- info: 'ReleasedODESolverLowerBounds.Transport.plainEncOf_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.plainEncOf_isometry

/-- info: 'ReleasedODESolverLowerBounds.Transport.plainCircuitsOf_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.plainCircuitsOf_eval

/-- info: 'ReleasedODESolverLowerBounds.Transport.plainCircuitsOf_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.plainCircuitsOf_cost

/-- info: 'ReleasedODESolverLowerBounds.Transport.exists_treeSolver_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.exists_treeSolver_plain

/-! ### Label-generic call forms (`Transport.Calls`) -/

/-- info: 'ReleasedODESolverLowerBounds.Transport.formSel_eq_formSelOf' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.formSel_eq_formSelOf

/-- info: 'ReleasedODESolverLowerBounds.Transport.callOpt_callFamily_apply_formSelOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.callOpt_callFamily_apply_formSelOf

/-- info: 'ReleasedODESolverLowerBounds.Transport.callOpt_callFamily_apply_query' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.callOpt_callFamily_apply_query

/-- info: 'ReleasedODESolverLowerBounds.Transport.formSelOf_eq_some' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.formSelOf_eq_some

/-- info: 'ReleasedODESolverLowerBounds.Transport.callFlat_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.callFlat_apply

/-- info: 'ReleasedODESolverLowerBounds.Transport.patOp_callFlat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.patOp_callFlat

/-! ### Measured solvers over a physical oracle: the call shape (`Transport.Call`) -/

/-- info: 'ReleasedODESolverLowerBounds.Transport.callEncOf_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.callEncOf_isometry

/-- info: 'ReleasedODESolverLowerBounds.Transport.callFlat_selFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.callFlat_selFamily

/-- info: 'ReleasedODESolverLowerBounds.Transport.callCircuitsOf_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.callCircuitsOf_eval

/-- info: 'ReleasedODESolverLowerBounds.Transport.callCircuitsOf_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.callCircuitsOf_cost

/-- info: 'ReleasedODESolverLowerBounds.Transport.exists_treeSolver_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Transport.exists_treeSolver_call

/-! ### Measured forcing over the general-mesh oracle (`Mesh.Model`) -/

/-- info: 'ReleasedODESolverLowerBounds.Mesh.countWeight_value' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.countWeight_value

/-- info: 'ReleasedODESolverLowerBounds.Mesh.MeasuredMeshCost.of_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.MeasuredMeshCost.of_measured

/-- info: 'ReleasedODESolverLowerBounds.Mesh.MeasuredMeshForces.le_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.MeasuredMeshForces.le_cost

/-- info: 'ReleasedODESolverLowerBounds.Mesh.MeasuredMeshWitnesses.inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.MeasuredMeshWitnesses.inClass

/-- info: 'ReleasedODESolverLowerBounds.Mesh.MeasuredMeshWitnesses.time_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.MeasuredMeshWitnesses.time_eq

/-- info: 'ReleasedODESolverLowerBounds.Mesh.MeasuredMeshWitnesses.forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.MeasuredMeshWitnesses.forces

/-- info: 'ReleasedODESolverLowerBounds.Mesh.MeasuredMeshWitnesses.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.MeasuredMeshWitnesses.mono

/-! ### The general-mesh oracle absorbs its spectator lift (`Mesh.Upgrade.Absorb`) -/

/-- info: 'ReleasedODESolverLowerBounds.Mesh.meshAbsorbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.meshAbsorbs

/-! ### Adaptive from measured solvers, plain shape (`Mesh.Upgrade.Plain`) -/

/-- info: 'ReleasedODESolverLowerBounds.Mesh.exists_meshTree_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.exists_meshTree_plain

/-! ### Adaptive from measured solvers, call shape (`Mesh.Upgrade.Call`) -/

/-- info: 'ReleasedODESolverLowerBounds.Mesh.exists_meshTree_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.exists_meshTree_call

/-! ### Measured forcing from adaptive forcing (`Mesh.Upgrade.Cost`) -/

/-- info: 'ReleasedODESolverLowerBounds.Mesh.MeasuredMeshCost.exists_meshCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.MeasuredMeshCost.exists_meshCost_le

/-- info: 'ReleasedODESolverLowerBounds.Mesh.measuredMeshForces_of_meshForces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.measuredMeshForces_of_meshForces

/-! ### Adaptive forcing from measured forcing (`Mesh.Upgrade.Converse`) -/

/-- info: 'ReleasedODESolverLowerBounds.Mesh.meshForces_of_measuredMeshForces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.meshForces_of_measuredMeshForces

/-! ### Measured witnesses over the general-mesh oracle (`Mesh.Upgrade`) -/

/-- info: 'ReleasedODESolverLowerBounds.Mesh.measuredMeshWitnesses_of_meshWitnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.measuredMeshWitnesses_of_meshWitnesses

/-! ### Measured lower bounds over the general-mesh oracle (`Mesh.Corollaries`) -/

/-- info: 'ReleasedODESolverLowerBounds.Mesh.herald_witness_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.herald_witness_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.herald_witness_pad_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.herald_witness_pad_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.precision_terms_witness_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.precision_terms_witness_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.psd_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.psd_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.joint_witness_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.joint_witness_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.hom_witness_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.hom_witness_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.combined_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.combined_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.combined_pad_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.combined_pad_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.herald_max_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.herald_max_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.psd_max_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.psd_max_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.combined_max_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.combined_max_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.combined_max_release_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.combined_max_release_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.joint_release_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.joint_release_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.mixed_release_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.mixed_release_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.precision_release_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.precision_release_measured_mesh

/-! ### Padded and common-dimension forms, general mesh (`Mesh.Padded`) -/

/-- info: 'ReleasedODESolverLowerBounds.Mesh.joint_witness_pad_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.joint_witness_pad_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.joint_common_dimension_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.joint_common_dimension_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.joint_qubit_register_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.joint_qubit_register_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.precision_terms_witness_pad_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.precision_terms_witness_pad_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.herald_max_pad_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.herald_max_pad_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.combined_max_pad_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.combined_max_pad_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.combined_common_dimension_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.combined_common_dimension_measured_mesh

/-- info: 'ReleasedODESolverLowerBounds.Mesh.combined_qubit_register_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Mesh.combined_qubit_register_measured_mesh

/-! ### Measured forcing over the constant-coefficient oracle (`Const.Model`) -/

/-- info: 'ReleasedODESolverLowerBounds.Const.MeasuredConstCost.of_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.MeasuredConstCost.of_measured

/-- info: 'ReleasedODESolverLowerBounds.Const.MeasuredConstForces.le_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.MeasuredConstForces.le_cost

/-- info: 'ReleasedODESolverLowerBounds.Const.MeasuredConstWitnesses.inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.MeasuredConstWitnesses.inClass

/-- info: 'ReleasedODESolverLowerBounds.Const.MeasuredConstWitnesses.time_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.MeasuredConstWitnesses.time_eq

/-- info: 'ReleasedODESolverLowerBounds.Const.MeasuredConstWitnesses.forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.MeasuredConstWitnesses.forces

/-- info: 'ReleasedODESolverLowerBounds.Const.MeasuredConstWitnesses.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.MeasuredConstWitnesses.mono

/-! ### Measured forcing from adaptive forcing, constant coefficients (`Const.Upgrade`) -/

/-- info: 'ReleasedODESolverLowerBounds.Const.constAbsorbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.constAbsorbs

/-- info: 'ReleasedODESolverLowerBounds.Const.exists_constTree_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.exists_constTree_plain

/-- info: 'ReleasedODESolverLowerBounds.Const.exists_constTree_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.exists_constTree_call

/-- info: 'ReleasedODESolverLowerBounds.Const.MeasuredConstCost.exists_constCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.MeasuredConstCost.exists_constCost_le

/-- info: 'ReleasedODESolverLowerBounds.Const.measuredConstForces_of_constForces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.measuredConstForces_of_constForces

/-- info: 'ReleasedODESolverLowerBounds.Const.constForces_of_measuredConstForces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.constForces_of_measuredConstForces

/-- info: 'ReleasedODESolverLowerBounds.Const.measuredConstWitnesses_of_constWitnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.measuredConstWitnesses_of_constWitnesses

/-! ### Measured lower bounds over the constant-coefficient oracle (`Const.Corollaries`) -/

/-- info: 'ReleasedODESolverLowerBounds.Const.herald_witness_measured_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.herald_witness_measured_const

/-- info: 'ReleasedODESolverLowerBounds.Const.herald_witness_pad_measured_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.herald_witness_pad_measured_const

/-- info: 'ReleasedODESolverLowerBounds.Const.precision_terms_witness_measured_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.precision_terms_witness_measured_const

/-- info: 'ReleasedODESolverLowerBounds.Const.psd_measured_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.psd_measured_const

/-- info: 'ReleasedODESolverLowerBounds.Const.herald_max_measured_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.herald_max_measured_const

/-- info: 'ReleasedODESolverLowerBounds.Const.psd_max_measured_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.psd_max_measured_const

/-- info: 'ReleasedODESolverLowerBounds.Const.herald_max_release_measured_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.herald_max_release_measured_const

/-- info: 'ReleasedODESolverLowerBounds.Const.psd_max_release_measured_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.psd_max_release_measured_const

/-! ### Padded and common-dimension forms, constant coefficients (`Const.Padded`) -/

/-- info: 'ReleasedODESolverLowerBounds.Const.precision_terms_witness_pad_measured_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.precision_terms_witness_pad_measured_const

/-- info: 'ReleasedODESolverLowerBounds.Const.herald_max_pad_measured_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.herald_max_pad_measured_const

/-- info: 'ReleasedODESolverLowerBounds.Const.herald_common_dimension_measured_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.herald_common_dimension_measured_const

/-- info: 'ReleasedODESolverLowerBounds.Const.herald_qubit_register_measured_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Const.herald_qubit_register_measured_const

/-! ### Runs of the released general-mesh solver with split energy bounds (`Runs.Model`) -/

/-- info: 'ReleasedODESolverLowerBounds.Runs.meshTheta_one_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.meshTheta_one_zero

/-- info: 'ReleasedODESolverLowerBounds.Runs.meshTheta_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.meshTheta_eq

/-- info: 'ReleasedODESolverLowerBounds.Runs.MeshRun.R_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.MeshRun.R_pos

/-- info: 'ReleasedODESolverLowerBounds.Runs.MeshRun.sources_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.MeshRun.sources_public

/-- info: 'ReleasedODESolverLowerBounds.Runs.MeshRun.release' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.MeshRun.release

/-- info: 'ReleasedODESolverLowerBounds.Runs.MeshRun.valueQueries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.MeshRun.valueQueries_le

/-- info: 'ReleasedODESolverLowerBounds.Runs.MeshRun.matrixQueries_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.MeshRun.matrixQueries_le

/-- info: 'ReleasedODESolverLowerBounds.Runs.MeshRun.ofReleaseRun_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.MeshRun.ofReleaseRun_queries

/-- info: 'ReleasedODESolverLowerBounds.Runs.meshForces_meshRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.meshForces_meshRun

/-- info: 'ReleasedODESolverLowerBounds.Runs.meshCost_meshRun' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.meshCost_meshRun

/-! ### Existence of runs of the released general-mesh solver (`Runs.Exists`) -/

/-- info: 'ReleasedODESolverLowerBounds.Runs.exists_meshParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.exists_meshParams

/-- info: 'ReleasedODESolverLowerBounds.Runs.exists_meshProtocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.exists_meshProtocol

/-- info: 'ReleasedODESolverLowerBounds.Runs.meshRun_nonempty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.meshRun_nonempty

/-- info: 'ReleasedODESolverLowerBounds.Runs.norm_half_mul_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.norm_half_mul_sq_le

/-- info: 'ReleasedODESolverLowerBounds.Runs.norm_hamiltonianPart_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.norm_hamiltonianPart_sq_le

/-- info: 'ReleasedODESolverLowerBounds.Runs.norm_dissipativePart_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.norm_dissipativePart_sq_le

/-- info: 'ReleasedODESolverLowerBounds.Runs.part_rows_cols_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.part_rows_cols_le_one

/-- info: 'ReleasedODESolverLowerBounds.Runs.parts_le_one_of_inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.parts_le_one_of_inClass

/-- info: 'ReleasedODESolverLowerBounds.Runs.meshRun_nonempty_of_inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.meshRun_nonempty_of_inClass

/-- info: 'ReleasedODESolverLowerBounds.Runs.exists_releaseProtocol_of_meshProtocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.exists_releaseProtocol_of_meshProtocol

/-! ### Runs on the positive semidefinite and homogeneous families (`Runs.Instances`) -/

/-- info: 'ReleasedODESolverLowerBounds.Runs.psd_meshRuns_exist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.psd_meshRuns_exist

/-- info: 'ReleasedODESolverLowerBounds.Runs.psd_meshRun_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.psd_meshRun_bounds

/-- info: 'ReleasedODESolverLowerBounds.Runs.psd_meshRun_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.psd_meshRun_bracket

/-- info: 'ReleasedODESolverLowerBounds.Runs.hom_meshRun_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.hom_meshRun_exists

/-- info: 'ReleasedODESolverLowerBounds.Runs.hom_meshRun_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.hom_meshRun_bounds

/-- info: 'ReleasedODESolverLowerBounds.Runs.hom_meshRun_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.hom_meshRun_bracket

/-- info: 'ReleasedODESolverLowerBounds.Runs.MeshRun.exists_measuredSolver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.MeshRun.exists_measuredSolver

/-! ### Runs of the released constant-coefficient solver as measured solvers (`Runs.Const`) -/

/-- info: 'ReleasedODESolverLowerBounds.Runs.constRun_exists_measuredSolver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReleasedODESolverLowerBounds.Runs.constRun_exists_measuredSolver
