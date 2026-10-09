import TimeDependentHamiltonianLowerBound.NonVacuity

set_option autoImplicit false

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem of the library of the
lower bound of Theorem `hsl:thm:main` for the time-dependent classes of Theorem `hs:thm:time`
(98 theorems) and every `Prop`-valued field of the structures `UniformHyp`, `MeshHyp`,
`MeshPath` and `IntegrablePath` (35 fields), in module order. Every report lists `propext`,
`Classical.choice` and `Quot.sound`.
-/

/-! ### Constant data, constant paths and propagators (`Constant`) -/

/-- info: 'TimeDependentHamiltonianLowerBound.constData_matrix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.constData_matrix

/-- info: 'TimeDependentHamiltonianLowerBound.constData_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.constData_table

/-- info: 'TimeDependentHamiltonianLowerBound.constData_rowOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.constData_rowOracle

/-- info: 'TimeDependentHamiltonianLowerBound.constData_columnOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.constData_columnOracle

/-- info: 'TimeDependentHamiltonianLowerBound.constData_hermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.constData_hermitian

/-- info: 'TimeDependentHamiltonianLowerBound.constData_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.constData_row

/-- info: 'TimeDependentHamiltonianLowerBound.constData_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.constData_col

/-- info: 'TimeDependentHamiltonianLowerBound.oracles_constData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.oracles_constData

/-- info: 'TimeDependentHamiltonianLowerBound.cayley_constData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.cayley_constData

/-- info: 'TimeDependentHamiltonianLowerBound.sampledOracle_constData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.sampledOracle_constData

/-- info: 'TimeDependentHamiltonianLowerBound.constPath_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.constPath_apply

/-- info: 'TimeDependentHamiltonianLowerBound.constProp_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.constProp_zero

/-- info: 'TimeDependentHamiltonianLowerBound.constProp_eq_exp_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.constProp_eq_exp_smul

/-- info: 'TimeDependentHamiltonianLowerBound.hasDerivAt_constProp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.hasDerivAt_constProp

/-- info: 'TimeDependentHamiltonianLowerBound.solvesOn_constProp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.solvesOn_constProp

/-- info: 'TimeDependentHamiltonianLowerBound.isPropagator_constProp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.isPropagator_constProp

/-- info: 'TimeDependentHamiltonianLowerBound.isPropagator_eq_constProp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.isPropagator_eq_constProp

/-- info: 'TimeDependentHamiltonianLowerBound.propagator_eq_constProp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.propagator_eq_constProp

/-- info: 'TimeDependentHamiltonianLowerBound.solvesOn_constPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.solvesOn_constPath

/-- info: 'TimeDependentHamiltonianLowerBound.isPropagator_constPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.isPropagator_constPath

/-- info: 'TimeDependentHamiltonianLowerBound.propagator_constPath_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.propagator_constPath_eq

/-- info: 'TimeDependentHamiltonianLowerBound.isPropagator_constPath_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.isPropagator_constPath_eq

/-- info: 'TimeDependentHamiltonianLowerBound.evolve_eq_constProp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.evolve_eq_constProp

/-! ### Time-dependent classes, membership and criteria (`Class`) -/

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.simulation

/-- info: 'TimeDependentHamiltonianLowerBound.MeshHyp.simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshHyp.simulation

/-- info: 'TimeDependentHamiltonianLowerBound.MeshHyp.simulation_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshHyp.simulation_integrable

/-- info: 'TimeDependentHamiltonianLowerBound.uniformHyp_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.uniformHyp_const

/-- info: 'TimeDependentHamiltonianLowerBound.uniformHyp_const_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.uniformHyp_const_zero

/-- info: 'TimeDependentHamiltonianLowerBound.meshHyp_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.meshHyp_const

/-- info: 'TimeDependentHamiltonianLowerBound.meshPath_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.meshPath_const

/-- info: 'TimeDependentHamiltonianLowerBound.integrablePath_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.integrablePath_const

/-- info: 'TimeDependentHamiltonianLowerBound.uniformHyp_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.uniformHyp_hard

/-- info: 'TimeDependentHamiltonianLowerBound.meshHyp_hard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.meshHyp_hard

/-- info: 'TimeDependentHamiltonianLowerBound.uniform_criterion_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.uniform_criterion_iff

/-- info: 'TimeDependentHamiltonianLowerBound.integrable_criterion_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.integrable_criterion_iff

/-- info: 'TimeDependentHamiltonianLowerBound.endpoint_of_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.endpoint_of_mesh

/-- info: 'TimeDependentHamiltonianLowerBound.mesh_criterion_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.mesh_criterion_iff

/-- info: 'TimeDependentHamiltonianLowerBound.uniformGuarantee_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.uniformGuarantee_const

/-- info: 'TimeDependentHamiltonianLowerBound.MeshGuarantee.criterion_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshGuarantee.criterion_const

/-- info: 'TimeDependentHamiltonianLowerBound.IntegrableGuarantee.criterion_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.IntegrableGuarantee.criterion_const

/-- info: 'TimeDependentHamiltonianLowerBound.uniformGuarantee_of_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.uniformGuarantee_of_zero

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.eta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.eta_pos

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.time_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.time_nonneg

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.beta_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.beta_nonneg

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.eps_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.eps_pos

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.eps_le_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.eps_le_half

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.slots_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.slots_pos

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.mesh

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.freeze' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.freeze

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.cayley

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.hermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.hermitian

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.row

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.col

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.path_hermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.path_hermitian

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.lipschitz

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.sample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.sample

/-- info: 'TimeDependentHamiltonianLowerBound.UniformHyp.budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.UniformHyp.budget

/-- info: 'TimeDependentHamiltonianLowerBound.MeshHyp.intervals_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshHyp.intervals_pos

/-- info: 'TimeDependentHamiltonianLowerBound.MeshHyp.eta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshHyp.eta_pos

/-- info: 'TimeDependentHamiltonianLowerBound.MeshHyp.time_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshHyp.time_pos

/-- info: 'TimeDependentHamiltonianLowerBound.MeshHyp.eps_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshHyp.eps_pos

/-- info: 'TimeDependentHamiltonianLowerBound.MeshHyp.eps_le_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshHyp.eps_le_half

/-- info: 'TimeDependentHamiltonianLowerBound.MeshHyp.slots_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshHyp.slots_pos

/-- info: 'TimeDependentHamiltonianLowerBound.MeshHyp.isMesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshHyp.isMesh

/-- info: 'TimeDependentHamiltonianLowerBound.MeshHyp.clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshHyp.clock

/-- info: 'TimeDependentHamiltonianLowerBound.MeshHyp.cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshHyp.cayley

/-- info: 'TimeDependentHamiltonianLowerBound.MeshHyp.refine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshHyp.refine

/-- info: 'TimeDependentHamiltonianLowerBound.MeshHyp.hermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshHyp.hermitian

/-- info: 'TimeDependentHamiltonianLowerBound.MeshHyp.row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshHyp.row

/-- info: 'TimeDependentHamiltonianLowerBound.MeshHyp.col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshHyp.col

/-- info: 'TimeDependentHamiltonianLowerBound.MeshPath.hermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshPath.hermitian

/-- info: 'TimeDependentHamiltonianLowerBound.MeshPath.integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshPath.integrable

/-- info: 'TimeDependentHamiltonianLowerBound.MeshPath.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.MeshPath.certificate

/-- info: 'TimeDependentHamiltonianLowerBound.IntegrablePath.hermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.IntegrablePath.hermitian

/-- info: 'TimeDependentHamiltonianLowerBound.IntegrablePath.integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.IntegrablePath.integrable

/-- info: 'TimeDependentHamiltonianLowerBound.IntegrablePath.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.IntegrablePath.certificate

/-! ### Normal form and Boolean certificates of the released oracles (`Access`) -/

/-- info: 'TimeDependentHamiltonianLowerBound.isWrap_timeWrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.isWrap_timeWrap

/-- info: 'TimeDependentHamiltonianLowerBound.isWrap_alignedWrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.isWrap_alignedWrap

/-- info: 'TimeDependentHamiltonianLowerBound.sampled_eq_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.sampled_eq_wrap

/-- info: 'TimeDependentHamiltonianLowerBound.aligned_eq_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.aligned_eq_wrap

/-- info: 'TimeDependentHamiltonianLowerBound.sampled_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.sampled_normal_form

/-- info: 'TimeDependentHamiltonianLowerBound.aligned_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.aligned_normal_form

/-- info: 'TimeDependentHamiltonianLowerBound.uniform_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.uniform_normal_form

/-- info: 'TimeDependentHamiltonianLowerBound.mesh_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.mesh_normal_form

/-- info: 'TimeDependentHamiltonianLowerBound.aligned_oracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.aligned_oracle_unitary

/-- info: 'TimeDependentHamiltonianLowerBound.time_sampled_implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.time_sampled_implementsOn

/-- info: 'TimeDependentHamiltonianLowerBound.mixed_sampled_implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.mixed_sampled_implementsOn

/-- info: 'TimeDependentHamiltonianLowerBound.precision_sampled_implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.precision_sampled_implementsOn

/-! ### Theorem `hsl:thm:main` over the released time-dependent oracles (`Release`) -/

/-- info: 'TimeDependentHamiltonianLowerBound.time_sampled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.time_sampled

/-- info: 'TimeDependentHamiltonianLowerBound.mixed_sampled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.mixed_sampled

/-- info: 'TimeDependentHamiltonianLowerBound.precision_sampled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.precision_sampled

/-- info: 'TimeDependentHamiltonianLowerBound.main_max_sampled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.main_max_sampled

/-- info: 'TimeDependentHamiltonianLowerBound.main_max_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.main_max_uniform

/-- info: 'TimeDependentHamiltonianLowerBound.main_max_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.main_max_mesh

/-- info: 'TimeDependentHamiltonianLowerBound.main_max_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.main_max_integrable

/-! ### Admissible time-dependent oracles (`Adaptive`) -/

/-- info: 'TimeDependentHamiltonianLowerBound.nativeCall_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.nativeCall_conj

/-- info: 'TimeDependentHamiltonianLowerBound.admissible_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.admissible_conj

/-- info: 'TimeDependentHamiltonianLowerBound.coherentAccess_constData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.coherentAccess_constData

/-- info: 'TimeDependentHamiltonianLowerBound.admissible_coherentAccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.admissible_coherentAccess

/-- info: 'TimeDependentHamiltonianLowerBound.admissible_callFamily_coherentAccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.admissible_callFamily_coherentAccess

/-- info: 'TimeDependentHamiltonianLowerBound.admissible_of_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.admissible_of_normal_form

/-- info: 'TimeDependentHamiltonianLowerBound.admissible_sampledOracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.admissible_sampledOracle

/-- info: 'TimeDependentHamiltonianLowerBound.admissible_aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.admissible_aligned

/-- info: 'TimeDependentHamiltonianLowerBound.admissible_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.admissible_uniform

/-- info: 'TimeDependentHamiltonianLowerBound.admissible_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.admissible_mesh

/-! ### Theorem `hsl:thm:main` for adaptive algorithms (`Trees`) -/

/-- info: 'TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff

/-- info: 'TimeDependentHamiltonianLowerBound.main_max_tree_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.main_max_tree_access

/-- info: 'TimeDependentHamiltonianLowerBound.main_max_tree_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.main_max_tree_calls

/-- info: 'TimeDependentHamiltonianLowerBound.main_max_tree_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.main_max_tree_uniform

/-- info: 'TimeDependentHamiltonianLowerBound.main_max_tree_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.main_max_tree_mesh

/-! ### Theorem `hsl:thm:main` for the time-dependent classes (`ClassBound`) -/

/-- info: 'TimeDependentHamiltonianLowerBound.uniform_class_members' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.uniform_class_members

/-- info: 'TimeDependentHamiltonianLowerBound.uniform_class_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.uniform_class_max

/-- info: 'TimeDependentHamiltonianLowerBound.mesh_class_members' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.mesh_class_members

/-- info: 'TimeDependentHamiltonianLowerBound.mesh_class_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.mesh_class_max

/-- info: 'TimeDependentHamiltonianLowerBound.integrable_class_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.integrable_class_max

/-! ### Bracket for the released time-dependent simulators (`Theta`) -/

/-- info: 'TimeDependentHamiltonianLowerBound.exists_uniformSimulates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.exists_uniformSimulates

/-- info: 'TimeDependentHamiltonianLowerBound.exists_meshSimulates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.exists_meshSimulates

/-- info: 'TimeDependentHamiltonianLowerBound.count_shape_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.count_shape_one

/-- info: 'TimeDependentHamiltonianLowerBound.uniform_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.uniform_theta

/-- info: 'TimeDependentHamiltonianLowerBound.uniform_theta_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.uniform_theta_bracket

/-- info: 'TimeDependentHamiltonianLowerBound.mesh_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.mesh_theta

/-- info: 'TimeDependentHamiltonianLowerBound.mesh_theta_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.mesh_theta_bracket

/-! ### The hypotheses of the lower bounds can be met (`NonVacuity`) -/

/-- info: 'TimeDependentHamiltonianLowerBound.uniform_class_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.uniform_class_nonvacuous

/-- info: 'TimeDependentHamiltonianLowerBound.mesh_class_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.mesh_class_nonvacuous

/-- info: 'TimeDependentHamiltonianLowerBound.integrable_class_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.integrable_class_nonvacuous

/-- info: 'TimeDependentHamiltonianLowerBound.single_tree_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.single_tree_hyps

/-- info: 'TimeDependentHamiltonianLowerBound.eval_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.eval_cast

/-- info: 'TimeDependentHamiltonianLowerBound.unitSlot_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.unitSlot_fiber

/-- info: 'TimeDependentHamiltonianLowerBound.access_of_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.access_of_uniform

/-- info: 'TimeDependentHamiltonianLowerBound.boolEmbed_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.boolEmbed_apply

/-- info: 'TimeDependentHamiltonianLowerBound.boolEmbed_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.boolEmbed_isometry

/-- info: 'TimeDependentHamiltonianLowerBound.eval_plainLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.eval_plainLift

/-- info: 'TimeDependentHamiltonianLowerBound.calls_of_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentHamiltonianLowerBound.calls_of_access
