import IntegrablePathSimulation.Statements

set_option autoImplicit false

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem of the time-dependent
simulation of integrable Hermitian paths (75 theorems), in module order. Every report lists
`propext`, `Classical.choice` and `Quot.sound`. -/

/-! ### Integral equations and Grönwall's inequality (`IntegrablePathSimulation.Calculus`) -/

/-! #### `IntegrablePathSimulation.Calculus.Absolute` -/

/-- info: 'IntegrablePathSimulation.Calculus.absolutelyContinuousOnInterval_of_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Calculus.absolutelyContinuousOnInterval_of_dist_le

/-- info: 'IntegrablePathSimulation.Calculus.dist_integral_le_dist_integral_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Calculus.dist_integral_le_dist_integral_norm

/-- info: 'IntegrablePathSimulation.Calculus.absolutelyContinuousOnInterval_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Calculus.absolutelyContinuousOnInterval_primitive

/-- info: 'IntegrablePathSimulation.Calculus.eq_add_integral_of_ae_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Calculus.eq_add_integral_of_ae_hasDerivAt

/-- info: 'IntegrablePathSimulation.Calculus.absolutelyContinuousOnInterval_of_eq_add_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Calculus.absolutelyContinuousOnInterval_of_eq_add_integral

/-- info: 'IntegrablePathSimulation.Calculus.continuousOn_of_eq_add_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Calculus.continuousOn_of_eq_add_integral

/-- info: 'IntegrablePathSimulation.Calculus.ae_hasDerivAt_of_eq_add_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Calculus.ae_hasDerivAt_of_eq_add_integral

/-! #### `IntegrablePathSimulation.Calculus.Product` -/

/-- info: 'IntegrablePathSimulation.Calculus.norm_sub_le_integral_norm_of_eq_add_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Calculus.norm_sub_le_integral_norm_of_eq_add_integral

/-- info: 'IntegrablePathSimulation.Calculus.intervalIntegrable_mul_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Calculus.intervalIntegrable_mul_add

/-- info: 'IntegrablePathSimulation.Calculus.mul_eq_add_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Calculus.mul_eq_add_integral

/-- info: 'IntegrablePathSimulation.Calculus.integral_mul_primitive_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Calculus.integral_mul_primitive_pow

/-! #### `IntegrablePathSimulation.Calculus.Gronwall` -/

/-- info: 'IntegrablePathSimulation.Calculus.tendsto_sum_pow_div_factorial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Calculus.tendsto_sum_pow_div_factorial

/-- info: 'IntegrablePathSimulation.Calculus.le_mul_exp_of_le_add_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Calculus.le_mul_exp_of_le_add_integral

/-- info: 'IntegrablePathSimulation.Calculus.eq_zero_of_le_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Calculus.eq_zero_of_le_integral

/-- info: 'IntegrablePathSimulation.Calculus.eq_zero_of_norm_le_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Calculus.eq_zero_of_norm_le_integral

/-! ### Propagators of integrable paths (`IntegrablePathSimulation.Propagator`) -/

/-! #### `IntegrablePathSimulation.Propagator.Basic` -/

/-- info: 'IntegrablePathSimulation.Propagator.SolvesIntegralOn.intervalIntegrable_rhs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.SolvesIntegralOn.intervalIntegrable_rhs

/-- info: 'IntegrablePathSimulation.Propagator.SolvesIntegralOn.absolutelyContinuousOnInterval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.SolvesIntegralOn.absolutelyContinuousOnInterval

/-- info: 'IntegrablePathSimulation.Propagator.SolvesIntegralOn.continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.SolvesIntegralOn.continuousOn

/-- info: 'IntegrablePathSimulation.Propagator.SolvesIntegralOn.ae_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.SolvesIntegralOn.ae_hasDerivAt

/-- info: 'IntegrablePathSimulation.Propagator.SolvesIntegralOn.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.SolvesIntegralOn.mono

/-- info: 'IntegrablePathSimulation.Propagator.SolvesIntegralOn.trans' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.SolvesIntegralOn.trans

/-- info: 'IntegrablePathSimulation.Propagator.SolvesIntegralOn.congr_ae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.SolvesIntegralOn.congr_ae

/-- info: 'IntegrablePathSimulation.Propagator.IsPropagator.solvesIntegralOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.IsPropagator.solvesIntegralOn

/-- info: 'IntegrablePathSimulation.Propagator.IsPropagator.continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.IsPropagator.continuousOn

/-! #### `IntegrablePathSimulation.Propagator.Existence` -/

/-- info: 'IntegrablePathSimulation.Propagator.picardTerm_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.picardTerm_continuousOn

/-- info: 'IntegrablePathSimulation.Propagator.intervalIntegrable_picardIntegrand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.intervalIntegrable_picardIntegrand

/-- info: 'IntegrablePathSimulation.Propagator.intervalIntegrable_zero_of_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.intervalIntegrable_zero_of_mem_Icc

/-- info: 'IntegrablePathSimulation.Propagator.norm_picardTerm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.norm_picardTerm_le

/-- info: 'IntegrablePathSimulation.Propagator.isPropagator_picardSeries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.isPropagator_picardSeries

/-- info: 'IntegrablePathSimulation.Propagator.exists_isPropagator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.exists_isPropagator

/-! #### `IntegrablePathSimulation.Propagator.Uniqueness` -/

/-- info: 'IntegrablePathSimulation.Propagator.SolvesIntegralOn.eqOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.SolvesIntegralOn.eqOn

/-- info: 'IntegrablePathSimulation.Propagator.IsPropagator.eqOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.IsPropagator.eqOn

/-- info: 'IntegrablePathSimulation.Propagator.existsUnique_isPropagator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.existsUnique_isPropagator

/-! #### `IntegrablePathSimulation.Propagator.Unitary` -/

/-- info: 'IntegrablePathSimulation.Propagator.exists_linearIsometry_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.exists_linearIsometry_star

/-- info: 'IntegrablePathSimulation.Propagator.star_intervalIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.star_intervalIntegral

/-- info: 'IntegrablePathSimulation.Propagator.intervalIntegrable_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.intervalIntegrable_star

/-- info: 'IntegrablePathSimulation.Propagator.star_neg_I_smul_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.star_neg_I_smul_mul

/-- info: 'IntegrablePathSimulation.Propagator.SolvesIntegralOn.intervalIntegrable_star_rhs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.SolvesIntegralOn.intervalIntegrable_star_rhs

/-- info: 'IntegrablePathSimulation.Propagator.SolvesIntegralOn.star_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.SolvesIntegralOn.star_eq

/-- info: 'IntegrablePathSimulation.Propagator.SolvesIntegralOn.star_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.SolvesIntegralOn.star_mul_self

/-- info: 'IntegrablePathSimulation.Propagator.SolvesIntegralOn.norm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.SolvesIntegralOn.norm_apply

/-- info: 'IntegrablePathSimulation.Propagator.SolvesIntegralOn.norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.SolvesIntegralOn.norm_le_one

/-- info: 'IntegrablePathSimulation.Propagator.IsPropagator.star_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.IsPropagator.star_mul_self

/-- info: 'IntegrablePathSimulation.Propagator.IsPropagator.mul_star_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.IsPropagator.mul_star_self

/-- info: 'IntegrablePathSimulation.Propagator.IsPropagator.isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.IsPropagator.isUnitary

/-- info: 'IntegrablePathSimulation.Propagator.IsPropagator.norm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.IsPropagator.norm_apply

/-- info: 'IntegrablePathSimulation.Propagator.IsPropagator.norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.IsPropagator.norm_le_one

/-! #### `IntegrablePathSimulation.Propagator.Duhamel` -/

/-- info: 'IntegrablePathSimulation.Propagator.SolvesIntegralOn.duhamel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.SolvesIntegralOn.duhamel

/-- info: 'IntegrablePathSimulation.Propagator.SolvesIntegralOn.window_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.SolvesIntegralOn.window_error

/-- info: 'IntegrablePathSimulation.Propagator.IsPropagator.mesh_error_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.IsPropagator.mesh_error_integral

/-- info: 'IntegrablePathSimulation.Propagator.IsPropagator.refined_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.IsPropagator.refined_error

/-! #### `IntegrablePathSimulation.Propagator.Classical` -/

/-- info: 'IntegrablePathSimulation.Propagator.solvesIntegralOn_of_solvesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.solvesIntegralOn_of_solvesOn

/-- info: 'IntegrablePathSimulation.Propagator.isPropagator_of_solvesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.isPropagator_of_solvesOn

/-- info: 'IntegrablePathSimulation.Propagator.pieceIndex_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.pieceIndex_lt

/-- info: 'IntegrablePathSimulation.Propagator.pieceIndex_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.pieceIndex_eq

/-- info: 'IntegrablePathSimulation.Propagator.mem_Icc_pieceIndex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.mem_Icc_pieceIndex

/-- info: 'IntegrablePathSimulation.Propagator.glue_eq_of_mem_Ico' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.glue_eq_of_mem_Ico

/-- info: 'IntegrablePathSimulation.Propagator.glue_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.glue_ae_eq

/-- info: 'IntegrablePathSimulation.Propagator.intervalIntegrable_glue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.intervalIntegrable_glue

/-- info: 'IntegrablePathSimulation.Propagator.solvesIntegralOn_glue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.solvesIntegralOn_glue

/-- info: 'IntegrablePathSimulation.Propagator.isPropagator_glue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.isPropagator_glue

/-! #### `IntegrablePathSimulation.Propagator.Released` -/

/-- info: 'IntegrablePathSimulation.Propagator.duhamel_integral_of_solvesOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.duhamel_integral_of_solvesOn

/-- info: 'IntegrablePathSimulation.Propagator.ae_star_glue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.ae_star_glue

/-- info: 'IntegrablePathSimulation.Propagator.sum_integral_glue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.sum_integral_glue

/-- info: 'IntegrablePathSimulation.Propagator.mesh_error_integral_piecewise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.mesh_error_integral_piecewise

/-- info: 'IntegrablePathSimulation.Propagator.refined_error_piecewise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Propagator.refined_error_piecewise

/-! ### Theorem `hs:thm:time` for integrable paths (`Hamiltonian`, `Coherent`, `BlockEncoding`) -/

/-! #### `IntegrablePathSimulation.Hamiltonian.Theorem` -/

/-- info: 'IntegrablePathSimulation.Hamiltonian.simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Hamiltonian.simulation

/-! #### `IntegrablePathSimulation.Hamiltonian.Corollaries` -/

/-- info: 'IntegrablePathSimulation.Hamiltonian.simulation_piecewise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Hamiltonian.simulation_piecewise

/-- info: 'IntegrablePathSimulation.Hamiltonian.simulation_classical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Hamiltonian.simulation_classical

/-- info: 'IntegrablePathSimulation.Hamiltonian.simulation_dyson' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Hamiltonian.simulation_dyson

/-- info: 'IntegrablePathSimulation.Hamiltonian.simulation_with_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Hamiltonian.simulation_with_reference

/-! #### `IntegrablePathSimulation.Coherent.Theorem` -/

/-- info: 'IntegrablePathSimulation.Coherent.coherent_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Coherent.coherent_windows

/-! #### `IntegrablePathSimulation.Coherent.Corollaries` -/

/-- info: 'IntegrablePathSimulation.Coherent.coherent_windows_piecewise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.Coherent.coherent_windows_piecewise

/-! #### `IntegrablePathSimulation.BlockEncoding.Theorem` -/

/-- info: 'IntegrablePathSimulation.BlockEncoding.simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.BlockEncoding.simulation

/-- info: 'IntegrablePathSimulation.BlockEncoding.simulation_piecewise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IntegrablePathSimulation.BlockEncoding.simulation_piecewise
