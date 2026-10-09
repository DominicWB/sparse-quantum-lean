import TimeDependentODE.Corollaries

/-! ## Axiom audits

Each audit fails to compile if the declaration depends on an axiom other than
`propext`, `Classical.choice` and `Quot.sound`. The audits cover every
theorem of the time-dependent ODE library, beginning with the final theorem
and its corollaries. -/

/-! ### Final theorem and corollaries -/

/-- info: 'SparseHamiltonian.TimeDependentODE.solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.solver

/-- info: 'SparseHamiltonian.TimeDependentODE.retarget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.retarget

/-- info: 'SparseHamiltonian.TimeDependentODE.mesh_conditions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.mesh_conditions

/-- info: 'SparseHamiltonian.TimeDependentODE.discretisation_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.discretisation_eq

/-! ### Public source coefficients, sampled families and the discretised target -/

/-- info: 'SparseHamiltonian.TimeDependentODE.PublicSource.sum_norms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.PublicSource.sum_norms

/-- info: 'SparseHamiltonian.TimeDependentODE.PublicSource.norms_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.PublicSource.norms_nonneg

/-- info: 'SparseHamiltonian.TimeDependentODE.PublicSource.coefficients_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.PublicSource.coefficients_mass

/-- info: 'SparseHamiltonian.TimeDependentODE.PublicSource.mass_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.PublicSource.mass_eq

/-- info: 'SparseHamiltonian.TimeDependentODE.PublicSource.actual_coefficients_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.PublicSource.actual_coefficients_eq

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.generator_accretive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.generator_accretive

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.generator_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.generator_norm_le

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.dissipative_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.dissipative_norm_le

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.decomposition

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.slotDurations_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.slotDurations_nonneg

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.slotDurations_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.slotDurations_le

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.family_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.family_analyticAt

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.family_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.family_norm_le_one

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.family_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.family_lipschitz

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.family_neg_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.family_neg_I

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.branchEvolution_eq_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.branchEvolution_eq_family

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.padded_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.padded_sum

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.target_eq_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.target_eq_recurrence

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.target_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.target_norm_le

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.sources_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.sources_norm

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.unitDirection_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.unitDirection_smul

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.target_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.target_budget

/-- info: 'SparseHamiltonian.TimeDependentODE.Sampling.discretisation_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Sampling.discretisation_error

/-! ### Gaussian LCHS for contractive entire families -/

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.differentiable_of_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.differentiable_of_analyticAt

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.continuous_of_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.continuous_of_analyticAt

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.real_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.real_continuous

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.real_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.real_norm_le_one

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.shifted_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.shifted_norm_le_one

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.integrand_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.integrand_continuous

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.integrand_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.integrand_integrable

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.integrand_integrable_of_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.integrand_integrable_of_one_le

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.topWeighted_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.topWeighted_continuous

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.top_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.top_integrable

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.shiftedWeighted_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.shiftedWeighted_continuous

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.shiftedWeighted_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.shiftedWeighted_norm_le

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.shiftedWeighted_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.shiftedWeighted_integrable

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.shifted_integral_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.shifted_integral_norm_le

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.vertical_weighted_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.vertical_weighted_norm_le

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.weightedRegular_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.weightedRegular_analyticAt

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.weightedRegular_analyticOnNhd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.weightedRegular_analyticOnNhd

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.weightedRegular_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.weightedRegular_differentiableOn

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.weighted_eq_poleQuotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.weighted_eq_poleQuotient

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.weightedRegular_neg_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.weightedRegular_neg_I

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.weighted_pole_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.weighted_pole_decomposition

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.regularized_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.regularized_differentiableOn

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.regularized_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.regularized_norm_le

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.horizontal_difference_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.horizontal_difference_norm_le

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.horizontal_difference_tendsto_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.horizontal_difference_tendsto_zero

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.regularized_line_continuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.regularized_line_continuous

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.line_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.line_decomposition

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.horizontal_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.horizontal_decomposition

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.top_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.top_decomposition

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.shifted_decomposition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.shifted_decomposition

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.horizontal_difference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.horizontal_difference

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.top_integral_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.top_integral_tendsto

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.shifted_integral_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.shifted_integral_tendsto

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.integral_difference_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.integral_difference_tendsto

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.residue_normalization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.residue_normalization

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.finite_difference_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.finite_difference_tendsto

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.integral_difference_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.integral_difference_eq

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.full_line_error_eq_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.full_line_error_eq_residual

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.full_line_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.full_line_error

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.truncated_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.truncated_error

/-! ### Ordered LCHS products and the public Gaussian table -/

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.productFamily_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.productFamily_zero

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.productFamily_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.productFamily_succ

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.productFamily_analyticAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.productFamily_analyticAt

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.productFamily_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.productFamily_norm_le_one

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.productFamily_neg_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.productFamily_neg_I

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.productFamily_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.productFamily_ofReal

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.productFamily_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.productFamily_lipschitz

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.weighted_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.weighted_lipschitz

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.weightedLipschitz_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.weightedLipschitz_nonneg

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.table_sum_eq_uniformSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.table_sum_eq_uniformSum

/-- info: 'SparseHamiltonian.TimeDependentODE.GaussianLCHS.table_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.GaussianLCHS.table_certificate

/-! ### Coherent sampled-time native layer and SELECT -/

/-- info: 'SparseHamiltonian.TimeDependentODE.labelOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.labelOracle_unitary

/-- info: 'SparseHamiltonian.TimeDependentODE.compileLabel_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.compileLabel_count

/-- info: 'SparseHamiltonian.TimeDependentODE.compileLabel_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.compileLabel_cost

/-- info: 'SparseHamiltonian.TimeDependentODE.compileLabel_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.compileLabel_eval

/-- info: 'SparseHamiltonian.TimeDependentODE.slotPlace_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.slotPlace_apply

/-- info: 'SparseHamiltonian.TimeDependentODE.schedule_branch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.schedule_branch

/-- info: 'SparseHamiltonian.TimeDependentODE.schedule_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.schedule_count

/-- info: 'SparseHamiltonian.TimeDependentODE.schedule_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.schedule_cost

/-- info: 'SparseHamiltonian.TimeDependentODE.cayleyOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.cayleyOracle_unitary

/-- info: 'SparseHamiltonian.TimeDependentODE.cayleyProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.cayleyProgram_count

/-- info: 'SparseHamiltonian.TimeDependentODE.cayleyProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.cayleyProgram_cost

/-- info: 'SparseHamiltonian.TimeDependentODE.coherentClean_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.coherentClean_apply

/-- info: 'SparseHamiltonian.TimeDependentODE.cayleyProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.cayleyProgram_intertwines

/-- info: 'SparseHamiltonian.TimeDependentODE.layout_symm_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.layout_symm_single

/-- info: 'SparseHamiltonian.TimeDependentODE.valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.valid

/-- info: 'SparseHamiltonian.TimeDependentODE.oracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.oracle_unitary

/-- info: 'SparseHamiltonian.TimeDependentODE.program_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.program_count

/-- info: 'SparseHamiltonian.TimeDependentODE.implementsOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.implementsOn

/-- info: 'SparseHamiltonian.TimeDependentODE.Select.evolution_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Select.evolution_diagonal

/-- info: 'SparseHamiltonian.TimeDependentODE.Select.evolution_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Select.evolution_congr

/-- info: 'SparseHamiltonian.TimeDependentODE.Select.actions_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Select.actions_eq

/-- info: 'SparseHamiltonian.TimeDependentODE.Select.select_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Select.select_core

/-- info: 'SparseHamiltonian.TimeDependentODE.Select.step_le_quarter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Select.step_le_quarter

/-- info: 'SparseHamiltonian.TimeDependentODE.Select.count_le_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Select.count_le_shape

/-- info: 'SparseHamiltonian.TimeDependentODE.Select.exists_native_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Select.exists_native_select

/-- info: 'SparseHamiltonian.TimeDependentODE.Select.alignedOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Select.alignedOracle_unitary

/-- info: 'SparseHamiltonian.TimeDependentODE.Select.select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.Select.select

/-! ### Label-dependent sources, amplification and native coordinates -/

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.forcing_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.forcing_eq

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.forcing_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.forcing_unitary

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.combined_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.combined_unitary

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.combined_eq_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.combined_eq_diagonal

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.combined_inputEmbedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.combined_inputEmbedding

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.sourceOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.sourceOracle_unitary

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.oracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.oracle_unitary

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.program_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.program_unitary

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.program_state' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.program_state

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.decoded_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.decoded_eq

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.program_matrix_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.program_matrix_cost

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.program_source_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.program_source_cost

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.program_source_total_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.program_source_total_cost

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.compiled_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.compiled_geometry

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.counted_source_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.counted_source_certificate

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.sourceFamily_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.sourceFamily_unitary

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.primitive_source_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.primitive_source_certificate

/-- info: 'SparseHamiltonian.TimeDependentODE.SourceTD.logicalTrials_eq_publicLogicalTrials' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SourceTD.logicalTrials_eq_publicLogicalTrials

/-- info: 'SparseHamiltonian.TimeDependentODE.NativeSource.matrixOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.NativeSource.matrixOracle_unitary

/-- info: 'SparseHamiltonian.TimeDependentODE.NativeSource.matrix_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.NativeSource.matrix_valid

/-- info: 'SparseHamiltonian.TimeDependentODE.NativeSource.input_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.NativeSource.input_isometry

/-- info: 'SparseHamiltonian.TimeDependentODE.NativeSource.physicalOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.NativeSource.physicalOracle_unitary

/-- info: 'SparseHamiltonian.TimeDependentODE.NativeSource.coefficient_trial_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.NativeSource.coefficient_trial_certificate

/-! ### Continuous problem, discretisation and existence -/

/-- info: 'SparseHamiltonian.TimeDependentODE.SolvesODE.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SolvesODE.mono

/-- info: 'SparseHamiltonian.TimeDependentODE.SolvesODE.continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SolvesODE.continuousOn

/-- info: 'SparseHamiltonian.TimeDependentODE.accretive_iff_dissipative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.accretive_iff_dissipative

/-- info: 'SparseHamiltonian.TimeDependentODE.accretive_exp_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.accretive_exp_norm_le_one

/-- info: 'SparseHamiltonian.TimeDependentODE.accretive_exp_sub_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.accretive_exp_sub_norm_le

/-- info: 'SparseHamiltonian.TimeDependentODE.one_sub_exp_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.one_sub_exp_norm_le

/-- info: 'SparseHamiltonian.TimeDependentODE.SolvesODE.hasDerivWithinAt_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SolvesODE.hasDerivWithinAt_norm_sq

/-- info: 'SparseHamiltonian.TimeDependentODE.SolvesODE.norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.SolvesODE.norm_le

/-- info: 'SparseHamiltonian.TimeDependentODE.exists_local_propagator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.exists_local_propagator

/-- info: 'SparseHamiltonian.TimeDependentODE.exists_local_forced' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.exists_local_forced

/-- info: 'SparseHamiltonian.TimeDependentODE.exists_local_solvesODE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.exists_local_solvesODE

/-- info: 'SparseHamiltonian.TimeDependentODE.exists_solvesODE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.exists_solvesODE

/-- info: 'SparseHamiltonian.TimeDependentODE.continuousOn_of_norm_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.continuousOn_of_norm_sub_le

/-- info: 'SparseHamiltonian.TimeDependentODE.exists_solvesODE_of_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.exists_solvesODE_of_lipschitz

/-- info: 'SparseHamiltonian.TimeDependentODE.recurrence_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.recurrence_zero

/-- info: 'SparseHamiltonian.TimeDependentODE.recurrence_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.recurrence_succ

/-- info: 'SparseHamiltonian.TimeDependentODE.mask_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.mask_of_le

/-- info: 'SparseHamiltonian.TimeDependentODE.mask_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.mask_of_lt

/-- info: 'SparseHamiltonian.TimeDependentODE.mask_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.mask_nonneg

/-- info: 'SparseHamiltonian.TimeDependentODE.hasDerivWithinAt_clm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.hasDerivWithinAt_clm_apply

/-- info: 'SparseHamiltonian.TimeDependentODE.step_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.step_error

/-- info: 'SparseHamiltonian.TimeDependentODE.mesh_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.mesh_error

/-- info: 'SparseHamiltonian.TimeDependentODE.maskedPropagator_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.maskedPropagator_norm_le_one

/-- info: 'SparseHamiltonian.TimeDependentODE.maskedPropagator_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.maskedPropagator_of_le

/-- info: 'SparseHamiltonian.TimeDependentODE.maskedPropagator_succ_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.maskedPropagator_succ_of_le

/-- info: 'SparseHamiltonian.TimeDependentODE.recurrence_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.TimeDependentODE.recurrence_eq_sum
