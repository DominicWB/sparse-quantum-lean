import SparseLinearSystems.All


/-! Checked axiom dependencies for every theorem of the linear-system library,
in module order. Each requires exactly `propext`, `Classical.choice` and
`Quot.sound`. -/

/-! ### `SparseLinearSystems.Foundations.Cayley` -/

/-- info: 'SparseLinearSystems.Cayley.resolventAtOne_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cayley.resolventAtOne_factor

/-- info: 'SparseLinearSystems.Cayley.one_sub_cayleyAction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cayley.one_sub_cayleyAction

/-- info: 'SparseLinearSystems.Cayley.one_sub_cayleyAction_mul_resolventAtOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cayley.one_sub_cayleyAction_mul_resolventAtOne

/-- info: 'SparseLinearSystems.Cayley.resolventAtOne_mul_one_sub_cayleyAction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cayley.resolventAtOne_mul_one_sub_cayleyAction

/-- info: 'SparseLinearSystems.Cayley.resolventAtOne_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cayley.resolventAtOne_gram

/-- info: 'SparseLinearSystems.Cayley.cayleyAction_star_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cayley.cayleyAction_star_mul_self

/-! ### `SparseLinearSystems.Foundations.Regularization` -/

/-- info: 'SparseLinearSystems.Regularization.dilation_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Regularization.dilation_square

/-- info: 'SparseLinearSystems.Regularization.dilation_inverse_on_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Regularization.dilation_inverse_on_left

/-- info: 'SparseLinearSystems.Regularization.signedDiagonal_exchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Regularization.signedDiagonal_exchange

/-- info: 'SparseLinearSystems.Regularization.exchange_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Regularization.exchange_square

/-- info: 'SparseLinearSystems.Regularization.signedDiagonal_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Regularization.signedDiagonal_square

/-- info: 'SparseLinearSystems.Regularization.regularized_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Regularization.regularized_square

/-- info: 'SparseLinearSystems.Regularization.regularization_weight_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Regularization.regularization_weight_identity

/-- info: 'SparseLinearSystems.Regularization.regularized_real_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Regularization.regularized_real_square

/-! ### `SparseLinearSystems.Foundations.Augmentation` -/

/-- info: 'SparseLinearSystems.Augmentation.column_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmentation.column_apply

/-- info: 'SparseLinearSystems.Augmentation.column_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmentation.column_surjective

/-- info: 'SparseLinearSystems.Augmentation.parameter_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmentation.parameter_apply

/-- info: 'SparseLinearSystems.Augmentation.parameter_eq_smul_generator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmentation.parameter_eq_smul_generator

/-- info: 'SparseLinearSystems.Augmentation.generator_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmentation.generator_ne_zero

/-- info: 'SparseLinearSystems.Augmentation.column_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmentation.column_eq_zero_iff

/-- info: 'SparseLinearSystems.Augmentation.column_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmentation.column_parameter

/-- info: 'SparseLinearSystems.Augmentation.column_generator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmentation.column_generator

/-- info: 'SparseLinearSystems.Augmentation.parameter_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmentation.parameter_injective

/-- info: 'SparseLinearSystems.Augmentation.kernel_parameterization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmentation.kernel_parameterization

/-- info: 'SparseLinearSystems.Augmentation.kernel_unique_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmentation.kernel_unique_parameter

/-- info: 'SparseLinearSystems.Augmentation.ker_eq_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmentation.ker_eq_range

/-- info: 'SparseLinearSystems.Augmentation.ker_eq_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmentation.ker_eq_span

/-- info: 'SparseLinearSystems.Augmentation.kernelEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmentation.kernelEquiv_apply

/-- info: 'SparseLinearSystems.Augmentation.withNormGuess_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmentation.withNormGuess_apply

/-- info: 'SparseLinearSystems.Augmentation.withNormGuess_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmentation.withNormGuess_eq_zero_iff

/-! ### `SparseLinearSystems.Foundations.KernelWalk` -/

/-- info: 'SparseLinearSystems.KernelWalk.reflection_involutive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.KernelWalk.reflection_involutive

/-- info: 'SparseLinearSystems.KernelWalk.fixed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.KernelWalk.fixed_iff

/-- info: 'SparseLinearSystems.KernelWalk.two_compression_resolvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.KernelWalk.two_compression_resolvent

/-- info: 'SparseLinearSystems.KernelWalk.projection_lift_of_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.KernelWalk.projection_lift_of_kernel

/-- info: 'SparseLinearSystems.KernelWalk.fixed_lift_of_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.KernelWalk.fixed_lift_of_kernel

/-- info: 'SparseLinearSystems.KernelWalk.lift_reconstruct_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.KernelWalk.lift_reconstruct_fixed

/-- info: 'SparseLinearSystems.KernelWalk.kernel_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.KernelWalk.kernel_of_fixed

/-- info: 'SparseLinearSystems.KernelWalk.resolvent_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.KernelWalk.resolvent_eq

/-! ### `SparseLinearSystems.Foundations.GeometricBudget` -/

/-- info: 'SparseLinearSystems.GeometricBudget.dyadic_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.GeometricBudget.dyadic_sum

/-- info: 'SparseLinearSystems.GeometricBudget.dyadic_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.GeometricBudget.dyadic_sum_le

/-- info: 'SparseLinearSystems.GeometricBudget.weighted_dyadic_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.GeometricBudget.weighted_dyadic_sum

/-- info: 'SparseLinearSystems.GeometricBudget.weighted_dyadic_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.GeometricBudget.weighted_dyadic_sum_le

/-- info: 'SparseLinearSystems.GeometricBudget.stageCost_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.GeometricBudget.stageCost_eq

/-- info: 'SparseLinearSystems.GeometricBudget.stageCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.GeometricBudget.stageCost_le

/-- info: 'SparseLinearSystems.GeometricBudget.stageFailure_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.GeometricBudget.stageFailure_nonneg

/-- info: 'SparseLinearSystems.GeometricBudget.stageFailure_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.GeometricBudget.stageFailure_sum_le

/-- info: 'SparseLinearSystems.GeometricBudget.dyadic_bracket' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.GeometricBudget.dyadic_bracket

/-- info: 'SparseLinearSystems.GeometricBudget.sparse_stageCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.GeometricBudget.sparse_stageCost_le

/-! ### `SparseLinearSystems.Foundations.HilbertBlocks` -/

/-- info: 'SparseLinearSystems.HilbertBlocks.blockMap_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertBlocks.blockMap_apply

/-- info: 'SparseLinearSystems.HilbertBlocks.block_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertBlocks.block_comp

/-- info: 'SparseLinearSystems.HilbertBlocks.block_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertBlocks.block_mul

/-- info: 'SparseLinearSystems.HilbertBlocks.block_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertBlocks.block_identity

/-- info: 'SparseLinearSystems.HilbertBlocks.block_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertBlocks.block_adjoint

/-! ### `SparseLinearSystems.Foundations.RegularizationGap` -/

/-- info: 'SparseLinearSystems.RegularizationGap.square_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.RegularizationGap.square_nonneg

/-- info: 'SparseLinearSystems.RegularizationGap.gap_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.RegularizationGap.gap_nonneg

/-- info: 'SparseLinearSystems.RegularizationGap.gap_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.RegularizationGap.gap_sq

/-- info: 'SparseLinearSystems.RegularizationGap.square_rewrite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.RegularizationGap.square_rewrite

/-- info: 'SparseLinearSystems.RegularizationGap.reciprocal_square_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.RegularizationGap.reciprocal_square_le_one

/-- info: 'SparseLinearSystems.RegularizationGap.sigma_le_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.RegularizationGap.sigma_le_gap

/-- info: 'SparseLinearSystems.RegularizationGap.reciprocal_le_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.RegularizationGap.reciprocal_le_gap

/-- info: 'SparseLinearSystems.RegularizationGap.gap_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.RegularizationGap.gap_pos

/-- info: 'SparseLinearSystems.RegularizationGap.gap_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.RegularizationGap.gap_le_one

/-- info: 'SparseLinearSystems.RegularizationGap.gap_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.RegularizationGap.gap_bounds

/-- info: 'SparseLinearSystems.RegularizationGap.gap_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.RegularizationGap.gap_mono

/-- info: 'SparseLinearSystems.RegularizationGap.gap_halving' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.RegularizationGap.gap_halving

/-- info: 'SparseLinearSystems.RegularizationGap.terminal_gap_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.RegularizationGap.terminal_gap_le

/-- info: 'SparseLinearSystems.RegularizationGap.terminal_weight_le_sqrt_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.RegularizationGap.terminal_weight_le_sqrt_two

/-! ### `SparseLinearSystems.Foundations.HilbertRegularization` -/

/-- info: 'SparseLinearSystems.HilbertRegularization.weighted_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.weighted_apply

/-- info: 'SparseLinearSystems.HilbertRegularization.signedDiagonal_exchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.signedDiagonal_exchange

/-- info: 'SparseLinearSystems.HilbertRegularization.weighted_square_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.weighted_square_apply

/-- info: 'SparseLinearSystems.HilbertRegularization.regularized_square_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.regularized_square_apply

/-- info: 'SparseLinearSystems.HilbertRegularization.norm_real_smul_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.norm_real_smul_sq

/-- info: 'SparseLinearSystems.HilbertRegularization.dilation_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.dilation_apply

/-- info: 'SparseLinearSystems.HilbertRegularization.dilation_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.dilation_selfAdjoint

/-- info: 'SparseLinearSystems.HilbertRegularization.dilation_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.dilation_square

/-- info: 'SparseLinearSystems.HilbertRegularization.dilation_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.dilation_norm_sq

/-- info: 'SparseLinearSystems.HilbertRegularization.dilation_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.dilation_norm_le_one

/-- info: 'SparseLinearSystems.HilbertRegularization.dilation_lower_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.dilation_lower_sq

/-- info: 'SparseLinearSystems.HilbertRegularization.signedDiagonal_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.signedDiagonal_selfAdjoint

/-- info: 'SparseLinearSystems.HilbertRegularization.exchange_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.exchange_selfAdjoint

/-- info: 'SparseLinearSystems.HilbertRegularization.exchange_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.exchange_square

/-- info: 'SparseLinearSystems.HilbertRegularization.weighted_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.weighted_selfAdjoint

/-- info: 'SparseLinearSystems.HilbertRegularization.regularized_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.regularized_selfAdjoint

/-- info: 'SparseLinearSystems.HilbertRegularization.weighted_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.weighted_norm_sq

/-- info: 'SparseLinearSystems.HilbertRegularization.regularized_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.regularized_norm_sq

/-- info: 'SparseLinearSystems.HilbertRegularization.regularized_norm_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.regularized_norm_le_one

/-- info: 'SparseLinearSystems.HilbertRegularization.regularized_lower_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.regularized_lower_sq

/-- info: 'SparseLinearSystems.HilbertRegularization.regularized_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.regularized_lower

/-- info: 'SparseLinearSystems.HilbertRegularization.regularized_condition_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.regularized_condition_lower

/-- info: 'SparseLinearSystems.HilbertRegularization.regularized_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertRegularization.regularized_injective

/-! ### `SparseLinearSystems.Foundations.HilbertAugmentation` -/

/-- info: 'SparseLinearSystems.HilbertAugmentation.ray_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.ray_apply

/-- info: 'SparseLinearSystems.HilbertAugmentation.column_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.column_apply

/-- info: 'SparseLinearSystems.HilbertAugmentation.column_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.column_surjective

/-- info: 'SparseLinearSystems.HilbertAugmentation.column_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.column_eq_zero_iff

/-- info: 'SparseLinearSystems.HilbertAugmentation.parameter_eq_smul_generator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.parameter_eq_smul_generator

/-- info: 'SparseLinearSystems.HilbertAugmentation.generator_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.generator_ne_zero

/-- info: 'SparseLinearSystems.HilbertAugmentation.parameter_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.parameter_injective

/-- info: 'SparseLinearSystems.HilbertAugmentation.generator_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.generator_norm_sq

/-- info: 'SparseLinearSystems.HilbertAugmentation.generator_norm_sq_reciprocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.generator_norm_sq_reciprocal

/-- info: 'SparseLinearSystems.HilbertAugmentation.normalizedGenerator_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.normalizedGenerator_norm

/-- info: 'SparseLinearSystems.HilbertAugmentation.column_adjoint_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.column_adjoint_eq_zero_iff

/-- info: 'SparseLinearSystems.HilbertAugmentation.column_adjoint_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.column_adjoint_injective

/-- info: 'SparseLinearSystems.HilbertAugmentation.hamiltonian_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.hamiltonian_apply

/-- info: 'SparseLinearSystems.HilbertAugmentation.hamiltonian_selfadjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.hamiltonian_selfadjoint

/-- info: 'SparseLinearSystems.HilbertAugmentation.hamiltonian_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.hamiltonian_eq_zero_iff

/-- info: 'SparseLinearSystems.HilbertAugmentation.hamiltonian_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.hamiltonian_parameter

/-- info: 'SparseLinearSystems.HilbertAugmentation.hamiltonian_generator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.hamiltonian_generator

/-- info: 'SparseLinearSystems.HilbertAugmentation.hamiltonian_normalizedGenerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.hamiltonian_normalizedGenerator

/-- info: 'SparseLinearSystems.HilbertAugmentation.kernel_parameterization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.kernel_parameterization

/-- info: 'SparseLinearSystems.HilbertAugmentation.kernel_unique_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.kernel_unique_parameter

/-- info: 'SparseLinearSystems.HilbertAugmentation.kernel_eq_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentation.kernel_eq_span

/-! ### `SparseLinearSystems.Foundations.HilbertCayley` -/

/-- info: 'SparseLinearSystems.HilbertCayley.denominator_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertCayley.denominator_apply

/-- info: 'SparseLinearSystems.HilbertCayley.denominator_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertCayley.denominator_eq_zero

/-- info: 'SparseLinearSystems.HilbertCayley.denominator_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertCayley.denominator_injective

/-- info: 'SparseLinearSystems.HilbertCayley.resolvent_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertCayley.resolvent_inner

/-- info: 'SparseLinearSystems.HilbertCayley.resolvent_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertCayley.resolvent_norm_sq

/-- info: 'SparseLinearSystems.HilbertCayley.resolvent_norm_sq_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertCayley.resolvent_norm_sq_bounds

/-- info: 'SparseLinearSystems.HilbertCayley.denominator_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertCayley.denominator_surjective

/-- info: 'SparseLinearSystems.HilbertCayley.denominator_mul_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertCayley.denominator_mul_inverse

/-- info: 'SparseLinearSystems.HilbertCayley.inverse_mul_denominator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertCayley.inverse_mul_denominator

/-- info: 'SparseLinearSystems.HilbertCayley.cayley_star_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertCayley.cayley_star_mul_self

/-- info: 'SparseLinearSystems.HilbertCayley.cayley_norm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertCayley.cayley_norm_apply

/-- info: 'SparseLinearSystems.HilbertCayley.cayley_mul_star_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertCayley.cayley_mul_star_self

/-- info: 'SparseLinearSystems.HilbertCayley.one_sub_cayley_mul_resolvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertCayley.one_sub_cayley_mul_resolvent

/-- info: 'SparseLinearSystems.HilbertCayley.resolvent_mul_one_sub_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertCayley.resolvent_mul_one_sub_cayley

/-- info: 'SparseLinearSystems.HilbertCayley.cayley_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertCayley.cayley_unitary

/-! ### `SparseLinearSystems.Foundations.InputInverseBounds` -/

/-- info: 'SparseLinearSystems.InputInverseBounds.left_inverse_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.InputInverseBounds.left_inverse_lower

/-- info: 'SparseLinearSystems.InputInverseBounds.left_inverse_lower_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.InputInverseBounds.left_inverse_lower_sq

/-- info: 'SparseLinearSystems.InputInverseBounds.equiv_inverse_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.InputInverseBounds.equiv_inverse_mul

/-- info: 'SparseLinearSystems.InputInverseBounds.equiv_mul_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.InputInverseBounds.equiv_mul_inverse

/-- info: 'SparseLinearSystems.InputInverseBounds.equiv_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.InputInverseBounds.equiv_lower

/-- info: 'SparseLinearSystems.InputInverseBounds.equiv_lower_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.InputInverseBounds.equiv_lower_sq

/-- info: 'SparseLinearSystems.InputInverseBounds.equiv_adjoint_inverse_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.InputInverseBounds.equiv_adjoint_inverse_mul

/-- info: 'SparseLinearSystems.InputInverseBounds.equiv_adjoint_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.InputInverseBounds.equiv_adjoint_lower

/-- info: 'SparseLinearSystems.InputInverseBounds.equiv_adjoint_lower_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.InputInverseBounds.equiv_adjoint_lower_sq

/-- info: 'SparseLinearSystems.InputInverseBounds.dilation_lower_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.InputInverseBounds.dilation_lower_sq

/-- info: 'SparseLinearSystems.InputInverseBounds.regularized_dilation_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.InputInverseBounds.regularized_dilation_lower

/-- info: 'SparseLinearSystems.InputInverseBounds.regularized_dilation_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.InputInverseBounds.regularized_dilation_injective

/-- info: 'SparseLinearSystems.InputInverseBounds.regularized_dilation_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.InputInverseBounds.regularized_dilation_surjective

/-- info: 'SparseLinearSystems.InputInverseBounds.regularizedDilationEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.InputInverseBounds.regularizedDilationEquiv_apply

/-- info: 'SparseLinearSystems.InputInverseBounds.regularizedDilationEquiv_symm_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.InputInverseBounds.regularizedDilationEquiv_symm_norm_le

/-- info: 'SparseLinearSystems.InputInverseBounds.regularizedDilationEquiv_inverse_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.InputInverseBounds.regularizedDilationEquiv_inverse_norm_le

/-! ### `SparseLinearSystems.Foundations.HilbertAugmentationGap` -/

/-- info: 'SparseLinearSystems.HilbertAugmentationGap.firstEmbedding_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentationGap.firstEmbedding_apply

/-- info: 'SparseLinearSystems.HilbertAugmentationGap.columnRightInverse_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentationGap.columnRightInverse_apply

/-- info: 'SparseLinearSystems.HilbertAugmentationGap.column_comp_rightInverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentationGap.column_comp_rightInverse

/-- info: 'SparseLinearSystems.HilbertAugmentationGap.columnRightInverse_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentationGap.columnRightInverse_norm_le

/-- info: 'SparseLinearSystems.HilbertAugmentationGap.rightInverse_adjoint_comp_column_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentationGap.rightInverse_adjoint_comp_column_adjoint

/-- info: 'SparseLinearSystems.HilbertAugmentationGap.column_adjoint_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentationGap.column_adjoint_lower

/-- info: 'SparseLinearSystems.HilbertAugmentationGap.column_adjoint_lower_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentationGap.column_adjoint_lower_sq

/-- info: 'SparseLinearSystems.HilbertAugmentationGap.column_gram_rayleigh_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentationGap.column_gram_rayleigh_lower

/-- info: 'SparseLinearSystems.HilbertAugmentationGap.hamiltonian_nonzero_eigenvalue_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentationGap.hamiltonian_nonzero_eigenvalue_gap

/-- info: 'SparseLinearSystems.HilbertAugmentationGap.regularized_column_adjoint_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentationGap.regularized_column_adjoint_lower

/-- info: 'SparseLinearSystems.HilbertAugmentationGap.regularized_column_gram_rayleigh_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentationGap.regularized_column_gram_rayleigh_lower

/-- info: 'SparseLinearSystems.HilbertAugmentationGap.regularizedAugmentedHamiltonian_selfadjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentationGap.regularizedAugmentedHamiltonian_selfadjoint

/-- info: 'SparseLinearSystems.HilbertAugmentationGap.regularizedAugmentedHamiltonian_nonzero_eigenvalue_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentationGap.regularizedAugmentedHamiltonian_nonzero_eigenvalue_gap

/-- info: 'SparseLinearSystems.HilbertAugmentationGap.regularizedAugmentedHamiltonian_normalizedGenerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentationGap.regularizedAugmentedHamiltonian_normalizedGenerator

/-- info: 'SparseLinearSystems.HilbertAugmentationGap.regularizedAugmentedHamiltonian_kernel_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.HilbertAugmentationGap.regularizedAugmentedHamiltonian_kernel_unique

/-! ### `SparseLinearSystems.Foundations.AugmentedMoments` -/

/-- info: 'SparseLinearSystems.AugmentedMoments.sparse_regularization_weight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.AugmentedMoments.sparse_regularization_weight_le

/-- info: 'SparseLinearSystems.AugmentedMoments.reciprocal_square_le_sixty_four' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.AugmentedMoments.reciprocal_square_le_sixty_four

/-- info: 'SparseLinearSystems.AugmentedMoments.four_branch_moment_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.AugmentedMoments.four_branch_moment_le

/-- info: 'SparseLinearSystems.AugmentedMoments.sixty_six_over_two_fifty_six_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.AugmentedMoments.sixty_six_over_two_fifty_six_le_one

/-! ### `SparseLinearSystems.Foundations.FourBranchCompression` -/

/-- info: 'SparseLinearSystems.FourBranchCompression.embedding_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.FourBranchCompression.embedding_apply

/-- info: 'SparseLinearSystems.FourBranchCompression.embedding_adjoint_comp_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.FourBranchCompression.embedding_adjoint_comp_self

/-- info: 'SparseLinearSystems.FourBranchCompression.diagonal_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.FourBranchCompression.diagonal_apply

/-- info: 'SparseLinearSystems.FourBranchCompression.diagonal_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.FourBranchCompression.diagonal_mul

/-- info: 'SparseLinearSystems.FourBranchCompression.diagonal_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.FourBranchCompression.diagonal_adjoint

/-- info: 'SparseLinearSystems.FourBranchCompression.diagonal_selfadjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.FourBranchCompression.diagonal_selfadjoint

/-- info: 'SparseLinearSystems.FourBranchCompression.compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.FourBranchCompression.compression

/-- info: 'SparseLinearSystems.FourBranchCompression.secondCompression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.FourBranchCompression.secondCompression

/-- info: 'SparseLinearSystems.FourBranchCompression.diagonal_embedding_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.FourBranchCompression.diagonal_embedding_norm_sq

/-- info: 'SparseLinearSystems.FourBranchCompression.diagonal_embedding_norm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.FourBranchCompression.diagonal_embedding_norm_sq_le

/-- info: 'SparseLinearSystems.FourBranchCompression.augmented_moment_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.FourBranchCompression.augmented_moment_le_one

/-! ### `SparseLinearSystems.Spectral.Diagonal` -/

/-- info: 'SparseLinearSystems.Diagonal.inner_basis_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.inner_basis_apply

/-- info: 'SparseLinearSystems.Diagonal.inner_apply_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.inner_apply_diag

/-- info: 'SparseLinearSystems.Diagonal.inner_self_apply_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.inner_self_apply_diag

/-- info: 'SparseLinearSystems.Diagonal.re_inner_self_apply_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.re_inner_self_apply_diag

/-- info: 'SparseLinearSystems.Diagonal.adjoint_eq_of_diag_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.adjoint_eq_of_diag_real

/-- info: 'SparseLinearSystems.Diagonal.norm_sq_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.norm_sq_eq_sum

/-- info: 'SparseLinearSystems.Diagonal.mul_inverseOfInjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.mul_inverseOfInjective

/-- info: 'SparseLinearSystems.Diagonal.inverseOfInjective_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.inverseOfInjective_mul

/-- info: 'SparseLinearSystems.Diagonal.apply_inverseOfInjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.apply_inverseOfInjective

/-- info: 'SparseLinearSystems.Diagonal.inverseOfInjective_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.inverseOfInjective_apply

/-- info: 'SparseLinearSystems.Diagonal.inverse_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.inverse_unique

/-- info: 'SparseLinearSystems.Diagonal.isSymmetric_of_adjoint_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.isSymmetric_of_adjoint_eq

/-- info: 'SparseLinearSystems.Diagonal.apply_eigenBasis' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.apply_eigenBasis

/-- info: 'SparseLinearSystems.Diagonal.eigenBasis_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.eigenBasis_ne_zero

/-- info: 'SparseLinearSystems.Diagonal.abs_eigenValues_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.abs_eigenValues_le

/-- info: 'SparseLinearSystems.Diagonal.inertia_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.inertia_injective

/-- info: 'SparseLinearSystems.Diagonal.inertia_injective_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Diagonal.inertia_injective_neg

/-- info: 'SparseLinearSystems.prodExt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.prodExt

/-! ### `SparseLinearSystems.Spectral.UnitaryFilter` -/

/-- info: 'SparseLinearSystems.UnitaryFilter.Unitary.left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.Unitary.left

/-- info: 'SparseLinearSystems.UnitaryFilter.Unitary.right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.Unitary.right

/-- info: 'SparseLinearSystems.UnitaryFilter.Unitary.adjoint_comp_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.Unitary.adjoint_comp_self

/-- info: 'SparseLinearSystems.UnitaryFilter.Unitary.comp_adjoint_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.Unitary.comp_adjoint_self

/-- info: 'SparseLinearSystems.UnitaryFilter.Unitary.norm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.Unitary.norm_apply

/-- info: 'SparseLinearSystems.UnitaryFilter.Unitary.adjoint_apply_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.Unitary.adjoint_apply_apply

/-- info: 'SparseLinearSystems.UnitaryFilter.Unitary.apply_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.Unitary.apply_adjoint_apply

/-- info: 'SparseLinearSystems.UnitaryFilter.Unitary.pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.Unitary.pow

/-- info: 'SparseLinearSystems.UnitaryFilter.Unitary.norm_eigenvalue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.Unitary.norm_eigenvalue

/-- info: 'SparseLinearSystems.UnitaryFilter.Unitary.adjoint_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.Unitary.adjoint_eigen

/-- info: 'SparseLinearSystems.UnitaryFilter.mem_fixedSpace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.mem_fixedSpace

/-- info: 'SparseLinearSystems.UnitaryFilter.Unitary.adjoint_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.Unitary.adjoint_fixed

/-- info: 'SparseLinearSystems.UnitaryFilter.Unitary.orth_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.Unitary.orth_invariant

/-- info: 'SparseLinearSystems.UnitaryFilter.defect_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.defect_adjoint

/-- info: 'SparseLinearSystems.UnitaryFilter.re_inner_defect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.re_inner_defect

/-- info: 'SparseLinearSystems.UnitaryFilter.adjoint_one_apply'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.adjoint_one_apply'

/-- info: 'SparseLinearSystems.UnitaryFilter.Unitary.defect_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.Unitary.defect_eq

/-- info: 'SparseLinearSystems.UnitaryFilter.Unitary.defect_commute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.Unitary.defect_commute

/-- info: 'SparseLinearSystems.UnitaryFilter.Unitary.defect_eigen_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.Unitary.defect_eigen_lower

/-- info: 'SparseLinearSystems.UnitaryFilter.Unitary.lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.Unitary.lower_bound

/-- info: 'SparseLinearSystems.UnitaryFilter.avg_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.avg_fixed

/-- info: 'SparseLinearSystems.UnitaryFilter.avg_orth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.avg_orth

/-- info: 'SparseLinearSystems.UnitaryFilter.sub_one_avg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.sub_one_avg

/-- info: 'SparseLinearSystems.UnitaryFilter.avg_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.avg_bound

/-- info: 'SparseLinearSystems.UnitaryFilter.filter_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.filter_fixed

/-- info: 'SparseLinearSystems.UnitaryFilter.filter_orth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.filter_orth

/-- info: 'SparseLinearSystems.UnitaryFilter.filter_sub_proj_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.filter_sub_proj_le

/-- info: 'SparseLinearSystems.UnitaryFilter.filter_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.UnitaryFilter.filter_norm_sq

/-! ### `SparseLinearSystems.Spectral.CayleyAlgebra` -/

/-- info: 'SparseLinearSystems.CayleyAlgebra.cayley_eq_of_right_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CayleyAlgebra.cayley_eq_of_right_inverse

/-- info: 'SparseLinearSystems.CayleyAlgebra.cayley_mul_denominator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CayleyAlgebra.cayley_mul_denominator

/-- info: 'SparseLinearSystems.CayleyAlgebra.cayley_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CayleyAlgebra.cayley_zero

/-- info: 'SparseLinearSystems.CayleyAlgebra.blockMap_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CayleyAlgebra.blockMap_selfAdjoint

/-- info: 'SparseLinearSystems.CayleyAlgebra.blockMap_mul_diag' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CayleyAlgebra.blockMap_mul_diag

/-- info: 'SparseLinearSystems.CayleyAlgebra.blockMap_one'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CayleyAlgebra.blockMap_one'

/-- info: 'SparseLinearSystems.CayleyAlgebra.blockMap_sub_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CayleyAlgebra.blockMap_sub_I

/-- info: 'SparseLinearSystems.CayleyAlgebra.blockMap_add_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CayleyAlgebra.blockMap_add_I

/-- info: 'SparseLinearSystems.CayleyAlgebra.cayley_blockMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CayleyAlgebra.cayley_blockMap

/-- info: 'SparseLinearSystems.CayleyAlgebra.cayley_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CayleyAlgebra.cayley_conj

/-! ### `SparseLinearSystems.WalkGap` -/

/-- info: 'SparseLinearSystems.WalkGap.reflection_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.reflection_apply

/-- info: 'SparseLinearSystems.WalkGap.isometry_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.isometry_apply

/-- info: 'SparseLinearSystems.WalkGap.isometry_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.isometry_norm

/-- info: 'SparseLinearSystems.WalkGap.reflection_reflection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.reflection_reflection

/-- info: 'SparseLinearSystems.WalkGap.reflection_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.reflection_mul_self

/-- info: 'SparseLinearSystems.WalkGap.adjoint_one'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.adjoint_one'

/-- info: 'SparseLinearSystems.WalkGap.reflection_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.reflection_adjoint

/-- info: 'SparseLinearSystems.WalkGap.walk_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.walk_unitary

/-- info: 'SparseLinearSystems.WalkGap.norm_eigenvalue_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.norm_eigenvalue_eq_one

/-- info: 'SparseLinearSystems.WalkGap.normSq_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.normSq_unit

/-- info: 'SparseLinearSystems.WalkGap.norm_add_one_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.norm_add_one_sq

/-- info: 'SparseLinearSystems.WalkGap.norm_sub_one_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.norm_sub_one_sq

/-- info: 'SparseLinearSystems.WalkGap.tau_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.tau_spec

/-- info: 'SparseLinearSystems.WalkGap.tau_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.tau_ne_zero

/-- info: 'SparseLinearSystems.WalkGap.chord_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.chord_sq

/-- info: 'SparseLinearSystems.WalkGap.Hyp.isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.isometry

/-- info: 'SparseLinearSystems.WalkGap.Hyp.selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.selfAdjoint

/-- info: 'SparseLinearSystems.WalkGap.Hyp.alpha_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.alpha_pos

/-- info: 'SparseLinearSystems.WalkGap.Hyp.compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.compression

/-- info: 'SparseLinearSystems.WalkGap.Hyp.moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.moment

/-- info: 'SparseLinearSystems.WalkGap.Hyp.mu_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.mu_nonneg

/-- info: 'SparseLinearSystems.WalkGap.Hyp.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.bound

/-- info: 'SparseLinearSystems.WalkGap.Hyp.k0_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.k0_nonneg

/-- info: 'SparseLinearSystems.WalkGap.resolvent_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.resolvent_apply

/-- info: 'SparseLinearSystems.WalkGap.Hyp.compression_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.compression_apply

/-- info: 'SparseLinearSystems.WalkGap.Hyp.hamiltonian_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.hamiltonian_eq

/-- info: 'SparseLinearSystems.WalkGap.Hyp.hamiltonian_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.hamiltonian_selfAdjoint

/-- info: 'SparseLinearSystems.WalkGap.Hyp.walk_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.walk_unitary

/-- info: 'SparseLinearSystems.WalkGap.Hyp.lift_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.lift_adjoint

/-- info: 'SparseLinearSystems.WalkGap.walk_fixed_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.walk_fixed_iff

/-- info: 'SparseLinearSystems.WalkGap.one_sub_cayley_resolvent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.one_sub_cayley_resolvent

/-- info: 'SparseLinearSystems.WalkGap.resolvent_one_sub_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.resolvent_one_sub_cayley

/-- info: 'SparseLinearSystems.WalkGap.Hyp.fixed_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.fixed_lift

/-- info: 'SparseLinearSystems.WalkGap.Hyp.kernel_of_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.kernel_of_fixed

/-- info: 'SparseLinearSystems.WalkGap.Hyp.lift_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.lift_norm_sq

/-- info: 'SparseLinearSystems.WalkGap.Hyp.secular' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.secular

/-- info: 'SparseLinearSystems.WalkGap.one_sub_smul_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.one_sub_smul_lower

/-- info: 'SparseLinearSystems.WalkGap.oneSub_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.oneSub_apply

/-- info: 'SparseLinearSystems.WalkGap.oneSub_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.oneSub_injective

/-- info: 'SparseLinearSystems.WalkGap.gInv_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.gInv_left

/-- info: 'SparseLinearSystems.WalkGap.gInv_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.gInv_right

/-- info: 'SparseLinearSystems.WalkGap.abs_tau_eigen_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.abs_tau_eigen_le

/-- info: 'SparseLinearSystems.WalkGap.one_sub_eigen_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.one_sub_eigen_pos

/-- info: 'SparseLinearSystems.WalkGap.one_sub_eigen_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.one_sub_eigen_le

/-- info: 'SparseLinearSystems.WalkGap.one_sub_eigen_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.one_sub_eigen_ge

/-- info: 'SparseLinearSystems.WalkGap.gInv_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.gInv_eigen

/-- info: 'SparseLinearSystems.WalkGap.core_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.core_identity

/-- info: 'SparseLinearSystems.WalkGap.incrementCore_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.incrementCore_eigen

/-- info: 'SparseLinearSystems.WalkGap.coreCoeff_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.coreCoeff_pos

/-- info: 'SparseLinearSystems.WalkGap.coreCoeff_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.coreCoeff_lower

/-- info: 'SparseLinearSystems.WalkGap.coreCoeff_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.coreCoeff_upper

/-- info: 'SparseLinearSystems.WalkGap.incrementCore_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.incrementCore_adjoint

/-- info: 'SparseLinearSystems.WalkGap.norm_sq_K_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.norm_sq_K_eq

/-- info: 'SparseLinearSystems.WalkGap.incrementCore_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.incrementCore_bounds

/-- info: 'SparseLinearSystems.WalkGap.increment_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.increment_adjoint

/-- info: 'SparseLinearSystems.WalkGap.increment_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.increment_re

/-- info: 'SparseLinearSystems.WalkGap.Hyp.tangent_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.tangent_gap

/-- info: 'SparseLinearSystems.WalkGap.tStar_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.tStar_pos

/-- info: 'SparseLinearSystems.WalkGap.Hyp.chord_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.chord_gap

/-! ### `SparseLinearSystems.Statistics.BinomialTail` -/

/-- info: 'SparseLinearSystems.BinomialTail.binom_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.BinomialTail.binom_nonneg

/-- info: 'SparseLinearSystems.BinomialTail.sum_binom_mul_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.BinomialTail.sum_binom_mul_pow

/-- info: 'SparseLinearSystems.BinomialTail.sum_binom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.BinomialTail.sum_binom

/-- info: 'SparseLinearSystems.BinomialTail.mgf_base_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.BinomialTail.mgf_base_le

/-- info: 'SparseLinearSystems.BinomialTail.exp_sub_le_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.BinomialTail.exp_sub_le_sq

/-- info: 'SparseLinearSystems.BinomialTail.mgf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.BinomialTail.mgf_le

/-- info: 'SparseLinearSystems.BinomialTail.upper_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.BinomialTail.upper_tail

/-- info: 'SparseLinearSystems.BinomialTail.lower_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.BinomialTail.lower_tail

/-- info: 'SparseLinearSystems.BinomialTail.two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.BinomialTail.two_sided

/-- info: 'SparseLinearSystems.BinomialTail.two_sided_le_of_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.BinomialTail.two_sided_le_of_count

/-! ### `SparseLinearSystems.Augmented.Operators` -/

/-- info: 'SparseLinearSystems.Augmented.eta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.eta

/-- info: 'SparseLinearSystems.Augmented.mk_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.mk_fst

/-- info: 'SparseLinearSystems.Augmented.mk_snd_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.mk_snd_fst

/-- info: 'SparseLinearSystems.Augmented.mk_snd_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.mk_snd_snd

/-- info: 'SparseLinearSystems.Augmented.inner_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.inner_right

/-- info: 'SparseLinearSystems.Augmented.inner_pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.inner_pub

/-- info: 'SparseLinearSystems.Augmented.norm_sq_pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.norm_sq_pub

/-- info: 'SparseLinearSystems.Augmented.lift_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.lift_apply

/-- info: 'SparseLinearSystems.Augmented.lift_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.lift_selfAdjoint

/-- info: 'SparseLinearSystems.Augmented.lift_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.lift_norm_sq

/-- info: 'SparseLinearSystems.Augmented.lift_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.lift_norm_le

/-- info: 'SparseLinearSystems.Augmented.zb_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.zb_apply

/-- info: 'SparseLinearSystems.Augmented.zb_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.zb_selfAdjoint

/-- info: 'SparseLinearSystems.Augmented.exchange_apply'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.exchange_apply'

/-- info: 'SparseLinearSystems.Augmented.exchange_selfAdjoint'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.exchange_selfAdjoint'

/-- info: 'SparseLinearSystems.Augmented.norm_exchange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.norm_exchange

/-- info: 'SparseLinearSystems.Augmented.sndEmb_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.sndEmb_apply

/-- info: 'SparseLinearSystems.Augmented.T2_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.T2_apply

/-- info: 'SparseLinearSystems.Augmented.T2_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.T2_selfAdjoint

/-- info: 'SparseLinearSystems.Augmented.T2_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.T2_norm_le

/-- info: 'SparseLinearSystems.Augmented.T1_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.T1_selfAdjoint

/-- info: 'SparseLinearSystems.Augmented.T1_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.T1_norm_le

/-- info: 'SparseLinearSystems.Augmented.H0_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.H0_selfAdjoint

/-- info: 'SparseLinearSystems.Augmented.regularized_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.regularized_eq

/-- info: 'SparseLinearSystems.Augmented.column_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.column_adjoint_apply

/-- info: 'SparseLinearSystems.Augmented.hamiltonian_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.hamiltonian_decomp

/-- info: 'SparseLinearSystems.Augmented.norm_betaOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.norm_betaOf

/-- info: 'SparseLinearSystems.Augmented.solEmb_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.solEmb_apply

/-- info: 'SparseLinearSystems.Augmented.solEmb_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.solEmb_isometry

/-- info: 'SparseLinearSystems.Augmented.solEmb_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.solEmb_adjoint_apply

/-! ### `SparseLinearSystems.Augmented.Walk` -/

/-- info: 'SparseLinearSystems.Augmented.BranchProps.selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.BranchProps.selfAdjoint

/-- info: 'SparseLinearSystems.Augmented.BranchProps.compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.BranchProps.compression

/-- info: 'SparseLinearSystems.Augmented.BranchProps.moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.BranchProps.moment

/-- info: 'SparseLinearSystems.Augmented.BranchProps.bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.BranchProps.bound

/-- info: 'SparseLinearSystems.Augmented.real_smul_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.real_smul_selfAdjoint

/-- info: 'SparseLinearSystems.Augmented.walkK_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.walkK_selfAdjoint

/-- info: 'SparseLinearSystems.Augmented.adjoint_id'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.adjoint_id'

/-- info: 'SparseLinearSystems.Augmented.branchCompression_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.branchCompression_id

/-- info: 'SparseLinearSystems.Augmented.walk_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.walk_compression

/-- info: 'SparseLinearSystems.Augmented.diagonal_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.diagonal_bound

/-- info: 'SparseLinearSystems.Augmented.augmented_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.augmented_hyp

/-- info: 'SparseLinearSystems.Augmented.tStar_augmented' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.tStar_augmented

/-- info: 'SparseLinearSystems.Augmented.chi_le_tStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.chi_le_tStar

/-- info: 'SparseLinearSystems.Augmented.chord_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.chord_mono

/-- info: 'SparseLinearSystems.Augmented.augmented_chord_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.augmented_chord_gap

/-! ### `SparseLinearSystems.Augmented.Probability` -/

/-- info: 'SparseLinearSystems.WalkGap.Hyp.fixedSpace_eq_span' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.fixedSpace_eq_span

/-- info: 'SparseLinearSystems.WalkGap.Hyp.fixedProj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.fixedProj_apply

/-- info: 'SparseLinearSystems.WalkGap.Hyp.inner_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.inner_lift

/-- info: 'SparseLinearSystems.WalkGap.Hyp.lift_norm_sq_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.lift_norm_sq_complex

/-- info: 'SparseLinearSystems.WalkGap.Hyp.seed_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.seed_probability

/-- info: 'SparseLinearSystems.WalkGap.Hyp.extracted_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.extracted_amplitude

/-! ### `SparseLinearSystems.Augmented.Solution` -/

/-- info: 'SparseLinearSystems.Augmented.Mσ_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.Mσ_coe

/-- info: 'SparseLinearSystems.Augmented.hamiltonian_eq_branches' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.hamiltonian_eq_branches

/-- info: 'SparseLinearSystems.Augmented.hamiltonian_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.hamiltonian_kernel

/-- info: 'SparseLinearSystems.Augmented.inner_generator_eVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.inner_generator_eVec

/-- info: 'SparseLinearSystems.Augmented.generator_norm_sq_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.generator_norm_sq_real

/-- info: 'SparseLinearSystems.Augmented.M0_symm_beta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.M0_symm_beta

/-- info: 'SparseLinearSystems.Augmented.rSigma_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.rSigma_zero

/-! ### `SparseLinearSystems.Augmented.NormLadder` -/

/-- info: 'SparseLinearSystems.Augmented.inv_norm_sq_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.inv_norm_sq_ge

/-- info: 'SparseLinearSystems.Augmented.inv_norm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.inv_norm_sq_le

/-- info: 'SparseLinearSystems.Augmented.dilation_form_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.dilation_form_le

/-- info: 'SparseLinearSystems.Augmented.dilation_form_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.dilation_form_ge

/-- info: 'SparseLinearSystems.Augmented.Mσ_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.Mσ_norm_sq

/-- info: 'SparseLinearSystems.Augmented.Mσ_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.Mσ_selfAdjoint

/-- info: 'SparseLinearSystems.Augmented.rSigma_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.rSigma_congr

/-- info: 'SparseLinearSystems.Augmented.rSigma_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.rSigma_one

/-- info: 'SparseLinearSystems.Augmented.rSigma_anti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.rSigma_anti

/-- info: 'SparseLinearSystems.Augmented.rSigma_half_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.rSigma_half_le

/-- info: 'SparseLinearSystems.Augmented.rSigma_zero_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.rSigma_zero_le

/-- info: 'SparseLinearSystems.Augmented.one_le_rSigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.one_le_rSigma

/-- info: 'SparseLinearSystems.Augmented.rSigma_le_kappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.rSigma_le_kappa

/-! ### `SparseLinearSystems.Augmented.Analysis` -/

/-- info: 'SparseLinearSystems.WalkGap.Hyp.seed_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.seed_facts

/-- info: 'SparseLinearSystems.WalkGap.Hyp.seed_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.seed_bounds

/-- info: 'SparseLinearSystems.Augmented.conj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.conj_apply

/-- info: 'SparseLinearSystems.Augmented.adjoint_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.adjoint_transport

/-- info: 'SparseLinearSystems.WalkGap.Hyp.transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.WalkGap.Hyp.transport

/-- info: 'SparseLinearSystems.Augmented.conj_reflection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.conj_reflection

/-- info: 'SparseLinearSystems.Augmented.conj_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.conj_cayley

/-- info: 'SparseLinearSystems.Augmented.conj_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.conj_walk

/-- info: 'SparseLinearSystems.Augmented.branchHam_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.branchHam_eq

/-- info: 'SparseLinearSystems.Augmented.branchHam_kerVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.branchHam_kerVec

/-- info: 'SparseLinearSystems.Augmented.branchHam_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.branchHam_kernel

/-- info: 'SparseLinearSystems.Augmented.kerVec_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.kerVec_ne_zero

/-- info: 'SparseLinearSystems.Augmented.kerVec_inner_eVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.kerVec_inner_eVec

/-- info: 'SparseLinearSystems.Augmented.kerVec_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.kerVec_norm_sq

/-- info: 'SparseLinearSystems.Augmented.branchHam_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.branchHam_gap

/-- info: 'SparseLinearSystems.Augmented.solEmb_kerVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.solEmb_kerVec

/-- info: 'SparseLinearSystems.Augmented.filter_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Augmented.filter_bounds

/-! ### `SparseLinearSystems.Sparse.SplitBoundary` -/

/-- info: 'SparseLinearSystems.SplitBoundary.split_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SplitBoundary.split_inl

/-- info: 'SparseLinearSystems.SplitBoundary.split_inr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SplitBoundary.split_inr

/-- info: 'SparseLinearSystems.SplitBoundary.leftPart_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SplitBoundary.leftPart_split

/-- info: 'SparseLinearSystems.SplitBoundary.rightPart_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SplitBoundary.rightPart_split

/-- info: 'SparseLinearSystems.SplitBoundary.inner_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SplitBoundary.inner_split

/-- info: 'SparseLinearSystems.SplitBoundary.norm_sq_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SplitBoundary.norm_sq_split

/-- info: 'SparseLinearSystems.SplitBoundary.block_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SplitBoundary.block_split

/-- info: 'SparseLinearSystems.SplitBoundary.gram_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SplitBoundary.gram_apply

/-- info: 'SparseLinearSystems.SplitBoundary.gram_apply_column' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SplitBoundary.gram_apply_column

/-- info: 'SparseLinearSystems.SplitBoundary.fixedSplit_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SplitBoundary.fixedSplit_isometry

/-- info: 'SparseLinearSystems.SplitBoundary.locator_fixedSplit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SplitBoundary.locator_fixedSplit

/-- info: 'SparseLinearSystems.SplitBoundary.entryGenerator_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SplitBoundary.entryGenerator_split

/-- info: 'SparseLinearSystems.SplitBoundary.split_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SplitBoundary.split_compression

/-- info: 'SparseLinearSystems.SplitBoundary.split_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SplitBoundary.split_moment

/-! ### `SparseLinearSystems.Sparse.SparseBranch` -/

/-- info: 'SparseLinearSystems.SparseBranch.pair_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SparseBranch.pair_add

/-- info: 'SparseLinearSystems.SparseBranch.pair_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SparseBranch.pair_smul

/-- info: 'SparseLinearSystems.SparseBranch.sum_norm_sq_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SparseBranch.sum_norm_sq_pair

/-- info: 'SparseLinearSystems.SparseBranch.J0lin_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SparseBranch.J0lin_norm

/-- info: 'SparseLinearSystems.SparseBranch.J0_apply_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SparseBranch.J0_apply_fst

/-- info: 'SparseLinearSystems.SparseBranch.J0_apply_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SparseBranch.J0_apply_snd

/-- info: 'SparseLinearSystems.SparseBranch.K0_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SparseBranch.K0_apply

/-- info: 'SparseLinearSystems.SparseBranch.generator_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SparseBranch.generator_adjoint

/-- info: 'SparseLinearSystems.SparseBranch.quad_diagonal_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SparseBranch.quad_diagonal_adjoint

/-- info: 'SparseLinearSystems.SparseBranch.K0_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SparseBranch.K0_selfAdjoint

/-- info: 'SparseLinearSystems.SparseBranch.inner_split_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SparseBranch.inner_split_G

/-- info: 'SparseLinearSystems.SparseBranch.J0_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SparseBranch.J0_compression

/-- info: 'SparseLinearSystems.SparseBranch.K0_J0_norm_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SparseBranch.K0_J0_norm_sq

/-- info: 'SparseLinearSystems.SparseBranch.K0_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SparseBranch.K0_bound

/-- info: 'SparseLinearSystems.SparseBranch.branchProps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.SparseBranch.branchProps

/-! ### `SparseLinearSystems.Circuit.LogicalWalk` -/

/-- info: 'SparseLinearSystems.LogicalWalk.diagonal_sub_smul_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.diagonal_sub_smul_one

/-- info: 'SparseLinearSystems.LogicalWalk.diagonal_add_smul_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.diagonal_add_smul_one

/-- info: 'SparseLinearSystems.LogicalWalk.diagonal_mul'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.diagonal_mul'

/-- info: 'SparseLinearSystems.LogicalWalk.cayley_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.cayley_diagonal

/-- info: 'SparseLinearSystems.LogicalWalk.smul_blockMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.smul_blockMap

/-- info: 'SparseLinearSystems.LogicalWalk.smul_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.smul_diagonal

/-- info: 'SparseLinearSystems.LogicalWalk.cayley_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.cayley_congr

/-- info: 'SparseLinearSystems.LogicalWalk.cayley_fourDiagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.cayley_fourDiagonal

/-- info: 'SparseLinearSystems.LogicalWalk.generator_smul_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.generator_smul_selfAdjoint

/-- info: 'SparseLinearSystems.LogicalWalk.cayley_smul_generator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.cayley_smul_generator

/-- info: 'SparseLinearSystems.LogicalWalk.cayley_K0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.cayley_K0

/-- info: 'SparseLinearSystems.LogicalWalk.slotOp_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.slotOp_apply

/-- info: 'SparseLinearSystems.LogicalWalk.slotOp_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.slotOp_adjoint

/-- info: 'SparseLinearSystems.LogicalWalk.blockMap_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.blockMap_isUnitary

/-- info: 'SparseLinearSystems.LogicalWalk.slotOp_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.slotOp_unitary

/-- info: 'SparseLinearSystems.LogicalWalk.inner_betaOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.inner_betaOf

/-- info: 'SparseLinearSystems.LogicalWalk.slotOp_betaOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.slotOp_betaOf

/-- info: 'SparseLinearSystems.LogicalWalk.T2_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.T2_slot

/-- info: 'SparseLinearSystems.LogicalWalk.Kw_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.Kw_selfAdjoint

/-- info: 'SparseLinearSystems.LogicalWalk.Ww_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.Ww_unitary

/-- info: 'SparseLinearSystems.LogicalWalk.Vd_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.Vd_adjoint

/-- info: 'SparseLinearSystems.LogicalWalk.diag_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.diag_product

/-- info: 'SparseLinearSystems.LogicalWalk.Ww_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.Ww_factor

/-! ### `SparseLinearSystems.Circuit.CounterFilter` -/

/-- info: 'SparseLinearSystems.CounterFilter.avgPolyC_eq_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CounterFilter.avgPolyC_eq_map

/-- info: 'SparseLinearSystems.CounterFilter.avgPoly_coeff_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CounterFilter.avgPoly_coeff_nonneg

/-- info: 'SparseLinearSystems.CounterFilter.coeff_mul_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CounterFilter.coeff_mul_nonneg

/-- info: 'SparseLinearSystems.CounterFilter.coef_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CounterFilter.coef_nonneg

/-- info: 'SparseLinearSystems.CounterFilter.avgPoly_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CounterFilter.avgPoly_natDegree_le

/-- info: 'SparseLinearSystems.CounterFilter.filterPoly_natDegree_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CounterFilter.filterPoly_natDegree_le

/-- info: 'SparseLinearSystems.CounterFilter.coef_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CounterFilter.coef_eq_zero

/-- info: 'SparseLinearSystems.CounterFilter.avgPoly_eval_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CounterFilter.avgPoly_eval_one

/-- info: 'SparseLinearSystems.CounterFilter.sum_coef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CounterFilter.sum_coef

/-- info: 'SparseLinearSystems.CounterFilter.sum_coef_fin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CounterFilter.sum_coef_fin

/-- info: 'SparseLinearSystems.CounterFilter.aeval_avgPolyC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CounterFilter.aeval_avgPolyC

/-- info: 'SparseLinearSystems.CounterFilter.sum_coef_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CounterFilter.sum_coef_pow

/-- info: 'SparseLinearSystems.CounterFilter.steps_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CounterFilter.steps_eq

/-- info: 'SparseLinearSystems.CounterFilter.seedMap_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CounterFilter.seedMap_isometry

/-- info: 'SparseLinearSystems.CounterFilter.counter_compression' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CounterFilter.counter_compression

/-- info: 'SparseLinearSystems.CounterFilter.counter_compression_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.CounterFilter.counter_compression_le

/-! ### `SparseLinearSystems.Circuit.Source` -/

/-- info: 'SparseLinearSystems.Source.srcU_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Source.srcU_unitary

/-- info: 'SparseLinearSystems.Source.slice_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Source.slice_apply

/-- info: 'SparseLinearSystems.Source.srcU_nEmb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Source.srcU_nEmb

/-- info: 'SparseLinearSystems.Source.controlled_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Source.controlled_unitary

/-- info: 'SparseLinearSystems.Source.controlled_packet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Source.controlled_packet

/-- info: 'SparseLinearSystems.Source.sourceOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Source.sourceOracle_unitary

/-- info: 'SparseLinearSystems.Source.sourceOracle_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Source.sourceOracle_apply

/-- info: 'SparseLinearSystems.Source.sourceProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Source.sourceProgram_count

/-- info: 'SparseLinearSystems.Source.sourceProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Source.sourceProgram_intertwines

/-! ### `SparseLinearSystems.Circuit.Opaque` -/

/-- info: 'SparseLinearSystems.LogicalWalk.completeOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.completeOf

/-- info: 'SparseLinearSystems.LogicalWalk.findimOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.findimOf

/-- info: 'SparseLinearSystems.LogicalWalk.instCompleteSpacePrivO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.instCompleteSpacePrivO

/-- info: 'SparseLinearSystems.LogicalWalk.instFiniteDimensionalPrivO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.instFiniteDimensionalPrivO

/-- info: 'SparseLinearSystems.LogicalWalk.toO_symm_apply_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.toO_symm_apply_apply

/-- info: 'SparseLinearSystems.LogicalWalk.toO_apply_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.toO_apply_symm_apply

/-- info: 'SparseLinearSystems.LogicalWalk.norm_toO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.norm_toO

/-- info: 'SparseLinearSystems.LogicalWalk.opO_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.opO_apply

/-- info: 'SparseLinearSystems.LogicalWalk.opO_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.opO_mul

/-- info: 'SparseLinearSystems.LogicalWalk.opO_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.opO_one

/-- info: 'SparseLinearSystems.LogicalWalk.opO_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.opO_star

/-- info: 'SparseLinearSystems.LogicalWalk.opO_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.opO_adjoint

/-- info: 'SparseLinearSystems.LogicalWalk.opO_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.opO_unitary

/-- info: 'SparseLinearSystems.LogicalWalk.opO_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.opO_add

/-- info: 'SparseLinearSystems.LogicalWalk.opO_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.opO_zero

/-- info: 'SparseLinearSystems.LogicalWalk.opO_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.opO_smul

/-- info: 'SparseLinearSystems.LogicalWalk.opO_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.opO_pow

/-- info: 'SparseLinearSystems.LogicalWalk.opO_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.opO_sum

/-- info: 'SparseLinearSystems.LogicalWalk.WwO_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.WwO_unitary

/-- info: 'SparseLinearSystems.LogicalWalk.WwO_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.LogicalWalk.WwO_factor

/-! ### `SparseLinearSystems.Circuit.Cells` -/

/-- info: 'SparseLinearSystems.Cells.quadL_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.quadL_apply

/-- info: 'SparseLinearSystems.Cells.e0L_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.e0L_apply

/-- info: 'SparseLinearSystems.Cells.br0_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.br0_apply

/-- info: 'SparseLinearSystems.Cells.brk_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.brk_zero

/-- info: 'SparseLinearSystems.Cells.brk_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.brk_one

/-- info: 'SparseLinearSystems.Cells.brk_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.brk_two

/-- info: 'SparseLinearSystems.Cells.pubE_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.pubE_apply

/-- info: 'SparseLinearSystems.Cells.pubV_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.pubV_apply

/-- info: 'SparseLinearSystems.Cells.norm_sq_P0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.norm_sq_P0

/-- info: 'SparseLinearSystems.Cells.norm_sq_cells_pub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.norm_sq_cells_pub

/-- info: 'SparseLinearSystems.Cells.norm_sq_priv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.norm_sq_priv

/-- info: 'SparseLinearSystems.Cells.norm_cellMap_sq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.norm_cellMap_sq_sum

/-- info: 'SparseLinearSystems.Cells.cellMapO_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.cellMapO_apply

/-- info: 'SparseLinearSystems.Cells.norm_cellMapO_sq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.norm_cellMapO_sq_sum

/-- info: 'SparseLinearSystems.Cells.encL_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.encL_apply

/-- info: 'SparseLinearSystems.Cells.encL_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.encL_norm

/-- info: 'SparseLinearSystems.Cells.Enc_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.Enc_apply

/-- info: 'SparseLinearSystems.Cells.Asp_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.Asp_fst

/-- info: 'SparseLinearSystems.Cells.Asp_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.Asp_snd

/-- info: 'SparseLinearSystems.Cells.sparseCells_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.sparseCells_fst

/-- info: 'SparseLinearSystems.Cells.sparseCells_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.sparseCells_snd

/-- info: 'SparseLinearSystems.Cells.cellMap_Asp_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.cellMap_Asp_sparse

/-- info: 'SparseLinearSystems.Cells.cellMap_Asp_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.cellMap_Asp_other

/-- info: 'SparseLinearSystems.Cells.cellMapO_Asp_sparse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.cellMapO_Asp_sparse

/-- info: 'SparseLinearSystems.Cells.cellMapO_Asp_other' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.cellMapO_Asp_other

/-- info: 'SparseLinearSystems.Cells.sparse_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.sparse_intertwines

/-- info: 'SparseLinearSystems.Cells.slotOp_fst_fst_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.slotOp_fst_fst_fst

/-- info: 'SparseLinearSystems.Cells.slotOp_fst_fst_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.slotOp_fst_fst_snd

/-- info: 'SparseLinearSystems.Cells.slotOp_fst_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.slotOp_fst_snd

/-- info: 'SparseLinearSystems.Cells.slotOp_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.slotOp_snd

/-- info: 'SparseLinearSystems.Cells.Vd_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.Vd_fst

/-- info: 'SparseLinearSystems.Cells.Vd_snd_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.Vd_snd_fst

/-- info: 'SparseLinearSystems.Cells.Vd_snd_snd_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.Vd_snd_snd_fst

/-- info: 'SparseLinearSystems.Cells.Vd_snd_snd_snd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.Vd_snd_snd_snd

/-- info: 'SparseLinearSystems.Cells.cellMap_Vd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.cellMap_Vd

/-- info: 'SparseLinearSystems.Cells.cellMapO_Vd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.cellMapO_Vd

/-- info: 'SparseLinearSystems.Cells.source_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Cells.source_intertwines

/-! ### `SparseLinearSystems.Circuit.Step` -/

/-- info: 'SparseLinearSystems.Step.physOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.physOracle_unitary

/-- info: 'SparseLinearSystems.Step.E_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.E_isometry

/-- info: 'SparseLinearSystems.Step.logOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.logOracle_unitary

/-- info: 'SparseLinearSystems.Step.neg_one_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.neg_one_unitary

/-- info: 'SparseLinearSystems.Step.diagonal_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.diagonal_unitary

/-- info: 'SparseLinearSystems.Step.reflection_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.reflection_unitary

/-- info: 'SparseLinearSystems.Step.cayley_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.cayley_isUnitary

/-- info: 'SparseLinearSystems.Step.Fa_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.Fa_unitary

/-- info: 'SparseLinearSystems.Step.Fb_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.Fb_unitary

/-- info: 'SparseLinearSystems.Step.Vd_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.Vd_unitary

/-- info: 'SparseLinearSystems.Step.inlProg_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.inlProg_eval

/-- info: 'SparseLinearSystems.Step.inlProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.inlProg_cost

/-- info: 'SparseLinearSystems.Step.inrProg_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.inrProg_eval

/-- info: 'SparseLinearSystems.Step.inrProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.inrProg_cost

/-- info: 'SparseLinearSystems.Step.intertwine_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.intertwine_mul

/-- info: 'SparseLinearSystems.Step.fixedStep_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.fixedStep_intertwines

/-- info: 'SparseLinearSystems.Step.nativeStep_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.nativeStep_eval

/-- info: 'SparseLinearSystems.Step.sourceStep_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.sourceStep_eval

/-- info: 'SparseLinearSystems.Step.nativeStep_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.nativeStep_intertwines

/-- info: 'SparseLinearSystems.Step.sourceStep_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.sourceStep_intertwines

/-- info: 'SparseLinearSystems.Step.stepProg_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.stepProg_intertwines

/-- info: 'SparseLinearSystems.Step.nativeStep_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.nativeStep_cost

/-- info: 'SparseLinearSystems.Step.sourceStep_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.sourceStep_cost

/-- info: 'SparseLinearSystems.Step.stepProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.stepProg_cost

/-- info: 'SparseLinearSystems.Step.stepProg_cost_mat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.stepProg_cost_mat

/-- info: 'SparseLinearSystems.Step.stepProg_cost_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Step.stepProg_cost_src

/-! ### `SparseLinearSystems.Circuit.Run` -/

/-- info: 'SparseLinearSystems.Run.runLog_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.runLog_eval

/-- info: 'SparseLinearSystems.Run.runLog_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.runLog_count

/-- info: 'SparseLinearSystems.Run.runPhys_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.runPhys_intertwines

/-- info: 'SparseLinearSystems.Run.runPhys_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.runPhys_unitary

/-- info: 'SparseLinearSystems.Run.runPhys_cost_mat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.runPhys_cost_mat

/-- info: 'SparseLinearSystems.Run.runPhys_cost_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.runPhys_cost_src

/-- info: 'SparseLinearSystems.Run.opO_avg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.opO_avg

/-- info: 'SparseLinearSystems.Run.opO_filter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.opO_filter

/-- info: 'SparseLinearSystems.Run.JwO_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.JwO_apply

/-- info: 'SparseLinearSystems.Run.filter_JwO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.filter_JwO

/-- info: 'SparseLinearSystems.Run.JwO_adjoint_toO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.JwO_adjoint_toO

/-- info: 'SparseLinearSystems.Run.one_comp'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.one_comp'

/-- info: 'SparseLinearSystems.Run.E_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.E_norm

/-- info: 'SparseLinearSystems.Run.E_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.E_adjoint_apply

/-- info: 'SparseLinearSystems.Run.seedMap_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.seedMap_norm

/-- info: 'SparseLinearSystems.Run.norm_eVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.norm_eVec

/-- info: 'SparseLinearSystems.Run.seedVec_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.seedVec_norm

/-- info: 'SparseLinearSystems.Run.testFlag_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.testFlag_isometry

/-- info: 'SparseLinearSystems.Run.finalOutput_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.finalOutput_isometry

/-- info: 'SparseLinearSystems.Run.test_amplitudeO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.test_amplitudeO

/-- info: 'SparseLinearSystems.Run.final_amplitudeO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.final_amplitudeO

/-- info: 'SparseLinearSystems.Run.test_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.test_amplitude

/-- info: 'SparseLinearSystems.Run.test_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.test_probability

/-- info: 'SparseLinearSystems.Run.final_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Run.final_amplitude

/-! ### `SparseLinearSystems.Circuit.Facts` -/

/-- info: 'SparseLinearSystems.Facts.equivOfLower_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.equivOfLower_apply

/-- info: 'SparseLinearSystems.Facts.equivOfLower_coe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.equivOfLower_coe

/-- info: 'SparseLinearSystems.Facts.equivOfLower_symm_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.equivOfLower_symm_norm

/-- info: 'SparseLinearSystems.Facts.column_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.column_energy

/-- info: 'SparseLinearSystems.Facts.row_energy' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.row_energy

/-- info: 'SparseLinearSystems.Facts.concrete_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.concrete_hyp

/-- info: 'SparseLinearSystems.Facts.Ww_unitaryF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.Ww_unitaryF

/-- info: 'SparseLinearSystems.Facts.adjoint_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.adjoint_norm_le

/-- info: 'SparseLinearSystems.Facts.bLow_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.bLow_pos

/-- info: 'SparseLinearSystems.Facts.hypO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.hypO

/-- info: 'SparseLinearSystems.Facts.WwO_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.WwO_eq

/-- info: 'SparseLinearSystems.Facts.WwO_unitaryF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.WwO_unitaryF

/-- info: 'SparseLinearSystems.Facts.gapO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.gapO

/-- info: 'SparseLinearSystems.Facts.kernel_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.kernel_data

/-- info: 'SparseLinearSystems.Facts.norm_JwO_eVec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.norm_JwO_eVec

/-- info: 'SparseLinearSystems.Facts.test_fact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.test_fact

/-- info: 'SparseLinearSystems.Facts.final_fact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Facts.final_fact

/-! ### `SparseLinearSystems.Protocol.Tree` -/

/-- info: 'SparseLinearSystems.Protocol.TestRun.seed_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.TestRun.seed_unit

/-- info: 'SparseLinearSystems.Protocol.TestRun.flag_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.TestRun.flag_isometry

/-- info: 'SparseLinearSystems.Protocol.TestRun.probability_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.TestRun.probability_nonneg

/-- info: 'SparseLinearSystems.Protocol.TestRun.probability_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.TestRun.probability_le_one

/-- info: 'SparseLinearSystems.Protocol.Tree.indicator_of_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.indicator_of_pos

/-- info: 'SparseLinearSystems.Protocol.Tree.indicator_of_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.indicator_of_neg

/-- info: 'SparseLinearSystems.Protocol.Tree.indicator_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.indicator_nonneg

/-- info: 'SparseLinearSystems.Protocol.Tree.indicator_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.indicator_le_one

/-- info: 'SparseLinearSystems.Protocol.Tree.binom_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.binom_succ

/-- info: 'SparseLinearSystems.Protocol.Tree.binom_sum_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.binom_sum_succ

/-- info: 'SparseLinearSystems.Protocol.Tree.expect_countRuns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.expect_countRuns

/-- info: 'SparseLinearSystems.Protocol.Tree.AllLeaves.imp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.AllLeaves.imp

/-- info: 'SparseLinearSystems.Protocol.Tree.allLeaves_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.allLeaves_true

/-- info: 'SparseLinearSystems.Protocol.Tree.expect_real_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.expect_real_test

/-- info: 'SparseLinearSystems.Protocol.Tree.expect_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.expect_mono

/-- info: 'SparseLinearSystems.Protocol.Tree.expect_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.expect_const

/-- info: 'SparseLinearSystems.Protocol.Tree.expect_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.expect_add

/-- info: 'SparseLinearSystems.Protocol.Tree.expect_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.expect_mul

/-- info: 'SparseLinearSystems.Protocol.Tree.reach_add_compl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.reach_add_compl

/-- info: 'SparseLinearSystems.Protocol.Tree.reach_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.reach_nonneg

/-- info: 'SparseLinearSystems.Protocol.Tree.successMass_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.successMass_ge

/-- info: 'SparseLinearSystems.Protocol.Tree.allLeaves_countRuns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.allLeaves_countRuns

/-- info: 'SparseLinearSystems.Protocol.Tree.runsUnitary_countRuns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.runsUnitary_countRuns

/-- info: 'SparseLinearSystems.Protocol.Tree.worstCost_countRuns' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.worstCost_countRuns

/-- info: 'SparseLinearSystems.Protocol.Tree.successMass_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.successMass_test

/-- info: 'SparseLinearSystems.Protocol.Tree.successDensity_test' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.successDensity_test

/-- info: 'SparseLinearSystems.Protocol.Tree.successDensity_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.successDensity_positive

/-- info: 'SparseLinearSystems.Protocol.Tree.trace_successDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.trace_successDensity

/-- info: 'SparseLinearSystems.Protocol.Tree.diagonalMass_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.diagonalMass_sub_le

/-- info: 'SparseLinearSystems.Protocol.Tree.diagonalMass_pure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.diagonalMass_pure_le

/-- info: 'SparseLinearSystems.Protocol.Tree.output_guarantee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Tree.output_guarantee

/-! ### `SparseLinearSystems.Protocol.Estimator` -/

/-- info: 'SparseLinearSystems.Protocol.Estimator.clip_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.clip_of_mem

/-- info: 'SparseLinearSystems.Protocol.Estimator.one_le_clip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.one_le_clip

/-- info: 'SparseLinearSystems.Protocol.Estimator.clip_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.clip_le

/-- info: 'SparseLinearSystems.Protocol.Estimator.candidates_allLeaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.candidates_allLeaves

/-- info: 'SparseLinearSystems.Protocol.Estimator.stages_allLeaves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.stages_allLeaves

/-- info: 'SparseLinearSystems.Protocol.Estimator.candidates_runsUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.candidates_runsUnitary

/-- info: 'SparseLinearSystems.Protocol.Estimator.stages_runsUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.stages_runsUnitary

/-- info: 'SparseLinearSystems.Protocol.Estimator.candidates_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.candidates_cost

/-- info: 'SparseLinearSystems.Protocol.Estimator.stages_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.stages_cost

/-- info: 'SparseLinearSystems.Protocol.Estimator.count_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.count_step

/-- info: 'SparseLinearSystems.Protocol.Estimator.expect_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.expect_unit

/-- info: 'SparseLinearSystems.Protocol.Estimator.n_pos_of_accurate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.n_pos_of_accurate

/-- info: 'SparseLinearSystems.Protocol.Estimator.accept_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.accept_good

/-- info: 'SparseLinearSystems.Protocol.Estimator.reject_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.reject_inv

/-- info: 'SparseLinearSystems.Protocol.Estimator.last_accepts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.last_accepts

/-- info: 'SparseLinearSystems.Protocol.Estimator.candidates_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.candidates_le

/-- info: 'SparseLinearSystems.Protocol.Estimator.stages_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.stages_le

/-- info: 'SparseLinearSystems.Protocol.Estimator.algorithm_bad_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.Estimator.algorithm_bad_le

/-! ### `SparseLinearSystems.Protocol.Leaf` -/

/-- info: 'SparseLinearSystems.Protocol.single_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.single_amplitude

/-- info: 'SparseLinearSystems.Protocol.single_meanSuccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.single_meanSuccess

/-- info: 'SparseLinearSystems.Protocol.single_oneTrialDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.single_oneTrialDensity

/-- info: 'SparseLinearSystems.Protocol.single_successMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.single_successMass

/-- info: 'SparseLinearSystems.Protocol.single_successDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.single_successDensity

/-- info: 'SparseLinearSystems.Protocol.single_leaf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.single_leaf_spec

/-- info: 'SparseLinearSystems.Protocol.leafDir_single' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Protocol.leafDir_single

/-! ### `SparseLinearSystems.Endpoint.Algorithm` -/

/-- info: 'SparseLinearSystems.Endpoint.sig_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.sig_nonneg

/-- info: 'SparseLinearSystems.Endpoint.sig_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.sig_pos

/-- info: 'SparseLinearSystems.Endpoint.sig_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.sig_le_one

/-- info: 'SparseLinearSystems.Endpoint.sig_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.sig_succ

/-- info: 'SparseLinearSystems.Endpoint.stageOf_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.stageOf_le

/-- info: 'SparseLinearSystems.Endpoint.stageOf_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.stageOf_of_le

/-- info: 'SparseLinearSystems.Endpoint.Ntest_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.Ntest_pos

/-- info: 'SparseLinearSystems.Endpoint.Ntest_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.Ntest_spec

/-- info: 'SparseLinearSystems.Endpoint.Nfin_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.Nfin_pos

/-- info: 'SparseLinearSystems.Endpoint.Nfin_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.Nfin_spec

/-- info: 'SparseLinearSystems.Endpoint.Ttest_le_Tw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.Ttest_le_Tw

/-- info: 'SparseLinearSystems.Endpoint.Tfin_le_Tw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.Tfin_le_Tw

/-- info: 'SparseLinearSystems.Endpoint.test_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.test_degree

/-- info: 'SparseLinearSystems.Endpoint.final_degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.final_degree

/-- info: 'SparseLinearSystems.Endpoint.kappa_le_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.kappa_le_pow

/-- info: 'SparseLinearSystems.Endpoint.sig_stages_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.sig_stages_le

/-- info: 'SparseLinearSystems.Endpoint.zeta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.zeta_pos

/-- info: 'SparseLinearSystems.Endpoint.reps_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.reps_spec

/-- info: 'SparseLinearSystems.Endpoint.sum_zeta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.sum_zeta_le

/-- info: 'SparseLinearSystems.Endpoint.kfin_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.kfin_spec

/-- info: 'SparseLinearSystems.Endpoint.test_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.test_fits

/-- info: 'SparseLinearSystems.Endpoint.final_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.final_fits

/-- info: 'SparseLinearSystems.Endpoint.testRun_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.testRun_unitary

/-- info: 'SparseLinearSystems.Endpoint.testRun_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.testRun_probability

/-- info: 'SparseLinearSystems.Endpoint.finalCircuit_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.finalCircuit_unitary

/-- info: 'SparseLinearSystems.Endpoint.final_amp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.final_amp

/-- info: 'SparseLinearSystems.Endpoint.finalAmp_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.finalAmp_eq

/-- info: 'SparseLinearSystems.Endpoint.finalLeaf_successMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.finalLeaf_successMass

/-- info: 'SparseLinearSystems.Endpoint.finalLeaf_leafDir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.finalLeaf_leafDir

/-- info: 'SparseLinearSystems.Endpoint.finalLeaf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.finalLeaf_spec

/-- info: 'SparseLinearSystems.Endpoint.finalAmp_norm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.finalAmp_norm_sq_le

/-! ### `SparseLinearSystems.Endpoint.Correctness` -/

/-- info: 'SparseLinearSystems.Endpoint.norm_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.norm_source

/-- info: 'SparseLinearSystems.Endpoint.norm_beta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.norm_beta

/-- info: 'SparseLinearSystems.Endpoint.normA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.normA

/-- info: 'SparseLinearSystems.Endpoint.rho_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.rho_zero

/-- info: 'SparseLinearSystems.Endpoint.rho_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.rho_bounds

/-- info: 'SparseLinearSystems.Endpoint.rho_ladder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.rho_ladder

/-- info: 'SparseLinearSystems.Endpoint.test_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.test_bounds

/-- info: 'SparseLinearSystems.Endpoint.unitDirection_real_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.unitDirection_real_smul

/-- info: 'SparseLinearSystems.Endpoint.one_sub_pow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.one_sub_pow_le

/-- info: 'SparseLinearSystems.Endpoint.q_ratio_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.q_ratio_lower

/-- info: 'SparseLinearSystems.Endpoint.finalLeaf_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.finalLeaf_good

/-- info: 'SparseLinearSystems.Endpoint.correctness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.correctness

/-! ### `SparseLinearSystems.Endpoint.Cost` -/

/-- info: 'SparseLinearSystems.Endpoint.two_le_log_ten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.two_le_log_ten

/-- info: 'SparseLinearSystems.Endpoint.log_ten_le_logInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.log_ten_le_logInv

/-- info: 'SparseLinearSystems.Endpoint.two_le_logInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.two_le_logInv

/-- info: 'SparseLinearSystems.Endpoint.hundred_div_bLow_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.hundred_div_bLow_le

/-- info: 'SparseLinearSystems.Endpoint.ceil_pred_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.ceil_pred_le

/-- info: 'SparseLinearSystems.Endpoint.Ttest_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.Ttest_le

/-- info: 'SparseLinearSystems.Endpoint.Nfin_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.Nfin_sub_le

/-- info: 'SparseLinearSystems.Endpoint.kfin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.kfin_le

/-- info: 'SparseLinearSystems.Endpoint.reps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.reps_le

/-- info: 'SparseLinearSystems.Endpoint.sum_mul_half_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.sum_mul_half_pow

/-- info: 'SparseLinearSystems.Endpoint.two_pow_stages_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.two_pow_stages_le

/-- info: 'SparseLinearSystems.Endpoint.walkSteps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.walkSteps_le

/-- info: 'SparseLinearSystems.Endpoint.finalLeaf_worstCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.finalLeaf_worstCost

/-- info: 'SparseLinearSystems.Endpoint.algorithm_worstCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.algorithm_worstCost

/-- info: 'SparseLinearSystems.Endpoint.algorithm_matrix_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.algorithm_matrix_queries

/-- info: 'SparseLinearSystems.Endpoint.algorithm_source_queries' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.algorithm_source_queries

/-! ### `SparseLinearSystems.Endpoint.Main` -/

/-- info: 'SparseLinearSystems.Endpoint.Promise.norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.Promise.norm_le

/-- info: 'SparseLinearSystems.Endpoint.Promise.isUnit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.Promise.isUnit

/-- info: 'SparseLinearSystems.Endpoint.Promise.inverse_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.Promise.inverse_norm_le

/-- info: 'SparseLinearSystems.Endpoint.Promise.inverse_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.Promise.inverse_apply

/-- info: 'SparseLinearSystems.Endpoint.Promise.apply_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.Promise.apply_inverse

/-- info: 'SparseLinearSystems.Endpoint.Promise.lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.Promise.lower

/-- info: 'SparseLinearSystems.Endpoint.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.main

/-- info: 'SparseLinearSystems.Endpoint.main_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseLinearSystems.Endpoint.main_exists
