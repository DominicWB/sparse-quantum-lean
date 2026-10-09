import GateEfficientODE.Theorem
import GateEfficientODE.Time.Theorem

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 28 combinatorial lemmas about
wires, configurations and literal lists, whose reports list a subset of
these three axioms (or none). The audits cover every theorem of the
gate-efficient ODE library, beginning with the final theorems for constant
and time-dependent coefficients. -/

/-! ### Final theorem and public sizes -/

/-- info: 'SparseHamiltonian.GateODE.solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.solver

/-- info: 'SparseHamiltonian.GateODE.card_oWire' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.card_oWire

/-- info: 'SparseHamiltonian.GateODE.pow_clog_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.pow_clog_lt

/-- info: 'SparseHamiltonian.GateODE.Params.card_simWires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.card_simWires

/-- info: 'SparseHamiltonian.GateODE.Params.card_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.card_W

/-- info: 'SparseHamiltonian.GateODE.Params.degree_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.degree_bound

/-- info: 'SparseHamiltonian.GateODE.Params.sim_sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.sim_sizes

/-- info: 'SparseHamiltonian.GateODE.Params.l_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.l_bounds

/-- info: 'SparseHamiltonian.GateODE.Params.J_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.J_le

/-- info: 'SparseHamiltonian.GateODE.Params.J_le_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.J_le_log

/-- info: 'SparseHamiltonian.GateODE.Params.k_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.k_bounds

/-- info: 'SparseHamiltonian.GateODE.Params.prepGates_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.prepGates_eq

/-- info: 'SparseHamiltonian.GateODE.Params.reflGates_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.reflGates_eq

/-- info: 'SparseHamiltonian.GateODE.Params.gate_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.gate_count

/-- info: 'SparseHamiltonian.GateODE.Params.gate_count_grid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.gate_count_grid

/-! ### Time-dependent coefficients: final theorem and public sizes -/

/-- info: 'SparseHamiltonian.GateODE.Time.solver' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.solver

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.card_simWires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.card_simWires

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.card_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.card_W

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.degree_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.degree_bound

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.r_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.r_bounds

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.mesh_of_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.mesh_of_le

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.l_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.l_bounds

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.J_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.J_le

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.J_le_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.J_le_log

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.prepGates_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.prepGates_eq

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.reflGates_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.reflGates_eq

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.discretisation_exact_samples' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.discretisation_exact_samples

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.gate_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.gate_count

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.gate_count_grid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.gate_count_grid

/-! ### The complete protocol: programs, worst-case counts, success and output -/

/-- info: 'SparseHamiltonian.GateODE.Params.program_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.program_eval

/-- info: 'SparseHamiltonian.GateODE.Params.program_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.program_cost

/-- info: 'SparseHamiltonian.GateODE.Params.trial_cost_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.trial_cost_bound

/-- info: 'SparseHamiltonian.GateODE.Params.protocol_worst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.protocol_worst

/-- info: 'SparseHamiltonian.GateODE.Params.protocol_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.protocol_eq

/-- info: 'SparseHamiltonian.GateODE.Params.trials_choices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.trials_choices

/-- info: 'SparseHamiltonian.GateODE.Params.trials_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.trials_eval

/-- info: 'SparseHamiltonian.GateODE.Params.trials_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.trials_amplitude

/-- info: 'SparseHamiltonian.GateODE.Params.outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.outcome

/-! ### The analytic LCHS grid: contour shift, trapezoidal rule, analytic table -/

/-- info: 'SparseHamiltonian.StripQuadrature.abs_le_of_mem_uIcc_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.abs_le_of_mem_uIcc_zero

/-- info: 'SparseHamiltonian.StripQuadrature.rect_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.rect_identity

/-- info: 'SparseHamiltonian.StripQuadrature.integral_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.integral_shift

/-- info: 'SparseHamiltonian.StripQuadrature.norm_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.norm_phase

/-- info: 'SparseHamiltonian.StripQuadrature.phase_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.phase_ofReal

/-- info: 'SparseHamiltonian.StripQuadrature.phase_differentiable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.phase_differentiable

/-- info: 'SparseHamiltonian.StripQuadrature.fourier_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.fourier_norm_le

/-- info: 'SparseHamiltonian.StripQuadrature.envelope_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.envelope_eq

/-- info: 'SparseHamiltonian.StripQuadrature.envelope_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.envelope_integrable

/-- info: 'SparseHamiltonian.StripQuadrature.envelope_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.envelope_integral

/-- info: 'SparseHamiltonian.StripQuadrature.sq_tendsto_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.sq_tendsto_atTop

/-- info: 'SparseHamiltonian.StripQuadrature.sq_tendsto_atBot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.sq_tendsto_atBot

/-- info: 'SparseHamiltonian.StripQuadrature.envelope_tendsto_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.envelope_tendsto_atTop

/-- info: 'SparseHamiltonian.StripQuadrature.envelope_tendsto_atBot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.envelope_tendsto_atBot

/-- info: 'SparseHamiltonian.StripQuadrature.envelope_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.envelope_summable

/-- info: 'SparseHamiltonian.StripQuadrature.denominator_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.denominator_lower

/-- info: 'SparseHamiltonian.StripQuadrature.hasSum_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.hasSum_two_sided

/-- info: 'SparseHamiltonian.StripQuadrature.geometric_ratio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.geometric_ratio

/-- info: 'SparseHamiltonian.StripQuadrature.trapezoid_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.trapezoid_error

/-- info: 'SparseHamiltonian.StripQuadrature.opNorm_le_of_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.opNorm_le_of_inner

/-- info: 'SparseHamiltonian.StripQuadrature.trapezoid_error_op' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.trapezoid_error_op

/-- info: 'SparseHamiltonian.StripQuadrature.cauchy_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.StripQuadrature.cauchy_sum_le

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.evolution_norm_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.evolution_norm_le_exp

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.kernel_denominator_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.kernel_denominator_ne

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.kernel_differentiableAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.kernel_differentiableAt

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.kernel_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.kernel_norm_le

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.log_arg_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.log_arg_pos

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.stepBound_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.stepBound_pos

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.radius_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.radius_pos

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.halfCount_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.halfCount_pos

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.step_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.step_pos

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.radius_eq_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.radius_eq_mul

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.step_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.step_le

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.exp_step_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.exp_step_ge

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.gridSize_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.gridSize_pos

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.gridSize_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.gridSize_le

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.nodes_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.nodes_abs_le

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.sum_fin_eq_sum_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.sum_fin_eq_sum_Icc

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.node_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.node_cast

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.mass_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.mass_le

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.exp_three_halves_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.exp_three_halves_le

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.residual_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.residual_le

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.exp_step_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.exp_step_large

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.trapezoid_term_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.trapezoid_term_le

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.cauchy_factor_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.cauchy_factor_le

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.strip_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.strip_bound

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.finite_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.finite_sum_eq

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.tail_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.tail_bound

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.table_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.table_error

/-- info: 'SparseHamiltonian.GateODE.AnalyticLCHS.table_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.AnalyticLCHS.table_certificate

/-! ### Instruction model: exposure, instructions, block estimate -/

/-- info: 'SparseHamiltonian.GateODE.overwrite_apply_ι' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.overwrite_apply_ι

/-- info: 'SparseHamiltonian.GateODE.overwrite_apply_out' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.overwrite_apply_out

/-- info: 'SparseHamiltonian.GateODE.overwrite_overwrite_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.overwrite_overwrite_comp

/-- info: 'SparseHamiltonian.GateODE.clearCfg_clearCfg_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.clearCfg_clearCfg_comp

/-- info: 'SparseHamiltonian.GateODE.clearCfg_comp_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.clearCfg_comp_restrict

/-- info: 'SparseHamiltonian.GateODE.localOp_localOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.localOp_localOp

/-- info: 'SparseHamiltonian.GateODE.localOp_localOp'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.localOp_localOp'

/-- info: 'SparseHamiltonian.GateODE.ctrlOK_map' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.ctrlOK_map

/-- info: 'SparseHamiltonian.GateODE.update_comp_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.update_comp_injective

/-- info: 'SparseHamiltonian.GateODE.localOp_gateOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.localOp_gateOp

/-- info: 'SparseHamiltonian.GateODE.Gate.map_op' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Gate.map_op

/-- info: 'SparseHamiltonian.GateODE.localOp_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.localOp_sub

/-- info: 'SparseHamiltonian.GateODE.put_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.put_apply

/-- info: 'SparseHamiltonian.GateODE.localOp_put' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.localOp_put

/-- info: 'SparseHamiltonian.GateODE.norm_put' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.norm_put

/-- info: 'SparseHamiltonian.GateODE.norm_sum_put_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.norm_sum_put_sq

/-- info: 'SparseHamiltonian.GateODE.pctl_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.pctl_apply

/-- info: 'SparseHamiltonian.GateODE.pctl_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.pctl_bas

/-- info: 'SparseHamiltonian.GateODE.pctl_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.pctl_comp

/-- info: 'SparseHamiltonian.GateODE.pctl_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.pctl_one

/-- info: 'SparseHamiltonian.GateODE.pctl_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.pctl_adjoint

/-- info: 'SparseHamiltonian.GateODE.pctl_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.pctl_isUnitary

/-- info: 'SparseHamiltonian.GateODE.pres2_pctl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.pres2_pctl

/-- info: 'SparseHamiltonian.GateODE.adjIf_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.adjIf_adjoint

/-- info: 'SparseHamiltonian.GateODE.adjIf_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.adjIf_isUnitary

/-- info: 'SparseHamiltonian.GateODE.projector_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.projector_star

/-- info: 'SparseHamiltonian.GateODE.seedRefl_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.seedRefl_adjoint

/-- info: 'SparseHamiltonian.GateODE.seedRefl_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.seedRefl_isUnitary

/-- info: 'SparseHamiltonian.GateODE.OInstr.eval_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.OInstr.eval_gate

/-- info: 'SparseHamiltonian.GateODE.OInstr.eval_uj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.OInstr.eval_uj

/-- info: 'SparseHamiltonian.GateODE.OInstr.eval_priv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.OInstr.eval_priv

/-- info: 'SparseHamiltonian.GateODE.OInstr.eval_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.OInstr.eval_src

/-- info: 'SparseHamiltonian.GateODE.OInstr.eval_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.OInstr.eval_seed

/-- info: 'SparseHamiltonian.GateODE.OInstr.isGate_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.OInstr.isGate_inv

/-- info: 'SparseHamiltonian.GateODE.OInstr.isUJ_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.OInstr.isUJ_inv

/-- info: 'SparseHamiltonian.GateODE.OInstr.isPriv_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.OInstr.isPriv_inv

/-- info: 'SparseHamiltonian.GateODE.OInstr.isSrc_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.OInstr.isSrc_inv

/-- info: 'SparseHamiltonian.GateODE.OInstr.isSeed_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.OInstr.isSeed_inv

/-- info: 'SparseHamiltonian.GateODE.OInstr.valid_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.OInstr.valid_inv

/-- info: 'SparseHamiltonian.GateODE.OInstr.eval_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.OInstr.eval_inv

/-- info: 'SparseHamiltonian.GateODE.OInstr.eval_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.OInstr.eval_isUnitary

/-- info: 'SparseHamiltonian.GateODE.run_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.run_nil

/-- info: 'SparseHamiltonian.GateODE.run_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.run_cons

/-- info: 'SparseHamiltonian.GateODE.run_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.run_append

/-- info: 'SparseHamiltonian.GateODE.run_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.run_singleton

/-- info: 'SparseHamiltonian.GateODE.run_invList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.run_invList

/-- info: 'SparseHamiltonian.GateODE.run_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.run_isUnitary

/-- info: 'SparseHamiltonian.GateODE.valid_invList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.valid_invList

/-- info: 'SparseHamiltonian.GateODE.nGates_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.nGates_append

/-- info: 'SparseHamiltonian.GateODE.nUJ_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.nUJ_append

/-- info: 'SparseHamiltonian.GateODE.nPriv_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.nPriv_append

/-- info: 'SparseHamiltonian.GateODE.nSrc_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.nSrc_append

/-- info: 'SparseHamiltonian.GateODE.nSeed_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.nSeed_append

/-- info: 'SparseHamiltonian.GateODE.nGates_invList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.nGates_invList

/-- info: 'SparseHamiltonian.GateODE.nUJ_invList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.nUJ_invList

/-- info: 'SparseHamiltonian.GateODE.nPriv_invList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.nPriv_invList

/-- info: 'SparseHamiltonian.GateODE.nSrc_invList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.nSrc_invList

/-- info: 'SparseHamiltonian.GateODE.nSeed_invList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.nSeed_invList

/-- info: 'SparseHamiltonian.GateODE.run_ofGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.run_ofGates

/-- info: 'SparseHamiltonian.GateODE.ofGates_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.ofGates_append

/-- info: 'SparseHamiltonian.GateODE.nGates_ofGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.nGates_ofGates

/-- info: 'SparseHamiltonian.GateODE.ofGates_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.ofGates_counts

/-- info: 'SparseHamiltonian.GateODE.valid_ofGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.valid_ofGates

/-- info: 'SparseHamiltonian.GateODE.eval_embI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.eval_embI

/-- info: 'SparseHamiltonian.GateODE.run_map_embI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.run_map_embI

/-- info: 'SparseHamiltonian.GateODE.embI_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.embI_valid

/-- info: 'SparseHamiltonian.GateODE.embI_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.embI_counts

/-- info: 'SparseHamiltonian.GateODE.toProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.toProgram_eval

/-- info: 'SparseHamiltonian.GateODE.toProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.toProgram_cost

/-- info: 'SparseHamiltonian.GateODE.sum_map_indicator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.sum_map_indicator

/-- info: 'SparseHamiltonian.GateODE.basL_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.basL_apply

/-- info: 'SparseHamiltonian.GateODE.basL_adjoint_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.basL_adjoint_comp

/-- info: 'SparseHamiltonian.GateODE.cfg_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.cfg_eq_iff

/-- info: 'SparseHamiltonian.GateODE.bas_eq_put' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.bas_eq_put

/-- info: 'SparseHamiltonian.GateODE.put_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.put_sub

/-- info: 'SparseHamiltonian.GateODE.branchEmb_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.branchEmb_apply

/-- info: 'SparseHamiltonian.GateODE.branchEmb_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.branchEmb_isometry

/-- info: 'SparseHamiltonian.GateODE.localOp_branch_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.localOp_branch_error

/-! ### Uniformly controlled gadgets: rotation trees, diagonal phases -/

/-- info: 'SparseHamiltonian.GateODE.wordOf_update' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.wordOf_update

/-- info: 'SparseHamiltonian.GateODE.wordOf_update_other' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.wordOf_update_other

/-- info: 'SparseHamiltonian.GateODE.mem_prefLitsG' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.mem_prefLitsG

/-- info: 'SparseHamiltonian.GateODE.prefLitsG_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.prefLitsG_length

/-- info: 'SparseHamiltonian.GateODE.prefLitsG_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.prefLitsG_iff

/-- info: 'SparseHamiltonian.GateODE.prefLitsG_ne_t' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.prefLitsG_ne_t

/-- info: 'SparseHamiltonian.GateODE.ucgT_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.ucgT_agrees

/-- info: 'SparseHamiltonian.GateODE.ucgT_full_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.ucgT_full_agrees

/-- info: 'SparseHamiltonian.GateODE.ucgT_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.ucgT_length

/-- info: 'SparseHamiltonian.GateODE.ucgT_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.ucgT_ok

/-- info: 'SparseHamiltonian.GateODE.prepT_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.prepT_agrees

/-- info: 'SparseHamiltonian.GateODE.prepT_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.prepT_length

/-- info: 'SparseHamiltonian.GateODE.prepT_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.prepT_length_le

/-- info: 'SparseHamiltonian.GateODE.prepT_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.prepT_ok

/-- info: 'SparseHamiltonian.GateODE.treeOp_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.treeOp_zero

/-- info: 'SparseHamiltonian.GateODE.phaseMat_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.phaseMat_unitary

/-- info: 'SparseHamiltonian.GateODE.phaseT_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.phaseT_agrees

/-- info: 'SparseHamiltonian.GateODE.phaseOp_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.phaseOp_bas

/-- info: 'SparseHamiltonian.GateODE.phaseT_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.phaseT_length

/-- info: 'SparseHamiltonian.GateODE.gRun_constT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.gRun_constT

/-- info: 'SparseHamiltonian.GateODE.constT_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.constT_length

/-- info: 'SparseHamiltonian.GateODE.constT_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.constT_ok

/-! ### Wires, labels and clean configurations -/

/-- info: 'SparseHamiltonian.GateODE.poolClean_of_workClean' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.poolClean_of_workClean

/-- info: 'SparseHamiltonian.GateODE.mem_poolList' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.mem_poolList

/-- info: 'SparseHamiltonian.GateODE.poolList_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.poolList_nodup

/-- info: 'SparseHamiltonian.GateODE.poolList_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.poolList_length

/-- info: 'SparseHamiltonian.GateODE.poolClean_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.poolClean_iff

/-- info: 'SparseHamiltonian.GateODE.labOf_cfgOf' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.labOf_cfgOf

/-- info: 'SparseHamiltonian.GateODE.cfgOf_inl' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.cfgOf_inl

/-- info: 'SparseHamiltonian.GateODE.workClean_cfgOf' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.workClean_cfgOf

/-- info: 'SparseHamiltonian.GateODE.cfgOf_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.cfgOf_injective

/-- info: 'SparseHamiltonian.GateODE.outPart_cfgOf_injective' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.outPart_cfgOf_injective

/-- info: 'SparseHamiltonian.GateODE.cfgOf_zero' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.cfgOf_zero

/-- info: 'SparseHamiltonian.GateODE.lchTS_injective' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.lchTS_injective

/-- info: 'SparseHamiltonian.GateODE.lchTree_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.lchTree_ok

/-- info: 'SparseHamiltonian.GateODE.srcTS_injective' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.srcTS_injective

/-! ### Zero-test and seed reflections -/

/-- info: 'SparseHamiltonian.GateODE.basL_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.basL_adjoint_apply

/-- info: 'SparseHamiltonian.GateODE.zeroLits_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.zeroLits_length

/-- info: 'SparseHamiltonian.GateODE.mem_zeroLits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.mem_zeroLits

/-- info: 'SparseHamiltonian.GateODE.zeroLits_ne_flg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.zeroLits_ne_flg

/-- info: 'SparseHamiltonian.GateODE.zeroLits_ne_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.zeroLits_ne_pool

/-- info: 'SparseHamiltonian.GateODE.ctrlOK_zeroLits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.ctrlOK_zeroLits

/-- info: 'SparseHamiltonian.GateODE.zeroLits_length_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.zeroLits_length_le

/-- info: 'SparseHamiltonian.GateODE.poolClean_update_flg' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.poolClean_update_flg

/-- info: 'SparseHamiltonian.GateODE.poolClean_clean' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.poolClean_clean

/-- info: 'SparseHamiltonian.GateODE.flagGate_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.flagGate_agrees

/-- info: 'SparseHamiltonian.GateODE.goodF_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.goodF_isometry

/-- info: 'SparseHamiltonian.GateODE.rgoodI_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.rgoodI_bas

/-- info: 'SparseHamiltonian.GateODE.rgood_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.rgood_agrees

/-- info: 'SparseHamiltonian.GateODE.rgoodI_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.rgoodI_isUnitary

/-- info: 'SparseHamiltonian.GateODE.rgoodI_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.rgoodI_adjoint

/-- info: 'SparseHamiltonian.GateODE.workClean_zero' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.workClean_zero

/-- info: 'SparseHamiltonian.GateODE.pres2_rgoodI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.pres2_rgoodI

/-- info: 'SparseHamiltonian.GateODE.seedState_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.seedState_norm

/-- info: 'SparseHamiltonian.GateODE.rseedI_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.rseedI_bas

/-- info: 'SparseHamiltonian.GateODE.flagG_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.flagG_bas

/-- info: 'SparseHamiltonian.GateODE.rseed_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.rseed_agrees

/-- info: 'SparseHamiltonian.GateODE.rseedI_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.rseedI_isUnitary

/-- info: 'SparseHamiltonian.GateODE.rseedI_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.rseedI_adjoint

/-- info: 'SparseHamiltonian.GateODE.pres2_rseedI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.pres2_rseedI

/-! ### Trial circuits, validity and exact counts -/

/-- info: 'SparseHamiltonian.GateODE.Params.l_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.l_pos

/-- info: 'SparseHamiltonian.GateODE.Params.J_add_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.J_add_two_le

/-- info: 'SparseHamiltonian.GateODE.Params.l_le_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.l_le_pool

/-- info: 'SparseHamiltonian.GateODE.Params.zero_test_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.zero_test_le

/-- info: 'SparseHamiltonian.GateODE.sim_public' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.sim_public

/-- info: 'SparseHamiltonian.GateODE.countP_replicate_flatten' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.countP_replicate_flatten

/-- info: 'SparseHamiltonian.GateODE.Params.select_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.select_counts

/-- info: 'SparseHamiltonian.GateODE.Params.load_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.load_counts

/-- info: 'SparseHamiltonian.GateODE.Params.srcPrep_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.srcPrep_length

/-- info: 'SparseHamiltonian.GateODE.Params.lchPrep_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.lchPrep_length

/-- info: 'SparseHamiltonian.GateODE.Params.lchPhase_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.lchPhase_length

/-- info: 'SparseHamiltonian.GateODE.Params.prepC_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.prepC_counts

/-- info: 'SparseHamiltonian.GateODE.Params.rgoodG_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.rgoodG_length

/-- info: 'SparseHamiltonian.GateODE.Params.flagG_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.flagG_length

/-- info: 'SparseHamiltonian.GateODE.Params.rseedC_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.rseedC_counts

/-- info: 'SparseHamiltonian.GateODE.Params.stepC_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.stepC_counts

/-- info: 'SparseHamiltonian.GateODE.Params.trialC_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.trialC_counts

/-- info: 'SparseHamiltonian.GateODE.Params.srcMat_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.srcMat_unitary

/-- info: 'SparseHamiltonian.GateODE.Params.prepC_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.prepC_valid

/-- info: 'SparseHamiltonian.GateODE.Params.stepC_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.stepC_valid

/-- info: 'SparseHamiltonian.GateODE.Params.trialC_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.trialC_valid

/-! ### Agreement with the ideal amplification -/

/-- info: 'SparseHamiltonian.GateODE.pres2_treeFrom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.pres2_treeFrom

/-- info: 'SparseHamiltonian.GateODE.treeFrom_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.treeFrom_isUnitary

/-- info: 'SparseHamiltonian.GateODE.gateOp_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.gateOp_neg_one

/-- info: 'SparseHamiltonian.GateODE.Agrees.comp'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Agrees.comp'

/-- info: 'SparseHamiltonian.GateODE.Preserves.of_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Preserves.of_agrees

/-- info: 'SparseHamiltonian.GateODE.projector_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.projector_map

/-- info: 'SparseHamiltonian.GateODE.workClean_update_inl' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.workClean_update_inl

/-- info: 'SparseHamiltonian.GateODE.workClean_update_inr' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.workClean_update_inr

/-- info: 'SparseHamiltonian.GateODE.workClean_overwrite_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.workClean_overwrite_inl

/-- info: 'SparseHamiltonian.GateODE.pres2_localOp_inl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.pres2_localOp_inl

/-- info: 'SparseHamiltonian.GateODE.pres2_run_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.pres2_run_select

/-- info: 'SparseHamiltonian.GateODE.srcTS_stable' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.srcTS_stable

/-- info: 'SparseHamiltonian.GateODE.lchTS_stable' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.lchTS_stable

/-- info: 'SparseHamiltonian.GateODE.Params.run_srcPrep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.run_srcPrep

/-- info: 'SparseHamiltonian.GateODE.Params.pres2_SP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.pres2_SP

/-- info: 'SparseHamiltonian.GateODE.Params.pres2_LP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.pres2_LP

/-- info: 'SparseHamiltonian.GateODE.Params.pres2_PH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.pres2_PH

/-- info: 'SparseHamiltonian.GateODE.Params.SP_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.SP_isUnitary

/-- info: 'SparseHamiltonian.GateODE.Params.LP_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.LP_isUnitary

/-- info: 'SparseHamiltonian.GateODE.Params.PH_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.PH_isUnitary

/-- info: 'SparseHamiltonian.GateODE.Params.pres2_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.pres2_load

/-- info: 'SparseHamiltonian.GateODE.Params.lchPrep_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.lchPrep_agrees

/-- info: 'SparseHamiltonian.GateODE.Params.lchPhase_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.lchPhase_agrees

/-- info: 'SparseHamiltonian.GateODE.Params.prepC_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.prepC_agrees

/-- info: 'SparseHamiltonian.GateODE.Params.pres2_Wideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.pres2_Wideal

/-- info: 'SparseHamiltonian.GateODE.Params.prepC_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.prepC_isUnitary

/-- info: 'SparseHamiltonian.GateODE.Params.Wideal_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.Wideal_isUnitary

/-- info: 'SparseHamiltonian.GateODE.Params.pres2_prepC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.pres2_prepC

/-- info: 'SparseHamiltonian.GateODE.Params.stepC_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.stepC_agrees

/-- info: 'SparseHamiltonian.GateODE.Params.pres_groverStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.pres_groverStep

/-- info: 'SparseHamiltonian.GateODE.Params.steps_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.steps_agree

/-- info: 'SparseHamiltonian.GateODE.Params.trialC_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.trialC_seed

/-- info: 'SparseHamiltonian.GateODE.Params.decoded_prepC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.decoded_prepC

/-! ### Padded LCHS words, source input and output identification -/

/-- info: 'SparseHamiltonian.GateODE.sum_padIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.sum_padIdx

/-- info: 'SparseHamiltonian.GateODE.norm_elim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.norm_elim

/-- info: 'SparseHamiltonian.GateODE.smul_elim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.smul_elim

/-- info: 'SparseHamiltonian.GateODE.Params.table_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.table_mass_le

/-- info: 'SparseHamiltonian.GateODE.Params.coeffW_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.coeffW_sum_eq

/-- info: 'SparseHamiltonian.GateODE.Params.coeffW_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.coeffW_mass

/-- info: 'SparseHamiltonian.GateODE.Params.lchAmp_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.lchAmp_nonneg

/-- info: 'SparseHamiltonian.GateODE.Params.lchAmp_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.lchAmp_sq

/-- info: 'SparseHamiltonian.GateODE.Params.lchAmp_sq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.lchAmp_sq_sum

/-- info: 'SparseHamiltonian.GateODE.Params.nodeW_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.nodeW_abs_le

/-- info: 'SparseHamiltonian.GateODE.Params.coeffW_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.coeffW_sum

/-- info: 'SparseHamiltonian.GateODE.setLow_apply_ts' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.setLow_apply_ts

/-- info: 'SparseHamiltonian.GateODE.coefficientPhase_ofReal_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.coefficientPhase_ofReal_mul

/-- info: 'SparseHamiltonian.GateODE.phaseMat_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.phaseMat_conjTranspose

/-- info: 'SparseHamiltonian.GateODE.phaseOp_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.phaseOp_adjoint

/-- info: 'SparseHamiltonian.GateODE.Params.branchE_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.branchE_isometry

/-- info: 'SparseHamiltonian.GateODE.Params.setLow_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.setLow_src

/-- info: 'SparseHamiltonian.GateODE.Params.setLow_lch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.setLow_lch

/-- info: 'SparseHamiltonian.GateODE.Params.srcMat_prod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.srcMat_prod

/-- info: 'SparseHamiltonian.GateODE.Params.SP_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.SP_zero

/-- info: 'SparseHamiltonian.GateODE.Params.LP_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.LP_src

/-- info: 'SparseHamiltonian.GateODE.Params.wiring_ini' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.wiring_ini

/-- info: 'SparseHamiltonian.GateODE.Params.load_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.load_bas

/-- info: 'SparseHamiltonian.GateODE.Params.labels_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.labels_zero

/-- info: 'SparseHamiltonian.GateODE.Params.norm_zsrc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.norm_zsrc

/-- info: 'SparseHamiltonian.GateODE.Params.mass_zsrc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.mass_zsrc

/-- info: 'SparseHamiltonian.GateODE.Params.srcAmp_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.srcAmp_sq

/-- info: 'SparseHamiltonian.GateODE.Params.srcAmp_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.srcAmp_nonneg

/-- info: 'SparseHamiltonian.GateODE.Params.sqrt_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.sqrt_probability

/-- info: 'SparseHamiltonian.GateODE.Params.inMap_eq_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.inMap_eq_input

/-- info: 'SparseHamiltonian.GateODE.Params.outMap_eq_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.outMap_eq_output

/-! ### Coherent selection of the released simulator -/

/-- info: 'SparseHamiltonian.GateODE.Params.dur_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.dur_nonneg

/-- info: 'SparseHamiltonian.GateODE.Params.dur_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.dur_le

/-- info: 'SparseHamiltonian.GateODE.Params.branchH_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.branchH_selfAdjoint

/-- info: 'SparseHamiltonian.GateODE.Params.branchH_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.branchH_norm_le

/-- info: 'SparseHamiltonian.GateODE.Params.exp_branchH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.exp_branchH

/-- info: 'SparseHamiltonian.GateODE.Params.branch_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.branch_block

/-- info: 'SparseHamiltonian.GateODE.Params.select_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.select_error

/-! ### LCHS and source quadrature -/

/-- info: 'SparseHamiltonian.GateODE.gen_dissipative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.gen_dissipative

/-- info: 'SparseHamiltonian.GateODE.Params.lchs_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.lchs_error

/-- info: 'SparseHamiltonian.GateODE.Params.two_pow_k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.two_pow_k

/-- info: 'SparseHamiltonian.GateODE.Params.sum_words_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.sum_words_eq

/-- info: 'SparseHamiltonian.GateODE.Params.smul_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.smul_ofReal

/-- info: 'SparseHamiltonian.GateODE.Params.source_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.source_sum_eq

/-- info: 'SparseHamiltonian.GateODE.Params.quadrature_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.quadrature_error

/-- info: 'SparseHamiltonian.GateODE.Params.solution_le_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.solution_le_mass

/-! ### The actual-source certificate and trial bounds -/

/-- info: 'SparseHamiltonian.GateODE.Params.PublicOK.eps_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.PublicOK.eps_le_one

/-- info: 'SparseHamiltonian.GateODE.Params.PublicOK.tau_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.PublicOK.tau_pos

/-- info: 'SparseHamiltonian.GateODE.Params.PublicOK.nu_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.PublicOK.nu_pos

/-- info: 'SparseHamiltonian.GateODE.Params.PublicOK.TD_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.PublicOK.TD_nonneg

/-- info: 'SparseHamiltonian.GateODE.Params.unitaries_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.unitaries_of

/-- info: 'SparseHamiltonian.GateODE.Params.prep_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.prep_certificate

/-- info: 'SparseHamiltonian.GateODE.Params.decoded_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.decoded_eq

/-- info: 'SparseHamiltonian.GateODE.Params.trial_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Params.trial_bounds

/-! ### Time-dependent coefficients: the complete protocol, worst-case counts, success and output -/

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.program_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.program_eval

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.program_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.program_cost

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.trial_cost_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.trial_cost_bound

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.protocol_worst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.protocol_worst

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.protocol_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.protocol_eq

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.trials_choices' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.trials_choices

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.trials_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.trials_eval

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.trials_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.trials_output

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.trials_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.trials_seed

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.trials_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.trials_amplitude

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.outcome

/-! ### Time-dependent coefficients: instruction model -/

/-- info: 'SparseHamiltonian.GateODE.Time.psel_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.psel_apply

/-- info: 'SparseHamiltonian.GateODE.Time.psel_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.psel_bas

/-- info: 'SparseHamiltonian.GateODE.Time.psel_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.psel_comp

/-- info: 'SparseHamiltonian.GateODE.Time.psel_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.psel_one

/-- info: 'SparseHamiltonian.GateODE.Time.psel_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.psel_adjoint

/-- info: 'SparseHamiltonian.GateODE.Time.psel_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.psel_isUnitary

/-- info: 'SparseHamiltonian.GateODE.Time.pres2_psel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.pres2_psel

/-- info: 'SparseHamiltonian.GateODE.Time.teval_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.teval_gate

/-- info: 'SparseHamiltonian.GateODE.Time.teval_uj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.teval_uj

/-- info: 'SparseHamiltonian.GateODE.Time.teval_priv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.teval_priv

/-- info: 'SparseHamiltonian.GateODE.Time.teval_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.teval_load

/-- info: 'SparseHamiltonian.GateODE.Time.teval_wprep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.teval_wprep

/-- info: 'SparseHamiltonian.GateODE.Time.teval_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.teval_seed

/-- info: 'SparseHamiltonian.GateODE.Time.wprep_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.wprep_adjoint

/-- info: 'SparseHamiltonian.GateODE.Time.teval_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.teval_inv

/-- info: 'SparseHamiltonian.GateODE.Time.wprep_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.wprep_isUnitary

/-- info: 'SparseHamiltonian.GateODE.Time.teval_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.teval_isUnitary

/-- info: 'SparseHamiltonian.GateODE.Time.trun_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.trun_nil

/-- info: 'SparseHamiltonian.GateODE.Time.trun_cons' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.trun_cons

/-- info: 'SparseHamiltonian.GateODE.Time.trun_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.trun_append

/-- info: 'SparseHamiltonian.GateODE.Time.trun_singleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.trun_singleton

/-- info: 'SparseHamiltonian.GateODE.Time.trun_invList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.trun_invList

/-- info: 'SparseHamiltonian.GateODE.Time.trun_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.trun_isUnitary

/-- info: 'SparseHamiltonian.GateODE.Time.trun_ofGates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.trun_ofGates

/-- info: 'SparseHamiltonian.GateODE.Time.trun_eq_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.trun_eq_run

/-- info: 'SparseHamiltonian.GateODE.Time.teval_embI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.teval_embI

/-- info: 'SparseHamiltonian.GateODE.Time.trun_map_embI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.trun_map_embI

/-- info: 'SparseHamiltonian.GateODE.Time.ttoProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.ttoProgram_eval

/-- info: 'SparseHamiltonian.GateODE.Time.ttoProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.ttoProgram_cost

/-! ### Time-dependent coefficients: trial circuits, validity and exact counts -/

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.l_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.l_pos

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.J_add_two_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.J_add_two_le

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.l_le_pool' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.l_le_pool

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.zero_test_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.zero_test_le

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.M_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.M_pos

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.select_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.select_counts

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.lchPrep_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.lchPrep_length

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.lchPhase_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.lchPhase_length

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.prepC_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.prepC_counts

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.rgoodG_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.rgoodG_length

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.flagG_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.flagG_length

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.rseedC_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.rseedC_counts

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.stepC_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.stepC_counts

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.trialC_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.trialC_counts

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.prepC_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.prepC_valid

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.stepC_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.stepC_valid

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.trialC_valid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.trialC_valid

/-! ### Time-dependent coefficients: agreement with the ideal amplification -/

/-- info: 'SparseHamiltonian.GateODE.Time.workClean_overwrite_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.workClean_overwrite_src

/-- info: 'SparseHamiltonian.GateODE.Time.pres2_wprep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.pres2_wprep

/-- info: 'SparseHamiltonian.GateODE.Time.pres2_trun_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.pres2_trun_select

/-- info: 'SparseHamiltonian.GateODE.Time.rseedT_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.rseedT_agrees

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.pres2_LP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.pres2_LP

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.pres2_PH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.pres2_PH

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.LP_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.LP_isUnitary

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.PH_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.PH_isUnitary

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.pres2_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.pres2_load

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.run_wprepC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.run_wprepC

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.lchPrep_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.lchPrep_agrees

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.lchPhase_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.lchPhase_agrees

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.prepC_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.prepC_agrees

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.pres2_Wideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.pres2_Wideal

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.prepC_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.prepC_isUnitary

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.Wideal_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.Wideal_isUnitary

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.pres2_prepC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.pres2_prepC

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.stepC_agrees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.stepC_agrees

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.pres_groverStep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.pres_groverStep

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.steps_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.steps_agree

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.trialC_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.trialC_seed

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.decoded_prepC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.decoded_prepC

/-! ### Time-dependent coefficients: padded words, weight promise and source input -/

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.ratio_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.ratio_ge

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.acc_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.acc_pos

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.acc_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.acc_le_one

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.table_mass_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.table_mass_le

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.coeffW_sum_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.coeffW_sum_eq

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.coeffW_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.coeffW_mass

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.lchAmp_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.lchAmp_nonneg

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.lchAmp_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.lchAmp_sq

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.lchAmp_sq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.lchAmp_sq_sum

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.nodeW_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.nodeW_abs_le

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.coeffW_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.coeffW_sum

/-- info: 'SparseHamiltonian.GateODE.Time.matOp_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.matOp_bas

/-- info: 'SparseHamiltonian.GateODE.Time.localOp_matOp_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.localOp_matOp_bas

/-- info: 'SparseHamiltonian.GateODE.Time.overwrite_src_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.overwrite_src_zero

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.wordValue_zero'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.wordValue_zero'

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.mass_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.mass_eq

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.srcAmp_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.srcAmp_nonneg

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.srcAmp_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.srcAmp_sq

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.branchE_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.branchE_isometry

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.WP_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.WP_zero

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.LP_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.LP_src

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.load_bas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.load_bas

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.labels_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.labels_zero

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.sqrt_probability' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.sqrt_probability

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.inMap_eq_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.inMap_eq_input

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.outMap_eq_output' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.outMap_eq_output

/-! ### Time-dependent coefficients: coherent slot-selected selection -/

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.nu_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.nu_pos

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.nu_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.nu_le_one

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.mask_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.mask_le_one

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.dur_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.dur_nonneg

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.dur_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.dur_le

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.branchH_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.branchH_selfAdjoint

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.branchH_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.branchH_norm_le

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.exp_branchH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.exp_branchH

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.evolution_branchH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.evolution_branchH

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.clock_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.clock_family

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.branch_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.branch_block

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.select_error_of_blocks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.select_error_of_blocks

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.select_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.select_error

/-! ### Time-dependent coefficients: product growth, LCHS, source sum and discretisation -/

/-- info: 'SparseHamiltonian.GateODE.Time.productFamily_norm_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.productFamily_norm_le_exp

/-- info: 'SparseHamiltonian.GateODE.Time.slot_accretive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.slot_accretive

/-- info: 'SparseHamiltonian.GateODE.Time.recurrence_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.recurrence_congr

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.sum_dur_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.sum_dur_le

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.family_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.family_ofReal

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.family_neg_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.family_neg_I

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.lchs_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.lchs_error

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.source_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.source_sum

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.target_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.target_norm_le

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.discretisation_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.discretisation_error

/-! ### Time-dependent coefficients: certificate and trial bounds -/

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.PublicOK.eps_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.PublicOK.eps_le_one

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.PublicOK.tau_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.PublicOK.tau_pos

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.PublicOK.nu_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.PublicOK.nu_pos

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.PublicOK.TD_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.PublicOK.TD_nonneg

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.unitary_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.unitary_of

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.target_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.target_facts

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.prep_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.prep_certificate

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.decoded_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.decoded_eq

/-- info: 'SparseHamiltonian.GateODE.Time.TParams.trial_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateODE.Time.TParams.trial_bounds
