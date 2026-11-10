import MixedOutputODE.TraceNorm
import MixedOutputODE.PartialTrace
import MixedOutputODE.Selection
import MixedOutputODE.Interface
import MixedOutputODE.Protocol
import MixedOutputODE.Theorem
import MixedOutputODE.Complexity

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (65 theorems), beginning
with the main theorems, then in module order. Every report lists exactly `propext`,
`Classical.choice` and `Quot.sound`. -/

/-! ### Final theorems: Theorem `ode:thm:general` with a mixed-output solver, the selection estimate
and the partial trace -/

/-- info: 'SparseHamiltonian.MixedOutputODE.general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.general

/-- info: 'SparseHamiltonian.MixedOutputODE.general_query_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.general_query_bound

/-- info: 'SparseHamiltonian.MixedOutputODE.general_of_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.general_of_block

/-- info: 'SparseHamiltonian.MixedOutputODE.mixed_of_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.mixed_of_block

/-- info: 'SparseHamiltonian.MixedOutputODE.exists_mixed_protocol_of_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.exists_mixed_protocol_of_block

/-- info: 'SparseHamiltonian.MixedOutputODE.selection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.selection

/-- info: 'SparseHamiltonian.MixedOutputODE.tnorm_compress_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.tnorm_compress_le

/-- info: 'SparseHamiltonian.MixedOutputODE.ptrace_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.ptrace_conj

/-! ### The trace norm of self-adjoint operators (`TraceNorm`) -/

/-- info: 'SparseHamiltonian.MixedOutputODE.tnorm_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.tnorm_nonneg

/-- info: 'SparseHamiltonian.MixedOutputODE.tnorm_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.tnorm_congr

/-- info: 'SparseHamiltonian.MixedOutputODE.hermitianTraceDistance_eq_tnorm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.hermitianTraceDistance_eq_tnorm

/-- info: 'SparseHamiltonian.MixedOutputODE.apply_eig' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.apply_eig

/-- info: 'SparseHamiltonian.MixedOutputODE.tnorm_eq_diagonalMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.tnorm_eq_diagonalMass

/-- info: 'SparseHamiltonian.MixedOutputODE.norm_tr_comp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.norm_tr_comp_le

/-- info: 'SparseHamiltonian.MixedOutputODE.mul_sgn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.mul_sgn

/-- info: 'SparseHamiltonian.MixedOutputODE.norm_sgn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.norm_sgn

/-- info: 'SparseHamiltonian.MixedOutputODE.inner_signOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.inner_signOp

/-- info: 'SparseHamiltonian.MixedOutputODE.norm_signOp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.norm_signOp_le

/-- info: 'SparseHamiltonian.MixedOutputODE.tr_signOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.tr_signOp

/-- info: 'SparseHamiltonian.MixedOutputODE.tr_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.tr_add

/-- info: 'SparseHamiltonian.MixedOutputODE.tr_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.tr_sub

/-- info: 'SparseHamiltonian.MixedOutputODE.tr_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.tr_smul

/-- info: 'SparseHamiltonian.MixedOutputODE.tnorm_eq_norm_tr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.tnorm_eq_norm_tr

/-- info: 'SparseHamiltonian.MixedOutputODE.tnorm_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.tnorm_add_le

/-- info: 'SparseHamiltonian.MixedOutputODE.tnorm_smul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.tnorm_smul_le

/-- info: 'SparseHamiltonian.MixedOutputODE.tnorm_pure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.tnorm_pure_le

/-- info: 'SparseHamiltonian.MixedOutputODE.eq_zero_of_tnorm_le_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.eq_zero_of_tnorm_le_zero

/-- info: 'SparseHamiltonian.MixedOutputODE.hermitianTraceDistance_triangle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.hermitianTraceDistance_triangle

/-- info: 'SparseHamiltonian.MixedOutputODE.eq_of_hermitianTraceDistance_le_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.eq_of_hermitianTraceDistance_le_zero

/-- info: 'SparseHamiltonian.MixedOutputODE.hermitianTraceDistance_pure_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.hermitianTraceDistance_pure_le

/-- info: 'SparseHamiltonian.MixedOutputODE.pure_sub_isSymmetric' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.pure_sub_isSymmetric

/-- info: 'SparseHamiltonian.MixedOutputODE.hermitianTraceDistance_pure_phase_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.hermitianTraceDistance_pure_phase_le

/-! ### Partial trace over the work register (`PartialTrace`) -/

/-- info: 'SparseHamiltonian.MixedOutputODE.slot_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.slot_adjoint_apply

/-- info: 'SparseHamiltonian.MixedOutputODE.slot_adjoint_comp_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.slot_adjoint_comp_slot

/-- info: 'SparseHamiltonian.MixedOutputODE.sum_slot_comp_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.sum_slot_comp_adjoint

/-- info: 'SparseHamiltonian.MixedOutputODE.tensorLeft_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.tensorLeft_slot

/-- info: 'SparseHamiltonian.MixedOutputODE.adjoint_tensorLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.adjoint_tensorLeft

/-- info: 'SparseHamiltonian.MixedOutputODE.slot_adjoint_tensorLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.slot_adjoint_tensorLeft

/-- info: 'SparseHamiltonian.MixedOutputODE.tensorLeft_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.tensorLeft_isometry

/-- info: 'SparseHamiltonian.MixedOutputODE.pureOperator_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.pureOperator_adjoint_apply

/-- info: 'SparseHamiltonian.MixedOutputODE.ptrace_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.ptrace_pure

/-- info: 'SparseHamiltonian.MixedOutputODE.ptrace_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.ptrace_smul

/-- info: 'SparseHamiltonian.MixedOutputODE.tr_ptrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.tr_ptrace

/-- info: 'SparseHamiltonian.MixedOutputODE.ptrace_isPositive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.ptrace_isPositive

/-- info: 'SparseHamiltonian.MixedOutputODE.ptrace_isDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.ptrace_isDensity

/-! ### Selection from a mixed output (`Selection`) -/

/-- info: 'SparseHamiltonian.MixedOutputODE.isSymmetric_real_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.isSymmetric_real_smul

/-- info: 'SparseHamiltonian.MixedOutputODE.pure_unitDirection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.pure_unitDirection

/-- info: 'SparseHamiltonian.MixedOutputODE.tr_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.tr_pure

/-! ### The mixed-output solver interface and constants (`Interface`) -/

/-- info: 'SparseHamiltonian.MixedOutputODE.slot_unit_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.slot_unit_isometry

/-- info: 'SparseHamiltonian.MixedOutputODE.slot_comp_adjoint_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.slot_comp_adjoint_unit

/-- info: 'SparseHamiltonian.MixedOutputODE.norm_slot_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.norm_slot_unit

/-- info: 'SparseHamiltonian.MixedOutputODE.unitDirection_slot_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.unitDirection_slot_unit

/-- info: 'SparseHamiltonian.MixedOutputODE.ptrace_pure_slot_unit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.ptrace_pure_slot_unit

/-- info: 'SparseHamiltonian.MixedOutputODE.mixedDelta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.mixedDelta_pos

/-- info: 'SparseHamiltonian.MixedOutputODE.mixedDelta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.mixedDelta_le

/-- info: 'SparseHamiltonian.MixedOutputODE.theta_sq_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.theta_sq_ge

/-- info: 'SparseHamiltonian.MixedOutputODE.two_mixedDelta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.two_mixedDelta_le

/-- info: 'SparseHamiltonian.MixedOutputODE.mixed_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.mixed_select

/-- info: 'SparseHamiltonian.MixedOutputODE.mixed_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.mixed_gap

/-- info: 'SparseHamiltonian.MixedOutputODE.mixed_amplitude' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.mixed_amplitude

/-- info: 'SparseHamiltonian.MixedOutputODE.mixed_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.mixed_error

/-! ### The protocol (`Protocol`) -/

/-! ### Theorem `ode:thm:general` with a mixed-output solver (`Theorem`) -/

/-- info: 'SparseHamiltonian.MixedOutputODE.exists_protocol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.exists_protocol

/-! ### The closed-form query bound (`Complexity`) -/

/-- info: 'SparseHamiltonian.MixedOutputODE.log_mixedDelta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.log_mixedDelta_le

/-- info: 'SparseHamiltonian.MixedOutputODE.matrixBudget_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.matrixBudget_le

/-- info: 'SparseHamiltonian.MixedOutputODE.sourceBudget_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.MixedOutputODE.sourceBudget_le
