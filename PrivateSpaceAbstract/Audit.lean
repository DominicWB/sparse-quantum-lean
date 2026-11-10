import PrivateSpaceAbstract.Pad
import PrivateSpaceAbstract.Flag

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library. Each report lists at
most `propext`, `Classical.choice` and `Quot.sound`. -/

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.isometry_adjoint_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.isometry_adjoint_apply

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.padUnitary_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.padUnitary_eq

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.padUnitary_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.padUnitary_apply

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.padResolvent_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.padResolvent_apply

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.adjoint_padUnitary_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.adjoint_padUnitary_apply

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.adjoint_padResolvent_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.adjoint_padResolvent_apply

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.padUnitary_comp_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.padUnitary_comp_isometry

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.padUnitary_apply_of_orth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.padUnitary_apply_of_orth

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.padUnitary_comp_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.padUnitary_comp_apply

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.padUnitary_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.padUnitary_adjoint

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.padUnitary_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.padUnitary_unitary

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.padResolvent_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.padResolvent_right

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.padResolvent_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.padResolvent_left

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.norm_padResolvent_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.norm_padResolvent_le

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.pad_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.pad_boundary

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.pad_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.pad_moment

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.pad_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.pad_isometry

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.abstract_simulation_private' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.abstract_simulation_private

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.finrank_anc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.finrank_anc

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.exists_isometry_of_finrank_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.exists_isometry_of_finrank_le

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.exists_isometry_anc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.exists_isometry_anc

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.abstract_simulation_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.abstract_simulation_finite

/-! ### The padded call and the zero system (`Flag`) -/

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.flagCall_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.flagCall_apply

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.rangeRefl_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.rangeRefl_apply

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.adjoint_rangeRefl_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.adjoint_rangeRefl_apply

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.adjoint_flagCall_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.adjoint_flagCall_apply

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.flagCall_comp_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.flagCall_comp_isometry

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.flagCall_apply_of_orth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.flagCall_apply_of_orth

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.flagCall_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.flagCall_adjoint

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.rangeRefl_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.rangeRefl_adjoint

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.rangeRefl_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.rangeRefl_mul_self

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.rangeRefl_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.rangeRefl_unitary

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.padUnitary_eq_flagCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.padUnitary_eq_flagCall

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.flagCall_comm_rangeRefl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.flagCall_comm_rangeRefl

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.flagCall_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.flagCall_unitary

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.padUnitary_adjoint_eq_flagCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.padUnitary_adjoint_eq_flagCall

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.oracleOp_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.oracleOp_comp

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.oracleOp_padUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.oracleOp_padUnitary

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.oracleOp_padUnitary_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.oracleOp_padUnitary_adjoint

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.eq_of_subsingleton' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.eq_of_subsingleton

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.run_subsingleton_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.run_subsingleton_exact

/-- info: 'SparseHamiltonian.PrivateSpaceAbstract.abstract_simulation_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.PrivateSpaceAbstract.abstract_simulation_zero
