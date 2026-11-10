import NativeSignedFactor.Local
import NativeSignedFactor.Gate
import NativeSignedFactor.Factor
import NativeSignedFactor.Physical
import NativeSignedFactor.Simulation

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem of the library
(91 theorems), beginning with the native simulation theorems and the factor identities, then in
module order. Every report lists exactly `propext`, `Classical.choice` and `Quot.sound`. -/

/-! ### Final theorems: the native simulation and the factor identities -/

/-- info: 'NativeSignedFactor.native_signed_simulation_eta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.native_signed_simulation_eta

/-- info: 'NativeSignedFactor.native_signed_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.native_signed_simulation

/-- info: 'NativeSignedFactor.simulates_of_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.simulates_of_factor

/-- info: 'NativeSignedFactor.phys_ham' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.phys_ham

/-- info: 'NativeSignedFactor.phys_Cop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.phys_Cop

/-- info: 'NativeSignedFactor.phys_Dop_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.phys_Dop_eq

/-- info: 'NativeSignedFactor.phys_Dop_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.phys_Dop_le

/-- info: 'NativeSignedFactor.phys_Dop_le_eta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.phys_Dop_le_eta

/-- info: 'NativeSignedFactor.row_abs_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.row_abs_sum_le

/-- info: 'NativeSignedFactor.physProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.physProgram_count

/-- info: 'NativeSignedFactor.physProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.physProgram_cost

/-- info: 'NativeSignedFactor.factor_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.factor_eq

/-- info: 'NativeSignedFactor.facQ_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.facQ_sign

/-- info: 'NativeSignedFactor.facQ_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.facQ_gram

/-- info: 'NativeSignedFactor.localGate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.localGate_unitary

/-! ### The local factor (`Local`) -/

/-- info: 'NativeSignedFactor.norm_clip_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.norm_clip_le

/-- info: 'NativeSignedFactor.clip_of_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.clip_of_norm_le

/-- info: 'NativeSignedFactor.norm_clip_le_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.norm_clip_le_norm

/-- info: 'NativeSignedFactor.norm_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.norm_phase

/-- info: 'NativeSignedFactor.norm_mul_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.norm_mul_phase

/-- info: 'NativeSignedFactor.norm_mul_conj_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.norm_mul_conj_phase

/-- info: 'NativeSignedFactor.phase_mul_conj_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.phase_mul_conj_phase

/-- info: 'NativeSignedFactor.conj_phase_mul_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.conj_phase_mul_phase

/-- info: 'NativeSignedFactor.conj_r2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.conj_r2

/-- info: 'NativeSignedFactor.r2_mul_r2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.r2_mul_r2

/-- info: 'NativeSignedFactor.amp_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.amp_sq

/-- info: 'NativeSignedFactor.amp_sq_add_fam_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.amp_sq_add_fam_sq

/-- info: 'NativeSignedFactor.orient_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.orient_unitary

/-- info: 'NativeSignedFactor.flagRot_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.flagRot_unitary

/-- info: 'NativeSignedFactor.localOp_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.localOp_unitary

/-- info: 'NativeSignedFactor.localOp_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.localOp_apply

/-- info: 'NativeSignedFactor.facQ_false' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.facQ_false

/-- info: 'NativeSignedFactor.facQ_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.facQ_true

/-- info: 'NativeSignedFactor.facQ_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.facQ_adjoint

/-- info: 'NativeSignedFactor.orient_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.orient_sum

/-! ### The factor unitary and its known structure (`Gate`) -/

/-- info: 'NativeSignedFactor.addrLayout_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.addrLayout_apply

/-- info: 'NativeSignedFactor.addrLayout_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.addrLayout_symm_apply

/-- info: 'NativeSignedFactor.norm_entry_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.norm_entry_le

/-- info: 'NativeSignedFactor.entry_table' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.entry_table

/-- info: 'NativeSignedFactor.norm_entry_table_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.norm_entry_table_le

/-- info: 'NativeSignedFactor.gate_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.gate_unitary

/-- info: 'NativeSignedFactor.gate_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.gate_apply

/-- info: 'NativeSignedFactor.factorProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.factorProgram_count

/-- info: 'NativeSignedFactor.factorProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.factorProgram_cost

/-- info: 'NativeSignedFactor.factorProgram_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.factorProgram_unitary

/-- info: 'NativeSignedFactor.gate_value_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.gate_value_clean

/-- info: 'NativeSignedFactor.value_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.value_clean

/-- info: 'NativeSignedFactor.proj_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.proj_apply

/-- info: 'NativeSignedFactor.sign_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.sign_apply

/-- info: 'NativeSignedFactor.input_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.input_isometry

/-- info: 'NativeSignedFactor.proj_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.proj_adjoint

/-- info: 'NativeSignedFactor.proj_idem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.proj_idem

/-- info: 'NativeSignedFactor.sign_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.sign_adjoint

/-- info: 'NativeSignedFactor.sign_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.sign_sq

/-- info: 'NativeSignedFactor.sign_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.sign_proj

/-- info: 'NativeSignedFactor.proj_value_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.proj_value_clean

/-! ### The factor identities (`Factor`) -/

/-- info: 'NativeSignedFactor.adjoint_comp_cancel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.adjoint_comp_cancel

/-- info: 'NativeSignedFactor.transport_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.transport_factor

/-- info: 'NativeSignedFactor.transport_Cop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.transport_Cop

/-- info: 'NativeSignedFactor.transport_Dop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.transport_Dop

/-- info: 'NativeSignedFactor.adjoint_comp_self_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.adjoint_comp_self_le

/-- info: 'NativeSignedFactor.Dop_le_of_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.Dop_le_of_bound

/-- info: 'NativeSignedFactor.lift_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.lift_adjoint

/-- info: 'NativeSignedFactor.sign_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.sign_clean

/-- info: 'NativeSignedFactor.facOp_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.facOp_sign

/-- info: 'NativeSignedFactor.norm_facQ_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.norm_facQ_sq

/-- info: 'NativeSignedFactor.norm_facOp_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.norm_facOp_sq

/-- info: 'NativeSignedFactor.matrixOperator_mul_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.matrixOperator_mul_const

/-- info: 'NativeSignedFactor.clean_sign_clean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.clean_sign_clean

/-- info: 'NativeSignedFactor.Cop_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.Cop_eq

/-- info: 'NativeSignedFactor.sum_selected_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.sum_selected_le

/-- info: 'NativeSignedFactor.entry_row_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.entry_row_sq_le

/-- info: 'NativeSignedFactor.entry_col_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.entry_col_sq_le

/-- info: 'NativeSignedFactor.norm_factor_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.norm_factor_sq_le

/-- info: 'NativeSignedFactor.Dop_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.Dop_le

/-- info: 'NativeSignedFactor.facOp_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.facOp_gram

/-- info: 'NativeSignedFactor.lift_scalar_stack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.lift_scalar_stack

/-- info: 'NativeSignedFactor.Dop_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.Dop_eq

/-! ### The physical factor (`Physical`) -/

/-- info: 'NativeSignedFactor.physOracle_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.physOracle_unitary

/-- info: 'NativeSignedFactor.embed_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.embed_isometry

/-- info: 'NativeSignedFactor.physProgram_intertwines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.physProgram_intertwines

/-- info: 'NativeSignedFactor.physProgram_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.physProgram_unitary

/-- info: 'NativeSignedFactor.phys_norm_factor_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.phys_norm_factor_sq_le

/-- info: 'NativeSignedFactor.phys_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.phys_bound

/-! ### The simulation (`Simulation`) -/

/-- info: 'NativeSignedFactor.diagProgram_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.diagProgram_count

/-- info: 'NativeSignedFactor.diagProgram_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.diagProgram_cost

/-- info: 'NativeSignedFactor.diagProgram_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.diagProgram_eval

/-- info: 'NativeSignedFactor.subst_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.subst_count

/-- info: 'NativeSignedFactor.subst_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.subst_cost

/-- info: 'NativeSignedFactor.subst_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.subst_eval

/-- info: 'NativeSignedFactor.Simulates.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NativeSignedFactor.Simulates.mono
