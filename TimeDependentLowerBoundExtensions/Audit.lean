import TimeDependentLowerBoundExtensions.Statements

set_option autoImplicit false

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem of the library of the
lower bound of Theorem `hsl:thm:main` in the further time-dependent settings (time-indexed block
encodings, coherent selection, call forms of the released oracle families, gate-level circuits
with exactly or approximately realised private operations, piecewise Lipschitz paths, measured
algorithms over the released oracle families; 161 theorems) and every `Prop`-valued field of the
structure `Tolerant.LipschitzPath` (4 fields), 165 audits in module order. Definitions,
including the `Prop`-valued criteria `BECriterion`, `BEIntegrableCriterion`, `SelectCriterion`,
`WindowsCriterion`, `WindowsIntegrableCriterion`, `Tolerant.LipschitzGuarantee`, the hypotheses
`NativeRealization` and `Tolerant.ApproxRealization` and the certificates
`Measured.IsMaskedLift` and `Measured.NativeCompiles`, are covered through the theorems that use
them. Every report lists `propext`, `Classical.choice` and `Quot.sound`, except
`Core.hardCost_eq_two_mul`, which depends on no axiom.
-/

/-! ### Assembly for certified families (`Core.Assembly`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Core.nonempty_access_of_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Core.nonempty_access_of_normal_form

/-- info: 'TimeDependentLowerBoundExtensions.Core.main_max_access' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Core.main_max_access

/-- info: 'TimeDependentLowerBoundExtensions.Core.main_max_uniform_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Core.main_max_uniform_weight

/-! ### Masked calls, call forms and spectator wrappers (`Core.Masked`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Core.maskedEncoding_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Core.maskedEncoding_isometry

/-- info: 'TimeDependentLowerBoundExtensions.Core.implementsOn_masked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Core.implementsOn_masked

/-- info: 'TimeDependentLowerBoundExtensions.Core.callFamily_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Core.callFamily_conj

/-- info: 'TimeDependentLowerBoundExtensions.Core.admissible_callFamily_of_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Core.admissible_callFamily_of_normal_form

/-- info: 'TimeDependentLowerBoundExtensions.Core.nonempty_access_of_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Core.nonempty_access_of_wrap

/-! ### Boolean cost of labelled native calls (`Core.Cost`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Core.hardCost_eq_two_mul' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Core.hardCost_eq_two_mul

/-- info: 'TimeDependentLowerBoundExtensions.Core.cost_hardCost_fst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Core.cost_hardCost_fst

/-- info: 'TimeDependentLowerBoundExtensions.Core.cost_valueWeight_fst_le_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Core.cost_valueWeight_fst_le_count

/-- info: 'TimeDependentLowerBoundExtensions.Core.max_calls_of_hardCost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Core.max_calls_of_hardCost

/-! ### Hermitian block encodings of the hard instances (`BlockEncoding.Hard`) -/

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.conj_star_of_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.conj_star_of_star

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.conj_compress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.conj_compress

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.beOp_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.beOp_selfAdjoint

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.beOp_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.beOp_unitary

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.beJ_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.beJ_isometry

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.beAlpha_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.beAlpha_pos

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.beJ_compress' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.beJ_compress

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.blockSample_beOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.blockSample_beOp

/-! ### Boolean certificates of the block-encoding oracles (`BlockEncoding.Access`) -/

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.isWrap_beWrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.isWrap_beWrap

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.aligned_eq_beWrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.aligned_eq_beWrap

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.implementsOn_beOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.implementsOn_beOp

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.beEncoding_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.beEncoding_isometry

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.primitive_beConst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.primitive_beConst

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.nonempty_primitiveAccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.nonempty_primitiveAccess

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.nonempty_alignedAccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.nonempty_alignedAccess

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.alignedOracle_beConst_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.alignedOracle_beConst_unitary

/-! ### Bounds in block-encoding calls (`BlockEncoding.Bound`) -/

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.beCriterion_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.beCriterion_endpoint

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.main_max_block_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.main_max_block_endpoint

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.main_max_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.main_max_block

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.main_max_block_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.main_max_block_primitive

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.main_max_calls_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.main_max_calls_block

/-! ### Non-vacuity of the block-encoding bounds (`BlockEncoding.NonVacuity`) -/

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.beConst_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.beConst_hyps

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.exists_beProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.exists_beProgram

/-! ### Block-encoding calls under the integrable-path criterion (`BlockEncoding.Integrable`) -/

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.beIntegrableCriterion_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.beIntegrableCriterion_endpoint

/-- info: 'TimeDependentLowerBoundExtensions.BlockEncoding.main_max_block_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.BlockEncoding.main_max_block_integrable

/-! ### The coherent-selection family on constant data (`Coherent.Access`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.isWrap_selectWrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.isWrap_selectWrap

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.alignedOracle_eq_selectWrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.alignedOracle_eq_selectWrap

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.select_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.select_normal_form

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.nonempty_selectAccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.nonempty_selectAccess

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.admissible_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.admissible_select

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.admissible_callFamily_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.admissible_callFamily_select

/-! ### Bounds with coherent selection (`Coherent.Bound`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.branchInj_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.branchInj_isometry

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.diagonal_comp_branchInj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.diagonal_comp_branchInj

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.evolution_exp_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.evolution_exp_const

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.endpoint_of_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.endpoint_of_comp

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.select_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.select_endpoint

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.windows_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.windows_endpoint

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.main_max_of_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.main_max_of_value

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.main_max_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.main_max_select

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.main_max_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.main_max_windows

/-! ### Adaptive algorithms over the selection family (`Coherent.Tree`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.main_max_tree_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.main_max_tree_select

/-! ### Non-vacuity of the coherent-selection bounds (`Coherent.NonVacuity`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.exists_selectProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.exists_selectProgram

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.exists_windowsProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.exists_windowsProgram

/-! ### Call forms of the coherent-selection family (`Coherent.Calls`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.branch_encoding_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.branch_encoding_isometry

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.main_max_calls_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.main_max_calls_select

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.main_max_calls_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.main_max_calls_windows

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.main_max_tree_calls_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.main_max_tree_calls_select

/-! ### Coherent windows under the integrable-path criterion (`Coherent.Integrable`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.windowsIntegrable_endpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.windowsIntegrable_endpoint

/-- info: 'TimeDependentLowerBoundExtensions.Coherent.main_max_windows_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Coherent.main_max_windows_integrable

/-! ### Call forms of the released time-dependent families (`Calls.Bound`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Calls.admissible_callFamily_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Calls.admissible_callFamily_uniform

/-- info: 'TimeDependentLowerBoundExtensions.Calls.admissible_callFamily_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Calls.admissible_callFamily_mesh

/-- info: 'TimeDependentLowerBoundExtensions.Calls.main_max_calls_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Calls.main_max_calls_uniform

/-- info: 'TimeDependentLowerBoundExtensions.Calls.main_max_calls_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Calls.main_max_calls_mesh

/-- info: 'TimeDependentLowerBoundExtensions.Calls.main_max_calls_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Calls.main_max_calls_integrable

/-- info: 'TimeDependentLowerBoundExtensions.Calls.main_max_tree_calls_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Calls.main_max_tree_calls_uniform

/-- info: 'TimeDependentLowerBoundExtensions.Calls.main_max_tree_calls_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Calls.main_max_tree_calls_mesh

/-! ### Gate-level circuits as oracle programs (`Gate.Program`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Gate.slotOracle_const_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Gate.slotOracle_const_eq

/-- info: 'TimeDependentLowerBoundExtensions.Gate.exists_program' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Gate.exists_program

/-! ### Bounds for gate-level circuits (`Gate.Bound`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Gate.nonempty_privAccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Gate.nonempty_privAccess

/-- info: 'TimeDependentLowerBoundExtensions.Gate.main_max_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Gate.main_max_gate

/-- info: 'TimeDependentLowerBoundExtensions.Gate.main_max_gate_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Gate.main_max_gate_uniform

/-! ### Satisfiability of the native-realisation hypothesis (`Gate.NonVacuity`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Gate.nativeRealization_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Gate.nativeRealization_call

/-! ### Approximate implementations: inverses and masked calls (`Tolerant.Approx`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.approx_adjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.approx_adjoint

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.masked_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.masked_approx

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.approx_comp_encoding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.approx_comp_encoding

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.controlOne_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.controlOne_isometry

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.masked_comp_controlOne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.masked_comp_controlOne

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.comp_controlOne_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.comp_controlOne_isometry

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.approx_of_controlled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.approx_of_controlled

/-! ### Private operations realised by sparse queries within an error `ξ` (`Tolerant.Realization`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.approxRealization_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.approxRealization_zero_iff

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.approxRealization_of_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.approxRealization_of_native

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.ApproxRealization.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.ApproxRealization.mono

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.approxRealization_of_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.approxRealization_of_near

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.approxRealization_call' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.approxRealization_call

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.approxRealization_of_controlled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.approxRealization_of_controlled

/-! ### Gate-level circuits with approximately realised private operations (`Tolerant.Program`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.realFamily_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.realFamily_unitary

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.realEncoding_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.realEncoding_isometry

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.nonempty_realAccess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.nonempty_realAccess

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.norm_sub_conj_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.norm_sub_conj_le

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.exists_approxProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.exists_approxProgram

/-! ### Bounds for gate-level circuits with private operations realised within `ξ` (`Tolerant.Bound`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.main_max_gate_tolerant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.main_max_gate_tolerant

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.main_max_gate_uniform_tolerant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.main_max_gate_uniform_tolerant

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.main_max_gate_of_tolerant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.main_max_gate_of_tolerant

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.main_max_gate_uniform_of_tolerant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.main_max_gate_uniform_of_tolerant

/-! ### The class of piecewise Lipschitz paths with breakpoints (`Tolerant.LipschitzClass`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.LipschitzPath.hermitian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.LipschitzPath.hermitian

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.LipschitzPath.lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.LipschitzPath.lipschitz

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.LipschitzPath.sample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.LipschitzPath.sample

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.LipschitzPath.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.LipschitzPath.certificate

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.LipschitzPath.meshPath' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.LipschitzPath.meshPath

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.lipschitzGuarantee_of_meshGuarantee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.lipschitzGuarantee_of_meshGuarantee

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.lipschitzPath_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.lipschitzPath_const

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.LipschitzGuarantee.criterion_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.LipschitzGuarantee.criterion_const

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.simulation_lipschitz_guarantee' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.simulation_lipschitz_guarantee

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.meshHyp_simulation_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.meshHyp_simulation_lipschitz

/-! ### Bounds for the class of piecewise Lipschitz paths (`Tolerant.LipschitzBound`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.lipschitz_class_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.lipschitz_class_max

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.lipschitz_class_max_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.lipschitz_class_max_calls

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.mesh_class_max_of_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.mesh_class_max_of_lipschitz

/-- info: 'TimeDependentLowerBoundExtensions.Tolerant.lipschitz_class_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Tolerant.lipschitz_class_nonvacuous

/-! ### Compiling the calls of a measured algorithm (`Measured.Compile`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Measured.eval_callProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.eval_callProgram

/-- info: 'TimeDependentLowerBoundExtensions.Measured.cost_callProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.cost_callProgram

/-- info: 'TimeDependentLowerBoundExtensions.Measured.successDensity_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.successDensity_compile

/-- info: 'TimeDependentLowerBoundExtensions.Measured.successMass_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.successMass_compile

/-- info: 'TimeDependentLowerBoundExtensions.Measured.conditionalDensity_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.conditionalDensity_compile

/-- info: 'TimeDependentLowerBoundExtensions.Measured.worstCost_compile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.worstCost_compile

/-- info: 'TimeDependentLowerBoundExtensions.Measured.worstCost_const_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.worstCost_const_le

/-- info: 'TimeDependentLowerBoundExtensions.Measured.worstCost_compile_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.worstCost_compile_le

/-! ### Masked lifts: fixed layouts of masked spectator registers (`Measured.MaskedLift`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Measured.masked_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.masked_conj

/-- info: 'TimeDependentLowerBoundExtensions.Measured.masked_masked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.masked_masked

/-- info: 'TimeDependentLowerBoundExtensions.Measured.masked_diagonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.masked_diagonal

/-- info: 'TimeDependentLowerBoundExtensions.Measured.isMaskedLift_masked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.isMaskedLift_masked

/-- info: 'TimeDependentLowerBoundExtensions.Measured.isMaskedLift_fiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.isMaskedLift_fiber

/-- info: 'TimeDependentLowerBoundExtensions.Measured.isMaskedLift_of_isWrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.isMaskedLift_of_isWrap

/-- info: 'TimeDependentLowerBoundExtensions.Measured.isMaskedLift_normal_form' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.isMaskedLift_normal_form

/-- info: 'TimeDependentLowerBoundExtensions.Measured.IsMaskedLift.conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.IsMaskedLift.conj

/-- info: 'TimeDependentLowerBoundExtensions.Measured.IsMaskedLift.masked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.IsMaskedLift.masked

/-- info: 'TimeDependentLowerBoundExtensions.Measured.IsMaskedLift.wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.IsMaskedLift.wrap

/-- info: 'TimeDependentLowerBoundExtensions.Measured.IsMaskedLift.map_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.IsMaskedLift.map_one

/-- info: 'TimeDependentLowerBoundExtensions.Measured.IsMaskedLift.map_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.IsMaskedLift.map_mul

/-- info: 'TimeDependentLowerBoundExtensions.Measured.IsMaskedLift.map_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.IsMaskedLift.map_star

/-- info: 'TimeDependentLowerBoundExtensions.Measured.IsMaskedLift.map_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.IsMaskedLift.map_unitary

/-- info: 'TimeDependentLowerBoundExtensions.Measured.IsMaskedLift.admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.IsMaskedLift.admissible

/-- info: 'TimeDependentLowerBoundExtensions.Measured.eval_liftProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.eval_liftProgram

/-- info: 'TimeDependentLowerBoundExtensions.Measured.cost_liftProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.cost_liftProgram

/-! ### Measured algorithms over natively compiled families (`Measured.Assembly`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Measured.nativeCompiles_of_admissible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.nativeCompiles_of_admissible

/-- info: 'TimeDependentLowerBoundExtensions.Measured.NativeCompiles.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.NativeCompiles.map

/-- info: 'TimeDependentLowerBoundExtensions.Measured.NativeCompiles.callFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.NativeCompiles.callFamily

/-- info: 'TimeDependentLowerBoundExtensions.Measured.exists_compiled_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.exists_compiled_measured

/-- info: 'TimeDependentLowerBoundExtensions.Measured.main_max_measured_compiled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.main_max_measured_compiled

/-! ### Block-encoding calls as fixed products of native calls (`Measured.BlockCompile`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Measured.isMaskedLift_sectorLift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.isMaskedLift_sectorLift

/-- info: 'TimeDependentLowerBoundExtensions.Measured.admissible_beSector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.admissible_beSector

/-- info: 'TimeDependentLowerBoundExtensions.Measured.beSwap_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.beSwap_unitary

/-- info: 'TimeDependentLowerBoundExtensions.Measured.eval_beProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.eval_beProgram

/-- info: 'TimeDependentLowerBoundExtensions.Measured.cost_beProgram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.cost_beProgram

/-- info: 'TimeDependentLowerBoundExtensions.Measured.nativeCompiles_beOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.nativeCompiles_beOp

/-- info: 'TimeDependentLowerBoundExtensions.Measured.nativeCompiles_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.nativeCompiles_primitive

/-- info: 'TimeDependentLowerBoundExtensions.Measured.nativeCompiles_aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.nativeCompiles_aligned

/-- info: 'TimeDependentLowerBoundExtensions.Measured.nativeCompiles_calls_aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.nativeCompiles_calls_aligned

/-! ### Measured algorithms over time-indexed block encodings (`Measured.Block`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Measured.main_max_measured_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.main_max_measured_block

/-- info: 'TimeDependentLowerBoundExtensions.Measured.main_max_measured_block_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.main_max_measured_block_primitive

/-- info: 'TimeDependentLowerBoundExtensions.Measured.main_max_measured_calls_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.main_max_measured_calls_block

/-! ### Measured algorithms over the released uniform-mesh oracles (`Measured.Uniform`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Measured.main_max_measured_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.main_max_measured_uniform

/-- info: 'TimeDependentLowerBoundExtensions.Measured.main_max_measured_calls_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.main_max_measured_calls_uniform

/-! ### Measured algorithms over the released general-mesh oracles (`Measured.Mesh`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Measured.main_max_measured_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.main_max_measured_mesh

/-- info: 'TimeDependentLowerBoundExtensions.Measured.main_max_measured_calls_mesh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.main_max_measured_calls_mesh

/-! ### Measured algorithms with coherent selection (`Measured.Select`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Measured.main_max_measured_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.main_max_measured_select

/-- info: 'TimeDependentLowerBoundExtensions.Measured.main_max_measured_calls_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.main_max_measured_calls_select

/-! ### Non-vacuity of the measured bounds (`Measured.NonVacuity`) -/

/-- info: 'TimeDependentLowerBoundExtensions.Measured.adjoint_one_comp_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.adjoint_one_comp_one

/-- info: 'TimeDependentLowerBoundExtensions.Measured.programRun_meets' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.programRun_meets

/-- info: 'TimeDependentLowerBoundExtensions.Measured.released_uniform_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.released_uniform_measured

/-- info: 'TimeDependentLowerBoundExtensions.Measured.released_mesh_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.released_mesh_measured

/-- info: 'TimeDependentLowerBoundExtensions.Measured.released_integrable_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.released_integrable_measured

/-- info: 'TimeDependentLowerBoundExtensions.Measured.released_select_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.released_select_measured

/-- info: 'TimeDependentLowerBoundExtensions.Measured.released_block_measured' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TimeDependentLowerBoundExtensions.Measured.released_block_measured
