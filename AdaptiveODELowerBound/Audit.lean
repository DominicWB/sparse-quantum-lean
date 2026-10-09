import AdaptiveODELowerBound.Statements

set_option autoImplicit false

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the
declaration depends on any other axiom. The audits cover every theorem of the dissipative-ODE
lower bounds for adaptive solvers (125 theorems) and every `Prop`-valued field of the structures
`Model.TreeSolver` and `Model.TreeWitnesses` (6 fields), in module order. Every report lists
`propext`, `Classical.choice` and `Quot.sound`. -/

/-! ### Inverse and controlled calls (`AdaptiveODELowerBound.Access`) -/

/-! #### `AdaptiveODELowerBound.Access.Calls` -/

/-- info: 'AdaptiveODELowerBound.Access.formOp_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.formOp_unitary

/-- info: 'AdaptiveODELowerBound.Access.callFamily_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.callFamily_unitary

/-- info: 'AdaptiveODELowerBound.Access.callFamily_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.callFamily_const

/-! #### `AdaptiveODELowerBound.Access.Control` -/

/-- info: 'AdaptiveODELowerBound.Access.phase_ctrlFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.phase_ctrlFamily

/-- info: 'AdaptiveODELowerBound.Access.activeEmbed_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.activeEmbed_apply

/-- info: 'AdaptiveODELowerBound.Access.activeEmbed_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.activeEmbed_isometry

/-- info: 'AdaptiveODELowerBound.Access.ctrlOp_comp_activeEmbed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.ctrlOp_comp_activeEmbed

/-- info: 'AdaptiveODELowerBound.Access.flipD_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.flipD_apply

/-- info: 'AdaptiveODELowerBound.Access.flipD_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.flipD_mul_self

/-- info: 'AdaptiveODELowerBound.Access.star_flipD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.star_flipD

/-- info: 'AdaptiveODELowerBound.Access.flipD_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.flipD_unitary

/-- info: 'AdaptiveODELowerBound.Access.alignCtrl_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.alignCtrl_unitary

/-- info: 'AdaptiveODELowerBound.Access.callEncoding_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.callEncoding_isometry

/-- info: 'AdaptiveODELowerBound.Access.implementsOn_active' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.implementsOn_active

/-- info: 'AdaptiveODELowerBound.Access.implementsOn_plainForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.implementsOn_plainForm

/-- info: 'AdaptiveODELowerBound.Access.implementsOn_controlledForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.implementsOn_controlledForm

/-- info: 'AdaptiveODELowerBound.Access.star_ctrlOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.star_ctrlOp

/-- info: 'AdaptiveODELowerBound.Access.implementsOn_callFamily' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.implementsOn_callFamily

/-! #### `AdaptiveODELowerBound.Access.HardCalls` -/

/-- info: 'AdaptiveODELowerBound.Access.implementsOn_calls_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.implementsOn_calls_joint

/-- info: 'AdaptiveODELowerBound.Access.calls_locator_const_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.calls_locator_const_joint

/-- info: 'AdaptiveODELowerBound.Access.implementsOn_calls_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.implementsOn_calls_hom

/-- info: 'AdaptiveODELowerBound.Access.calls_locator_const_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.calls_locator_const_hom

/-! #### `AdaptiveODELowerBound.Access.Admissible` -/

/-- info: 'AdaptiveODELowerBound.Access.admissible_callFamily_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Access.admissible_callFamily_spec

/-! ### The adaptive solver model and the combined arithmetic (`Model/Solver`, `Bound`) -/

/-! #### `AdaptiveODELowerBound.Model.Solver` -/

/-- info: 'AdaptiveODELowerBound.Model.worstCost_mono_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.worstCost_mono_tree

/-- info: 'AdaptiveODELowerBound.Model.worstCost_mul_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.worstCost_mul_tree

/-- info: 'AdaptiveODELowerBound.Model.TreeSolver.readout_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.TreeSolver.readout_isometry

/-- info: 'AdaptiveODELowerBound.Model.TreeSolver.success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.TreeSolver.success

/-- info: 'AdaptiveODELowerBound.Model.TreeSolver.accurate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.TreeSolver.accurate

/-- info: 'AdaptiveODELowerBound.Model.TreeWitnesses.inClass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.TreeWitnesses.inClass

/-- info: 'AdaptiveODELowerBound.Model.TreeWitnesses.time_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.TreeWitnesses.time_eq

/-- info: 'AdaptiveODELowerBound.Model.TreeWitnesses.forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.TreeWitnesses.forces

/-- info: 'AdaptiveODELowerBound.Model.TreeWitnesses.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.TreeWitnesses.mono

/-- info: 'AdaptiveODELowerBound.Model.TreeForces.le_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.TreeForces.le_cost

/-- info: 'AdaptiveODELowerBound.Model.treeForces_of_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.treeForces_of_cost

/-- info: 'AdaptiveODELowerBound.Model.forces_or_of_cost₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.forces_or_of_cost₂

/-- info: 'AdaptiveODELowerBound.Model.forces_or_of_cost₃' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.forces_or_of_cost₃

/-- info: 'AdaptiveODELowerBound.Model.worstCost_retryToTree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.worstCost_retryToTree

/-- info: 'AdaptiveODELowerBound.Model.treeForces_retryForces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.treeForces_retryForces

/-- info: 'AdaptiveODELowerBound.Model.treeWitnesses_retryWitnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.treeWitnesses_retryWitnesses

/-- info: 'AdaptiveODELowerBound.Model.treeForces_forces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.treeForces_forces

/-- info: 'AdaptiveODELowerBound.Model.treeWitnesses_witnesses' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.treeWitnesses_witnesses

/-! #### `AdaptiveODELowerBound.Bound` -/

/-- info: 'AdaptiveODELowerBound.combinedBound_le_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.combinedBound_le_max

/-! ### The positive-weight adversary for trees (`AdaptiveODELowerBound.Adversary`) -/

/-! #### `AdaptiveODELowerBound.Adversary.Weighted` -/

/-- info: 'AdaptiveODELowerBound.Adversary.norm_rescale_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Adversary.norm_rescale_le

/-- info: 'AdaptiveODELowerBound.Adversary.rescale_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Adversary.rescale_mul

/-- info: 'AdaptiveODELowerBound.Adversary.rescale_mul_inner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Adversary.rescale_mul_inner

/-- info: 'AdaptiveODELowerBound.Adversary.abs_progressW_program_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Adversary.abs_progressW_program_le

/-- info: 'AdaptiveODELowerBound.Adversary.abs_kernel_progressW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Adversary.abs_kernel_progressW_le

/-! #### `AdaptiveODELowerBound.Adversary.Kernel` -/

/-- info: 'AdaptiveODELowerBound.Adversary.norm_mul_inner_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Adversary.norm_mul_inner_le

/-- info: 'AdaptiveODELowerBound.Adversary.abs_treeKernel_progressW_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Adversary.abs_treeKernel_progressW_le

/-- info: 'AdaptiveODELowerBound.Adversary.abs_treeKernel_progress_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Adversary.abs_treeKernel_progress_le

/-! #### `AdaptiveODELowerBound.Adversary.Purify` -/

/-- info: 'AdaptiveODELowerBound.Adversary.pairOp_toLp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Adversary.pairOp_toLp

/-- info: 'AdaptiveODELowerBound.Adversary.inner_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Adversary.inner_pair

/-- info: 'AdaptiveODELowerBound.Adversary.norm_pairOp_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Adversary.norm_pairOp_le

/-- info: 'AdaptiveODELowerBound.Adversary.tree_purification_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Adversary.tree_purification_step

/-- info: 'AdaptiveODELowerBound.Adversary.exists_tree_purification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Adversary.exists_tree_purification

/-! #### `AdaptiveODELowerBound.Adversary.Decision` -/

/-- info: 'AdaptiveODELowerBound.Adversary.tree_decision_count_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Adversary.tree_decision_count_ge

/-! ### Lemma `odel:lem:outer`, Theorem `odel:thm:joint` and Remark `odel:rem:homogeneous`
(`AdaptiveODELowerBound.Joint`) -/

/-! #### `AdaptiveODELowerBound.Joint.General` -/

/-- info: 'AdaptiveODELowerBound.Joint.outer_count_ge_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Joint.outer_count_ge_tree

/-- info: 'AdaptiveODELowerBound.Joint.outer_general_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Joint.outer_general_tree

/-- info: 'AdaptiveODELowerBound.Joint.joint_general_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Joint.joint_general_tree

/-! #### `AdaptiveODELowerBound.Joint.Families` -/

/-- info: 'AdaptiveODELowerBound.Joint.joint_forces_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Joint.joint_forces_tree

/-- info: 'AdaptiveODELowerBound.Joint.joint_witness_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Joint.joint_witness_tree

/-- info: 'AdaptiveODELowerBound.Joint.hom_forces_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Joint.hom_forces_tree

/-- info: 'AdaptiveODELowerBound.Joint.hom_witness_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Joint.hom_witness_tree

/-! ### Lemma `odel:lem:herald` and Theorem `odel:thm:combined` (`Herald/Transfer`, `Theorem`) -/

/-! #### `AdaptiveODELowerBound.Herald.Transfer` -/

/-- info: 'AdaptiveODELowerBound.Model.TreeSolver.accurate_ham' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.TreeSolver.accurate_ham

/-- info: 'AdaptiveODELowerBound.Herald.treeForces_of_ham' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Herald.treeForces_of_ham

/-- info: 'AdaptiveODELowerBound.Herald.time_forces_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Herald.time_forces_tree

/-- info: 'AdaptiveODELowerBound.Herald.mixed_forces_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Herald.mixed_forces_tree

/-- info: 'AdaptiveODELowerBound.Herald.precision_forces_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Herald.precision_forces_tree

/-- info: 'AdaptiveODELowerBound.Herald.precision_forces_sqrt_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Herald.precision_forces_sqrt_tree

/-! #### `AdaptiveODELowerBound.Theorem` -/

/-- info: 'AdaptiveODELowerBound.herald_max_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.herald_max_tree

/-- info: 'AdaptiveODELowerBound.herald_max_cost_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.herald_max_cost_tree

/-- info: 'AdaptiveODELowerBound.herald_witness_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.herald_witness_tree

/-- info: 'AdaptiveODELowerBound.precision_terms_witness_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.precision_terms_witness_tree

/-- info: 'AdaptiveODELowerBound.combined_max_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.combined_max_tree

/-- info: 'AdaptiveODELowerBound.combined_max_cost_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.combined_max_cost_tree

/-- info: 'AdaptiveODELowerBound.combined_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.combined_tree

/-! ### Theorem `odel:thm:psd` (`AdaptiveODELowerBound.Psd`) -/

/-! #### `AdaptiveODELowerBound.Psd.Transfer` -/

/-- info: 'AdaptiveODELowerBound.Model.TreeSolver.accurate_heat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Model.TreeSolver.accurate_heat

/-- info: 'AdaptiveODELowerBound.Psd.hardAccess_psdSearchData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Psd.hardAccess_psdSearchData

/-- info: 'AdaptiveODELowerBound.Psd.hardAccess_psdScalarData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Psd.hardAccess_psdScalarData

/-- info: 'AdaptiveODELowerBound.Psd.treeForces_of_heat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Psd.treeForces_of_heat

/-! #### `AdaptiveODELowerBound.Psd.Theorem` -/

/-- info: 'AdaptiveODELowerBound.Psd.psdAmp_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Psd.psdAmp_le_one

/-- info: 'AdaptiveODELowerBound.Psd.psd_search_tree_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Psd.psd_search_tree_general

/-- info: 'AdaptiveODELowerBound.Psd.psd_scalar_tree_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Psd.psd_scalar_tree_general

/-- info: 'AdaptiveODELowerBound.Psd.psd_scalar_forces_half_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Psd.psd_scalar_forces_half_tree

/-- info: 'AdaptiveODELowerBound.Psd.psd_search_forces_local_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Psd.psd_search_forces_local_tree

/-- info: 'AdaptiveODELowerBound.Psd.psd_search_forces_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Psd.psd_search_forces_tree

/-- info: 'AdaptiveODELowerBound.Psd.psd_scalar_forces_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Psd.psd_scalar_forces_tree

/-- info: 'AdaptiveODELowerBound.Psd.psd_scalar_forces_sqrt_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Psd.psd_scalar_forces_sqrt_tree

/-- info: 'AdaptiveODELowerBound.Psd.psd_search_witness_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Psd.psd_search_witness_tree

/-- info: 'AdaptiveODELowerBound.Psd.psd_scalar_witness_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Psd.psd_scalar_witness_tree

/-- info: 'AdaptiveODELowerBound.Psd.psd_max_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Psd.psd_max_tree

/-- info: 'AdaptiveODELowerBound.Psd.psd_max_cost_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Psd.psd_max_cost_tree

/-- info: 'AdaptiveODELowerBound.Psd.psd_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Psd.psd_tree

/-! ### The padded families (`AdaptiveODELowerBound.Padding`) -/

/-! #### `AdaptiveODELowerBound.Padding.Readout` -/

/-- info: 'AdaptiveODELowerBound.Padding.densityAccurate_padReadout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.densityAccurate_padReadout

/-- info: 'AdaptiveODELowerBound.Padding.treeAccurate_of_zeroPad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.treeAccurate_of_zeroPad

/-! #### `AdaptiveODELowerBound.Padding.Joint` -/

/-- info: 'AdaptiveODELowerBound.Padding.valueCalls_of_hardCost_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.valueCalls_of_hardCost_tree

/-- info: 'AdaptiveODELowerBound.Padding.joint_forces_dense_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.joint_forces_dense_tree

/-- info: 'AdaptiveODELowerBound.Padding.joint_forces_pad_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.joint_forces_pad_tree

/-- info: 'AdaptiveODELowerBound.Padding.joint_witness_dense_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.joint_witness_dense_tree

/-- info: 'AdaptiveODELowerBound.Padding.joint_witness_pad_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.joint_witness_pad_tree

/-- info: 'AdaptiveODELowerBound.Padding.joint_common_dimension_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.joint_common_dimension_tree

/-- info: 'AdaptiveODELowerBound.Padding.joint_qubit_register_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.joint_qubit_register_tree

/-! #### `AdaptiveODELowerBound.Padding.Herald` -/

/-- info: 'AdaptiveODELowerBound.Padding.hardAccess_timePadData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.hardAccess_timePadData

/-- info: 'AdaptiveODELowerBound.Padding.hardAccess_mixedPadData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.hardAccess_mixedPadData

/-- info: 'AdaptiveODELowerBound.Padding.hardAccess_precisionPadData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.hardAccess_precisionPadData

/-- info: 'AdaptiveODELowerBound.Padding.time_forces_pad_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.time_forces_pad_tree

/-- info: 'AdaptiveODELowerBound.Padding.mixed_forces_pad_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.mixed_forces_pad_tree

/-- info: 'AdaptiveODELowerBound.Padding.precision_forces_pad_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.precision_forces_pad_tree

/-- info: 'AdaptiveODELowerBound.Padding.precision_forces_sqrt_pad_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.precision_forces_sqrt_pad_tree

/-- info: 'AdaptiveODELowerBound.Padding.herald_max_cost_pad_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.herald_max_cost_pad_tree

/-- info: 'AdaptiveODELowerBound.Padding.herald_witness_pad_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.herald_witness_pad_tree

/-- info: 'AdaptiveODELowerBound.Padding.precision_terms_witness_pad_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.precision_terms_witness_pad_tree

/-! #### `AdaptiveODELowerBound.Padding.Combined` -/

/-- info: 'AdaptiveODELowerBound.Padding.combined_max_cost_pad_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.combined_max_cost_pad_tree

/-- info: 'AdaptiveODELowerBound.Padding.combined_pad_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.combined_pad_tree

/-- info: 'AdaptiveODELowerBound.Padding.combined_max_cost_common_dimension_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.combined_max_cost_common_dimension_tree

/-- info: 'AdaptiveODELowerBound.Padding.combined_common_dimension_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.combined_common_dimension_tree

/-- info: 'AdaptiveODELowerBound.Padding.combined_qubit_register_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Padding.combined_qubit_register_tree

/-! ### The released solver's oracle (`AdaptiveODELowerBound.Release`) -/

/-! #### `AdaptiveODELowerBound.Release.Bridge` -/

/-- info: 'AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree

/-- info: 'AdaptiveODELowerBound.Release.joint_release_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Release.joint_release_tree

/-- info: 'AdaptiveODELowerBound.Release.mixed_release_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Release.mixed_release_tree

/-- info: 'AdaptiveODELowerBound.Release.precision_release_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Release.precision_release_tree

/-- info: 'AdaptiveODELowerBound.Release.combined_max_release_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.Release.combined_max_release_tree

/-! ### Retry-protocol forms (`Retry`) -/

/-! #### `AdaptiveODELowerBound.Retry` -/

/-- info: 'AdaptiveODELowerBound.psd_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.psd_retry

/-- info: 'AdaptiveODELowerBound.hom_witness_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.hom_witness_retry

/-- info: 'AdaptiveODELowerBound.joint_witness_pad_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.joint_witness_pad_retry

/-- info: 'AdaptiveODELowerBound.herald_witness_pad_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.herald_witness_pad_retry

/-- info: 'AdaptiveODELowerBound.combined_pad_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.combined_pad_retry

/-- info: 'AdaptiveODELowerBound.joint_common_dimension_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.joint_common_dimension_retry

/-- info: 'AdaptiveODELowerBound.joint_qubit_register_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.joint_qubit_register_retry

/-- info: 'AdaptiveODELowerBound.combined_common_dimension_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.combined_common_dimension_retry

/-- info: 'AdaptiveODELowerBound.combined_qubit_register_retry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AdaptiveODELowerBound.combined_qubit_register_retry
