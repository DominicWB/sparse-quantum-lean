import GateEfficientSelect.Model
import GateEfficientSelect.Branch
import GateEfficientSelect.Lemma
import GateEfficientSelect.NonVacuity
import GateEfficientSelect.ODE.Branch
import GateEfficientSelect.ODE.Table
import GateEfficientSelect.ODE.Disc
import GateEfficientSelect.ODE.Certificate
import GateEfficientSelect.ODE.Theorem
import GateEfficientSelect.ODE.Native
import GateEfficientSelect.ODE.Left
import GateEfficientSelect.ODE.NonVacuity

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`, except for 3 lemmas, whose reports list a subset of these
three axioms: the injectivity lemmas `labCfg_injective` and `outPart_labCfg_injective` of the
label configurations (`Quot.sound` only) and `ODE.fin_one_fun_eq` (`propext` and
`Quot.sound`). The audits cover every theorem of the library of Lemma `ode:lem:gate-select` on
branch-dependent meshes, beginning with the lemma `gate_select` and the solvers `ODE.solverB`
and `ODE.native_ode_time_solverB`, and ending with the branch data and the certificate of the
differential-equation solver.
-/

/-! ### Lemma `ode:lem:gate-select`, exact gates -/

/-- info: 'SparseHamiltonian.GateSelect.gate_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.gate_select

/-- info: 'SparseHamiltonian.GateSelect.gate_select_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.gate_select_inverse

/-- info: 'SparseHamiltonian.GateSelect.branchPath_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.branchPath_selfAdjoint

/-- info: 'SparseHamiltonian.GateSelect.branchPath_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.branchPath_lipschitz

/-- info: 'SparseHamiltonian.GateSelect.branch_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.branch_budget

/-- info: 'SparseHamiltonian.GateSelect.branch_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.branch_error

/-! ### Theorem `ode:thm:gates`, time-dependent part, on branch-dependent meshes -/

/-- info: 'SparseHamiltonian.GateSelect.ODE.exists_branch_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.exists_branch_solution

/-- info: 'SparseHamiltonian.GateSelect.ODE.outcomeB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.outcomeB

/-- info: 'SparseHamiltonian.GateSelect.ODE.solverB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.solverB

/-- info: 'SparseHamiltonian.GateSelect.ODE.native_time_outcomeB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.native_time_outcomeB

/-- info: 'SparseHamiltonian.GateSelect.ODE.native_ode_time_solverB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.native_ode_time_solverB

/-- info: 'SparseHamiltonian.GateSelect.ODE.maskedPropagator_eq_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.maskedPropagator_eq_shift

/-- info: 'SparseHamiltonian.GateSelect.ODE.homog_disc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.homog_disc

/-- info: 'SparseHamiltonian.GateSelect.ODE.vLeft_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.vLeft_mem

/-- info: 'SparseHamiltonian.GateSelect.ODE.wLeft_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.wLeft_nonneg

/-- info: 'SparseHamiltonian.GateSelect.ODE.bsW_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.bsW_left

/-- info: 'SparseHamiltonian.GateSelect.ODE.startB_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.startB_left

/-- info: 'SparseHamiltonian.GateSelect.ODE.start_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.start_lt

/-- info: 'SparseHamiltonian.GateSelect.ODE.quad_leftEndpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.quad_leftEndpoint

/-! ### Non-vacuity -/

/-- info: 'SparseHamiltonian.GateSelect.one_add_I_mul_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.one_add_I_mul_ne_zero

/-- info: 'SparseHamiltonian.GateSelect.cayleyScalar_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.cayleyScalar_norm

/-- info: 'SparseHamiltonian.GateSelect.smul_one_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.smul_one_comp

/-- info: 'SparseHamiltonian.GateSelect.isUnitary_smul_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.isUnitary_smul_one

/-- info: 'SparseHamiltonian.GateSelect.clock_scalar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.clock_scalar

/-- info: 'SparseHamiltonian.GateSelect.nvStart_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.nvStart_mem

/-- info: 'SparseHamiltonian.GateSelect.nvK_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.nvK_mem

/-- info: 'SparseHamiltonian.GateSelect.nvAddr_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.nvAddr_mem

/-- info: 'SparseHamiltonian.GateSelect.nvVal_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.nvVal_mem

/-- info: 'SparseHamiltonian.GateSelect.smul_one_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.smul_one_norm_le

/-- info: 'SparseHamiltonian.GateSelect.smul_one_star' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.smul_one_star

/-- info: 'SparseHamiltonian.GateSelect.nvH_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.nvH_sub

/-- info: 'SparseHamiltonian.GateSelect.nv_sample_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.nv_sample_eq

/-- info: 'SparseHamiltonian.GateSelect.nv_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.nv_steps

/-- info: 'SparseHamiltonian.GateSelect.nv_all_hyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.nv_all_hyps

/-- info: 'SparseHamiltonian.GateSelect.nv_select' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.nv_select

/-- info: 'SparseHamiltonian.GateSelect.ODE.permMat_unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.permMat_unitary

/-- info: 'SparseHamiltonian.GateSelect.ODE.nvP_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.nvP_tau

/-- info: 'SparseHamiltonian.GateSelect.ODE.nvP_nu' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.nvP_nu

/-- info: 'SparseHamiltonian.GateSelect.ODE.nvP_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.nvP_ok

/-- info: 'SparseHamiltonian.GateSelect.ODE.wordValue_fin_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.wordValue_fin_one

/-- info: 'SparseHamiltonian.GateSelect.ODE.fin_one_fun_eq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.fin_one_fun_eq

/-- info: 'SparseHamiltonian.GateSelect.ODE.nv_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.nv_mass

/-- info: 'SparseHamiltonian.GateSelect.ODE.nv_zsrc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.nv_zsrc

/-- info: 'SparseHamiltonian.GateSelect.ODE.nv_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.nv_instance

/-- info: 'SparseHamiltonian.GateSelect.ODE.nvB_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.nvB_outcome

/-! ### One branch on its own mesh -/

/-- info: 'SparseHamiltonian.GateSelect.clock_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.clock_family

/-- info: 'SparseHamiltonian.GateSelect.qbar_nonneg_of_clock' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.qbar_nonneg_of_clock

/-- info: 'SparseHamiltonian.GateSelect.exp_branch_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.exp_branch_step

/-- info: 'SparseHamiltonian.GateSelect.branch_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.branch_block

/-- info: 'SparseHamiltonian.GateSelect.branch_propagator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.branch_propagator

/-! ### Label-selected circuits -/

/-- info: 'SparseHamiltonian.GateSelect.evalS_gate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.evalS_gate

/-- info: 'SparseHamiltonian.GateSelect.runS_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.runS_eq

/-- info: 'SparseHamiltonian.GateSelect.runS_invList' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.runS_invList

/-- info: 'SparseHamiltonian.GateSelect.runS_isUnitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.runS_isUnitary

/-- info: 'SparseHamiltonian.GateSelect.labCfg_injective' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.labCfg_injective

/-- info: 'SparseHamiltonian.GateSelect.outPart_labCfg_injective' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.outPart_labCfg_injective

/-- info: 'SparseHamiltonian.GateSelect.labelOf_clear' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.labelOf_clear

/-- info: 'SparseHamiltonian.GateSelect.selE_isometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.selE_isometry

/-- info: 'SparseHamiltonian.GateSelect.select_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.select_error

/-- info: 'SparseHamiltonian.GateSelect.card_SW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.card_SW

/-! ### The branch-dependent solver: branches, selection, LCHS, discretisation and certificate -/

/-- info: 'SparseHamiltonian.GateSelect.ODE.startB_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.startB_mem

/-- info: 'SparseHamiltonian.GateSelect.ODE.durB_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.durB_nonneg

/-- info: 'SparseHamiltonian.GateSelect.ODE.durB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.durB_le

/-- info: 'SparseHamiltonian.GateSelect.ODE.stepB_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.stepB_nonneg

/-- info: 'SparseHamiltonian.GateSelect.ODE.sum_stepB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.sum_stepB

/-- info: 'SparseHamiltonian.GateSelect.ODE.zsrc_bsW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.zsrc_bsW

/-- info: 'SparseHamiltonian.GateSelect.ODE.mass_bsW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.mass_bsW

/-- info: 'SparseHamiltonian.GateSelect.ODE.branchHB_selfAdjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.branchHB_selfAdjoint

/-- info: 'SparseHamiltonian.GateSelect.ODE.branch_sample_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.branch_sample_norm_le

/-- info: 'SparseHamiltonian.GateSelect.ODE.exp_branchHB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.exp_branchHB

/-- info: 'SparseHamiltonian.GateSelect.ODE.evolution_branchHB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.evolution_branchHB

/-- info: 'SparseHamiltonian.GateSelect.ODE.branch_blockB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.branch_blockB

/-- info: 'SparseHamiltonian.GateSelect.ODE.select_errorB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.select_errorB

/-- info: 'SparseHamiltonian.GateSelect.ODE.familyB_ofReal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.familyB_ofReal

/-- info: 'SparseHamiltonian.GateSelect.ODE.familyB_neg_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.familyB_neg_I

/-- info: 'SparseHamiltonian.GateSelect.ODE.lchs_errorB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.lchs_errorB

/-- info: 'SparseHamiltonian.GateSelect.ODE.propB_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.propB_norm_le

/-- info: 'SparseHamiltonian.GateSelect.ODE.targetB_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.targetB_norm_le

/-- info: 'SparseHamiltonian.GateSelect.ODE.solvesODE_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.solvesODE_shift

/-- info: 'SparseHamiltonian.GateSelect.ODE.propB_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.propB_eq

/-- info: 'SparseHamiltonian.GateSelect.ODE.branch_disc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.branch_disc

/-- info: 'SparseHamiltonian.GateSelect.ODE.target_errorB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.target_errorB

/-- info: 'SparseHamiltonian.GateSelect.ODE.BInstanceOK.unitary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.BInstanceOK.unitary

/-- info: 'SparseHamiltonian.GateSelect.ODE.target_factsB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.target_factsB

/-- info: 'SparseHamiltonian.GateSelect.ODE.prep_certificateB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.prep_certificateB

/-- info: 'SparseHamiltonian.GateSelect.ODE.trial_boundsB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateSelect.ODE.trial_boundsB
