import GateEfficientQuadrature.Energy
import GateEfficientQuadrature.Certificate
import GateEfficientQuadrature.Mass
import GateEfficientQuadrature.Paper
import GateEfficientQuadrature.Solver
import GateEfficientQuadrature.Native
import GateEfficientQuadrature.Sharp
import GateEfficientQuadrature.NonVacuity

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile
if the declaration depends on any other axiom. Every report lists `propext`,
`Classical.choice` and `Quot.sound`. The audits cover every theorem of the library of the
sufficient source quadrature of Theorem `ode:thm:gates`, beginning with the paper's statement
`paper_quadrature`, the certificate `cert_left` and the Lipschitz bound `flow_lipschitz`, and
ending with the energy bound and the algebra of solutions.
-/

/-! ### The sufficient left-endpoint quadrature of the proof of Theorem `ode:thm:gates` -/

/-- info: 'SparseHamiltonian.GateQuad.paper_quadrature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.paper_quadrature

/-- info: 'SparseHamiltonian.GateQuad.cert_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.cert_left

/-- info: 'SparseHamiltonian.GateQuad.flow_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.flow_lipschitz

/-- info: 'SparseHamiltonian.GateQuad.step_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.step_left

/-! ### The quadrature mass against the continuous mass -/

/-- info: 'SparseHamiltonian.GateQuad.integral_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.integral_affine

/-- info: 'SparseHamiltonian.GateQuad.mass_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.mass_left

/-- info: 'SparseHamiltonian.GateQuad.mass_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.mass_bounds

/-- info: 'SparseHamiltonian.GateQuad.nodes_sufficient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nodes_sufficient

/-- info: 'SparseHamiltonian.GateQuad.exists_pow_two_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.exists_pow_two_nodes

/-! ### The solver on branch-dependent meshes with the left-endpoint quadrature -/

/-- info: 'SparseHamiltonian.GateQuad.vQ_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.vQ_mem

/-- info: 'SparseHamiltonian.GateQuad.wQ_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.wQ_nonneg

/-- info: 'SparseHamiltonian.GateQuad.mass_wQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.mass_wQ

/-- info: 'SparseHamiltonian.GateQuad.wordValue_wordOf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.wordValue_wordOf

/-- info: 'SparseHamiltonian.GateQuad.sum_labels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.sum_labels

/-- info: 'SparseHamiltonian.GateQuad.sum_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.sum_words

/-- info: 'SparseHamiltonian.GateQuad.quad_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.quad_left

/-- info: 'SparseHamiltonian.GateQuad.LInstanceOK.toB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.LInstanceOK.toB

/-- info: 'SparseHamiltonian.GateQuad.outcomeL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.outcomeL

/-- info: 'SparseHamiltonian.GateQuad.solverL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.solverL

/-- info: 'SparseHamiltonian.GateQuad.budget_of_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.budget_of_paper

/-- info: 'SparseHamiltonian.GateQuad.disc_of_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.disc_of_paper

/-- info: 'SparseHamiltonian.GateQuad.nu_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nu_paper

/-- info: 'SparseHamiltonian.GateQuad.budget_disc_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.budget_disc_paper

/-- info: 'SparseHamiltonian.GateQuad.native_time_outcomeL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.native_time_outcomeL

/-! ### Sharpness and non-vacuity -/

/-- info: 'SparseHamiltonian.GateQuad.sum_range_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.sum_range_cast

/-- info: 'SparseHamiltonian.GateQuad.rampSol_solves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.rampSol_solves

/-- info: 'SparseHamiltonian.GateQuad.ramp_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.ramp_lipschitz

/-- info: 'SparseHamiltonian.GateQuad.const_homog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.const_homog

/-- info: 'SparseHamiltonian.GateQuad.sharp_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.sharp_cert

/-- info: 'SparseHamiltonian.GateQuad.sharp_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.sharp_mass

/-- info: 'SparseHamiltonian.GateQuad.cfg2_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.cfg2_eq

/-- info: 'SparseHamiltonian.GateQuad.inv_sqrt_two_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.inv_sqrt_two_sq

/-- info: 'SparseHamiltonian.GateQuad.nvWp2_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nvWp2_mul_self

/-- info: 'SparseHamiltonian.GateQuad.nvWp2_conjTranspose' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nvWp2_conjTranspose

/-- info: 'SparseHamiltonian.GateQuad.nvL_quadMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nvL_quadMass

/-- info: 'SparseHamiltonian.GateQuad.nvL_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nvL_mass

/-- info: 'SparseHamiltonian.GateQuad.nvL_zsrc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nvL_zsrc

/-- info: 'SparseHamiltonian.GateQuad.nvL_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nvL_instance

/-- info: 'SparseHamiltonian.GateQuad.nvL_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nvL_outcome

/-- info: 'SparseHamiltonian.GateQuad.nvL_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nvL_error

/-- info: 'SparseHamiltonian.GateQuad.nvL_kappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nvL_kappa

/-- info: 'SparseHamiltonian.GateQuad.nvL1_quadMass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nvL1_quadMass

/-- info: 'SparseHamiltonian.GateQuad.nvL1_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nvL1_mass

/-- info: 'SparseHamiltonian.GateQuad.nvL1_zsrc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nvL1_zsrc

/-- info: 'SparseHamiltonian.GateQuad.nvL1_instance' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nvL1_instance

/-- info: 'SparseHamiltonian.GateQuad.nvL1_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nvL1_outcome

/-- info: 'SparseHamiltonian.GateQuad.nvL1_error' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.nvL1_error

/-! ### The energy bound and the algebra of solutions -/

/-- info: 'SparseHamiltonian.GateQuad.affInt_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.affInt_hasDerivAt

/-- info: 'SparseHamiltonian.GateQuad.affInt_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.affInt_left

/-- info: 'SparseHamiltonian.GateQuad.affInt_right' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.affInt_right

/-- info: 'SparseHamiltonian.GateQuad.affInt_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.affInt_nonneg

/-- info: 'SparseHamiltonian.GateQuad.energy_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.energy_affine

/-- info: 'SparseHamiltonian.GateQuad.homog_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.homog_norm_le

/-- info: 'SparseHamiltonian.GateQuad.homog_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.homog_eq_zero

/-- info: 'SparseHamiltonian.GateQuad.solves_add_path' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.solves_add_path

/-- info: 'SparseHamiltonian.GateQuad.solves_sub_homog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.solves_sub_homog

/-- info: 'SparseHamiltonian.GateQuad.homog_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.homog_add

/-- info: 'SparseHamiltonian.GateQuad.homog_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.GateQuad.homog_sum
