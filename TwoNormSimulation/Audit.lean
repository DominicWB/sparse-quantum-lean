import TwoNormSimulation.Bounded
import TwoNormSimulation.Regimes
import TwoNormSimulation.TwoNorm

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (16 theorems), beginning
with the main theorems, then in module order. Every report lists exactly `propext`,
`Classical.choice` and `Quot.sound`. -/

/-! ### Final theorems: Theorem `hs:thm:two-norm` and its main steps -/

/-- info: 'TwoNormSimulation.two_norm_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoNormSimulation.two_norm_simulation

/-- info: 'TwoNormSimulation.two_norm_simulation_with_reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoNormSimulation.two_norm_simulation_with_reference

/-- info: 'TwoNormSimulation.bounded_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoNormSimulation.bounded_simulation

/-- info: 'TwoNormSimulation.exists_normalized_simulation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoNormSimulation.exists_normalized_simulation

/-- info: 'TwoNormSimulation.query_certificate_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoNormSimulation.query_certificate_sigma

/-- info: 'TwoNormSimulation.generator_norm_le_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoNormSimulation.generator_norm_le_entry

/-- info: 'TwoNormSimulation.bounded_shape_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoNormSimulation.bounded_shape_le

/-! ### The bounded-logarithm regime (`Bounded`) -/

/-- info: 'TwoNormSimulation.physical_exponent_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoNormSimulation.physical_exponent_sigma

/-- info: 'TwoNormSimulation.active_implementsOn_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoNormSimulation.active_implementsOn_sigma

/-- info: 'TwoNormSimulation.sqrt_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoNormSimulation.sqrt_sigma

/-- info: 'TwoNormSimulation.one_le_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoNormSimulation.one_le_sigma

/-- info: 'TwoNormSimulation.theta_sqrt_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoNormSimulation.theta_sqrt_sigma

/-! ### Scalar comparisons (`Regimes`) -/

/-- info: 'TwoNormSimulation.targetLog_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoNormSimulation.targetLog_le

/-! ### Theorem `hs:thm:two-norm` (`TwoNorm`) -/

/-- info: 'TwoNormSimulation.sigma_mul_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoNormSimulation.sigma_mul_theta

/-- info: 'TwoNormSimulation.sqrt_sigma_mul_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoNormSimulation.sqrt_sigma_mul_theta

/-- info: 'TwoNormSimulation.sigma_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TwoNormSimulation.sigma_eq
