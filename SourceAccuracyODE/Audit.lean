import SourceAccuracyODE.Outcome
import SourceAccuracyODE.Constant
import SourceAccuracyODE.Time

/-! ## Axiom audits

Each audit fixes the exact axiom report of its declaration and fails to compile if the declaration
depends on any other axiom. The audits cover every theorem of the library (17 theorems), beginning
with the main theorems, then in module order. Every report lists exactly `propext`,
`Classical.choice` and `Quot.sound`. -/

/-! ### Final theorems: the constant-coefficient and time-dependent gate solvers with source circuits
within `ν` and the protocol guarantees from a relative vector error -/

/-- info: 'SparseHamiltonian.SourceAccuracyODE.binary_ode_outcome_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.binary_ode_outcome_nonneg

/-- info: 'SparseHamiltonian.SourceAccuracyODE.binary_time_outcome_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.binary_time_outcome_nonneg

/-- info: 'SparseHamiltonian.SourceAccuracyODE.binary_ode_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.binary_ode_outcome

/-- info: 'SparseHamiltonian.SourceAccuracyODE.binary_time_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.binary_time_outcome

/-- info: 'SparseHamiltonian.SourceAccuracyODE.native_ode_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.native_ode_outcome

/-- info: 'SparseHamiltonian.SourceAccuracyODE.native_zero_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.native_zero_outcome

/-- info: 'SparseHamiltonian.SourceAccuracyODE.native_time_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.native_time_outcome

/-- info: 'SparseHamiltonian.SourceAccuracyODE.native_time_zero_outcome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.native_time_zero_outcome

/-- info: 'SparseHamiltonian.SourceAccuracyODE.woutcome_of_vec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.woutcome_of_vec

/-- info: 'SparseHamiltonian.SourceAccuracyODE.woutcome_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.woutcome_of_bounds

/-! ### The protocol with a general per-trial bound (`Outcome`) -/

/-- info: 'SparseHamiltonian.SourceAccuracyODE.precision_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.precision_mul

/-- info: 'SparseHamiltonian.SourceAccuracyODE.trial_bounds_of_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.trial_bounds_of_rel

/-- info: 'SparseHamiltonian.SourceAccuracyODE.WOutcome.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.WOutcome.mono

/-- info: 'SparseHamiltonian.SourceAccuracyODE.native_trial_bounds_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.native_trial_bounds_rel

/-- info: 'SparseHamiltonian.SourceAccuracyODE.native_vector_error_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.native_vector_error_le

/-- info: 'SparseHamiltonian.SourceAccuracyODE.woutcome_lifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.woutcome_lifted

/-- info: 'SparseHamiltonian.SourceAccuracyODE.woutcome_direct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SparseHamiltonian.SourceAccuracyODE.woutcome_direct
