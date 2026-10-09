import GeneralODE.Theorem
import GeneralODE.Complexity

/-!
# General constant-coefficient ODE: paper-to-Lean entry point

Theorem `ode:thm:general` (general constant-coefficient equations) of the
accompanying paper, with Lemma `ode:lem:block` (Fourier implementation of the
arcsine polynomial), is formalized here. The one ingredient from outside the
paper, a near-optimal linear-system solver with block-encoded input (Costa et
al.; Dalzell), is the explicit hypothesis `BlockSolver f q₀`; it is never an
axiom.

* Main theorem: `SparseHamiltonian.GeneralODE.general` in
  `GeneralODE/Theorem.lean`, with the guarantee
  `SparseHamiltonian.GeneralODE.Outcome`, the physical oracle family
  `SparseHamiltonian.GeneralODE.physicalOracle` and the budgets
  `SparseHamiltonian.GeneralODE.matrixBudget` and `sourceBudget`.
* Closed form for a solver with `c κ log(2/δ)` calls:
  `SparseHamiltonian.GeneralODE.Complexity.general_query_bound` in
  `GeneralODE/Complexity.lean`.
* Lemma `ode:lem:block`:
  `SparseHamiltonian.GeneralODE.NativeBlock.exists_native_block` in
  `GeneralODE/Native/BlockEncoding.lean`.

**Equation.** `x' = A x + b`, `x(0) = x₀`, on `[0, T]` with `A = -M` for the
matrix `M = D.matrix x` of the released native sparse access
(`ODEPublicSourceMesh.generator D x`); the target is
`x(T) = ODEConstantForcing.solution A x₀ b T`. No dissipativity or normality
is assumed.

**Access model.** The released native sparse data `D : Data X n Z s` (row
and column locators and the entry oracle, `NativeSparseBlockEncoding`), and
the released source interfaces: unitaries `J₀ x`, `J_b x` with a public unit
seed, `J₀ x seed = x₀/‖x₀‖` and `J_b x seed = b/‖b‖` when these vectors are
nonzero, with public norms `‖x₀‖ = r₀` and `‖b‖ = r_b`. The physical oracles
(`physicalOracle`) are the native queries on one of `K` copies of the
block-encoding register (labels `(i, l)`) and the two source interfaces
(labels `false`, `true`), each acting on the workspace of the released
native control (`NativeMaskedProgram.oracle`) with all other registers as
spectators; the physical calls themselves are uncontrolled. Forward and
inverse calls are counted by `ODESourceQueryBudget.matrixWeight` and
`sourceWeight`.

**Hypothesis** (`Solver.BlockSolver f q₀`, `GeneralODE/Solver/Interface.lean`).
For all finite registers `s, a`, a clean ancilla `a₀`, a unit input `e₀`,
`κ ≥ 1` and `0 < δ ≤ 1/2` there are a solver circuit with at most `f κ δ`
calls, acting on `w` branches of the oracle register `s × a`, and a fixed
isometric decoder `out`, such that for every unitary block encoding `U` and
preparation `B` with `B (e₀ ⊗ a₀) = β ⊗ a₀`, `‖β‖ = 1`, block
`M = ⟨a₀| U |a₀⟩` with `‖v‖ ≤ κ ‖M v‖` for all `v`, and `M x = β`, the decoded
output has squared norm at least `q₀` and direction within `δ` of that of
`x`, up to a phase. Its oracle calls apply `U` or `B` on the branches selected
by a fixed mask; controlled calls are obtained by fixed permutations.

**Public data.** `Λ > 0` with the promise `‖M‖ ≤ Λ` for every input; `T > 0`;
`C̄ ≥ 1`; `g ≥ 1`; `0 < ε ≤ 1/2`; the solver's `0 < q₀ ≤ 1`; and `r₀, r_b`.
Derived (`GeneralODE/Plan.lean`): `α = 8√2 Λ`, `m = ⌈α T⌉` steps of length
`h = T/m`, the budget `ϑ = ε/(1680 C̄ g)`, the Taylor degree
`K = ⌈log₂ ⌈m/ϑ⌉⌉`, the arcsine degree `K + 1`, the simulation precision
`ε_n = ϑ/(4m(K+1))`, `κ = 7 κ_H(m, 2, e, 2C̄) = 7 (2 + 2C̄ (2m+1)(2+4e))`,
`δ = ε/(40 g)` and the amplification gain `5 g/√q₀`.

**Instance hypotheses.** `‖x₀‖ = r₀`, `‖b‖ = r_b`, the source directions,
`‖e^{tA}‖ ≤ C̄` and `‖x(t)‖ ≤ g ‖x(T)‖` for `0 ≤ t ≤ T`, and `x(T) ≠ 0`.

**Guarantees** (`general`). One protocol, chosen before the input, such that
in every history, including four failures, it makes at most

* `matrixBudget = 40 (5g/√q₀) · f(κ, δ) · 3K · 1327104 · shape(2s, 2(K+1), log(2/ε_n))`
  native matrix queries, where
  `shape(a, b, ℓ) = √a b + √(a b ℓ) + ℓ` is the released query shape;
* `sourceBudget = 40 (5g/√q₀) · 3 f(κ, δ)` calls of each source interface;

and for every input satisfying the instance hypotheses (`Amplify.Outcome`)
it succeeds with probability at least `175/256 > 2/3`, and conditioned on
success its output is a density operator within spectral trace distance `ε`
of `x(T)/‖x(T)‖`. As for the released ODE endpoints, the output guarantee is
stated for the conditional mixed output.

**Closed form** (`Complexity.general_query_bound`). If `f(κ, δ) = c κ log(2/δ)`
with `c ≥ 0`, then with `𝓛 = 1 + log((1 + ΛT) C̄ g / ε)` there is a protocol
with the guarantees above (in the proof, the protocol of `general`) making at
most
`159443481054412800 · c (g/√q₀) C̄ (1 + ΛT) √s 𝓛³` native matrix queries and
`18404400 · c (g/√q₀) C̄ (1 + ΛT) 𝓛` calls of each source, since
`κ ≤ 4382 C̄ (1 + ΛT)`, `log(2/δ) ≤ 7 𝓛`, `K ≤ 34 𝓛` and the block encoding
costs at most `1327104 · 192 √s 𝓛` queries. With constant `q₀` this is the
paper's `Õ(√s ḡ_path C̄ (1 + ΛT))`.

**Proof map.** Module paths are relative to `GeneralODE/`.

* Analysis of the history system: perturbed powers (`Analysis/Runs`),
  Taylor and `φ₁` remainders (`Analysis/ExpBounds`), affine recursions
  (`Analysis/Recursion`), the residual map and its inverse bound
  `norm_le_kappaH` (`Analysis/History`), the explicit history solution,
  the forcing bound `T ‖b‖ ≤ (3 + 2ΛT) max_j ‖x(jh)‖` and the trajectory
  accuracy (`Analysis/HistorySolution`), the implemented step and source
  built from the blocks `B_U ≈ A/α`, `B₀ ≈ I` (`Analysis/Implemented`,
  `implemented_bounds`), the common error budget (`Analysis/Accuracy`,
  `history_accuracy`) and final-time decoding (`Analysis/Decode`).
* Block encodings: registers, selected maps, fresh-ancilla products,
  standard forms and program lifts (`Block/Registers`, `Block/Selected`,
  `Block/Power`, `Block/Standard`, `Block/Programs`); the history unitary
  with block `N⁻¹ (P₀ - S - C)` (`Block/HistoryCircuit`, `Block/HistoryBlock`,
  `Block/HistoryEncoding`, `HistData.block_unitary`) and its program with
  exactly `K` calls of the block-encoding program (`Block/HistoryProgram`).
* Lemma `ode:lem:block`: the arcsine series and its Fourier form
  (`Native/Arcsine`), the arcsine LCU of a self-adjoint operator
  (`Native/Spectral`, `lcu_approx`), linear combinations of selected
  families (`Native/LCU`), `A = -((1+i)/2) K₊ + ((1-i)/2) K₋` with the row and
  column energies (`Native/Matrix`), the branch table (`Native/Branches`,
  `lcu_block_approx`) and the native program (`Native/BlockEncoding`,
  `signed_evolution`, `exists_native_block`).
* The solver interface, the exact right-hand-side preparation, compilation
  to the native oracles, the system on one instance, damping and
  amplification, and the protocol: `Solver/Interface`, `Solver/Source`
  (`prepProgram_eval`), `Solver/Compose` (`composed_eval`,
  `composed_matrix_cost`), `Solver/System` (`system`), `Solver/Amplify`
  (`outcome`, `protocol_worstCost`), `Solver/Protocol`
  (`exists_protocol_of_block`); parameters `Plan`; main theorem `Theorem`;
  closed form `Complexity`.

**Formalization choices.**

* The `φ₁` source enters through a source column of the history matrix: the
  forcing slot carries `μ b` and is coupled to the slots `1, …, m` through
  `Φ/√m`, `Φ = ∑_k τ^k/(k+1)! P_k`. The right-hand side `(μ b, x₀, 0, …)` is
  therefore prepared exactly, with public weights, by one call of each
  source. The bound `ḡ_B` is not needed: the forcing mass is controlled by
  `T ‖b‖ ≤ (3 + 2ΛT) max_j ‖x(jh)‖ ≤ (3 + 2ΛT) g ‖x(T)‖`.
* Lemma `ode:lem:block` uses the released two-tag native access
  `K_± = H ± L` (`L = (M + M†)/2`, `H = (M - M†)/(2i)`) instead of the
  Hermitian dilation; each `X_± = K_±/(4Λ)` has norm at most `1/2`, and the
  arcsine Fourier LCU gives a block of `A/(8√2 Λ)` (the paper's normalisation
  is `2πΛ`) with error `2ε_n + 4^{-(K+1)}/2`, and a second block of `I` with
  error `2ε_n`. Negative durations are implemented by a forward run of the
  released coherent simulator followed by the adjoint of a second run.
* No closeness of unitary extensions and no perturbed generator `Â` is used:
  the implemented blocks enter the Taylor step and the source polynomial
  directly, and their errors are charged to the common budget `ϑ` together
  with the Taylor remainder.
* Masked calls of the history unitary and of the preparation are compiled
  by the released whole-program native control: every native or source query
  inside a masked call becomes three uncontrolled calls on one common clean
  encoding, so a masked history call costs `3 K · count(qP)` native queries
  and a masked preparation three calls of each source. The source interfaces
  are applied controlled on the history slot register (`Solver.sourceOracle`:
  `J₀` on slot `0`, `J_b` on the forcing slot), a controlled-source access of
  the kind the paper's ODE model grants; these wrappers are defined in
  `Solver/Source`.
* Final-time extraction uses a damping qubit and the released randomized
  amplification with gain `5 g/√q₀`, followed by at most four attempts.
* The history normalisation is `7`; all constants are explicit and not
  optimised.
* Not formalised: the block-input linear-system solver itself (the
  hypothesis), the case `T = 0` (direct state preparation), and gate counts.
-/
