import MixedOutputODE.Complexity

/-!
# General constant-coefficient ODE with a mixed-output solver: paper-to-Lean entry point

Theorem `ode:thm:general` (Section `ode:sec:general`) is proved here from the solver guarantee that
the manuscript requests in eq. `ode:eq:history-solver-tolerance`: a block-input linear-system solver
that delivers only a *conditional output trace distance* `δ_LS = ε / (2¹² ḡ²)`, possibly with mixed
output. The released library `GeneralODE` proves the theorem from the stronger pure-output
hypothesis `GeneralODE.Solver.BlockSolver`; everything except the solver interface, the final
selection and the requested accuracy is reused from it. References to the manuscript use its labels.

* Main theorem: `SparseHamiltonian.MixedOutputODE.general` in
  `MixedOutputODE/Theorem.lean`, with the guarantee
  `SparseHamiltonian.MixedOutputODE.Outcome` and the budgets
  `MixedOutputODE.matrixBudget` and `MixedOutputODE.sourceBudget`.
* Closed form for a solver with `c κ log(2/δ)` calls:
  `SparseHamiltonian.MixedOutputODE.general_query_bound` in
  `MixedOutputODE/Complexity.lean`.
* The pure-output hypothesis `BlockSolver` implies `MixedBlockSolver` with a
  trivial work register (`mixed_of_block`); `general_of_block` is the theorem
  from `BlockSolver`.

**Hypothesis** (`MixedBlockSolver f q₀`, `MixedOutputODE/Interface.lean`).
For all finite registers `s, a`, a clean ancilla `a₀`, a unit input `e₀`,
`κ ≥ 1` and `0 < δ ≤ 1/2` there are a solver circuit with at most `f κ δ`
calls, a finite work register `W` and a fixed isometric decoder
`out : ℂ^{s × W} → workspace`, such that for every unitary block encoding `U`
and preparation `B` as in `BlockSolver` (block `M` with `‖v‖ ≤ κ ‖M v‖`,
`M x = β`), the decoded output `z` has squared norm at least `q₀` and the
reduced state `ptrace |ẑ⟩⟨ẑ|` of `ẑ = z / ‖z‖` on `s` is within trace distance
`δ` of `|x̂⟩⟨x̂|`. The work register holds the solver's work and measurement
records coherently; nothing is assumed about it.

**Access model, public data and instance hypotheses** are those of
`GeneralODE.general`: native sparse access to `M = D.matrix x` with
`A = -M` and `‖A‖ ≤ Λ`, the source interfaces `J₀`, `J_b` with a unit seed and
public norms, `Λ > 0`, `T > 0`, `C̄ ≥ 1`, `g ≥ 1`, `0 < ε ≤ 1/2`, `0 < q₀ ≤ 1`, and for
the instance `‖e^{tA}‖ ≤ C̄`, `‖x(t)‖ ≤ g ‖x(T)‖` on `[0, T]` and `x(T) ≠ 0`.
The requested solver accuracy is `mixedDelta g ε = ε / (4096 g²)`.

**Guarantees** (`general`). There are a work register `W` and one protocol,
chosen before the input, such that in every history it makes at most

* `matrixBudget = 40 (5g/√q₀) · f(κ, ε/(4096 g²)) · 3 K · 1327104 · shape(2s, 2(K+1), log(2/ε_n))`
  native matrix queries;
* `sourceBudget = 40 (5g/√q₀) · 3 f(κ, ε/(4096 g²))` calls of each source
  interface;

and for every valid input (`MixedOutcome`) it succeeds with probability at
least `175/256 > 2/3`, and conditioned on success its output, after the work
register is discarded (`ptrace`), is a density operator within trace
distance `ε` of `x(T)/‖x(T)‖`.

**Closed form** (`general_query_bound`). If `f(κ, δ) = c κ log(2/δ)` with
`c ≥ 0`, then with `𝓛 = 1 + log((1 + ΛT) C̄ g / ε)` there is a protocol with
the guarantee of `general` (in the proof, the protocol of `general`) that
makes at most `227776401506304000 · c (g/√q₀) C̄ (1 + ΛT) √s 𝓛³` native matrix
queries and
`26292000 · c (g/√q₀) C̄ (1 + ΛT) 𝓛` calls of each source, since
`log(2/δ) ≤ 10 𝓛` (`log_mixedDelta_le`). With constant `q₀` this is the
paper's `Õ(√s ḡ_path C̄ (1 + ΛT))`.

**Proof map.** Module paths are relative to `MixedOutputODE/`.

* Trace norm of self-adjoint operators: Hölder bound, sign operator,
  triangle inequality, scaling, compressions, pure-state bound
  (`TraceNorm`: `norm_tr_comp_le`, `tr_signOp`, `tnorm_add_le`,
  `tnorm_compress_le`, `hermitianTraceDistance_triangle`,
  `hermitianTraceDistance_pure_le`, `eq_of_hermitianTraceDistance_le_zero`).
* Partial trace over the retained work register and `V ⊗ 1`
  (`PartialTrace`: `ptrace`, `tensorLeft`, `ptrace_conj`, `ptrace_pure`,
  `tr_ptrace`, `ptrace_isDensity`).
* Selection from a mixed output: selected probability at least `p - 2δ`,
  selected reduced state within `2δ / (p - 2δ)` (`Selection`: `selection`).
* The interface, its implication from the pure-output interface and the constants
  (`Interface`: `MixedBlockSolver`, `mixed_of_block`, `mixedDelta`,
  `mixed_select`, `mixed_amplitude`, `mixed_error`).
* The protocol: the released history system and composed solver, the
  decoder `V ⊗ 1` on the retained register, the released damped randomized
  amplification with the actual selected vector as its own target (so it is
  preserved exactly), and the discarded register
  (`Protocol`: `exists_mixed_protocol_of_block`, `MixedOutcome`).
* Assembly and the closed form: `Theorem` (`exists_protocol`, `general`,
  `general_of_block`), `Complexity` (`general_query_bound`).

**Formalization choices.**

* The solver output is modelled as a pure state on the solution register and
  a finite work register, as produced by a unitary circuit with deferred
  measurements; its conditional reduced state is the mixed output of
  eq. `ode:eq:history-solver-tolerance`.
* The amplification acts on the joint workspace, with the work register
  kept; the target of the released amplification certificate is the actual
  selected vector, so amplification adds no error, and the error budget is
  `2δ/(p - 2δ) + ε/4 ≤ ε` with `p ≥ θ²`, `θ = (1 - ε/8)/(8g)`
  (`mixed_error`).
* Selection uses the released final-time decoder of `GeneralODE`, onto the
  uniform superposition of the final slots (`GeneralODE.Decode.finalSlots`),
  rather than the projection `P` onto all final labels. Its ideal selection
  probability is at least `θ² ≥ 225/(16384 g²)` instead of the manuscript's
  `1/(12 ḡ²)`, and the estimates of `selection`, selected probability at
  least `p - 2δ` and selected-state error `2δ/(p - 2δ)`, are weaker than the
  manuscript's `p - δ` and `2δ/p`; with `δ = ε/(4096 g²)` the selection error
  is at most `8ε/221`.
* The history construction, the native block encoding and the source
  preparation are those of `GeneralODE`, with its formalisation choices
  (`GeneralODE/Statements.lean`): a source column with an exactly prepared
  right-hand side, the two-tag block encoding of normalisation `8√2 Λ`, no
  perturbed generator, and no bound `ḡ_B`.
* Not formalised: the solver itself (the hypothesis) and gate counts. The
  case `T = 0` needs no solver and is `GeneralODE.general_zero`
  (`GeneralODEZeroTime`); the statement for every `T ≥ 0` there,
  `GeneralODE.general_nonneg`, uses `BlockSolver`, and no version of it for
  `MixedBlockSolver` is stated.
-/
