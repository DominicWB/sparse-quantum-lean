import GeneralODEZeroTime.Theorem

/-!
# Theorem `ode:thm:general` at `T = 0`: paper-to-Lean entry point

The proof of Theorem `ode:thm:general` (general constant-coefficient equations, Section
`ode:sec:general`) of the accompanying paper begins with "The case `T = 0` is direct state
preparation." The released theorem `SparseHamiltonian.GeneralODE.general` (library
`GeneralODE`, whose statement file lists the case `T = 0` as not formalised) assumes `T > 0`;
it is unchanged. This library formalises the case `T = 0` in the same physical oracle model and
states Theorem `ode:thm:general` for every `T ≥ 0`. Nothing from outside the paper is used at
`T = 0`: in particular the hypothesis `BlockSolver f q₀` (the block-input linear-system solver
of Costa et al. and Dalzell) is not needed there. Declarations are named relative to the
namespace `SparseHamiltonian.GeneralODE`; the new ones are in `GeneralODEZeroTime/Theorem.lean`,
the others in the released libraries (`GeneralODE` and the ODE layer of `SparseODE`).

* The case `T = 0` (direct state preparation): `general_zero`, with the protocol
  `ZeroTime.protocol`.
* Theorem `ode:thm:general` for every `T ≥ 0`: `general_nonneg`.

**Equation and access model.** As for `general` (see `GeneralODE/Statements.lean`):
`x' = A x + b`, `x(0) = x₀`, with `A = -M` for the matrix `M = D.matrix x` of the released
native sparse data `D : Data X n Z s` (`ODEPublicSourceMesh.generator D x`), and the target
`x(T) = ODEConstantForcing.solution A x₀ b T`; at `T = 0` it is `x₀`
(`ODEConstantForcing.solution_zero`). The sources are the released unitary interfaces `J₀ x`
and `J_b x` with a public unit seed. The oracles are `physicalOracle D J₀ Jb N Tn d m K w`: the
native queries on one of `K` copies of the block-encoding register (labels `(i, l)`) and the
two source interfaces (label `false` for `J₀`, label `true` for `J_b`), each acting
uncontrolled on the workspace of the released native control of `w` solver branches, with the
damping qubit as a spectator (`ZeroTime.physicalOracle_eq`). Native matrix queries are counted
by `ODESourceQueryBudget.matrixWeight (fun _ => 1)` and the calls of source `b` by
`ODESourceQueryBudget.sourceWeight b`, inverse calls included; `worstCost` is the maximum over
all histories of the protocol, failed attempts included.

**Hypotheses and guarantees.**

* `general_zero`: for any native data `D`, sources with `J₀ y` and `J_b y` unitary for every
  `y`, a seed with `‖seed‖ = 1` and any `N Tn d m K w` with `0 < w`, there is one protocol over
  `physicalOracle D J₀ Jb N Tn d m K w`, chosen before the input, that in every history makes no
  native matrix query, no call of `J_b` and at most `40` calls of `J₀`; and for every input `x`,
  every `x₀ ≠ 0` with `J₀ x seed = x₀/‖x₀‖`, every `b` and every `ε ≥ 0`, it satisfies
  `Amplify.Outcome prot x (x(0)) ε`: success probability at least `175/256` (and at least
  `2/3`), and conditioned on success the output is a density operator within spectral trace
  distance `ε` of `x(0)/‖x(0)‖ = x₀/‖x₀‖`. No norm bound on `M`, no public norm and no
  `BlockSolver` hypothesis is assumed.
* `general_nonneg`: the hypotheses of `general` with `0 ≤ T` in place of `0 < T`: a solver
  `BlockSolver f q₀` with `0 < q₀ ≤ 1` (used only for `T > 0`), `Λ > 0` with
  `‖matrixOperator (D.matrix x)‖ ≤ Λ` for every input, `C̄ ≥ 1`, `g ≥ 1`, `0 < ε ≤ 1/2`,
  unitary sources and a unit seed. With the parameters of `Plan` there are `Tn`, `d`, `w` and
  one protocol, chosen before the input, that in every history makes at most
  `if T = 0 then 0 else matrixBudget f q₀ s Λ T C̄ g ε` native matrix queries and at most
  `if T = 0 then (if b then 0 else 40) else sourceBudget f q₀ Λ T C̄ g ε` calls of source `b`,
  and that satisfies `Amplify.Outcome prot x (x(T)) ε` on every input satisfying the instance
  hypotheses of `Outcome`: `‖x₀‖ = r₀`, `‖b‖ = r_b`, the source directions,
  `‖e^{tA}‖ ≤ C̄` and `‖x(t)‖ ≤ g ‖x(T)‖` for `0 ≤ t ≤ T`, and `x(T) ≠ 0`. For `T > 0` this is
  `general`; for `T = 0` it is `general_zero` with `Tn = d = 0` and `w = 1`, where the
  hypothesis `x(0) ≠ 0` gives `x₀ ≠ 0`. With the parameters of `Plan` at `T = 0` the degree
  `K = Plan.degree Λ 0 C̄ g ε` is `0`, so the oracle family has no matrix-query labels at all
  (`Fin 0 × Query`); `general_zero` gives the bound `0` for every `K`.

**Proof map** (construction in the namespace `SparseHamiltonian.GeneralODE.ZeroTime`).

* The fixed encoding `ZeroTime.decoder`, `u ↦ |w₀⟩ ⊗ packet(|slot 0⟩ ⊗ u ⊗ |a₀⟩)`, with the
  history ancilla in a fixed clean basis state and the native control workspace in its clean
  packet, is both the input encoding of the seed and the output decoder (`decoder_isometry`,
  `norm_decoder`, `decoder_adjoint_apply`); `w₀ = 0` and `i₀` is any system index
  (`nonempty_of_norm_seed`).
* One uncontrolled physical call of `J₀` maps the encoding of `u` to the encoding of `J₀ x u`
  (`query_decoder`, from `oracle_branch_packet`, `slotControlled_ketL` and
  `sourceOracle_false_embed`); the program `ZeroTime.prepare` is this single query
  (`prepare_count`, `prepare_cost`), and all oracles are unitary (`maskedOracle_unitary`).
* `ZeroTime.protocol` is the released damping, randomized amplification and four-attempt
  wrapper `Amplify.protocol` with gain `1` applied to `prepare`. `Amplify.protocol_worstCost`
  bounds every history by `40` times the cost of `prepare` (`protocol_worstCost_le`,
  `protocol_matrix`, `protocol_forcing`, `protocol_initial`), and `Amplify.outcome`, with
  decoded amplitude `1 ≥ 1/2` and direction error `0`, gives the guarantee
  (`protocol_outcome`).

Every theorem of the library is axiom-audited in `GeneralODEZeroTime/Audit.lean`.

**Formalisation choices.**

* Direct state preparation is one call of the initial-state interface `J₀` on the encoded seed;
  the decoded output is exactly `x₀/‖x₀‖`. It is passed through the released damping and
  amplification wrapper, so that the guarantee has the same form as for `T > 0`
  (`Amplify.Outcome`: heralded success at least `175/256`, conditional mixed output).
* The budgets at `T = 0` are `0` matrix queries, `0` forcing calls and `40` initial-state calls
  (the worst case of the wrapper with gain `1`), not the `T > 0` budgets of `general`. The
  forcing `b`, the public norms and the bounds `Λ`, `C̄`, `g` play no role at `T = 0`.
* `general_zero` holds for all register parameters of the physical oracle model; in
  `general_nonneg` they are those of `Plan`, as in `general`.

**Not formalised.** The block-input linear-system solver used for `T > 0` (it remains the
hypothesis `BlockSolver f q₀` of `general` and `general_nonneg`), gate counts, and the related
remarks after `hs:thm:time`, `ode:thm:main` and `ode:thm:gates` that zero time or a known zero
generator needs no matrix queries (for a known zero generator with `T > 0` the target
`x₀ + T b` needs both source interfaces).
-/
