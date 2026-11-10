import SignedFactorSimulation.Theorem

set_option autoImplicit false

/-!
# Theorem `opt:thm:signed`: paper-to-Lean entry point

Appendix A of the manuscript proves Theorem `hs:thm:optimal` through a
simulation theorem for indefinite factors, Theorem `opt:thm:signed`, whose
finite implementation is Sections `opt:sec:factor` and `opt:sec:tail`. This library proves Theorem
`opt:thm:signed` at the circuit level, from the clock weights of Theorem `opt:thm:weights` and the
operator tail estimate of Lemma `opt:lem:tail` (library `OptimalPrecision`). The native and
large-sparsity factors (`opt:sec:native`, `opt:sec:core`) and Theorem `hs:thm:optimal` are not
part of this library.

No result from another paper is used. The released libraries are unchanged; the reuse, LCU,
amplification and chronological-network constructions of `SparseHamiltonian` are reused. References
to the manuscript use its labels. Every theorem of the library is axiom-audited
in `SignedFactorSimulation/Audit.lean`.

**Naming convention.** All declarations are in the namespace `SignedFactorSimulation`; names
below are relative to it, except the fully qualified names of the released libraries.

## The statement

The factor interface `opt:eq:factor` is `Known P W` (module `Factor`): a known initialised-input
isometry `E : P → W`, a known success projection `Π` and a known Hermitian unitary `Z` commuting
with `Π`. For a supplied unitary `U = U_B` on `W`, the factor is `B = Π U E`
(`Known.factor`), `C = B† Z B` (`Known.Cop`) and `D = B† B` (`Known.Dop`); the Hamiltonian is
`H = λ C` (`Known.ham`).

**Theorem `opt:thm:signed`** (`signed_factor_simulation`, module `Theorem`). Let `P` and `W` be
finite-dimensional, let `U x` be unitary for every instance `x`, and let `D(U x) ⪯ δ I` with
`λ > 0` and `0 < δ ≤ 1`. For every time `t` and `0 < ε ≤ 1/64`, put `T = λ|t|`, `b = T δ`,
`L = log(1/ε)` and `r_b = L/log(e + L/b)` (`rb`). There are a finite label type `ι`, a known
isometry `inp : P → ℂ^ι ⊗ W` (the space `PiLp 2 (fun _ : ι => W)`) and a program whose only
oracle is the factor query `I_ι ⊗ U` (`SparseHamiltonian.WeightedClock.diagonal
(fun _ : ι => U x)`) and its adjoint, every other gate being a known unitary
(`SparseHamiltonian.OracleCircuit.Program`), such that

* the number of factor queries, counting adjoints, is `0` if `b ≤ ε` and at most
  `4·10¹⁰ (√(Tb) + √(T r_b) + r_b)` otherwise (`opt:eq:signed-bound`, with an explicit constant
  in place of `O(·)`);
* for every instance, `‖p.eval x ∘ inp - inp ∘ e^{-itH}‖ ≤ ε` (full-output error, with the
  same known embedding on input and output).

The embedding `inp` is not a plain `|0⟩` initialisation: it contains the known LCU preparation and
the uniform public clock state. By the paper's convention ("Known changes of input or output
encoding can be absorbed into surrounding circuits") this is the full-output error of the paper. The
input, the embedding and every gate are chosen before the instance; the program is the same for all
instances `x`. `signed_factor_simulation_uniform` states the theorem with the instances all
admissible factor unitaries (`Admissible K δ`, unitaries with `D ⪯ δ I`). Controls are not oracle
primitives: the controlled private steps are built from `U`, `U†` and known gates, and their cost is
included in the count.

## The proof

*Clock identity and three-phase transfer* (modules `Coefficients`, `Factor`, `FiniteTransfer`,
`Cascade`). The uniform clock of `n` reuses of a colligation is `Ces_n` of its causal transfer
(`successfulBlock_eq_ces`). The private unitary `P = U† G U` with the known Cayley phase `G` of
`qZ` on success (`Known.phase`, `Known.priv`) has the generator
`E†(I + wP)(I - wP)⁻¹E = OptimalPrecision.Tail.Omega q C D w` (`Known.omega_eq`, `opt:eq:omega`),
and the
chronological cascade of `m` boundary rotations has the transfer `u(w)^m`, with
`u = (I - (v/2)Ω)(I + (v/2)Ω)⁻¹` (`transfer_cascade`, `Known.transfer_cascade_factor`,
`opt:eq:finite-transfer`, `opt:eq:finite-F`).

*Finite mesh* (module `Mesh`). For `m ≥ 8an` slots of step `v = a/m`,
`‖∑ λ_j Ces_j(F_m) - ∑ λ_j Ces_j(e^{-aΩ})‖ ≤ 128 A a³ n⁴/m²` (`Known.finite_mesh`,
`opt:eq:finite-mesh`).

*Signed LCU* (modules `Extension`, `LCU`). Every register is a copy of `W`; the public block of
a colligation is extended from `P` to `W` by the identity off the range of `E` (`extA`, `extB`,
`extC`, `ext_energy`, `successfulBlock_ext`). Branch `j` runs `j` reuses of the cascade; two
padding branches complete the absolute weight. The successful block of the LCU is
`s ∑_{j=1}^n λ_j Ces_j(F_m)` (`cascade_block`), and a known diagonal sign unitary maps its output
preparation to its input preparation (`lcuSign_comp_lcuOut`).

*Factor queries* (module `Query`). One factor query is `U` on every register (`liftU`). The
private step on the active branches is `liftU(U)† · (known controlled phase) · liftU(U)`
(`liftU_conj`); on public registers and finished branches the two queries cancel. Each layer of
the synchronized SELECT is a known coupling network after this step (`select_eq_product`), so
SELECT uses `2n` queries (`select_implements`).

*Amplification* (modules `Amplify`, `Query`, `Core`). The LCU is attenuated to
`s₀ = sin(π/(2·3⁸))` (`ampS`); eight rounds of the three-SELECT reflection round
(`ampCirc`, `3⁸` calls of SELECT) give block error at most `7⁸ e₀` (`ampIter_block_error`), and
a block error `δ` gives full-output error `√(2δ)` (`full_output_error`, `opt:eq:amplified-full`);
`amplified_error` combines them with the sign alignment.

*The circuit for `q ≥ 1`* (module `Core`). With the clock weights of Theorem `opt:thm:weights`
(`n ≤ 27 qM`, `∑ |λ_j| ≤ 3000`), Lemma `opt:lem:tail` and the mesh, `core` gives a program with
at most `2·3⁸·27·qM` queries and full-output error `ε` for `e^{-i q²M C}`, after the known
flattening of the workspace to `ℂ^ι ⊗ W` (`flat`, `flat_liftU`).

*Order, attenuation and time* (modules `Parameters`, `Attenuation`, `Theorem`). The order is
`M = ⌈40000 b + 100000 r_b⌉` (`order`), for which the factorial tail is at most `ε²/(4·7⁸)`
(`tail_bound`) and `r_b ≥ 1/2` when `b > ε` (`rb_ge_half`, `opt:eq:rb-lower`). If `T ≥ M`, then
`q = √(T/M)`; if `T < M`, the factor is attenuated by `κ = T/M` (`Known.atten`: the known input
`(√κ|0⟩ + √(1-κ)|1⟩) ⊗ E` with success flag `|0⟩`, so that `C' = κ C`, `D' = κ D` and the factor
query is `I ⊗ U`, `Known.atten_Cop`, `Known.atten_Dop`) and `q = 1` (`positive_time`). Negative
time uses the adjoint program; if `b ≤ ε` the identity suffices, since
`‖e^{-itH} - I‖ ≤ |t| ‖H‖ ≤ b` (`norm_evolution_sub_one_le`, `Known.norm_ham_le`).

## Scope and differences from the manuscript

* Only query complexity is claimed here; the gate-level implementation (Theorem `gate:thm:main`) is
  the library `GateOptimalPrecision`; here the finite mesh and the known
  coefficient preparations are exact known gates of the query model, not gate-efficient
  constructions. Accordingly no error budget is spent on approximating known gates.
* The amplification uses `k_o = 3⁸` (eight rounds of tripling with an explicit error recursion)
  in place of an odd `k_o = O(A_*)` with the polar-decomposition argument; the query count is
  within the same bound.
* The attenuation of the factor is placed in the known input isometry instead of a rotation
  after `U_B`; the factor query is then exactly `I ⊗ U_B`.
* Every register is a copy of `W`: public slots are copies of `W` and public blocks are
  extended by the identity off the range of `E` (`extA`), so that a factor query acts on every
  register; on the public registers `U` and `U†` cancel.
* The signed weights `2 s₀ λ_j` are padded to absolute mass two by two cancelling branches, in
  place of padding the normalisation to `A_*` and attenuating.
* `Z` is a Hermitian unitary on all of `W` commuting with `Π` (equivalently, `Z` on the
  success space extended by the identity).
* The error budgets are `ε²/(4·7⁸)` for the tail and for the mesh, in place of `ε²/144`.
* The constant `4·10¹⁰` is explicit and is not optimised.
-/
