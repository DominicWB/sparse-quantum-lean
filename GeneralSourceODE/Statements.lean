import GeneralSourceODE.Corollaries

/-!
# Time-dependent sparse ODE with the general source interface: paper-to-Lean entry point

Theorem `ode:thm:time` (Section `ode:sec:time`) with the source
access of eqs. `ode:eq:source-interface-mass` and
`ode:eq:source-interface-preparation` is formalized by
`SparseHamiltonian.GeneralSourceODE.solver` in `GeneralSourceODE/Theorem.lean`,
with the uniform statement `SparseHamiltonian.GeneralSourceODE.Outcome`. The
earlier library `TimeDependentODE` proves the same theorem for the special
left-endpoint source rule with public source norms; this library replaces
that rule by the general interface. References to the manuscript use its labels.

**Equation and matrix access.** The equation is `x' = -G(u) x + b(u)` on
`[0, T]` with accretive `G(u)` (`TimeDependentODE.Accretive`), so `A = -G` is
dissipative. The represented samples `G̃_r = D.matrix (x, r)` on the uniform
mesh `t_r = r T / M` are released native sparse data
`D : NativeSparseBlockEncoding.Data (X × Fin M) n Z s`; a matrix query applies
one coherent sampled-time primitive, counted once with `r` in superposition
(`Native.matrixOracle`, as in `TimeDependentODE`).

**Source interface.** The input supplies public nodes `v : Fin m → ℝ` with
`v i ∈ [0, T]` and complex coefficients `ω : Fin m → ℂ`; the number `m` of
nodes is independent of `M`. Label `none` is the initial state and `some i`
the node `i`. The actual source vectors are `x(0)` and `ω_i b(v_i)`
(`sources`), with absolute mass `B_q = ‖x(0)‖ + ∑ |ω_i| ‖b(v_i)‖`
(`mass_sources`). The supplied preparations are unitary families
`Pw x` on the label register (`Weights.LabelOp`) and `J x a` on the data
register:

* `P_w |none⟩ = ∑_a √(‖z_a‖ / B_q) |a⟩` (`Compiled.WeightPrep`; the completion
  on other columns is arbitrary);
* `U_load`, applied as `∑_a |a⟩⟨a| ⊗ J x a`, prepares `x(0)/‖x(0)‖` on label
  `none` and `b(v_i)/‖b(v_i)‖` on every label with `ω_i ≠ 0`, `b(v_i) ≠ 0`.

The coefficient phases `ω_i / |ω_i|` are a public gate (`phases`,
`Oracles.phaseGate`). The primitive oracle family `Oracles.actualOracle` has
the matrix labels and three source labels, `P_w`, `U_load` and `P_w†`
(`SourceCall`, operations `Oracles.sourceOperation`), each applied with its
enable control (`ODESectorTensor.sourcePhysical` in `Oracles.actualOracle`).

**Hypotheses** of `solver`, all public:

* `0 ≤ η_H`, `0 ≤ η_D`, `0 < T`, `1 ≤ ḡ`, `1 ≤ c_q`, `0 < ε ≤ 1`, `0 < M`, and
  the sample energy bounds and positivity of `TimeDependentODE.solver` (the
  positivity is the formal restriction stated in `TimeDependentODE/Statements.lean`);
* with `g = c_q ḡ`, the mesh conditions of `TimeDependentODE.solver` at `g`
  (`ρ = η_H + R η_D > 0`, `8 s ρ T ≤ M`, `3 (√(2s) ρ T)³ ≤ ν M²`, where
  `R = TimeDependentODE.radius g ε` and `ν = TimeDependentODE.precision g ε`);
* nodes in `[0, T]`, unitary `P_w` and `U_load`, and a unit seed.

For every instance, after the circuit has been selected: the generator path
is accretive and `β_G`-Lipschitz with sample errors
`‖G(t_r) - G̃_r‖ ≤ δ_G`; the forcing `b` is continuous; `x(·)` solves the
equation (`SolvesODE`); `U t w` is the homogeneous solution on `[t, T]` with
value `w` at `t` (`IsPropagator`, so `U t w T = U(T, t) w`); `P_w` and
`U_load` act as above; `B_q ≤ c_q B` with `B = ‖x(0)‖ + ∫₀ᵀ ‖b‖`
(`sourceScale`); the propagated vector integral is certified,

  `‖∫₀ᵀ U(T, v) b(v) dv - ∑ ω_i U(T, v_i) b(v_i)‖ ≤ ζ B`;

`x(T) ≠ 0`, `B ≤ ḡ ‖x(T)‖`; and `ζ + c_q T (β_G T/M + δ_G) ≤ ε / (2000 ḡ)`.

**Guarantees.** There are a filter degree `d` and one public trial family
`t` over `Oracles.actualOracle`, with `chosenIterations (2 c_q ḡ)` unitary
trial circuits, such that for every valid instance four fresh trials of `t`
satisfy `Oracles.ActualCertificate` for the target `x(T)`, with
`g' = 2 c_q ḡ`:

* success probability at least `2/3` (also `175/256`);
* conditioned on success, the output density operator is positive with
  trace one and trace distance at most `ε` from `x(T) / ‖x(T)‖`;
* every history makes at most `1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)` matrix
  queries, `Θ = T η_H + T η_D ℓ`, `ℓ = log (10000 g' / (ε / 2))`, and at most
  `40 g'` calls of each of `P_w`, `U_load` and `P_w†` (`120 g'` in total),
  inverse calls included. Neither `M` nor `m` enters the counts.

`propagated_solver` (`PropagatedOutcome`) is the version on the two counted
composite interfaces `phase ∘ U_load ∘ (P_w ⊗ 1)` and `P_w† ⊗ 1`: its
certificate is stated for `x(T) - U(T,0)x(0) - ∑ ω_i U(T, v_i) b(v_i)`, it
does not assume that `b` is continuous, and it concludes the released complete
certificate `ODECompleteTrial.Certificate` with at most `40 g'` calls of each
composite interface (`80 g'` in total). Duhamel's formula (`duhamel`, which
uses the continuity of `b`) identifies the two certificates, and `solver`
follows by substituting `P_w`, `U_load`, the phase gate and `P_w†` for the
composite interfaces. `exists_isPropagator` shows that the propagator family
exists for every continuous generator path.

**Proof map.** Module paths are relative to `GeneralSourceODE/`.

* Clipped clock and per-label durations: a branch starting at `v` uses the
  parts of the slots after `v`, with a partial first step
  (`Durations`: `clip`, `width`, `durationTable`, `nodePropagator`; the LCHS
  product family `family`, with `family_neg_I` and
  `branchEvolution_eq_family`).
* Propagation error of one branch, uniformly over the start time
  (`Branch`: `homogeneous_norm_le`, `branch_error`).
* Label operators `P_w ⊗ 1` on the joint source/LCHS register, and the
  identities turning the public point-weight seed into the norm-weighted
  coefficient states (`Weights`: `act`, `act_coefficientInput`,
  `act_comp_coefficientOutput`, `loader`, `phaseGate`).
* The compiled preparation circuit with public seed and output, and its
  decoded vector (`Compiled`: `prep`, `sourceFamily`, `program`, `decoded_eq`).
* Counted amplification and primitive compilation with public trials
  (`Counted`: `compiled_geometry`, `counted_source_certificate`;
  `Primitive`: `trialCertificate_of_transfer`, `public_source_certificate`;
  `Native`: `matrix_valid`, `trial_certificate`).
* Source vectors, phases and the propagated target (`Target`:
  `phased_prepares`, `target_error`).
* Uniqueness, linearity, cocycle law and Duhamel's formula
  (`Duhamel`: `solvesODE_norm_le`, `homogeneous_unique`,
  `IsPropagator.cocycle`, `duhamel_hasDerivWithinAt`, `duhamel`).
* Separate counts of `P_w`, `U_load` and `P_w†` (`Oracles`:
  `implementation_eval`, `fourTrials_conditionalDensity_congr`,
  `actual_certificate`).
* Assembly with the released actual-source certificate
  (`Theorem`: `propagated_solver`, `solver`).

**Formalization choices.**

* The mesh of the matrix samples is uniform; the source nodes are arbitrary
  and independent of it. The duration table of a branch is public and is
  computed from its node, so the SELECT circuit is public.
* The circuit propagates every branch by the represented samples from its
  start time, and the LCHS formula is applied to these sampled propagators,
  so every sample must have a positive semidefinite dissipative part (the
  positivity hypothesis of `TimeDependentODE.solver`). This is a restriction of
  the formal theorem: the manuscript applies the LCHS formula to the exact path
  and asks of the represented samples only the uniform moment and norm
  promises, and its theorem is not changed. The certified branch error is
  `T (β_G T/M + δ_G)` per unit source norm (`branch_error`), a first-order
  bound in place of the chronological sampling estimate eq. `ode:eq:timedisc`.
  The quadrature error is the hypothesis `ζ B`.
* The weight oracle replaces the public source norms of the earlier
  library: the seed and output encoding are public and use the point weight
  on the initial label, so the circuit needs neither `B_q` nor the source
  norms. Only the bounds `B_q ≤ c_q B` and `B ≤ ḡ ‖x(T)‖` enter, through the
  amplification ratio `g' = 2 c_q ḡ`.
* `c_q ≥ 1` is assumed: a smaller `c_q` may be replaced by `1`, since the
  mass hypothesis is an upper bound, and the counts are then those at
  `c_q = 1`. The manuscript's `c_q` is an absolute constant, so its `O(ḡ)`
  source calls are unaffected.
* The library `GeneralSourceExtensions` proves the variants left out here:
  nonuniform meshes with breakpoints and integrated sample-error
  certificates, preparations implemented with operator-norm errors (here
  the preparations are exact), and the zero-time and zero-energy
  degenerate branches inherited from `ode:thm:main` (`T = 0`,
  `η_H + R η_D = 0`), separately and combined. Not formalised: gate and
  workspace costs.
-/
