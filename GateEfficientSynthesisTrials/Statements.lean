import GateEfficientSynthesisTrials.Binary
import GateEfficientSynthesis.ODESolver

/-!
# Synthesised trials with exact reflections: paper-to-Lean entry point

Theorem `ode:thm:gates` of the accompanying paper ends with the per-trial claim "every
successful trial has Euclidean error at most `ε`, up to a global phase". Its proof (paragraph
"Bounded amplification of the implemented circuit") performs `j` Grover iterations on the
actual finite-gate preparation unitary and its actual inverse, with the reflections kept exact
("These tests are exactly implementable using reversible Boolean gates and a phase flip"), so
every successful attempt outputs the data direction `y/‖y‖` of the implemented preparation, and
the vector error of the implemented circuit (equation `ode:eq:gate-vector-error`) gives the
per-trial error. The finite-gate-set forms of `GateEfficientSynthesis`
(`GateSynth.native_ode_solver_synth`, `GateSynth.native_ode_time_solver_synth`) synthesise every
gate of every trial, the reflections included, and state no per-trial claim
(`GateSynth.SOutcome`). This library formalises Theorem `ode:thm:gates` over a finite gate set
with the per-trial claim, as in the proof of the paper: only the preparation is synthesised, its
inverse is the exact adjoint of the synthesised preparation, and the zero tests and the global
sign are exact gates of the gate set. The released libraries are unchanged. All declarations
below are in the namespace `SparseHamiltonian.GateSynthTrials`.

* Theorem `ode:thm:gates` over a finite gate set, with the per-trial claim:
  `native_ode_solver_trials` (constant coefficients), `native_ode_time_solver_trials`
  (time-dependent coefficients); from binary sparse data: `binary_ode_solver_trials`,
  `binary_ode_time_solver_trials`.
* The gate-set hypotheses: `AdjClosed`, `zeroTestKinds` (`GateOf.inv`, `gateOf_mcGate`,
  `two_le_zeroLitsN`, `gateOf_rgoodNG`, `gateOf_rseedNG`, `gateOf_negGateN`); they are without
  loss of generality: `closeKinds`, `extra_hyps` (`zeroTestKinds_adjClosed`,
  `zeroTestKinds_finite`, `closeKinds_adjClosed`, `synthesis_closeKinds`).
* The trial register and the synthesised preparation: `SX`, `sPool`, `SWO`, `embS`,
  `synthPrep` (`synthPrep_valid`, `synthPrep_counts`, `synthPrep_gateOf`,
  `synthPrep_inv_gateOf`, `synthPrep_pres`, `trialS_valid`, `trialS_gateOf`, `hnP_SWO`); the
  registers of the solvers `SNW`, `STW`.
* The error of the synthesised preparation: `synthPrep_approx` (`approxOn_trans`,
  `approxOn_restrict`, `liftB_embS`).
* The certificate with the vector error `10νB`: `output_certificate10`, `trial_bounds_of_vec10`,
  `vector_error10`, `native_trial_bounds10`, `noutcome10`; the synthesised protocol:
  `synth_noutcome`.
* The counts: `synth_protocol_worst`, `synth_protocol_worst_log`, `card_SWO`, `card_SWO_eq`,
  `card_tested`.

**The model.** As in `GateEfficientNative` and `GateEfficientSynthesis`: circuits are lists of
native instructions (`GateNative.NInstr`: elementary gates, one-qubit unitaries with at most
three literal controls, and calls of the primitive oracles), and a native preparation `prepN`
acts on a native ODE register `V = HWO a m r K k l f S Zs nP Z bT bP A` (the released wires, the
system, the private work wires, the source scratch `Zs`, a flag and a pool `Fin nP`). A gate kind
records the control values and the matrix of a gate; `GateSynth.GateOf 𝒢 g`: `g` has distinct
control wires and kind in `𝒢`. `GateSynth.Synthesis 𝒢 X len`: `𝒢` is finite and every one-qubit
unitary with at most three controls is approximated within every `ζ > 0` by at most `len ζ`
valid gates of `𝒢` on its wires and the clean ancilla wires `X`, in the full-output convention
(ancilla residues and phases included). `GateSynth.synthBudget hS η prepN` synthesises every
gate of `prepN` at accuracy `η/(N+1)`, `N` its gates, and keeps every call.

**The gate-set hypotheses and why they are needed.**

* `AdjClosed 𝒢`: `(p, u) ∈ 𝒢 → (p, uᴴ) ∈ 𝒢`. The inverse preparation of every Grover step is
  the literal inverse `GateNative.ninv` of the synthesised preparation, whose gates are
  `⟨cs, t, uᴴ⟩`: it is then a circuit over `𝒢` (`GateOf.inv`, `synthPrep_inv_gateOf`) and it is
  the exact adjoint of the synthesised preparation, which the exact Grover analysis of the
  actual unitary needs (an independently synthesised inverse would not be).
* `zeroTestKinds ⊆ 𝒢`, `zeroTestKinds = {([0,0], X), ([1,0], X), ([1], Zm), ([], -1)}`
  (`X = pauliX`, `Zm = zMat = diag(-1, 1)`): the zero tests are kept exact, so their gates must
  be gates of `𝒢`. A zero test with at least two zero literals (`GateCircuit.mcGate`; the native
  zero tests have at least the solver wires `ini` and `flg`, `two_le_zeroLitsN`) computes an
  AND chain on clean flags by NOT gates with two controls of values `(0, 0)` (first step) and
  `(1, 0)`, applies `zMat` to its flag controlled by the last flag of the chain (value `1`) and
  uncomputes the chain with the same NOT gates; the global sign of a Grover step is the
  one-qubit matrix `-1` (`gateOf_mcGate`, `gateOf_rgoodNG`, `gateOf_rseedNG`,
  `gateOf_negGateN`). These are exactly the kinds that occur.

**The hypotheses are not restrictive** (`extra_hyps`). For every synthesis hypothesis
`Synthesis 𝒢₀ X len`, the gate set `closeKinds 𝒢₀ = 𝒢₀ ∪ {(p, uᴴ) | (p, u) ∈ 𝒢₀} ∪ zeroTestKinds`
satisfies `Synthesis (closeKinds 𝒢₀) X len`, with the same ancillas and the same length function
(`synthesis_closeKinds`: it is finite and contains `𝒢₀`), is closed under adjoints
(`closeKinds_adjClosed`; the four kinds of the exact zero tests are self-adjoint,
`zeroTestKinds_adjClosed`) and contains `zeroTestKinds`. So the endpoints apply over
`closeKinds 𝒢₀` whenever the released synthesis hypothesis holds over `𝒢₀`. The two hypotheses
are formal versions of the "actual inverse" of the paper's proof and of its zero tests "exactly
implementable using reversible Boolean gates and a phase flip"; since the exact Grover analysis
needs the inverse and the reflections to be exact, some form of each is required.

Single-qubit synthesis and the decomposition of controlled gates enter only through the
released hypothesis `GateSynth.Synthesis`; no other result from another paper is used.

**The synthesised protocol** (`Register`, `Certificate`). The trial register
`SWO … = HWO a m r K k l f S (SX Zs nP X) (sPool …) Z bT bP A` is a native ODE register whose
scratch slot `SX Zs nP X = OX Zs nP ⊕ X` holds the native scratch, the native flag and pool and
the synthesis ancillas, with a fresh flag and a fresh pool of
`sPool = |AW| + |XW| + |SX| + |S|` wires for the zero tests (`hnP_SWO`). The placement
`embS : V ⊕ X ↪ SWO …` avoids the fresh flag and pool (`embS_not_refl`). The synthesised
preparation is `synthPrep hS η prepN = (synthBudget hS η prepN).map (NInstr.map embS)`, and the
synthesised protocol is the released native four-attempt protocol
`GateNative.nprotocol (synthPrep hS η prepN) g` on the trial register: a uniform trial count
`j < chosenIterations g ≤ 5 g`, the trial `GateNative.trialN (synthPrep hS η prepN) j` (the
synthesised preparation followed by `j` steps: the released exact good-subspace zero test
`rgoodNG`, the literal inverse of the synthesised preparation, the released exact seed zero test
`rseedNG`, the synthesised preparation and the sign `negGateN`), and the clean-output herald.
On the trial register the zero tests test every wire of `V ⊕ X` (except, for `rgoodNG`, the
system), the native flag and pool and the synthesis ancillas included, with the fresh flag and
pool as their scratch. Hence (released `GateNative.trialN_seed`) every trial applied to the seed
is exactly the actual Grover trial `ODEGroverActual.trial goodN (nrun prim P) sN j` of the
synthesised preparation unitary `P`.

**The error budget** (`Approx`, `Certificate`). With `ν = ε/(10000 g)` the released certificate
gives `‖3B goodF†(Urel seed) - x‖ ≤ 6νB` for the released preparation `Urel`, and the native
preparation is within `δ ≤ ν` of `liftB (conj Urel)` on clean work wires (the native budget
`24 d ζ + 2 ζs ≤ ν`, respectively `24 d ζ + 3 ζs ≤ ν`). The synthesised preparation is within
`η + δ` (`synthPrep_approx`), so with the public synthesis budget `η = ν/3` its decoded vector
satisfies `‖3B dS - x‖ ≤ 10νB` (`vector_error10`). The released output certificate holds with
`10νB` (relative error `10 ν g ≤ ε/1000`; `output_certificate10`), so the released randomized
amplification theorem `ODEGroverActual.randomized_certificate` applies to the actual
preparation (`trial_bounds_of_vec10`, `native_trial_bounds10`): mean success at least `1/4` and
every nonzero decoded trial within `ε/500` of `x/‖x‖` up to a global phase.

**Endpoints.** Hypotheses: `hS : Synthesis 𝒢 X len`, `hadj : AdjClosed 𝒢`,
`hzt : zeroTestKinds ⊆ 𝒢` (the last two without loss of generality, `extra_hyps`), and the
public hypotheses of the native solver (unchanged).

* `native_ode_solver_trials` (constant coefficients; public data `p` with `p.PublicOK`, `U_J`
  gates, a public native private operation `nd`, arithmetic `ar` with `ArithOK` at accuracy `ζ`,
  valid source circuits `srcC`): with `η = p.nu / 3` and `P = synthPrep hS η (nprepC p UJg nd ar
  srcC)`, (1) every instruction of every trial `trialN P j` is valid and every gate is a gate of
  `𝒢`; (2) the native preparation has at most
  `prepGates + 84 d |UJg| + 6 d G_C + |srcC 0| + |srcC 1|` gates and
  `12 d calls(V) + calls(srcC 0) + calls(srcC 1)` calls of every kind, and `P` has at most
  `N len(η/(N+1))` gates (`N` the native gates) and exactly the native calls; (3) in every history
  the protocol `nprotocol P g` makes at most `40 g` times the native calls of every kind and uses
  at most `40 g N_P + 20 g (4 n + 3)` gates, `N_P` the gates of `P` and
  `n = |W| + |XW| + |SX Zs nPool X| + |S|`; (4) if `len ζ' ≤ c₁ log(1/ζ') + c₀` on `(0, 1]`
  (`c₀, c₁ ≥ 0`), at most `40 g N (c₁ log((N+1)/η) + c₀) + 20 g (4 n + 3)` gates; (5) the register
  `SNW p S Zs Z bT bP A X` has
  `|S| + 2 (|W| + (|Z| + bT + bP + A + 3) + (|Zs| + 1 + nPool + |X|)) + |S| + 1` qubits,
  `nPool = |W| + |XW| + |Zs| + |S|`; (6) for every instance satisfying the hypotheses of
  `GateNative.native_ode_solver` (unitary primitive oracles, `NativeOK`, source circuits within
  `ζs`, `24 d ζ + 2 ζs ≤ ν`, `p.InstanceOK`) the protocol has the guarantees
  `GateNative.NOutcome (P) g ε prim x`, `x = p.target H L x0 b` the solution at time `T`:
  unitary trials, mean success at least `1/4`, **every successful trial within `ε/500` of
  `x/‖x‖` up to a global phase** (`trial_direction`: for every `j`, if the decoded trial
  amplitude `goodN† (nrun prim (trialN P j) sN)` is nonzero, some `ω` with `‖ω‖ = 1` has
  `‖ω • unitDirection(amplitude) - unitDirection x‖ ≤ ε/500`), success probability at least
  `175/256 ≥ 2/3`, and a conditional output density within trace distance `ε` of `x/‖x‖`.
* `native_ode_time_solver_trials` (time-dependent coefficients, `p : TParams`): the same with
  `tnprepC p UJg nd ar loadC wpC`, the ratio `2 g` (so `80 g` times the calls and
  `80 g N_P + 40 g (4 n + 3)` gates), the native gate count
  `prepGates + 84 d |UJg| + 6 d G_C + |loadC| + 2 |wpC|`, the budget `24 d ζ + 3 ζs ≤ ν` and the
  target `x(T)`; here `ν = (ε/2)/(10000 · 2g)`.
* `binary_ode_solver_trials`, `binary_ode_time_solver_trials`: the instantiations for the binary
  data of `GateBinaryODE.binary_ode_solver` and `GateBinaryODETime.binary_ode_time_solver`
  (native counts of `binary_ode_counts`, `binary_ode_time_counts`; `n` with `k` system qubits;
  the instance hypotheses of the released binary solvers), with the same conclusions.

**Proof map.** `Kinds` (gate-set hypotheses, gates of the zero tests) → `Register` (trial
register, synthesised preparation, validity, gate set, untouched fresh flag and pool) → `Approx`
(error `η + δ` of the synthesised preparation) → `Certificate` (`10νB`, the released
`trialN_seed` and `ODEGroverActual.randomized_certificate`, `NOutcome`) → `Protocol` (counts) →
`Solver` (the native glue of `native_ode_solver` and `native_time_outcome`: `oprep_approx`, the
released certificate `prep_certificate`, `decoded_eq`, target facts) → `Binary`.

**Formalisation choices and deviations from the paper.**

* The paper's vector error is `19νB` for its own allocation; here the released allocation is
  kept (`6νB` for the released preparation, `δ ≤ ν` for the native implementation) and the
  synthesis gets `η = ν/3`, giving `10νB`; the direction error is `ε/500`, stronger than the
  paper's `ε`.
* The synthesis budget `η = ν/3` is chosen from public data only (`ν = ε/(10000 g)`,
  respectively `ε/(40000 g)`); the native instance hypotheses are unchanged.
* The zero tests act on a fresh flag and pool, and test the native flag and pool and the
  synthesis ancillas as well: the synthesised preparation need not keep any wire exactly
  clean. The trial register therefore has `2 (|V| + |X|) + 1` qubits for the native register `V`
  and the synthesis ancillas `X` (`card_SWO`, `card_SWO_eq`): about twice the `|V| + |X|` qubits
  of the synthesised register of `GateEfficientSynthesis`, a constant factor.
* Only the preparation is synthesised, so the logarithmic synthesis factor multiplies only its
  gates; the zero tests and the sign count as exact gates (`40 g N (c₁ log((N+1)/η) + c₀) +
  20 g (4 n + 3)`), unlike `GateSynth.sprotocol_worst_log`, where every gate of a trial is
  synthesised.
* The source circuits are part of the native preparation and are synthesised with it; the paper
  counts `G_src(ν)` directly over the gate set.
* The exact zero tests use NOT gates with two controls of values `(0, 0)` and `(1, 0)`, a
  controlled `zMat` and the sign `-1`, each counted as one gate of `𝒢`. Adding these four
  self-adjoint kinds and the adjoints of `𝒢` keeps `𝒢` finite and keeps `Synthesis` with the same
  length function (`extra_hyps`), so the hypotheses are not restrictive; for a fixed gate set such
  as Clifford+T, which implements them only by exact circuits (a Toffoli gate with negated
  controls in at most 19 gates, seven of them `T` or `T†` gates; the controlled `zMat` in 5
  Clifford gates; `-1 = (XZ)²`), an exact decomposition step would multiply the zero-test count by
  a constant; it is not formalised.

Every theorem of the library is axiom-audited in `GateEfficientSynthesisTrials/Audit.lean`.

**Not formalised.** Single-qubit synthesis and the decomposition of controlled gates (released
hypothesis `GateSynth.Synthesis`); exact inverses and exact decompositions of the zero-test kinds
over gate sets that are not adjoint-closed or do not contain these kinds (for example Clifford+T
without Toffoli-type gates); the asymptotic form of equations `ode:eq:gate-main` and
`ode:eq:gate-space` (for the binary-data solvers see `GateEfficientODEBudget`); the construction
of the source circuits.

**Provenance.** New library; it reuses without change `GateEfficientNative` (native register,
trials, zero tests, protocol, `NOutcome`, the glue lemmas of the native solvers),
`GateEfficientSynthesis` (`Synthesis`, `GateOf`, `synthBudget`, `synthC_approxOn`,
`gates_log_le`), `GateEfficientHamiltonian` (`GateCircuit.mcGate`, `GateCircuit.andChain`,
`GateCircuit.pauliX`, `GateCircuit.Sim.zMat`), `SparseODE.ODEGroverActual` (randomized
amplification of the actual preparation), `GateEfficientODE` (the released certificate) and the
binary-data libraries `GateEfficientBinaryODE`, `GateEfficientBinaryODETime`.
-/
