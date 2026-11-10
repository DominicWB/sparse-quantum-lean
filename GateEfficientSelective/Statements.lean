import GateEfficientSelective.HamBridge
import GateEfficientSelective.Nodes
import GateEfficientSelective.ODEBudget

/-!
# Selective finite-gate-set synthesis: equations `hs:eq:gate-total`, `ode:eq:gate-main` and
`ode:eq:gate-space` with the supplied finite-set circuits charged linearly: paper-to-Lean entry
point

Theorem `hs:thm:gates` of the accompanying paper lets "`G_C(ξ)` and `A_C(ξ)` bound the additional
gates and clean work qubits for this controlled operation to error on all output registers at most
`ξ` [...] The inverse is the adjoint of the implemented circuit", and with `ξ = ε/(24d)` and
`G_syn = C₀[d(C_J+a+m_slot+r_reuse) + A_C(ξ)]` (equation `hs:eq:gate-Gzero`) bounds the
additional gates and auxiliary qubits by `O(d G_C(ξ) + G_syn log((G_syn+1)/ε))` and
`O(A_C(ξ) + a + m_slot + r_reuse)` (equation
`hs:eq:gate-total`). Theorem `ode:thm:gates` lets "`G_src(ζ)` count the gates for `P_w`, this
loading and `P_w†` … This includes the non-matrix-oracle gates inside the chosen loading circuits;
`A_src(ζ)` bounds their work qubits", and bounds the gates and auxiliary qubits of the solver by
`C ḡ [q P(𝔟) + G_src(ν) + A_src(ν)]` and `P(𝔟) + C A_src(ν)` (equations `ode:eq:gate-main`,
`ode:eq:gate-space`) for a polynomial `P` that does not depend on the supplied circuits.

The released finite-gate-set compiler (`GateSynth.synthC`, `GateSynth.synthBudget`) synthesises
every elementary gate of a native circuit, the gates of supplied circuits included, so its counts
are `N L(ε'/(N+1))` with `N` all the gates (`GateSynth.binary_simulation_budget_synth`), and the
released ODE budgets carry the synthesis factor `64(𝔟+1) + log(G_src + 1)` on the source gates
(`GateBitBudget.binary_ode_budget_trials_bits`, `GateBinaryNodes.binary_nodes_budget_trials_bits`).
This library adds a compiler that retains the gates already in the finite gate set and synthesises
only the others, and proves the separated forms of both theorems (for `ode:thm:gates` a partial
formalisation, under this package's format hypotheses, of its finite-set statement: the manuscript
states Theorem `ode:thm:gates` over a finite gate set; the conformance endpoints count native
gates) with the supplied costs entering
linearly and outside every logarithm, without any assumption on their size.

No result from another paper is used. The released libraries are unchanged. References to the
manuscript use its labels. Every theorem of the library is axiom-audited in
`GateEfficientSelective/Audit.lean`.

**Naming convention.** All declarations of this library are in the namespace
`SparseHamiltonian.GateSelective` and are named relative to it below. Released declarations are
named relative to `SparseHamiltonian` (for example `GateNative.NInstr`, `GateSynth.Synthesis`,
`GateSynthTrials.AdjClosed`, `GateNative.nprotocol`); the released names `GateOf`
(`GateSynth`), `ApproxOn`, `CleanP`, `CleanX`, `ctrlIdeal`, `selOp`, `liftB`, `privMacro`,
`nGatesN`, `nCallsN`, `NOutcome` (`GateNative`), `AdjClosed` and `zeroTestKinds`
(`GateSynthTrials`) are also used unqualified.

**The synthesis hypothesis** (released, unchanged). `GateSynth.Synthesis 𝒢 X L`: every
one-qubit unitary with at most three controls is approximated within every `ζ > 0` by at most
`L ζ` gates of the finite gate set `𝒢`, on distinct wires and a fixed register `X` of clean
ancillas, in the full-output convention (ancilla residues and phases included);
`GateSynth.Synthesis.of_parts` derives it from single-qubit synthesis and an exact
decomposition of controlled gates. `GateOf 𝒢 g`: the gate `g` is a gate of `𝒢`.

**The selective compiler** (module `Compiler`). For a native circuit `C` (elementary gates and
primitive calls), `nSynN 𝒢 C` counts its gate occurrences outside `𝒢` and `nKeepN 𝒢 C` those in
`𝒢` (`nKeepN_add_nSynN`). `selC hS ζ C` keeps every gate of `𝒢` verbatim (`selRep_kept`), replaces
every other gate by its synthesis at accuracy `ζ` on the reused clean register `X` (`selRep_synth`)
and keeps every primitive call.

* `selC_spec`: valid instructions, every gate a gate of `𝒢`, at most `nKeepN C + nSynN C · L ζ`
  gates, exactly the calls of `C` for every oracle.
* `selC_approxOn`, `selC_error`: for unitary primitive oracles the compiled circuit is within
  `nSynN C · ζ` of `C` on clean synthesis ancillas, in the full-output convention: only the
  synthesised gates contribute.
* `selBudget hS δ C = selC hS (δ/(K+1)) C`, `K = nSynN C`: error at most `δ`
  (`selBudget_approxOn`, `selBudget_error`), at most `nKeepN C + K L(δ/(K+1))` gates
  (`selBudget_spec`) and, if `L ζ ≤ c₁ log(1/ζ) + c₀`, at most
  `nKeepN C + K' (c₁ log((K'+1)/δ) + c₀)` gates for every `K' ≥ K` (`selBudget_gates_log`).
* `selC_retained`, `selC_append`: a circuit over `𝒢` is unchanged, and the compiler acts
  instruction by instruction; `nSynN_ninv`, `nKeepN_ninv`, `selC_inv_gateOf`, `ninv_gateOf`: for
  an adjoint-closed `𝒢` the literal reverse-adjoint of the compiled circuit is a circuit over `𝒢`
  with the same counts.

**Hamiltonian simulation** (modules `HamMacro`, `HamSim`, `HamBridge`).

* `hcircP ρ sw UJg pc l`: the native circuit of `GateNative.hcirc` in which every
  sector-controlled private Cayley call is the **supplied** circuit `pc` for the enable-controlled
  private operation (or its literal reverse-adjoint `ninv pc`), on the private wires
  `PWr Sel (Fin a ⊕ S) Z bT bP A`; with `pc = privMacro nd ar` it is the released native circuit
  (`hcircP_privMacro`). The hypothesis on `pc` is the full-output guarantee
  `ApproxOn CleanP (nrun prim pc) (ctrlIdeal Dsel) ξ`: on every input with clean work wires it is
  within `ξ` of the ideal enable-controlled operation, which returns the work wires clean;
  `ctrl_inv_approx` gives the same for its reverse-adjoint.
* `hcircP_nCalls`, `hcircP_nGates`, `hcircP_nil_nGates`, `nSynN_hcircP_le`, `hcircP_error`: the
  calls are `nPriv · |pc|_calls`, the gates `nGatesN (hcircP ∅) + nPriv · |pc|`, the synthesised
  occurrences at most `nGatesN (hcircP ∅)` whatever `pc` (gates of `pc` in an adjoint-closed `𝒢`),
  and the errors of the private calls add (`nPriv · ξ`).
* `sel_simulation` (equations `hs:eq:gate-Gzero`, `hs:eq:gate-total`): under the synthesis
  hypothesis with `L ζ ≤ c₁ log(1/ζ) + c₀`, an adjoint-closed `𝒢`, the clock promises of the
  released analysis and a valid `pc` over `𝒢` within `ξ`, `24dξ ≤ ε`: the selective circuit
  `selSim` (the released circuit at accuracy `ε/2`, the private calls supplied, synthesis budget
  `ε/4`) consists of valid gates of `𝒢` and primitive calls, makes exactly `6d` times the calls
  of `pc`, synthesises at most `G₀ = 200(d+1)(a+m+r+1) + 84dC_J` occurrences whatever `pc`, has
  at most `6d|pc| + G₀(c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates and
  `|S| + (2a + 3m + 6r + 3) + (|Z| + bT + bP + A + 3) + |X|` qubits, and its full output, every
  qubit outside the system clean, is within `ε` of `exp(-iτH)`; `d` is the released formal degree.
* `sel_simulation_signed`: every real time (the literal reverse-adjoint of the compiled circuit for
  `|t|`, a circuit over `𝒢`); `sel_time_simulation`: time-dependent Hamiltonians on a uniform mesh
  with a supplied slot-selected private circuit.
* `privSel hS η nd ar`, `privSel_spec`, `nSynN_privMacro_le`: from the native data of
  `GateEfficientNative`, an actual finite-set circuit for the enable-controlled private operation:
  the native implementation compiled selectively once, within `η + 4ζ`, with exactly twice the
  calls of the compute circuit `V` and at most `nKeepN + K L(η/(K+1))` gates,
  `K ≤ 2 nSynN V + 2|arith| + 2bP + bT + 1`; `sel_simulation_native`,
  `sel_time_simulation_native`: the endpoints for this circuit (`G_C(ξ) = |privSel|`,
  `A_C(ξ) = |Z| + |X| + bT + bP + A`, `ξ = η + 4ζ`).

**Dissipative equations** (modules `Prep`, `Sources`, `ODESolver`, `ODEBudget`, `Nodes`).

* `selPrep hS η prepN`: the native preparation compiled selectively and placed on the released
  trial register (fresh flag and pool for the exact zero tests); the protocol is the released
  four-attempt protocol `GateNative.nprotocol` on it (the preparation, `j` Grover steps with the
  exact zero tests, the literal reverse-adjoint of the preparation as its inverse, the exact sign).
  `selPrep_valid`, `selPrep_counts`, `selPrep_pres`, `selPrep_approx` (within `η + δ` of the lifted
  released preparation when the native preparation is within `δ`), `trialSel_gateOf`
  (`AdjClosed 𝒢`, `zeroTestKinds ⊆ 𝒢`), `sel_protocol_worst`, `sel_protocol_worst_log` (worst-case
  counts over every history).
* `nSynN_omacro_le`, `nSynN_nprepC_le`, `nSynN_tnprepC_le`: with source circuits over an
  adjoint-closed `𝒢`, the synthesised occurrences of the native preparations are at most the gates
  of the same preparations with empty source circuits.
* `const_outcome_of`, `time_outcome_of`, `timeC_outcome_of`: the released correctness arguments for
  every compiled preparation that is valid, leaves the zero-test wires untouched and is within
  `ν/3 + δ` of the lifted released preparation.
* `native_ode_solver_sel` (constant coefficients), `native_ode_time_solver_sel` (time-dependent
  coefficients): valid trials over `𝒢`, the native counts, at most
  `K = prepGates + 84dC_J + 6dG_C` synthesised occurrences, and in every history at most
  `40g(G_src + K(c₁ log((K+1)/(ν/3)) + c₀ + 1)) + 20g(4n + 3)` gates (`80g`, `40g` for
  time-dependent coefficients), `G_src = |srcC 0| + |srcC 1|` (respectively `|loadC| + 2|wpC|`) the
  supplied source circuits charged once each, outside the logarithm, `n` the tested wires; the
  guarantees `GateNative.NOutcome` (every successful trial within `ε/500` of the normalised
  solution up to a global phase, success probability at least `2/3`, conditional output within
  trace distance `ε`) for every instance of the released native solvers.
  `native_time_sel_outcomeBI`, `native_time_sel_outcomeB`: the same protocol (its counts do not
  depend on the instance) has the guarantees on branch-dependent meshes for every positive source
  quadrature with the integrated certificate (`GateBinaryNodes.BInstanceOKI`) or the certificate
  of `GateSelect.ODE.BInstanceOK` (equation `ode:eq:gate-source-certificates`).
* `binary_ode_budget_sel` (equations `ode:eq:gate-main`, `ode:eq:gate-space` in `𝔟`, constant
  coefficients from binary sparse oracles): at most
  `40g(G_src + 2·10¹⁸q*(𝔟+1)³(64c₁(𝔟+1) + c₀ + 1)) + 20g(4(3·10¹¹(𝔟+1)³ + 2|Zs| + |Xa|) + 3)`
  gates of `𝒢`, at most `3932160 g q*` calls of each matrix oracle besides `40g` times the calls
  of the source circuits, and at most `7·10¹¹(𝔟+1)³ + 4|Zs| + 2|Xa|` qubits; `G_src` enters
  linearly and `A_src = |Zs|` through the zero tests and the register; the polynomial in `𝔟` does
  not depend on the source circuits. `binary_ode_time_budget_sel` (time-dependent coefficients,
  common mesh): the same with `80g`, `40g` in the gate bound,
  `G_src = |loadC| + 2|wpC|`, and at most `7864320 g q*` calls of each matrix oracle besides
  `80g` times the calls of `loadC` and of `wpC` (twice), `q*` taken at the solver's ratio `2g`
  and accuracy `ε/2`.
* `binary_nodes_solver_sel`, `binary_nodes_budget_sel`: the same for coherently computed source
  nodes (`GateEfficientBinaryNodes`), with `𝔟 + μ` and the node-program gates `|N|`:
  `80g(G_src + 2·10¹⁸q*((𝔟+μ+1)³ + |N|)(c₁(64(𝔟+μ+1) + log(|N|+1)) + c₀ + 1)) +
  40g(4(3·10¹¹(𝔟+μ+1)³ + 2|Zn| + 2|Zs| + |Xa|) + 3)` gates.

**Scope.** The supplied finite-set circuits, the source certificates and the loading and
weight-preparation circuits are hypotheses, as in the paper (`privSel` constructs the private
circuit from the native data). In the Hamiltonian endpoints the amplification reflections act on
the released wires only: the work wires of `pc` are covered by its full-output guarantee, so
`G₀` has no `A_C(ξ)` term and the qubit count has `|Z| + bT + bP + A + 3`. The endpoints of this
library use the released filter schedule; `GateEfficientSchedule` gives the Hamiltonian endpoints
with the manuscript's schedule `hs:eq:gate-schedule`, `hs:eq:gate-clocks` and `ξ = ε/(24d)`.
-/
