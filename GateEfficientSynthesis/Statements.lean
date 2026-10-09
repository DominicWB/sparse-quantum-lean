import GateEfficientSynthesis.Parts
import GateEfficientSynthesis.Binary
import GateEfficientSynthesis.ODESolver

/-!
# Synthesis over a finite gate set: paper-to-Lean entry point

Theorems `hs:thm:gates` and `ode:thm:gates` of the accompanying paper count gates over a finite gate
set. The gate-level circuits consist of elementary gates (one-qubit unitaries with at most three
literal controls, `GateOK 3`) and primitive oracle calls; the paper finally compiles every
elementary gate over a finite gate set admitting single-qubit synthesis of length `O(log(1/ζ))` at
accuracy `ζ`, after decomposing controlled known gates. The native forms of the two theorems
(`GateEfficientNative`) and the binary-data forms of `hs:thm:gates` (`GateEfficientBinary`,
`GateEfficientBinaryTime`) stop before this step. This library adds it. Single-qubit synthesis and
the decomposition of controlled gates are results from other papers; they enter only as explicit
hypotheses (`OneQubitSynthesis`, `ControlDecomposition`, combined in `Synthesis`). The released
libraries are unchanged. All declarations below are in the namespace `SparseHamiltonian.GateSynth`.
`ζ` is a synthesis accuracy in `Synthesis`, `exists_rep` and `synthC`; the endpoint theorems keep
the native name `ζ` for the accuracy of the angle arithmetic (as in `G_C` polynomial in `log(1/ζ)`).

* The synthesis hypothesis: `Synthesis 𝒢 X L`, derived from single-qubit synthesis and the
  exact decomposition of controlled gates by `Synthesis.of_parts` (logarithmic length:
  `of_parts_len_le`).
* The synthesis of a native circuit: `synthC`, `synthBudget` (`synthC_spec`, `synthC_approxOn`,
  `synthC_error`, `synthBudget_spec`, `synthBudget_error`, `gates_log_le`).
* Theorem `hs:thm:gates` over a finite gate set: `native_simulation_synth`,
  `native_simulation_signed_synth`, `native_time_simulation_synth`; from binary data:
  `binary_simulation_synth`, `binary_time_simulation_synth`; the budgets
  `binary_simulation_budget_synth`, `binary_time_simulation_budget_synth`.
* Theorem `ode:thm:gates` over a finite gate set: `native_ode_solver_synth`,
  `native_ode_time_solver_synth`, with the synthesised protocol `sprotocol` (`sprotocol_valid`,
  `sprotocol_worst`, `sprotocol_worst_log`, `soutcome`) and the perturbation of the
  four-attempt protocol `perturb_four`.

**Gate sets and the synthesis hypothesis** (`Hypothesis.lean`). A gate kind
`Kind = List Bool × Matrix Bool Bool ℂ` records the values of the control literals of a gate, in
order, and its one-qubit matrix; a gate set is a set `𝒢` of kinds. A gate `g` placed on any
wires is a gate of `𝒢`, `GateOf 𝒢 g`, if its control wires are distinct and its kind `kind g` is
in `𝒢` (validity, `GateOK 3`, keeps the controls off the target). `canon n p u` is the gate with
`n` controls of values `p` and the matrix `u` on its canonical wires `CW n = Fin n ⊕ Unit`.
`Synthesis 𝒢 X L` states that `𝒢` is finite and that for every `n ≤ 3`, every `p`, every
unitary `u` and every `ζ > 0` some list `gs` of at most `L ζ` valid gates of `𝒢` on the wires
`CW n ⊕ X` satisfies `ApproxOn CleanX (gRun gs) (liftB (canon n p u).op) ζ` for the payload `ℂ`:
on every input with the ancilla wires `X` zero, its output is within `ζ` times the input norm of
the output of the canonical gate with untouched ancillas, ancilla residues and phases included.

`Synthesis.of_parts` (`Parts.lean`): single-qubit synthesis `OneQubitSynthesis 𝒢 X₁ L` (the
case `n = 0`) and the exact decomposition `ControlDecomposition 𝒢 X₂ K` (every gate with at most
three controls acts on clean ancillas `X₂` exactly as a product of at most `K` valid gates, each
a gate of `𝒢` or without controls) give `Synthesis 𝒢 (X₂ ⊕ X₁) (ζ ↦ K (L(ζ/(K+1)) + 1))`. If
`L ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]`, this length is at most
`K c₁ log(1/ζ) + K (c₁ log(K+1) + c₀ + 1)` there (`of_parts_len_le`).

**One gate** (`Place.lean`, `Payload.lean`). `exists_rep`: under `Synthesis 𝒢 X L`, every valid
gate `g` on wires `V` (its controls on arbitrary wires, possibly repeated) is approximated within
every `ζ > 0` by at most `L ζ` valid gates of `𝒢` on `V ⊕ X`, in the same sense. Two literals of
different values on one wire never fire (`gateOp_conflict`, the empty list); repeated literals
are removed (`gateOp_dedup`); the canonical synthesis is renamed along the injective placement of
the canonical wires (`approxOn_place`). `approxOn_rep`: the bound proved for the payload `ℂ`
holds for every payload Hilbert space, because gate lists act on the configurations only
(`gateOp_eq_matOp`, `gRun_eq_matOp`, `approxOn_payload`).

**A circuit** (`Circuit.lean`, `Hamiltonian.lean`). `synthC hS ζ C` replaces every elementary
gate of the native circuit `C` by its synthesis at accuracy `ζ` (`synthRep`) and keeps every
primitive call on the native wires; it depends only on `C`. `synthC_spec`: valid instructions,
every gate a gate of `𝒢`, at most `nGatesN C · L ζ` gates and exactly the calls of `C` (for every
selection of oracle labels). `synthC_approxOn`: for unitary primitive oracles and every payload,
`ApproxOn CleanX (nrun prim (synthC hS ζ C)) (liftB (nrun prim C)) (nGatesN C · ζ)`; errors add
along the circuit (`approxOn_replace`). `synthC_error`: along every contractive system embedding
`E`, the full-output error grows by at most `nGatesN C · ζ`. The synthesis budget `ε'` is spent
uniformly: `synthBudget hS ε' C = synthC hS (ε'/(N+1)) C`, `N = nGatesN C`, adds at most `ε'` to
the error (`synthBudget_error`) and has at most `N L(ε'/(N+1))` gates (`synthBudget_spec`). If
`L ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]`, `c₀, c₁ ≥ 0` and `0 < ε' ≤ 1`, then
`N L(ε'/(N+1)) ≤ G (c₁ log((G+1)/ε') + c₀)` for every `G ≥ N` (`gates_log_le`).

**Theorem `hs:thm:gates` over a finite gate set.**

* `native_simulation_synth`, `native_simulation_signed_synth`, `native_time_simulation_synth`:
  under the hypotheses of `GateNative.native_simulation`, `native_simulation_signed` and
  `native_time_simulation`, `Synthesis 𝒢 X L` and `ε' > 0`, the synthesised native circuit
  consists of valid gates of `𝒢` and primitive calls, makes exactly `12 d` times the primitive
  calls of the compute circuit `V`, uses at most `N L(ε'/(N+1))` gates with the native gate count
  `N` bounded as in the native theorem, and its full output on the clean embedding
  `cleanEmb ∘ sysEmb io` (every qubit outside the system and every synthesis ancilla zero) is
  within `ε + ε'` of `exp(-iτH)`, of `exp(-itH)` for every real `t`, and of every propagator
  `U(t)` of the path, respectively. The first and the third also count the qubits (those of the
  native register and `|X|`), and the third gives a propagator of the path.
* `binary_simulation_synth`, `binary_time_simulation_synth`: the same, qubit counts included,
  for the binary-data circuits `GateBinary.binarySim` and `binaryTimeSim`, with `12 d` times `2`
  row, `2` column and `1` value calls.
* `binary_simulation_budget_synth`, `binary_time_simulation_budget_synth`: the rescaling `γ` of
  `binary_simulation_budget` (respectively `binary_time_simulation_budget`) is chosen from `s`, the
  time and `ε` before the gate set, the synthesis budget and the data, with the bounds of those
  theorems (`d ≤ 4608 q`; in the time-independent case also `τ' ≤ √s q` and the bounds on `2^m` and
  `2^r`). Then for every gate set with `L ζ ≤ c₁ log(1/ζ) + c₀`, every `0 < ε' ≤ 1` and every
  admissible instance, the synthesised circuit consists of valid gates of `𝒢` and primitive calls,
  makes at most `55296 q` times `2` row, `2` column and `1` value calls, uses at most
  `G (c₁ log((G+1)/ε') + c₀)` gates, where `G = 200 (4608 q + 1)(G_C + (σ+1) + (k+1) + m + r + 1)`
  is the pre-synthesis budget (`m = simM` in the time-independent case, the number of slot wires in
  the time-dependent case, which also gives `2^r ≤ 4 (4608 q + 1)` and a propagator of the path),
  and has full-output error at most `ε + ε'`. This is an upper bound of the form
  `G₀ log((G₀ + 1)/ε)` of equation `hs:eq:gate-total`, in which the gates of the native private
  calls (the term `d G_C(ξ)` of the paper) are synthesised together with the other gates; in the
  time-independent case, with `G_C` polynomial in the word lengths and in `log(1/ζ)` for the
  arithmetic accuracy `ζ`, it gives equation `hs:eq:gate-binary` after synthesis.

**Theorem `ode:thm:gates` over a finite gate set** (`ODE.lean`, `ODESolver.lean`,
`Perturb.lean`). The native four-attempt protocol `GateNative.nprotocol prepN g` draws a trial
count `j < chosenIterations g` and runs the native trial `trialN prepN j`. The synthesised
protocol `sprotocol hS η prepN g` is the released four-attempt wrapper with the trials
`synthBudget hS η (trialN prepN j)` on the native register and the synthesis ancillas, the seed
`sseed = cleanEmb sN` and the herald `sgood = cleanEmb ∘ goodN`; it depends only on the native
preparation, `g`, the synthesis hypothesis and `η`.

* `sprotocol_valid`: every synthesised trial consists of valid gates of `𝒢` and primitive calls.
* `sprotocol_worst`: in every history the protocol uses at most `4 B` elementary gates whenever
  `N_j L(η/(N_j+1)) ≤ B` for every trial (`N_j` the gates of the native trial `j`), and at most
  `40 g` times the primitive calls of the native preparation (the native bound).
* `sprotocol_worst_log`: if `L ζ ≤ c₁ log(1/ζ) + c₀` and `0 < η ≤ 1`, the protocol uses at most
  `(40 g N + 20 g (4 n + 3)) (c₁ log((G+1)/η) + c₀)` elementary gates in every history, where
  `N` counts the gates of the native preparation, `n` the wires tested by the seed reflection
  and `G = 10 g N + 5 g (4 n + 3)` bounds the gates of every native trial
  (`GateNative.ntrial_cost_bound`).
* `soutcome`: if the native protocol has its guarantees for an instance
  (`GateNative.NOutcome`: unitary trials, mean Born success at least `1/4` and phase-free
  direction error `ε/500` of the decoded trial amplitudes), the primitive oracles are unitary,
  `x ≠ 0` and `0 < η ≤ min(1/400, ε/20)`, then the synthesised protocol has the guarantees
  `SOutcome`: success probability at least `2/3`, and a conditional output that is a density
  operator within trace distance `ε` of `x/‖x‖`. Every decoded synthesised amplitude is within
  `η` of the native one (`strials_close`, from `synthC_approxOn`), and `perturb_four` applies:
  amplitudes of norm at most one moved by `η ≤ 1/400` keep the four-attempt success
  probability at least `2/3` (the mean Born success drops by at most `2η`), and the conditional
  output moves to trace distance at most `6 δ + 12 η` from the target when the unperturbed
  amplitudes have direction error `δ`. The perturbed amplitudes need no direction bound of their
  own: every branch is weighted by its Born probability (`branch_le`).
* `native_ode_solver_synth`, `native_ode_time_solver_synth`: the synthesised protocol with
  `η = ε/200`. Its trials consist of valid gates of `𝒢` and primitive calls; the counts of one
  native preparation are those of `native_ode_solver` (respectively `native_ode_time_solver`); in
  every history it makes at most the native bound on primitive calls and, with a logarithmic
  synthesis length, uses at most the native gate bound times `c₁ log((G + 1)/(ε/200)) + c₀` gates;
  it has the native qubits and `|X|`; and on every instance satisfying the hypotheses of the
  native theorem it succeeds with probability at least `2/3` with a conditional output within
  trace distance `ε` of the normalised solution.

Every theorem of the library is axiom-audited in `GateEfficientSynthesis/Audit.lean`.

**Formalisation choices.**

* The approximation convention of the hypothesis is the full-output convention of the native
  theorems: the operator norm on inputs with clean ancillas, ancilla residues and phases
  included (a gate is not identified with its multiples by a global phase). A gate set whose
  one-qubit matrices have determinants in a finite group (for example Clifford+T) therefore meets
  the hypothesis only with ancillas: without them the determinant of a gate list on one wire stays
  in that group.
* The hypothesis is stated for the payload `ℂ` (finite matrices) and transferred to every
  payload Hilbert space.
* Every elementary gate is synthesised separately, all of them on one reused ancilla register
  `X`, so the synthesised circuits have `|X|` more qubits than the native ones. The gates of the
  native private calls, of the arithmetic and of the reflections are synthesised like all others.
* A synthesis budget is spent uniformly over the gates of a circuit (`ε'/(N+1)` per gate). For
  `hs:thm:gates` the budget `ε'` is added to the native error `ε`; for `ode:thm:gates` the budget
  `ε/200` of every trial is absorbed in the native accuracy, since the native trials meet the
  direction error `ε/500`.
* A logarithmic synthesis length is the explicit hypothesis `L ζ ≤ c₁ log(1/ζ) + c₀` on
  `(0, 1]`; the gate bounds are stated in the closed form `G (c₁ log((G+1)/ε') + c₀)`.

**Not formalised.** Single-qubit synthesis over a finite gate set (for example the constructions
of Kliuchnikov, Maslov and Mosca and of Ross and Selinger) and the decomposition of controlled
gates (Barenco et al.): they are hypotheses. The per-trial statement of `ode:thm:gates` after
synthesis (every successful trial within `ε` up to a global phase): the paper amplifies one
synthesised preparation with reflections that are exact over the gate set, while here every gate
of a trial, the reflections included, is synthesised, and the output direction of a trial whose
native success amplitude is at most about `η` is not controlled (such a trial succeeds with
probability `O(η²)`); only the conditional mixed output is bounded. Theorem `ode:thm:gates` from
binary data.
-/
