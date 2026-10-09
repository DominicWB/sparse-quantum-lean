import GateEfficientRemarks.AbstractScalar
import GateEfficientRemarks.AbstractIsometry
import GateEfficientRemarks.AbstractBinary
import GateEfficientRemarks.QubitsSynth
import GateEfficientRemarks.ZeroSynthBinary
import GateEfficientBitBudget.NonVacuity
import GateEfficientRemarks.ODE.Poly
import GateEfficientRemarks.ODE.PolySynth
import GateEfficientRemarks.ODE.SynthZero
import GateEfficientRemarks.ODE.SynthCombined
import GateEfficientRemarks.ODE.SynthBinary
import GateEfficientRemarks.ODE.SynthBinaryTime
import GateEfficientRemarks.ODE.ZeroTrials
import GateEfficientRemarks.ODE.ZeroTrialsTime
import GateEfficientRemarks.ODE.ZeroReleasedTrialsTime
import GateEfficientRemarks.ODE.PolyNonneg
import GateEfficientRemarks.ODE.NonVacuity
import GateEfficientBinaryODE.Synth
import GateEfficientBinaryODETime.Synth

/-!
# Remarks on the gate-level theorems: paper-to-Lean entry point

This library formalises statements around Theorems `hs:thm:gates` (gate-efficient sparse
simulation, manuscript line 2866) and `ode:thm:gates` (gate-efficient dissipative equations,
lines 4447-4489) of the accompanying paper that the released gate-level libraries leave open. It
has two parts.

The Hamiltonian part (modules `GateEfficientRemarks/*.lean`, namespace
`SparseHamiltonian.GateRemarks`) formalises:

* Lemma `hs:lem:abstract` (the general boundary-resolvent simulation lemma, line 1964, with the
  interface `hs:eq:interface`, line 1907) under its own name, for every real time `t`;
* the auxiliary-qubit count of equation `hs:eq:gate-total` (line 2882) in the bit-length
  parameter of equation `hs:eq:gate-binary` (line 2896), for the binary-data constructions;
* the remark "At `t = 0` the identity circuit suffices" (lines 2909-2910) for the binary-data
  and finite-gate-set variants of `hs:thm:gates`.

The ODE part (modules `GateEfficientRemarks/ODE/*.lean`, namespace
`SparseHamiltonian.GateRemarks.ODE`) concerns Theorem `ode:thm:gates`, which bounds the complete
solver, in the word budget `𝔟 = b_data + log(N+1) + log(M+1) + log(m+1) + log((q ḡ+1)/ε)` of
equation `ode:eq:gate-word-budget` (line 4459), by `G_ODE ≤ C ḡ [q P(𝔟) + G_src(ν) + A_src(ν)]`
gates and `A_ODE ≤ P(𝔟) + C A_src(ν)` auxiliary qubits (equations `ode:eq:gate-main`,
`ode:eq:gate-space`, lines 4466-4472), and ends with two remarks (lines 4483-4488): "If the source
gate and work costs are polynomial in `𝔟`, the total gate bound is `ḡ q poly(𝔟)`", and "Zero time
or a known zero generator uses direct source assembly and needs no matrix calls."
The released library
`GateEfficientBitBudget` proves the two equations in `𝔟` with explicit constants for the solvers
from binary sparse data, with the source costs `G_src`, `|Zs|` as parameters and for `T > 0`,
`η_H + η_D > 0`; the released library `ZeroTimeGateODE` proves the second remark with explicit
worst-case counts (exact gates, native gates, binary data, finite gate sets with the per-trial
claim). This part of the library `GateEfficientRemarks` states, without results from other
papers:

* **A.** the first remark: if `G_src ≤ c (𝔟+1)^j` and `|Zs| ≤ c (𝔟+1)^j`, the gate bounds of the
  released budgets in `𝔟` and of their forms for every `T ≥ 0` (C) become `C g q* (𝔟+1)^(max j 3)`
  (one more power over a finite gate set) and the qubit bounds `C' (𝔟+1)^(max j 3)`, with
  explicit `C`, `C'` depending only on `c`, `j` (and the synthesis constants; over a finite gate
  set the released additive terms in the synthesis ancillas `|Xa|` are kept);
* **B.** the zero case of the four released finite-gate-set solvers that synthesise every trial,
  and their forms for every `T ≥ 0`;
* **C.** the zero case with the absolute constants of equations `ode:eq:gate-main` and
  `ode:eq:gate-space`: for binary data at `T = 0` or with zero energy bounds the direct source
  assembly meets the bounds of the released budgets in `𝔟` with the same constants, also over a
  finite gate set with the per-trial claim, on a minimal register and, for a rescaling `γ` of bit
  length `b_data`, on the released registers, where this gives the released budgets in `𝔟` for
  every `T ≥ 0` with every conclusion of the released endpoints.

The released libraries are unchanged. No result from another paper is used, except single-qubit
synthesis and the decomposition of controlled gates through the released hypothesis
`GateSynth.Synthesis` of the finite-gate-set forms. Manuscript lines refer to
`sparse_quantum_algorithms.tex` (v16); the labels are the stable references. Every theorem of the
library is axiom-audited in `GateEfficientRemarks/Audit.lean`.

## Hamiltonian part

**Naming convention.** The declarations of this part are in the namespace
`SparseHamiltonian.GateRemarks` and are named relative to it below. Released declarations are
named relative to `SparseHamiltonian` (for example `GateCircuit.Sim.simCircuit`,
`GateBinary.binarySim`, `GateSynth.synthBudget`, `GateBitBudget.bitH`,
`ZeroTimeRemarks.Gates.nativeCircuit`); `NativeSparseBlockEncoding`, `CayleyClockInterface`,
`TimeSchedule`, `ImprovedPrecisionBudget` and `SparseStateOverlap` are namespaces of the package
under `SparseHamiltonian`.

**What was already released (cited, not redone).**

* The content of Lemma `hs:lem:abstract` at gate level for `t ≥ 0`, with `J = U_J ι₀`:
  `GateCircuit.Sim.gate_efficient_simulation` (exact gates; circuit `GateCircuit.Sim.simCircuit`,
  exactly `6 d` private calls, error `ε` against `exp(-iτh)`,
  `d ≤ 128 (τ q̄ + Q (1 + log(3/ε)))`); at operator level, for an arbitrary isometry `J`, the
  Cayley-power implementation `SharpClockSimulation.exists_precise_implementation`.
* The binary-data constructions and their gate budgets: `GateBinary.binary_simulation`,
  `GateBinary.binary_simulation_budget`, `GateBinary.binary_time_simulation`,
  `GateBinary.binary_time_simulation_budget` (register sizes stated exactly); over a finite gate
  set `GateSynth.native_simulation_synth`, `GateSynth.native_simulation_signed_synth`,
  `GateSynth.native_time_simulation_synth`, `GateSynth.binary_simulation_synth`,
  `GateSynth.binary_time_simulation_synth`, `GateSynth.binary_simulation_budget_synth`,
  `GateSynth.binary_time_simulation_budget_synth`.
* The gate counts in the bit lengths: `GateBitBudget.binary_simulation_bits`,
  `GateBitBudget.binary_time_simulation_bits`, `GateBitBudget.binary_simulation_budget_synth_bits`,
  `GateBitBudget.binary_time_simulation_budget_synth_bits`, with the word lemmas
  `GateBitBudget.cordicWords_le`, `GateBitBudget.simM_word`, `GateBitBudget.simR_word`,
  `GateBitBudget.hs_gates_le`, `GateBitBudget.hs_gatesT_le` and the satisfiability of their
  hypotheses `GateBitBudget.hs_all_hyps`, `GateBitBudget.hsT_all_hyps`.
* The zero-time remark for the exact-gate and native circuits: `ZeroTimeRemarks.Gates.*`
  (`simulation_nonneg`, `time_simulation_nonneg`, `native_simulation_nonneg`,
  `native_simulation_signed_zero`, `native_time_simulation_nonneg`), with the combined native
  circuits `ZeroTimeRemarks.Gates.nativeCircuit`, `ZeroTimeRemarks.Gates.nativeCircuitSigned`,
  `ZeroTimeRemarks.Gates.nativeCircuitT` and the lemmas `ZeroTimeRemarks.Gates.exp_zero_time`,
  `ZeroTimeRemarks.Gates.identity_comp_error_eq_zero`,
  `ZeroTimeRemarks.Gates.identity_comp_error_le`, reused here.

**Endpoints of this part.**

* Lemma `hs:lem:abstract`: `abstract_simulation` (circuit `absCircuit`); for an arbitrary known
  isometry on a finite-dimensional system `abstract_simulation_isometry`
  (`exists_unitary_extension`); the Loewner form of the second moment
  `second_moment_iff` (`adjoint_comp_self_le_iff`); non-vacuity: the scalar instance with `h = 1`
  `abstract_simulation_scalar` and, from binary sparse data, `interface_binary`,
  `abstract_simulation_binary`.
* The qubits of `hs:eq:gate-total` in `𝔟_H`: `binary_simulation_bits_qubits`,
  `binary_time_simulation_bits_qubits`, `binary_simulation_budget_synth_bits_qubits`,
  `binary_time_simulation_budget_synth_bits_qubits`; the register formulas
  `card_binary_register`, `card_binary_registerT`; the register bounds `cordic_register_le`,
  `binary_register_le`, `binary_registerT_le`; the lower bounds behind the cubic degree
  `cordic_A_ge`, `nOf_ge`, `binArith_A_ge`.
* `hs:thm:gates` at zero time: circuits `binaryCircuit`, `binaryTimeCircuit`; endpoints
  `binary_simulation_nonneg`, `binary_simulation_budget_nonneg`, `binary_time_simulation_nonneg`,
  `binary_time_simulation_budget_nonneg`, `native_simulation_synth_nonneg`,
  `native_simulation_signed_synth_zero`, `native_time_simulation_synth_nonneg`,
  `binary_simulation_synth_nonneg`, `binary_time_simulation_synth_nonneg`,
  `binary_simulation_budget_synth_nonneg`, `binary_time_simulation_budget_synth_nonneg`; the
  lemma `synthBudget_nil`.

**Lemma `hs:lem:abstract`** (modules `AbstractTransfer`, `Abstract`, `AbstractScalar`,
`AbstractIsometry`, `AbstractBinary`). Model: the exact-gate model of
`GateEfficientHamiltonian/Statements.lean`. The system is any complex Hilbert space `P`; `U_J` and
the private operation `D` are supplied operators on `GateCircuit.Anc a P` (`a` ancilla qubits and
the system); `J = U_J ∘ ι₀` with `ι₀ = GateCircuit.Sim.iota0` (the system on the all-zero ancilla
word). A circuit is a list of `GateCircuit.Instr` on the wires `GateCircuit.Sim.SimWire a Q τ ν ε`:
elementary gates (a one-qubit unitary with at most three controls), calls of `U_J` or `U_J†` and
private calls of `D` or `D†`, each oracle call with at most one control (`GateCircuit.Instr.Valid`);
it runs as `GateCircuit.run (GateCircuit.Sim.simSem U_J D)`, with clean input `GateCircuit.Sim.io`
(every wire zero). Counts: `GateCircuit.nPriv` (private calls, inverse calls included),
`GateCircuit.nUJ`, `GateCircuit.nGates`. `d = GateCircuit.Sim.fDeg Q τ ν ε` is the filter degree,
`m = GateCircuit.Sim.simM τ ε` the slot exponent (`2^m` time slots) and
`r = GateCircuit.Sim.simR Q τ ν ε` the reuse-register size, for the time `τ = α|t|`.

* `absCircuit a α t Q ν ε`: `GateCircuit.Sim.simCircuit a (α|t|) Q ν ε` if `0 ≤ t`, and
  `flipDs` of it if `t < 0` (`flipDs` exchanges the private calls `D` and `D†`;
  `run_flipDs`: run with `D` it is the released circuit run with `D†`). It depends only on the
  public numbers.
* `abstract_simulation`. Hypotheses: `U_J`, `D` unitary (`OracleCircuit.IsUnitary`); `R₁` with
  `(1 - D) R₁ = 1` and `R₁ (1 - D) = 1`; `h` self-adjoint (`star h = h`) with `‖h‖ ≤ 1`; the
  interface `hs:eq:interface`: `J† R₁ J = (1 + i h)/2`, the compressed second moment
  `J† R₁† R₁ J ≤ ((ν/2 : ℝ) : ℂ) • 1` in Mathlib's Loewner order on `P →L[ℂ] P`
  (`ContinuousLinearMap.instLoewnerPartialOrder`: `A ≤ B` iff `B - A` is positive),
  `‖R₁‖ ≤ Q`, `1 ≤ Q`, `0 < ν ≤ Q`; `α > 0`; every real `t`; `0 < ε ≤ 1/2`. Guarantees, with
  `W = α|t|ν`: every instruction of `absCircuit a α t Q ν ε` is valid; `nPriv = 6 d` and
  `nPriv ≤ 3840 (W + Q log(1/ε))` (equation `hs:eq:abstractcost`); `nUJ = 12 d` and
  `nUJ ≤ 7680 (W + Q log(1/ε))`; `nGates ≤ 200 (d+1)(a+m+r+1)`; `2a + 3m + 6r + 3` qubit
  wires besides the system (the `a` ancilla wires included); the full output on clean inputs
  satisfies
  `‖run (simSem U_J D) (absCircuit …) ∘ io - io ∘ exp((-i t) • (α • h))‖ ≤ ε`;
  `d ≤ 128 (α|t| ν + Q (1 + log(1/(ε/3))))`, whose right-hand side does not involve the slots;
  the slots separately: `steps(α|t|, ε/3) ≤ 2^m < 2 steps(α|t|, ε/3)`
  (`TimeSchedule.steps`); and `2d + 2 ≤ 2^r ≤ 4 (d+1)`.
* `abstract_simulation_isometry`: for a finite-dimensional `P` (`[FiniteDimensional ℂ P]`, with
  the instance `[CompleteSpace P]` of the gate model) and an arbitrary isometry
  `J : P →L[ℂ] Anc a P`, `J† J = 1`, with the interface stated for `J` itself (`D` unitary, the
  inverse `R₁`, `h` self-adjoint with `‖h‖ ≤ 1`, `J† R₁ J = (1 + i h)/2`,
  `J† R₁† R₁ J ≤ (ν/2) • 1`, `‖R₁‖ ≤ Q`, `1 ≤ Q`,
  `0 < ν ≤ Q`, `α > 0`, `0 < ε ≤ 1/2`): there is a unitary `U_J` with `U_J ∘ ι₀ = J` for which
  all conclusions of `abstract_simulation` hold. `exists_unitary_extension`: every isometry
  `J : P → Anc a P` of a finite-dimensional `P` is `U_J ∘ ι₀` for a unitary `U_J`.
* `adjoint_comp_self_le_iff`: for Hilbert spaces `E`, `F`, `T : E →L[ℂ] F` and `c ≥ 0`,
  `T† ∘ T ≤ (c : ℂ) • 1 ↔ ‖T‖² ≤ c`. `second_moment_iff`: for `R : F →L[ℂ] F`,
  `J : E →L[ℂ] F` and `ν ≥ 0`, `J† ∘ R† ∘ R ∘ J ≤ ((ν/2 : ℝ) : ℂ) • 1 ↔ ‖R ∘ J‖² ≤ ν/2`: the
  paper's second moment is the released endpoint hypothesis `‖R₁ J‖ ≤ b`, `b² ≤ q̄/2`.
* `abstract_simulation_scalar` (non-vacuity with `h = 1`): `U_J = 1`, `D = i • 1`,
  `R₁ = ((1 + i)/2) • 1`, `h = 1`, `Q = ν = α = 1` meet every hypothesis of
  `abstract_simulation`, for every `a`, every system `P` and every real `t` (with `ε = 1/2`): the
  circuit `absCircuit a 1 t 1 1 (1/2)` is within `1/2` of `exp(-it)` with at most
  `3840 (|t| + log 2)` calls of `D` or `D†` (`smul_one_comp_smul_one`).
* `interface_binary` (non-vacuity): for binary sparse data as in `GateBinary.binary_simulation`
  (`NativeSparseBlockEncoding.Data`, `k`-bit indices `en`, `s = 2^σ` slots on the lowest `σ ≤ k`
  bits), an input whose matrix is Hermitian with row and column norms at most one, and
  `0 < γ ≤ 1`, the released operators `U_J = GateNative.UJop (GateBinary.hadUJ k σ hσ)`,
  `D = GateBinary.Dbin`, `R₁ = GateBinary.R1bin`, `h = GateBinary.Hbin` satisfy every hypothesis
  of `abstract_simulation` with `Q = CayleyClockInterface.width s γ = ⌈max(1, γ √s)⌉` (an integer)
  and `ν = CayleyClockInterface.moment γ = (1 + γ²)/2`, and `(√s/γ) • h` is the qubit lift
  `GateBinary.qlift en (SparseStateOverlap.matrixOperator H)` of the represented matrix (the
  paper's `α = η √s/γ` with `η = 1`). `abstract_simulation_binary`: the lemma for these
  operators: valid instructions, `6 d ≤ 3840 (α|t|ν + Q log(1/ε))` calls of `D` or `D†`,
  `12 d` calls of `U_J` or `U_J†`, and error `ε` against `exp(-itĤ)`, for every real `t`.

**The qubits of `hs:eq:gate-total` in the bit lengths** (modules `QubitWords`, `Qubits`,
`QubitsSynth`). Model: the binary-data constructions `GateBinary.binarySim` and
`GateBinary.binaryTimeSim` (native instruction lists on the wires
`GateNative.HW (SimWire (k+1) …) (Fin k) Empty (GateBinary.SZ k b) bT bP A`, the `k` system qubits
included), their synthesis `GateSynth.synthBudget` with the clean synthesis ancillas `Xa`, the
bit-length model `GateBitBudget.HasBits` and `𝔟_H = GateBitBudget.bitH b_data (2^k) q ε =
b_data + log₂(N+1) + log₂((q+1)/ε)` (`N = 2^k`).

* `binary_simulation_bits_qubits`: for `s ≥ 1`, `τ ≥ 0`, `0 < ε ≤ 1/2` and
  `q = ImprovedPrecisionBudget.shape s τ (log(1/ε)) = √s τ + √(s τ log(1/ε)) + log(1/ε)`, there is a
  rescaling `γ`, chosen before the data, with every property that
  `GateBitBudget.binary_simulation_bits` states, such that: for all data and accuracies as in
  `GateBitBudget.binary_simulation_bits` (`b ≤ b_data`, `HasBits b_data c₀`,
  `ε/(442368 q) ≤ ζ ≤ ε/(221184 q)`), the circuit `GateBinary.binarySim` has at most
  `10¹⁵ q (𝔟_H + 1)³` elementary gates and its register at most `4·10⁶ (𝔟_H + 1)³` qubits, the
  register size is exactly `k + (2(k+1) + 3m + 6r + 3) + (6k + 2b + bT + bP + A + 3)` (the formula
  of `GateBinary.binary_simulation`), and every other conclusion of
  `GateBitBudget.binary_simulation_bits` holds (private-operation gates at most `2·10⁹ (𝔟_H + 1)³`,
  at most `55296 q` times `2` row, `2` column and `1` value calls, the released gate count,
  full-output error at most `ε`).
* `binary_time_simulation_bits_qubits`: the same for `GateBitBudget.binary_time_simulation_bits`
  (`0 < ε ≤ 1`, `q = √s t + √(s t log(2/ε)) + log(2/ε)`, `M = 2^m` time slots, the path and mesh
  hypotheses), with at most `4·10⁶ (𝔟_H + log₂(M+1) + 1)³` qubits and every conclusion of
  `GateBitBudget.binary_time_simulation_bits` (`2^r ≤ 4 (4608 q + 1)`, the propagator, error `ε`).
* `binary_simulation_budget_synth_bits_qubits`,
  `binary_time_simulation_budget_synth_bits_qubits`: the same for the finite-gate-set forms
  `GateBitBudget.binary_simulation_budget_synth_bits` and
  `GateBitBudget.binary_time_simulation_budget_synth_bits` (`Synthesis 𝒢 Xa L`,
  `L ζ ≤ c₁ log(1/ζ) + c₀`, `0 < ε' ≤ 1`), with at most `4·10⁶ (𝔟_H + 1)³ + |Xa|`, respectively
  `4·10⁶ (𝔟_H + log₂(M+1) + 1)³ + |Xa|`, qubits, the exact register size plus `|Xa|`, and every
  conclusion of the released endpoints (gates of `𝒢` at most
  `10¹⁵ q (𝔟+1)³ (c₁ (36 (𝔟+1) + log(1/ε')) + c₀)`, validity, calls, error `ε + ε'`).
* `card_binary_register`, `card_binary_registerT`: the register formulas
  `k + (2(k+1) + 3m + 6r + 3) + (6k + 2b + bT + bP + A + 3)` hold for all parameters.
  `cordic_register_le`: `9k + 2b + bT + bP + A ≤ 13 u + 11 + 207 (u+1)³` for the CORDIC
  arithmetic `GateBinary.cordicArith` and `u = GateBitBudget.cordicWords k b κ ζ`;
  `binary_register_le`, `binary_registerT_le`: the register bounds under the hypotheses of
  `GateBitBudget.hs_gates_le`, respectively `GateBitBudget.hs_gatesT_le`.
* `cordic_A_ge`: the CORDIC workspace has `A ≥ 12 n³` wires for `n = GateBinary.Cordic.nOf ζ` steps;
  `nOf_ge`: `n ≥ log₂(8/ζ) + 2`; `binArith_A_ge`: for `0 < ζ`, `q ≥ 1/2`, `0 < ε ≤ 1` and
  `221184 q ζ ≤ ε` (the accuracy window of the endpoints), `A ≥ 12 (log₂(1/ε))³` for the arithmetic
  `GateBinary.binArith k b κ ζ` of the binary construction.

**Theorem `hs:thm:gates` at zero time** (modules `ZeroBinary`, `ZeroSynth`, `ZeroSynthBinary`;
the style of `ZeroTimeRemarks.Gates`). The combined circuits are the empty circuit at zero time
and the released circuit otherwise, on the same wires: `binaryCircuit k b σ hσ s γ c₀ τ ε ζ =
if τ = 0 then [] else GateBinary.binarySim …`, `binaryTimeCircuit k b m σ hσ s γ c₀ t ε ζ =
if t = 0 then [] else GateBinary.binaryTimeSim …`; the finite-gate-set forms synthesise the
combined native circuits, `GateSynth.synthBudget hS ε' C` for `C` one of
`ZeroTimeRemarks.Gates.nativeCircuit`, `ZeroTimeRemarks.Gates.nativeCircuitSigned`,
`ZeroTimeRemarks.Gates.nativeCircuitT`, `binaryCircuit`, `binaryTimeCircuit`, and the synthesis
of the empty circuit is empty (`synthBudget_nil`). Each combined form assumes exactly the
hypotheses of the released theorem and keeps every conclusion: counts that depend on the circuit
become `if <zero time> then 0 else <released count>` (calls with `=` or `≤` as released; the
synthesised gate count `if … then 0 else N L(ε'/(N+1))` with `N` the gate count of the released
native circuit; for the budget forms `if … then 0 else <released bound>`); conclusions that do
not depend on the circuit (qubit counts, the bound on the released native gate count `N`, degree
and register bounds, existence of a propagator) are unchanged; the full-output error is at most
`ε` (`ε + ε'` after synthesis), and a new conjunct states that it is exactly `0` at zero time.

* `binary_simulation_nonneg` (`GateBinary.binary_simulation`, every `τ ≥ 0`),
  `binary_simulation_budget_nonneg` (`GateBinary.binary_simulation_budget`; a rescaling `γ`
  chosen from `s`, `τ`, `ε` before the data, with the released bounds),
  `binary_time_simulation_nonneg` (`GateBinary.binary_time_simulation`, every `t ≥ 0`; error
  against every propagator `U` of the lifted path, `0` at `t = 0` since `U 0 = 1`),
  `binary_time_simulation_budget_nonneg` (`GateBinary.binary_time_simulation_budget`).
* `native_simulation_synth_nonneg` (`GateSynth.native_simulation_synth`, every `τ ≥ 0`),
  `native_simulation_signed_synth_zero` (`GateSynth.native_simulation_signed_synth`, every real
  `t`), `native_time_simulation_synth_nonneg` (`GateSynth.native_time_simulation_synth`, every
  `t ≥ 0`).
* `binary_simulation_synth_nonneg` (`GateSynth.binary_simulation_synth`),
  `binary_time_simulation_synth_nonneg` (`GateSynth.binary_time_simulation_synth`),
  `binary_simulation_budget_synth_nonneg` (`GateSynth.binary_simulation_budget_synth`) and
  `binary_time_simulation_budget_synth_nonneg` (`GateSynth.binary_time_simulation_budget_synth`),
  the budget forms with the released order of quantifiers (the rescaling before the gate set,
  the synthesis budget and the data).

**Proof map** (module paths relative to `GateEfficientRemarks/`).

* `AbstractTransfer`: the exchange of `D` and `D†` (`flipD`, `flipDs`, `isGate_flipD`,
  `isUJ_flipD`, `isPriv_flipD`, `run_flipDs`, `nPriv_flipDs`, `nUJ_flipDs`, `nGates_flipDs`,
  `valid_flipDs`); the interface of `D†` and
  `-h` with the inverse `1 - R₁`, from `resolvent_adjoint` (`R₁† = 1 - R₁` for unitary `D`):
  `transfer_unitary`, `transfer_right`, `transfer_left`, `transfer_norm`,
  `transfer_boundary`, `transfer_moment` (`((1 - R₁)J)†((1 - R₁)J) = (R₁J)†(R₁J)`),
  `transfer_endpoint`; the Loewner form `adjoint_comp_self_le_iff` (`re_inner_moment`) and
  `second_moment_iff`.
* `Abstract`: `one_add_log_le` (`1 + log(3/ε) ≤ 5 log(1/ε)` for `ε ≤ 1/2`, from
  `log 3 ≤ 2 log 2` and `log 2 > 1/2`), `abstract_cost_le` (`6 d ≤ 3840 (W + Q log(1/ε))`), the
  exponents `exponent_nonneg`, `exponent_neg`, and `abstract_simulation` from the released
  `GateCircuit.Sim.gate_efficient_simulation` (time `α|t|`, `b = ‖R₁ J‖`, `q̄ = ν`; for `t < 0`
  with `D†`, `1 - R₁`, `-h`).
* `AbstractScalar`: `smul_one_comp_smul_one` and `abstract_simulation_scalar` from
  `abstract_simulation` and `second_moment_iff` (`(1 - i) (1 + i)/2 = 1`, `|(1 + i)/2|² = 1/2`).
* `AbstractIsometry`: `exists_unitary_extension` (Mathlib's `LinearIsometry.extend` of
  `ι₀ p ↦ J p` on the range of `ι₀`, upgraded by `LinearIsometry.toLinearIsometryEquiv`; adjoint
  by `LinearIsometryEquiv.adjoint_eq_symm`), `abstract_simulation_isometry`.
* `AbstractBinary`: `interface_binary` from the released `GateBinary.R1bin_boundary`,
  `GateBinary.R1bin_endpoint` (with `CayleyClockInterface.endpoint_sq`),
  `GateBinary.norm_R1bin_le`, `GateBinary.norm_Hbin_le`, `GateBinary.Hbin_self`,
  `GateBinary.Dbin_isUnitary`, `GateBinary.one_sub_Dbin_R1bin`, `GateBinary.R1bin_one_sub_Dbin`,
  `GateNative.UJop_isUnitary`, `GateBinary.hadUJ_ok`, `GateBinary.Hbin_eq_smul`;
  `abstract_simulation_binary` from `interface_binary` and `abstract_simulation`.
* `QubitWords`: `card_binary_register`, `card_binary_registerT` from `GateNative.card_HW`,
  `GateCircuit.Sim.card_simWire`, `GateCircuit.Sim.card_wire` and `GateBinary.card_SZ`;
  `cordic_register_le` from `GateBinary.cordicArith_counts`, `GateBinary.params_fields` and
  `GateODEBudget.wordOf_le`; `binary_register_le`, `binary_registerT_le` from
  `GateBitBudget.cordicWords_le`, `GateBitBudget.cube_le`, `GateBitBudget.simM_word`,
  `GateBitBudget.simR_word`, `GateBitBudget.nat_le_logb` (`half_le_shape`); `cordic_A_ge` from
  the same counts, `nOf_ge` from the definition of `GateBinary.Cordic.nOf` (`Nat.le_pow_clog`),
  `binArith_A_ge` from both. `Qubits`, `QubitsSynth`: the endpoints from the
  released `GateBitBudget` endpoints, the register formulas and `Fintype.card_sum`.
* `ZeroBinary`, `ZeroSynth`, `ZeroSynthBinary`: case split on the zero-time condition; the
  released endpoint otherwise; at zero time `GateNative.nrun_nil`, `synthBudget_nil`,
  `ZeroTimeRemarks.Gates.exp_zero_time` and `ZeroTimeRemarks.Gates.identity_comp_error_eq_zero`.

Every theorem of this part is axiom-audited in `GateEfficientRemarks/Audit.lean`.

**Formalisation choices.**

* `hs:lem:abstract`: the known isometry is `J = U_J ι₀` with a supplied unitary `U_J`, as in the
  released gate model; for a finite-dimensional system every isometry has this form
  (`exists_unitary_extension`, `abstract_simulation_isometry`). `Q` is any real `Q ≥ 1`; the lemma's
  integer `Q` is a special case (the sparse instance has the integer `Q = ⌈max(1, γ √s)⌉`,
  `interface_binary`). The "calls to these unitaries" are the private calls (`GateCircuit.nPriv`,
  each a call of `D` or `D†` with at most one control, inverse calls counted); the calls of the
  known `U_J` and the elementary gates are counted separately, as in the released theorem. Negative
  times exchange `D` and `D†` in the released circuit (the interface of `D†` holds for `-h`), rather
  than taking the literal inverse circuit; both use only `D`, `D†` and their controls with the same
  counts. The error is the released full-output error, which bounds the operator-norm error of the
  simulation. The constant `3840` is explicit: the released degree bound
  `d ≤ 128 (W + Q (1 + log(3/ε)))` with `1 + log(3/ε) ≤ 5 log(1/ε)` for `ε ≤ 1/2`. The slot count
  `2^m ≥ steps(α|t|, ε/3) ≥ √(3 (α|t|)³/ε)` enters the wires and the gate count (through `m`) but
  neither `d` nor its bound.
* Qubits: the bound covers the whole register, the `k = log₂ N` system qubits included (the
  auxiliary qubits are `k` fewer); the payload `R` is an untouched reference and is not counted.
  The polynomial is cubic because the released CORDIC arithmetic has `1 + 2w + (6(n+1)+1) w ≥ 12 n³`
  work wires for `n` steps and width `w = 2n² + …`, and in the accuracy window of the endpoints
  `n ≥ log₂(8/ζ) + 2 ≥ log₂(1/ε)`; for fixed data `𝔟_H` grows like `log₂(1/ε)` as `ε → 0`, so no
  bound `C (𝔟_H + 1)²` holds for these circuits (a quadratic bound would need another
  arithmetic; `cordic_A_ge`, `binArith_A_ge`). The rescaling is existential, as in the released
  endpoints; `binary_register_le` and `binary_registerT_le` assume only properties that the
  released endpoints state for their rescaling, so the qubit bounds hold for the rescaling of
  every released endpoint as well.
  Logarithms in `𝔟_H` are base 2, as in `GateEfficientBitBudget` (natural logarithms change the
  constant by at most `(1/log 2)³ < 3.01`). The constants `4·10⁶` and `207` are explicit and
  generous.
* Zero time: as in `ZeroTimeRemarks.Gates`, the empty circuit runs on the released wires, the
  combined forms keep all released hypotheses (clock promises, arithmetic budgets, mesh
  conditions), which the empty circuit does not need, and the zero-time error is stated as an
  extra conjunct.

**Not formalised.**

* `hs:lem:abstract` for an isometry `J` into an infinite-dimensional private space that is not of
  the form `U_J ι₀` (in infinite dimension an isometry need not extend to a unitary); the lemma
  with approximate implementations of `D` (native or synthesised `D`; the native and
  finite-gate-set forms of the released gate-level theorems cover the sparse construction).
* Qubit bounds in `𝔟` for the native constructions whose arithmetic is a hypothesis
  (`GateEfficientNative`) and for floating-point parameters; a quadratic qubit bound, which fails
  for the released CORDIC arithmetic and would need another arithmetic (`cordic_A_ge`,
  `binArith_A_ge`).
* Negative times for the circuits built from binary sparse oracles (the released `GateBinary.*`
  endpoints are for `τ ≥ 0`; `abstract_simulation_binary` supplies `D` as a unitary).
* Private spaces other than `a` qubits and the system (a finite-dimensional private space reduces
  to this by extending `D₀` with `-1` on the complement and `R₁` with `1/2`).
* Zero-time forms of the bit-length endpoints (`GateBitBudget.binary_simulation_bits` and its
  variants) and of the certified and mesh endpoints of `GateEfficientMesh`; the combined circuits
  of this part apply to them in the same way, but those statements are not repeated.

**Provenance.** This part is new, written against the released package: it imports
`GateEfficientHamiltonian`, `GateEfficientNative`, `GateEfficientBinary`,
`GateEfficientBinaryTime`, `GateEfficientSynthesis`, `GateEfficientBitBudget` (with
`GateEfficientODEBudget`, for `GateODEBudget.wordOf_le`) and `ZeroTimeRemarks` and changes none
of them. The statement guide of `GateEfficientHamiltonian` lists negative times as not
formalised for the exact-gate theorem (the README records them as covered for native
implementations by `GateNative.native_simulation_signed`, with the literal inverse circuit;
`abstract_simulation` covers them in the exact-gate model itself, every real `t`); that of
`ZeroTimeRemarks` lists the zero-time forms of the binary-data and
finite-gate-set variants of `hs:thm:gates` (`GateBinary.*`, `GateSynth.*`) as not formalised; that
of `GateEfficientBitBudget` lists "the qubit count of `hs:thm:gates` in `𝔟`" as not formalised.
These entries are superseded here, within the scope stated above.

## ODE part

**Naming convention.** All declarations of this part are in the namespace
`SparseHamiltonian.GateRemarks.ODE` (modules `GateEfficientRemarks/ODE/…`) and are named relative
to it. Released declarations are named relative to `SparseHamiltonian` (for example
`GateBitBudget.binary_ode_budget_bits`, `ZeroTimeGateODE.zprepC`, `GateSynth.sprotocol`).

**What was already released (cited, not redone).** The budgets in `𝔟`:
`GateBitBudget.binary_ode_budget_bits`, `GateBitBudget.binary_ode_time_budget_bits`,
`GateBitBudget.binary_ode_time_budget_bits_user`, `GateBitBudget.binary_ode_budget_trials_bits`,
`GateBitBudget.binary_ode_time_budget_trials_bits` (with `GateBitBudget.bitB` the paper's `𝔟`
with base-2 logarithms and `GateODEBudget.qOf` the query shape `q*`), which keep every conclusion
of the explicit-constant budgets `GateODEBudget.binary_ode_budget`, `binary_ode_budget_words`,
`binary_ode_budget_trials` and their time-dependent forms (with the preparation bounds
`GateODEBudget.prepBound`, `prepBoundT`). The remark on zero time and a known zero generator: the
direct source assembly `ZeroTimeGateODE.zprepC (srcRot T r₀ r_b) srcC` and
`ZeroTimeGateODE.tzprepC loadC wpC` on every native register `ZeroTimeGateODE.ZNW …`, the
combined preparations `ZeroTimeGateODE.cprepC`, `ZeroTimeGateODE.ctprepC`,
`ZeroTimeGateODE.bprepC`, `ZeroTimeGateODE.btprepC`, the zero cases `ZeroTimeGateODE.ZeroCase`,
`TZeroCase`, `BZeroCase`, `BTZeroCase` and public conditions `PublicOK0`, `TPublicOK0`,
`BPublicOK0`, `BTPublicOK0`, the zero-case instance conditions `ZInstanceOK`, `TZInstanceOK` and
their derivation from the time-indexed binary data `binary_tzInstanceOK`, and the endpoints
`native_ode_solver_zero`, `native_ode_time_solver_zero`, `native_ode_solver_nonneg`,
`native_ode_time_solver_nonneg`, `binary_ode_solver_nonneg`, `binary_ode_time_solver_nonneg`,
`native_ode_solver_zero_trials`, `native_ode_time_solver_zero_trials`,
`binary_ode_solver_nonneg_trials`, `binary_ode_time_solver_nonneg_trials` (all in
`ZeroTimeGateODE`). The word bounds of the released budgets: `GateBitBudget.words_le`,
`GateBitBudget.wordsT_le` (for the public rescaling, positive case). The synthesis of every trial:
`GateSynth.sprotocol`, `GateSynth.sprotocol_valid`, `GateSynth.sprotocol_worst`,
`GateSynth.sprotocol_worst_log`, `GateSynth.soutcome`, `GateSynth.SOutcome` and the released
synthesised solvers `GateSynth.native_ode_solver_synth`, `GateSynth.native_ode_time_solver_synth`,
`GateBinaryODE.binary_ode_solver_synth`, `GateBinaryODETime.binary_ode_time_solver_synth`. The
witnesses of the positive case: `GateBitBudget.ode_all_hyps`, `GateBitBudget.ode_time_all_hyps`.

**Endpoints of this part.**

* A (modules `Poly`, `PolySynth`, `PolyNonneg`): `binary_ode_budget_poly`,
  `binary_ode_time_budget_poly`, `binary_ode_time_budget_poly_user`,
  `binary_ode_budget_trials_poly`, `binary_ode_time_budget_trials_poly` (from the released
  endpoints) and, for every `T ≥ 0`, `binary_ode_budget_poly_nonneg`,
  `binary_ode_time_budget_poly_nonneg`, `binary_ode_time_budget_poly_user_nonneg`,
  `binary_ode_budget_trials_poly_nonneg`, `binary_ode_time_budget_trials_poly_nonneg` (from the
  combined forms of C).
* B (modules `SynthZero`, `SynthCombined`, `SynthBinary`, `SynthBinaryTime`):
  `native_ode_solver_synth_zero`, `native_ode_time_solver_synth_zero` (zero case),
  `native_ode_solver_synth_nonneg`, `native_ode_time_solver_synth_nonneg` (every `T ≥ 0`),
  `binary_ode_solver_synth_zero`, `binary_ode_solver_synth_nonneg`,
  `binary_ode_time_solver_synth_zero`, `binary_ode_time_solver_synth_nonneg`.
* C (modules `MinRegister`, `ZeroBudget`, `ZeroBudgetTime`, `ZeroTrials`, `ZeroTrialsTime`):
  `binary_ode_budget_bits_zero`, `binary_ode_time_budget_bits_zero`,
  `binary_ode_budget_trials_bits_zero`, `binary_ode_time_budget_trials_bits_zero`; the minimal
  register `MinW` and its trial register `MinSW`.
* C on the released registers, every `T ≥ 0` (modules `ZeroWords`, `ZeroWordsSum`,
  `ZeroReleased`, `ZeroWordsT`, `ZeroReleasedTime`, `ZeroReleasedTrials`,
  `ZeroReleasedTrialsTime`): `binary_ode_budget_bits_zero_released`,
  `binary_ode_time_budget_bits_zero_released`, `binary_ode_budget_trials_bits_zero_released`,
  `binary_ode_time_budget_trials_bits_zero_released` (zero case) and
  `binary_ode_budget_bits_nonneg`, `binary_ode_time_budget_bits_nonneg`,
  `binary_ode_budget_trials_bits_nonneg`, `binary_ode_time_budget_trials_bits_nonneg` (every
  `T ≥ 0`); the explicit counts `binary_ode_budget_count_zero`,
  `binary_ode_time_budget_count_zero` and the preparation bounds `prepBound_le_zero`,
  `prepBoundT_le_zero` (zero case); the word bounds `zero_words_le`, `zero_wordsT_le`; the
  register identities `card_NW_eq`, `card_TNW_eq` (all public data).
* Satisfiability (module `NonVacuity`): `zero_all_hyps`, `zero_time_all_hyps`,
  `zero_instance_all_hyps`, `zero_instance_outcome`, with the data `zeroPub`, `zeroPubT`,
  `zeroPubZ`.
* Supporting: `nonneg_of_le_mul_pow`, `gates_absorb`, `space_absorb`, `log_succ_le`,
  `synth_factor_le`, `synth_absorb` (`Absorb`); `card_AW_min`, `card_XW_min`, `card_MinW`,
  `tested_min`, `card_MinSW`, `tested_minS`, `one_le_qOf`, `qOf_zero`, `logb_X_nonneg`,
  `kx_le_bitB`, `kx_add_le_bitB`, `log_le_bitB`, `log_trial_le`, `log_trialT_le`
  (`MinRegister`); `lin_le_cube`, `lin_le_cube_space` (`ZeroBudget`); `env_one_le`, `env_q_le`,
  `env_div_le`, `env_inv_precision_le`, `env_ell_le`, `env_ell_le_logb`, `env_radius_le`,
  `width_le_of`, `r_word_of`, `J_le_of`, `kap_words_of`, `hasBits_one`, `zero_TlamD`,
  `zero_TlamHD`, `zero_tau`, `zero_m`, `zero_k`, `zero_degree`, `width_le`, `zero_r_word`,
  `zero_J_le` (`ZeroWords`); `zero_kap_words`, `card_NW_le` (`ZeroWordsSum`); `count_arith`
  (`ZeroReleased`); `logBudget_two_le`, `bitB_le_succ`, `zeroT_TlamD`, `zeroT_tau`,
  `zeroT_degree`, `widthT_le`, `zeroT_r_word`, `zeroT_J_le`, `zeroT_kap_words`, `card_TNW_le`
  (`ZeroWordsT`); `count_arithT` (`ZeroReleasedTime`); `trial_budget_le`, `card_trial_released`,
  `trial_count_le`, `zero_gates_le_prepBound` (`ZeroReleasedTrials`); `card_trialT_released`,
  `zero_gates_le_prepBoundT` (`ZeroReleasedTrialsTime`); `zeroPub_ok0`, `zeroPub_zero`,
  `zeroPubT_mesh`, `zeroPubT_ok0`, `zeroPubT_zero`, `zeroPubZ_q`, `zeroPubZ_nu`, `zeroPubZ_spec`,
  `zeroPubZ_ok0`, `approx_empty` (`NonVacuity`).

**Model** (those of `GateEfficientNative/Statements.lean`, `GateEfficientSynthesis/Statements.lean`,
`GateEfficientSynthesisTrials/Statements.lean`, `GateEfficientBitBudget/Statements.lean` and
`ZeroTimeGateODE/Statements.lean`). A native circuit is a list of `GateNative.NInstr`;
`GateNative.nGatesN C` (`|C|`) counts its elementary gates and `GateNative.nCallsN c C`
(`calls_c(C)`) its primitive calls of the kinds selected by `c`. `GateNative.nprotocol prepN g`
is the released four-attempt protocol around the preparation `prepN` (trials
`GateNative.trialN prepN j`); `worstCost GateNative.wGateN` and `worstCost (GateNative.wCallN c)`
are its worst-case gates and calls over every history, including four failures;
`GateNative.NOutcome` its guarantees (unitary trials, mean success at least `1/4`, every
successful trial within `ε/500` of the normalised target up to a global phase, success at least
`175/256 > 2/3`, conditional output within trace distance `ε`). Every trial synthesised:
`GateSynth.sprotocol hS (ε/200) prepN g` runs `GateSynth.synthBudget hS (ε/200) (trialN prepN j)`
(every gate of the trial compiled over the finite gate set `𝒢` under `GateSynth.Synthesis 𝒢 X len`)
on the register with the synthesis ancillas `X` added; `GateSynth.GateOf 𝒢` states that a gate
is a gate of `𝒢` on distinct wires; `GateSynth.SOutcome P ε prim x`: success probability at least
`2/3` and a conditional output density within trace distance `ε` of `x/‖x‖` (no claim about
single trials). Per-trial claim: `GateSynthTrials.synthPrep hS (ν/3) prepN` synthesises only the
preparation, on the trial register `GateSynthTrials.SWO` (with `AdjClosed 𝒢` and
`zeroTestKinds ⊆ 𝒢`). `c₀, c₁ ≥ 0` denote the synthesis constants of
`len ζ ≤ c₁ log(1/ζ) + c₀` (not the decoder scale). Throughout `q* = GateODEBudget.qOf s T η_H η_D
g ε`, `ℓ = ImprovedODEQueryBudget.logBudget g ε = log(10⁴ g/ε)`, `ν = ε/(10⁴ g)` (the released
`q.params.nu`; for time-dependent data `ν = (ε/2)/(10⁴ · 2g)`), and `bitB b_data N M m_src Q g ε =
b_data + log₂(N+1) + log₂(M+1) + log₂(m_src+1) + log₂((Q g + 1)/ε)` (`GateBitBudget.bitB`).

**A. Source costs polynomial in `𝔟`** (`Poly`, `PolySynth`, `PolyNonneg`). For constant
coefficients `G_src = |srcC false| + |srcC true|` and `𝔟 = bitB b_data (2^k_x) (2^m) (2^k) q* g ε`
(`m = q.params.m`, `k = q.params.k`); for time-dependent coefficients `G_src = |loadC| + 2 |wpC|`,
the internal `q*' = qOf s T η_H η_D (2g) (ε/2)` and `𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε`,
or the user's `q*` and `𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε`. In each corollary the
hypotheses are exactly those of the endpoint it follows from plus, for a real `c` and `j : ℕ`,
`G_src ≤ c (𝔟+1)^j` and `|Zs| ≤ c (𝔟+1)^j` (then `c ≥ 0`, `nonneg_of_le_mul_pow`); `J = max j 3`.

* `binary_ode_budget_poly` (from `GateBitBudget.binary_ode_budget_bits`: `q.OK`, the public
  rescaling `q.γ = gammaOf T η_H η_D g ε`, `ν ≤ 196608 q* ζ`, `b ≤ b_data`, `HasBits b_data` of
  `c₀`, `T`, `η_H`, `η_D`, the binary data `D`, `en`, `hrange`, `hdec`, valid source circuits
  `srcC`): the protocol `GateNative.nprotocol (q.prep srcC) g` uses at most
  `10²⁰ (1 + 2c) g q* (𝔟+1)^J` elementary gates in every history, and the register
  `GateNative.NW q.params (Fin k_x) Zs (SZ4 k_x b) bT bP A` has at most
  `(3·10¹¹ + 2c) (𝔟+1)^J` qubits.
* `binary_ode_time_budget_poly` (from `GateBitBudget.binary_ode_time_budget_bits`, internal
  `q*'`, `𝔟'`): at most `2·10²⁰ (1 + 2c) g q*' (𝔟'+1)^J` gates for the protocol of
  `q.prep loadC wpC` with ratio `2g`, at most `(3·10¹¹ + 2c) (𝔟'+1)^J` qubits of
  `GateNative.TNW q.params …`.
* `binary_ode_time_budget_poly_user` (from `GateBitBudget.binary_ode_time_budget_bits_user`,
  hypotheses in the user's `𝔟`): at most `2·10²² (1 + 2c) g q* (𝔟+1)^J` gates and
  `(9·10¹² + 2c) (𝔟+1)^J` qubits.
* `binary_ode_budget_trials_poly` (from `GateBitBudget.binary_ode_budget_trials_bits`: the
  hypotheses of `binary_ode_budget_bits`, `Synthesis 𝒢 Xa len`, `AdjClosed 𝒢`,
  `zeroTestKinds ⊆ 𝒢`, `len ζ ≤ c₁ log(1/ζ) + c₀`): the protocol
  `nprotocol (synthPrep hS (ν/3) (q.prep srcC)) g` uses at most
  `[40 (2·10¹⁸ + c) (c₁ (64 + j + c) + c₀) + 20 (12·10¹¹ + 8c + 3)] g q* (𝔟+1)^(J+1) +
  80 g |Xa|` gates of `𝒢`, and the register `GateSynthTrials.SNW …` has at most
  `(7·10¹¹ + 4c) (𝔟+1)^J + 2 |Xa|` qubits.
* `binary_ode_time_budget_trials_poly` (from `GateBitBudget.binary_ode_time_budget_trials_bits`,
  internal `q*'`, `𝔟'`): at most
  `[80 (2·10¹⁸ + c) (c₁ (64 + j + c) + c₀) + 40 (12·10¹¹ + 8c + 3)] g q*' (𝔟'+1)^(J+1) +
  160 g |Xa|` gates, at most `(7·10¹¹ + 4c) (𝔟'+1)^J + 2 |Xa|` qubits of
  `GateSynthTrials.STW …`.
* For every `T ≥ 0`: `binary_ode_budget_poly_nonneg`, `binary_ode_time_budget_poly_nonneg`,
  `binary_ode_time_budget_poly_user_nonneg`, `binary_ode_budget_trials_poly_nonneg`,
  `binary_ode_time_budget_trials_poly_nonneg` (from the combined forms
  `binary_ode_budget_bits_nonneg`, `binary_ode_time_budget_bits_nonneg` (its gate and qubit bounds
  in `𝔟'`, resp. in the user's `𝔟`), `binary_ode_budget_trials_bits_nonneg`,
  `binary_ode_time_budget_trials_bits_nonneg` of C, under their hypotheses: `BPublicOK0 q`,
  resp. `BTPublicOK0 q`, `γ` of bit length `b_data` in the zero case and the public rescaling
  otherwise): the same bounds with the same constants for the protocols of `bprepC q srcC`,
  `btprepC q loadC wpC`.
* The arithmetic (`Absorb`): `gates_absorb` (`K g (Q Y³ + G + Z) ≤ K (1 + 2c) g Q Y^J` for
  `Q, Y ≥ 1`, `G, Z ≤ c Y^j`), `space_absorb` (`P Y³ + a Z ≤ (P + a c) Y^J`), `log_succ_le`
  (`log(G + 1) ≤ c + j Y` for `0 ≤ G ≤ c Y^j`), `synth_factor_le`
  (`c₁ (64 Y + log(G + 1)) + c₀ ≤ (c₁ (64 + j + c) + c₀) Y`) and `synth_absorb` (the
  finite-gate-set form); `q* ≥ 1` is the released `GateODEBudget.ShapeOK.one_le_q` for `T > 0`
  and `one_le_qOf` for every `T ≥ 0`.

**B. Zero time or a known zero generator, every trial synthesised** (`SynthZero`,
`SynthCombined`, `SynthBinary`, `SynthBinaryTime`). The synthesis budget is `ε/200` per trial,
as in the released synthesised solvers; with `len ζ ≤ c₁ log(1/ζ) + c₀` the gate bound is
`(40 g' N + 20 g' (4 n + 3)) (c₁ log((10 g' N + 5 g' (4 n + 3) + 1)/(ε/200)) + c₀)` (`g' = g`, or
`2g` for time-dependent coefficients; `N` the gates of the preparation, `n` the wires tested by
the zero tests: `|AW| + |XW| + |Zs| + |S|`, for binary data `|W| + |XW| + |Zs| + k_x`).

* `native_ode_solver_synth_zero`: for `T ≥ 0`, `g ≥ 1`, `0 < ε ≤ 1/2`, `r₀, r_b ≥ 0`,
  `r₀ + T r_b > 0`, valid source circuits, `Synthesis 𝒢 X len`, on every native register
  `ZeroTimeGateODE.ZNW a m r K k l f S Zs Z bT bP A` (`⊕ X`), the protocol
  `GateSynth.sprotocol hS (ε/200) (zprepC (srcRot T r₀ r_b) srcC) g`: every synthesised trial
  consists of valid gates of `𝒢` and primitive calls; `|zprepC …| = |srcC 0| + |srcC 1| + 2` and
  `calls_c(zprepC …) = calls_c(srcC 0) + calls_c(srcC 1)` for every kind `c`; in every history at
  most `40 g (calls_c(srcC 0) + calls_c(srcC 1))` calls, and none of a kind that the source
  circuits do not call; the gate bound above with `N = |srcC 0| + |srcC 1| + 2`; the qubits
  `|S| + 2 (|AW| + (|Z| + bT + bP + A + 3) + |Zs|) + |S| + 1 + |X|`; and, under the hypotheses of
  `ZeroTimeGateODE.native_ode_solver_zero` (unitary primitive oracles and source interfaces,
  source circuits within `ζs` of `GateNative.srcIdeal`, `2 ζs ≤ ν`, `‖x₀‖ = r₀`, `‖b‖ = r_b`, the
  seed promises, `x₀ + T b ≠ 0`, `r₀ + T r_b ≤ g ‖x₀ + T b‖`), `GateSynth.SOutcome` against
  `x₀ + T b`.
* `native_ode_time_solver_synth_zero`: for `p : GateODE.Time.TParams` with `T ≥ 0`, `g ≥ 1`,
  `0 < ε ≤ 1/2`, `λ_H, λ_D ≥ 0`, `T = 0 ∨ λ_H + R λ_D = 0`, valid `loadC`, `wpC`, on every
  `ZNW a m r K p.m l f …` (`⊕ X`), the protocol `sprotocol hS (ε/200) (tzprepC loadC wpC) (2g)`:
  the same conclusions with `N = |loadC| + 2 |wpC|`, calls `calls_c(loadC) + 2 calls_c(wpC)`, at
  most `40 · 2g` times these, and `SOutcome` against `x(T)` under `3 ζs ≤ ν` and `TZInstanceOK`
  (the hypotheses of `ZeroTimeGateODE.native_ode_time_solver_zero`).
* `native_ode_solver_synth_nonneg`: for `p : GateODE.Params` with `PublicOK0 p` and the released
  public native data (`UJg` with `GateOK 3`, a public `nd`, `ar` with `ArithOK` at accuracy
  `ζ ≥ 0`, valid source circuits), the protocol `sprotocol hS (ε/200) (cprepC p UJg nd ar srcC) g`
  on `GateNative.NW p … ⊕ X`: the conclusions of the released `GateSynth.native_ode_solver_synth`
  with `|cprepC …| ≤ if ZeroCase p then |srcC 0| + |srcC 1| + 2 else p.prepGates +
  84 d |UJg| + 6 d privGates nd ar + |srcC 0| + |srcC 1|` and
  `calls_c(cprepC …) ≤ if ZeroCase p then calls_c(srcC 0) + calls_c(srcC 1) else
  12 d calls_c(nd.V) + calls_c(srcC 0) + calls_c(srcC 1)`, worst-case calls at most
  `40 g calls_c(cprepC …)`, the gate bound with `N = |cprepC …|`, the released qubits plus `|X|`,
  and `SOutcome` against `p.target H L x₀ b` under `2 ζs ≤ ν ∧ ZInstanceOK …` if `ZeroCase p` and
  under `NativeOK ∧ 24 d ζ + 2 ζs ≤ ν ∧ p.InstanceOK …` otherwise.
* `native_ode_time_solver_synth_nonneg`: the same for `TPublicOK0 p`, `ctprepC`, ratio `2g`, the
  counts with `|loadC| + 2 |wpC|`, and the case-dependent hypotheses
  `3 ζs ≤ ν ∧ TZInstanceOK …` / `NativeOK ∧ 24 d ζ + 3 ζs ≤ ν ∧ p.InstanceOK …`, against `x(T)`.
* `binary_ode_solver_synth_zero`: for `q : GateBinaryODE.Pub` with `BPublicOK0 q` and
  `BZeroCase q`, the binary data `D`, `en` and valid source circuits, the protocol
  `sprotocol hS (ε/200) (bprepC q srcC) g` on the released binary register `⊕ Xa`: valid
  synthesised trials of `𝒢`; `|bprepC q srcC| = |srcC 0| + |srcC 1| + 2`, exact calls; at most
  `40 g (calls_c(srcC 0) + calls_c(srcC 1))` calls of every kind `c` of the binary sparse oracles,
  none of a kind that the source circuits do not call; the gate bound; the released qubits plus
  `|Xa|`; and for every input with the row energy promises, unitary source interfaces, sources
  within `ζs`, `2 ζs ≤ ν`, the public norms, the seed promises, `x(T) ≠ 0` and
  `r₀ + T r_b ≤ g ‖x(T)‖`: `SOutcome` against the solution `x(T)` of `x' = -M̂ x + b`
  (`= x₀ + T b`, `ZeroTimeGateODE.binary_target_zero`).
* `binary_ode_solver_synth_nonneg`: for `BPublicOK0 q` and the hypotheses of the released
  `GateBinaryODE.binary_ode_solver_synth` (`hrange`, `hdec`): its conclusions for the protocol of
  `bprepC q srcC` with the counts of `ZeroTimeGateODE.binary_ode_solver_nonneg`
  (`if BZeroCase q then … else <released>`), and `SOutcome` under the released hypotheses on the
  input and the sources (`24 d ζ + 2 ζs ≤ ν`).
* `binary_ode_time_solver_synth_zero`, `binary_ode_time_solver_synth_nonneg`: the same for
  `q : GateBinaryODETime.PubT` with `BTPublicOK0 q`, `btprepC`, ratio `2g`; in the zero case
  `SOutcome` against `x(T)` under the energy and accretivity promises of every sample, circuits
  within `ζs`, `3 ζs ≤ ν` and `PubT.Rest` (through `ZeroTimeGateODE.binary_tzInstanceOK`); for
  every `T ≥ 0` under the released hypotheses (`24 d ζ + 3 ζs ≤ ν`, `PubT.Rest`).

**C. Zero time or a known zero generator with the absolute constants** (`MinRegister`,
`ZeroBudget`, `ZeroBudgetTime`, `ZeroTrials`, `ZeroTrialsTime`). The register is
`MinW k k_x Zs = ZeroTimeGateODE.ZNW 0 0 0 0 k 0 0 (Fin k_x) Zs Empty 0 0 0`: the native register
of `ZeroTimeGateODE` without simulator, LCHS, private-operation and arithmetic wires, that is the
sector wire `sec`, the source-label wire `ini` and the flags `hf`, `lf`, `flg` of the released wire
types with zero parameters, `k` source-label bits (`k = 0` for constant coefficients, the mesh
bits `m` for time-dependent coefficients), three native flags, the system `Fin k_x`, the source
scratch `Zs`, the native flag and the released pool of the zero tests:
`2 k_x + 2 k + 2 |Zs| + 17` qubits (`card_MinW`), `k + k_x + |Zs| + 8` tested wires
(`tested_min`). Its trial register `MinSW k k_x Zs Xa` (`GateSynthTrials.SWO` of it) has
`4 k_x + 4 k + 4 |Zs| + 2 |Xa| + 35` qubits (`card_MinSW`) and `2 k + 2 k_x + 2 |Zs| + |Xa| + 17`
tested wires (`tested_minS`). In the zero case `q* = ℓ` (`qOf_zero`) and `q* ≥ 1` for all
`T, η ≥ 0` (`one_le_qOf`); `k_x ≤ 𝔟`, `k_x + m ≤ 𝔟` (`kx_le_bitB`, `kx_add_le_bitB`).

* `binary_ode_budget_bits_zero`: for `q : Pub` with `BPublicOK0 q` and `BZeroCase q`, the binary
  data `D`, `en`, valid source circuits, every `b_data` and every `M`, `m_src`, with
  `𝔟 = bitB b_data (2^k_x) M m_src q* g ε`, the protocol
  `GateNative.nprotocol (zprepC (srcRot T r₀ r_b) srcC) g` on `MinW 0 k_x Zs`: at most
  `10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` gates in every history and at most
  `3·10¹¹ (𝔟+1)³ + 2 |Zs|` qubits (the bounds of `GateBitBudget.binary_ode_budget_bits`, with the
  released `M = 2^m`, `m_src = 2^k` among the admissible choices); at most
  `780 g [q* (𝔟+1) + G_src + |Zs|]` gates and `17 (𝔟+1) + 2 |Zs|` qubits; `q* = ℓ`; at most
  `40 g (G_src + 2) + 20 g (4 (k_x + |Zs| + 8) + 3)` gates and exactly `2 k_x + 2 |Zs| + 17`
  qubits; valid trials; at most `40 g (calls_c(srcC 0) + calls_c(srcC 1))` calls of every kind
  `c`, and none of a kind that the source circuits do not call; and `GateNative.NOutcome` against
  the solution `x(T)` of `x' = -M̂ x + b` under the row energy promises, unitary source interfaces,
  sources within `ζs`, `2 ζs ≤ ν`, the public norms, the seed promises, `x(T) ≠ 0` and
  `r₀ + T r_b ≤ g ‖x(T)‖`.
* `binary_ode_time_budget_bits_zero`: for `q : PubT` with `BTPublicOK0 q` and `BTZeroCase q`,
  valid `loadC`, `wpC`, every `b_data`, the protocol `nprotocol (tzprepC loadC wpC) (2g)` on
  `MinW m k_x Zs` (`m = q.params.m = q.m`): with the internal `q*'` and
  `𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε` at most `2·10²⁰ g [q*' (𝔟'+1)³ + G_src + |Zs|]`
  gates and `3·10¹¹ (𝔟'+1)³ + 2 |Zs|` qubits (the bounds of
  `GateBitBudget.binary_ode_time_budget_bits`); with the user's `q*` and
  `𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε` at most `2·10²² g [q* (𝔟+1)³ + G_src + |Zs|]` gates
  and `9·10¹² (𝔟+1)³ + 2 |Zs|` qubits (those of `binary_ode_time_budget_bits_user`), and at most
  `1400 g [q* (𝔟+1) + G_src + |Zs|]` gates and `17 (𝔟+1) + 2 |Zs|` qubits; `q* = ℓ`; at most
  `80 g G_src + 40 g (4 (m + k_x + |Zs| + 8) + 3)` gates and exactly `2 k_x + 2 m + 2 |Zs| + 17`
  qubits; valid trials; at most `80 g (calls_c(loadC) + 2 calls_c(wpC))` calls, none of a kind that
  the supplied circuits do not call; and `NOutcome` against `x(T)` under the energy and accretivity
  promises of every sample, circuits within `ζs`, `3 ζs ≤ ν` and `PubT.Rest`.
* `binary_ode_budget_trials_bits_zero`: under `Synthesis 𝒢 Xa len`, `AdjClosed 𝒢`,
  `zeroTestKinds ⊆ 𝒢`, `len ζ ≤ c₁ log(1/ζ) + c₀` and the hypotheses of
  `binary_ode_budget_bits_zero`, the protocol
  `nprotocol (synthPrep hS (ν/3) (zprepC (srcRot T r₀ r_b) srcC)) g` on `MinSW 0 k_x Zs Xa`: at
  most `40 g (2·10¹⁸ q* (𝔟+1)³ + G_src) (c₁ (64 (𝔟+1) + log(G_src+1)) + c₀) +
  20 g (4 (3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢` and `7·10¹¹ (𝔟+1)³ + 4 |Zs| + 2 |Xa|`
  qubits (the bounds of `GateBitBudget.binary_ode_budget_trials_bits`); at most
  `40 g N (c₁ log((N+1)/(ν/3)) + c₀) + 20 g (4 (2 k_x + 2 |Zs| + |Xa| + 17) + 3)` gates
  (`N = G_src + 2`) and exactly `4 k_x + 4 |Zs| + 2 |Xa| + 35` qubits; `q* = ℓ`; every trial of
  valid gates of `𝒢` and primitive calls; the calls as above; `NOutcome` (with the per-trial
  claim) under the zero-case conditions of `binary_ode_budget_bits_zero`.
* `binary_ode_time_budget_trials_bits_zero`: the same for time-indexed data on
  `MinSW m k_x Zs Xa`, ratio `2g`: at most
  `80 g (2·10¹⁸ q*' (𝔟'+1)³ + G_src) (c₁ (64 (𝔟'+1) + log(G_src+1)) + c₀) +
  40 g (4 (3·10¹¹ (𝔟'+1)³ + 2 |Zs| + |Xa|) + 3)` gates and `7·10¹¹ (𝔟'+1)³ + 4 |Zs| + 2 |Xa|`
  qubits (`GateBitBudget.binary_ode_time_budget_trials_bits`); at most
  `80 g G_src (c₁ log((G_src+1)/(ν/3)) + c₀) + 40 g (4 (2 m + 2 k_x + 2 |Zs| + |Xa| + 17) + 3)`
  gates on exactly `4 k_x + 4 m + 4 |Zs| + 2 |Xa| + 35` qubits; `q*' = log(4·10⁴ g/ε)`; calls;
  `NOutcome` against `x(T)` under the zero-case conditions of `binary_ode_time_budget_bits_zero`.
* The synthesis factor (`log_le_bitB`, `log_trial_le`, `log_trialT_le`): with `N = G_src + 3`
  (resp. `G_src + 1`), `log(N/(ν/3)) ≤ 64 (𝔟+1) + log(G_src+1)` for every `Q ≥ 1` in `𝔟`; the
  linear-to-cubic steps `lin_le_cube`, `lin_le_cube_space`.

**C on the released registers, every `T ≥ 0`** (`ZeroWords`, `ZeroWordsSum`, `ZeroReleased`,
`ZeroWordsT`, `ZeroReleasedTime`, `ZeroReleasedTrials`, `ZeroReleasedTrialsTime`). The released
budgets in `𝔟` rest on the word bounds `GateBitBudget.words_le`, `wordsT_le`
(`𝔴 + ℓ ≤ 300 (𝔟+1)`, `𝔴` the sum of the register words), proved for the public rescaling
`γ = gammaOf T η_H η_D g ε`, which is `0` in the zero case. In the zero case the common time
`τ` vanishes, so the time and quadrature words vanish (`zero_m`, `zero_k`), the filter degree is
`d ≤ 128 Q_w (1 + log(3/ν))` with the clock width `Q_w ≤ 3 · 2^k_x` (`zero_degree`, `width_le`),
the LCHS grid has `J ≤ 60 ℓ²` (`zero_J_le`), and with `γ` of bit length `b_data`
(`GateBitBudget.HasBits b_data γ`, so `γ⁻¹ ≤ 2^b_data`) the decoder words are bounded
(`zero_kap_words`); hence the word bound with the same constant (`zero_words_le`,
`zero_wordsT_le`) and, with the qubits of the released registers (`card_NW_eq`, `card_NW_le`,
`card_TNW_eq`, `card_TNW_le`, for all public data), the released budgets on the released
registers. The zero and combined forms below keep every conclusion of the released endpoint they
extend, in the released order, and add the listed extras.

* `binary_ode_budget_count_zero`: for `q : Pub` with `BPublicOK0 q`, `BZeroCase q` and valid
  source circuits (no hypothesis on `γ`, `ζ` or the bit lengths), the protocol
  `nprotocol (bprepC q srcC) g` uses at most
  `36873000 g [q* (G_C + k_x + σ + m + r + k + ℓ (l+1) + 8) + G_src + A]` gates in every history
  (the explicit count of `GateODEBudget.binary_ode_budget`; `G_C = 2 (28 k_x + 2) + 2 |arith| +
  2 bP + bT + 1`, `A = k_x + |Zs| + (6 k_x + 4 b) + bT + bP + A_arith`; `count_arith`);
  `binary_ode_time_budget_count_zero`: the same with `73746000`, `q*'`, `ℓ'` and no `k` for
  `nprotocol (btprepC q loadC wpC) (2g)` (that of `GateODEBudget.binary_ode_time_budget`;
  `count_arithT`).
* `binary_ode_budget_bits_zero_released`: for `q : Pub` with `BPublicOK0 q`, `BZeroCase q`,
  `HasBits b_data γ`, `ν ≤ 196608 q* ζ`, `b ≤ b_data`, `HasBits b_data` of `c₀`, `η_H`, `η_D`,
  the binary data `D`, `en`, valid source circuits and every `M`, `m_src`, with
  `𝔟 = bitB b_data (2^k_x) M m_src q* g ε`, the protocol `nprotocol (bprepC q srcC) g` on the
  released register `GateNative.NW q.params (Fin k_x) Zs (SZ4 k_x b) bT bP A` has every bound of
  `GateBitBudget.binary_ode_budget_bits`, in its order: at most
  `10²⁰ g [q* (𝔟+1)³ + G_src + |Zs|]` gates and `3·10¹¹ (𝔟+1)³ + 2 |Zs|` qubits;
  `𝔴 + ℓ ≤ 300 (𝔟+1)` (`𝔴 = GateODEBudget.words q`); at most
  `3·10¹² g [q* (𝔴+ℓ+1)³ + G_src + |Zs|]` gates and `10⁴ (𝔴+1)³ + 2 |Zs|` qubits (the bounds of
  `GateODEBudget.binary_ode_budget_words`); the explicit count `36873000 g […]`; at most
  `40 g (calls_c(srcC 0) + calls_c(srcC 1))` calls of every kind `c` (no matrix call);
  `|NW| = 22 k_x + 12 m + 24 r + 4 k + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + 47`; further
  `q* = ℓ`, valid trials, no call of a kind that the source circuits do not call, and `NOutcome`
  under the zero-case conditions of `binary_ode_budget_bits_zero`.
* `binary_ode_budget_bits_nonneg`: for `BPublicOK0 q` (every `T ≥ 0`), the hypothesis
  `if BZeroCase q then HasBits b_data γ else γ = gammaOf T η_H η_D g ε` and otherwise those of
  `GateBitBudget.binary_ode_budget_bits` (`ν ≤ 196608 q* ζ`, `b ≤ b_data`, `HasBits b_data` of
  `c₀`, `T`, `η_H`, `η_D`, `hrange`, `hdec`, valid sources), with
  `𝔟 = bitB b_data (2^k_x) (2^m) (2^k) q* g ε`: every conclusion of `binary_ode_budget_bits`, in
  its order, for the protocol `nprotocol (bprepC q srcC) g` (`10²⁰`, `3·10¹¹`, `300`, `3·10¹²`,
  `10⁴`, the explicit count `36873000 g […]`, at most `(if BZeroCase q then 0 else
  3932160 g q* ([row] + [col] + [value])) + 40 g (calls_c(srcC 0) + calls_c(srcC 1))` calls of
  every kind `c`, the register identity, and `NOutcome` under the released hypotheses,
  `98304 q* ζ + 2 ζs ≤ ν`), with the validity of the trials inserted before `NOutcome`.
* `binary_ode_time_budget_bits_zero_released`, `binary_ode_time_budget_bits_nonneg`: the same for
  `q : PubT` with `BTPublicOK0 q`, `btprepC`, ratio `2g`: every conclusion of
  `GateBitBudget.binary_ode_time_budget_bits`, in its order (the internal `q*'`,
  `𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε`; `2·10²⁰`, `3·10¹¹`, `300`, `6·10¹²`, `10⁴`, the
  explicit count `73746000 g […]`, the calls `(if BTZeroCase q then 0 else 7864320 g q*' (…)) +
  80 g (calls_c(loadC) + 2 calls_c(wpC))`, in the zero form without the matrix part,
  `|TNW| = 22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + 47`), then both
  bounds of `GateBitBudget.binary_ode_time_budget_bits_user` (`2·10²²`, `9·10¹²` in the user's
  `q*`, `𝔟`; in the zero case `q*' ≤ 2 q*` and `𝔟' ≤ 𝔟 + 1`, `logBudget_two_le`, `bitB_le_succ`);
  the zero form further `q*' = ℓ'`, valid trials, no call of a kind that the supplied circuits do
  not call and `NOutcome` against `x(T)` under the zero-case conditions of
  `binary_ode_time_budget_bits_zero`; the combined form valid trials and `NOutcome` under the
  released hypotheses (`98304 q*' ζ + 3 ζs ≤ ν`, `PubT.Rest`).
* `binary_ode_budget_trials_bits_zero_released`, `binary_ode_budget_trials_bits_nonneg` (and the
  time-dependent `binary_ode_time_budget_trials_bits_zero_released`,
  `binary_ode_time_budget_trials_bits_nonneg`): under the synthesis hypotheses, the protocol
  `nprotocol (synthPrep hS (ν/3) (bprepC q srcC)) g` (resp. of `btprepC`, ratio `2g`) on the
  released trial register `GateSynthTrials.SNW` (resp. `STW`) has every conclusion of
  `GateBitBudget.binary_ode_budget_trials_bits` (resp. `binary_ode_time_budget_trials_bits`), in
  its order: the native preparation bound `B = GateODEBudget.prepBound q srcC` (resp.
  `prepBoundT q loadC wpC`) satisfies `B ≤ 2·10¹⁸ q* (𝔟+1)³ + G_src` (in the zero case
  `prepBound_le_zero`, `prepBoundT_le_zero`); in every history at most
  `40 g (2·10¹⁸ q* (𝔟+1)³ + G_src) (c₁ (64 (𝔟+1) + log(G_src+1)) + c₀) +
  20 g (4 (3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢` (resp. `80 g`, `40 g`, `q*'`, `𝔟'`)
  on at most `7·10¹¹ (𝔟+1)³ + 4 |Zs| + 2 |Xa|` qubits; valid trials of `𝒢`; one preparation within
  `B` gates (the direct source assembly has `G_src + 2`, resp. `G_src`, gates,
  `zero_gates_le_prepBound`, `zero_gates_le_prepBoundT`); the synthesised count
  `40 g B (c₁ log((B+1)/(ν/3)) + c₀) + 20 g (4 n' + 3)` (resp. `80 g`, `40 g`;
  `n' = 22 k_x + 12 m + 24 r + 4 k + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + |Xa| + 47`, resp.
  `16 m` and no `k`; `trial_count_le`); the calls with the matrix part
  `if <zero case> then 0 else <released>`; the register identity
  `|SNW| = 44 k_x + 24 m + 48 r + 8 k + 8 l + 16 b + 4 (bT + bP + A_arith) + 4 |Zs| + 2 |Xa| + 95`
  (resp. `|STW| = 44 k_x + 32 m + 48 r + 8 l + 16 b + …`); and `NOutcome` under the zero-case
  conditions, resp. the released hypotheses. The zero forms further give `q* = ℓ`, the exact
  gates `N` of one preparation, the sharper count `40 g N (c₁ log((N+1)/(ν/3)) + c₀) +
  20 g (4 (n + |Xa|) + 3)` (`n` the qubits of the released register; `card_trial_released`,
  `card_trialT_released`; `trial_budget_le` gives the released form) and no call of a kind that
  the supplied circuits do not call.

**Satisfiability** (`NonVacuity`). The hypotheses of the endpoints hold together for explicit
data. The released `GateBitBudget.ode_all_hyps`, `ode_time_all_hyps` witness the positive case,
which the corollaries of A from the released endpoints and the positive branches of the combined
forms share; the polynomial hypotheses of A hold for every single instance with
`c = G_src + |Zs|`, `j = 0`. `zero_all_hyps`, `zero_time_all_hyps`: the zero-time public data
`zeroPub`, `zeroPubT` (`T = 0`, `γ = 1`, `ε = ζ = 1/2`, `m = 0`), `b_data = 1`, the one-point
binary data `GateBitBudget.pointData`, the identity equivalence and empty circuits on the empty
source scratch satisfy every hypothesis of `binary_ode_budget_bits_zero_released` and
`binary_ode_budget_bits_nonneg` (zero branch), resp. `binary_ode_time_budget_bits_nonneg`, whose
gate bounds then hold. `zero_instance_all_hyps`: with `zeroPubZ` (`ζ = ν/(196608 q*)`,
`GateBitBudget.zetaOf`), `J_src = 1`, `x₀ = seedV`, `v = 0` and `ζs = 0` (`approx_empty`), every
hypothesis of `binary_ode_budget_bits_zero`, `binary_ode_budget_bits_zero_released` and
`binary_ode_budget_bits_nonneg` (zero branch), the antecedents of their guarantees included,
holds at once; `zero_instance_outcome` derives the guarantees `NOutcome` on the minimal and on the
released register. The finite-gate-set forms add only the released synthesis hypotheses
(`GateSynth.Synthesis`, `len ζ ≤ c₁ log(1/ζ) + c₀` with `c₀, c₁ ≥ 0`, `AdjClosed`,
`zeroTestKinds ⊆ 𝒢`), and the minimal-register forms no bit-length hypothesis. The remaining
instance conditions `PubT.Rest` of the time-dependent guarantees are not witnessed (the released
libraries do not witness them either).

**Proof map** (module paths relative to `GateEfficientRemarks/`).

* `ODE/Absorb` (arithmetic) → `ODE/Poly` (A, from `GateBitBudget.binary_ode_budget_bits`,
  `binary_ode_time_budget_bits`, `binary_ode_time_budget_bits_user`, with
  `GateODEBudget.pub_shapeOK`, `pubT_shapeOK` for `q* ≥ 1` and `GateBitBudget.bitB_nonneg`) and
  `ODE/PolySynth` (A over a finite gate set, from the two released `_trials_bits` endpoints and
  `synth_absorb`); `ODE/PolyNonneg` (A for every `T ≥ 0`, the same arithmetic on the combined
  forms of C, with `one_le_qOf`).
* `ODE/SynthZero` (B, native zero case): the counts and the guarantee `NOutcome` of
  `ZeroTimeGateODE.native_ode_solver_zero` (`native_ode_time_solver_zero`), then the released
  `GateSynth.sprotocol_valid`, `sprotocol_worst`, `sprotocol_worst_log` and `GateSynth.soutcome`
  (budget `ε/200 ≤ min(1/400, ε/20)`, nonzero target) → `ODE/SynthCombined` (case split through
  `ZeroTimeGateODE.native_ode_solver_nonneg`, `native_ode_time_solver_nonneg`) → `ODE/SynthBinary`,
  `ODE/SynthBinaryTime` (the zero forms from `ODE/SynthZero` on the released binary register with
  `ZeroTimeGateODE.binary_target_zero`, `binary_tzInstanceOK`, `btparams_ok0`,
  `btzeroCase_params`; the combined forms from `ZeroTimeGateODE.binary_ode_solver_nonneg`,
  `binary_ode_time_solver_nonneg`).
* `ODE/MinRegister` (registers, `q*`, `𝔟`) → `ODE/ZeroBudget`, `ODE/ZeroBudgetTime` (C, from
  `ZeroTimeGateODE.native_ode_solver_zero`, `native_ode_time_solver_zero` on the minimal register:
  the explicit counts, the linear bounds from `k_x (+ m) ≤ 𝔟` and `q* ≥ 1`, the cubic bounds by
  `lin_le_cube`, `lin_le_cube_space`) → `ODE/ZeroTrials`, `ODE/ZeroTrialsTime` (C over a finite
  gate set, from `ZeroTimeGateODE.native_ode_solver_zero_trials`,
  `native_ode_time_solver_zero_trials` and `log_trial_le`, `log_trialT_le`).
* `ODE/ZeroWords` (the envelope `X = (Q g + 1)/ε`, the generic word bounds at zero common time and
  the zero case of the constant-coefficient parameters, from the released `GateBitBudget.kap_le`,
  `kap_inv_le`, `rho_le`, `one_le_mul_rho`, `one_le_radius`, `nat_le_mul_pow`,
  `clog_le_mul_pow`, `clog_ceil_le_nat`, `SharpFilterSchedule.degree_le` and
  `GateODE.AnalyticLCHS.gridSize_le`) → `ODE/ZeroWordsSum` (`zero_words_le` with the released
  `l_word`, `F_word`, `nOf_word`; `card_NW_eq`, `card_NW_le` from `ZeroTimeGateODE.card_ZNW` and
  `GateODEBudget.binary_arith_words`) → `ODE/ZeroReleased` (the explicit count from
  `ZeroTimeGateODE.native_ode_solver_zero` and `count_arith`; the zero form on the released
  register with `GateBitBudget.cube_le`; the combined form by cases, the positive case from
  `GateBitBudget.binary_ode_budget_bits` through `ZeroTimeGateODE.bpublicOK_of`).
  `ODE/ZeroWordsT` → `ODE/ZeroReleasedTime`: the same for time-indexed data, with
  `GateBitBudget.logb_X_two_le`, `GateODEBudget.binary_time_arith_words`, `count_arithT`,
  `native_ode_time_solver_zero`, `binary_ode_time_budget_bits`,
  `binary_ode_time_budget_bits_user`. `ODE/ZeroReleasedTrials`, `ODE/ZeroReleasedTrialsTime`:
  the zero forms from `native_ode_solver_zero_trials`, `native_ode_time_solver_zero_trials`, the
  zero forms above, `log_trial_le`, `log_trialT_le`, `trial_budget_le`,
  `GateSynthTrials.card_SWO`, the preparation bounds (`GateBitBudget.inner_le`, `cube_le` as in
  the released `GateBitBudget.prepBound_le`, `prepBoundT_le`) and `trial_count_le` (with the
  released `GateBitBudget.synth_arith`); the combined forms with the validity of
  `ZeroTimeGateODE.binary_ode_solver_nonneg_trials`, `binary_ode_time_solver_nonneg_trials` and
  the positive case from `GateBitBudget.binary_ode_budget_trials_bits`,
  `binary_ode_time_budget_trials_bits`.
* `ODE/NonVacuity` (satisfiability): the released `GateBitBudget.pointData`, `pointData_range`,
  `pointData_matrix`, `hasBits_zero` and `zetaOf_spec`, and `hasBits_one` (`ODE/ZeroWords`),
  applied to the zero forms and the combined forms.

Every theorem of this part is axiom-audited in `GateEfficientRemarks/Audit.lean`.

**Formalisation choices.**

* A: the polynomial source costs are the hypotheses `G_src ≤ c (𝔟+1)^j`, `|Zs| ≤ c (𝔟+1)^j` on
  the instance (`𝔟+1 ≥ 1`, so `j = 0` gives constants); their content is uniformity over a family:
  every single instance meets them with `c = G_src + |Zs|`, `j = 0`. The exponent `max j 3` comes
  from the cubic released bounds (the CORDIC counts), one more power over a finite gate set from
  `log(G_src + 1) ≤ c + j (𝔟+1)`. The synthesis ancillas `|Xa|` of the hypothesis
  `Synthesis 𝒢 Xa len` do not depend on the instance and are kept as the released additive terms
  (`80 g |Xa|`, `160 g |Xa|`, `2 |Xa|`); since `q* (𝔟+1)^(J+1) ≥ 1` they can be absorbed into the
  constant. The corollaries state only the polynomial bounds; the protocols and every other
  conclusion are those of the endpoints they follow from (the released endpoints, resp. the
  combined forms of C) under the same hypotheses (as for the released
  `GateBitBudget.binary_ode_time_budget_bits_user`).
* B: the synthesis budget `ε/200` per trial and the guarantee `SOutcome` (without per-trial claim)
  are those of the released synthesised solvers. The native zero forms hold on every register
  `ZeroTimeGateODE.ZNW` (the released register `NW p` is one, `ZeroTimeGateODE.nw_eq_znw`), the
  binary forms on the released binary registers through `bprepC`, `btprepC`. The zero forms use
  the zero-case conditions of `ZeroTimeGateODE` (weaker than the released ones: no condition on
  `U_J`, private operations, arithmetic, column energies or accretivity for constant
  coefficients, and the source budget `2 ζs ≤ ν` resp. `3 ζs ≤ ν`); the binary zero forms drop the
  hypotheses `hrange`, `hdec` of the released binary solvers on the slots and the decoder of the
  data (the direct source assembly does not query the data); the combined native forms use the
  case-dependent hypotheses of `ZeroTimeGateODE.native_ode_solver_nonneg`
  (`native_ode_time_solver_nonneg`), the combined binary forms the released hypotheses in both
  cases, as `ZeroTimeGateODE.binary_ode_solver_nonneg` (`binary_ode_time_solver_nonneg`).
* C: the zero-case protocol uses no simulator, so its natural register is the minimal one. On
  `MinW` no bit-length hypothesis is needed (the only words are `k_x` and `m`), so the bounds hold
  for every `b_data`; for constant coefficients they hold for `𝔟` with every time mesh `M` and
  number of source nodes `m_src` (`bitB` grows with both, `GateBitBudget.bitB_mono`, so
  `M = m_src = 0` gives the strongest bound; the released `M = 2^m`, `m_src = 2^k` are among the
  admissible choices), for time-dependent coefficients with the mesh `M = 2^m` and its `2^m`
  source nodes. The constants are those of the positive case (`10²⁰`, `2·10²⁰`, `2·10²²`,
  `3·10¹¹`, `9·10¹²`, `7·10¹¹`, `64`) and the bounds are in fact linear in `𝔟` before synthesis
  (`780`, `1400`, `17`). The guarantees are those of `ZeroTimeGateODE` under its zero-case
  conditions (without `hrange`, `hdec`); at `T = 0` the forcing circuit is applied with weight
  zero (as there).
* C on the released registers (those of `bprepC`, `btprepC`, which give the forms for every
  `T ≥ 0`): their words depend on the rescaling `γ`, a free public parameter in the zero case (the
  public choice `gammaOf` vanishes there and is excluded by `BPublicOK0`), and the released word
  lemmas assume the positive case. The zero forms assume `γ` of bit length `b_data`
  (`HasBits b_data γ`, the released bit-length hypothesis of `c₀`, `T`, `η_H`, `η_D` extended to
  `γ`; the public choice `γ = 1` meets it, since `b_data ≥ b ≥ 1`, `hasBits_one`) and the released
  accuracy condition `ν ≤ 196608 q* ζ`; the combined forms take
  `if <zero case> then HasBits b_data γ else γ = gammaOf …` and otherwise the released
  hypotheses, with the released `𝔟` (`M = 2^m`, `m_src = 2^k`, resp. `2^m`, `2^m`), the released
  constants, and in the zero case the bound `0` for the calls of the matrix oracles. The explicit
  counts, the register identities and `G_src + 2 ≤ B` (resp. `G_src ≤ B`) need none of these
  hypotheses. The zero forms keep the zero-case conditions of `ZeroTimeGateODE` for the
  guarantees and drop `hrange`, `hdec`; the combined forms assume the released hypotheses in both
  cases (they imply the zero-case conditions).
* `𝔟` uses base-2 logarithms (`GateBitBudget.bitB`), as in the released budgets.

**Not formalised.**

* Bounds in `𝔟` on the released registers in the zero case without a bit-length hypothesis on
  the free rescaling `γ` (it enters the decoder word `⌈log₂ ⌈1/κ⌉⌉` through `γ⁻¹`). In
  particular the explicit-constant budgets of `GateEfficientODEBudget`
  (`GateODEBudget.binary_ode_budget`, `binary_ode_budget_words`, `binary_ode_budget_trials` and
  their time-dependent forms) are restated for the zero case only inside the forms in `𝔟` of C,
  under their bit-length and accuracy hypotheses; without these hypotheses C states the explicit
  counts `binary_ode_budget_count_zero`, `binary_ode_time_budget_count_zero`, the register
  identities and qubit bounds `card_NW_eq`, `card_NW_le`, `card_TNW_eq`, `card_TNW_le` and the
  preparation gates `zero_gates_le_prepBound`, `zero_gates_le_prepBoundT`. The sizes
  `GateODEBudget.binary_ode_sizes`, `binary_ode_time_sizes` are not restated for the zero case (C
  has the zero-case bounds `zero_tau`, `zero_degree`, `zero_r_word`, `zero_J_le` and their
  time-dependent forms).
* `𝔟` forms of the protocols that synthesise every trial (B), in the zero case and, as listed by
  the `GateEfficientBitBudget` guide, in the positive case; their counts are stated explicitly.
* A and C for the solvers whose arithmetic or data are hypotheses (`GateEfficientNative`, exact
  gates), which have no released form in `𝔟`; a finite-gate-set form with the query shape of the
  user's `(g, ε)` (no released endpoint).
* The A corollaries of the zero forms of C (`binary_ode_budget_bits_zero`,
  `binary_ode_time_budget_bits_zero`, the `_trials_bits_zero` forms and the `_zero_released`
  forms; the zero case on the released registers is covered by the corollaries of the combined
  forms in `PolyNonneg`); they follow from `gates_absorb`, `space_absorb`, `synth_absorb` and
  `one_le_qOf` as in `PolyNonneg`.
* The construction of the source circuits and their costs (`G_src`, `|Zs|` remain parameters;
  A assumes their polynomial bounds); floating-point public parameters; single-qubit synthesis
  and the decomposition of controlled gates (the hypothesis `GateSynth.Synthesis`).

**Provenance.** New part of the new library `GateEfficientRemarks`; it imports
`GateEfficientBitBudget`, `ZeroTimeGateODE`, `GateEfficientSynthesis`,
`GateEfficientSynthesisTrials`, `GateEfficientODEBudget`, `GateEfficientBinaryODE.Synth`,
`GateEfficientBinaryODETime.Synth` (and through them the gate-level ODE libraries) and changes none
of them. It reuses without change `GateBitBudget` (`bitB`, `bitB_nonneg`, `nat_le_logb`,
`logb_succ_nonneg`, `log_le_logb`, `synth_arith`, `inner_le`, the five endpoints above, the
witnesses `ode_all_hyps`, `ode_time_all_hyps` and `pointData`, `pointData_range`,
`pointData_matrix`, `hasBits_int`, `hasBits_zero`, `zetaOf`, `zetaOf_spec`), `GateODEBudget` (`qOf`,
`thetaOf`, `pub_shapeOK`, `pubT_shapeOK`, `ShapeOK.one_le_q`, `prepBound`, `prepBoundT`),
`ImprovedODEQueryBudget` (`logBudget`, `logBudget_ge_one`, `precision`, `precision_pos`,
`precision_le_one_ten_thousandth`, `theta`, `queryShape`), `ZeroTimeGateODE` (the circuits,
conditions and endpoints listed above, `ZNW`, `zPool`, `card_ZNW`), `GateSynth` (`sprotocol`,
`synthBudget`, `GateOf`, `SOutcome`, `soutcome`, `sprotocol_valid`, `sprotocol_worst`,
`sprotocol_worst_log`), `GateSynthTrials` (`synthPrep`, `SWO`, `SX`, `card_SWO`), `GateNative`
(`nprotocol`, `NOutcome`, `trialN`, `nGatesN`, `nCallsN`, `wGateN`, `wCallN`, `XW`) and
`GateCircuit.Sim.card_wire`, `GateODE.card_oWire`, and for C on the released registers the listed
word lemmas of the proof map, `GateBitBudget.HasBits`, `bitB_mono`, `cube_le`, `logBudget_two`,
`GateODEBudget.words`, `wordsT`, `gammaOf`, `sqrt_four_mul`, `binary_arith_words`,
`binary_time_arith_words`, `ZeroTimeGateODE.bpublicOK_of`, `btpublicOK_of`, `btparams_ok0`,
`btzeroCase_params`, `binary_target_zero`, `binary_tzInstanceOK`. The statement guide of
`GateEfficientBitBudget` lists "the absorption of source costs polynomial in `𝔟` into `q poly(𝔟)`"
as not a Lean statement and the cases `T = 0`, `η_H + η_D = 0` as excluded (as does that of
`GateEfficientODEBudget`); the guide of `ZeroTimeGateODE` lists as not formalised "The
finite-gate-set forms that synthesise every trial (`GateSynth.native_ode_solver_synth`,
`GateSynth.native_ode_time_solver_synth`, `GateBinaryODE.binary_ode_solver_synth`,
`GateBinaryODETime.binary_ode_time_solver_synth`) are not restated for the zero case; they would
follow from the `GateNative.NOutcome` statements here by the released `GateSynth.soutcome`." and
"The absolute-constant forms of equations `ode:eq:gate-main` and `ode:eq:gate-space` for the zero
case, and the explicit-constant budgets of the library `GateEfficientODEBudget` for it (the explicit
counts above are stated instead)."; the README lists both remarks among the items not formalised.
These entries are superseded by A, B and C, except for the items listed under **Not formalised**.
-/
