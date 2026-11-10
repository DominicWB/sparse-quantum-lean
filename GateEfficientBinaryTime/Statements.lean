import GateEfficientBinaryTime.Budget

/-!
# Time-dependent gate-level construction from binary data: paper-to-Lean entry point

Theorem `hs:thm:gates` of the accompanying paper is "a time-independent result"; its circuit with
slot-selected private Cayley operations covers the time-dependent setting of Theorem `hs:thm:time`
on a uniform mesh of `2^m` slots (package extension: Theorem `hs:thm:time` with the circuit of
`hs:thm:gates` (single-label case of Lemma `ode:lem:gate-select`)). Its native form,
`GateNative.native_time_simulation` (before finite-set synthesis), takes as hypotheses the entry
decoding and the reversible angle arithmetic (`ArithOK`), the public compute circuit of the
slot-selected private Cayley operation with its native identity (`NativeOK` for the slot-selected
family), and `U_J` given by elementary gates. The library `GateEfficientBinary` constructs these for
time-independent Hamiltonians given by binary sparse oracles. This library constructs them for
time-dependent Hamiltonians given by time-indexed binary sparse oracles and instantiates the
time-dependent gate-level simulation (package extension: Theorem `hs:thm:time` with the circuit of
`hs:thm:gates` (single-label case of Lemma `ode:lem:gate-select`)) and
its budget with the rescaled sparse parameters of `hs:thm:time`. The released libraries and
`GateEfficientBinary` are unchanged. No result from another paper is used. All declarations below
are in the namespace `SparseHamiltonian.GateBinary`, unless stated otherwise.
References to the manuscript use its labels.

* The time-dependent gate-level simulation (package extension: Theorem `hs:thm:time` with the
  circuit of `hs:thm:gates` (single-label case of Lemma `ode:lem:gate-select`)) for binary data:
  `binary_time_simulation`, with the circuit `binaryTimeSim`; the
  budget form: `binary_time_simulation_budget`.
* The native identity of the slot-selected private operation: `sparse_nativeOK_time`, with the
  time-indexed primitive oracles `primsT`, the compute circuit `computeVT` and the native private
  operation `sparseOpT` (public: `sparseOpT_public`; counts: `computeVT_nGates`,
  `computeVT_nCalls`).
* The generic transfer from per-slot native identities to the slot-selected one:
  `nativeOK_slot`, with `nrun_slot`, `Rdec_slot`, `slot_public`, `nGatesN_slot` and
  `nCallsN_slot`.
* The clock promises at every slot: those of `GateEfficientBinary` for the sample of the slot,
  with the normalisation `α = √s/γ` (`compressed_eq_smul`, `Hbin_eq_smul`, `DbinT_word`).

**Time-indexed binary data.**
`D : NativeSparseBlockEncoding.Data (X × Fin (2^m)) n (Cfg (VW b)) s` are the released native
sparse data whose input carries the time slot: on input `x`, the sample of time slot `j` is
`H̃_j = D.matrix (x, j)`, with its own stored words, locators and location oracles (the slot
embedding `D.slot` and the decoder do not depend on the input). Entries, indices and slots are
as in `GateEfficientBinary`: two `b`-bit two's complement words with decoder `c₀ (X + i Y)`,
`c₀ > 0` (`hdec`), `k`-bit indices (`en`), and `s = 2^σ` slots, `σ ≤ k`, on the index words
supported on the lowest `σ` bits (`hrange`). A slot word `w : Cfg (Fin m)` on the `m` time-slot
wires names the time slot `wordEquivFin m w`.

**Time-indexed primitive oracles** (`primsT D en x`). They act on `m` slot qubits, the edge
register and the value qubits: at slot word `w` they are the binary primitive oracles
`prims D en (x, wordEquivFin m w)` of the sample (`slotPrim`: for each oracle label, the
coherent sampled-time oracle `Σ_w |w⟩⟨w| ⊗ O(x, w)`). They are unitary (`primsT_isUnitary`);
calls are never controlled, and every call, forward or inverse, counts once.

**The slot-selected native private operation** (`sparseOpT k b m κ`). The private register and
the scratch are those of `sparseOp`, with the `m` slot wires as selection wires. The compute
circuit `computeVT` is `computeV` with every call also reading the slot wires (`slotInstr`):
`28 k` elementary gates and `2` row, `2` column and `1` value calls. The decoder is `κ (X + i Y)`
of the value wires.

* `nativeOK_slot`: for a native operation without selection wires, if the native identity holds
  for the primitives `primAt w` and the private operation `Dat w` at every word `w`, then its
  slot extension satisfies the native identity for the selection-controlled primitives
  `slotPrim primAt` and the selected family `selOp Dat`. Proof: the extended circuit acts at
  word `w` as the original circuit with `primAt w` (`nrun_slot`), the decoded rotation is the
  original one (`Rdec_slot`), and the clean embedding and `selOp` decompose by words
  (`slice_cleanEmb`).
* `sparse_nativeOK_time`: `NativeOK (primsT D en x) (sparseOpT k b m (γ √s c₀)) (selOp D̂)` with
  `D̂ w = unconj (qlift (phiPR en) (FixedNativeCayleySimulation.action D (x, wordEquivFin m w) γ))`:
  at slot word `w`, `V† R_val V` acts on clean scratch as the qubit lift of the private Cayley
  operation of the sample `wordEquivFin m w` (from `sparse_nativeOK` for each sample).

**The time-dependent gate-level simulation (package extension: Theorem `hs:thm:time` with the
circuit of `hs:thm:gates` (single-label case of Lemma `ode:lem:gate-select`)) for binary data**
(`binary_time_simulation`). Hypotheses: the time-indexed binary
data above with `b ≥ 1`; an input `x` whose samples are Hermitian with row and column Euclidean
norms at most one; a time `t ≥ 0` and a matrix path `H : ℝ → Matrix n n ℂ`, Hermitian on `[0, t]`,
`β`-Lipschitz in operator norm on `[0, t]` for some `β ≥ 0` and within `δ` of the samples at the
slot times, `‖H(j t/2^m) - H̃_j‖ ≤ δ`; a rescaling `0 < γ ≤ 1`; accuracies `0 < ε ≤ 1` and
`0 < ζ ≤ 1`; the mesh conditions of `native_time_simulation` with the normalisation `α = √s/γ`,
`steps τ' (ε/12) ≤ 2^m` and `8 β t² ≤ ε 2^m`; the sample-error budget `8 t δ ≤ ε`; and the
arithmetic budget `48 d ζ ≤ ε`. Here `τ' = time s t γ = t √s/γ` is the clock time of the circuit,
`d = fDeg Q τ' qbar (ε/4)` is the filter degree and `r = simR Q τ' qbar (ε/4)` the size of the phase
registers, for `Q = width s γ = ⌈max(1, γ √s)⌉` and `qbar = moment γ = (1 + γ²)/2`. The circuit
`binaryTimeSim` is the native slot circuit `GateNative.nativeSimT` with `2^m` time slots,
`U_J = hadUJ`, the native private operation `sparseOpT` and the arithmetic `binArithT` (the CORDIC
circuit on the value wires at scale `κ = γ √s c₀`). Conclusions: every instruction is valid; for
every selection `p : Query → Bool` of oracle labels the circuit makes exactly `12 d` times `2`
row-location, `2` column-location and `1` value calls of the selected labels; it uses at most
`200 (d+1)(k + 1 + m + r + 1) + 84 d (σ + 1) + 6 d (56 k + 2 |circ| + 2 bP + bT + 1)` elementary
gates (`|circ|`, `bP`, `bT` of `binArithT`, bounded by `cordicArith_counts`); it has
`k + (2 (k+1) + 3 m + 6 r + 3) + (6 k + 2 b + bT + bP + A + 3)` qubits;
`d ≤ 128 (τ' qbar + Q (1 + log (12/ε)))` and `2d + 2 ≤ 2^r ≤ 4 (d + 1)`; the propagator of the
lifted path `u ↦ qlift en (H u)` exists; and for every such propagator `U`,

`‖nrun (primsT D en x) (binaryTimeSim …) ∘ sysEmb io - sysEmb io ∘ U(t)‖ ≤ ε`,

where `sysEmb io` puts every non-system qubit in `0` (input and target alike) and the payload `R`
is an untouched reference. The clock promises at every slot are those of the time-independent
case for the sample (`Dbin`, `R1bin`, `R1bin_boundary`, `R1bin_endpoint`), with the sample
Hamiltonian `Hs j = qlift en (H̃_j) = (√s/γ) Hbin` (`Hbin_eq_smul`, from `compressed_eq_smul`: the
compressed sparse generator at rescaling `γ` is `(γ/√s) H̃_j`); the lifted path inherits the
Lipschitz and sample bounds because the lift is a contraction (`norm_qlift_le`).

**The budget** (`binary_time_simulation_budget`). For `s ≥ 1`, `t ≥ 0`, `0 < ε ≤ 1` and
`q = √s t + √(s t log(2/ε)) + log(2/ε)`, the released time-dependent precision budget
(`GateCircuit.SlotSim.sparse_counts` at accuracy `ε/2`) gives one `γ ∈ (0, 1]` with `γ √s ≥ 1`,
chosen from `s`, `t` and `ε` before the data, the input, the path and the mesh (the existential
precedes every such binder), with `d ≤ 4608 q`; `q` has `log(2/ε)` in place of the `log(1/ε)` of
`hs:thm:gates` because the filter accuracy is `ε/4`. For all data, paths and meshes as above and
every `0 < ζ ≤ 1` with `221184 q ζ ≤ ε`, the circuit makes at most `55296 q` times `2` row,
`2` column and `1` value calls, uses at most
`200 (4608 q + 1) (G_C + (σ + 1) + (k + 1) + m + r + 1)` elementary gates with
`G_C = privGates = 56 k + 2 |circ| + 2 bP + bT + 1` and `2^r ≤ 4 (4608 q + 1)`, and has
full-output error at most `ε` for every propagator. Neither `β` nor `δ` enters these bounds; `β`
only constrains the number `2^m` of time slots (`8 β t² ≤ ε 2^m`), which enters only through the
`m` slot wires.

Every theorem of the library is axiom-audited in `GateEfficientBinaryTime/Audit.lean`.

**Formalisation choices.**

* The time-indexed data are released native sparse data with the slot in the input, so that the
  primitive oracles of each sample are those of `GateEfficientBinary`; the slot-selected oracles
  read the slot qubits of the circuit. The data format, the slot set and `U_J` are those of
  `GateEfficientBinary` (two's complement words, power-of-two dimension and sparsity, Hadamard
  `U_J`).
* The native identity of the slot-selected operation is reduced to the per-sample identity by a
  generic transfer (`nativeOK_slot`), with no new circuit analysis.
* The path is a matrix path `H`; the simulated propagator is that of its qubit lift on the `k`
  system qubits with an untouched reference payload. The normalisation of the native time theorem
  is `α = √s/γ`, so the clock time of the circuit is `τ' = α t = √s t/γ`.
* The mesh conditions are hypotheses with the explicit constants of `native_time_simulation`.
  They differ from equation `hs:eq:timegrid` (with `η = 1`): the Cayley condition
  `steps τ' (ε/12) ≤ 2^m`, where `steps τ ε = 1 + ⌈max (4 τ, (τ³/ε)^{1/2})⌉`, uses `τ' = α t`
  also in the cubic term, where the paper uses `Λ T` with `Λ = √s ≤ α`; freezing is
  `8 β t² ≤ ε 2^m` (paper: `6 β T² ≤ ε M`); and the sample-error budget is `8 t δ ≤ ε` (paper:
  `12 T δ_val ≤ ε`). The budget form chooses `γ` first, so that `m` can be chosen afterwards from
  `τ'`, `β`, `t` and `ε`.

**Not formalised.** Theorem `ode:thm:gates` from binary data (the label-selected private
operations of the ODE solvers combine the entries of `A_H` and `A_L` with the LCHS nodes);
nonuniform meshes in the gate counts; gate synthesis over a finite gate set.
-/
