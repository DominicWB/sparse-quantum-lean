import GateEfficientTimeDependent.Theorem

/-!
# Gate-efficient time-dependent Hamiltonian simulation: paper-to-Lean entry point

Gate counts for time-dependent Hamiltonian simulation on a uniform mesh
(Theorem `hs:thm:time`), with exact gates, are formalized by
`SparseHamiltonian.GateCircuit.SlotSim.gate_efficient_time_simulation` in
`GateEfficientTimeDependent/Theorem.lean`.  The manuscript states the
gate-efficient Theorem `hs:thm:gates` for time-independent Hamiltonians only;
the circuit here is the released circuit of `hs:thm:gates` with a
slot-selected private Cayley operation, the single-label case of the coherent
selection `ode:lem:gate-select`.  The library also supplies the slot-selected
simulator used by the time-dependent part of `GateEfficientODE`.

**Access model.** As in `GateEfficientHamiltonian`: the system is an
arbitrary complex Hilbert space `P` (which may include an untouched
reference), `U_J` is a supplied unitary on `a` ancilla qubits and the system,
and the circuits are lists of the released instructions on the wires
`Wire a m r K` (`Circuit.Instr`): elementary gates (one-qubit unitaries with at
most three literal controls), `U_J` or `U_J†`, and the private operation or its
inverse, both controlled by the private-sector wire.  The private operation is
*slot-selected*: one call applies the supplied unitary `D k` to the ancilla
slice of every configuration whose `m` slot wires carry the slot `k`
(`slotOracle`), and is counted once.  `runT U_J D gs` is the operator of the
circuit `gs` in this semantics; lists without private calls run exactly as in
the released semantics (`runT_eq_run`).  `io` places the system on the
all-zero configuration of every wire.

**Hypotheses** (`gate_efficient_time_simulation`). Public: `t ≥ 0`, `α > 0`,
`Q ≥ 1`, `qbar ≤ Q`, `0 < ε ≤ 1`, `β ≥ 0`, and a mesh exponent `m` with
`steps (α t) (ε/6) ≤ 2^m` (subdivision of the Cayley steps, `steps τ δ =
1 + ⌈max (4τ, (τ³/δ)^{1/2})⌉`) and `4 β t² ≤ ε 2^m` (freezing); `meshExp`
gives an explicit `m` with `2^m < 2 max (steps (α t) (ε/6), ⌈4 β t²/ε⌉)`.
Instance: `U_J` and every `D k` (`k < 2^m`) are unitary and satisfy the clock
promises of the released analysis for the boundary isometry `J = U_J ι₀` and
the normalised represented sample `H̃_k / α` — the resolvent
`R1 k = (1 - D k)⁻¹` with `‖R1 k‖ ≤ Q`, `J† R1 k J = (1 + i H̃_k/α)/2`,
`‖R1 k J‖ ≤ b`, `b² ≤ qbar/2` — with `H̃_k` self-adjoint and `‖H̃_k‖ ≤ α`; a
Hermitian path `H(u)`, `0 ≤ u ≤ t`, with `‖H(u) - H(v)‖ ≤ β |u - v|`; sample
errors `‖H(k t/2^m) - H̃_k‖ ≤ δ` with `4 t δ ≤ ε`.

**Circuit.** `simCircuitT a (α t) Q qbar (ε/2) m` is the released circuit
`ampI` (one oblivious amplification round of the LCU of signed coherent-reuse
branches) for the normalised time `α t`, with `2^m` slots, Cayley step
`w = α t / 2^m` and filter degree `d = fDeg Q (α t) qbar (ε/2)`; it depends
only on the public numbers.

**Guarantees** (`gate_efficient_time_simulation`):

* every instruction is a valid elementary instruction;
* exactly `6d` slot-selected private calls and exactly `12d` calls of `U_J` or
  `U_J†`;
* at most `200 (d+1)(a+m+r+1)` elementary gates on `2a + 3m + 6r + 3` qubit
  wires besides the system;
* `d ≤ 128 (α t qbar + Q (1 + log (6/ε)))` and `2d + 2 ≤ 2^r ≤ 4 (d+1)`;
* the path has a propagator (`TimeDependent.exists_solvesOn_of_lipschitz`),
  and for every propagator `U` with `U(0) = 1` and `U' = -i H U`,
  `‖runT U_J D (simCircuitT …) ∘ io - io ∘ U(t)‖ ≤ ε`: the full output,
  including every work register, is within `ε` of the clean evolved state.

`propagator_error` gives the general split: with accuracy parameter `ε'`
and `2^m ≥ steps (α t) (ε'/3)`, the error is at most
`ε' + β t²/2^m + t δ`.

**Sparse parameters** (`sparse_counts`). For sparsity `s ≥ 1`, row and column
norm bound `η` and `τ = η t`, the released precision budget
(`ImprovedPrecisionBudget.exists_rescaling_for_precision`, as in
`hs:thm:time`) chooses `γ ∈ (0, 1]` with `γ √s ≥ 1`; with `α = η √s / γ`,
`Q = ⌈max (1, γ √s)⌉ ≥ 1` and `qbar = (1 + γ²)/2 ≤ Q`,
`d ≤ 4608 (√s τ + √(s τ log(1/ε)) + log(1/ε))`, so on any mesh meeting the
subdivision condition the circuit makes at most `27648 q` private calls and
`55296 q` calls of `U_J` or `U_J†` and uses at most
`200 (4608 q + 1)(a + m + r + 1)` gates, `2^r ≤ 4 (4608 q + 1)`,
`q = √s τ + √(s τ ℓ) + ℓ`, `ℓ = log(1/ε)`. Neither `2^m` nor `β` multiplies
the number of calls; they enter the gate count only through `m`.

**Proof map.** Module paths are relative to `GateEfficientTimeDependent/`.

* Slot-selected semantics and the reuse model: `SlotSim` (`slotOracle`,
  `runT_eq_run`; on embedded reuse-model states the slot-selected private
  call is the parallel slot action `⊕ₖ D k`, `secOracleT_emb`; the reuse step
  `STEPT_emb`, the selection `selectNT_emb` and its successful block
  `select_blockT`; agreement with the ideal operators on clean inputs
  `stepT_agrees`, `selectT_agrees`).
* The LCU block, the slot-dependent chronological clock and the error:
  `SlotError` (`lcu_blockT`; `netB_slot`, `netG_slot`: the effective
  transducer blocks are those of the released time-dependent implementation
  `TimeDependent.implementationV`; `ampT_agrees`, `lcu_compressionT`;
  `cayley_evolution_error`: each Cayley step is within `w³` of the slot
  exponential; `ampT_error` with the released
  `TimeDependent.exists_precise_implementationV` and
  `GateBlockTransfer.amplified_error_le`; `simulationT`: error against the
  ordered product of the slot exponentials `exp (-i w H_k)`).
* Public counts, mesh, propagator error and the theorems: `Theorem`
  (`simCircuitT_public`, `meshExp_spec`, `propagator_error` with the released
  freezing estimate `TimeDependent.mesh_error`,
  `gate_efficient_time_simulation`, `sparse_counts`).

**Formalization choices.**

* Gates are exact: arbitrary one-qubit unitaries with at most three controls
  and exact rotation angles, as in `GateEfficientHamiltonian`.
* All slots use the same Cayley step `w = α t / 2^m`, so the released dyadic
  boundary network, pointer states and amplification are reused unchanged;
  only the private call reads the slot register.
* The error budget is `ε/2` for the simulation of the ordered product (`ε/6`
  for the filter, doubled by amplification, and `ε/6` for the Cayley steps),
  `ε/4` for freezing the path at the left endpoints and `ε/4` for the sample
  errors.
* Not formalised here: the native sparse instantiation of `U_J` and of the
  slot-selected Cayley operations (entry decoding, arithmetic and the
  sampled-time locators), approximate private implementations,
  finite-gate-set synthesis, nonuniform meshes and negative times.
-/
