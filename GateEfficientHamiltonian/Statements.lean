import GateEfficientHamiltonian.Circuit.Theorem

/-!
# Gate-efficient Hamiltonian simulation: paper-to-Lean entry point

The exact-gate part of Theorem `hs:thm:gates` (gate-efficient sparse
simulation) of the accompanying paper is formalized by
`SparseHamiltonian.GateCircuit.Sim.gate_efficient_simulation` in
`GateEfficientHamiltonian/Circuit/Theorem.lean`.
References to the manuscript use its labels.

**Access model.** The system is an arbitrary complex Hilbert space `P`; for
the simulation of a finite register, `P` is that register (and may include an
untouched reference). `U_J` and the private Cayley operation `D` are supplied
unitaries on `Anc a P`, that is `a` ancilla qubits together with the system.
A circuit is a list of instructions on the qubit wires `Wire a m r K` and the
system (`Circuit.Instr`):

* an elementary gate: a one-qubit unitary on one wire with at most three
  literal controls on other wires (`Instr.Valid`);
* `U_J` or `U_J†` on the ancillas and the system, controlled by the
  private-sector wire;
* the private Cayley operation `D` or `D†`, controlled by the same wire.

`run (simSem U_J D) gs` is the operator of the circuit `gs`; `io` places the
system on the all-zero configuration of every wire. Inverse calls are counted.

**Hypotheses.** Those of the released continuous-time simulation
(`SparseHamiltonian.SharpClockSimulation.exists_precise_implementation`) for
the private operation `D` and the boundary isometry `J = U_J ι₀`, where `ι₀`
puts the system on the zero ancilla word: the resolvent `R1 = (1-D)⁻¹` with
`‖R1‖ ≤ Q`, the boundary identity `J† R1 J = (1 + iH)/2` for a self-adjoint
`H` with `‖H‖ ≤ 1`, and the endpoint bound `‖R1 J‖ ≤ b`, `b² ≤ qbar/2`,
`qbar ≤ Q`. These are the clock promises supplied by Theorem `hs:thm:main`.
In addition `U_J` and `D` are unitary, `τ ≥ 0`, `Q ≥ 1` and `0 < ε ≤ 1`.

**Circuit.** `simCircuit a τ Q qbar ε` depends only on these public numbers,
not on the oracles. With `d = fDeg Q τ qbar ε` the filter degree,
`2^m ≥ steps(τ, ε/3)` time slots (`simM`) and `2^r ≥ 2d + 2` (`simR`), it is
one oblivious amplification round `L Z L† Z L` (times `-1`) of the LCU circuit
`L`, which prepares the signed branch table and the uniform pointer state of
every branch, runs `N = 2d` reuse steps (private call, `U_J`-conjugated
boundary network at the current pointer word, pointer increment), and
unprepares. `d` and `2^m` here follow the package schedule. Theorem
`hs:thm:gates` with eqs. `hs:eq:gate-schedule` and `hs:eq:gate-clocks` is
`SparseHamiltonian.GateSchedule.gate_efficient_simulation_ms` (exact gates;
`GateEfficientSchedule/Endpoint.lean:123`) and
`SparseHamiltonian.GateSchedule.sel_simulation_ms` (finite gate set;
`GateEfficientSchedule/Selective.lean:150`).

**Guarantees** (`gate_efficient_simulation`):

* every instruction is a valid elementary instruction;
* exactly `6d` private Cayley calls and exactly `12d` calls of `U_J` or `U_J†`;
* at most `200 (d+1)(a+m+r+1)` elementary gates;
* `2a + 3m + 6r + 3` qubit wires besides the system;
* `‖run (simSem U_J D) (simCircuit …) ∘ io - io ∘ exp(-iτH)‖ ≤ ε`: the full
  output, including every work register, is within `ε` of the clean evolved
  state;
* `d ≤ 128 (τ qbar + Q (1 + log(3/ε)))`, `steps ≤ 2^m < 2 steps` and
  `2d + 2 ≤ 2^r ≤ 4(d + 1)`.

**Proof map.** Module paths are relative to `GateEfficientHamiltonian/Circuit/`.

* Dyadic compression of the chronological boundary network, equation
  `gate:eq:dyadic`: `Dyadic` (`chron_eq_compressed`, `chron_closed`).
* The network on the register and its transducer blocks:
  `NetLift`, `NetIdeal` (`NET_emb`, `chron_boundary`), `Select` (`BNET_emb`,
  `blkB_net`, `blkC_net`, `blkG_net`).
* The factorisation `hs:eq:gate-transducer` and one reuse step: `Select`
  (`STEP_emb`); the pointer increment `INC_emb`.
* Successive reuse and equation `hs:eq:gate-reuse-block`: `Select`
  (`select_block`) with the released `CoherentReuse`.
* The filter state, uniform pointer states and the LCU block: `Tree`,
  `Range`, `LCU` (`lcu_block`).
* Amplification and error: `Amplify` (`AMP_io`, `lcu_compression`,
  `amp_error`), with `GateEfficientHamiltonian/Simulator/BlockTransfer.lean`
  (`amplified_error_le`).
* Gate-level implementations, agreeing with the ideal operators on clean
  configurations (`Impl`): boundary network with prefix-flag chains `GNet`
  (`net_agrees`), ripple increment `GInc` (`inc_agrees`), uniform pointer
  states `GRange` (`range_agrees`), the label table and the clean reflection
  `GPrep` (`prep_agrees`, `zr_agrees`), assembly `GSim` (`amp_agrees`).
* Unitarity and clean invariance of the ideal operators: `Ideal`.
* Instruction counts: `GCount` (`ampI_counts`); the final theorem: `Theorem`.

**Formalization choices.**

* The branch labels are the released finite list `ReuseWeights.Index d`
  (`2(d+1)` branches with the signed smoothing weights; the zero-length branch
  has weight zero and length one), with the signs in the output preparation.
  This gives the same successful block as the paper's state with label `⊥`.
* The uniform pointer state `|u_n⟩` is prepared exactly by a binary tree of
  rotations: a Hadamard-type rotation below prefixes smaller than that of `n`
  and a fixed rotation below the prefix of `n`, using one tight flag per bit,
  instead of an attenuated preparation with amplitude amplification. The cost
  is again `O(r)` gates per label.
* The reuse loop has `N = 2d` steps independent of the label; a branch of
  length `n` reads only the public pointer words below `n`.
* The error budget is `ε/3` for the filter (doubled by amplification) and
  `ε/3` for the Cayley subdivision.
* Gates are exact: rotation angles are exact reals. Finite-gate-set synthesis
  (equation `hs:eq:gate-total`), approximate private Cayley implementations
  with error `ξ`, the native sparse instantiation of `U_J` and `D`, the
  binary-entry corollary (equation `hs:eq:gate-binary`) and negative times are
  not formalised here.

The modules `GateEfficientHamiltonian/Gate*.lean` are the earlier milestone
development (exact frame gate lists, pointer encodings, range and table
preparations); the final theorem uses its dyadic-boundary scalars, pointer
encoding and binary reuse model.
-/
