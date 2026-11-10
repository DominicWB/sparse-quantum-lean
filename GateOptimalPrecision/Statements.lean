import GateOptimalPrecision.Main
import GateOptimalPrecision.LocalFactor
import GateOptimalPrecision.JointAlgebra
import GateOptimalPrecision.NativeMain
import GateOptimalPrecision.ControlledLocator

set_option autoImplicit false

/-!
# Theorem `gate:thm:main` (gate-efficient improved-precision simulation): paper-to-Lean entry point

Theorem `gate:thm:main` of the manuscript (Section `gate:sec:result`, proved in Appendix
`gate:sec:proof`) gives an elementary-gate implementation of the improved-precision
time-independent simulators of Theorems `hs:thm:two-norm` and `hs:thm:optimal`: the theorem
(two-norm form) and its single-norm case ("Taking `μ = η` gives the gate implementation of Theorem
`hs:thm:optimal`"), built from a compiler for chronological products and signed reuse (Section
`gate:sec:compiler`: Lemma `hs:lem:boundary`, Lemma `gate:lem:reuse`, Proposition
`gate:prop:finite`), the signed-factor construction (Section `gate:sec:signed`, Proposition
`gate:prop:signed`), the reduced-entry (clipped-transducer) construction (Section `gate:sec:core`,
Proposition `gate:prop:core`), and native signed factors, controls and reversible arithmetic
(Section `gate:sec:native`), combined in Section `gate:sec:combine`.
References to the manuscript use its labels.

This library formalises these results at the level of the released gate model of the baseline gate
theorem. No result from another paper is used: the analytic inputs ("The moment and contour
estimates are those proved in Appendices `opt:sec:proof` and `twonorm:sec:proof`") are the released
query-level libraries `SignedFactorSimulation`, `LargeSparsityCore`, `OptimalSparseSimulation` and
`TwoNormSimulation`, and the gate model, the boundary network and the native macros are those of
`GateEfficientHamiltonian` and `GateEfficientNative`. Every theorem of the library is axiom-audited
in `GateOptimalPrecision/Audit.lean`.

**Naming convention.** All declarations are in the namespace `GateOptimalPrecision`; names below
are relative to it, except the names of other libraries, which are fully qualified. In the gate
model (`SparseHamiltonian.GateCircuit`), a released circuit is a list of instructions on the wires
`Wire a m r K` (`a` ancilla qubits, `m` slot bits, `r`-bit pointer and label words, `K` work
wires and the sector wire) acting on a payload `P` (the system): elementary gates (a one-qubit
unitary with at most three literal controls), calls of the boundary `U_J` and calls of the private
operation `D` (each with literal controls), with `nGates`, `nUJ`, `nPriv` counting them. `run`
is its operator, `io` the clean embedding, and `‖run … ∘L io - io ∘L U‖` its full-output error.
In the native model (`SparseHamiltonian.GateNative`) a native circuit is a list of elementary
gates and uncontrolled calls of supplied primitive oracles `prim j` (`nGatesN`, `nCallsN`) on
qubit wires with an untouched payload `R`; `sysEmb io` is the clean embedding of the system
qubits `S`.

## The model of the statements

* Gates: the manuscript counts "gates outside the supplied value and locator oracles" (Section
  `gate:sec:result`) and, before finite-set synthesis, decomposes "the remaining known gates with
  at most three controls" (proof of Proposition `gate:prop:finite`). Here every one-qubit unitary
  with at most three literal controls is one elementary gate; finite-set synthesis (the finite-gate
  assumptions of Section `gate:sec:result`: "An arbitrary one-qubit unitary can be synthesised to
  error `ζ` with `O(log(1/ζ))` gates for `0 < ζ ≤ 1/2`", Ref. KMM2013) is not part of this library;
  it is applied to the binary endpoint in `GateOptimalBinary.gate_optimal_binary_synth`, with the
  single-qubit synthesis result as the hypothesis `SparseHamiltonian.GateSynth.Synthesis`.
* Accuracy: the error on all output registers, eq. `gate:eq:full`, which "includes every work
  register and an untouched reference"; the system space is any finite-dimensional space, so an
  untouched finite reference is included.
* Interfaces: the private operation of each regime is given on a gate register by its interface
  (`BoundedIface`, `SignedIface`, `ClippedIface`), required only in its own regime. In the paper
  these are the native sparse constructions of Section `gate:sec:native`; here that the sparse
  oracles meet each regime's representation and factor identities enters as a hypothesis on the
  gate register, as do the native identities and the accuracy of the arithmetic in the native form
  below. For binary sparse oracles the library `GateOptimalBinary` constructs every interface and
  every native identity (`GateOptimalBinary.gate_optimal_binary`).

## Section `gate:sec:compiler`: a compiler for chronological products and signed reuse

* **Lemma `hs:lem:boundary`** (boundary compression) is the boundary network of the baseline gate
  theorem, reused unchanged: the factorisation of Ref. CGJLWZ
  (`SparseHamiltonian.GateCircuit.Dyadic.chron_eq_compressed`, with the proof of Lemma
  `hs:lem:boundary`) and its gates (`SparseHamiltonian.GateCircuit.Sim.net_agrees`;
  `SparseHamiltonian.GateCircuit.Sim.netGates_length`: at most `4(a+r) + 8m + 5` gates).
* **Lemma `gate:lem:reuse`** (compiled signed reuse, module `Reuse`). `netTransfer c σ J D m` is the
  causal transfer `F(w) = A + wB(I - wD)⁻¹C` of the chronological product on `2^m` slots
  (`gate:eq:global`, `gate:eq:transfer`); `lcu_ces`: the clean block of the ideal operator `LCU` of
  the released LCU circuit is `∑_ℓ (wt_ℓ/2) Ces_{n_ℓ}(F)`; `lcu_ces_pad`: for weights with
  `∑ |w_j| ≤ A₀` (completed by two cancelling branches, `padWt`, `padLen`) the block is
  `A₀⁻¹ ∑_j w_j Ces_j(F)` (`gate:eq:lcu`); **`lcuI_ces_pad`**: the same block for the released
  circuit `SparseHamiltonian.GateCircuit.Sim.lcuI` run with the oracles `U_J` and `D`;
  `netTransfer_cascade`: for the Cayley boundary scalars the transfer is the cascade transfer of the
  query proof. The counts are those of the released LCU circuit
  (`SparseHamiltonian.GateCircuit.Sim.lcuI_counts`).
* Amplification (module `Amplify`): `ampIt l k` is `k` rounds of the released oblivious
  amplification, `k_o = 3^k` calls of the base circuit or its inverse; `ampOp_error`: for a
  unitary circuit operator `X` and a unitary `W`, a block within `e₀` of `sin(π/(2·3^k)) W` with
  `7^k e₀ ≤ 7/16` gives full output within `√(2·7^k e₀)` of `io W`; `ampIt_counts`.
* **Native-model form of Proposition `gate:prop:finite`, before finite-set synthesis** (explicit
  resource bound): the replacement of every private
  call by its native implementation, with telescoping of the full-output error and the actual
  adjoints of the implemented circuits, is the native transfer below (`native_transfer`: `4ζ` per
  edge-rotation call; `signed_transfer`: `3ζ` per factor call). `gate_optimal_native_total` keeps
  the paper's ideal budget `ε/2`; since synthesis over a finite gate set is not part of this
  library, the private calls get the remaining `ε/2` (the paper splits it as `ε/4` for the private
  calls and `ε/4` for synthesis; `GateOptimalBinary.gate_optimal_binary_synth` adds a synthesis
  budget for binary sparse oracles).

## Native-model form of Proposition `gate:prop:signed`, before finite-set synthesis

The signed-factor gate bound. This section gives its exact-gate part, with abstract unitaries
`U_J`, `U_B`; the form with native factors is `signed_native_simulation`, in Section
`gate:sec:native` below. The factor interface on `a` ancilla qubits (`SignedLayout`):
`wKnown U_J f z`, the factor
`B = Π U_B U_J ι₀` with success wire `f` and sign wire `z` (`gate:eq:factor`); the attenuation by a
known flag rotation on one more ancilla (`attKnown`, `attKnown_factor`, `attKnown_Cop`,
`attKnown_Dop`); the private operation `P = U_B† G U_B` (`gate:eq:factor-private`) with "only the
three known middle phases" under the sector control: `privExpand`, `run_privExpand` (an
unconditional factor call, three phase gates `phaseGates`, an unconditional inverse factor call),
`ujExpand`, `run_ujExpand`, `run_expand`, `expand_counts` (module `SignedExpand`). The circuit
(`SignedCore`): `sigBase` (the LCU with the padded clock table), `sigAmp` (`3⁸` amplification
calls), `sigCircuit`; `sig_block`, `sig_core`, `sig_counts`, `sig_mesh`.

**`signed_gate_simulation`** (`SignedTheorem`). For unitaries `U_J`, `U_B` on `a` ancillas and
the system with `D = B†B ⪯ δ I`, `0 < δ ≤ 1`, `λ > 0`, `H = λ B†ZB` and `0 < ε ≤ 1/64`, the circuit
`sgCircuit a f z λ δ t ε` (the identity if `b = λ|t|δ ≤ ε`, the inverse circuit for `t < 0`) is
valid, makes `nPriv ≤ 4·10¹⁰ (√(Tb) + √(T r_b) + r_b)` calls of `U_B` or `U_B†` (`T = λ|t|`,
`r_b = L/log(e + L/b)`), the same number of calls of `U_J`, at most `64·3⁸ (n+1)(a+m+r+1)`
elementary gates on `2a + 3m + 6r + 5` auxiliary qubits (the system is the payload),
`2^m ≤ 10⁷ n⁴/ε` when `ε < b`, and `2^r < 2(n+2)`, and its full output is within `ε` of
`e^{-itH}`.

## Native-model form of Proposition `gate:prop:core`, before finite-set synthesis

The clipped-transducer gate bound. This section gives its exact-gate part, with abstract unitaries
`U_J`, `D`; the native private calls are in Section `gate:sec:native` below and in
`GateOptimalBinary.clip_transfer`.

`ClippedCore`: the large-sparsity core on any mesh of `T ≥ N_s` slots
(`core_implementation_mesh`, `filter_estimate_mesh`: "This is allowed by the analytic proof").
**`clipped_gate_simulation`**, `clipped_gate_simulation_neg` (`ClippedTheorem`): under the core
hypotheses `LargeSparsityCore.Core.CoreData` in the regime `LargeSparsityCore.Parameters.Regime`,
the circuit `clipCircuit` (the smoothing table of the product filter, `2d` reuse steps, one
amplification round, `2^m ≥ N_s` slots) is valid, uses exactly `6d` private calls and `12d`
boundary calls, at most `200(d+1)(a+m+r+1)` elementary gates on `2a + 3m + 6r + 3` auxiliary
qubits, and its full output is within `ε` of `e^{-i a J†KJ}`; `d ≤ 21520 √(sτr)`.

## Theorem `gate:thm:main` and its single-norm case

With `sμ² = ση²` and `θ = η²|t|/μ` (`gate:eq:effective`; `two_norm_params`: `σ ≥ 1`,
`√σ θ = √s η|t|`, `σθ = sμ|t|`) and `Q_μ = √s η|t| + √(sμ|t| r_μ) + r_μ`, `r_μ = L/log(e + L/θ)`
(`Qmu`):

* the bounded regime (`Bounded`): the baseline Cayley construction with the generator `K₀`
  (`BoundedIface`: `‖K₀‖ ≤ √σ`, `‖K₀J₀‖ ≤ 1`, `J₀†K₀J₀ = H/(√s η)`) and the public rescaling of the
  baseline, `bounded_gate_simulation`, `bounded_gate_simulation_neg`;
* `GateClaims UJ D l H t ε Q` (`Combine`): `l` is valid and unitary, `nPriv l ≤ 2·10¹¹ Q`,
  `nUJ l ≤ 2·10¹¹ Q`, `nGates l ≤ 10¹³ (Q+1)(a+m+r+1)`, at most `2a + 3m + 6r + 5` auxiliary
  qubits (the wires of `l`; the system is the payload), `2^m ≤ 10³⁶ (Q+1)⁴/ε` (so
  `m = O(log((Q+1)/ε))`), `2^r ≤ 10⁸ (Q+1)`, and full-output error at most `ε` for `e^{-itH}`;
  `bounded_branch`, `signed_branch`, `clipped_branch`.

**Theorem `gate:thm:main`** (`gate_optimal_simulation`, exact gates). For `μ ≤ η ≤ √s μ`, `θ ≥ 1`,
`0 < ε ≤ 1/64` and self-adjoint `H`, with the interface of each regime required only in that
regime, according to the regime (`h = log(e + L/θ) < 10⁴`; `h ≥ 10⁴` and `σθ < Lh`; `h ≥ 10⁴`
and `σθ ≥ Lh`) the circuit `bdSigned`, `sgCircuit` or `clipSigned` satisfies `GateClaims` with
`Q = Q_μ`. **The single-norm case** (`gate_optimal_simulation_single`): `μ = η`, `Q_η = Q` (`Qone`,
`Qmu_self`).

## Section `gate:sec:native`: native signed factors, controls and reversible arithmetic

**The stable three-qubit factor** (paragraph "A stable constant-dimensional signed factor")
(`LocalFactor`). `eMat`, `vMat`, `piP`, `piM`, `tMat`, `aMat`, `rMat`, `uMat` are `E(c)`, `V_φ`,
`Π_±`, `T_φ`, `A_φ`, `R_u`, `U(c)`; `eMat_eq`, `bP_sq`, `bM_sq` (`gate:eq:local-factor`), `tMat_eq`,
`uMat_eq` (the block form of `gate:eq:dilation`), `uMat_unitary`, `uMat_action`
(`gate:eq:factor-action`), `uMat_gates` (five gates: `V_φ`, Toffoli, `R_u`, Toffoli, `V_φ†`),
`uMat_zero`, `norm_uMat_sub_one_le` (`gate:eq:small`: `‖U(c) - I‖ ≤ 1 - √(1-u) + √u ≤ 2√u` on all
inputs), `norm_uMat_sub_zero_le` (`u ≤ ξ²/16` may be replaced by zero with error at most `ξ/2`),
`norm_uMat_sub_le_of_accuracy` (magnitude accuracy `ξ²` and phase accuracy `ξ` give error at most
`3ξ`).

**The gates of `U(c)`** (`LocalGates`, on three wires of any register, via `BlockOp`). The angle
word encodes `α ∈ [0, π/2]` (`alphaVal`) and the phase word `φ` (`phiVal` of the baseline);
`locGates` are the phase gates `diag(e^{-iφ_j}, 1)` on the orientation qubit (one per bit, under
that bit), `H`, the Toffoli gate `f, o → z`, the rotations `R_y(2α_j)` on the flag (one per bit),
the Toffoli gate, `H` and the phase gates `diag(e^{iφ_j}, 1)`: `2 b_P + b_T + 4` gates with at most
two controls (`locGates_length`, `locGates_ok`). `gRun_locGates`: they act as the block
`uImpl α φ`, and `uImpl_eq_uMat`: `uImpl α φ = U(sin² α e^{iφ})`. `norm_uImpl_sub_le`: if either
`‖c‖ ≤ ξ²/16` and `α = 0`, or `|sin² α - ‖c‖| ≤ ξ²` and `|e^{iφ} - c/|c|| ≤ ξ`, then
`‖uImpl α φ - U(c)‖ ≤ 3ξ`; `norm_matOp_blk_le` transfers the matrix norm to every payload.

**The joint private operation** (paragraph "Sparse preparation and the joint private operation")
(`JointAlgebra`). `clip_split` (`gate:eq:clip`), `norm_corrE_le_one`, `norm_bulk_le` (`|y| ≤ 2q/β`;
the manuscript's clipping parameter is `β = h_a`), `edgeMat_cayley` and `edgeMat_unitary`
(`gate:eq:cayley`: `D(y)` is the Cayley transform of `E(y)`), `edgeMat_zero` (`D(0) = -I`),
`norm_edgeMat_add_one_le` (`‖D(y) - D(0)‖ ≤ 2|y|`), `hMat_edgeMat_hMat` (the correction phases
`(±2q + i)/(±2q - i)` and the signed-factor phases are edge rotations in the Hadamard basis).

**The native form** (`NativeCayley`, `NativeFactor`, `NativeSigned`, `NativeMain`). The
sector-controlled private calls of the bounded and clipped circuits are replaced by the
compute–rotate–uncompute macro of the baseline gate theorem (`nativeOf`; "For conjugated private
calls control only the middle local operation"), with the native identity `V† R V = D`
(`SparseHamiltonian.GateNative.NativeOK`) and the accuracy `ζ` of the angle arithmetic
(`SparseHamiltonian.GateNative.ArithOK`) as hypotheses. The unconditional factor calls of the signed
circuit are replaced by the native factor of the paragraph "Sparse preparation and the joint private
operation" of Section `gate:sec:native` ("We compute the value word while retaining the entry
indices, perform the local operation on its three separate qubits, and uncompute the value"):
`FactorOp` (the compute circuit `W`, the flag, orientation and sign qubits, the decoded entry `c`,
and the reversible arithmetic of the angle and phase words), `factorMacro` (`W`, the arithmetic,
`locGates`, the inverse arithmetic, `W†`), with the public conditions `FactorOp.Public` (the decoder
does not read the three qubits, `‖c‖ ≤ 1`), the arithmetic hypothesis `FactorArithOK fo ζ` (the
threshold branch or magnitude accuracy `ζ²` and phase accuracy `ζ`) and the native identity
`FactorNativeOK` (`W† U(c) W = U_B` on clean scratch) as hypotheses. Every boundary call is replaced
by the gates of `U_J` under the sector wire.

* `native_transfer`, `signed_transfer`: from the full-output error `ε₀` of a released circuit to
  `ε₀ + 4ζ nPriv` (resp. `ε₀ + 3ζ nPriv`) for the native circuit, with exact primitive-call counts
  and gate counts `nGates + 7 C_J nUJ + G_C nPriv`, where `C_J = |UJg|` and the gates of one
  native private call are `G_C = 2|V| + 2|circ| + 2 b_P + b_T + 1` for the Cayley macro and
  `G_C = 2|W| + 2|circ| + 2 b_P + b_T + 4` for the factor (`circ` the arithmetic);
  `factorMacro_approx`, `factorMacro_inv_approx` (within `3ζ` of `U_B`, and the actual adjoint
  within `3ζ` of `U_B†`; `arith_block_agrees`, `arith_loc_agrees`, `Util_approx`); `UJop_shiftG`
  (the gates of `U_J` on the last `a` of `a + 1` ancillas); `uncOK_sgCircuit`;
* `signed_native_simulation`: native-model form of Proposition `gate:prop:signed`, before finite-set
  synthesis, with native factors (`sgNative`);
* `NativeClaims prim C H t ε Q calls G δ`: the native circuit `C` is valid and unitary, makes at
  most `2·10¹¹ Q · calls p` primitive calls of each kind `p`, has at most
  `10¹³ (Q+1)(a+m+r+1) + 2·10¹¹ Q G` elementary gates on at most
  `2a + 3m + 6r + 5 + |S| + |Z| + b_T + b_P + A + 3` wires (with the system qubits),
  `2^m ≤ 10³⁶ (Q+1)⁴/ε`, `2^r ≤ 10⁸ (Q+1)`, and its full output is within `δ` of `e^{-itH}`; the
  native data of a regime are `CayleyNative` (per call `calls = 2 nCallsN V`, `G = 7 C_J + G_C`,
  `δ = ε + 2·10¹¹ Q · 4ζ`) and `FactorNative` (`calls = 2 nCallsN W`,
  `G = 7 C_J + 2|W| + 2|circ| + 2 b_P + b_T + 4`, `δ = ε + 2·10¹¹ Q · 3ζ`);
* **`gate_optimal_native`** (Theorem `gate:thm:main`, native form) and
  **`gate_optimal_native_single`** (the single-norm case, native form): in each regime the native
  circuit satisfies `NativeClaims` with `Q = Q_μ` (resp. `Q`); **`gate_optimal_native_total`**,
  `gate_optimal_native_single_total`: with the exact-gate construction at `ε/2` and
  `32·10¹¹ Q ζ ≤ ε` (`Q` at `ε`), `NativeClaims` hold at `ε/2` with the count parameter `2Q`
  (`Qmu_half_le`: `Q_μ(ε/2) ≤ 2 Q_μ(ε)`) and the full output is within `ε` of `e^{-itH}`
  (`gate:eq:full`).

**Controls on native locators** (paragraph "Controls on native locators") (`ControlledLocator`). For
a primitive locator `U` on `w`-bit words with `U|x_*⟩ = |y_*⟩` (`y_*` need not be known),
`ctrlLoc j x_*` is the construction of the manuscript: the two-query reference preparation `prepL`
(`U`, a copy `copyG`, `U†`), the swap with a dummy on the inactive branch (`swapG`),
`V = W_{y_*}† U` (one query and the XOR translation `xorG`), the swap undone, the controlled
`W_{y_*}` and the reference preparation again. **`ctrlLoc_agrees`**: on clean work wires
(`LocClean`: the reference and the dummy in `x_*`) it is exactly the controlled `U` (`ctrlU`), for
every unitary `U` with the prescribed action at `x_*`; `ctrlLoc_inv_agrees`: the reversed circuit
controls `U†`; `ctrlLoc_nCalls` (five queries), `ctrlLoc_nGates` (at most `12w` gates),
`ctrlLoc_valid`, `card_LocW` (`4w + 1` wires). On zero work wires (`LocZero`), **`ctrlLoc0`** also
prepares and resets the reference and the dummy with `X` gates (`setG`): `ctrlLoc0_agrees`,
`ctrlLoc0_inv_agrees`, `ctrlLoc0_nCalls` (five queries), `ctrlLoc0_nGates` (at most `16w` gates),
`ctrlLoc0_valid`.

## Scope and differences from Appendix `gate:sec:proof`

* Gate counts are explicit in the supplied per-call costs: `C_J = |UJg|` gates of `U_J`, and the
  lengths of the compute circuits and of the arithmetic circuits. The paper's assumption that these
  are polynomial in `b_data`, the index widths and `log(1/ξ)` ("These assumptions concern
  calculations on a single loaded entry or a known scalar parameter.") is not formalised, so the
  polynomial form of `gate:eq:main-gates` is not stated; with it, the bounds of `NativeClaims` give
  that form.
* Not formalised here: finite-set synthesis (Ref. KMM2013); the dyadic rounding of the signed
  weights (`gate:eq:round`) and the classical compilation of the tables (the gates are exact
  rotations with the real weights of the query proof); the derivation of the interfaces and of the
  native identities from the sparse oracles (they enter as hypotheses). The library
  `GateOptimalBinary` derives the interfaces and native identities from binary sparse oracles and
  applies finite-set synthesis under the synthesis hypothesis
  `SparseHamiltonian.GateSynth.Synthesis` (one-qubit gates with at most three controls; by
  `Synthesis.of_parts` it follows from single-qubit synthesis and an exact decomposition of the
  controlled gates); there the scalar arithmetic of the signed and clipped regimes remains a
  hypothesis.
* Preparation: the branch tables and the uniform pointer states are prepared exactly by the released
  binary trees of rotations of the baseline (`lcuI`), not by the Möttönen preparation or the
  one-Grover-round fixed-range preparation of the manuscript; the counts are those of the released
  circuit.
* Padding (Lemma `gate:lem:reuse`): weights with `∑ |w_j| < A₀` are completed by two branches of
  length one with opposite weights `±(1 - ∑ |w_j|/A₀)` (`padMass`), which cancel in the block, in
  place of the manuscript's dummy branch with a rejection flag.
* Regimes: the split uses `L = log(1/ε)` and `h = log(e + L/θ)` at the target accuracy `ε`
  (`LargeSparsityCore.Parameters.Lval`, `LargeSparsityCore.Parameters.hval`), not
  `L_a = log(2/ε)` and `h_a` at `ε_a = ε/2`; the split is exhaustive either way. In the signed
  regime the trivial case is `b = λ|t|δ ≤ ε` (the empty circuit, valid since
  `‖e^{-itH} - I‖ ≤ λ|t|δ`) rather than `b_f ≤ ε/2`.
* The native signed factor uses bit-controlled phase gates and rotations `R_y` (arbitrary one-qubit
  gates are elementary) and an angle word for `arcsin √u`, with the paper's accuracy split
  ("magnitude accuracy of order `ξ²` and phase accuracy of order `ξ`") as the arithmetic
  hypothesis; the native Cayley macro is that of the baseline gate theorem.
* Constants follow the query proofs: `k_o = 3⁸` amplification calls with `s₀ = sin(π/(2·3⁸))` in
  the signed regime, the error budgets of `SignedFactorSimulation` and of the large-sparsity core,
  and the public rescaling of the baseline in the bounded regime. The constants `2·10¹¹`,
  `10¹³`, `10³⁶` and `10⁸` of `GateClaims` are uniform over the three regimes.
* The clipped regime uses the parameters and the error split of the large-sparsity core
  (`LargeSparsityCore/Statements.lean`) in place of the manuscript's `Q₀`, `B₀` and filter
  constants.
-/
