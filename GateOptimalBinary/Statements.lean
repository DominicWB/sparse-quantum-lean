import GateOptimalBinary.Tables

set_option autoImplicit false

/-!
# Theorem `gate:thm:main` from binary sparse oracles: paper-to-Lean entry point

The library `GateOptimalPrecision` proves Theorem `gate:thm:main` (gate-efficient
improved-precision simulation) for a private operation given on a gate register by its interface
(`BoundedIface`, `SignedIface`, `ClippedIface`) and, in native form, for native identities and
arithmetic accuracies supplied as hypotheses (`CayleyNative`, `FactorNative`). This library
constructs every interface and every native identity from the binary sparse oracles of
`GateEfficientBinary` (Section `gate:sec:native`, paragraphs "Sparse preparation and the joint
private operation" and "A stable constant-dimensional signed factor"), and applies the generic
finite-gate-set synthesis of `GateEfficientSynthesis` to the resulting circuits. The remaining
hypotheses are the scalar-arithmetic assumptions of Section `gate:sec:native` for the signed and
clipped regimes ("Standard efficiently decoded binary or fixed-point data satisfy the
scalar-arithmetic assumption"; the angle arithmetic of the bounded regime is the CORDIC circuit of
`GateEfficientBinary`, whose accuracy and counts are proved), each required only in its own
regime and met at every accuracy by reversible lookup tables (`Tables`, with gate counts exponential
in `b`), and, for finite gate sets, the synthesis hypothesis `SparseHamiltonian.GateSynth.Synthesis`
for one-qubit gates with at most three controls (by `SparseHamiltonian.GateSynth.Synthesis.of_parts`
it follows from single-qubit synthesis, the external result of Ref. KMM2013, which is not reproved,
and an exact decomposition of the controlled gates). References to the manuscript use its labels.
Every theorem of the library is axiom-audited in `GateOptimalBinary/Audit.lean`.

**Naming convention.** All declarations are in the namespace `GateOptimalBinary`; names below are
relative to it, except the names of other libraries, which are fully qualified.

## The binary sparse oracles

The data are `NativeSparseBlockEncoding.Data` with `k`-bit indices (`en : Cfg (Fin k) ≃ n`),
`s = 2^{s_b}` slots enumerated by the low words of the index (`hrange`), and entries stored as
`b`-bit two's complement components with the decoder `c₀(X + iY)` (`hdec`). The primitives are the
row-location, column-location and value oracles (`SparseHamiltonian.GateBinary.prims`); the
compute circuit `SparseHamiltonian.GateBinary.computeV` makes `2` row, `2` column and `1` value
calls (`computeV_calls_total`: `5` calls) with `28 k` gates, and the scratch register `SZ k b` has
`6k + 2b` qubits (`SparseHamiltonian.GateBinary.card_SZ`). The represented Hamiltonian is the qubit
lift `sysH D en x` of `D.matrix x` on the `k` system qubits.

`BinaryInput D en sb c₀ x η μ` collects the hypotheses on the data and the input: `s = 2^{s_b}`,
`s_b ≤ k`, the slot range, `b > 0`, `c₀ > 0`, the decoder, and that `D.matrix x` is Hermitian with
row and column Euclidean norms at most `η` and entries of modulus at most `μ`. `MainParams` collects
the parameters of Theorem `gate:thm:main`: `μ ≤ η ≤ √s μ`, `sμ² = ση²`, `θ = η²|t|/μ ≥ 1`,
`0 < ε ≤ 1/64`.

## The bounded regime (`Bounded`)

`bdK`: the generator `K₀ = √σ E_H` of the normalised data with the boundary `U_J = hadUJ`;
`boundedIface` (`GateOptimalPrecision.BoundedIface`: `‖K₀‖ ≤ √σ`, `‖K₀J₀‖ ≤ 1`,
`J₀†K₀J₀ = H/(√s η)`); `bdPriv_elift`: the private Cayley operation of the bounded circuit is the
qubit lift of the baseline private Cayley operation, so the native identity
`SparseHamiltonian.GateBinary.sparse_nativeOK` applies; `boundedNative`
(`GateOptimalPrecision.CayleyNative`), with the CORDIC arithmetic at accuracy `ζ`.

## The signed-factor regime (`FactorLayout`, `FactorLocal`, `SignedIface`, `SignedNative`)

The factor register `GU k` (`k + 3` ancillas: the bounded edge register, the flag `f` and the sign
`z`); `uMat_sign_block`, `uMat_weight_block`: the compressions of `U(c)† Π Z Π U(c)` and
`U(c)† Π U(c)` to the initial block are `E(c)` and `|c| I`; `sgUJg` (the boundary), `UF` (the factor
`U_B = F† U(c) F` with the lifted locator), `sg_Cop`, `sg_Dop`, `signedIface`
(`GateOptimalPrecision.SignedIface`: `H = sμ B†ZB`, `B†B ⪯ σ^{-1/2} I`). The native factor `sgFO`
(the compute circuit on the bounded wires, the decoder `clip((c₀/μ)(X + iY))`, the local qubits and
the factor arithmetic of the hypothesis `FactorWordArith`); `sgFO_native`
(`GateOptimalPrecision.FactorNativeOK`); `signedNative` (`GateOptimalPrecision.FactorNative`).

## The clipped regime (`ClipLocal`, `ClipOps`, `ClipLayout`, `ClipIface`, `ClipMoments`, `ClipCore`)

The joint private operation of the clipped transducer (`twonorm:eq:joint`) on `k + 4` ancillas
(`PRf k`: the branch `g`, the factor register): the entries clipped at `μ` with `β = h`
(`cl1 = c₁`, `cl2 = c₂`); the frame `W = A F` (the lifted locator and, on the correction branch,
`U(c₂)`); in the frame `K = 2q E(y)`, `D = D(y)` (the edge rotation) and `P_± = [g = 1][f = 1] Π_±`
on the orientation qubit, `y = [g = 0] 2q c₁ + [g = 1][f = 1] 2q e^{iφ}` (`LK`, `LD`, `LP`, `LM`);
the boundary `clUJg` (the Hadamard gates of the bounded regime and one on the branch).

* `clip_spectral` (`LargeSparsityCore.CayleyBlocks.Spectral`), `clD_isometry`, `clD_isUnitary`;
* `uMat_fblk_block`: the local factor enters the compressions only through its action on the
  initial block; `clip_compress`, `cj_compress`: the compression of a located operation is the
  qubit lift of an edge compression by the sparse boundary `J₀`;
* `edgeOp_P`, `edgeOp_M`, `edgeOp_KK`, `edgeOp_B`, `edgeOp_K`: the edgewise operators `|c₂|Π_±/2`,
  `2q²(|c₁|² + |c₂|) I`, `2q²|c₁|² I` and `q E(c₁ + c₂)`;
* `clip_bulk_le` (`‖R₁(K) P₀‖ ≤ Q₀`), `clip_isoP_sq`, `clip_isoM_sq`, `clip_moment_sq`,
  `clip_second_sq` (with `ρ = η²/μ²`: `βρ/(2s)`, `2q²ρ/s`, `2q²(1 + β)ρ/s`), and
  **`clip_coreData`**: the hypotheses `LargeSparsityCore.Core.CoreData` with the moment parameter
  `σ` (`sμ² = ση²`);
* `clip_compress_K`: `J†KJ = H/α`, `α = sμ/q`, for entries of modulus at most `μ`;
* **`clippedIface`** (`GateOptimalPrecision.ClippedIface`).

## The native clipped private operation (`ClipTransfer`, `ClipNative`)

The private Cayley unitary of the clipped interface is `D = U_f† C U_f` (`clD_split`): the factor
`U_f = F† A F` (`Uf`) and the rotation `C = F† D(y) F` (`Cf`). The unitary `D` itself does not have
the compute–rotate–uncompute form of `GateOptimalPrecision.CayleyNative`; its pieces are native
(the rotation `C` has that form, and `U_f` is a native factor):

* `ClipNative` (generic): the native factor of `U_f` (`FactorOp`, `FactorArithOK` at accuracy `ξ`,
  `FactorNativeOK`) and the native rotation of `C` (`NativeOp`, `ArithOK` at accuracy `ζ` on the
  same arithmetic wires, `NativeOK`); `ClipNative.pc`: the native factor, the native rotation and
  the literal inverse of the native factor; `ClipNative.pc_approx`: within `6ξ + 4ζ` of the
  enable-controlled `D` on clean work wires (`ideal_conj`: `U†(ctrl C)U = ctrl(U†CU)`);
  `ClipNative.calls_eq` (`4|W|_calls + 2|V|_calls`), `ClipNative.pc_nGates`;
* `clip_transfer`, `clip_claims`: the transfer with the supplied private circuit of
  `SparseHamiltonian.GateSelective.hcircP`; **`gate_optimal_native_clip`**,
  `gate_optimal_native_clip_total`: `GateOptimalPrecision.gate_optimal_native` with this private
  call in the clipped regime (full-output error `ε + 2·10¹¹ Q_μ (6ξ + 4ζ)`), and the native factor
  of the signed regime at accuracy `ξ`;
* the binary instances: the native factor `clFO` (decoder `[g] c₂` of the branch and the value word,
  `cfdec`; the factor arithmetic of the hypothesis `ClipFactorArith`), the native rotation `clND`
  (decoder `y(g, f, c₁, c₂)` of the branch, the flag and the value word, `ckdec`; the angle
  arithmetic of the hypothesis `ClipAngleArith`), `clFO_native` (`FactorNativeOK`), `clND_native`
  (`NativeOK`), and **`clipNative`**.

The native call computes the value word three times (in the native factor, the native rotation and
the inverse native factor): six compute circuits, `30` oracle calls per private call, where the
manuscript's single computation would use `10`. The difference is a constant factor; a fused call
is not formalised.

## The binary endpoint (`Main`)

`binIB`, `binNB`, `binIS`, `binNS`, `binIC`, `binNC`: the interfaces and native data of the three
regimes (the arithmetic of the signed and clipped regimes as functions of the regime conditions);
`bdNativeCircuit`, `sgNativeCircuit`, `clNativeCircuit` (with `clipPC`): the native circuits;
`bdNativeCost`, `sgNativeCost`, `clNativeCost`: the gates of one native boundary call and one native
private call; `bdNativeCost_le`: the explicit bound of the bounded regime from the CORDIC counts
(`bdParams`, `SparseHamiltonian.GateBinary.cordicArith_counts`).

**`gate_optimal_binary`** (Theorem `gate:thm:main` from binary sparse oracles, native form). For a
binary sparse input and the parameters of the theorem, the CORDIC accuracy `0 < ζ ≤ 1`, and the
scalar arithmetic of the signed factor (`FactorWordArith` at `ξ`, given the conditions of the signed
regime) and of the clipped factor and rotation (`ClipFactorArith` at `ξ`, `ClipAngleArith` at `ζ`,
given `Regime`), according to the regime the native
circuit satisfies `GateOptimalPrecision.NativeClaims` with the sparse oracles as primitives: at most
`2·10¹¹ Q_μ` times `2`, `2` or `6` compute circuits of primitive calls (`10`, `10` or `30` calls per
private call), at most `10¹³ (Q_μ + 1)(a + m + r + 1) + 2·10¹¹ Q_μ G` gates with `G` the explicit
per-call cost, on at most `2a + 3m + 6r + 5 + k + (6k + 2b + b_T + b_P + A + 3)` qubits, and
full-output error `ε + 2·10¹¹ Q_μ ζ'` with `ζ' = 4ζ`, `3ξ` or `6ξ + 4ζ`.
**`gate_optimal_binary_total`**: at accuracy `ε/2` with `8·10¹¹ Q_μ (6ξ + 4ζ) ≤ ε`, total error
`ε`.

**`gate_optimal_binary_synth`** (over a finite gate set). Under the synthesis hypothesis
`SparseHamiltonian.GateSynth.Synthesis 𝒢 X_a L` and the budget `ε' > 0`, the synthesised circuit
`SparseHamiltonian.GateSynth.synthBudget hS ε' C` of the native circuit `C` of the regime satisfies
`SynthClaims` (`synthClaims_of_native`): gates of `𝒢` only, the same primitive calls, at most
`N L(ε'/(N+1))` gates for the `N` gates of `C`, `|X_a|` more qubits, and full-output error `ε + ε'`
with every ancilla clean. **`SynthClaims.gates_log`**: if `L ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]` and
`ε' ≤ 1`, the synthesised circuit has at most `G_N (c₁ log((G_N + 1)/ε') + c₀)` gates, with
`G_N = 10¹³ (Q + 1)(a + m + r + 1) + 2·10¹¹ Q G` the native gate bound: the finite-gate-set form of
`gate:eq:main-gates`.

## Lookup-table arithmetic (`Tables`)

The arithmetic hypotheses can be met at every positive accuracy, by reversible lookup tables:

* `cfgRun_mcGate`: on clean flags, the AND-chain gate `SparseHamiltonian.GateCircuit.mcGate` with
  target `X` flips its target exactly when all literals hold and restores the flags;
  `mcGate_classical`, `mcGate_cs_length` (at most two controls per gate);
* `tableG`, `cfgRun_tableG`: one AND-chain NOT gate per pair `(u, o)` of an input pattern `u` and
  an output bit `o`; on clean flags every output bit is flipped once for each pair whose pattern
  holds; `tableC` (the table of a word function on the arithmetic register), `tableC_compute`
  and `tableC_classical` (on `|I| ≤ A + 1` work wires), `tableC_elem`, `tableC_length`
  (`2^|I| (b_T + b_P)(2|I| + 1)` gates);
* word rounding: `exists_word`, `roundW`, `roundW_spec` (every `a ∈ [0, c]` is within `c/2^n` of
  the value of an `n`-bit word), with `thetaVal`, `phiVal`, `alphaVal` as word values
  (`thetaVal_eq`, `phiVal_eq`, `alphaVal_eq`) and the word lengths `bitsFor c e = ⌈log₂ ⌈c/e⌉⌉`
  (`div_pow_le`);
* `fac_acc` (the factor accuracy from the rounded words of `arcsin √|c|` and `arg c`, with
  `π/2^{b_T} ≤ ξ²`, `2π/2^{b_P} ≤ ξ`), `th_acc`, `ph_acc` (the angle accuracy from the rounded words
  of `2 arctan |y|` and `arg y`, with `π/2^{b_T} ≤ ζ`, `2π/2^{b_P} ≤ ζ`);
* **`factorWordArith_exists`** (on `2b` work wires, word lengths `bitsFor π ξ²`, `bitsFor 2π ξ`,
  at most `2^{2b} (b_T + b_P)(4b + 1)` gates) and **`clipArith_exists`** (both clipped hypotheses on
  common arithmetic wires: `2b + 1` work wires, word lengths `clipBT ξ ζ`, `clipBP ξ ζ`, at most
  `2^{2b+1} (b_T + b_P)(4b + 3)` and `2^{2b+2} (b_T + b_P)(4b + 5)` gates);
* **`gate_optimal_binary_tables`**, `gate_optimal_binary_synth_tables`: `gate_optimal_binary_total`
  and `gate_optimal_binary_synth` with these tables, so with no arithmetic hypothesis. The tables
  and their length bounds are fixed before the instance (the binary sparse input), and their
  lengths enter the gate costs, exponential in `b`.

## Scope

* The arithmetic of the signed and clipped regimes is a hypothesis (`FactorWordArith`,
  `ClipFactorArith`, `ClipAngleArith`), required only in its own regime: reversible circuits of
  controlled NOT gates with at most three controls writing angle and phase words of the decoded
  scalars to the stated accuracies; the manuscript's assumption that they have polynomially many
  gates in `b`, `k` and the logarithm of the inverse accuracy enters only through their lengths in
  the explicit gate costs. Such circuits exist at every accuracy: the reversible lookup tables of
  `Tables` (of length exponential in `b`) meet all three hypotheses (`gate_optimal_binary_tables`).
* The clipped native call makes `30` oracle calls per private call instead of the `10` of a single
  computation of the value word (see above).
* The binary data format is that of `GateEfficientBinary`: `k`-bit indices, `s = 2^{s_b}` slots
  enumerated by the low index words, two's complement entries with a linear decoder.
-/
