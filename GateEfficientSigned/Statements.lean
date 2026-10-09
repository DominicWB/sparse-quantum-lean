import GateEfficientSigned.Zero
import GateEfficientSigned.NonVacuity

/-!
# Theorem `hs:thm:gates` for every real time from binary sparse oracles: paper-to-Lean entry point

Theorem `hs:thm:gates` of the accompanying paper (gate-efficient sparse simulation, manuscript
line 3103) holds "under the assumptions of Theorem `hs:thm:main`", and Theorem `hs:thm:main`
(line 2031) simulates `e^{-itH}` for every real `t`, with `τ = η|t|`; the proof of
`hs:thm:gates` says "It is enough to consider `t = T > 0`; negative times use the inverse
circuit" (lines 3152-3153). The released gate-level endpoints treat negative times for native
implementations (`GateNative.native_simulation_signed`, with the literal inverse circuit) and,
in the exact-gate model, through Lemma `hs:lem:abstract` (`GateRemarks.abstract_simulation`,
exchanging `D` and `D†`); the time-independent endpoints for the circuits built from binary sparse
oracles, with the entry decoding, the angle arithmetic, the compute circuit and `U_J`
constructed, are stated for `τ ≥ 0`. This library states each of them for every real `t`: for
`t < 0` the circuit is the literal inverse of the released circuit for `|t|`, which calls the
inverse oracles, has the same counts and simulates `e^{-itĤ}` with the same full-output error.

Theorem `hs:thm:time` (line 2565) is stated for `T ≥ 0` (the propagator `U_H(T, 0)`), and so is
the time-dependent part of `hs:thm:gates`; the differential equations are posed on `0 ≤ t ≤ T`
(equation `ode:eq:ode`, line 3859). Their endpoints need no signed form.

No result from another paper is used, except single-qubit synthesis and the decomposition of
controlled gates through the released hypothesis `GateSynth.Synthesis` of the finite-gate-set
forms. The released libraries are unchanged. Manuscript lines refer to
`sparse_quantum_algorithms.tex` (v19); the labels are the stable references. Every theorem of the
library is axiom-audited in `GateEfficientSigned/Audit.lean`.

**Naming convention.** All declarations of this library are in the namespace
`SparseHamiltonian.GateSigned` and are named relative to it below. Released declarations are
named relative to `SparseHamiltonian` (for example `GateBinary.binarySim`,
`GateNative.ninv`, `GateSynth.synthBudget`, `GateBitBudget.bitH`, `GateRemarks.binaryCircuit`);
`NativeSparseBlockEncoding`, `CayleyClockInterface`, `TimeSchedule`, `ImprovedPrecisionBudget`,
`SparseStateOverlap` and `SparseValuePrecision` are namespaces of the package under
`SparseHamiltonian`. Each endpoint is named after the released endpoint that it extends: the
released name with `_signed` appended, and with `_zero` appended once more for the forms with the
empty circuit at `t = 0` (the released native forms are named `GateNative.native_simulation_signed`
and `GateSynth.native_simulation_signed_synth` instead).

**What was already released (cited, not redone).**

* Negative times for native implementations: `GateNative.native_simulation_signed` (circuit
  `GateNative.nativeSimSigned`, the literal inverse `GateNative.ninv` with
  `GateNative.nrun_ninv`, `GateNative.valid_ninv`, `GateNative.nGatesN_ninv`,
  `GateNative.nCallsN_ninv`, and the error transfer `GateNative.err_neg`), over a finite gate set
  `GateSynth.native_simulation_signed_synth`, and with the empty circuit at `t = 0`
  `ZeroTimeRemarks.Gates.native_simulation_signed_zero` and
  `GateRemarks.native_simulation_signed_synth_zero`. They take the private Cayley operation, the
  arithmetic and the identity `GateNative.NativeOK` as hypotheses.
* Lemma `hs:lem:abstract` for every real time in the exact-gate model, also for the operators of
  the binary-data construction with `D` a supplied unitary: `GateRemarks.abstract_simulation`,
  `GateRemarks.abstract_simulation_binary`.
* The binary-data endpoints of `hs:thm:gates` for `τ ≥ 0`: `GateBinary.binary_simulation`,
  `GateBinary.binary_simulation_budget`, `GateBitBudget.binary_simulation_bits`,
  `GateRemarks.binary_simulation_bits_qubits`; over a finite gate set
  `GateSynth.binary_simulation_synth`, `GateSynth.binary_simulation_budget_synth`,
  `GateBitBudget.binary_simulation_budget_synth_bits`,
  `GateRemarks.binary_simulation_budget_synth_bits_qubits`; with the empty circuit at `τ = 0`
  `GateRemarks.binary_simulation_nonneg`, `GateRemarks.binary_simulation_budget_nonneg`,
  `GateRemarks.binary_simulation_synth_nonneg`,
  `GateRemarks.binary_simulation_budget_synth_nonneg`; the one-point data
  `GateBitBudget.pointData` and the satisfiability witness `GateBitBudget.hs_all_hyps` (at
  `τ = 0`, zero matrix).

**Endpoints** (each with the released endpoint it extends to every real `t`).

* Native, before finite-set synthesis: `binary_simulation_signed`
  (`GateBinary.binary_simulation`), `binary_simulation_budget_signed`
  (`GateBinary.binary_simulation_budget`), `binary_simulation_bits_signed`
  (`GateBitBudget.binary_simulation_bits`), `binary_simulation_bits_qubits_signed`
  (`GateRemarks.binary_simulation_bits_qubits`).
* Over a finite gate set: `binary_simulation_synth_signed` (`GateSynth.binary_simulation_synth`),
  `binary_simulation_budget_synth_signed` (`GateSynth.binary_simulation_budget_synth`),
  `binary_simulation_budget_synth_bits_signed`
  (`GateBitBudget.binary_simulation_budget_synth_bits`),
  `binary_simulation_budget_synth_bits_qubits_signed`
  (`GateRemarks.binary_simulation_budget_synth_bits_qubits`).
* With the empty circuit at `t = 0`: `binary_simulation_signed_zero`
  (`GateRemarks.binary_simulation_nonneg`), `binary_simulation_budget_signed_zero`
  (`GateRemarks.binary_simulation_budget_nonneg`), `binary_simulation_synth_signed_zero`
  (`GateRemarks.binary_simulation_synth_nonneg`), `binary_simulation_budget_synth_signed_zero`
  (`GateRemarks.binary_simulation_budget_synth_nonneg`).
* Non-vacuity at a negative time, and the error of the released circuit for `|t|` there:
  `hs_signed_all_hyps`, `binarySim_error_ge`.

**Model** (that of `GateEfficientBinary/Statements.lean`, `GateEfficientSynthesis/Statements.lean`
and `GateEfficientBitBudget/Statements.lean`). Binary sparse data
`NativeSparseBlockEncoding.Data X n (Cfg (VW b)) s` with `k`-bit indices `en : Cfg (Fin k) ≃ n`,
`s = 2^σ` slots on the lowest `σ ≤ k` bits, `b`-bit two's complement components and decoder
`c₀ (X + i Y)`; the primitive oracles `GateBinary.prims D en x` (row location, column location and
value, `NativeSparseBlockEncoding.Query`); native circuits are lists of `GateNative.NInstr`
(elementary gates and calls of a primitive oracle or of its inverse, `call j adj pos`) run by
`GateNative.nrun` with the head first; the counts are `GateNative.nGatesN` and
`GateNative.nCallsN p` (a call of an inverse oracle counts as a call of the oracle); the full
output error is `‖nrun prim C ∘ sysEmb io - sysEmb io ∘ e^{-itĤ}‖` for the clean system embedding
`GateNative.sysEmb GateCircuit.Sim.io` and the qubit lift
`Ĥ = GateBinary.qlift en (SparseStateOverlap.matrixOperator (D.matrix x))`, with an untouched
reference `R`; after synthesis the synthesis ancillas `Xa` are clean
(`GateNative.cleanEmb`).

* `signed t C = if 0 ≤ t then C else GateNative.ninv C`, where `ninv C` reverses `C` and inverts
  every instruction (a gate by its conjugate transpose, a call by the call of the inverse
  oracle); `binarySimSigned k b σ hσ s γ c₀ t ε ζ = signed t (GateBinary.binarySim k b σ hσ s γ c₀
  |t| ε ζ)`, on the wires of the circuit for `|t|` (`binarySimSigned_of_nonneg`,
  `binarySimSigned_of_neg`); `binaryCircuitSigned … t … = if t = 0 then [] else
  binarySimSigned … t …`. The circuits depend only on the public data and on `t`.
* Every endpoint assumes exactly the hypotheses of the released endpoint for the time `|t|` (no
  sign condition on `t`): for the native form the data hypotheses, `0 < γ ≤ 1`, `0 < ε ≤ 1`,
  `0 < ζ ≤ 1` and `48 d ζ ≤ ε` with `d = GateCircuit.Sim.fDeg (width s γ) (time s |t| γ)
  (moment γ) (ε/2)`; for the budget forms `s ≥ 1`, `0 < ε ≤ 1/2`, and, after the rescaling `γ`
  (chosen from `s`, `|t|` and `ε` before the data), `221184 q ζ ≤ ε` with
  `q = √s |t| + √(s |t| log(1/ε)) + log(1/ε)` (`ImprovedPrecisionBudget.shape s |t| (log(1/ε))`),
  and for the forms in the bit lengths also `b ≤ b_data`, `GateBitBudget.HasBits b_data c₀` and
  `ε ≤ 442368 q ζ`; over a finite gate set the released `GateSynth.Synthesis 𝒢 Xa L`, a synthesis
  budget `ε' > 0` and, for the budget forms, synthesis constants `c₀, c₁ ≥ 0` (not the decoder
  scale `c₀`) with `L ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]`, and `ε' ≤ 1`.
* Every endpoint keeps every conclusion of the released endpoint for `|t|`, for the signed
  circuit (or its synthesis): validity, the exact call count `12 d` times `2` row-location, `2`
  column-location and `1` value calls (native form) or the bound `55296 q` times these (budget
  forms), the elementary gate bounds (`200 (d+1)(k+1+m+r+1) + 84 d (σ+1) + 6 d G_C`,
  `200 (4608 q + 1)(G_C + (σ+1) + (k+1) + m + r + 1)`, `10¹⁵ q (𝔟_H+1)³`,
  `N L(ε'/(N+1))`, `G (c₁ log((G+1)/ε') + c₀)` and `10¹⁵ q (𝔟_H+1)³ (c₁ (36 (𝔟_H+1) + log(1/ε'))
  + c₀)`), the private gate count `2·10⁹ (𝔟_H+1)³`, the qubit counts (exact, and
  `4·10⁶ (𝔟_H+1)³` plus `|Xa|` after synthesis), the degree and register bounds (`d ≤ 128 (τ' q̄ +
  Q (1 + log(6/ε)))`, `steps τ' (ε/6) ≤ 2^m < 2 steps τ' (ε/6)`, `2d + 2 ≤ 2^r ≤ 4 (d+1)`, and for
  the budget forms `d ≤ 4608 q`, `τ' ≤ √s q`, `2^m < 2 (2 + 4τ' + √(6τ'³/ε))`,
  `2^r ≤ 4 (4608 q + 1)`, with `τ' = √s |t|/γ`), and the full-output error at most `ε`
  (`ε + ε'` after synthesis), now against `e^{-itĤ}`. The forms with the empty circuit at `t = 0`
  state the counts as `if t = 0 then 0 else <count>` and add that the error is exactly `0` at
  `t = 0`, as `GateRemarks.binary_simulation_nonneg` and its variants do for `τ ≥ 0`.

**Non-vacuity at a negative time** (module `NonVacuity`). `wordData Y b c₀ w` is the one-point
data of `GateBitBudget.pointData` with every stored entry the word `w`; with `b = 2`, `c₀ = 1` and
the word `oneWord` (real part `1`) its matrix is the identity (`wordData_matrix`) and `Ĥ = 1`
(`wordData_hamiltonian`). `hs_signed_all_hyps`: for `s = 1`, `t = -1`, `ε = 1/2`, these data,
some `b_data ≥ 2`, `ζ = ε/(442368 q)` and some rescaling `γ ∈ (0, 1]` (in the proof, that of
`GateBitBudget.binary_simulation_bits` for `|t|`) satisfy every hypothesis of
`binary_simulation_bits_signed` and `48 d ζ ≤ ε`; the signed circuit has the gate bound
`10¹⁵ q (𝔟_H+1)³` and error at most `ε` against `e^{-itĤ}` (payload `ℂ`); and
`‖e^{-itĤ} ψ - e^{-i|t|Ĥ} ψ‖ > 1` (it is `|e^{i} - e^{-i}| = 2 sin 1`) for the unit vector
`ψ = GateCircuit.bas default 1` (`exp_smul_one_reg`, `one_lt_norm_exp_sub`).
`binarySim_error_ge`: under the hypotheses of `GateBinary.binary_simulation` for `|t|`, the
released circuit for `|t|` is at least `‖e^{-itĤ} ψ - e^{-i|t|Ĥ} ψ‖ - ε` from `e^{-itĤ}` for every
unit `ψ` (`error_sep`). Every hypothesis of `binarySim_error_ge` is among the conclusions of
`hs_signed_all_hyps`, so at `t = -1` for these data the released circuit for `|t|` is farther than
`ε` from `e^{-itĤ}`, while the signed circuit is within `ε`; there the two evolutions differ by the
global phase `e^{2i}`.

**Proof map** (module paths relative to `GateEfficientSigned/`).

* `Basic`: `signed`, `signed_of_nonneg`, `signed_of_neg`, `nGatesN_signed` and `nCallsN_signed`
  (from `GateNative.nGatesN_ninv`, `GateNative.nCallsN_ninv`), `valid_signed`
  (`GateNative.valid_ninv`), `err_signed` (for `t < 0` from `GateNative.nrun_ninv`,
  `GateNative.nrun_isUnitary` and `GateNative.err_neg`; for `t ≥ 0`, `|t| = t`),
  `qlift_matrixOperator_self` (`GateBinary.qlift_star`,
  `SparseValuePrecision.matrixOperator_star_eq`), `binarySimSigned` and its lemmas.
* `Binary`: each endpoint from the released endpoint for `|t|` (`abs_nonneg t`); validity for the
  budget forms from `GateBinary.binary_simulation` with `48 d ζ ≤ 48 · 4608 q ζ = 221184 q ζ ≤ ε`;
  the counts by `nGatesN_binarySimSigned`, `nCallsN_binarySimSigned`; the error by `err_signed`.
* `Synth`: from the signed native endpoints (`binary_simulation_signed`,
  `binary_simulation_budget_signed`; the forms in the bit lengths from
  `binary_simulation_budget_synth_signed` and `binary_simulation_budget_synth_bits_signed`) with
  `GateSynth.synthBudget_spec`, `GateSynth.synthBudget_error`, `GateSynth.gates_log_le` and, in the
  bit lengths, `GateBitBudget.hs_gates_le`, `GateBitBudget.hs_synth_arith`,
  `GateBitBudget.bitH_nonneg`, `GateRemarks.card_binary_register`,
  `GateRemarks.binary_register_le`.
* `Zero`: case split on `t = 0`; at zero time `GateNative.nrun_nil`, `GateRemarks.synthBudget_nil`,
  `ZeroTimeRemarks.Gates.exp_zero_time`, `ZeroTimeRemarks.Gates.identity_comp_error_eq_zero` and
  `ZeroTimeRemarks.Gates.identity_comp_error_le`; otherwise the signed endpoints.
* `NonVacuity`: `wordData` (the fields of `GateBitBudget.pointData`), `twos_inl_oneWord`,
  `twos_inr_oneWord` (`decide`), `gauss_oneWord`, `wordData_matrix`, `wordData_range`,
  `matrixOperator_one`, `wordData_hamiltonian` (`GateBinary.qlift_one`), `exp_smul_one_reg`
  (`NormedSpace.algebraMap_exp_comm`, `Complex.exp_eq_exp_ℂ`), `error_sep` (triangle inequality
  at `ψ`), `one_lt_norm_exp_sub` (`Complex.abs_im_le_norm`, `Complex.exp_ofReal_mul_I_im`,
  `Real.sin_gt_sub_cube`), `binarySim_error_ge` (`GateBinary.binary_simulation`, `error_sep`,
  `GateNative.norm_sysEmb`), `hs_signed_all_hyps` (`GateBitBudget.binary_simulation_bits`,
  `GateBitBudget.exists_common_bits`, `GateBitBudget.hs_zeta_shape_spec`,
  `binary_simulation_signed`).

**Formalisation choices.**

* Negative times use the literal inverse of the released circuit for `|t|`, as
  `GateNative.native_simulation_signed` does and as the proof of `hs:thm:gates` says, rather than
  the exchange of `D` and `D†` of `GateRemarks.abstract_simulation` (there `D` is a supplied
  unitary; here the private operation is built from the primitive oracles, and the inverse
  circuit calls their inverses). The inverse circuit runs on the wires of the circuit for `|t|`
  and has the same counts; a call of an inverse oracle counts as a call, as in the released counts
  (Theorem `hs:thm:time` counts queries "including inverse calls"). The gate set of the native
  circuits is closed under inversion (a gate with the conjugate-transposed matrix).
* Over a finite gate set the signed circuit is synthesised as it is
  (`GateSynth.synthBudget hS ε' (binarySimSigned …)`); this is not the inverse of the synthesis
  of the circuit for `|t|`, and the synthesised counts follow from those of the signed circuit,
  which are the released ones for `|t|`.
* All parameters are those of the released endpoints for `|t|`: the rescaling `γ`, the slot and
  reuse registers, `q` and `𝔟_H`. At `t ≥ 0`, `binarySimSigned … t …` is the released circuit for
  `|t| = t` (`binarySimSigned_of_nonneg`), so each signed endpoint contains the released one for
  `t ≥ 0`; at `t = 0` it is the released circuit at zero time, and the forms with the empty
  circuit are separate (`Zero`).
* The non-vacuity witness has `k = 0` index bits, one slot and the identity matrix, so `Ĥ = 1`;
  on this one-dimensional system `e^{-itĤ}` and `e^{-i|t|Ĥ}` differ at `t = -1` by the global
  phase `e^{2i}`, to which the full-output error, an operator norm, is sensitive. That the
  released circuit for `|t|` is farther than `ε` from `e^{-itĤ}` there is the combination of
  `hs_signed_all_hyps` (every hypothesis of `binarySim_error_ge`, and the separation of the two
  evolutions by more than `2ε` on a unit vector) with `binarySim_error_ge`; it is not stated as a
  separate theorem.

**Not formalised.**

* Negative times for the time-dependent endpoints (`GateBinary.binary_time_simulation` and its
  variants, the certified and mesh endpoints of `GateEfficientMesh`) and for the
  differential-equation solvers, which the paper does not claim: it states Theorem `hs:thm:time`
  for `T ≥ 0` and poses the differential equations on `0 ≤ t ≤ T`.
* A witness on which the released circuit for `|t|` misses `e^{-itĤ}` at a negative time by more
  than `ε` even up to a global phase (this needs a system of dimension at least two).
* Zero-time forms of the bit-length endpoints, signed or not (`GateEfficientRemarks` lists them as
  not formalised; the combined circuit `binaryCircuitSigned` applies to them in the same way).

**Provenance.** New library, written against the released package: it imports
`GateEfficientBinary`, `GateEfficientSynthesis`, `GateEfficientBitBudget`,
`GateEfficientRemarks` and `ZeroTimeRemarks` (with their dependencies) and changes none of them.
The statement guide of `GateEfficientRemarks` lists "negative times for the circuits built from
binary sparse oracles" as not formalised; that entry is superseded here, within the scope stated
above.
-/
