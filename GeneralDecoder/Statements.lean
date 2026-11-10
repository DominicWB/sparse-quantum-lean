/-!
# General decoders in the gate theorems: statement guide

The package's binary gate endpoints decode the stored words as `c₀(X + iY)` on `b`-bit two's
complement words (`GateOptimalBinary.BinaryInput`, `ManuscriptConformance.BinaryFormat`) and build
the angle arithmetic of the bounded regime by CORDIC. The manuscript's gate theorems allow every
efficiently decoded encoding: Theorem `gate:thm:main` assumes (in the paragraph before it) that "the
decoder and reversible scalar arithmetic must evaluate the normalised entries, elementary real
functions and local rotation parameters specified in Section `gate:sec:native` to accuracy `ξ` using
gates and clean work polynomial in `b_data`, the index widths and `log(1/ξ)`", and `hs:thm:gates`
(the sentence before eq. `hs:eq:gate-binary`) that "decoding and reversible arithmetic have
polynomial gate and workspace costs". This library removes the decoder from the gate endpoints
(review item B2): the native operations decode with the public decoder of the data, and the
arithmetic of the local rotation parameters is the computational assumption.

## The native operations with the decoder of the data

The native layer (`GateEfficientNative`, `GateOptimalPrecision`) is decoder-generic: a native
operation carries its decoded entry as a function of the base wires, and its native identity
`V† R(dec) V = D` holds as soon as the decoded entry of the computed words is the entry of the
located edge. Here the decoded entries are those of the data itself
(`NativeSparseBlockEncoding.Data.decode`, which may depend on the edge), read from the index and
value wires:

* `Native`: `sparseOpD D en κ`, the private operation of `hs:thm:gates` with the decoded entry
  `κ · decode(e, w)`, and its native identity `sparse_nativeOKD`;
* `Simulation`, `Budget`: `binarySimD`, `binary_simulationD` and `binary_simulation_budgetD`, the
  simulation circuit and its counts for any angle arithmetic of that decoded entry
  (`GateNative.ArithOK`);
* `MainNative`: the native data of the three regimes of `gate:thm:main`: `boundedNativeD` (the
  private operation of the normalised data), `sgFOD` with the factor entry `clip(decode(e, w)/μ)`
  (`sgDec`), `clFOD` with the correction entry `[g] c₂` (`cfdecD`) and `clNDD` with the clipped
  value `y(g, f, c₁, c₂)` (`ckdecD`), with their native identities (`sgFOD_native`,
  `clFOD_native`, `clNDD_native`) and the native data `signedNativeD`, `clipNativeD`;
* `MainEndpoint`: `BinaryInputD` (binary sizes, no assumption on the decoder) and the binary
  endpoint `gate_optimal_binaryD_total`, `gate_optimal_binaryD_synth` with the arithmetic of each
  regime supplied on the base wires.

## Arithmetic on the value word and the validity of the index pair

* `Arith`: `RotWordArith`, an angle arithmetic of a decoder of the value word; `FlagGen`:
  `WordArith`, a word arithmetic on general input wires, with the accuracies `FactorAcc` (factor
  arithmetic) and `RotAcc` (angle arithmetic);
* `Flag`, `FlagGen`: the wrappers with the validity of the pair of index words. The manuscript
  computes "the validity predicate `[i < N] ∧ [j < N]` before querying" and on an invalid pair
  selects "the zero-entry rotation `-I` independently of the returned encoding" (Section
  `hs:sec:gates`, before Theorem `hs:thm:gates`):
  `validC` computes the validity on the index wires (`evalidW`); `RotWordArith.flagLift` and
  `WordArith.flagLiftG` run the arithmetic of the value word, copy its words under the validity
  (for the clipped rotation, the angle word also under the branch, since the zero entry of the
  clipped regime has the value `y(g, f, 0, 0) = 2q [g][f]`), and uncompute;
  `RotWordArith.flagLift_ok`, `flagLiftG_factorOK`, `flagLiftG_rotOK`: the arithmetic hypotheses of
  the native operations for the decoders with the validity of the pair;
* `PadArith`: the arithmetic hypotheses of the native operations of `gate:thm:main` for the padded
  data with a validity decoder (`sgFOD_padDataE_ok`, `clFOD_padDataE_ok`, `clNDD_padDataE_ok`)
  from word arithmetic of the decoder `val` on the value word (`sgVal`, `cfVal`, `ckVal`), and the
  gates and work wires of the wrappers (`wrap_cost_le`);
* `Tables`: the form and the accuracy of this arithmetic can be met for every decoder and every
  accuracy by reversible lookup tables (`WordArith.table`; `rotWordArith_exists`,
  `sgWordArith_exists`, `clipWordArith_exists`, with gate counts exponential in `b`), as for the
  decoder `c₀(X + iY)` (`GateOptimalBinary.factorWordArith_exists`,
  `GateOptimalBinary.clipArith_exists`); `bitsFor_words`, `table_cost_le`: their word lengths and
  costs.

The padded data with a validity decoder are `SparseHamiltonian.GeneralSparseAccess.QData.padDataE`
(module `GeneralSparseAccess.PadE`): the supplied word of the low index words on every pair,
decoded as `val w` on a valid pair and as `0` otherwise, so no zero word of the decoder is needed;
`GeneralSparseAccess.ImplE` implements its primitives from the supplied oracles (`implPE`,
`implOKE`: the padded locators and one supplied value call).

## Use

`ManuscriptConformance.GateDecoder` states `hs:thm:gates` (eq. `hs:eq:gate-binary`) for the decoder
of the data in binary sizes (`hs_gates_dataDec`) and for general sizes and general decoders
(`hs_thm_gates_decoder`); `ManuscriptConformance.GateMainDecoder` states `gate:thm:main` in both
forms (`gate_main_dataDec`, `gate_thm_main_decoder`). The computational assumptions are those of
the manuscript, stated for the decoder `val` of the stored words: the angle arithmetic of the
bounded regime and of `hs:thm:gates` (`comp_rotArith`), the factor arithmetic of the signed-factor
regime (`comp_signedArithV`) and the factor and angle arithmetic of the clipped regime
(`comp_clipArithV`), each with gates and work wires at most
`c_A (b_data + k + log₂(1/ξ) + 1)^{d_A}` at accuracy `ξ`. `ManuscriptConformance.GateDecoderTables`
shows that they hold for every decoder with `c_A = 2^{2b+8} (b + 1)` and `d_A = 1`, by the tables
(`comp_rotArith_tables`, `comp_signedArithV_tables`, `comp_clipArithV_tables`), so that for stored
words of bounded width the two theorems hold with no arithmetic hypothesis
(`hs_thm_gates_decoder_tables`, `gate_thm_main_decoder_tables`, with constants exponential in the
width); the polynomial bound with constants independent of `b` is the computational content of
the assumptions. `ManuscriptConformance.GateDecoderBinary` shows that for the decoder `c₀(X + iY)`
the hypotheses of the general-size theorems `hs_thm_gates_general`, `gate_thm_main_general` imply
these assumptions, at `c_A = 2·10⁷`, `d_A = 3` and at `max(c_A, 2·10⁷)`, `max(d_A, 3)`
(`comp_rotArith_binary`: the CORDIC arithmetic of the package placed on the value word;
`comp_signedArithV_binary`, `comp_clipArithV_binary`), so the decoder theorems extend them with
other constants `C`, `K` (`hs_thm_gates_general_of_decoder`, `gate_thm_main_general_of_decoder`).
The angle assumption `comp_rotArith` is asked at the rescalings `κ ∈ [1/η, √(2s)/η]` of the
construction.

## Scope

The ODE gate theorems decode the stored words as `c₀(X + iY)` in the binary format
(`ode_thm_gates`, `ode_thm_gates_time`) and for sparse access of general size
(`ode_thm_gates_general`, `ode_thm_gates_time_general`, library `GeneralSparseODE`); for sparse
access of general size with other decoders they take an exact reversible binary entry decoding of
the stored words (`ode_thm_gates_decoder`, `ode_thm_gates_time_decoder`, library
`GeneralDecoderODE`).
-/
