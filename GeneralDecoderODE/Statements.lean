import GeneralDecoderODE.Decode
import GeneralDecoderODE.ImplDec
import GeneralDecoderODE.Compose
import GeneralDecoderODE.Solver
import GeneralDecoderODE.SolverBudget
import GeneralDecoderODE.SolverTime
import GeneralDecoderODE.SolverTimeBudget
import GeneralDecoderODE.Decoder

/-!
# The gate-level dissipative solvers with binary entry decoding: statement guide

The manuscript's sparse access (Section `hs:sec:control`) stores a bit string `w_ij` for every valid
pair of indices and represents the entry `H_ij = val(w_ij)` for a known decoder `val`; Theorem
`ode:thm:gates` assumes "efficient binary entry decoding" (the opening of Section `ode:sec:gates`:
entry decoding admits reversible circuits of fixed polynomial gate and work cost). The gate-level
solvers for sparse access of general size (`GeneralSparseODE`) read the stored words as two `b`-bit
two's complement words decoded by `c₀(X + iY)`. This library removes that restriction (review item
B2) for every decoder `val` with an exact reversible decoding circuit into binary entries
`c₀ (X + iY)`, so with values on the grid `c₀ (ℤ + iℤ)`: the solvers run on the decoded data and
call the supplied oracles through the decoding circuit.

## Binary entry decoding

* `Decode`: `BinDecode b b' A`, a reversible circuit of controlled NOT gates with at most three
  controls on the stored word (`2b` bits), the decoded word (two `b'`-bit two's complement
  components) and `A` work wires, writing the decoded word `dw w` on clean wires and restoring the
  work wires; `BinDecode.Exact dc val c₀`: `val w = c₀ (X + iY)` for the components of `dw w`;
  `BinDecode.cost`: its gates and wires `|circ| + 2b + 2b' + A`; `BinDecode.wires`: its wires
  `2b + 2b' + A` (`wires_le_cost`). `QData.decData`: the decoded data,
  the sparse access with the stored words replaced by the decoded words read by `c₀(X + iY)`, with
  the matrix and the locators of `D`. `BinDecode.copy`: the copy of the stored word, an exact
  decoding of `c₀(X + iY)` (`copy_exact`, `copy_cost`); `BinDecode.table`, `exists_table_exact`:
  the lookup-table decoding of any decoder with binary entries.

## The decoded oracles and the padded oracles from the supplied ones

* `ImplDec`: `implDec dc`, the oracles of the decoded data from the supplied ones on clean ancillas
  (the locators: one supplied call; the value oracle: a supplied value call into clean stored-word
  ancillas, the decoding circuit, the copy of the decoded word into the value wires by controlled
  NOT gates, the decoding backwards and a second supplied value call); `implDec_ok`
  (`GeneralSparseAccess.ImplOK`), `kindOK_implDec` (at most two calls of the kind of the call),
  `nGatesN_implDec_le` (at most `2 |dc| + 2b'` gates).
* `Compose`: `implComp impl₁ impl₂`, an implementation with every call replaced by an
  implementation of it, the wires reassociated (`assocE`); `implOK_comp`, `kindOK_comp`,
  `nGatesN_implComp_le`.
* `Decoder`: `implDP N s z₀ dc = implComp (implP N s z₀) (implDec dc)`, the padded oracles of the
  decoded data from the supplied oracles (`implOK_implDP`, `kindOK_implDP`: at most six calls,
  `nGatesN_implDP_le`: at most `implG k b' + 3 (2 |dc| + 2b')` gates per padded call).

## The solvers through any implementation

* `Solver`, `SolverTime`: `ndI`, `arI`, `prepI` and `ndTI`, `arTI`, `prepTI`: the private
  operations, the arithmetic and the preparations of the constant-coefficient and the
  time-dependent general solvers through any implementation `impl` of the padded oracles from
  unitary primitives on any register; `general_ode_outcomeI`, `general_time_outcomeI`: the
  guarantees of `GeneralSparseODE.general_ode_outcome` and `general_time_outcome` for these
  primitives (`nativeOKTI`: the native identity of the time-dependent operation for the
  selection-controlled primitives).
* `SolverBudget`, `SolverTimeBudget`: `general_ode_budgetI`, `general_time_budgetI`: the bounds of
  `general_ode_budget` and `general_time_budget` with the gates `G` per call and the ancillas `Xa` of
  the implementation kept apart (`9·10¹⁹ g [q* (𝔟₀+1)³ + G_src + |Zs|] + 3·10¹² g (q* G + |Xa|)`
  gates, `2.8·10¹¹ (𝔟₀+1)³ + 2 |Zs| + 2 |Xa|` qubits, `3932160 c g q*` calls for `c` calls per
  call; time-dependent `1.8·10²⁰`, `6·10¹²`, `2.8·10¹¹`, `7864320 c`).

## The decoder solvers

* `Decoder`: `prepD q N dc srcC`, `prepTD q N dc loadC wpC`: the preparations through `implDP`;
  `decoder_ode_outcome`, `decoder_time_outcome`: the guarantees for the supplied oracles of `D`
  (time-dependent: the coherent sampled-time supplied oracles `primsTG D x`), against the marker
  embedding of the solution for the matrix of `D`; `decoder_ode_budget`, `decoder_time_budget`:
  at most `10²⁰ g [q* ((𝔟₀+1)³ + cost dc) + G_src + |Zs|]` (time-dependent
  `2·10²⁰ g [q*' ((𝔟'+1)³ + cost dc) + G_src + |Zs|]`) gates,
  `3·10¹¹ (𝔟₀+1)³ + 2 |Zs| + 2 wires dc` (time-dependent `(𝔟'+1)³`) qubits and `23592960 g q*`
  (time-dependent `47185920 g q*'`) supplied calls of each matrix oracle (none in the zero case)
  besides those of the source circuits, for decoded words of `b' ≤ b_data` bits;
  `robustRestG_decData`: the instance conditions `GeneralSparseODE.RobustRestG` carry over to the
  decoded data.

## Use

`ManuscriptConformance.GateODEDecoder` (`ode_thm_gates_decoder`, `ode_thm_gates_time_decoder`)
states Theorem `ode:thm:gates` for sparse access of general size with a decoder that has an exact
binary entry decoding (`ManuscriptConformance.BinaryEntryDecoding`), with the decoding cost in the
polynomial of the gate bound and its wires in the qubit bound; the decoder `c₀(X + iY)` of
`ode_thm_gates_general` has the copy decoding (`ManuscriptConformance.binaryEntryDecoding_copy`),
so these theorems apply under its hypotheses, with their own protocol and constants. The library
`MeshCertificateODE` proves the guarantees of the time-dependent decoder solver under the
manuscript's source and sample certificates in place of `GeneralSparseODE.RobustRestG`
(`MeshCertificateODE.decoder_time_cert_outcome`;
`ManuscriptConformance.ode_thm_gates_time_decoder_cert`).
-/
