/-!
# Sparse access of general size: statement guide

The package's gate endpoints take sparse data in a binary format (`GateOptimalBinary.BinaryInput`,
`ManuscriptConformance.BinaryFormat`): `N = 2^k`, `s = 2^{s_b}` slots enumerated by the low index
words, and two's complement entries decoded as `c₀(X + iY)`. The manuscript's sparse access
(Section `hs:sec:control`) allows every `N` and `s ≤ N`, and locators prescribed on the valid list
inputs only, with an arbitrary unitary action elsewhere. This library reduces the
sizes `N`, `s` of sparse access to those of the binary format by padding the oracles (review item
B, general sizes); the decoder is kept, so the padded data are in the binary format when the words
are decoded as `c₀(X + iY)`. For a general decoder, which need not have a zero word, the padded
data with a validity decoder (`PadE`, `ImplE`) decode the supplied word as `0` on an invalid pair
(review item B2, with the library `GeneralDecoder`). The manuscript instead treats non-power-of-two
`s` by a uniform-range preparation and index labels outside `[0, N)` by validity tests inside the
circuit (Section `hs:sec:gates`, paragraph *Entry arithmetic and the precise resource bound*);
padding the oracles lets the binary circuits apply unchanged.

## The data (`Data`)

`QData X N s k b`: an `N × N` matrix with `s`-sparse lists, `1 ≤ s ≤ N ≤ 2^k`, on `k`-bit
little-endian index words (`binW`), stored words of `2b` bits read by a public decoder `val` (the
value oracle XOR-writes a stored word on every pair of index words, `table`), and row and column
locators that are unitary on the full edge register with the prescribed action on the valid list
inputs (`row_valid`, `column_valid`) only. `QData.prims` are the three primitive
oracles of the gate model on the register `PY k b`; `QData.padMat` is the matrix extended by zero
to the index words `≥ N`.

## The padded data (`Padded`, `PaddedData`, `PadSpec`)

`QData.padData D z₀ hz₀` (`z₀` a public word with `val z₀ = 0`): `k + 1`-bit index words with a
marker (top bit), `s' = 2^⌈log₂ s⌉ < 2s` slots enumerated by the low words (`pslot_range`), the
matrix of `D` on the valid index words (marker `0`, low word below `N`) and zero elsewhere
(`padData_matrix`, `padData_matrix_mark`); the lists of valid rows and columns are the supplied
lists followed by marked positions. On an input `(y, a)` the padded locators flip the marker of the
position `a` unless the index word `y` is valid and the low word of `a` is below `s` (`maskE`),
then apply the supplied locator to the low words if that marker is clear (`rowMat`; `colMat` then
exchanges the two index registers): both are unitary and act as prescribed on every valid list
input of the padded data, for every unitary extension of the supplied locators outside their own
valid list inputs. The padded matrix inherits Hermiticity and the row, column and entry bounds
(`padData_isHermitian`, `padData_row_le`, `padData_col_le`, `padData_entry_le`).

## Implementing the padded oracles (`Compare`, `CtrlRef`, `Implement`, `ImplVal`, `ImplOK`)

`implP N s z₀`: native circuits on the padded register and clean ancillas (`AW k b`) calling only
the supplied oracles:

* the padded locators: the comparisons of the index and position words with `N` and `s`
  (`ltChain`, a ripple of controlled NOT gates on clean borrow wires; cf. the manuscript's validity
  predicate `[i < N] ∧ [j < N]`, Section `hs:sec:gates`, paragraph *Entry arithmetic and the precise
  resource bound*), the flip of the position marker and the uncomputation of the comparisons
  (`maskC`), then the supplied
  locator controlled on a clear marker by the manuscript's controlled reversible access with a
  reference (Lemma `access:lem:control`, three calls: `ctrlRef_agrees`, `maskCtrl_clean`), and for
  the column locator the exchange of the two index registers (`swapRegs`);
* the padded value oracle: the validity flag of the pair, the supplied word computed into a
  scratch register, copied into the value wires on a valid pair (the zero word `z₀` otherwise) and
  uncomputed (two calls; `implVal_clean`).

`implOK`: on clean ancillas each circuit acts exactly as the padded primitive, for every action of
the supplied locators outside their valid list inputs; `kindOK_implP`: at most three calls, all of
the corresponding supplied oracle; `nGatesN_implP_le`: at most `implG k b = 30(k + 1) + 4b`
elementary gates.

## The padded data with a validity decoder (`PadE`, `ImplE`)

`QData.padDataE D`: the index words, slots and locators of `padData`, with the supplied word of the
low index words stored on every pair (`ptableE`) and the validity decoder `pdecode` (the decoder
`val` of `D` on a pair of valid index words, `0` otherwise), so no zero word of the decoder is
needed; the manuscript likewise selects the zero-entry rotation on an invalid pair "independently of
the returned encoding" (Section `hs:sec:gates`, paragraph *Entry arithmetic and the precise resource
bound*). Its matrix is again the matrix of `D` on the valid index words and zero elsewhere
(`padDataE_matrix`, `padForm_padDataE`), with the promises of the matrix (`PadForm.isHermitian`,
`PadForm.row_le`, `PadForm.col_le`, `PadForm.entry_le`).
`implPE N s`: the padded locators of `implP` and, for the value oracle, one supplied value call on
the low edge wires (`implValE`); `implOKE`, `kindOK_implPE`, `nGatesN_implPE_le`: on clean
ancillas each acts as the padded primitive, with at most three calls of the corresponding supplied
oracle and `implG k b` gates.

## Substitution and synthesis (`Subst`, `Keep`)

* `nrun_subst_cleanEmb`: for unitary primitives, replacing every call of a circuit by its
  implementation (and every inverse call by the literal inverse) on shared clean ancillas gives a
  circuit acting as the original one on clean ancillas, exactly; `nGatesN_subst_le`,
  `nCallsN_subst_le`, `valid_subst`;
* `keepC`, `keepC_spec`, `keepC_error`: the gates outside a finite gate set synthesised at accuracy
  `ζ`, the gates of the gate set kept, with full-output error at most `nGatesN C · ζ` more;
  `nGatesOut_subst_le`: substituted into a circuit over the gate set, the implementations leave at
  most `implG k b` gates outside it per call.

## Use

`ManuscriptConformance.GateGeneralDefs` transfers a circuit of the padded data to the supplied
oracles (`genCirc`, `genCirc_spec`, `genCirc_error`: full-output error against the evolution of
`D.padMat x` on the low index wires, every other wire clean), and
`ManuscriptConformance.GateGeneral` states `gate:thm:main` and `hs:thm:gates` for sparse access
of general size (`gate_thm_main_general`, `hs_thm_gates_general`). For general decoders,
`ManuscriptConformance.GateDecoderDefs` transfers a circuit of `padDataE` to the supplied oracles
(`genCircE`, `genCircE_spec`, `genCircE_error`), and `ManuscriptConformance.GateDecoder`,
`ManuscriptConformance.GateMainDecoder` state `hs:thm:gates` and `gate:thm:main` for sparse
access of general size with any public decoder of the stored words (`hs_thm_gates_decoder`,
`gate_thm_main_decoder`; the native operations with the decoder of the data and the arithmetic of
the decoder are in the library `GeneralDecoder`).

## Scope

`gate_thm_main_general` and `hs_thm_gates_general` decode the stored words as `c₀(X + iY)` on
`b`-bit two's complement words (`formal_binaryDecoder`); `gate_thm_main_decoder` and
`hs_thm_gates_decoder` take any public decoder, with the computational assumptions on its
arithmetic (review item B2). The ODE gate theorems take sparse access of general size through the
library `GeneralSparseODE` (`ode_thm_gates_general`, `ode_thm_gates_time_general`, with the decoder
`c₀(X + iY)`) and, with a decoder that has an exact binary entry decoding, through the library
`GeneralDecoderODE` (`ode_thm_gates_decoder`, `ode_thm_gates_time_decoder`); `ode_thm_gates` and
`ode_thm_gates_time` keep the binary format.
-/
