import GeneralSparseODE.Subst
import GeneralSparseODE.SubstSlot
import GeneralSparseODE.Embed
import GeneralSparseODE.Padded
import GeneralSparseODE.Valid
import GeneralSparseODE.Source
import GeneralSparseODE.Constant
import GeneralSparseODE.ConstantBudget
import GeneralSparseODE.Time
import GeneralSparseODE.TimeBudget

/-!
# The gate-level dissipative solvers for sparse access of general size: statement guide

The package's gate-level dissipative solvers (Theorem `ode:thm:gates`, constant and time-dependent
coefficients) take binary sparse data: `N = 2^k` indices, `s = 2^{s_b}` slots on the low index
words and entries `c₀(X + iY)` (`GateBinaryODE`, `GateBinaryODETime`, with every `T ≥ 0` in
`ZeroTimeGateODE` and the source budgets of `SourceAccuracyODE`). The manuscript's sparse access
(Section `hs:sec:control`) has general sizes `N`, `1 ≤ s ≤ N`, index registers of `k = ⌈log₂ N⌉`
qubits, and locators prescribed on the valid list inputs only
(`SparseHamiltonian.GeneralSparseAccess.QData`). This library runs the released solvers on the
padded data `QData.padData` of `GeneralSparseAccess` (`k + 1`-bit index words with a marker,
`2^⌈log₂ s⌉` slots, the matrix extended by zero to the invalid index words), with the padded
oracles implemented from the supplied ones (`GeneralSparseAccess.implP`, review item B), and
transfers the instance conditions and the conclusions between the index register and the padded
register along the marker embedding.

## The private operation calling the supplied oracles

* `Subst`: `substOp nd impl`, the native private operation `nd` of a solver with every primitive
  call of its compute circuit replaced by an implementation `impl` on clean ancillas added to the
  scratch; `nativeOK_substOp`: the native identity `V† R_val V = D` carries over to the primitives
  implemented by `impl` (`GeneralSparseAccess.ImplOK`); `substOp_public`, `nGatesN_substOp_le`,
  `nCallsN_substOp_le`: the public conditions and the counts (at most `G` more gates and `c` calls
  per call); `liftA`, `arithOK_liftA`: the arithmetic of the solver on the base wires.
* `SubstSlot`: the time-slot-selected form for the time-dependent solver: `substSlot V₀ o₀ dec
  impl`, the substituted compute circuit extended to the slot wires
  (`GateBinaryODETime.slotOp2`), with the native identity for the selection-controlled supplied
  oracles `GateBinary.slotPrim` (`nativeOK_substSlot`) and the counts.

## The padded problem

* `Embed`: `markEmb k`, the clean embedding of the `k`-qubit index register into the padded
  register (marker clear), `lowPart k` its adjoint, `zext A = markEmb ∘ A ∘ lowPart`, the zero
  extension of an operator, and `lowOp O`, an operator on the low wires; `solution_comp`,
  `solves_zext`: the solutions of `x' = -A x + b` (constant and time-dependent) along the marker
  embedding, `accretive_zext`, `norm_zext_le`, `seedV_markEmb`, `unitDirection_markEmb`.
* `Padded`: `zpad`, the matrix extended by zero; the energy bounds and the accretivity of the padded
  matrix (`zpad_row_le`, `zpad_col_le`, `zpad_accretive`); `padLift D x`, the lift of the matrix
  extended by zero to the `2^k` index words (`QData.padMat`), and `mLift_padData`: the lift of the
  padded matrix is its zero extension.
* `Source`: `liftC`, the source circuits of the index register on the low wires of the padded
  system register; `approxOn_liftSrc`, `approxOn_liftLoad`: their accuracies against the lifted
  controlled preparations.
* `Valid`: the problem on `ℂ^N` inside the index register: `validEmb N k` (the basis vector of `i`
  to that of the index word `binW k i`, an isometry), its left inverse and adjoint `validRes`, and
  `validLift A = validEmb ∘ A ∘ validRes`; `padLift_eq`: `padLift D x` is the lift of the matrix
  of `D`; `solution_padLift_validEmb`: the constant-coefficient solution from sources on `ℂ^N` is
  the embedding of the solution on `ℂ^N`; `solution_padLift_invalid`: a source component on an
  invalid index word evolves freely; `solves_comp`, `solves_validLift`, `accretive_validLift`,
  `norm_validLift_sub_le`, `norm_validLift_sub_padLift_le`: the conditions of a time-dependent
  problem on `ℂ^N` for the lifted generator path.

## Constant coefficients

* `Constant`: `GPub`, the public data (`GPub.pub`: the released public data of `k + 1` system
  qubits and `⌈log₂ s⌉` slot bits); `GPub.nd`, `GPub.ar`, `GPub.prep` (the direct source assembly
  in the zero case, the native preparation otherwise); `general_ode_outcome`: the guarantees
  `WOutcome … (ε/250)` for the supplied oracles against the marker embedding of the solution of
  `x' = -A x + b`, `A = padLift D x`, for every input with the released energy bounds and an
  accretive dissipative part on `ℂ^N` and source circuits within `ζ_s` of the controlled
  preparations on the index register.
* `ConstantBudget`: `general_ode_budget`: valid trials, at most
  `10²⁰ g [q* (𝔟₀+1)³ + G_src + |Zs|]` gates, `3·10¹¹ (𝔟₀+1)³ + 2 |Zs|` qubits and
  `11796480 g q*` supplied calls of each matrix oracle (three times the released count; none in the
  zero case), `q*`, `𝔟₀` those of the padded problem.

## Time-dependent coefficients

* `Time`: `primsTG D x`, the coherent sampled-time supplied oracles of time-indexed general sparse
  access `D : QData (X × Fin (2^m)) N s k b`; `GPubT`, `GPubT.pub`, `GPubT.nd` (with `substSlot`),
  `GPubT.ar`, `GPubT.prep`; `RobustRestG` (for sparse access of any stored bits), the remaining
  instance conditions of `RepresentedSampleODE.GateTime.RobustRest` on the index register, with the
  generator path within `δ_G` of the lifts `padLift D (x, r)` of the samples, for the released
  public parameters of the padded problem (the parameters `λ_H`, `λ_D` of the discretisation
  condition those of the `2^⌈log₂ s⌉` padded slots), and `RobustRestG.padded`, their transfer to the
  padded problem; `general_time_outcome`: the guarantees `WOutcome … (ε/100)` for the supplied oracles against the
  marker embedding of `x(T)` (represented samples of any sign).
* `TimeBudget`: `general_time_budget`: valid trials, at most
  `2·10²⁰ g [q*' (𝔟'+1)³ + G_src + |Zs|]` gates, `3·10¹¹ (𝔟'+1)³ + 2 |Zs|` qubits and
  `23592960 g q*'` supplied calls of each matrix oracle (none in the zero case), `q*'`, `𝔟'` those of
  the padded problem at the internal ratio `2g` and accuracy `ε/2`.

## Use

`ManuscriptConformance.GateODEGeneral` (`ode_thm_gates_general`) and
`ManuscriptConformance.GateODETimeGeneral` (`ode_thm_gates_time_general`) state Theorem
`ode:thm:gates` for sparse access of general size from these endpoints, with the counts in `N`
and `s` (the padded word budget is within `+3`, resp. `+5`, of the manuscript's, and the padded query
shape at most `2`, resp. `6`, times it), and the output against the normalised solution on the
index register with the marker clean; for a problem on `ℂ^N` this is the embedding of its
solution (`Valid`). The decoder is `c₀(X + iY)`
(`ManuscriptConformance.formal_binaryDecoder`, review item B2); the library `GeneralDecoderODE` runs
these solvers on the decoded data of sparse access with a decoder that has an exact binary entry
decoding (`ManuscriptConformance.ode_thm_gates_decoder`, `ode_thm_gates_time_decoder`). The library
`MeshCertificateODE` proves the guarantees of the time-dependent solver under the manuscript's
source and sample certificates in place of `RobustRestG`
(`MeshCertificateODE.general_time_cert_outcome`; `ManuscriptConformance.ode_thm_gates_time_cert`).
-/
