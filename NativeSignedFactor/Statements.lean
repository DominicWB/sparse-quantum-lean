import NativeSignedFactor.Simulation

set_option autoImplicit false

/-!
# Native sparse factors (`opt:sec:native`): paper-to-Lean entry point

Appendix A of the manuscript supplies the factor required by Theorem `opt:thm:signed` from the
original sparse oracles (subsection `opt:sec:native`). This library constructs a factor of that kind
as a circuit over the native oracles of the released package (with a local factor of the form
`√|c| V(c)†` in place of the blocks `B_±(c)` of `opt:eq:edge-factors`), proves the identities
`opt:eq:native-factor` and `opt:eq:whole-factor` for it, and derives the simulation "with `T = sτ`
and `b = √s τ`" from Theorem `opt:thm:signed` (`SignedFactorSimulation.signed_factor_simulation`).
The large-sparsity core (`opt:sec:core`), the combination of the regimes (the proof of Theorem
`hs:thm:optimal`, eq. `opt:eq:regime-comparison`) and Theorem `hs:thm:optimal` are not part of this
library.

No result from another paper is used. The released libraries are unchanged; the native oracle model,
the locator and value programs, the masked-call compilation and the edge-moment identities of
`SparseHamiltonian` are reused. References to the manuscript use its labels.
Every theorem of the library is axiom-audited in `NativeSignedFactor/Audit.lean`.

**Naming convention.** All declarations are in the namespace `NativeSignedFactor`; names below
are relative to it, except the fully qualified names of the released libraries.

## The oracle model

The sparse data are those of the released package,
`SparseHamiltonian.NativeSparseBlockEncoding.Data X n Z s`: for every instance `x`, a matrix
`H = D.matrix x` on `n`, a row locator and a column locator that are arbitrary unitaries with the
in-place, phase-one promise on the `s` listed slots of every row and column, and an additive
value oracle whose word decodes to the entry by a known decoder. The physical oracle family is
`physOracle D` (`SparseHamiltonian.NativeMaskedProgram.oracle` of
`SparseHamiltonian.NativeSparseMaskedAccess.flatOracle D`): each primitive (row locator, column
locator, value oracle) acts on its register and every other register is a spectator. Adjoint
calls are counted. No controlled oracle is assumed.

## The factor

*The local factor* (module `Local`, `opt:eq:edge-factors`). For a decoded entry `c` with
`|c| ≤ 1`, the success factor on the two orientations of an edge is `√|c| V(c)†` (`facQ`), where
`V(c)` diagonalises `E(c) = [[0, c], [conj c, 0]]`; its two output labels are the `+` and `-`
success labels, so that `B† σ_z B = E(c)` (`facQ_sign`) and `B† B = |c| I` (`facQ_gram`). The
failure amplitude `√(1 - |c|)` is placed on flag `1` by the unitary extension `localGate` (the
Kronecker product of the orientation change `orient` and the flag rotation `flagRot`,
`localGate_unitary`).

*The factor unitary* (module `Gate`). The logical factor unitary `U_B` (`factorProgram`) applies
the row locator on the row orientation and the column locator on the column orientation
(`SparseHamiltonian.OrientedNativeLayout.locatorProgram`), computes the entry word, applies the
local gate controlled by the edge and the word (`gate`), and uncomputes the word: four masked
calls (`factorProgram_cost`). The entry is the decoded word divided by a known entry scale `κ`
and clipped to the unit disk (`entry`, `clip`); on the oracle values with `|H_e| ≤ κ` it is
`H_e/κ` (`entry_table`). The known input is the public uniform slot preparation on both
orientations with clean value and flag registers (`input`), the success projection is flag `0`
(`proj`) and the success reflection is the orientation sign (`sign`); together they form the
known factor structure `known D` (`SignedFactorSimulation.Known`). The factor is
`B = clean ∘ facOp ∘ J₀` (`factor_eq`), with the sparse boundary
`J₀ = SparseHamiltonian.SparseEdgeMoments.boundary` of the actual locator lists.

*The physical factor* (module `Physical`). The masked calls are compiled to the physical oracle
family by the released three-query construction
(`SparseHamiltonian.NativeMaskedProgram.compile`), so `U_B` costs `12` native calls
(`physProgram_count`): three row-locator, three column-locator and six value calls
(`physProgram_cost`). The factor structure is transported along the clean encoding (`transport`,
`physKnown`); its data are known.

## The identities

For a Hermitian `H` with entries of modulus at most `κ` and row and column Euclidean norms at
most `η`, the physical factor `B` of `physKnown D` and `U_B = (physProgram D κ).eval x` satisfy
(`opt:eq:native-factor` with `X = H`, `opt:eq:whole-factor`)

* `B† Z B = H/(sκ)` (`phys_Cop`), equivalently `H = sκ B† Z B` (`phys_ham`);
* `B† B = D_H/(sκ)` with `D_H = diag(∑_j |H_ij|)` (`phys_Dop_eq`);
* `∑_j |H_ij| ≤ √s η` (`row_abs_sum_le`) and `B† B ⪯ η/(√s κ) I` (`phys_Dop_le`); for `κ = η`,
  `B† B ⪯ s^{-1/2} I` (`phys_Dop_le_eta`).

The proofs reduce to the edge picture: `B† Z B = J₀† E_{H/κ} J₀` (`facOp_sign`, `Cop_eq`) with the
compression `J₀† E_X J₀ = X/s` of the baseline
(`SparseHamiltonian.SparseEdgeMoments.generator_compression`), and
`‖B v‖² = ∑_e |c_e| ‖(J₀ v)_e‖²` (`norm_facOp_sq`) with Cauchy–Schwarz over the `s` listed slots
of every row and column (`sum_selected_le`, `norm_factor_sq_le`).

The manuscript also uses `opt:eq:native-factor` for matrices `X` other than `H` whose entries are
known functions of the entry word (for example the clipped correction of Appendix B). These are
covered by the same theorems applied to a `Data` record with the corresponding decoder and
matrix: the physical oracle family `physOracle D` does not depend on the decoder.

## The simulation

`Simulates O H t ε q` (module `Simulation`) states that there are a finite label type `ι`, a known
isometry `inp : ℂ^n → ℂ^ι ⊗ W` (the space `PiLp 2 (fun _ : ι => W)`) and a program whose only oracle
calls are calls of the family `O` on every block of `ℂ^ι ⊗ W`
(`SparseHamiltonian.CoherentQuerySchedule.oracle`), every other gate being a known unitary, with at
most `q` calls counting adjoints, unitary for every instance, and with full-output error
`‖p.eval x ∘ inp - inp ∘ e^{-itH(x)}‖ ≤ ε` for every instance. The input, the embedding and every
gate are chosen before the instance; the program is the same for all instances `x` of the family
`X`. The statement is a query statement for the family of all admissible instances: with a family of
a single instance it would hold trivially, so the theorems below are meant (and stated) for an
arbitrary family `X`, in particular for the family of all instances satisfying the promises. The
embedding `inp` is not a plain `|0⟩` initialisation: it contains the public slot preparation, the
clean encoding of the native workspace and the known preparations of Theorem `opt:thm:signed`; by
the paper's convention ("Known changes of input or output encoding can be absorbed into surrounding
circuits") this is the full-output error of the paper.

**Theorem** (`native_signed_simulation_eta`). Let `H = D.matrix x` be Hermitian with row and
column Euclidean norms at most `η > 0` for every instance. For every time `t` and
`0 < ε ≤ 1/64`, put `τ = η|t|`, `T = sτ`, `b = √s τ` and
`r_b = log(1/ε)/log(e + log(1/ε)/b)` (`SignedFactorSimulation.rb`). Then
`Simulates (physOracle D) H t ε q` with `q = 0` if `b ≤ ε` and
`q = 48·10¹⁰ (√(Tb) + √(T r_b) + r_b)` otherwise.

`native_signed_simulation` is the same statement for a general entry scale `κ ≥ max |H_ij|` with
`η ≤ √s κ`: `T = sκ|t|`, `b = √s η|t|` and `q = 12·4·10¹⁰ (√(Tb) + √(T r_b) + r_b)`. It is the
form used by the two-norm variant of Appendix B (`κ = μ`).

The proof applies Theorem `opt:thm:signed` to the physical factor with `λ = sκ` and
`δ = η/(√s κ)` and replaces every factor query `I_ι ⊗ U_B`, and every adjoint query, by the
physical factor program on every block (`diagProgram`, `subst`, `simulates_of_factor`).

## Scope and differences from the manuscript

* Only query complexity is claimed here; the gate-level implementation (Theorem `gate:thm:main`) is
  the library `GateOptimalPrecision`; here the known gates (the local factor gates
  and the gates of Theorem `opt:thm:signed`) are exact gates of the query model.
* The local factor is `√|c| V(c)†` with a sign qubit and a failure flag, in place of the two
  success blocks `B_±(c) = √((|c| I ± E(c))/2)` acting on the orientation qubit. The success
  part of the manuscript's local map is the success part of this one followed by the isometry
  `e_± ↦ |±⟩ ⊗ V(c) e_±`, which intertwines the sign reflections; both have `B† Z B = E(c)` and
  `B† B = |c| I`. On the failure flag the unitary extension used here carries `√(1 - |c|) V(c)† v`
  in place of `√(1 - |c|) v`; only the success block enters the factor.
* The entry scale `κ` is a parameter; the manuscript's case is `κ = η`. The decoded entry is
  clipped to the unit disk by the known decoder, so the gate is unitary on every value word;
  oracle values with `|H_ij| ≤ κ` are unchanged.
* Masked native calls use the released three-query construction of Lemma `access:lem:control`, from
  the phase-one locator promise at one fixed clean basis state (the five-query construction of the
  paragraph "Controls on native locators" of Section `gate:sec:native` is its gate-counted form,
  formalised in `GateOptimalPrecision`); the value calls also use it (in place of computing, copying
  and uncomputing the entry word, two queries in Lemma `access:lem:control`). The native cost of
  `U_B` is `12`; it is not optimised (the two unmasked value calls could use one physical call
  each).
* The condition `τ = η|t| ≥ 1` of Theorem `hs:thm:optimal` is not needed here: the theorems hold
  for every time `t`.
* The identity `B† B = D_H/(sκ)` uses Hermiticity (both orientations contribute the same
  absolute row sums), as in the manuscript; the bound `B† B ⪯ η/(√s κ) I` uses only the row and
  column norm promises.
* The constant `48·10¹⁰` is explicit and is not optimised.
-/
