import LinearSystemLowerBound.Theorem
import LinearSystemLowerBound.Readout
import LinearSystemLowerBound.Bridge
import LinearSystemLowerBound.XorLemma
import LinearSystemLowerBound.Matching

/-!
# Linear-system query lower bound: paper-to-Lean entry point

Theorem `qlsl:thm:main` (a matching linear-system query lower bound) and Lemma
`qlsl:lem:xor` (an elementary XOR lower bound) of the accompanying paper are formalised here.
No result from another paper is used; the argument is the paper's weight-growth argument
with weight `(2I - P)^{⊗n}` and parity observable `Z^{⊗n}`.  Two properties of the hard
family are transferred from the `SparseLowerBounds` library of this package (`Bridge.lean`).

* Main theorem: `LinearSystemLowerBound.lower_bound` (constant `1/3072`, as in the paper) and
  `LinearSystemLowerBound.lower_bound_sharp` (constant `1/1536`) in `Theorem.lean`; the case
  of a clean output: `lower_bound_sharp_clean`. For an output read through any fixed linear
  map of norm at most one (for instance an isometry) into output and garbage registers:
  `lower_bound_readout` and `lower_bound_sharp_readout` in `Readout.lean`, which contain the
  unitary case (`lower_bound_sharp_via_readout`).
* The hard family: `LinearSystemLowerBound.family`, `rhsVec`, `target`; its properties
  `family_promise`, `family_real_symm`, `family_indefinite`, `family_sparse`,
  `family_dimension`, `rhsVec_norm`; satisfiable access conditions `exists_access`.  Through
  `SparseLowerBounds` (`Bridge.lean`, `family_eq_submatrix`): the actual condition number
  `κ/16 < ‖A_X‖ ‖A_X⁻¹‖ ≤ κ` (`family_cond`, the remark after the theorem,
  eq. `qlsl:eq:actualconditioning`) and the dimension
  `s κ ln(1/ε)/32 < N ≤ (s - 1) κ ln(1/ε)` (`family_dimension_sharp`).
* Matching upper bound in the same model: `LinearSystemLowerBound.upper_meets_lower` and
  `physOracle_admissible` in `Matching.lean`.
* Lemma `qlsl:lem:xor`: `LinearSystemLowerBound.Boolean.xor_lemma` and `xor_lemma_count` in
  `XorLemma.lean`; for adaptive protocols over any oracle family whose labels have weight
  growth `C^{w l}`: `LinearSystemLowerBound.tree_xor` in `Weight/TreeBound.lean`.

**Parameters** (`Parameters.lean`).  For `κ ≥ 32`, an integer `s ≥ 5` and `0 < ε ≤ 1/64`:
`R = 2^{⌊log₂(κ/2)⌋}`, `m = 2^{⌊log₂(s-1)⌋}`, `L = ln(1/ε)`,
`n = ⌊((R - 1)/2) ln(1/(16ε))⌋`, `r = 1 - 1/R`, `2n` clock values.

**The hard family** (`Hard/`).  Inputs are `n` marked positions `X = (j_1, …, j_n)`
(`Inp κ ε s = Fin n → Fin m`); indices are sector, clock value and gadget position
(`Ind κ ε s = Bool × Fin (2n - 1 + 1) × Fin m`, with `2n - 1 + 1 = 2n` clock values by
`clock_count`, dimension `N = 4nm`).  The gadget is
`(U_j)_{a,b} = 2/m - [j = a - b - 1]` (`Hard.gadget`); the open clock
`T_X = ∑_{t ≤ 2n-2} L_t ⊗ |t+1⟩⟨t|` uses `L_t = U_{j_{t+1}}` for `t < n` and the identity
afterwards (`Hard.clock`); the matrix is the Hermitian dilation of `C_X = (I - r T_X)/2`,
written `A_X = (Π - r Q_X)/2` (`Hard.hardMatrix`), and `b = |false, 0, 0_L⟩`.

**Access model.**  The released native sparse access `NativeSparseBlockEncoding.Data` (in-place
row and column location oracles and the additive entry-value oracle).  The lower bound holds
for every data `D` with `D.matrix = family κ ε s`, input-independent location oracles, and a
value table that is a fixed encoding of the entry
(`D.table x α = enc α (D.matrix x α.1 α.2)`).

**Algorithms.** The released adaptive protocols `SparseLinearSystems.Protocol.Tree O F E`
(fresh measured runs with classical branching, then bounded fresh-trial preparations; the model
of Theorem `qls:thm:main`), on any workspace `K`, with any finite-dimensional output space `E`.
A fixed isometry `V : E ≃ EuclideanSpace ℂ (Ind κ ε s × G)` identifies `E` with the output
register and a garbage register `G` (any finite type), and the output state is the partial
trace over `G` (`ptrace`, characterised by `tr(B Tr_G A) = tr((B ⊗ I_G) A)` for all `B`:
`trace_comp_ptrace` and `ptrace_unique`). The `*_readout` forms replace `V` by any fixed linear
map `e : E → EuclideanSpace ℂ (Ind κ ε s × G)` with `‖e v‖ ≤ ‖v‖` (an isometry `e† e = 1`
qualifies: `readout_contraction_of_isometry`) and use the reduced state `Tr_G (e ρ e†)`; this
allows output spaces whose dimension is not a multiple of `N`, such as qubit registers (that an
algorithm accurate on a larger output register meets this hypothesis for a suitable isometry is
a channel argument, not formalised). Every oracle label must be admissible
(`Native.Admissible`): either a native call (`Native.NativeCall`: in a fixed isometric layout
`K ≃ ⊕_{σ ∈ S} NSpace`, every spectator branch applies the identity, one native query or the
inverse of one — this includes spectators, controlled and masked versions and inverses; its
weight is at least one), or an input-independent unitary (for instance the right-hand-side
preparation; any weight). The query count is `T.worstCost w`, the maximum over all transcripts
of the weighted number of calls, every fresh run counted.

**Guarantee** (hypothesis of `lower_bound`).  For every input: success probability
`2/3 ≤ T.successMass x`, and the reduced conditional output
`ptrace (V.conjStarAlgEquiv (T.conditionalDensity x))` is within spectral trace distance `ε`
of `|x_A⟩⟨x_A|`, `x_A = A⁻¹ b / ‖A⁻¹ b‖` (`target`).  For a clean output (a one-point
garbage register, `lower_bound_sharp_clean`) these are the success and accuracy guarantees of
Theorem `qls:thm:main`; its endpoint also proves that runs are unitary and that outputs are
density operators, which are not needed here.

**Conclusion.**  `κ √s ln(1/ε) / 3072 < T.worstCost w` (`lower_bound`), and
`κ √s ln(1/ε) / 1536 < T.worstCost w` (`lower_bound_sharp`); the same for the `*_readout`
forms.

**Proof map.**  Module paths are relative to `LinearSystemLowerBound/`.

* Weight growth (`Weight/`): families over hidden inputs, Kronecker weights and splitting at a
  coordinate (`Coordinates`); one-coordinate estimates: `‖w⁻¹‖ ≤ 1`, the single-bit growth
  `‖w Ô φ‖ ≤ (1 + 2/√m) ‖w φ‖` via `w Ô w⁻¹ = Ô - [P, Ô] w⁻¹`, and `‖w⁻¹ Z w⁻¹‖ ≤ 1/2`
  (`OneCoordinate`); weight growth of oracle families, closed under products, block diagonals
  and layouts, and of circuits (`Growth`); positive semidefinite kernels, the potential
  `pot G = Re ∑ (WᴴW)_{jj'} G_{jj'}`, Schur products with Gram matrices, the measurement split
  and the parity bound `2^{-n}` (`Kernel`); the induction over adaptive protocols and the XOR
  bound `tree_xor` (`TreeBound`); the partial trace over a garbage register, `B ⊗ I_G` and
  the identification of output spaces (`PartialTrace`); trace-distance contractivity and the
  bias `(2/3)(p - 2ε)` for clean outputs and for outputs with a garbage register (`Bias`).
* The hard family (`Hard/`): gadget, orthogonality and logical action (`Gadget`); clock,
  dilation, right-hand side and the exact history solution `hard_mul_sol` (`Clock`); norm
  bounds, invertibility, inverse norm, symmetry, one-bit entries and support (`Dilation`);
  decoder and answer probability `r^{2n}/(1 + r^{2n})` (`Answer`); weight growth of native
  queries and admissible labels (`Native`); native data with permutation locators and a
  three-bit word code (`Data`).
* Parameters and the final count (`Parameters`), main theorem (`Theorem`), readout through a
  contraction (`Readout`: `corr B (e A e†) = corr (e† B e) A` by cyclicity of the trace, and
  `e† (B ⊗ I_G) e` is a contraction), Boolean XOR lemma (`XorLemma`), matching upper bound
  (`Matching`).
* The bridge to `SparseLowerBounds` (`Bridge`): both gadget formulas query the bit at
  position `a - b - 1` (`gadget_eq`); `A_X` is `SparseLowerBounds.LinearSystems.hardMatrix`
  reindexed by the relabelling `bridge` of sector and clock (`hardMatrix_eq_submatrix`);
  reindexing is conjugation by a permutation unitary, which preserves the operator norm and
  the norm of the inverse (`norm_matrixOperator_submatrix`,
  `norm_inverse_matrixOperator_submatrix`); then `quarter_lt_cond` gives `family_cond` and
  `dim_bounds` gives `family_dimension_le`.

**Formalisation choices.**

* Adaptivity — fresh measured runs with classical branching, uniformly random trial labels
  and repeated trials — is handled by carrying a positive semidefinite Gram kernel through the
  protocol (the coordinate-free form of the paper's purification); a heralded failure
  contributes no output, which is the paper's random-bit convention.  Measurements inside a
  run followed by classically controlled operations can be deferred in the usual way; since a
  native call may apply different queries on different branches and is counted once, this
  does not increase the worst-case count (this reduction is not formalised).
* A value query is estimated directly: on every address block it is a translation of the
  value register depending on one bit, so it costs one growth factor `(1 + 2/√m)²`.  The
  paper simulates it by two Boolean queries, which costs a factor `2` in the constant; the
  formal proof therefore gives `1/1536`, and the paper's `1/3072` follows.
* The location oracles of the hard data are input-independent, so a label that calls only
  them is also an input-independent unitary and may have weight zero: the bound holds for the
  number of value queries alone.
* The lower bound is stated for every native data with the hard matrices, input-independent
  locators and an entry-determined value table; `exists_access` constructs one (fixed
  permutation locators, an address-independent word code with five entry values).
* The parameters `R` and `m` are powers of two as in the paper.  Not formalised: the remark
  on padding to larger dimensions.
-/
