import SparseGateAccounting.Accounting
import SparseGateAccounting.Native
import SparseGateAccounting.Original

/-!
# The gate accounting of Theorem `hs:thm:gates` for general sparse access: statement guide

Manuscript: Theorem `hs:thm:gates`, equations `hs:eq:gate-known`, `hs:eq:gate-Gzero` and
`hs:eq:gate-total`, with the schedule of `hs:eq:gate-schedule` and `hs:eq:gate-clocks`. For the
private Cayley operation with an arbitrary controlled implementation of costs `G_C(ξ)`, `A_C(ξ)`,
the baseline circuit uses at most `6 d` private operations and `O(d (C_J + a + m + r))` other gates
before synthesis; with `ξ = ε/(24 d)` and `G_syn = C₀ [d (C_J + a + m + r) + A_C(ξ)]`, the
additional gates are `O(d G_C(ξ) + G_syn log((G_syn + 1)/ε))` and the work qubits
`O(A_C(ξ) + a + m + r)`, with error at most `ε` on all output registers, including an untouched
reference.

**Setting.** Sparse access of general size, `GeneralSparseAccess.QData X N s k b`, with any public
decoder `D.val`; an instance `x` whose matrix is Hermitian with row and column Euclidean norms at
most `η > 0`; every rescaling `0 < γ ≤ 1`, which contains the manuscript's choice; `0 < ε ≤ 1`.
Nothing is assumed about the action of the locators outside the valid list inputs.

**The supplied circuit.** `pc : PrivC k b Z bT bP A` is any list of instructions calling the
supplied oracles `D.prims x`, on the enable wire, the private register and the work wires. Its
promise `PrivOK` says that on clean work wires it is within `ξ` of the enable-controlled private
Cayley operation of the construction. So `G_C = nGatesN pc`, the gates inside the oracles are not
counted, and the work is `A_C = |Z| + bT + bP + A`; the qubit count adds three flag wires of the
controlled `U_J` gates. The promise is a hypothesis of the theorems below; the module
`SparseGateAccounting.Native` constructs such a circuit and derives its promise (see *The
constructed circuit*).

**The construction.** The private operation is that of the padded data with the validity decoder,
normalised by `η` (`normPad`): `k + 1`-bit index words and `s' = 2^⌈log₂ s⌉` slots, `s ≤ s' < 2 s`
(`GeneralSparseAccess.sP_lt`). Hence `a = k + 2`, `C_J = ⌈log₂ s⌉ + 1` (`padUJ`, `padUJ_length`),
and the schedule has `α = η √s' / γ` and `Q = ⌈max{1, γ √s'}⌉`, the manuscript's values with `s'`
in place of `s`; they coincide when `s` is a power of two. The clock promises of the abstract
circuit (`D` unitary, `R₁` the inverse of `1 - D`, `‖R₁‖ ≤ Q`, the boundary and endpoint promises)
are discharged by `GateBinary` on this data, with `U_J` the Hadamard gates `padUJ`.

**The theorems.** With `τ = αT` (`clock`), `d = dg`, `m = slotMs`, `r = rg`, and
`G₀ = synG = 200 (d+1)(a+m+r+1) + 84 d C_J`:

* `sparse_known_gates` (`hs:eq:gate-known`): instantiates `GateSchedule.sim_supplied_ms`. Valid
  instructions; exactly `6 d` times the primitive calls of `pc`; gates exactly `6 d G_C` plus the
  known gates; known gates at most `G₀ ≤ 884 d (C_J + a + m + r)`; the exact qubit count; error at
  most `ε/2 + 6 d ξ`.
* `sparse_gate_total` (`hs:eq:gate-Gzero`, `hs:eq:gate-total`): instantiates
  `GateSchedule.sel_simulation_ms`, for a gate set with synthesis of length `c₁ log(1/ζ) + c₀` and
  a circuit `pc` over the gate set with `24 d ξ ≤ ε`; `ξ = ε/(24 d)` meets this (`xi_budget`). Valid
  gates of the set; exactly `6 d` times the primitive calls of `pc`; at most `G₀` synthesised
  occurrences; at most `6 d G_C + G₀ (c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates; the exact qubit count
  `k + 1 + (2a + 3m + 6r + 3) + (|Z| + bT + bP + A + 3) + |Xs|`; error at most `ε`; the schedule
  `d = k' (⌈32Q⌉ - 1)`, `k' = ⌈4W/Q + log₂(4096/ε)⌉` (`depthMs`),
  `d ≤ 128 W + 32 Q (log₂(4096/ε) + 1)`, `2^m` the least power of two at least
  `max{2, 4τ, √(τ³/(3ε))}`, `r = ⌈log₂(2d + 2)⌉`.
* `sparse_gate_total_signed`: instantiates `GateSchedule.sel_simulation_ms_signed`; every real
  time: the compiled circuit of `|t|` for `t ≥ 0`, its literal inverse for `t < 0`, with `|τ|` the
  clock of `|t|` (`abs_clock`).

**The constructed circuit** (`SparseGateAccounting.Native`). `privOp D η hη γ` is the native
private operation of the normalised padded data: the compute circuit `computeV` of the binary sparse
oracles of the padded data, the orientation wire and the decoder `γ √s' decode / η` of the padded
data with the validity decoder (`normPad_dec`), with every padded oracle call replaced by its
implementation `GeneralSparseAccess.implPE N s` on the supplied oracles of `D` and the implementation
ancillas `AW k b` joined to the scratch (`GeneralSparseODE.substOp`). `privCirc hS δ D η hη γ ar` is
its native implementation `GateNative.privMacro` with an arithmetic `ar` of the padded data on the
base wires (`GeneralSparseODE.liftA`), compiled selectively once with the synthesis budget `δ`
(`GateSelective.privSel`, synthesis ancillas `Xs` joined to the scratch). So
`Z = (SZ (k+1) b ⊕ AW k b) ⊕ Xs`, with `|SZ (k+1) b| = 6 (k+1) + 2 b` and `|AW k b| = 6 k + 6 + 2 b`.

* `privCirc_privOK`: for every instance, `PrivOK` with `ξ = δ + 4 ζ` whenever `ar` computes the
  rotation parameters of the decoded entries within `ζ` (`GateNative.ArithOK`). It is proved from the
  native identity of the padded data (`GeneralDecoder.sparse_nativeOKD`, the all-zero word being a
  slot: `normPad_zero_slot`), the implementation of the padded oracles by the supplied ones
  (`GeneralSparseAccess.implOKE`, `GeneralSparseODE.nativeOK_substOp`), the native implementation
  (`GateNative.privMacro_approx`) and the selective compilation (`GateSelective.privSel_spec`). No
  clock, Cayley or decoder correctness is assumed.
* `privCirc_spec`: valid, gates of `𝒢`, exactly `2 |V'|_calls` primitive calls with at most
  `3 (2[row] + 2[column] + [value])` calls of each kind in the compute circuit `V'`
  (`privOp_calls`: `GeneralSparseAccess.kindOK_implPE`), `|V'| ≤ 28 (k+1) + 5 (30 (k+1) + 4 b)`
  (`privOp_gates`), and `G_C = |privCirc| ≤ G_P (1 + c₁ log((G_P + 1)/δ) + c₀)`,
  `G_P = 2 |V'| + 2 |arith| + 2 bP + bT + 1` (`privG`, `selGates_le`).
* `exists_arith`: the arithmetic interface of the decoder, `ManuscriptConformance.comp_rotArith` on a
  range `[K₀, K]` containing `γ √s' / η`, gives `ar`, fixed by the public data, with gates and work
  wires at most `(3 c_A + 18)(b_data + k + 1 + log₂(1/ζ) + 1)^{max d_A 1}`
  (`ManuscriptConformance.comp_decArith_padDataE`: the validity of the index pair, the arithmetic of
  the value word, the copies under the validity and the uncomputation).
* `sparse_gate_native`, `sparse_gate_native_signed`: `sparse_gate_total` and
  `sparse_gate_total_signed` for `pc = privCirc …` under `24 d (δ + 4 ζ) ≤ ε`.
* `sparse_gate_constructed` (the headline): from the synthesis hypothesis and the arithmetic
  interface alone, with `ζ = ε/(192 d)` and `δ = ε/(48 d)` (`budget_facts`): one arithmetic and one
  circuit, fixed before the instance, with the counts of `privCirc_spec`, and on every admissible
  instance: valid gates of `𝒢`, exactly `6 d` private calls and so exactly `12 d |V'|_calls`
  primitive calls, at most `G₀` synthesised occurrences outside the private circuit, at most
  `6 d G_C + G₀ (c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates, `k + 1` system qubits and
  `(2a + 3m + 6r + 3) + (|SZ| + |AW| + |Xs| + bT + bP + A + 3) + |Xs|` further qubits, full-output
  error at most `ε` (both forms below), and the schedule of `sparse_gate_total`.

So the manuscript's interface for the private operation (costs `G_C(ξ)`, `A_C(ξ)` at accuracy `ξ`) is
met by an actual circuit derived from the permitted local arithmetic: `G_C` is polynomial in
`k + b + log(1/ξ)` through the arithmetic interface and the synthesis length, `A_C` is `O(k + b)`
plus the arithmetic work. The schedule of these theorems is that of `s'`; the next paragraph keeps
the original `s`.

**The original sparsity** (`SparseGateAccounting.Original`). The Hadamard circuit `padUJ` prepares the
uniform superposition of all `s'` slot words, which is why the schedule above has `s'`. With a
boundary circuit for the `s` original slots the schedule keeps `s`:

* `restrictSlots`, `padDataS`, `normS`: the padded data with the validity decoder restricted to its
  first `s` slots, which cover every nonzero entry (`padDataS_row_covers`,
  `padDataS_column_covers`: the covering slot of an entry is the slot of the original list); the same
  entries, table, decoder and oracles (`prims_normS`), so the padded calls are implemented from the
  supplied ones as before;
* `UJPrep UJg slot en`: the promise of a supplied boundary circuit `U_J` (a list of gates with at most
  three controls on the ancilla and system wires) that it prepares the boundary state of the slots on
  the clean ancillas, `U_J ι₀ = J ι₀`; `padUJ_prep` (`hadUJ_prep`): the Hadamard circuit meets it
  when `s` is a power of two. For other `s` it is the uniform-range preparation over the `s` slot
  words, **supplied, not constructed**, with its gate count `C_J = |U_J|` charged;
* `boundary_lift_of`, `R1bin_boundary_of`, `R1bin_endpoint_of`: the boundary and endpoint promises of
  the clock for any supplied `U_J` with `UJPrep`, for sparse data with any number of slots (the other
  clock promises, `norm_R1bin_le` and the rest, hold for every slot count);
* `sparse_gate_total_s`, `sparse_gate_total_signed_s`: `sparse_gate_total` and
  `sparse_gate_total_signed` with `α = η √s / γ` (`clockS`, `abs_clockS`, `evolutionS_eq`),
  `Q = width s γ = ⌈max{1, γ √s}⌉`, `d = dgS`, `r = rgS`, `C_J = |U_J|` and
  `G₀ = synGS = 200 (d+1)(a+m+r+1) + 84 d C_J`, for a supplied private circuit with the promise
  `PrivOKS` (the private Cayley operation of `normS`);
* `privOpS`, `privCircS`, `privCircS_privOK`, `privCircS_spec`, `exists_arithS`: the constructed private
  circuit for `normS` (decoder rescaled by `γ √s`), its promise derived as above, the arithmetic
  interface at `γ √s / η`;
* `sparse_gate_original` (the headline with the original `s`) and `sparse_gate_original_signed`: the
  conclusions of `sparse_gate_constructed`, with exactly `6 d` private calls at the degree `d` of `s`,
  `ξ = δ + 4 ζ = ε/(24 d)` at that `d`, and the schedule `d = k' (⌈32Q⌉ - 1)` with `Q = width s γ`.

So, with a boundary circuit for the original slots supplied, the printed schedule at `s` is admissible
for the padded construction: the private-call count `6 d`, the accuracy `ξ = ε/(24 d)` and the known
gates are those of the original sparsity.

**The error.** Each bound is stated twice, as an operator norm with `R` an arbitrary Hilbert space
acting as the untouched reference: on the padded index register against the evolution of
`D.padDataE.matrix x`, and on the embedding of the `k` index qubits with a clean marker
(`error_low`) against the evolution of `D.padMat x`, the matrix extended by zero to the index words
`≥ N`.

**Differences from the printed form.** The count `G₀` does not contain `A_C`: the elementary
instructions of this circuit act on the simulator wires and the three flag wires only, so its known
gates do not depend on
`pc`, and `G₀ ≤ 884 d (C_J + a + m + r) ≤ G_syn` for `C₀ ≥ 884` (`synG_le`). The counts are explicit
rather than orders. The conclusions hold for every `γ ∈ (0, 1]`. In `Accounting` and `Native` the
schedule has `s'` in place of `s`, as above: when `s` is not a power of two, `d`, `m`, `r` and
`ξ = ε/(24 d)` are those of `s'`, so the supplied circuit is required at that accuracy; `Original`
keeps `s` given a supplied boundary circuit for the `s` slots. The gate set is closed under adjoints (`AdjClosed`)
and the synthesis hypothesis is the combined `Synthesis`; `Synthesis.of_parts` and
`GateSynthTrials.extra_hyps` reach them from the printed assumptions, with the counts then over the
closed set. The query order of `hs:thm:main` is not restated: the call count is exactly `6 d` times
that of `pc`, and for `ε ≤ 1/2`, `GateSchedule.degreeMs_cost_le` gives
`6 d ≤ 3880 (W + Q log(1/ε))`.
-/
