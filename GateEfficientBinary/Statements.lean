import GateEfficientBinary.Sparse.Budget

/-!
# Gate-level construction from binary data: paper-to-Lean entry point

The native gate-level theorems of the library `GateEfficientNative` (Theorem `hs:thm:gates` and
Theorem `ode:thm:gates` of the accompanying paper, before finite-set synthesis) take as hypotheses,
as the paper does ("Under the assumptions of Theorem `hs:thm:main` and the implementations just
specified"; for the ODE solvers "with the source certificates and circuits specified above"), the
entry decoding and the reversible angle arithmetic (`GateNative.ArithOK`), the public compute
circuit of the private Cayley operation with its native identity (`GateNative.NativeOK`) and the
boundary unitary `U_J` given by elementary gates (the ODE solvers also take source circuits). This
library constructs these three ingredients for sparse Hamiltonians given by binary sparse oracles,
from the oracles themselves, and instantiates Theorem `hs:thm:gates` (time-independent Hamiltonians)
and the pre-synthesis form of its consequence `hs:eq:gate-binary`. The released libraries are
unchanged; the statement file of `GateEfficientNative` predates this library. No result from another
paper is used. All declarations below are in the namespace `SparseHamiltonian.GateBinary`
(subnamespace `Cordic` for the CORDIC analysis), unless stated otherwise.
References to the manuscript use its labels.

* Theorem `hs:thm:gates` for binary data: `binary_simulation`, with the circuit `binarySim`;
  the budget form of equation `hs:eq:gate-binary` before synthesis, with the rescaling chosen
  before the data: `binary_simulation_budget`.
* The native identity `NativeOK` from the binary sparse oracles: `sparse_nativeOK`, with the
  primitive oracles `prims`, the compute circuit `computeV` and the native private operation
  `sparseOp` (public: `sparseOp_public`; counts: `computeV_nGates`, `computeV_nCalls`).
* The entry decoding and the angle arithmetic, `ArithOK` for the CORDIC circuit:
  `cordicArith_ok`, with the counts `cordicArith_counts` and the parameters `params_fields`.
* `U_J` from Hadamard gates: `hadUJ`, `hadUJ_ok`, `hadUJ_length`, and the boundary
  identity `boundary_lift`.

**Binary data.** `D : NativeSparseBlockEncoding.Data X n (Cfg (VW b)) s` is the released native
sparse data whose stored entries `D.table x (i, j)` are two `b`-bit words (`VW b = Fin b ⊕ Fin b`,
real part `inl`, imaginary part `inr`), read as two's complement integers `X`, `Y` (`twos`); the
decoder hypothesis is `D.decode e z = c₀ (X + i Y)` for a public scale `c₀ > 0` (`gauss`). The
indices are `k`-bit words, `en : Cfg (Fin k) ≃ n`, so the dimension is `N = 2^k`. There are
`s = 2^σ` slots, `σ ≤ k`, and the slot embedding has exactly the index words supported on the
lowest `σ` bits as its range (`hrange`, `lowWord`); so the all-zero word is a slot (`zIdx`).
Other dimensions and sparsities are reached by padding the matrix with zero rows and columns and
the location lists with zero entries up to powers of two.

**Primitive oracles** (`prims D en x`). They act on the qubits `PY k b = EW k ⊕ VW b` of an edge
register (first index `inl`, second index `inr`, `2k` qubits) and `2b` value qubits:
`rowLocation` and `columnLocation` apply the full unitary location oracles `D.rowOracle x` and
`D.columnOracle x` of the data to the edge register in the computational basis (`qlift (phiE en)`,
the payload untouched), and `value` XORs the stored bits `D.table x (i, j)` into the value qubits
(`valPerm`). As in the released data model, the row oracle maps `|i, slot k⟩` to
`|i, rowloc i k⟩` and the column oracle maps `|j, slot k⟩` to `|colloc j k, j⟩`, so both act in
place on the edge register as a whole. They are unitary (`prims_isUnitary`); as in the native
model, calls are never controlled and every call (forward or inverse) counts once.

**The native private operation.** The private register is `PR k = Fin (k+1) ⊕ Fin k`: ancilla
`0` is the orientation, ancillas `1, …, k` the second index and the `k` system qubits the first
index (`oPR`, `ixPR`, `phiPR`). The scratch `SZ k b` has `6k + 2b` qubits (`card_SZ`): a dummy
edge register, a row and a column reference register, and the value wires. The compute circuit
`computeV k b` makes one row and one column call on the clean reference registers (writing the
images of the all-zero edge, by `row_valid`, `column_valid`), applies the row location oracle to
the index wires when the orientation is `0` and the column location oracle when it is `1`, each
by the controlled-call gadget (`gadget`, `gadget_agrees`: Fredkin swaps with the dummy register
and an XOR of the reference, `7 · 2k` gates), and makes one value call: `28 k` elementary gates
(`computeV_nGates`) and `2` row, `2` column and `1` value calls (`computeV_nCalls`). The decoder
of `sparseOp k b κ` is `binDec`, `κ (X + i Y)` of the value wires.

* `sparse_nativeOK`: `NativeOK (prims D en x) (sparseOp k b (γ √s c₀)) (selOp (fun _ => D̂))`
  with `D̂ = unconj (qlift (phiPR en) (FixedNativeCayleySimulation.action D x γ))`: on clean
  scratch, `V† R_val V` acts as the qubit lift of the private Cayley operation of the released
  sparse simulation (the locator conjugation `L† A L` of the exact edge action at rescaling `γ`),
  for every input `x` and every `γ`. Proof: on clean scratch `V` is the lifted locator followed
  by a permutation of basis configurations (`compute_cleanEmb`), and the decoded rotation commutes
  past that permutation into the lifted edge action (`rdec_sigma`, `qmat_action`).

**The angle arithmetic** (`cordicArith b xw yw κ ζ`, `Cordic/*`). A single-assignment program
of ripple-carry adders and subtractors of width `w` (`Reversible/*`: `crun_adderG`,
`ROp.crun_gates`, `crun_progG`) runs two stages of integer CORDIC vectoring with floor quotients:
stage 1 computes `arg (X + i Y)` and the radius, stage 2 computes `arctan (κ |X + i Y|)` from the
stage-1 radius; the scaling `2^T`, `T = n²`, makes every quotient exact (`toC_citer`), and the
angle constants are rounded (`cacc_error`). The circuit runs the program, copies the angle words
(`φ`: the low `bP` bits of the stage-1 angle; `θ`: the clamped stage-2 angle) and runs the program
backwards. `cordicArith_ok`: for `b ≥ 1`, input wires `xw`, `yw` that are distinct and avoid the
orientation wire, `κ > 0` and `0 < ζ ≤ 1`, the arithmetic hypothesis
`ArithOK (cordicArith b xw yw κ ζ) o (binDec xw yw κ) ζ` holds: classical controlled NOT gates
with at most three controls that write the words and restore their work wires, independently
of the orientation wire, with `|θ̃ - 2 arctan |z|| ≤ ζ` and, for `z ≠ 0`, `φ̃ = arg z` up to `ζ`
modulo `2π` (`theta_error`, `phi_error`, `params_theta`, `params_phi`). `cordicArith_counts`,
`params_fields`: at most `156 w (n+1) + bP + 2 bT` gates and `1 + 2w + (6 (n+1) + 1) w` work
wires, with `n = ⌈log₂ ⌈8/ζ⌉⌉ + 2` steps per stage, words of `bP = bT = n + ⌈log₂ (n+2)⌉ + 4`
bits and register width `w = 2 n² + ⌈log₂ ⌈κ⌉⌉ + n + 5 + ⌈log₂ ⌈1/κ⌉⌉ + b + 2 bP + 8`.

**The boundary** (`Sparse/Boundary`). `hadUJ k σ hσ` are `σ + 1` Hadamard gates, on the
orientation wire and on the lowest `σ` wires of the second index (`gRun_hadList_bas`).
`boundary_lift`: for every operator `A` of the oriented edge space,
`(U_J ι₀)† Â (U_J ι₀) = qlift en (J† A J)` with `Â = unconj (qlift (phiPR en) A)` and the fixed
boundary `J = FixedLocatorConjugation.fixedBoundary D.slot` of the released simulation.

**Theorem `hs:thm:gates` for binary data** (`binary_simulation`). Hypotheses: the binary data
above with `b ≥ 1`; an input `x` whose matrix `H = D.matrix x` is Hermitian with row and column
Euclidean norms at most one; a rescaling `0 < γ ≤ 1`; a time `τ ≥ 0`; `0 < ε ≤ 1`; an arithmetic
accuracy `0 < ζ ≤ 1` with `48 d ζ ≤ ε`, where `d = fDeg Q τ' qbar (ε/2)` is the filter degree for
`Q = width s γ = ⌈max(1, γ √s)⌉`, `qbar = moment γ = (1 + γ²)/2` and the rescaled time
`τ' = time s τ γ = τ √s / γ`. The circuit `binarySim` is the native circuit
`GateNative.nativeSim` with `U_J = hadUJ`, the native private operation `sparseOp` and the
arithmetic `binArith` (the CORDIC circuit on the value wires at scale `κ = γ √s c₀`).
Conclusions: every instruction is valid; for every selection `p : Query → Bool` of oracle labels
the circuit makes exactly `12 d` times `2` row-location, `2` column-location and `1` value calls
of the selected labels; it uses at most
`200 (d+1)(k + 1 + m + r + 1) + 84 d (σ + 1) + 6 d (56 k + 2 |circ| + 2 bP + bT + 1)` elementary
gates (`|circ|`, `bP`, `bT` of `binArith`, bounded by `cordicArith_counts`); it has
`k + (2 (k+1) + 3 m + 6 r + 3) + (6 k + 2 b + bT + bP + A + 3)` qubits; its full output on the
system embedding is within `ε` of `exp(-iτĤ)`,

`‖nrun (prims D en x) (binarySim …) ∘ sysEmb io - sysEmb io ∘ exp(-iτĤ)‖ ≤ ε`,

where `Ĥ = qlift en (matrixOperator H)` is `H` on the `k` system qubits (index `i` ↔ word
`en.symm i`), `sysEmb io` puts every other qubit in `0` (input and target alike), and the payload
`R` is an untouched reference, any complex Hilbert space; `d ≤ 128 (τ' qbar + Q (1 + log (6/ε)))`;
and the time and phase registers have `steps τ' (ε/6) ≤ 2^m < 2 steps τ' (ε/6)` and
`2 d + 2 ≤ 2^r ≤ 4 (d + 1)`. The clock promises of `native_simulation` are
discharged by transporting the released query-level analysis (`FixedNativeCayleySimulation`)
through the qubit lift (`Dbin`, `R1bin`, `Hbin`; `R1bin_boundary`,
`R1bin_endpoint`, `norm_R1bin_le`, `norm_Hbin_le`, `Hbin_exponent`), using that the lift is a
unital star algebra homomorphism (`qliftHom`) and a contraction (`norm_qlift_le`).

**The budget** (`binary_simulation_budget`, equation `hs:eq:gate-binary` before synthesis). For
`s ≥ 1`, `τ ≥ 0`, `0 < ε ≤ 1/2` and `q = √s τ + √(s τ log(1/ε)) + log(1/ε)`
(`ImprovedPrecisionBudget.shape`), the released precision budget gives one `γ ∈ (0, 1]` with
`γ √s ≥ 1`, chosen from `s`, `τ` and `ε` before the data and the input (the existential precedes
every data binder), with `d ≤ 4608 q`, `τ' ≤ √s q`, `2^m < 2 (2 + 4τ' + √(6τ'³/ε))` and
`2^r ≤ 4 (4608 q + 1)`. For all binary data with `s = 2^σ` slots, every admissible input and
every `0 < ζ ≤ 1` with `221184 q ζ ≤ ε`, the circuit makes at most `55296 q` times `2` row, `2`
column and `1` value calls, uses at most `200 (4608 q + 1) (G_C + (σ + 1) + (k + 1) + m + r + 1)`
elementary gates with `G_C = privGates = 56 k + 2 |circ| + 2 bP + bT + 1`, and has full-output
error at most `ε`. By `cordicArith_counts` and `params_fields`, `G_C` is polynomial in `b`, `k`,
`log (1/ζ)` and `|log κ|`; with `ζ` of order `ε / q` and the bounds on `m` and `r`, this reads
`q · poly(b, log N, log ((q+1)/ε), |log c₀|)` for `N = 2^k` (read off from these bounds, not a
separate Lean statement).

Every theorem of the library is axiom-audited in `GateEfficientBinary/Audit.lean`.

**Formalisation choices.**

* Entries are stored as two `b`-bit two's complement components with one public scale `c₀`; the
  slots are the index words supported on the lowest `σ` bits, so that `U_J` is `σ + 1` Hadamard
  gates. Other fixed-point formats and other slot sets need another decoder or another `U_J`.
* The dimension `N = 2^k` and the sparsity `s = 2^σ` are powers of two (zero padding), instead of
  the paper's validity predicate for unused index words and uniform-range preparation for
  general `s`; padding `s` costs at most a factor `√2` in `√s`.
* The controlled location calls of the paper's compute circuit are implemented with uncontrolled
  calls by the gadget, which costs one extra (reference) call per oracle and `14 k` gates per
  gadget; the reference calls are uncomputed by `V†`.
* The theorem holds for every rescaling `0 < γ ≤ 1` and every arithmetic accuracy `ζ` with
  `48 d ζ ≤ ε`; the budget form takes `γ` from the released precision budget.

**Not formalised.** The time-dependent gate-level simulation (Theorem `hs:thm:time` with the circuit
of `hs:thm:gates`) (`native_time_simulation`) and Theorem `ode:thm:gates` from binary data: they
need slot-selected (time-indexed) binary oracles and, for the ODE, reversible arithmetic that
combines the entries of `A_H` and `A_L` with the LCHS weights; these remain hypotheses of
`GateEfficientNative`. Gate synthesis over a finite gate set (the term `G_syn log((G_syn+1)/ε)` of
`hs:eq:gate-total`).
-/
