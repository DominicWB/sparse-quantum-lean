import GateEfficientBinaryODE.Solver
import GateEfficientBinaryODE.Synth

/-!
# The dissipative solver from binary data: paper-to-Lean entry point

The native gate-level dissipative ODE solver of `GateEfficientNative` (Theorem `ode:thm:gates` of
the accompanying paper, constant coefficients, before finite-gate-set synthesis:
`GateNative.native_ode_solver`) takes as hypotheses the gates of the boundary unitary `U_J`, a
native private operation (compute circuit, orientation wire and decoder) with its native identity
(`GateNative.NativeOK`), the reversible angle arithmetic (`GateNative.ArithOK`), the source
circuits, and the instance conditions of the released solver (`GateODE.Params.InstanceOK`), among
them the clock promises of every label. For dissipative ODEs `x' = -M x + b` whose matrix `M` is
given by binary sparse oracles, this library constructs the gates of `U_J` (from the slot
layout), the native private operation with its native identity (from the oracles) and the
arithmetic, and proves the instance conditions on `U_J`, the private operations and the
Hamiltonian and dissipative parts: unitarity, self-adjointness and the clock promises, and, from
energy bounds and the accretivity of the input, the norm and accretivity conditions; the source
circuits (with their accuracy `ζs` and the budget `24 d ζ + 2 ζs ≤ ν`) and the source and target
conditions of the instance remain hypotheses. It instantiates `native_ode_solver`
(`binary_ode_solver`, with the counts `binary_ode_counts` and the explicit worst-case gate count
`binary_ode_gate_count`) and its finite-gate-set form `GateSynth.native_ode_solver_synth`
(`binary_ode_solver_synth`, a partial formalisation, under this package's format hypotheses, of
the finite-set statement of Theorem `ode:thm:gates`). The released libraries are unchanged; the
statement files of `GateEfficientBinary`, `GateEfficientBinaryTime` and `GateEfficientSynthesis`
predate this library and list `ode:thm:gates` from binary data as not formalised. No result from
another paper is used, except single-qubit synthesis and the decomposition of controlled gates as
the hypothesis `GateSynth.Synthesis` of the finite-gate-set form. All declarations below are in the
namespace `SparseHamiltonian.GateBinaryODE`. References to the manuscript use its labels.

* Theorem `ode:thm:gates` for binary data, constant coefficients: `binary_ode_solver`,
  `binary_ode_counts`, `binary_ode_gate_count`; over a finite gate set (a partial formalisation,
  under this package's format hypotheses, of the finite-set statement of the theorem):
  `binary_ode_solver_synth`. The public data `Pub`, its conditions `Pub.OK`, the released parameters
  `Pub.params` (`Pub.params_ok`) and the native preparation `Pub.prep`.
* `U_J` from Hadamard gates: `hadUJ4`, `hadUJ4_ok`, `hadUJ4_length`, `boundary_lift4`.
* The native private operation and its native identity: `odeOp`, `computeV4` (`odeOp_public`,
  `computeV4_nGates`, `computeV4_nCalls`), `nativeOK4`, `decOK`, `Pub.nativeOK`.
* The angle arithmetic: `odeArith`, `odeAr` (`odeArith_ok`, `odeAr_ok`, `Pub.ar_ok`; counts
  `odeArith_counts`, `Pub.ar_counts`).
* The instance conditions: the clock promises `clock4`, `Pub.selectHyp`, `Pub.instanceOK`.

**Binary data.** As in `GateEfficientBinary`: `D : NativeSparseBlockEncoding.Data X n
(Cfg (VW b)) s` is the released native sparse data whose stored entries `D.table x (i, j)` are
two `b`-bit two's complement words `X`, `Y`, with the decoder `D.decode e z = c₀ (X + i Y)` for a
public scale `c₀ > 0` (`hdec`, `gauss`); the indices are `k`-bit words (`en : Cfg (Fin k) ≃ n`,
dimension `N = 2^k`), and there are `s = 2^σ` slots, exactly the index words supported on the
lowest `σ ≤ k` bits (`hrange`). The primitive oracles `GateBinary.prims D en x` are the row and
column location oracles and the value oracle of `GateEfficientBinary`. As in the released
query-level solver (`SparseHamiltonian.ODEMainEndpoint.solver`), the input `x` selects one possibly
nonnormal matrix `M = D.matrix x`; its Hamiltonian part `H = (M - M†)/(2i)` and dissipative part
`L = (M + M†)/2` (`ODEMatrixEnergy`) are formed from the two stored entries `M_ij` and `M_ji`. The
ODE is `x' = -M̂ x + b` (`gen_lift`, `target_lift`), where `M̂ = mLift D en x` is `M` on the `k`
system qubits; `hLift`, `lLift` are the lifts of `H` and `L`. The input hypotheses are those of
the released solver: the row and column energies `∑ⱼ |H_ij|²`, `∑ᵢ |H_ij|²` are at most `η_H²`,
those of `L` at most `η_D²`, and `L` is accretive (`re ⟪w, L w⟫ ≥ 0`).

**The public data** (`Pub`): the system qubits `k` (`kx`), the slot bits `σ ≤ k`, the stored
bits `b`, the decoder scale `c₀`, the energy bounds `η_H`, `η_D`, the Cayley rescaling `γ`, the
time `T`, the amplification bound `g`, the accuracy `ε`, the norms `r₀`, `rb` of the initial state
and of the forcing, and the arithmetic accuracy `ζ`. `Pub.OK`: `b ≥ 1`, `c₀ > 0`, `η_H, η_D ≥ 0`,
`η_H + η_D > 0`, `0 < γ ≤ 1`, `T > 0`, `g ≥ 1`, `0 < ε ≤ 1/2`, `r₀, rb ≥ 0`, `r₀ + T rb > 0` and
`0 < ζ ≤ 1`. The released parameters `Pub.params` have `a = k + 3` ancillas,
`Q = width(4s, γ) = ⌈max(1, γ √(4s))⌉`, `q̄ = moment γ = (1 + γ²)/2`, `λ_H = √(4s) η_H / γ`,
`λ_D = √(4s) η_D / γ` and `T`, `g`, `ε`, `r₀`, `rb`; they satisfy the released public conditions
(`Pub.params_ok`). With `ρ = η_H + R η_D` (`Pub.rho`, `R` the LCHS radius), the common simulation
time of the released solver is `τ = T (λ_H + R λ_D) = T √(4s) ρ / γ` (`Pub.tau_eq`); the filter
degree `d`, the precision `ν = ε/(10000 g)`, the LCHS grid size `J` and the label words are the
released public sizes of `Pub.params`.

**The four-sector private operation** (`Operator`, `Swap`, `Qubit`). The released tagged
construction (`ODETaggedMoments`, `ODEFixedTaggedMoments`) represents a Hermitian branch `K` of
`M` on two tagged copies of its support, with a boundary of weight `2s`. For the LCHS branch
`K = H + k_w L` at the node `k_w` the library places `H` and `k_w L` in two sectors, the part bit
(`partK`): the generator `gen4 = √2 (K₀(H) ⊕ K₀(k_w L))` and the boundary `bdry4 = (J ⊕ J)/√2`
satisfy `‖gen4‖ ≤ √(4s)` and `‖gen4 bdry4‖ ≤ 1` when the energies of the two sectors are at most
`ρ_H²`, `ρ_D²` with `ρ_H² + ρ_D² ≤ ρ²` (`gen4_norm`, `gen4_bdry4_norm`), and
`bdry4† gen4 bdry4 = (ρ √(4s))⁻¹ (H + k_w L)` (`compression4`). The Cayley action `act4` and the
resolvent at one `res4` satisfy the clock promises (`one_sub_act4_res4`, `res4_one_sub_act4`,
`norm_res4_le`, `res4_compression`, `norm_res4_bdry4`). `act4_eq_loc4`: the private operation is
`loc4† actS4 loc4`, where the locator applies the row locator when the orientation and the tag
agree and the column locator otherwise, without an exchange of the indices (`swap_locator`), and
`actS4` is the edgewise Cayley action. The qubits `PR4 k = Fin (k + 3) ⊕ Fin k` carry the
orientation, the tag, the part, the second index and (system wires) the first index (`phi4`); the
qubit lift `qlift4` is a unital star algebra homomorphism and a contraction, and `elift4` puts the
system qubits into the payload.

**The compute circuit and the native identity** (`Wires`, `Native`, `Decoder`). The native private
operation `odeOp k L κ ρ_L` acts on the label wires of the solver (source sector, node word and
LCHS word), the private register and the scratch `SZ4 k b` (`6 k + 4 b` qubits, `card_SZ4`: a
dummy edge register, row and column reference registers and two value registers). Its compute
circuit `computeV4` writes the reference images of the all-zero edge (one row and one column call),
XORs the orientation into the tag wire, applies the row location oracle to the index wires when
the tag wire is `0` and the column location oracle when it is `1` (the controlled-call gadgets of
`GateEfficientBinary`), XORs the orientation back, and XORs the stored entries of the located edge
`(i, j)` and of the transposed edge `(j, i)` into the two value registers: `28 k + 2` elementary
gates and two calls of each oracle. `nativeOK4`: if the decoder takes, after the compute circuit on
clean scratch, the value of the label-selected edgewise gate (`DecOK`), the native identity
`NativeOK (prims D en x) nd (selOp (labFam D̂ false))` holds for the label-selected private
operation `D̂ z = elift4 en (act4 D x (k_w z) ρ (γ_z))`, `k_w z` and `γ_z` the LCHS node and the
Cayley parameter of the label `z`. `decOK`: every value of the edgewise gate of a sector is a real
multiple of a Gaussian integer formed from the two stored entries (`core_identity`), so the
decoder `decO` with the scale `κ = γ √(4s) c₀ / (2^(k_T + F + 10) ρ)` (`kapOf`) and the step
factor `ρ_L = 2^F h / Hn` (`rhoL`) satisfies `DecOK` for the LCHS node `nodeW` and the rescaling
`γ dur / T` of every label (`nodeW_eq`, `dur_div`); here `h` is the step of the public LCHS grid,
`k_T` the node bits and `Hn = round(2^F h)`.

**The angle arithmetic** (`Program`, `ProgramSem`, `ProgramVal`, `Arith`). The decoded value is
`κ ρ_x Z'` with `Z' = 256 c_t d μ (A_x + i A_y)` (`decO`): `c_t ∈ {0, 1, 2}` the tag split of the
two stored entries, `d` the duration word, `μ = n_w Hn` on the dissipative and `2^F` on the
Hamiltonian part, `A` the combination of the two stored entries of the sector, and `ρ_x = ρ_L` on
the dissipative part and `1` otherwise. A single-assignment register program computes the two's
complement words of `zx`, `zy` (`v_xc`, `v_yc`); `odeArith` runs it, the CORDIC circuit of
`GateEfficientBinary` on its output and the program backwards. `odeArith_ok`: under the layout
bounds `Lay.OK` (`b ≥ 1`, `J ≤ 2^l`, `K < J`, `Hn < 2^(F+1)`), `κ > 0` and `|ρ - 1| ≤ 1/2`, the
arithmetic hypothesis `ArithOK` holds at every accuracy `ζ ≥ ζc + 2 |ρ - 1|`, `0 < ζc ≤ 1` the
CORDIC accuracy; `odeArith_counts`, `Pub.ar_counts`: the gates and work wires.

**The boundary and the clock promises** (`Boundary`, `Clock`). `hadUJ4` are `σ + 3` Hadamard
gates, on the orientation, the tag, the part and the lowest `σ` wires of the second index;
`boundary_lift4`: `(U_J ι₀)† Â (U_J ι₀) = qlift en (bdry4† A bdry4)` for every four-sector
operator `A` and its lift `Â`. The LCHS step satisfies `0 < h ≤ 1` (`hStep_le_one`); with
`F = fOf p ζ` fractional bits, `2^F h ≥ 4/ζ`, so `Hn ≥ 2/ζ`, `Hn < 2^(F+1)` and
`|ρ_L - 1| ≤ ζ/4` (`rhoL_close`), and the layout is admissible (`layOf_ok`); with the CORDIC
accuracy `ζ/2` the arithmetic satisfies `ArithOK` at accuracy `ζ` (`Pub.ar_ok`). `privFam`: the
label-selected private operation, at the LCHS node of the label and the rescaling
`γ_z = γ dur / T ≤ γ`. `clock4`: for every label the lifted resolvent `R₁ = elift4 (res4 …)`
satisfies `(1 - D_z) R₁ = R₁ (1 - D_z) = 1`, `‖R₁‖ ≤ width(4s, γ)`,
`(U_J ι₀)† R₁ (U_J ι₀) = (1 + i H_z)/2` for the rescaled branch Hamiltonian
`H_z = (dur/τ) (Ĥ + k_w L̂)` of the released solver, and `‖R₁ U_J ι₀‖ ≤ endpoint γ_z` with
`endpoint γ_z ² ≤ moment γ / 2`. `Pub.selectHyp`: `U_J` and `D_z` are unitary, `Ĥ`, `L̂` are
self-adjoint with `‖Ĥ‖ ≤ √(2s) η_H ≤ λ_H` and `‖L̂‖ ≤ λ_D` (`norm_matrixOperator_le`, from the
tagged compression), and the clock promises hold; `Pub.instanceOK` adds the accretivity of `L̂`
(`re_inner_qlift_nonneg`) and the source and target conditions.

**Theorem `ode:thm:gates` for binary data** (`binary_ode_counts`, `binary_ode_solver`).
Hypotheses: `q.OK`; valid source circuits `srcC` on the source control, the `k` system qubits and
source scratch `Zs`, calling the primitive oracles; for `binary_ode_solver` also the binary data
above with `s = q.s = 2^σ` and the decoder scale `c₀`. The native preparation
`q.prep srcC = nprepC q.params (hadUJ4 …) q.nd q.ar srcC` depends only on the public data and the
source circuits. `binary_ode_counts`: its trials are valid; it has at most
`prepGates + 84 d (σ + 3) + 6 d (2 (28 k + 2) + 2 |arith| + 2 bP + bT + 1) + |srcC 0| + |srcC 1|`
elementary gates and at most `24 d` calls of each oracle besides those of the source circuits; in
every history the protocol `nprotocol (q.prep srcC) g` uses at most
`40 g N + 20 g (4 (|W| + |XW| + |Zs| + k) + 3)` gates (`N` the gates of the preparation) and at
most `40 g` times the calls of the preparation; its register has
`k + 2 (|W| + (6 k + 4 b + bT + bP + A + 3) + |Zs|) + k + 1` qubits. `binary_ode_solver` restates
these counts and adds the guarantees: for every input `x` with the energy bounds and an accretive
dissipative part, every family of unitary source interfaces `J_src` that the source circuits
approximate within `ζs` in the full-output convention, with `24 d ζ + 2 ζs ≤ ν`, every initial
state `x₀` of norm `r₀` and forcing `b` of norm `rb` prepared by `J_src` from the seed, a nonzero
solution `x(T)` of `x' = -M̂ x + b`, `x(0) = x₀`, and
`r₀ + T rb ≤ g ‖x(T)‖`, the protocol has the guarantees `GateNative.NOutcome`: unitary trials,
mean success at least `1/4`, every successful trial within `ε/500` of `x(T)/‖x(T)‖` up to a
global phase, success probability at least `175/256 ≥ 2/3`, and a conditional output density
within trace distance `ε` of `x(T)/‖x(T)‖`.

`binary_ode_gate_count` (the explicit count underlying equation `ode:eq:gate-main`, for binary
data): the protocol uses at most
`9000 g [(d+1)(k + 3 + m + r + 1 + (σ + 3) + G_C) + (k_T + 1) + (J+2)(l+1) + G_src + A]`
elementary gates in every history, with `G_C = 2 (28 k + 2) + 2 |arith| + 2 bP + bT + 1`,
`G_src = |srcC 0| + |srcC 1|` and `A = k + |Zs| + (6 k + 4 b) + bT + bP + A_arith`; `d`, `m`, `r`,
`l` and `J` are bounded by the released size lemmas (`GateODE.Params.degree_bound`,
`GateODE.Params.sim_sizes`, `GateODE.Params.l_bounds`, `GateODE.Params.J_le_log`). By
`Pub.ar_counts`, `|arith|`, `A_arith`, `bP` and `bT` are polynomial in `b`, `k_T`, `l`, `F`,
`log(1/ζ)` and `|log κ|` (read off from the definitions of the layout and of the CORDIC
parameters, not a separate Lean statement); they do not depend on the system qubits `k`, and the
slot count `s = 2^σ` enters only through `κ`, `F`, `k_T` and `l`.

`binary_ode_solver_synth`: under `GateSynth.Synthesis 𝒢 Xa len` (gate set `𝒢`, synthesis ancillas
`Xa`, synthesis length `len`) the synthesised protocol
`GateSynth.sprotocol hS (ε/200) (q.prep srcC) g` consists of valid gates of `𝒢` and primitive
calls, makes at most `40 g` times the calls of the preparation, uses at most
`(40 g N + 20 g (4 n + 3)) (c₁ log((G + 1)/(ε/200)) + c₀)` gates when
`len ζ ≤ c₁ log(1/ζ) + c₀` (`n = |W| + |XW| + |Zs| + k`, `G = 10 g N + 5 g (4 n + 3)`), has
`|Xa|` more qubits, and for every instance as above succeeds with probability at least `2/3` with
a conditional output within trace distance `ε` of `x(T)/‖x(T)‖` (`GateSynth.SOutcome`).

Every theorem of the library is axiom-audited in `GateEfficientBinaryODE/Audit.lean`.

**Formalisation choices.**

* The binary data format, the slots and the primitive oracles are those of `GateEfficientBinary`
  (powers of two by zero padding, uncontrolled location calls with the controlled-call gadgets).
* The Hamiltonian and the dissipative part of an LCHS branch are placed in two sectors (a part
  qubit), so that every value of the edgewise gate is a positive multiple `κ ρ_x Z'` of one
  Gaussian integer `Z'`, which a register program computes from the stored bits and the label
  words; the boundary then has weight `4s` instead of `2s`, which costs a factor `√2` in `Q`,
  `λ_H` and `λ_D`.
* The LCHS nodes `n_w h` are represented through the rounded step `Hn = round(2^F h)`; the factor
  `ρ_L = 2^F h / Hn ∈ [1 - ζ/4, 1 + ζ/4]` of the dissipative part is absorbed in the arithmetic
  accuracy (CORDIC accuracy `ζ/2`, `ArithOK` at `ζ`).
* The Cayley parameter of a label is `γ dur / T ≤ γ`, so the clock promises hold with the
  label-independent `Q = width(4s, γ)` and `q̄ = moment γ` of the released solver.
* The public data are bundled in `Pub`; the theorem holds for every rescaling `0 < γ ≤ 1` and every
  arithmetic accuracy `0 < ζ ≤ 1` with `24 d ζ + 2 ζs ≤ ν`. The released parameters `q.params`,
  hence `d` and `ν`, do not depend on `ζ`, so the budget can be met by choosing `ζ` last.
* The source circuits, the source interfaces and the source and target conditions of the instance
  remain hypotheses, as in `native_ode_solver`.

**Not formalised.** The time-dependent part of Theorem `ode:thm:gates` from binary data
(`GateNative.native_ode_time_solver` keeps its native hypotheses: it needs time-indexed binary
oracles for the generators of the time steps); the construction of the source circuits from data
formats for `x₀` and `b`; the cases `T = 0` and `η_H + η_D = 0`, which the released public
conditions exclude.
-/
