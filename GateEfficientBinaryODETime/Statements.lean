import GateEfficientBinaryODETime.Solver
import GateEfficientBinaryODETime.Synth

/-!
# The time-dependent dissipative solver from binary data: paper-to-Lean entry point

The native gate-level dissipative ODE solver for time-dependent coefficients of
`GateEfficientNative` (Theorem `ode:thm:gates` of the accompanying paper, time-dependent part,
before finite-gate-set synthesis: `GateNative.native_ode_time_solver`) takes as hypotheses the
gates of the boundary unitary `U_J`, a label- and slot-selected native private operation
(compute circuit on the label and slot wires, orientation wire and decoder) with its native
identity (`GateNative.NativeOK` for the family `GateNative.tlabFam`), the reversible angle
arithmetic (`GateNative.ArithOK`), the loading and weight-preparation circuits, and the instance
conditions of the released time-dependent solver (`GateODE.Time.TParams.InstanceOK`), among them
the clock promises at every label and every time slot. For dissipative ODEs
`x' = -G(t) x + b(t)` whose generator is sampled on the uniform mesh of the solver by time-indexed
binary sparse oracles, this library constructs the gates of `U_J`, the label- and slot-selected
native private operation with its native identity and the arithmetic, and proves the selection
conditions of the instance: unitarity, self-adjointness, the clock promises at every label and
slot and, from energy bounds and the accretivity of every sample, the norm and accretivity
conditions. The loading and weight-preparation circuits (with their accuracy `ζs` and the budget
`24 d ζ + 3 ζs ≤ ν`) and the source, path and target conditions of the instance (`PubT.Rest`)
remain hypotheses. It instantiates `GateNative.native_ode_time_solver`
(`binary_ode_time_solver`, with the
counts `binary_ode_time_counts` and the explicit worst-case gate count
`binary_ode_time_gate_count`) and its finite-gate-set form `GateSynth.native_ode_time_solver_synth`
(`binary_ode_time_solver_synth`, a partial formalisation, under this package's format hypotheses,
of the finite-set statement of Theorem `ode:thm:gates`). The released libraries are unchanged; this
library imports and reuses `GateEfficientBinaryODE` (constant coefficients),
`GateEfficientBinaryTime` (time-indexed binary oracles) and `GateEfficientBinary`. No result from
another paper is used, except single-qubit synthesis and the decomposition of controlled gates as
the hypothesis `GateSynth.Synthesis` of the finite-gate-set form. All declarations below are in the
namespace `SparseHamiltonian.GateBinaryODETime`.
References to the manuscript use its labels.

* Theorem `ode:thm:gates`, time-dependent part, for time-indexed binary data:
  `binary_ode_time_solver`, `binary_ode_time_counts`, `binary_ode_time_gate_count`; over a finite
  gate set (a partial formalisation, under this package's format hypotheses, of the finite-set
  statement of the theorem): `binary_ode_time_solver_synth`. The public data `PubT`, its
  conditions `PubT.OK`, the released parameters `PubT.params` (`PubT.params_ok`), the native
  preparation `PubT.prep`, the remaining instance conditions `PubT.Rest`.
* `U_J`: the Hadamard gates `GateBinaryODE.hadUJ4` of the constant-coefficient library
  (`PubT.UJg`).
* The native private operation and its native identity: `odeOpT` (`odeOpT_public`,
  `odeOpT_nGates`, `odeOpT_nCalls`), `privFamT`, `decOK_T`, `nativeOK_T`, `PubT.nativeOK`; the
  generic slot transfer `nativeOK_slot2`.
* The angle arithmetic: the slot comparator `cmpOps` (`msb_cde`), `arithT`, `decT`
  (`arithT_ok`, `arithT_counts`), `odeArT` (`odeArT_ok`), `PubT.ar_ok`, `PubT.ar_counts`.
* The instance conditions: the clock promises `clock_at`, `clockT`; `PubT.selectHyp`,
  `PubT.instanceOK`.

**Time-indexed binary data.** As in `GateEfficientBinaryTime`:
`D : NativeSparseBlockEncoding.Data (X × Fin (2^m)) n (Cfg (VW b)) s` are released native sparse
data whose input carries the time slot; on input `x`, the sample of slot `r < 2^m` is the
possibly nonnormal matrix `M_r = D.matrix (x, r)`, with its own stored words and locators. Its
stored entries are two `b`-bit two's complement words with the decoder `c₀ (X + i Y)`, `c₀ > 0`
(`hdec`); the indices are `k`-bit words (`en : Cfg (Fin k) ≃ n`), and there are `s = 2^σ` slots,
exactly the index words supported on the lowest `σ ≤ k` bits (`hrange`). The primitive oracles
are the coherent sampled-time oracles `GateBinary.primsT D en x` of `GateEfficientBinaryTime`:
on the `m` slot qubits they select the binary row-location, column-location and value oracles of
the sample. The `2^m` samples are the samples of the uniform mesh of the released time-dependent
solver (`GateODE.Time.TParams`, `2^m` slots of length `T/2^m`). The Hamiltonian part
`H(M_r) = (M_r - M_r†)/(2i)` and the dissipative part `L(M_r) = (M_r + M_r†)/2`
(`ODEMatrixEnergy`) of a sample are lifted to the `k` system qubits: `HsT D en x r`,
`LsT D en x r` (`GateBinaryODE.hLift`, `lLift` of the sample; zero for `r ≥ 2^m`), and the
represented slot generator of the released solver is the lifted sample:
`GateODE.Time.gens (HsT D en x) (LsT D en x) r = M̂_r = mLift D en (x, r)` (`gensT_eq`). The
input hypotheses are, for every slot `r`: the row and column energies of `H(M_r)` are at most
`η_H²`, those of `L(M_r)` at most `η_D²`, and `L(M_r)` is accretive (`re ⟪w, L w⟫ ≥ 0`). The
accretivity of every sample is the hypothesis of the formal versions of Theorem
`ode:thm:time`, which that theorem of the manuscript does not make (the formal restriction
stated in `TimeDependentODE/Statements.lean`).

**The public data** (`PubT`): the system qubits `k` (`kx`), the slot bits `σ ≤ k`, the stored
bits `b`, the decoder scale `c₀`, the energy bounds `η_H`, `η_D`, the Cayley rescaling `γ`, the
time `T`, the amplification bound `g`, the accuracy `ε`, the time-slot bits `m` (`2^m` time slots)
and the arithmetic accuracy `ζ`. `PubT.OK`: `b ≥ 1`, `c₀ > 0`, `η_H, η_D ≥ 0`, `η_H + η_D > 0`,
`0 < γ ≤ 1`, `T > 0`, `g ≥ 1`, `0 < ε ≤ 1/2`, `0 < ζ ≤ 1`, and the mesh condition of the released
solver `TimeSchedule.steps τ (ν/3) ≤ 2^m`. The released parameters `PubT.params` have
`a = k + 3` ancillas, `Q = width(4s, γ) = ⌈max(1, γ √(4s))⌉`, `q̄ = moment γ = (1 + γ²)/2`,
`λ_H = √(4s) η_H / γ`, `λ_D = √(4s) η_D / γ`, `T`, `g`, `ε` and `m`; they satisfy the released
public conditions (`PubT.params_ok`). The released solver works with the ratio `2g` and the
accuracy `ε/2`: the precision is `ν = ε/(40000 g)`, the LCHS radius `R = radius(2g, ε/2)`, and,
with `ρ = η_H + R η_D` (`PubT.rho`), the common simulation time is
`τ = T (λ_H + R λ_D) = T √(4s) ρ / γ` (`PubT.tau_eq`); the filter degree `d`, the LCHS grid size
`J`, the LCHS word length `l` and the simulator sizes are the released public sizes of
`PubT.params`.

**The released time-dependent selection.** The source label `(ini, u)` (`ini` the forcing bit,
`u` an `m`-bit node word) starts at the slot `start = (ini ? u : 0)`; at the slot `r` the branch
of the joint label `z = ((ini, u), w)` evolves under the normalised Hamiltonian
`branchH z r = (T [start ≤ r] / τ)(H_r + k_w L_r)` (`TimeDependentODE.mask`), `k_w` the LCHS node
of the word `w` (`GateODE.Time.TParams.nodeW`). Its private operation at the slot `r` must
satisfy the clock promises (`GateODE.ClockPromise`) for `U_J` and `branchH z r`.

**The private operation** (`privFamT`). At the label `z` and the slot `r < 2^m` it is the lifted
four-sector Cayley action `GateBinaryODE.elift4 en (act4 D (x, r) k_w ρ γ_{z,r})` of the sample of
the slot (the two-sector representation of `H_r` and `k_w L_r` of the constant-coefficient
library, `GateBinaryODE.act4`), at the LCHS node `k_w` and the Cayley parameter
`γ_{z,r} = γ [start ≤ r] ≤ γ`; it is the identity for `r ≥ 2^m`, which the `m` slot wires never
select.
`clock_at` proves, at one data input, node `|k_w| ≤ R` and Cayley parameter `0 ≤ γ' ≤ γ`, the
clock promises with the lifted resolvent at one: `(1 - D) R₁ = R₁ (1 - D) = 1`,
`‖R₁‖ ≤ width(4s, γ)`, `(U_J ι₀)† R₁ (U_J ι₀) = (1 + i H)/2` for
`H = (γ' / (ρ √(4s))) (Ĥ + k_w L̂)`, and `‖R₁ U_J ι₀‖ ≤ endpoint γ'` with
`endpoint γ' ² ≤ moment γ / 2`; `clockT`: with `γ' = γ [start ≤ r]` and `τ = T √(4s) ρ / γ`
this is the clock promise of the released solver for `privFamT z r` and `branchH z r`, at every
label and slot.

**The native private operation** (`odeOpT`, `PubT.nd`). Its selection wires are the label wires
and the `m` slot wires (`GateNative.TSel`), its private register and scratch are those of the
constant-coefficient operation (`GateBinaryODE.PR4`, `SZ4`). The compute circuit is
`GateBinaryODE.computeV4` (`28 k + 2` elementary gates, two calls of each oracle) with every
primitive call also reading the slot wires (`slotInstr2`); the decoder is `decT` on the wiring
`inpT4`. `nativeOK_T` (`PubT.nativeOK`): `NativeOK (primsT D en x) nd (selOp (tlabFam privFamT))`.
Proof: at every slot word `w` the operation read at `w` (`atSlot2`) has the compute circuit
`computeV4` and a decoder satisfying the decoder hypothesis `GateBinaryODE.DecOK` of the sample
`w` with the LCHS node of each label and the Cayley parameter `γ [start ≤ w]` (`decOK_T`, from
the released `GateBinaryODE.core_identity`), so the released `GateBinaryODE.nativeOK4` gives the
native identity at `w`; `nativeOK_slot2` assembles the slot words. `nativeOK_slot2` generalises
`GateBinary.nativeOK_slot` of `GateEfficientBinaryTime` from operations without selection wires
to operations with label selection wires `Sel0`, extended by slot selection wires `Sel1`, with a
decoder that may read the slot wires: if the native identity holds at every slot word `w` for
the label-selected family `Dat w`, it holds for the selection-controlled primitives
`GateBinary.slotPrim primAt` and the label- and slot-selected family (`nrun_slot2`, `Rdec_slot2`).

**The angle arithmetic** (`Compare`, `Arith`, `Grid`). The decoded value of the private operation
at the label `((ini, u), w)` and the slot `r` is `κ ρ_x Z'` with `Z' = 256 c_t [start ≤ r] μ A`:
the constant-coefficient value (`GateBinaryODE.decO`) with the duration factor replaced by the
slot mask. The slot comparator `cmpOps` is a two-operation register program on the registers
`GateBinaryODE.RO (cLay m)` of the released program (width `m + 14`): `du := r - u`,
`de := du ± du` (`+` iff `ini`), so that the sign bit of `de` is `ini ∧ r < u` (`msb_cde`). The
released program `prog` computes the duration factor `dv = (ini ? U : 2^kq)`; on the wiring
`InpT.lift` its source bit is the comparator bit and its node word the zero wire, so
`dv = 2^kq [start ≤ r]` (`dv_lift`), with
`kq = 0` in the layout `layT`. `arithT` (`circT`) runs the comparator, the released arithmetic
circuit `GateBinaryODE.circO` (program, CORDIC of `GateEfficientBinary`, program backwards) on the
base wires and the comparator registers, and the comparator backwards; `circT_run`: on clean work
wires it writes the CORDIC angle words of the decoded value and restores every work wire.
`arithT_ok`: under the layout bounds, `κ > 0` and `|ρ - 1| ≤ 1/2`, the arithmetic hypothesis
`ArithOK` holds for the decoder `decT` at every accuracy `ζ ≥ ζc + 2 |ρ - 1|`, `0 < ζc ≤ 1` the
CORDIC accuracy (from the released `GateBinaryODE.odeArith_ok` at the lifted input).
`arithT_counts`: besides the gates and work wires of the released arithmetic, the comparator uses
at most `52 (m + 14)` gates and `1 + 64 (m + 14)` work wires. The grid of the released
time-dependent solver is that of the constant-coefficient parameters `gridP p` with ratio `2g` and
accuracy `ε/2` (`gridP_J`, `gridP_l`, `gridP_nodeW` by definition), so the rounded LCHS step of
`GateBinaryODE` applies: with `F = fOf (gridP p) ζ` fractional bits, the step factor
`ρ_L = 2^F h / Hn` is within `ζ/4` of one (`rhoLT_close`), the layout `layT` is admissible
(`layT_ok`), and with the decoder scale `κ = γ √(4s) c₀ / (2^(F+10) ρ)` (`kapT`) and the CORDIC
accuracy `ζ/2` the arithmetic satisfies `ArithOK` at accuracy `ζ` (`PubT.ar_ok`).

**The instance conditions** (`Pub`). `PubT.selectHyp`: `U_J` and every `privFamT z r` are
unitary, every `HsT r`, `LsT r` (`r < 2^m`) is self-adjoint with `‖HsT r‖ ≤ √(2s) η_H ≤ λ_H` and
`‖LsT r‖ ≤ λ_D` (`GateBinaryODE.norm_matrixOperator_le`), and the clock promises hold at every
label and slot (`clockT`). `PubT.instanceOK`: with the accretivity of every `LsT r`
(`GateBinaryODE.re_inner_qlift_nonneg`) and the remaining conditions `PubT.Rest`, the released
instance conditions hold for `(U_J, privFamT, Jl, Wp)`, `HsT`, `LsT`. `PubT.Rest` contains,
verbatim from `GateODE.Time.TParams.InstanceOK`: the loading `Jl` is unitary and prepares the
normalised initial state (label `(false, 0)`) and the normalised forcing samples `b_r` (labels
`(true, r)`) from the seed; the weight preparation `Wp` is unitary with the amplitudes
`√(‖z_s‖ / B)` (`TParams.srcAmp`) in its zero column; `x` solves `x' = -G(u) x + b(u)` on `[0, T]`
(`TimeDependentODE.SolvesODE`) for an accretive `βG`-Lipschitz path `G` with
`‖G(r T/2^m) - M̂_r‖ ≤ δG` (stated against the lifted samples, `gensT_eq`) and a `βb`-Lipschitz
forcing `b` with `‖b‖ ≤ bmax` and `‖b(r T/2^m) - b_r‖ ≤ δb`, `βG, βb ≥ 0`; `x(T) ≠ 0`; the source
mass `B = TParams.mass (x 0) b_·` satisfies `B ≤ g ‖x(T)‖`; and the discretisation budget
`TParams.discretisation βG δG βb δb bmax ‖x(0)‖ ≤ ε B / (2000 g)`.

**Theorem `ode:thm:gates`, time-dependent part, for binary data** (`binary_ode_time_counts`,
`binary_ode_time_solver`). Hypotheses: `q.OK`; a valid loading circuit `loadC` on the `m + 1`
source-label wires, the `k` system qubits and source scratch `Zs`, and a valid weight-preparation
circuit `wpC` on the source-label wires and `Zs`, calling the primitive oracles; for
`binary_ode_time_solver` also the time-indexed binary data above with `s = 2^σ` and the decoder
scale `c₀`. The native preparation `q.prep loadC wpC = tnprepC q.params (hadUJ4 …) q.nd q.ar
loadC wpC` depends only on the public data and the two circuits. `binary_ode_time_counts`: its
trials are valid; it has at most
`prepGates + 84 d (σ + 3) + 6 d (2 (28 k + 2) + 2 |arith| + 2 bP + bT + 1) + |loadC| + 2 |wpC|`
elementary gates and at most `24 d` calls of each coherent sampled-time oracle besides those of
the two circuits (`calls(loadC) + 2 calls(wpC)`); in every history the protocol
`nprotocol (q.prep loadC wpC) (2g)` uses at most `80 g N + 40 g (4 (|W| + |XW| + |Zs| + k) + 3)`
gates (`N` the gates of the preparation) and at most `80 g` times the calls of the preparation;
its register has `k + 2 (|W| + (6 k + 4 b + bT + bP + A + 3) + |Zs|) + k + 1` qubits.
`binary_ode_time_solver` restates these counts and adds the guarantees: for every input `x`
whose samples have the energy bounds and accretive dissipative parts, every loading `Jl` and
weight preparation `Wp` that the two circuits approximate within `ζs` in the full-output
convention (`ApproxOn CleanX … (liftB (loadIdeal Jl)) ζs`, `… (liftB (matOp Wp)) ζs`), with
`24 d ζ + 3 ζs ≤ ν`, and every path, forcing, solution and forcing samples satisfying
`PubT.Rest`, the protocol has the guarantees `GateNative.NOutcome`: unitary trials, mean success
at least `1/4`, every successful trial within `ε/500` of `x(T)/‖x(T)‖` up to a global phase,
success probability at least `175/256 ≥ 2/3`, and a conditional output density within trace
distance `ε` of `x(T)/‖x(T)‖`.

`binary_ode_time_gate_count` (the explicit count underlying equation `ode:eq:gate-main`, for
time-indexed binary data): the protocol uses at most
`18000 g [(d+1)(k + 3 + m + r + 1 + (σ + 3) + G_C) + (J+2)(l+1) + G_src + A]` elementary gates
in every history, with `G_C = 2 (28 k + 2) + 2 |arith| + 2 bP + bT + 1`,
`G_src = |loadC| + 2 |wpC|` and `A = k + |Zs| + (6 k + 4 b) + bT + bP + A_arith`; `d`, `r`, `l`
and `J` are the released public sizes, bounded by the released size lemmas
(`GateODE.Time.TParams.degree_bound`, `GateODE.Time.TParams.r_bounds`,
`GateODE.Time.TParams.l_bounds`, `GateODE.Time.TParams.J_le_log`), and `m` is the number of
time-slot bits; the mesh condition of `PubT.OK` holds for every `m ≥ simM τ ν`
(`GateODE.Time.TParams.mesh_of_le`), since `τ` and `ν` do not depend on `m`. By `PubT.ar_counts`,
`|arith|`, `A_arith`, `bP` and `bT` are those of the constant-coefficient arithmetic for the
layout `layT`
(polynomial in `b`, `l`, `F`, `log(1/ζ)` and `|log κ|`, read off from the definitions of the
layout and of the CORDIC parameters, not a separate Lean statement) plus at most `52 (m + 14)`
gates and `1 + 64 (m + 14)` work wires of the comparator; they do not depend on the system qubits
`k`, and the slot count `s = 2^σ` enters only through `κ`, `F` and `l`.

`binary_ode_time_solver_synth`: under `GateSynth.Synthesis 𝒢 Xa len` the synthesised protocol
`GateSynth.sprotocol hS (ε/200) (q.prep loadC wpC) (2g)` consists of valid gates of `𝒢` and
primitive calls, makes at most `80 g` times the calls of the preparation, uses at most
`(80 g N + 40 g (4 n + 3)) (c₁ log((G + 1)/(ε/200)) + c₀)` gates when
`len ζ ≤ c₁ log(1/ζ) + c₀` (`n = |W| + |XW| + |Zs| + k`, `G = 20 g N + 10 g (4 n + 3)`), has
`|Xa|` more qubits, and for every instance as above succeeds with probability at least `2/3`
with a conditional output within trace distance `ε` of `x(T)/‖x(T)‖` (`GateSynth.SOutcome`).

Every theorem of the library is axiom-audited in `GateEfficientBinaryODETime/Audit.lean`.

**Proof map.** Module paths are relative to `GateEfficientBinaryODETime/`.

* `Slot`: the slot transfer with label selection wires (`slotInstr2`, `slotOp2`, `atSlot2`,
  `nrun_slot2`, `Rdec_slot2`, `nativeOK_slot2`, counts and public conditions).
* `Compare`: the comparator program (`cmpOps`, `cmpOK`, `v_cdu`, `v_cde`, `msb_cde`).
* `Arith`: the lifted wiring (`InpT`, `InpT.lift`, `dv_lift`), the circuit (`circT`,
  `circT_run`), the arithmetic and its hypothesis (`arithT`, `decT`, `arithT_ok`,
  `arithT_counts`).
* `Grid`: the grid parameters `gridP`, the layout `layT`, the decoder scale `kapT`, the grid
  conditions (`layT_ok`, `rhoLT_close`, `hRoundT_ne`, `nodeWT_eq`).
* `Native`: the native operation (`inpT4`, `odeOpT`, `odeArT`), the decoder hypothesis at every
  slot (`decOK_T`), the private family (`privFamT`) and the native identity (`nativeOK_T`).
* `Clock`: `clock_at`, `HsT`, `LsT`, `gensT_eq`, `clockT`.
* `Pub`: `PubT`, `PubT.params`, `PubT.params_ok`, the native data, `PubT.ar_ok`,
  `PubT.ar_counts`, `PubT.nativeOK`, `PubT.selectHyp`, `PubT.Rest`, `PubT.instanceOK`.
* `Solver`: `binary_ode_time_counts`, `binary_ode_time_solver`, `binary_ode_time_gate_count`.
* `Synth`: `binary_ode_time_solver_synth`.

**Formalisation choices.**

* The binary data format, the slots, the coherent sampled-time oracles and the controlled-call
  gadgets are those of `GateEfficientBinary` and `GateEfficientBinaryTime`; the `2^m` samples are
  indexed by the slots of the released uniform mesh, so the slot wires of the simulator address
  the samples directly.
* As in `GateEfficientBinaryODE`, the Hamiltonian and the dissipative part of each LCHS branch are
  placed in two sectors (the boundary has weight `4s`, a factor `√2` in `Q`, `λ_H` and `λ_D`), the
  LCHS nodes are represented through the rounded step `Hn = round(2^F h)` (factor `ρ_L` absorbed
  in the arithmetic accuracy), and `U_J` consists of `σ + 3` Hadamard gates.
* The masking of the source branches on the common mesh of the released solver (the deviation
  from the branch-dependent meshes of Lemma `ode:lem:gate-select` noted in the manuscript) enters
  as the slot mask `[start ≤ r]` of the Cayley parameter: a masked label has the Cayley
  parameter `0` and the branch Hamiltonian `0` at that slot. The mask is
  computed by the slot comparator inside the angle arithmetic, and the released register
  program of the constant-coefficient library is reused unchanged on a lifted wiring (comparator
  bit as source bit, zero wire as node word, no node bits); the compute circuit is that of the
  constant-coefficient library, so its native identity applies at every slot.
* The Cayley parameter of a label at a slot is at most `γ`, so the clock promises hold with the
  label- and slot-independent `Q = width(4s, γ)` and `q̄ = moment γ` of the released solver.
* The comparator uses the register set of the released program (`RO (cLay m)`, 62 registers of
  width `m + 14`); it costs `O(m)` gates and work wires.
* The grid lemmas of `GateEfficientBinaryODE`, stated for the constant-coefficient parameters, are
  applied to `gridP p`, whose grid is that of the time-dependent solver (only `T`, `λ_D`, the
  ratio `2g` and the accuracy `ε/2` enter it).
* The instance conditions that do not concern the selection are bundled in `PubT.Rest`; the
  sample bound of the generator path is stated against the lifted samples `M̂_r`. The released
  parameters `q.params`, hence `d` and `ν`, do not depend on `ζ`, so the budget can be met by
  choosing `ζ` last.
* The theorem holds for every rescaling `0 < γ ≤ 1` (no optimisation of `γ` is needed for the
  statement). As in the released time-dependent solver, the forcing enters through the
  left-endpoint quadrature on the same `2^m`-slot mesh.

**Not formalised.** The construction of the loading and weight-preparation circuits from data
formats for `x(0)` and the forcing samples (they are hypotheses with their gate counts); the
regularity and sample certificates of the generator path (`PubT.Rest`; they concern the continuous
problem, not the binary data); nonuniform meshes and the branch-dependent meshes of Lemma
`ode:lem:gate-select`; the asymptotic form of `ode:eq:gate-main` in `q` and `𝔟` (the counts are
explicit in the released sizes); the per-trial error bound of `ode:thm:gates` after synthesis
(as in `GateEfficientSynthesis`, only the success probability and the conditional output are
proved); the cases `T = 0` and `η_H + η_D = 0`, which the released public conditions exclude.

**Provenance.** This library is new, written against the released package: it imports
`GateEfficientBinaryODE`, `GateEfficientBinaryTime`, `GateEfficientNative` and
`GateEfficientSynthesis` and changes none of them. The statement guides of `GateEfficientBinary`,
`GateEfficientBinaryTime` and `GateEfficientSynthesis` predate this library and list
`ode:thm:gates` from binary data as not formalised; that of `GateEfficientBinaryODE` predates it
and lists the time-dependent part of `ode:thm:gates` from binary data as not formalised.
-/
