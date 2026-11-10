import DysonFullClass.Perturb
import DysonFullClass.Clip
import DysonFullClass.Select
import DysonFullClass.Atten
import DysonFullClass.Target
import DysonFullClass.Herald
import DysonFullClass.Theorem
import DysonFullClass.Single
import DysonFullClass.Approx
import DysonFullClass.Corollaries
import DysonFullClass.Coverage
import DysonFullClass.Examples

/-!
# Lemma `odel:lem:dyson` on the full time-dependent input class: statement guide

Manuscript: Lemma 7.7 (`odel:lem:dyson`), eqs. `odel:eq:dyson` and `odel:eq:fixed`, on the
input class of Theorem 6.3 (`ode:thm:time`). The
older single-program theorem `DysonGeneralAccess.Dyson.single_dyson` (and `single_fixed`,
`single_no_uniform`) covers a narrower class: accretive true **and** represented generators, one
forcing sample per cell at its left endpoint with positive quadrature, public source norms and the
rate `s Λ T`. Those results are unchanged. This library proves the comparison on the class of
`ode:thm:time`, under this package's hypotheses of label-controlled loading and a classical
propagator on each closed mesh cell; certificates on the branches `K_{±k} = H ± kD` of two opposite
frequencies are covered through the coverage theorems of
`ManuscriptConformance.BranchCertificates` (table below); the theorems of this library take the
certificate on the represented `C`.

## Public data and unknown input

**Public** (fixed before the input `x : X`; the circuit, seed, herald and readout depend only on
these): the time-indexed native access `D₀ : Data (X × Fin Kₛ) n Z s` (row and column locators,
value oracle, decoder and slot count, their actual inverses and supported controls); a mesh `t`
of `[0, T]` with `M` cells (`IsMesh`) and the cell-to-sample map `σ`; the entry bound `η > 0`;
`T > 0`; `ḡ ≥ 1`; the absolute quadrature-mass constant `c_q ≥ 1`; `0 < ε ≤ 1`; the source rule
(nodes `v_i ∈ [0, T]`, independent of the mesh, and complex weights `ω_i`); the supplied
interfaces `P_w`, `U_load` (functions of the unknown input, used only as calls) and a unit seed.
The public parameters are `z = s η T` (`zParam`), `K = truncDegree z (c_q ḡ) ε` (`fullDegree`)
and `g' = c_q ḡ e^z` (`fullAmp`). Mesh, source rule and sizes may change with `ε`.

**Unknown** (vary with `x`): the true generator pieces `G_r = -A` on cell `r`, the forcing pieces
`b_r`, the solution, its propagator, the forcing samples `b(v_i)`, the source norms
`r_0 = ‖x₀‖`, `r_i = ‖b(v_i)‖`, `B_q = r_0 + ∑ |ω_i| r_i`, `B`, the source certificate `ζ`, and,
for approximate preparations, the exact preparations `P`, `L` and their distance `δ`.

## The validity relation (`Theorem.FullValidAt`, `Theorem.FullValid`)

`FullValidAt D₀ σ t T η ḡ c_q ε hη v ω P L seed x y`: there are true pieces, forcing, solution,
forcing samples, propagator and `ζ` with accretive pieces (the true path only; **no positivity of
the represented samples**), interval-integrable pieces with the mesh propagator classical on every
closed cell, the mild-solution identity, the weight preparation `P` of the actual source vectors
`x₀`, `ω_i b(v_i)`, label-controlled loading `L` of their directions, `B_q ≤ c_q B`, the
propagated source certificate `‖quadrature - ∑ ω_i U(T, v_i) b(v_i)‖ ≤ ζ B` against the original
propagator, `x(T) ≠ 0`, `B ≤ ḡ ‖x(T)‖`, the Dyson budget `ζ + c_q (e^{E} - 1) ≤ ε/(2000 ḡ)` with
`E = ∑_r ∫_{cell r} ‖G_r(u) - C_r‖`, `C_r = p_η(D₀.matrix (x, σ r))` (the radially clipped
represented sample), and `y = x(T)`. No `B ≤ B_q`, no lower bound on component norms, no public
source norms, no on-mesh nodes. `FullValid … P_w J … x y = FullValidAt … (P_w x) (J x) … x y`.

## Source/claim table

| label | Lean declaration (file) | inputs | output metric | resources |
|---|---|---|---|---|
| `odel:lem:dyson` | `full_single` (`Single.lean`) | public spec as above, unitary `P_w(x)`, `U_load(x)` | one heralded program (`Model.HeraldedSolver`): success `≥ 2/3`, `Readout.HeraldedAccurate` (conditional trace distance `≤ ε` after discarding work) on every `FullValid` instance | `≤ dysonBound z (c_q ḡ) ε` matrix queries (row, column, value calls and inverses, whole program); `≤ 40 g'` calls of each source interface |
| `odel:lem:dyson` | `full_dyson_shape`, `full_dyson` (`Theorem.lean`) | same | one public trial family with the released complete certificate `ODECompleteTrial.Certificate` (four fresh trials) | `2160 g' K` matrix queries (`54 K` per preparation, `18 K` in the SELECT), `40 g'` per source interface |
| `odel:lem:dyson` | `full_actual` (`Single.lean`) | same | `GeneralSourceODE.Oracles.ActualCertificate` over the separate primitives `P_w`, `U_load`, `P_w†` (`fullActualOracle`) | `2160 g' K` matrix queries; `≤ 40 g'` calls of each of `P_w`, `U_load`, `P_w†`; `≤ 120 g'` source calls |
| `odel:lem:dyson` | `full_approx` (`Approx.lean`) | supplied `P_w(x)`, `U_load(x)` on temporary work registers within `δ` of exact `P`, `L` on clean work (`CleanErr`), `30 g' δ ≤ 1/400`, `30 g' δ ≤ ε/20`, `FullValidAt … P L …` | `GeneralSourceExtensions.ApproxCertificate` (success `≥ 2/3`, conditional trace distance `≤ ε`) | as `full_actual` |
| `odel:eq:dyson` | `full_bound` (`Theorem.lean`) | `s > 0`, `T, η > 0`, `ḡ, c_q ≥ 1`, `0 < ε ≤ 1` | `2160 g' K ≤ dysonBound z (c_q ḡ) ε = 16000 c_q ḡ e^z (1 + z + L/log(e + L/z))`, `L = log(4000 c_q ḡ/ε)` | — |
| `odel:eq:fixed` | `full_fixed` (`Corollaries.lean`) | fixed `z > 0`, `ḡ ≥ 1`, `c_q ≥ 1` | `∃ C₀, ε₀ ∈ (0,1)`, `log log(1/ε) > 0` on `(0, ε₀]`, then for all `ε ≤ ε₀` and every public spec with `s η T = z` a heralded program on `FullValid` | `≤ C₀ log(1/ε)/log log(1/ε)` matrix queries |
| `odel:eq:fixed` (consequence) | `full_no_uniform` (`Corollaries.lean`) | fixed `s`, `τ > 0`, `ḡ ≥ 1`, `c_q ≥ 1`, `c > 0` | `∃ ε_c > 0`, for all `ε ≤ ε_c` and every public spec with `η T = τ` a heralded program on `FullValid` | `< c ḡ √s τ log(ḡ/ε)` matrix queries |
| `odel:eq:fixed` and consequence, approximate preparations | `approx_fixed`, `approx_no_uniform` (`Corollaries.lean`) | as `full_fixed`, `full_no_uniform`, with supplied preparations on temporary work registers | the four-attempt protocol of `full_approx` with `ApproxCertificate` on every valid instance within the clean-input budget | `≤ C₀ log(1/ε)/log log(1/ε)`, resp. `< c ḡ √s τ log(ḡ/ε)`, matrix queries in every history |
| `ode:thm:time` (coverage) | `fullValidAt_of_clipped`, `fullValidAt_of_raw` (`Coverage.lean`) | the clauses of `ode:thm:time`, `E ≤ log(1 + δ_m)` (clipped) or `2 s E_raw ≤ log(1 + δ_m)` with true entries `≤ η` and `s`-sparse pieces, `ζ + c_q δ_m ≤ ε/(2000 ḡ)` | `FullValidAt … x (x(T))` | — |
| `ode:thm:time` (coverage, branch certificates) | `ManuscriptConformance.fullValidAt_of_branch_raw`, `fullValidAt_of_branch_clipped`, `fullValid_of_branch_raw` (`ManuscriptConformance/BranchCertificates.lean`) | as above, with certificates `E_± = ∑_r ∫ ‖K_{±k}(G_r(u) - C_r)‖` on the opposite branches `K_{±k} = H ± k D` (`k > 0`) of the same samples: `2 s ((1 + 1/k)(E₊ + E₋)/2) ≤ log(1 + δ_m)` (raw) or `(1 + 1/k)(E₊ + E₋)/2 ≤ log(1 + δ_m)` (clipped) | `FullValidAt … x (x(T))`, resp. `FullValid` | — |

## The steps

* (A) `Perturb`: `cell_perturb`, `node_perturb`, `propagator_perturb`: for the true propagator `U`
  (contractive) and the represented product `V` (not contractive), `‖V‖ ≤ e^{E}` and
  `‖U - V‖ ≤ e^{E} - 1` uniformly over start times, partial first cells included, by Gronwall on
  the integrated distance (`integral_exp_weight_le`, `exp_norm_le_of_reLower`).
* (B) `Clip`: `radialClip` (`p_η`, `radialClip_zero`, `norm_radialClip_sub_le`), `clipData`
  (`oracles_clipData`: the same native calls; only the rotation decoder changes),
  `clip_sub_le` (`‖p_η(C_raw) - A‖ ≤ 2 s ‖C_raw - A‖` pointwise); the six-query block encoding of
  `C_r/(s η)` on the original access (`Select.gSelect_compression`).
* (C) `Select`, `Atten`, `Target`: the Dyson SELECT on arbitrary branch labels (`gSelect`,
  `18 K` native calls, coherently disabled unused slots, fresh flags); the label-dependent
  attenuation `cos θ = Target.cfgAtten` of the cell lengths `max(u, t_{j+1}) - max(u, t_j)`
  (`Atten.atten_compression`); the common table `fTable` with one normalisation
  `N_D = 2 e^z` independent of the hidden norms (`fTable_mass`); `table_sum_eq`: every label
  sees its own node series `nodeSeries`, later generators to the left, occupation factorials.
* (D) `Target.dysonTarget_error`: `‖y_K - x(T)‖ ≤ ζ B + B_q ((e^{E} - 1) + tail_K)`;
  `Theorem.fDecoded`: the decoded vector of the actual preparation is exactly `(N_D B_q)⁻¹ y_K`;
  `Herald.herald_window`: normalisation by `‖x(T)‖ ≥ B/ḡ` without `B ≤ B_q`; the actual
  preparation and its actual inverse are amplified about the public seed and output flag;
  `Approx.full_approx` charges the implementation error of the supplied preparations through the
  whole amplified protocol (`δ = O(ε/(c_q ḡ e^z))`).
* (E) `full_bound`, `full_fixed`, `full_no_uniform` as in the table; quantifier order: the
  program is chosen from the public specification, then the guarantee holds for every valid
  unknown input.

## Acceptance checks (`Examples`)

`growC_not_accretive`, `zero_true_cell`, `exp_growC`, `zero_true_sharp`, `const_error_eq` (check
1); `exMesh_widths`, `nodeSeries_end`, `exPhases`, `exMass`, `exAssembly`, `cfgProduct_cfg11`,
`meshNodeProduct_two`, `eLower_eRaise_ne` (check 2); `meshWidth_left`, `meshWidth_zero_start`,
`left_endpoint_mass` (check 3); `clipData_decode`, `numerator_charge` (check 4).

## Not covered

* A single coherent program for approximate preparations: `full_approx` is the four-attempt
  protocol with its worst-case counts; `full_single` uses exact preparations.
* Monotonicity of `dysonBound` in `ḡ`: the fixed-parameter corollaries hold for each fixed
  `c_q ≥ 1` (the absolute model constant), with constants depending on `c_q`.
* No gate bound and no time-register width are claimed.
-/
