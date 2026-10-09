import TimeDependentLowerBoundExtensions.Core.Assembly
import TimeDependentLowerBoundExtensions.Core.Masked
import TimeDependentLowerBoundExtensions.Core.Cost
import TimeDependentLowerBoundExtensions.BlockEncoding.Hard
import TimeDependentLowerBoundExtensions.BlockEncoding.Access
import TimeDependentLowerBoundExtensions.BlockEncoding.Bound
import TimeDependentLowerBoundExtensions.BlockEncoding.NonVacuity
import TimeDependentLowerBoundExtensions.BlockEncoding.Integrable
import TimeDependentLowerBoundExtensions.Coherent.Access
import TimeDependentLowerBoundExtensions.Coherent.Bound
import TimeDependentLowerBoundExtensions.Coherent.Tree
import TimeDependentLowerBoundExtensions.Coherent.NonVacuity
import TimeDependentLowerBoundExtensions.Coherent.Calls
import TimeDependentLowerBoundExtensions.Coherent.Integrable
import TimeDependentLowerBoundExtensions.Calls.Bound
import TimeDependentLowerBoundExtensions.Gate.Program
import TimeDependentLowerBoundExtensions.Gate.Bound
import TimeDependentLowerBoundExtensions.Gate.NonVacuity
import TimeDependentLowerBoundExtensions.Tolerant.Approx
import TimeDependentLowerBoundExtensions.Tolerant.Realization
import TimeDependentLowerBoundExtensions.Tolerant.Program
import TimeDependentLowerBoundExtensions.Tolerant.Bound
import TimeDependentLowerBoundExtensions.Tolerant.LipschitzClass
import TimeDependentLowerBoundExtensions.Tolerant.LipschitzBound
import TimeDependentLowerBoundExtensions.Measured.Compile
import TimeDependentLowerBoundExtensions.Measured.MaskedLift
import TimeDependentLowerBoundExtensions.Measured.Assembly
import TimeDependentLowerBoundExtensions.Measured.BlockCompile
import TimeDependentLowerBoundExtensions.Measured.Block
import TimeDependentLowerBoundExtensions.Measured.Uniform
import TimeDependentLowerBoundExtensions.Measured.Mesh
import TimeDependentLowerBoundExtensions.Measured.Select
import TimeDependentLowerBoundExtensions.Measured.NonVacuity

set_option autoImplicit false

/-!
# The lower bound of `hsl:thm:main` in further time-dependent settings: paper-to-Lean entry point

Theorem `hsl:thm:main` (the manuscript, lines 2102-2119, eq. `hsl:eq:main`, line 2109) bounds the
worst-case sparse-oracle query complexity of simulation by `c₀ (√s τ + √(sτr) + r)` with
`c₀ = log 2 / (4096π)`. The paragraph after Theorem `hs:thm:time` ends (lines 1512-1516): "The
lower bound in Theorem `hsl:thm:main` also applies to this class, since its time-independent
hard instances satisfy the new assumptions with `β = δ_val = 0`." The library
`TimeDependentHamiltonianLowerBound` formalises this remark for the released uniform-mesh,
general-mesh and integrable-path simulators. This library carries the same lower bound, with the
same time-independent hard instances (hard paths constant in time), into further settings:

* **time-indexed block encodings** (paragraph "Relation to time-indexed block encodings", lines
  1518-1538, eqs. `hs:eq:blockspecial`, line 1525, and `hs:eq:blockadditive`, line 1533; the
  normalisation comparison, lines 1552-1561);
* **coherent selection** of known durations and start times (lines 1505-1510: "provided the
  corresponding coherent sampled-time oracle is supplied");
* **all call forms** (plain, inverse, controlled, controlled inverse) of the oracle families of
  the released time-dependent simulators (native access "with inverses and coherent controls",
  lines 2078-2082);
* **gate-level time-dependent circuits** with slot-selected private operations (Theorem
  `hs:thm:gates`, line 1814, is stated for time-independent Hamiltonians only, line 1849; time
  slots, line 1801; the gate model with error `ξ` for controlled private operations, lines
  1805-1812), with private operations realised exactly or within an error `ξ`;
* the **piecewise Lipschitz paths** with breakpoints of the paragraph after Theorem
  `hs:thm:time` (lines 1497-1500);
* **measured algorithms** (measurements inside a run; "Randomised or adaptive algorithms are
  covered by purification and deferred measurement", lines 2363-2364) over the oracle families
  of the released time-dependent simulators and their call forms.

All declarations below are in the namespace `TimeDependentLowerBoundExtensions` (sub-namespaces
`Core`, `BlockEncoding`, `Coherent`, `Calls`, `Gate`, `Tolerant`, `Measured`). The hard
families `timeData`, `mixedMainData`, `precisionMainData`, the range `HSRange τ s ε`, `c0`, `hsR` and `hardCost` are
those of `SparseLowerBounds.Hamiltonian` (`SparseLowerBounds` for `hardCost`); `constData`,
`constPath`, `UniformGuarantee`, `MeshCriterion`, `IntegrableCriterion` are those of
`TimeDependentHamiltonianLowerBound`; `callFamily` is `AdaptiveODELowerBound.Access.callFamily`
and `valueWeight` is `AdaptiveHamiltonianLowerBound.Access.valueWeight`.

* **Assembly for certified families** (`Core`): `main_max_access` (any three oracle families
  with Boolean certificates and any weights), `main_max_uniform_weight` (one weight per call),
  `nonempty_access_of_normal_form`; masked calls, call forms and spectator wrappers:
  `maskedBoolean`, `maskedEncoding`, `maskedEncoding_isometry`, `implementsOn_masked`,
  `maskedAccess`, `callAccess`, `callFamily_conj`, `admissible_callFamily_of_normal_form`,
  `nonempty_access_of_wrap`; Boolean cost of labelled calls: `hardCost_eq_two_mul`,
  `cost_hardCost_fst`, `cost_valueWeight_fst_le_count`, `max_calls_of_hardCost`.
* **Time-indexed block encodings** (`BlockEncoding`): the hard Hermitian block encodings
  `beOp`, `beJ`, `beAlpha`, `beConst` (`BEBasis`, `beLayout`) with `beOp_selfAdjoint`,
  `beOp_unitary`, `beJ_isometry`, `beAlpha_pos`, `beJ_compress`, `blockSample_beOp`; the
  certificates `implementsOn_beOp`, `beEncoding_isometry`, `beOpAccess`, `primitive_beConst`,
  `nonempty_primitiveAccess`, `nonempty_alignedAccess` (spectators `beWrap`, `isWrap_beWrap`,
  `aligned_eq_beWrap`; `alignedOracle_beConst_unitary`); the criterion `BECriterion` and
  `beCriterion_endpoint`; the bounds `main_max_block_endpoint`, `main_max_block`,
  `main_max_block_primitive`, `main_max_calls_block`; under the integrable-path criterion
  `BEIntegrableCriterion`, `beIntegrableCriterion_endpoint`, `main_max_block_integrable`;
  non-vacuity `beConst_hyps`, `exists_beProgram`.
* **Coherent selection** (`Coherent`): `select_normal_form`, `nonempty_selectAccess`,
  `admissible_select`, `admissible_callFamily_select`; `branchInj`, `branchInj_isometry`; the
  criteria `SelectCriterion`, `WindowsCriterion` and `select_endpoint`, `windows_endpoint`; the
  bounds `main_max_select`, `main_max_windows`, `main_max_tree_select`, and over all call forms
  `main_max_calls_select`, `main_max_calls_windows`, `main_max_tree_calls_select`; under the
  integrable-path criterion `WindowsIntegrableCriterion`, `windowsIntegrable_endpoint`,
  `main_max_windows_integrable`; non-vacuity `exists_selectProgram`, `exists_windowsProgram`.
* **Call forms of the released families** (`Calls`): `main_max_calls_uniform`,
  `main_max_calls_mesh`, `main_max_calls_integrable`, `main_max_tree_calls_uniform`,
  `main_max_tree_calls_mesh`; admissibility `admissible_callFamily_uniform`,
  `admissible_callFamily_mesh`.
* **Gate-level circuits** (`Gate`): `privFamily`, `slotOracle_const_eq`, `exists_program`; the
  realisation hypothesis `NativeRealization`, `nonempty_privAccess`, and its satisfiability
  `nativeRealization_call`; the bounds `main_max_gate`, `main_max_gate_uniform`.
* **Gate-level circuits within `ξ`** (`Tolerant`, lines 1805-1812 and the accounting of Theorem
  `hs:thm:gates`, lines 1814-1851): operator facts `approx_adjoint`, `masked_approx`,
  `approx_comp_encoding`, `controlOne`, `controlOne_isometry`, `masked_comp_controlOne`,
  `comp_controlOne_isometry`, `approx_of_controlled`; the hypothesis `ApproxRealization` with
  `approxRealization_zero_iff`, `approxRealization_of_native`, `ApproxRealization.mono`,
  `approxRealization_of_near`, `approxRealization_call`, `approxRealization_of_controlled`; the
  realised circuits `realFamily`, `realEncoding`, `realFamily_unitary`, `realEncoding_isometry`,
  `nonempty_realAccess`, `norm_sub_conj_le`, `exists_approxProgram`; the bounds
  `main_max_gate_tolerant`, `main_max_gate_uniform_tolerant`; containment
  `main_max_gate_of_tolerant`, `main_max_gate_uniform_of_tolerant`.
* **Piecewise Lipschitz paths** (`Tolerant`, lines 1497-1500 and 1513-1516): the class
  `LipschitzPath` and criterion `LipschitzGuarantee`, `LipschitzPath.meshPath`,
  `lipschitzGuarantee_of_meshGuarantee`, `lipschitzPath_const`,
  `LipschitzGuarantee.criterion_const`, `simulation_lipschitz_guarantee`,
  `meshHyp_simulation_lipschitz`; the bounds `lipschitz_class_max`, `lipschitz_class_max_calls`;
  `mesh_class_max_of_lipschitz`, `lipschitz_class_nonvacuous`.
* **Measured algorithms** (`Measured`, lines 2363-2364): compilation of calls `callProgram`,
  `compile`, `eval_callProgram`, `cost_callProgram`, `successDensity_compile`,
  `successMass_compile`, `conditionalDensity_compile`, `worstCost_compile`,
  `worstCost_const_le`, `worstCost_compile_le`; masked lifts `IsMaskedLift`, `masked_conj`,
  `masked_masked`, `masked_diagonal`, `isMaskedLift_masked`, `isMaskedLift_fiber`,
  `isMaskedLift_of_isWrap`, `isMaskedLift_normal_form`, `IsMaskedLift.conj`, `.masked`, `.wrap`,
  `.map_one`, `.map_mul`, `.map_star`, `.map_unitary`, `.admissible`, `liftProgram`,
  `eval_liftProgram`, `cost_liftProgram`; the certificate `NativeCompiles`,
  `nativeCompiles_of_admissible`, `NativeCompiles.map`, `NativeCompiles.callFamily`,
  `exists_compiled_measured`, `main_max_measured_compiled`; block-encoding calls `sectorLift`,
  `beSector`, `beProgram`, `isMaskedLift_sectorLift`, `admissible_beSector`, `beSwap_unitary`,
  `eval_beProgram`, `cost_beProgram`, `nativeCompiles_beOp`, `nativeCompiles_primitive`,
  `nativeCompiles_aligned`, `nativeCompiles_calls_aligned`; the bounds
  `main_max_measured_block`, `main_max_measured_block_primitive`,
  `main_max_measured_calls_block`, `main_max_measured_uniform`,
  `main_max_measured_calls_uniform`, `main_max_measured_mesh`, `main_max_measured_calls_mesh`,
  `main_max_measured_select`, `main_max_measured_calls_select`; non-vacuity `programRun`,
  `adjoint_one_comp_one`, `programRun_meets`, `released_uniform_measured`,
  `released_mesh_measured`, `released_integrable_measured`, `released_select_measured`,
  `released_block_measured`.

**Hard instances.** The hard families of Theorem `hsl:thm:main` are the released native sparse
data `timeData τ s _`, `mixedMainData τ ε s _`, `precisionMainData τ ε s _` (real symmetric,
operator norm and row and column norms one, sparsity `s`, input-independent locators). In every
setting the hard path is constant in time: the constant data `constData D M` (every one of the
`M` samples equal to the instance) and the constant path `constPath D x u = D.matrix x`, whose
propagator at time `τ` is `exp(-iτH_x)`. For the block-encoding model the instance is supplied
through `beOp D x = dilation(W_x)`, the package's Hermitian dilation
(`SparseHamiltonian.HermitianDilation.dilation`) of the released six-query block encoding
`W_x` of `H_x/(s a)` (`a = D.scale`), on one extra qubit: `beOp D x` is Hermitian and unitary,
`beJ D = |+⟩ ⊗ J₀` is an isometry, and `beJ† (beOp D x) beJ = H_x / beAlpha D` with
`beAlpha D = s · D.scale` (`beJ_compress`, `blockSample_beOp`), the normalisation `α_BE = sη` of
a standard sparse block encoding (lines 1552-1561). `beConst D M` has every sample equal to
`beOp D x`.

**Access models.**

* Block encodings: programs over the released aligned block-encoding family
  `TimeDependentExtensions.BlockEncoding.alignedOracle (beConst D M) N α T ε'` (any number `M`
  of samples, slot count `N`, normalisation and schedule) or over the controlled time-indexed
  oracle `TimeDependentExtensions.BlockEncoding.primitive (beConst D M)` itself
  (`|c, r⟩ ⊗ v ↦ |c, r⟩ ⊗ O_r^c v`), or over all call forms `callFamily` of the aligned family.
  The cost is the number `p.count` of block-encoding calls.
* Coherent selection: programs or adaptive algorithms (`SparseLinearSystems.Protocol.Tree`)
  over the released selection family
  `TimeDependentExtensions.MeshSelect.alignedOracle (ι := ι) (constData D M) N γ ρ T ε'` (any
  branch register `ι`, samples, slots and schedule), or over all its call forms; a branch
  `i₀` is read through `E ∘ branchInj ι N i₀`. The cost is the number of value calls
  (`labelCount .value`, respectively `cost (valueWeight ∘ fst)` or `worstCost valueWeight`) and,
  for programs, also the number of calls.
* Call forms of the released families: programs over `callFamily` of
  `SparseHamiltonian.TimeDependent.oracle (constData D M) γ η t ε'` (uniform meshes) and of
  `TimeDependentExtensions.Hamiltonian.oracle (constData D M) N γ η T ε'` (general meshes and
  integrable paths), with a control qubit in the encoding (`Joint Bool _`), and adaptive
  algorithms over the same call families. Cost: value calls in any form, and the number of calls.
* Gate-level circuits: instruction lists `gs` of the package's slot-selected circuits
  (`SparseHamiltonian.GateCircuit.Instr`, run by `runT U_J D gs`), with a public unitary `U_J`,
  valid instructions, and a private operation `D_x` constant over the slots; cost `nPriv gs`,
  the number of private calls (forward or inverse, any literal controls). `privFamily` and
  `exists_program` express every such circuit as a program with `nPriv gs` calls.
  `NativeRealization D D_x q` says that `D_x` is implemented exactly, on one fixed isometric
  encoding with an untouched spectator register, by a program over all call forms of the native
  sparse queries of `D` with at most `q` value calls (location calls free).
  `Tolerant.ApproxRealization D D_x q ξ` says the same within operator-norm error `ξ`:
  `‖p(x) ∘ e - e ∘ D_x‖ ≤ ξ` on one fixed isometric encoding `e` (full-output ancilla
  convention, lines 511-533), with `q` independent of `ξ`.
* Piecewise Lipschitz paths: programs over the released general-mesh family
  `TimeDependentExtensions.Hamiltonian.oracle (constData D M) N γ η T ε'` (and over all its
  call forms) with an isometric encoding; cost the number of value calls and of calls.
* Measured algorithms `DeferredMeasurementLowerBounds.Model.Measured O K` (mid-run and
  multi-outcome measurements, classical control, randomness and resets) on the workspace of the
  family `O` itself: the uniform-mesh family `SparseHamiltonian.TimeDependent.oracle
  (constData D M) γ η t ε'`, the general-mesh and integrable-path family
  `TimeDependentExtensions.Hamiltonian.oracle (constData D M) N γ η T ε'`, the selection family
  `TimeDependentExtensions.MeshSelect.alignedOracle (constData D M) N γ ρ T ε'`, the aligned
  block-encoding family `TimeDependentExtensions.BlockEncoding.alignedOracle (beConst D M) N α T
  ε'` and the controlled time-indexed oracle `primitive (beConst D M)`, and all call forms of
  these. The cost is the worst-case number of value calls over all transcripts (`worstCost
  valueWeight`, every call form counted once, location calls free), and the worst-case number of
  block-encoding calls for the block-encoding families.

**Hypotheses.** `HSRange τ s ε` (`τ ≥ 1`, `s ≥ 32`, `0 < ε ≤ 1/64`), as in the released
`SparseLowerBounds.Hamiltonian.main_max`; isometric input encodings (`ι† ι = 1`); one error
criterion per family:

* endpoint error at most `ε` against `exp(-iτH_x)` (`main_max_block_endpoint`,
  `main_max_block_primitive`, `main_max_calls_block`, `main_max_gate`, `Core.main_max_access`);
* `BECriterion` (`main_max_block`): the guarantee of
  `TimeDependentExtensions.BlockEncoding.simulation`, error at most `ε` at time `τ` against every
  propagator from the identity of every family of self-adjoint, interval-integrable pieces whose
  integrated sample errors against `α J† O_r J` sum to at most `ε/9`;
* `BEIntegrableCriterion` (`main_max_block_integrable`): the guarantee of
  `IntegrablePathSimulation.BlockEncoding.simulation`, error at most `ε` at time `τ` against
  every integral-sense propagator of every path self-adjoint at almost every time of `[0, τ]`
  and interval integrable on `[0, τ]` whose integrated sample errors against `α J† O_r J` sum to
  at most `ε/9` (integrable Hermitian paths, lines 1500-1504);
* `SelectCriterion` with a public duration table `u` and a branch of total duration
  `∑_k u_{i₀}(σ k)/N = τ`; `WindowsCriterion` with a public table of windows and a branch with
  `t_{b_{i₀}} - t_{a_{i₀}} = τ` (the guarantees of
  `TimeDependentExtensions.Coherent.coherent_select` and `coherent_windows`);
  `WindowsIntegrableCriterion` (`main_max_windows_integrable`), the guarantee of
  `IntegrablePathSimulation.Coherent.coherent_windows` (paths Hermitian at almost every time of
  `[0, T]` and interval integrable on `[0, T]`, integral-sense solutions on the windows), with a
  branch with `t_{b_{i₀}} - t_{a_{i₀}} = τ`;
* `UniformGuarantee`, `MeshCriterion`, `IntegrableCriterion` on the constant paths (the
  criteria of the released theorems, as in `TimeDependentHamiltonianLowerBound`), and
  `UniformGuarantee` for `main_max_gate_uniform`;
* adaptive forms: success mass at least `2/3` and `DensityAccurate` within `ε` against every
  propagator of the constant path solving `U' = -iHU` from the identity (the hypotheses of
  `TimeDependentHamiltonianLowerBound.main_max_tree_uniform`);
* gate-level forms: `IsUnitary U_J`, `IsUnitary D_x`, valid instructions and
  `NativeRealization D D_x q` on each family;
* `ξ`-tolerant gate-level forms (`Tolerant.main_max_gate_tolerant`,
  `main_max_gate_uniform_tolerant`): the same with `ApproxRealization D D_x q ξ_F` on each family
  `F`, an ideal-circuit endpoint error `ε₀_F` against `exp(-iτH_x)` (respectively
  `UniformGuarantee` at `ε₀_F`) on an isometric encoding, and `ε₀_F + nPriv_F · ξ_F ≤ ε`;
* `LipschitzGuarantee` (`Tolerant.lipschitz_class_max`, `lipschitz_class_max_calls`): the
  guarantee of `TimeDependentExtensions.Hamiltonian.simulation_lipschitz`, error at most `ε` at
  the final time against every piecewise propagator of every piecewise Lipschitz path of the
  class (`LipschitzPath`: Hermitian `β_r`-Lipschitz pieces on the mesh intervals, one-sided
  sample errors `δ_r`, `∑_r (β_r Δ_r²/2 + δ_r Δ_r) ≤ ε/9`), no mesh hypothesis;
* measured forms (`Measured`): success mass at least `2/3` on every input from a unit initial
  vector and eq. `hsl:eq:accuracy` (line 2092) against every propagator of the constant path
  from the identity, as in the adaptive forms; `NativeCompiles D O c` for
  `main_max_measured_compiled`.

**Quantifiers.** For every `τ, s, ε` with `HSRange τ s ε`; for any sample counts, slot counts,
meshes, schedules and duration or window tables of each family; for any isometric encodings and
programs or adaptive algorithms meeting the stated criterion on each of the three hard families;
for the gate-level forms, any `q`, unitary `U_J` and valid instruction lists: the bound below
holds for the maximum of the three costs, with the constants stated there.

**Guarantees** (`S = √s τ + √(sτr) + r`, `L = log(1/ε)`, `h = log(e + L/τ)`, `r = hsR τ ε = L/h`,
`c₀ = log 2/(4096π)`; `Q_T, Q_M, Q_P` the costs of the algorithms on the time, mixed and
precision families):

* block-encoding calls: `c₀ S ≤ 8 · max(Q_T, Q_M, Q_P)` (`main_max_block`,
  `main_max_block_endpoint`, `main_max_block_primitive`, `main_max_calls_block`,
  `main_max_block_integrable`); every
  block-encoding call, in any form, costs at most `16` Boolean queries;
* gate-level private calls: `c₀ S ≤ q · max(nPriv_T, nPriv_M, nPriv_P)` (`main_max_gate`,
  `main_max_gate_uniform`, and `Tolerant.main_max_gate_tolerant`,
  `Tolerant.main_max_gate_uniform_tolerant` with `r = r(τ, ε)`);
* piecewise Lipschitz class: `c₀ S ≤ max(Q_T, Q_M, Q_P)` value calls and calls
  (`Tolerant.lipschitz_class_max`, `Tolerant.lipschitz_class_max_calls`);
* measured algorithms: `c₀ S ≤ max(Q_T, Q_M, Q_P)` worst-case value calls
  (`Measured.main_max_measured_uniform`, `_mesh`, `_select` and their `_calls_` forms),
  `c₀ S ≤ 8 · max(Q_T, Q_M, Q_P)` worst-case block-encoding calls
  (`Measured.main_max_measured_block`, `_block_primitive`, `_calls_block`), and
  `c₀ S ≤ c · max(Q_T, Q_M, Q_P)` for natively compiled families of cost `c`
  (`Measured.main_max_measured_compiled`);
* value calls otherwise: `c₀ S ≤ max(Q_T, Q_M, Q_P)` with `Q` the number of value calls (in any
  call form), and the same for the number of calls (`main_max_select`, `main_max_windows`,
  `main_max_windows_integrable`,
  `main_max_calls_select`, `main_max_calls_windows`, `main_max_calls_uniform`,
  `main_max_calls_mesh`, `main_max_calls_integrable`), and for the worst-case value-call cost of
  adaptive algorithms (`main_max_tree_select`, `main_max_tree_calls_select`,
  `main_max_tree_calls_uniform`, `main_max_tree_calls_mesh`);
* certified families: `2 c₀ S ≤ max(p_T.cost w_T, p_M.cost w_M, p_P.cost w_P)` in the Boolean
  cost (`Core.main_max_access`), and `2 c₀ S ≤ c · max(count_T, count_M, count_P)` for one
  weight `c` per call (`Core.main_max_uniform_weight`).

**Non-vacuity.** `exists_beProgram`: for any data, `0 < M`, any mesh `t` of `[0, T]` with
`M` pieces, `0 < T`, `0 < ε ≤ 1`, `0 < N`, `4 α T ≤ N`, `9 (αT)³ ≤ ε N²` and `9 M αT ≤ ε N`
(`α = beAlpha D`), the released block-encoding simulator gives a program over the family of
`main_max_block` with at most `2304 (αT + 1 + log(3/ε))` calls (eq. `hs:eq:blockadditive`) whose
clean isometric encoding meets `BECriterion`; `beConst_hyps` gives the instance hypotheses.
`exists_selectProgram`, `exists_windowsProgram`: for Hermitian data with row and column norms at
most `η > 0`, `0 < T`, `0 < ε ≤ 1`, `8 s η T ≤ N` and the Cayley condition, there is
`0 < γ ≤ 1` with `1 ≤ γ √(2s)` such that for every public duration table (every table of
windows of a mesh) a program over the selection family with at most
`663552 · shape(2s, ηT, targetLog ε)` calls (`ε/3` in the windows form,
`SparseHamiltonian.ImprovedPrecisionBudget.shape`) meets `SelectCriterion` (`WindowsCriterion`)
with its clean isometric encoding. For the call forms of the released families, non-vacuity is
that of `TimeDependentHamiltonianLowerBound` (plain calls are call forms). The integrable-path
criteria `BEIntegrableCriterion` and `WindowsIntegrableCriterion` are the error conclusions, for
one program, of `IntegrablePathSimulation.BlockEncoding.simulation` and
`IntegrablePathSimulation.Coherent.coherent_windows`, which supply such programs over the same
families under the same slot conditions (not restated here). `nativeRealization_call`: every
call form of one native sparse query, on any spectator register, satisfies `NativeRealization`
with `q = 1` (the one-call program on the identity encoding); the manuscript's gate model
(lines 1805-1812) assumes a fixed primitive-oracle cost per private operation, which
`NativeRealization` states in exact form. `Tolerant.approxRealization_call` (every `ξ ≥ 0`) and
`Tolerant.approxRealization_of_near` (an operation within `ξ` of an exactly realised one) give
`ApproxRealization`. `Tolerant.lipschitz_class_nonvacuous`: the released general-mesh simulators
of the three constant families meet the hypotheses of `lipschitz_class_max` on every admissible
mesh; `Tolerant.simulation_lipschitz_guarantee`: the conclusion of `simulation_lipschitz`, under
its own hypotheses, is `LipschitzGuarantee` for its program and encoding.
`Measured.programRun_meets`: a unitary program with endpoint error at most `ε`, run as a
measured algorithm and output in full, succeeds with probability one and meets eq.
`hsl:eq:accuracy` (lines 2096-2097); `Measured.released_uniform_measured`,
`released_mesh_measured`, `released_integrable_measured`, `released_select_measured` (every
branch of total duration `τ`) and `released_block_measured` (at most
`2304 (αT + 1 + log(3/ε))` calls): the released simulators on constant data supply such
programs over the families of the measured bounds.

**Proof map.** Module paths are relative to `TimeDependentLowerBoundExtensions/`.

* `Core/Assembly.lean`: `main_max_access` from the released family lemmas
  `SparseLowerBounds.Hamiltonian.time_general`, `mixed_general`, `precision_general` on any
  three certified families; `main_max_uniform_weight` with the constant weight;
  `nonempty_access_of_normal_form` transports the certificates of the native primitives
  through a fixed isometric identification `U⁻¹ (1_Ω ⊗ ·) U`.
* `Core/Masked.lean`: masked calls (`SparseHamiltonian.MaskedProgram.masked`) keep the weights
  (`implementsOn_masked`, `maskedAccess`); all call forms through
  `AdaptiveODELowerBound.Access.implementsOn_callFamily` (`callAccess`); spectator wrappers
  `ODELowerBoundExtensions.Release.IsWrap` (`nonempty_access_of_wrap`); admissibility of call
  forms through fixed layouts.
* `Core/Cost.lean`: `hardCost = 2 · valueWeight` on native labels, by induction on programs
  (`cost_hardCost_fst`); halving the Boolean max form (`max_calls_of_hardCost`).
* `BlockEncoding/Hard.lean`: the dilation of the six-query program and its compression
  (`NativeSparseBlockEncoding.compression`, `HermitianDilation.encodedPlus`).
* `BlockEncoding/Access.lean`: each call of `beOp D x` is the fixed swap and two masked runs of
  the six-query program, at most `16` Boolean queries (`implementsOn_beOp`); the released
  aligned families add spectators only.
* `BlockEncoding/Bound.lean`: `beCriterion_endpoint` (constant pieces, zero sample error), then
  `Core.main_max_uniform_weight` with weight `16` (`Core.callAccess` for the call forms).
* `BlockEncoding/NonVacuity.lean`: `TimeDependentExtensions.BlockEncoding.simulation` on
  `beConst D M`.
* `BlockEncoding/Integrable.lean`: the constant path has zero sample error and `exp(-iuH_x)` is
  an integral-sense propagator (`TimeDependentHamiltonianLowerBound.isPropagator_constProp`), so
  `beIntegrableCriterion_endpoint` gives the endpoint form; then `main_max_block_endpoint`.
* `Coherent/Access.lean`: on constant data the branch and time registers and the native Cayley
  wrapper (`ODELowerBoundExtensions.Release.cayleyWrap`) are spectators and relabellings
  (`select_normal_form`).
* `Coherent/Bound.lean`: `select_endpoint`, `windows_endpoint` restrict the criteria to the
  branch `i₀`; programs through `Core.main_max_access`.
* `Coherent/Tree.lean`: adaptive algorithms through
  `AdaptiveHamiltonianLowerBound.main_max_tree` with `admissible_select` and
  `TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff`.
* `Coherent/Calls.lean`, `Calls/Bound.lean`: `Core.callAccess` and
  `Core.admissible_callFamily_of_normal_form` with the released normal forms
  (`TimeDependentHamiltonianLowerBound.uniform_normal_form`, `mesh_normal_form`); the criteria
  reduce to the endpoint form as in `TimeDependentHamiltonianLowerBound`; programs through
  `Core.main_max_access` and `Core.max_calls_of_hardCost`, adaptive algorithms through
  `AdaptiveHamiltonianLowerBound.main_max_tree`.
* `Coherent/NonVacuity.lean`: `TimeDependentExtensions.Coherent.coherent_select` and
  `coherent_windows` on `constData D M`.
* `Coherent/Integrable.lean`: `V_i(u) = exp(-i(u - t_{a_i})H_x)` solves the constant path in
  the integral sense on every window
  (`IntegrablePathSimulation.Propagator.solvesIntegralOn_of_solvesOn` when
  `t_{a_i} ≤ t_{b_i}`, an empty interval otherwise), so `windowsIntegrable_endpoint` gives the
  endpoint form on the branch `i₀`; programs through `Core.main_max_access`.
* `Gate/Program.lean`: a constant slot-selected private call is a masked call of `D_x` in one
  fixed layout (`slotOracle_const_eq`), so every circuit is a program over `privFamily`
  (`exists_program`).
* `Gate/Bound.lean`: `NativeRealization` and `Core.implementsOn_masked` give `2q` Boolean
  queries per private call (`nonempty_privAccess`), then `Core.main_max_uniform_weight`;
  `main_max_gate_uniform` reduces `UniformGuarantee` to the endpoint form
  (`TimeDependentHamiltonianLowerBound.uniform_criterion_iff`).
* `Gate/NonVacuity.lean`: `nativeRealization_call`, the one-call program on the identity
  encoding.
* `Tolerant/Approx.lean`: adjoints, masks and isometric encodings keep the error `ξ`; the
  control-one branch `controlOne` restricts a controlled implementation.
* `Tolerant/Realization.lean`: `ApproxRealization` and its relation to `Gate.NativeRealization`
  (`approxRealization_zero_iff`).
* `Tolerant/Program.lean`: the circuit with realised private calls is a program over
  `realFamily` (`Gate.slotOracle_const_eq`), within `nPriv · ξ` of the ideal circuit on
  `realEncoding` (`exists_approxProgram`, a hybrid argument through `norm_sub_conj_le`);
  `nonempty_realAccess` gives `2q` Boolean queries per realised call.
* `Tolerant/Bound.lean`: `exists_approxProgram`, then `Core.main_max_uniform_weight` at error
  `ε₀_F + nPriv_F · ξ_F ≤ ε`; the uniform form through
  `TimeDependentHamiltonianLowerBound.uniform_criterion_iff`.
* `Tolerant/LipschitzClass.lean`: on nondecreasing mesh points a piecewise Lipschitz path is a
  path of the general-mesh class (`LipschitzPath.meshPath`); constant pieces belong to the class
  with `β = δ = 0` (`lipschitzPath_const`), and `LipschitzGuarantee` on constant data gives the
  general-mesh criterion on the constant path (`LipschitzGuarantee.criterion_const`).
* `Tolerant/LipschitzBound.lean`: `TimeDependentHamiltonianLowerBound.main_max_mesh` and
  `Calls.main_max_calls_mesh` through `LipschitzGuarantee.criterion_const`.
* `Measured/Compile.lean`: every call of a measured algorithm replaced by a program
  (`MultiOracleCircuit.Program.substitute`) keeps the heralded output and multiplies the
  worst-case cost by at most `c`.
* `Measured/MaskedLift.lean`, `Measured/Assembly.lean`: masked lifts of admissible labels are
  admissible (`IsMaskedLift.admissible`); natively compiled families compile into admissible
  families (`exists_compiled_measured`), then
  `DeferredMeasurementLowerBounds.Corollaries.main_max_measured`.
* `Measured/BlockCompile.lean`, `Measured/Block.lean`: each block-encoding call is the fixed
  product `SparseHamiltonian.NativeHermitianDilation.masked_swap` of masked native calls with
  `8` value calls (`eval_beProgram`, `cost_beProgram`), then `main_max_measured_compiled` with
  `TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff`.
* `Measured/Uniform.lean`, `Measured/Mesh.lean`, `Measured/Select.lean`: the labels are already
  admissible (`TimeDependentHamiltonianLowerBound.admissible_uniform`, `admissible_mesh`,
  `Coherent.admissible_select` and the call-form lemmas), then
  `DeferredMeasurementLowerBounds.Corollaries.main_max_measured`.
* `Measured/NonVacuity.lean`: `DeferredMeasurementLowerBounds.Model.ofProgram` with
  `SparseLowerBounds.Hamiltonian.accurate_of_endpoint`,
  `AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff` and
  `TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff`, on the released
  simulators' programs (`TimeDependent.simulation`, `TimeDependentExtensions.Hamiltonian`,
  `IntegrablePathSimulation.Hamiltonian`, `Coherent.exists_selectProgram`,
  `BlockEncoding.exists_beProgram`).

**Formalisation choices.**

* The block-encoding bounds are an extension of lines 1512-1516 to the model of lines
  1518-1538: the manuscript states no lower bound in block-encoding calls (it derives the upper
  bound `hs:eq:blockadditive` and compares normalisations, lines 1552-1561). The hard instances
  enter through the package's dilation `beOp` of the released six-query block encoding, with
  `α_BE = s · scale`; the factor `8` (at most `16` Boolean queries per call against `2` per
  value call of the native bound) and the choice of dilation are properties of this reduction,
  not constants of the manuscript.
* Gate-level forms: the private operation is realised exactly (`NativeRealization`,
  `p.eval x ∘ e = e ∘ D_x`), as in the exact-gate, slot-selected model of
  `SparseHamiltonian.GateCircuit.SlotSim.gate_efficient_time_simulation`; the gate-level bounds
  are conditional on `NativeRealization`, a hypothesis built from the package's program model
  and value-call weight. The manuscript's gate-level theorem is for time-independent
  Hamiltonians (line 1849); these bounds are corollaries of Theorem `hsl:thm:main` for the
  package's time-dependent circuits.
* The coherent non-vacuity statements keep the released call-count bound
  (`663552 · shape`) and the released range of `γ` (`0 < γ ≤ 1`, `1 ≤ γ √(2s)`) of the selection
  theorems, so they also bracket the cost.
* Certificates are `Nonempty (PhaseAccess …)`: normal forms are existential (a fixed isometric
  identification exists), and certificate-producing results are stated with `Nonempty`.
* Hard paths are constant in time: the time, branch and slot registers are spectators only
  because the data are constant; the coherent forms read the branch `i₀` of total duration
  (window length) `τ`.
* Normalised units as in Theorem `hsl:thm:main`; the schedules of the algorithms' workspaces
  (samples, slots, `γ`, `ρ`, `α`, `T`, `ε'`) are arbitrary, and only the error criterion fixes
  the time `τ` and the accuracy `ε`.
* The integrable-path criteria (`BEIntegrableCriterion`, `WindowsIntegrableCriterion`) are the
  conclusions of the integrable-path theorems; the piecewise corollaries
  `IntegrablePathSimulation.BlockEncoding.simulation_piecewise` and
  `IntegrablePathSimulation.Coherent.coherent_windows_piecewise` restate the released theorems,
  whose criteria are `BECriterion` and `WindowsCriterion`. In `WindowsIntegrableCriterion` the
  final time `T` of the integrability range is a free parameter of the bound.
* Call forms are counted per call (a controlled or inverse value call counts as one value
  call), the native access of lines 2078-2082.
* `ξ`-tolerant gate level. `ApproxRealization` uses the full-output ancilla convention of the
  paragraph "Temporary ancillas" (lines 511-533): one fixed isometric encoding into a control
  qubit, a spectator register and the native space, residual ancilla state included; the case
  `ξ = 0` is exactly `NativeRealization`. The package's configuration-form notion
  `SparseHamiltonian.GateNative.ApproxOn` (one register) is not used, because the realised
  operation acts on a different space. The primitive-oracle cost is a fixed number `q` of value
  calls, independent of `ξ`, the cost notion of `NativeRealization`. The error is placed on the
  bare operation `D_x`; controlled and inverse calls inherit it through `masked_approx` and
  `approx_adjoint`. The manuscript places it on the controlled operation (lines 1805-1807); its
  hypothesis implies this one with the same program and count
  (`approxRealization_of_controlled`), and the controlled-form hypothesis is written inline, not
  as a new predicate. A negative `ξ` makes the hypothesis unsatisfiable.
* The error hypothesis of the `ξ`-tolerant forms is on the ideal circuit (exact private
  operations), at endpoint error `ε₀_F`; the executed circuit then has error at most
  `ε₀_F + nPriv_F · ξ_F` (`exists_approxProgram`), which is how Theorem `hs:thm:gates` adds up
  its errors (lines 1823-1835: `ξ = ε/(24d)` for at most `6d` private operations). Each family
  has its own `ε₀_F` and `ξ_F`; only `q` and the range error `ε` are shared. One encoding serves
  every private call, so ancillas are reused and errors add linearly. The manuscript states the
  gate model for time-independent Hamiltonians (line 1849); its use for the slot-selected
  time-dependent circuits extends lines 1513-1516. The nearest package parallels
  (`SparseHamiltonian.OracleCircuit.Program.eval_retarget_error` and
  `SparseHamiltonian.OracleCircuit.product_error_le` on one space, the module
  `ChebyshevLinearSystemFinite.GateApprox` with approximate known gates and exact oracles, and
  `SparseHamiltonian.GateNative.ApproxOn`) do not fit an encoding into a larger space, so the
  encoding facts are stated in `Tolerant/Approx.lean`.
* Piecewise Lipschitz paths. `LipschitzPath` carries per-piece `β_r` and `δ_r` with breakpoints
  at the mesh points, exactly the hypotheses of `simulation_lipschitz`, and `LipschitzGuarantee`
  is exactly its conclusion (`simulation_lipschitz_guarantee`, by unpacking). The uniform-mesh
  form with one `β` is the existing `TimeDependentHamiltonianLowerBound.uniform_class_max`.
  `LipschitzPath.meshPath` and `mesh_class_max_of_lipschitz` assume nondecreasing mesh points
  (every `IsMesh` mesh); `TimeDependentHamiltonianLowerBound.mesh_class_max` needs no
  monotonicity and stays the statement for arbitrary meshes, and `lipschitz_class_max` assumes
  no mesh hypothesis. The membership of the constant hard pieces (`β = δ = 0`, any breakpoints)
  is proved, not assumed. The Lipschitz modules use the namespace `Tolerant` of their directory.
* Measured algorithms act on the workspace of the oracle family itself, as in
  `DeferredMeasurementLowerBounds.Corollaries.main_max_measured_access`; the released families
  already carry their spectator registers. Accuracy is eq. `hsl:eq:accuracy` against every
  propagator of the constant path (equivalently against `exp(-iτH_x) ψ_in`,
  `TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff`); a measured algorithm has
  no output operator, so the program criteria (`UniformGuarantee`, `MeshCriterion`,
  `IntegrableCriterion`, `SelectCriterion`, `WindowsCriterion`, `BECriterion`) are not
  restated, and a selection run meets the accuracy on a branch of total duration `τ`. The
  hypotheses are those of the lifted theorems (`HSRange`, a unit initial vector, success at
  least `2/3`).
* One measured theorem covers each shared oracle family: `main_max_measured_mesh` the
  general-mesh and integrable-path simulators, `main_max_measured_select` duration and window
  selection (also `IntegrablePathSimulation.Coherent.coherent_windows`), and
  `main_max_measured_block` both block-encoding simulations.
* `Measured.NativeCompiles D O c` is a reduction certificate built from
  `AdaptiveHamiltonianLowerBound.Access.Admissible` and `MultiOracleCircuit.Program.cost`, the
  `Admissible` counterpart of `SparseLowerBounds.Hamiltonian.HsRelease.PhaseAccess` and of
  `Core.maskedAccess`, `Core.callAccess`. It contains `Admissible`
  (`nativeCompiles_of_admissible`): with `c = 1` and unit weights, `main_max_measured_compiled`
  is `DeferredMeasurementLowerBounds.Corollaries.main_max_measured`. `IsMaskedLift` contains
  `ODELowerBoundExtensions.Release.IsWrap` (`isMaskedLift_of_isWrap`) and the normal form of
  `TimeDependentHamiltonianLowerBound.admissible_of_normal_form` (`isMaskedLift_normal_form`),
  and also allows masks that leave branches untouched, as the controlled forms need.
* Compilation happens before deferral (`Measured.compile`): the compiled object stays a
  measured algorithm over admissible labels, the reverse order of
  `DeferredMeasurementLowerBounds.Access.compiledProgram` and of
  `ReleasedODESolverLowerBounds`, used because `BlockEncoding/Bound.lean` has no tree form. The
  uniform-mesh, general-mesh and selection families need no compilation. The block-encoding call
  is factorised through `SparseHamiltonian.NativeHermitianDilation.masked_swap` with `8` value
  calls (four in `W`, four in `W†`), consistent with the factor `8` of `main_max_block`; the
  bounds concern the block encodings `beConst D M` with `α_BE = s · scale` (lines 1553-1560) and
  are consistent with eq. `hs:eq:blockadditive` (line 1533) for that normalisation.
* The measured class contains the unitary programs over the same families
  (`DeferredMeasurementLowerBounds.Model.ofProgram`); the witness run `Measured.programRun`
  outputs the whole workspace, read through `SparseLowerBounds.Hamiltonian.endpointReadout`, so
  it needs a finite-dimensional workspace, which the released workspaces have, and it uses the
  plain implication of lines 2096-2097 (trace distance `ε`), not the sharp constant of
  `MeasuredUnitaryLowerBound.OperatorNorm.densityAccurate_of_normImplements`. The witnesses are
  stated on generic constant data, as the other non-vacuity modules of the library.
  `Measured.programRun` is the same construction as
  `MeasuredUnitaryLowerBound.OperatorNorm.runAll` (and `Measured.adjoint_one_comp_one` the same
  fact as `MeasuredUnitaryLowerBound.OperatorNorm.adjoint_one_comp_one`), restated so that this
  library does not depend on `MeasuredUnitaryLowerBound`.

**Not formalised.**

* Non-vacuity of the gate-level forms for a simulating private operation: `NativeRealization`
  and `ApproxRealization` are shown only for bare call forms of the native queries
  (`nativeRealization_call`, `Tolerant.approxRealization_call`, `q = 1`). The private operation
  `i · beOp D x`, padded by a fixed phase, is expected to meet the clock hypotheses of
  `gate_efficient_time_simulation` with boundary `beJ` and to be realisable with at most `8`
  value calls (not proved here); stating this needs a padded qubit layout of the native sparse
  space. The bridge from the conclusion of `gate_efficient_time_simulation` to
  `UniformGuarantee` is not stated either. The gate-level bounds, exact and `ξ`-tolerant, are
  therefore conditional on `NativeRealization` and `ApproxRealization`.
* A `ξ`-tolerant gate-level form whose accuracy hypothesis is on the executed (realised)
  circuit rather than on the ideal circuit plus `nPriv · ξ`; the `ξ`-tolerant form with the
  hypothesis on the ideal circuit is proved (`Tolerant.main_max_gate_tolerant`).
* A measured form of the gate-level bounds (exact or `ξ`-tolerant).
* The native gate-level model `SparseHamiltonian.GateNative` (`NativeOK`, `nCallsN`,
  `native_time_simulation`), whose primitives act on qubit registers.
* Adaptive forms of the block-encoding family stated by name. They would follow, for
  finite-dimensional workspaces and unitary oracles, from `Measured.main_max_measured_block`
  through `DeferredMeasurementLowerBounds.Model.ofTree`, `successMass_ofTree` and
  `worstCost_ofTree`; this is not stated here.
* The piecewise Lipschitz form of the time-dependent ODE argument (line 2916); the piecewise
  Lipschitz corollary for the Hamiltonian class is proved (`Tolerant.lipschitz_class_max`).
* A measured form over the aligned sampled family with any slot count and degree
  (`TimeDependentHamiltonianLowerBound.main_max_sampled`); only the released
  `SparseHamiltonian.TimeDependent.oracle` is covered. A non-vacuity witness for the measured
  runs of the windows simulators (`TimeDependentExtensions.Coherent.coherent_windows`,
  `IntegrablePathSimulation.Coherent.coherent_windows`).
* Lower bounds in block-encoding calls for block encodings of normalisation smaller than
  `s · scale` (the manuscript states none; its upper bound eq. `hs:eq:blockadditive`
  (line 1533) with `α_BE` smaller than `s · scale` would contradict such bounds for large `s`).
* Coherent selection of public parameters other than durations and start times (line 1506:
  "or other public parameters"); only durations (`SelectCriterion`) and windows
  (`WindowsCriterion`) are formalised.
* Family forms (`main_exists_*`, as `SparseLowerBounds.Hamiltonian.main_exists` and
  `AdaptiveHamiltonianLowerBound.main_exists_tree`) over the families of this library, and
  separate heralded forms (`Readout`) over them; the max forms are stated.
* Hard instances that vary in time (not claimed by the manuscript, which uses time-independent
  hard instances, lines 1514-1516).

**Provenance.** No result from another paper is used. The modules use declarations of the
libraries they import (`TimeDependentHamiltonianLowerBound`, `AdaptiveODELowerBound`,
`TimeDependentExtensions`, `GateEfficientTimeDependent` and their dependencies); no released
module is changed. The statement guide of `TimeDependentHamiltonianLowerBound` lists time-indexed
block encodings, coherent selection of durations and windows, the gate-level time-dependent
theorems and controlled calls of the released physical families as not formalised; this library
supersedes those items for the settings above (time-indexed block encodings for the released
block-encoding simulator, coherent selection for `TimeDependentExtensions.Coherent`, gate-level
circuits conditional on `NativeRealization`, all call forms of the uniform-mesh, general-mesh,
integrable-path and selection families, and the `ξ`-tolerant gate-level form, the piecewise
Lipschitz corollary and the measured forms over the released time-dependent oracle families),
while the items of the list above remain open. The statement guide of
`DeferredMeasurementLowerBounds` lists the measured forms over the released oracle families of
the time-dependent simulators as not formalised; they are proved in `Measured`. Line
numbers in this guide refer to the manuscript version accompanying this library; the guides of
the imported libraries cite an earlier numbering, and the paper labels are the stable
references.

**Audits.** `TimeDependentLowerBoundExtensions/Audit.lean` fixes the exact axiom report of every
theorem of the library and of every `Prop`-valued field of `Tolerant.LipschitzPath`.
-/
