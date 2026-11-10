import ODELowerBoundExtensions.Psd.Theorem
import ODELowerBoundExtensions.Homogeneous.Theorem
import ODELowerBoundExtensions.Padding.Combined
import ODELowerBoundExtensions.Release.Theta
import ODELowerBoundExtensions.Dyson.Family.Retry
import ODELowerBoundExtensions.Dyson.Corollaries

/-!
# Extensions of the dissipative-ODE lower bounds: paper-to-Lean entry point

Five further parts of Section `part:odel` of the accompanying paper are formalised here, on top of
the ODE lower-bound library `ODELowerBounds` (modules `SparseLowerBounds/ODE`): Theorem
`odel:thm:psd` (the constant-coefficient positive semidefinite precision lower bound), Proposition
`odel:rem:homogeneous` (the source-free variant of Theorem `odel:thm:joint`), the padding remarks of
the section (dense padding of the joint family to maximum sparsity exactly `s`, known zero padding
to any larger or qubit register, padding the three hard families of Theorem `odel:thm:combined` to a
common dimension), and the application of the lower bound to the released ODE solver with the
two-sided `Θ` bracket of `odel:thm:combined` against eq. `odel:eq:upper`, and Lemma `odel:lem:dyson`
(the fixed-parameter precision obstruction: a truncated Dyson-series solver, proved outright) with
eq. `odel:eq:fixed` and its consequence. The released libraries are unchanged; no result from
another paper is used. References to the manuscript use its labels.

Declarations are named relative to the namespace given with each item and paragraph below (one
namespace per directory of `ODELowerBoundExtensions/`); declarations of the released libraries
are named relative to `SparseLowerBounds.ODE` (the model `Family`, `Family.InClass`, `Solver`,
`Family.Forces`, `Family.Witnesses`, the hard families `jointFamilyAt`, `timeFamilyAt`,
`mixedFamilyAt`, `precisionFamilyAt`, `CombinedRange`, `combinedBound`, `combinedConst`) and
`SparseLowerBounds.Hamiltonian` (`HSRange`, `hsL`, `hsR`, `precN`, `HardInstance`), as in their
statement files. Throughout, `L = hsL ε = log(1/ε)`, `r = hsR τ ε = L/log(e + L/τ)` and
`n = precN τ ε`.

* Theorem `odel:thm:psd` (namespace `ODELowerBoundExtensions.Psd`, directory
  `Psd/`): family form `psd`, max form `psd_max`, the per-family witnesses `psd_search_witness`,
  `psd_scalar_witness` and the instance properties `psd_hardInstance`, `psd_family_hardInstance`.
* Proposition `odel:rem:homogeneous` (namespace
  `ODELowerBoundExtensions.Homogeneous`, directory `Homogeneous/`): `hom_witness`, with
  `homFamilyAt_src` (`b = 0`), `homFamily_g` and `hom_g_theta` (`g = Θ(ḡ)`) and
  `hom_instance_props` (dimension); the native form `hom_forces` and the reduction
  `outer_general`.
* The padding remarks (proof of Theorem `odel:thm:joint` and proof of Theorem `odel:thm:combined`;
  namespace `ODELowerBoundExtensions.Padding`, directory `Padding/`): `combined_pad`,
  `combined_max_pad`, `combined_pad_sparsityAttained`, `combined_common_dimension`,
  `combined_max_common_dimension`, `combined_qubit_register`, `exists_qubit_register`; for the joint
  family `joint_witness_dense`, `joint_witness_pad`, `jointDenseFamilyAt_props`,
  `joint_common_dimension`, `joint_qubit_register`; for the `g = 1` families `herald_witness_pad`,
  `herald_max_pad`, `precision_terms_witness_pad`.
* The released solver and the bracket (Section `odel:sec:main`; namespace
  `ODELowerBoundExtensions.Release`, directory `Release/`): Theorem `odel:thm:combined` for retry
  protocols `combined_retry`, `combined_max_retry`; on the released oracle
  `combined_max_release` (the analogue of `Hamiltonian.main_max_release`); the released solver
  on the hard class `exists_releaseProtocol`; the bracket `release_theta`,
  `release_theta_exists`, `release_theta_bracket` and `joint_release_theta` (the analogue of
  `Hamiltonian.release_theta`).
* Lemma `odel:lem:dyson`, eq. `odel:eq:fixed` and its consequence (namespace
  `ODELowerBoundExtensions.Dyson`, directory `Dyson/`): the general solver `dyson` with
  `dyson_release_class`, `certificate_queries_le` and `queries_fixed`; the bound function
  `dysonBound` with `dyson_fixed` and `eventually_lt`; on the lower-bound class `family_dyson`,
  `retrySolver_dyson`, `retry_fixed`, `no_uniform_lower_bound` and `no_retry_witnesses`.

**Theorem `odel:thm:psd`** (namespace `ODELowerBoundExtensions.Psd`).

* Range. `PsdRange τ s ε`: `s ≥ 32`, `τ ≥ 1`, `ε > 0` and `L ≥ 64τ` (so `ε ≤ 1/64`); it is
  `HSRange τ s ε` together with `L ≥ 64τ` (`PsdRange.toHSRange`, `PsdRange.of_HSRange`), and it
  contains the paper's range `τ ≥ 2` (`PsdRange.of_paper`).
* Families. The homogeneous equations `ẋ = -D_X x` on `[0, τ]` with one stage and
  `x(t) = heat D t x₀ = e^{-tD} x₀` (`heat_eq_evolve`, `heatFamily_solves`):
  `psdSearchFamilyAt h` (the gadget family on `SearchIndex n (psdMu s) s`, register size
  `2^{psdMu s}`, the largest power of two at most `(s - 1)/2`) and `psdScalarFamilyAt h` (the
  scalar family), for `h : PsdRange τ s ε`. The generator is
  `D_X = (I - H'_X)/2 ⊕ diag(0, 1) ⊕ 2^{-⌈log₂ s⌉} 𝟙𝟙ᵀ`, that is
  `fullMatrix (psdCore H'_X) s` in the convention of `SparseLowerBounds`, with `H'_X` the rounded
  spin chain of the Hamiltonian lower bound at `u = τ/2`.
* Instance properties (`psd_hardInstance`, `psd_family_hardInstance`, `psdSearchFamilyAt_props`,
  `psdScalarFamilyAt_props`): `Hamiltonian.HardInstance` (real symmetric, so `H = 0`; operator
  norm exactly one; row and column Euclidean norms at most one with maximum exactly one; maximum
  row and column sparsity exactly `s`; exact dyadic words with decode scale one;
  input-independent locators) and `D_X ⪰ 0` (`Matrix.PosSemidef`) at every input; `T = τ` and
  `1 ≤ g ≤ √2`.
* `psd_max` (max form): for any heralded solvers `AG` of `psdSearchFamilyAt h` and `AS` of
  `psdScalarFamilyAt h` at accuracy `ε` (any branch registers and garbage),
  `psdBound s τ ε ≤ max(Q_G, Q_S)`, `Q = labelCount .value`, with
  `psdBound s τ ε = psdConst (√(sτr) + r)` and `psdConst = log 2/(3072√2)`.
* `psd` (family form, eq. `odel:eq:psd`): for every `ḡ ≥ √2`, one of the two families
  `Witnesses τ ḡ ε (psdBound s τ ε)` (in the class with `η = 1`, `T = τ`, `g ≤ ḡ`, and forcing
  the bound on value queries and on all queries).
* `psd_search_witness`: for `s ≥ 512n/τ` the gadget family witnesses
  `psdGadgetConst √(sτr)`, `psdGadgetConst = log 2/(1536√2)` (proof of Theorem `odel:thm:psd`);
  `psd_scalar_witness`: the scalar family witnesses `r/32` (proof of Theorem `odel:thm:psd`).
* Proof. Both families compile to two Boolean queries per value call
  (`implementsOn_psdSearchData_spec`, `implementsOn_psdScalarData_spec`). The readout is the
  released `Readout.heralded_correlation` with the input-independent workspace observable, which
  gives a fair sign on failure; the imaginary-time amplitude `⟨n|e^{uB_n}|0⟩ = sinh(u/n)^n`
  (`heat_neg_spinMatrix_last`), hence the end amplitude `a = e^{-u} sinh(u/n)^n` of the
  unrounded chain at time `2u` (`heatEndAmp_spinWeight`), and the rounding comparison
  (`norm_heatEndAmp_psdWeight_sub_le`) give the signed correlation `psd_heralded_corr`
  (amplitude `a ≥ 8ε`). The gadget bound
  `psd_search_forces` (from `psd_search_forces_local`, eq. `odel:eq:psdmixedlocal`) and the
  scalar bounds `psd_scalar_forces`, `psd_scalar_forces_sqrt` are combined by `psd_assembly`;
  `psd` follows from `psd_max` by `ODE.forces_or_of_max`.

**Proposition `odel:rem:homogeneous`** (namespace `ODELowerBoundExtensions.Homogeneous`).

* Range. `HomRange s τ ḡ ε`: `s ≥ 4`, `ḡ ≥ 2`, `τ ≥ 20(1 + log ḡ)` and `0 < ε ≤ 1/64`;
  `n = homN τ = ⌊τ/π⌋`, and `M = jointM ḡ`, `μ = jointMu s` are those of `odel:thm:joint`.
* Family. `homFamilyAt s τ ḡ …` on `HomIndex M μ s = Bool × JointIndex M μ s` (a flag qubit
  times the joint index): `n` hidden stages of length `π/2`, a merged phase pulse `-|1⟩⟨1|` of
  length `((n + 2) mod 4) π/2` (`pulseLen`), a `Y` pulse of length `π/4`, a dissipative stage
  `D = P_reject` of length `log(4√M)` and a known idle stage, `K = n + 4` stages and `T = τ`; no
  source (`homFamilyAt_src`, `homFamily_src`) and `B = ‖x₀‖ = 1`.
* `hom_witness`: under `HomRange s τ ḡ ε`, `homFamilyAt` witnesses `homConst ḡ √s τ`,
  `homConst = 1/500`. `homFamily_g`: `(4/√17)√M ≤ g ≤ √M` at every input (Proposition
  `odel:rem:homogeneous`); `hom_g_theta`: `(4/√34) ḡ ≤ g ≤ ḡ`; `hom_instance_props`: `ḡ/√2 ≤ √M ≤ ḡ`
  and `|HomIndex M μ s| ≤ 6 ḡ² s`.
* `hom_forces` (native form): for `M ≥ 2` even, `n ≥ 1` and `2ε ≤ 15/17`, `homFamily` forces
  `β² n √(M 2^μ)/16`, `β = homCorr ε = (2/3)(15/17 - 2ε)`.
* `outer_general`: `SparseLowerBounds.ODE.joint_general` for an arbitrary target `ψ`, Hermitian
  contraction `D` and ideal signed correlation `a ≥ 2ε`: a heralded solver gives Boolean cost at
  least `((2/3)(a - 2ε))² n √(M 2^μ)/8`; `joint_general` is its instance `a = 1`.
* Proof. The access compiles to `hardCost` membership queries (`implementsOn_hom`); the half
  indicator `homHalfObs` of the candidate register has ideal correlation at least `15/17`
  (`homEnd_ideal_corr`), and `outer_general` with `hom_numeric` (`n ≥ τ/5`,
  `√(M m) ≥ ḡ √s/2`) gives the constant.

**Padding remarks** (namespace `ODELowerBoundExtensions.Padding`). Let `P`, `PJ`, `PM`, `PP` be
any finite types (known padding registers).

* Zero padding. `ZeroPad F' F` says that `F'` is `F` padded by known zeros: matrices
  `padMat P H = H ⊕ 0`, the same stage lengths, sources and initial state `v ⊕ 0`. It
  transfers `T`, `B`, `Solves`, `InClass` and `SparsityAttained` (`ZeroPad.T_eq`,
  `ZeroPad.mass_eq`, `ZeroPad.solves`, `ZeroPad.inClass`, `ZeroPad.sparsityAttained`), and
  `ZeroPad.heraldedAccurate`: a solver of `F'` read through the released
  `LowerBoundRemarks.HamiltonianPadding.padReadout P G i₀ ∘ out` is heralded-accurate for `F`
  with the same herald and the same `ε`.
* Sparsity. `SparsityAttained F`: at every input and stage some row and some column of the
  sampled matrix have exactly `s` nonzeros, the ODE analogue of
  `HardInstance.row_sparsity_attained` and `col_sparsity_attained`.
* Joint family. `jointPadFamilyAt s τ ḡ dense … P`: with `dense = true` the dense block
  `i 2^{-⌈log₂ s⌉} 𝟙𝟙ᵀ` (`Hamiltonian.padBlock s`) on the unoccupied `Fin s` block of
  `JointIndex M μ s` at every stage, with `dense = false` the plain zero padding of
  `jointFamilyAt` (`jointZeroPad_zeroPad`, `jointZeroPad_table`), padded by `P` in both cases;
  `jointDenseFamilyAt` is the dense family on `JointIndex` itself. `jointDenseFamilyAt_props`:
  sparsity exactly `s`, block norm at most one, dyadic entries, the unchanged solution
  `jointSol`, `D = 0`, dimension `2Mm + s`; `jointDenseFamilyAt_g`, `jointPadFamilyAt_g`:
  `g = √M ∈ [ḡ/√2, ḡ]`. `joint_witness_dense`, `joint_witness_pad` (under `JointRange`):
  `Witnesses τ ḡ ε (ḡ √s τ/400)`, and `joint_witness_pad` adds sparsity exactly `s` when
  `dense = true` (for the dense family, `jointDenseFamily_sparsityAttained`);
  `joint_forces_dense`, `joint_forces_pad`: the native constant `β² n √(Mm)/16` of
  `joint_forces`.
* `g = 1` families. `timePadFamilyAt`, `mixedPadFamilyAt`, `precisionPadFamilyAt` are
  `timeFamilyAt`, `mixedFamilyAt`, `precisionFamilyAt` padded by known zeros
  (`*PadFamilyAt_zeroPad`). `herald_instances_pad`: in the class, `T = τ`, sparsity exactly `s`;
  `herald_pad_props`: `b = 0`, generator `i(H ⊕ 0)`, `B = 1`, `‖x(τ)‖ = 1`. `time_forces_pad`,
  `mixed_forces_pad`, `precision_forces_pad`, `precision_forces_sqrt_pad`: the bounds of
  `time_forces`, `mixed_forces`, `precision_forces`, `precision_forces_sqrt` with the same
  constants and side conditions; `herald_max_pad`, `herald_witness_pad` (eq. `odel:eq:hsbound`,
  `c₀ = log 2/(4096π)`) and `precision_terms_witness_pad`.
* Combined. Under `CombinedRange s τ ḡ ε`, for any `dense` and paddings `PJ`, `PM`, `PP`:
  `combined_max_pad` (`combinedBound s τ ḡ ε ≤ max(Q_J, Q_M, Q_P)`) and `combined_pad` (one of
  the three padded families witnesses `combinedBound s τ ḡ ε = c (ḡ √s τ + √(sτr) + r)`,
  `c = log 2/(8192π)`); `combined_pad_sparsityAttained` (with `dense = true` all three have
  maximum sparsity exactly `s`).
* One common dimension. With `HamiltonianPadding.PadTo S Nd = Fin (Nd - |S|)`: for every `Nd` at
  least the three dimensions, `combined_common_dimension` and `combined_max_common_dimension`
  (each padded family has dimension exactly `Nd`, the sparsity facts hold, the joint one guarded
  by `dense = true`, and eq. `odel:eq:combined` holds in family and max form);
  `card_le_of_combinedDim`: every `Nd ≥ 3 ḡ² s` with `Nd ≥ 4 s (τ + r + 1)` qualifies.
  `combined_qubit_register` is the case `Nd = 2^q` and `exists_qubit_register` gives a threshold
  `q₀` for every `q ≥ q₀`; `joint_common_dimension` and `joint_qubit_register` (`3 ḡ² s ≤ 2^q`)
  are the joint family alone.
* Proof. There is no generic transfer of `Forces` along `ZeroPad` (see Not formalized); as
  `LowerBoundRemarks.HamiltonianPadding` does for `hsl:thm:main`, the hardness of each padded
  family is re-derived from its Boolean implementation (`implementsOn_stageData`,
  `implementsOn_jointDense`, `implementsOn_jointPad`) through `joint_general` and the heralded
  lemmas `Hamiltonian.time_herald_general`, `mixed_herald_general`, `precision_herald_general`,
  with the readout transfer `ZeroPad.heraldedAccurate`.

**The released solver and the bracket** (namespace `ODELowerBoundExtensions.Release`).

* Retry protocols. `RetrySolver F O E G ε`: a bounded fresh-trial protocol
  `prot : SparseHamiltonian.ODERepeatProtocol.Protocol O E` (the released solver's semantics:
  each attempt draws a uniformly random circuit label, prepares a fixed unit seed afresh, runs
  the circuit and measures the clean-output herald; the first success is decoded, finitely many
  attempts) over any labelled oracle family `O` on the inputs of `F`, an isometric readout
  `E → ℂ^N ⊗ G`, `successMass x ≥ 2/3` at every input, and for every solution a conditional
  output within trace distance `ε` of `x(T)/‖x(T)‖`
  (`AdaptiveHamiltonianLowerBound.DensityAccurate`). `RetryForces F ε b`: every retry solver
  over `F.access ι` (any `ι`, `E` finite-dimensional, `G`) has worst-case value count and
  worst-case total count at least `b` (`Protocol.worstCost`, over all transcripts, every attempt
  and failure branch and inverse calls counted). `RetryWitnesses F τ ḡ ε b`: in the class
  (`η = 1`, `T = τ`, `g ≤ ḡ`) and `RetryForces F ε b`.
* Containment. Every `Solver` is a one-attempt retry solver with the same counts
  (`solverToRetry`, `toRetry_worstCost`), so `retryForces_forces` and `retryWitnesses_witnesses`:
  `RetryWitnesses F τ ḡ ε b → F.Witnesses τ ḡ ε b`, with no hypothesis on the input set.
* `combined_max_retry`, `combined_retry`: under `CombinedRange s τ ḡ ε`, Theorem
  `odel:thm:combined` for retry protocols with the constant of `combined`; each disjunct of
  `combined_retry` implies the corresponding disjunct of `ODE.combined`. `herald_max_retry`,
  `herald_witness_retry`, `precision_terms_witness_retry`: eq. `odel:eq:hsbound` and the fourth
  sentence of `odel:thm:combined` under `HSRange` and `ḡ ≥ 1`;
  `joint_witness_retry`, `time_forces_retry`, `mixed_forces_retry`, `precision_forces_retry`,
  `precision_forces_sqrt_retry` are the components.
* On the released oracle. `meshOracle F σ ι N d J₀ J_b` is the physical oracle family of
  `TimeDependentExtensions.ODE.solver` run on `stageData F.data σ` for a placement
  `σ : Fin M → Fin K` of mesh pieces into stages; `releaseOracle F R …` is the uniform refinement
  `σ = stageOf K R`. `PublicSources J₀ J_b`: the source interfaces are unitary and input-independent
  (Section `odel:sec:main`). `combined_max_release`: for every public placement, any `ι`, slot
  counts and degrees and any retry solvers over `meshOracle` of the three hard families with public
  sources, `combinedBound s τ ḡ ε` is at most the maximum of the value counts
  `worstCost (matrixWeight valueWeight)` and at most the maximum of the matrix counts
  `worstCost (matrixWeight (fun _ => 1))`; `joint_release`, `mixed_release`, `precision_release` are
  the components.
* The released solver on the hard class. `exists_releaseProtocol`: on a class family with
  `D = 0` and `T = τ`, for any unit seed and any unitary `J₀`, `J_b` meeting the premises of
  `TimeDependentExtensions.ODE.Outcome`, `TimeDependentExtensions.ODE.solver` gives a
  `ReleaseProtocol` with `Θ = τ`, `ℓ = releaseLog ḡ ε = log(40000 ḡ/ε)` and `g = 2ḡ`.
  `ReleaseRun F τ ḡ ε` is a release-form run
  (refinement `R > 0`, slots, a degree for which the certificate holds, public sources, the
  four-attempt protocol and the released complete certificate for every input), with
  `matrixQueries` and `valueQueries` (`ReleaseRun.valueQueries_le`).
* `release_theta`: under `CombinedRange s τ ḡ ε`, for release runs `AJ`, `AM`, `AP` on
  `jointFamilyAt`, `mixedFamilyAt`, `precisionFamilyAt`, with `S = ḡ √s τ + √(sτr) + r`,
  `ℓ = releaseLog ḡ ε` and `Q`, `V` the matrix and value counts:
  `c S ≤ max(Q_J, Q_M, Q_P) ≤ 2548039680 ḡ (√s τ + √(sτℓ) + ℓ) ≤ 7644119040 ℓ S`, the middle
  term (eq. `odel:eq:refined` at `Θ = τ`) is at most `7644119040 ḡ √s τ ℓ` (the `O(ḡ √s τ ℓ)`
  form of eq. `odel:eq:upper`), `c S ≤ max(V_J, V_M, V_P)` and
  `max(V_J, V_M, V_P) ≤ max(Q_J, Q_M, Q_P)`. `release_theta_exists`: such runs exist on
  `CombinedRange`; `release_theta_bracket`: runs exist that satisfy all six conjuncts.
  `joint_release_theta`: under `JointRange` and `ℓ ≤ τ`, every release run on the joint family
  has `ḡ √s τ/400 ≤ Q_J ≤ 7644119040 ḡ √s τ` (Section `odel:sec:main`).
* Proof. The joint bound uses an explicit lossless purification of all attempts in the
  coordinates of a finite-dimensional workspace (`exists_purification`) and the additive
  adversary along the protocol (`retry_decision_count_ge`, `outer_count_ge_retry`), so the
  constant `1/400` is unchanged; the `g = 1` bounds come from the released adaptive tree bounds
  `AdaptiveHamiltonianLowerBound.time_tree`, `mixed_tree`, `precision_tree` applied to
  `Tree.final` of the protocol (`retryForces_of_tree`). The released oracle is brought to the
  normal form `U⁻¹ (1_Ω ⊗ A) U` (`physicalOracle_normal_form`), the only interface to it. The
  upper half is `ODECompleteTrial.Certificate.matrix_queries` on the uniform refinement
  (`refine_quadrature`), with integrated sample errors exactly `0`.

**Lemma `odel:lem:dyson`** (namespace `ODELowerBoundExtensions.Dyson`). Throughout,
`z = s Λ T` with `Λ = D.scale` the public entry bound (the lemma's row and column Euclidean-norm
bound `η` implies the entry bound `Λ = η`; `rate D = s Λ`),
`L_g = dysonLog ḡ ε = log(4000 ḡ/ε)` (the paper's unspecified `C` is `4000` here; the bracket of
the released solver above uses `Release.releaseLog ḡ ε = log(40000 ḡ/ε)`, so the two constants
differ), and `dysonBound z ḡ ε = 16000 ḡ e^z (1 + z + L_g/log(e + L_g/z))` (eq. `odel:eq:dyson`).

* Degree and tail (`Degree`; eq. `odel:eq:degree`). `expTail z K` is the tail
  `∑_{k>K} z^k/k!` (`hasSum_expTail`); `expTail_le`: for `z ≥ 0` and `K + 2 ≥ 2z` it is at most
  `2 z^{K+1}/(K+1)!` and at most `2(ez/(K+1))^{K+1}`. The public degree is
  `K = truncDegree z ḡ ε = ⌈e² z + 4 L_g/log(e + L_g/z)⌉₊`; `expTail_truncDegree_le`: the tail is
  at most `ε/(2000 ḡ)` (`z > 0`, `ḡ ≥ 1`, `0 < ε ≤ 1`); `truncDegree_le`:
  `K ≤ e² z + 4 L_g/log(e + L_g/z) + 1`; `cost_le_dysonBound`:
  `2160 ḡ m K ≤ dysonBound z ḡ ε` whenever `m ≤ e^z`.
* Input class and conclusion (`Theorem`). The data are `D : Data (X × Fin Ks) n Z s`, a public
  mesh `t` with `M > 0` cells and `IsMesh t M T`, and a public cell-to-sample map
  `σ : Fin M → Fin Ks`; `T > 0`, `ḡ ≥ 1`, `0 < ε ≤ 1`, `r₀ ≥ 0`, `r_b ≥ 0`,
  `B = MeshSampling.mass r₀ t r_b > 0`, unitary source interfaces `J₀`, `J_b` and a unit seed.
  `Outcome D σ t T ḡ ε r₀ r_b J₀ J_b seed` has two parts: the shape bound
  `1274019840 g' · queryShape s 0 ℓ = 2160 g' K ≤ dysonBound z ḡ ε` (`shape_eq`), with
  `g' = ampFactor = ḡ · lcuMass/B ∈ [ḡ, ḡ e^z]` and `ℓ = shapeLength = K/589824`; and one public
  unitary trial family `q`, seed `ψ` and output map `F` over the Dyson access `oracle` such that
  `ODECompleteTrial.Certificate q (chosenIterations g') ψ F x (sol T) s 0 ℓ g' ε` (success at
  least `2/3`, conditional density within trace distance `ε` of `x(T)/‖x(T)‖`) for every valid
  instance: accretive generator pieces `G_r(u)`, accretive used samples
  `matrixOperator (D.matrix (x, σ r))`, integrable pieces with `‖b_r(u)‖ ≤ b_max`, a solution on
  each cell, source interfaces matching the initial value and the source samples,
  `B ≤ ḡ ‖x(T)‖`, and the released integrated certificate with constant `2000`:
  `(r₀ + b_max T) ∑ ∫‖G - G̃‖ + ∑ ∫‖b - b̃‖ + s Λ ∑ Δ_q² r_{b,q}/2 ≤ ε B/(2000 ḡ)`.
* `dyson` (Lemma `odel:lem:dyson`): under these hypotheses,
  `Outcome D σ t T ḡ ε r₀ r_b J₀ J_b seed`.
* `dyson_release_class` (the text after eq. `odel:eq:fixed`): for the data
  shape of `TimeDependentExtensions.ODE.solver` (`Ks = M`, `σ = id`), under `dyson`'s hypotheses and
  the release's public PSD promise on the sampled dissipative parts, at any slot count `N`, the
  shape bound holds and one public trial family satisfies the released complete certificate for
  every instance satisfying the premises of the released `TimeDependentExtensions.ODE.Outcome`,
  copied verbatim (including `sol T ≠ 0` and the error budget `publicError D t T N r₀ r_b`, which
  dominates the Dyson quadrature term by `quadrature_le_publicError`). None of the release's energy
  bounds, slot conditions or conditions on `N` is assumed.
* `certificate_queries_le` (eq. `odel:eq:dyson` for `Q_A`): given `Outcome`, every released
  complete certificate with the Dyson parameters (`Θ = 0`, `ℓ = shapeLength`, `g' = ampFactor`),
  over any trial family and oracle type, has
  `worstCost (matrixWeight (fun _ => 1)) ≤ dysonBound z ḡ ε`.
* Eq. `odel:eq:fixed`. `dyson_fixed`:
  for `z > 0` and `ḡ ≥ 1` there are `C` and `0 < ε₀ < 1` with
  `dysonBound z ḡ ε ≤ C log(1/ε)/log log(1/ε)` for all `0 < ε ≤ ε₀`. `queries_fixed`: such `C`, `ε₀`
  bound the worst-case matrix queries of every certificate with the Dyson parameters on every input
  with `rate D * T = z` satisfying `Outcome`.
* The lower-bound class (`Family/`). `family_dyson`: every `Family F` with `F.InClass η ḡ`,
  `η > 0`, `F.T > 0`, `ḡ ≥ 1` and `0 < ε ≤ 1` has public programs over
  `ODESourceQueryBudget.oracle (F.access ι) (fun _ _ => 1)` (idle source vocabulary) satisfying
  the released `Certificate` on every input, with
  `1274019840 g' · queryShape s 0 ℓ ≤ dysonBound (s η T) ḡ ε`. `retrySolver_dyson`: under the
  same hypotheses, some `ι` and `A : Release.RetrySolver F (F.access ι) ℂ^N ℂ^N ε` with
  `A.prot.worstCost (fun _ => 1) ≤ dysonBound (s η T) ḡ ε` (all labels counted, inverse calls
  included). `retry_fixed`: for every `s`, `τ > 0` and `ḡ ≥ 1` there are `C` and `0 < ε₀ < 1`
  such that for all `0 < ε ≤ ε₀` and all `η > 0`, every `F` with `F.InClass η ḡ` and
  `F.T η = τ` has such a retry solver with worst case at most `C log(1/ε)/log log(1/ε)`.
* The consequence (the text after eq. `odel:eq:fixed`). `eventually_lt`:
  for `s, τ > 0`, `ḡ ≥ 1` and `c > 0` there is `ε₀ > 0` with
  `dysonBound (sτ) ḡ ε < c ḡ √s τ log(ḡ/ε)` for all `0 < ε ≤ ε₀`. `no_uniform_lower_bound`: with the
  threshold `ε₀` uniform in `η > 0`, every family of the class `InClass η ḡ` with `T η = τ` has a
  retry solver with fewer than `c ḡ √s τ log(ḡ/ε)` queries. `no_retry_witnesses`: for all
  `0 < ε ≤ ε₀` and every `F : Family X N Z K s`,
  `¬ Release.RetryWitnesses F τ ḡ ε (c ḡ √s τ log(ḡ/ε))`. No `s > 0`, `B > 0` or `DecidableEq Z` is
  assumed. This is consistent with `Release.combined_retry`, whose bound `c (ḡ √s τ + √(sτr) + r)`
  has no logarithm on the `ḡ √s τ` term.
* Proof map. `Access`: the masked coherent sampled-time native access, built on the release's
  `SparseHamiltonian.TimeDependent.timeOracle` of `NativeSparseMaskedAccess.flatOracle D`, gives
  an exact block encoding of `G̃_r/(s Λ)`, `G̃_r = D.matrix (x, r)` the sampled generator
  (`−A(t_r)` in the paper's convention `ẋ = A x + b`), with six coherent queries
  (`slot_compression`, `matrixOperator_eq_smul`). `Flagged`: one flag bit per slot with a known
  flag split compresses a product of slot operators exactly (`flagged_compression`). `Series`:
  occupation-number configurations `Cfg` (`c : Fin M → Fin (K + 1)`, `∑ c ≤ K`) with
  coefficients `coef` (`sum_coef_le_exp`: mass at most `e^z`) give the truncated product
  `truncated` with error `truncated_error`; `Slots` places the slots of a configuration on the
  cells (`slot_product`). `Select`, `Compile`: the LCU select over configurations and branches
  (`select_compression`; `select_count`, `select_cost`: `18K` native matrix calls per
  application, independent of the mesh). `Target`: the source branches starting at mesh cells
  with the release's left-endpoint quadrature, coefficient mass `lcuMass`
  (`mass_le_lcuMass`, `lcuMass_le`: `B ≤ lcuMass ≤ B e^z`) and the error `lcuTarget_error` (with
  the mesh comparison `mesh_selected_error`). `Herald`, `Trials`: the herald bounds and the
  released amplification and four-attempt wrapper (`certificate_of_herald`). `Family/`: the ODE
  lower-bound access is the Dyson access up to fixed spectators (`familyLayout_matrix`,
  `oracle_inr`, `certificate_transport`), the data are clipped to `Λ = η` by the release's
  `NativeBandEncoding.tail` (`tail_matrix_of_le`), public sources become known gates
  (`sourceFreeProgram`, `exists_sourceFree`), and `Release/Strip` removes the idle source
  vocabulary from protocols (`Release.stripIdle`, `Release.mapProtocol`,
  `Release.certificate_densityAccurate`).

Every theorem of the library and every `Prop`-valued field of its structures is axiom-audited
in `ODELowerBoundExtensions/Audit.lean`.

**Formalization choices.**

* Base and solver class. The library builds on the released package and changes none of its
  Lean modules; the released definitions (`Family`, `Solver`, `Forces`, `Witnesses`, the hard
  families, `Readout.HeraldedAccurate`, `PadTo`, `padReadout`, the release solver and protocol
  types) are reused, not redefined. The class for the released solver is the release's own retry
  protocols (`ODERepeatProtocol.Protocol`), which contain every `Solver` and every run of the
  released solver, and not full adaptive trees or purified protocols. The remaining choices are
  recorded below.
* `odel:thm:psd`. The range is `τ ≥ 1` (the paper: `τ ≥ 2`; no step uses more). The parameters are
  those of the Hamiltonian lower bound (`n = ⌊r/4⌋`, `u = τ/2`; `half_tau_le_precN`). The dense PSD
  padding is always present (the paper: "when required", proof of Theorem `odel:thm:psd`), so both
  families have maximum sparsity exactly `s`; the unpadded sparsities `2m + 1` and `3` are facts
  about the core matrices (`card_row_psdSearchCore_le`, `card_row_psdScalarCore_le`). The rounding
  step is fixed to `δ = min(1/(2√n), a/(16u))`. The scalar bound `r/32` is stated for the padded
  family under `PsdRange` (so for `s ≥ 32`). The paper's strict `Q > √(sτr)/256` for `s < 512n/τ` is
  stated with `≥` (`psd_scalar_forces_sqrt`). The families take a range proof `h : PsdRange τ s ε`,
  in the style of `timeFamilyAt`.
* `odel:rem:homogeneous`. The paper's phase pulse (`(n mod 4) π/2`) and `Z` pulse are merged
  into one `-|1⟩⟨1|` stage of length `((n + 2) mod 4) π/2`; with the `Y` pulse this is exactly
  the Hadamard, so the family equals the paper's up to the global phase `-i` on `x(T)`, which
  changes neither normalised targets nor correlations, and the known pulses take less time. The
  literal three-pulse family is realisable in `NativeSparseBlockEncoding.Data` but not
  constructed. The locators depend on the stage but not on the input
  (`homData_locators_input_indep`); this is forced when `s` is a power of two and widens the
  premise of the controlled-locator argument of `ODE/Model` (input- and stage-independent
  locators), which still applies because the time address is a workspace register. The decision
  observable is the half indicator of the candidate register, so `β` and the constant
  `c_H = 1/500` are smaller than `c_J = 1/400`. `outer_general` generalises `joint_general` in
  its own module; `Homogeneous/Compile` follows the released `JointCompile` for stage-indexed tables
  and parallels `Padding/StageCompile`, which is fixed to `n + 2` stages.
* Padding. The dense block sits on the existing unoccupied `Fin s` block of `JointIndex` (proof of
  Theorem `odel:thm:joint`), so the dimension stays `2Mm + s` and the locators are unchanged.
  `2^{-⌈log₂ s⌉}` needs words of length `B = Hamiltonian.padExp s`; the padded joint data take a
  general word length `B ≥ μ` (`jointPadBits`), and with `dense = false` keep the words of
  `jointFamilyAt`. The dense block is added at every stage; on the idle and source stages its words
  are added by a fixed gate, with no query. The class needs only `dense = true → s ≤ 4^B` (row
  norms); the operator norm bound `norm_denseHam_le` needs `s ≤ 2^B`. The table-generic Boolean
  implementation (`stageBitFamily`, `stageBoolean`, `stageTableGate`, `stageData`) generalises the
  released `JointCompile` and agrees with it at `jointTable` (`stageBitFamily_jointTable`,
  `stageBoolean_jointTable`, `stageTableGate_jointTable`). "Dimension exactly `Nd`" means
  `Fintype.card (X ⊕ PadTo X Nd) = Nd`, as in `HamiltonianPadding`.
* Retry protocols. Counts are worst cases over all transcripts, every attempt, failure branch and
  inverse call counted; source-interface calls are free in the lower bound (Section
  `odel:sec:main`). Accuracy is the observable form of trace distance through an isometric readout
  with garbage; the release's `hermitianTraceDistance ≤ ε` is converted through the clean readout
  `Hamiltonian.endpointReadout 1 i₀`. The bridge and the bracket assume public source interfaces
  (`PublicSources`); this is necessary, since an input-dependent source interface would leak the
  hidden input, and the released choice satisfies it (`releaseSources_public`). The lower bounds on
  the released oracle hold for every public placement `σ`; uniform refinement is needed only for the
  upper-bound arithmetic, and is forced by the fixed `Δ² r_b` term of `publicError` on the joint
  family's unit-length source stage. The paper's unspecified constant `C > 1` in `ℓ = log(C ḡ/ε)` is
  the release's `40000`. The bracket is on the maximum over the three families, in the matrix count
  bounded by `Certificate.matrix_queries`, with the value count as a further conjunct.
* `odel:lem:dyson`: scope and access. The lemma is proved outright as an upper-bound algorithm
  in the release's ODE model and stated as a release-style retry protocol
  (the four-attempt `ODECompleteTrial.Certificate`), so it lies in the retry class of `Release`;
  no single-program `Solver` form is given. The access is the release builder
  `ODECoordinateNativeControl.physicalOracle` (also used by `MeshSource.physicalOracle`) with the
  supplied sources `TimeDependentODE.SourceTD.sourceFamily J₀ J_b` and, as matrix access, the
  masked coherent sampled-time native access `NativeMaskedProgram.oracle` of the release's
  `SparseHamiltonian.TimeDependent.timeOracle` (no local copy of the time register), not the
  release's aligned Cayley access `MeshSource.matrixOracle`. Idle slots of low-degree
  configurations use three native calls per call, so one LCU application costs `18K` native
  matrix calls and the query budget has zero slack (`10 · 18K = 106168320 K/589824`).
* `odel:lem:dyson`: input class. Mesh cells are public refinements of the data samples through
  `σ : Fin M → Fin Ks` (the paper's reversible cell-to-sample map, proof of Lemma `odel:lem:dyson`),
  with the data and certificate shape of `TimeDependentExtensions.ODE.solver`. Accretivity is a
  per-instance hypothesis on the samples actually used, weaker than the release's public PSD promise
  on all data (the formal restriction of `ode:thm:time` stated in `TimeDependentODE/Statements.lean`).
  The normalisation is `α = s Λ` with `Λ = D.scale`; on the lower-bound class the data
  are clipped to `Λ = η` by the release's own `NativeBandEncoding.tail` (same oracles), which
  changes nothing under the class's row-norm bound (`tail_matrix_of_le`). The certificate is the
  release's integrated one with constant `2000`, without the slot-refinement term `M (T/N) B` (the
  Dyson solver needs no uniform slots); `quadrature_le_publicError` shows that the release's
  `publicError` dominates it.
* `odel:lem:dyson`: source access. The proof of the lemma uses the general source interface of
  eqs. `ode:eq:source-interface-mass` and `ode:eq:source-interface-preparation` (complex
  quadrature coefficients through supplied phases, `B_q ≤ c_q B`); here the sources are those of
  the released time-dependent solver (public norms of the initial state and of one forcing
  sample per cell, unitary direction interfaces, the positive left-endpoint cell quadrature with
  `B ≤ ḡ ‖x(T)‖` imposed on its mass), the case of positive weights without phases. The lemma for
  the general interface is in `DysonFullClass`, with this package's label-controlled loading and
  a classical propagator on each closed mesh cell.
* `odel:lem:dyson`: construction. The paper's sorted i.i.d. cell labels and multinomial weights
  (proof of Lemma `odel:lem:dyson`) are replaced by occupation-number configurations
  `c : Fin M → Fin (K + 1)` with `∑ c ≤ K`, which give the same operator identity without
  multinomial counting; label preparation and the cell of each slot are known gates. Fresh encoding
  ancillas are one flag bit per slot with a known flag split, an exact compression for arbitrary
  slot operators. The amplitude is kept at most `1/2` by a cancelling padding pair
  `±(w_q · branchMass_q)/2` per source branch (identity operator), which doubles the coefficient
  mass and leaves the selected sum unchanged. Source branches start at mesh cells with the release's
  left-endpoint quadrature (`meshRecurrence`); the attenuation `((T - u)/T)^k` of the proof is the
  mask of the cells before the branch start. The exponential series is the package's
  `SparseHamiltonian.GeneralODE.ExpBounds.real_exp_hasSum`.
* `odel:lem:dyson`: constants. `C = 4000` in `L_g` (`dysonLog`), `K = truncDegree`,
  `g' = ampFactor ∈ [ḡ, ḡ e^z]`, `ℓ = K/589824`, and the released shape at `Θ = 0`
  (`queryShape s 0 ℓ = ℓ`, `s` the data sparsity as in the release), which absorbs the fixed
  constants `106168320`, `318504960` and `1274019840`; the final count is `2160 g' K`. The
  release bracket's `ℓ = log(40000 ḡ/ε)` is a different constant; no common `C` is used.
  `expTail_le` keeps both displayed tail inequalities.
* `odel:lem:dyson`: layers and counts. `family_dyson` states the released `Certificate` over
  `ODESourceQueryBudget.oracle (F.access ι) (fun _ _ => 1)`, since the certificate needs
  `Query ⊕ Bool` labels; the source vocabulary there is idle, and `Family/Retry` removes it
  (`Release.stripIdle`, `Release.mapProtocol`) and reads the output through
  `Hamiltonian.endpointReadout 1 i₀` (`Release.certificate_densityAccurate`, the oracle-generic form
  of which `Release.ReleaseProtocol.accurate` is the instance on `releaseOracle`). The retry
  statements count every label with `worstCost (fun _ => 1)`, inverse calls included, a stronger
  count than the paper's matrix queries; the general-class statements count matrix queries with
  `matrixWeight (fun _ => 1)`. `family_dyson` assumes no `B > 0` (`mass_pos_of_inClass`: every class
  family with an input has `B > 0`, which also discharges the hypothesis `0 < F.mass` of `Release`
  whenever `X` is nonempty). Eq. `odel:eq:fixed` is stated for the bound (`dyson_fixed`), for the
  general solver (`queries_fixed`, through `certificate_queries_le`, generic in the certificate's
  oracle type) and uniformly over the lower-bound class (`retry_fixed`, with `C`, `ε₀` depending
  only on `s`, `τ`, `ḡ` and the binder `∀ η > 0` after them, as in eq. `odel:eq:fixed`). The
  consequence is stated for the bound (`eventually_lt`),
  for the class (`no_uniform_lower_bound`) and in the package vocabulary (`no_retry_witnesses`, with
  `η = 1` as in `RetryWitnesses` and `Family.Witnesses`).
* `odel:lem:dyson`: transport. Two transport forms between the ODE lower-bound access and the
  released physical oracle coexist: `Release.physicalOracle_normal_form` and
  `Release.physicalOracle_inr_const` (with `PublicSources`), and `Dyson.familyLayout_matrix` and
  `Dyson.oracle_inr` (constant source interfaces, the special case reached through
  `Release.releaseJ₀` and `prepUnitary`). Together they supersede, for the oracle of the
  general-mesh solver `TimeDependentExtensions.ODE.solver`, the sentence of
  `SparseLowerBounds/ODE/Model` and its statement guide that there is no Lean transport between
  the two forms; that module is unchanged, and the constant-coefficient solver of `ode:thm:main`
  is not bridged. The generic retry-class helpers (`stripIdle`,
  `mapTrial`, `mapProtocol`, `certificate_densityAccurate`) sit in `Release/Strip.lean`, used by
  both `Release/Instances` and `Dyson/Family/Retry`.
* Names. The short names `mixed_release`, `precision_release`, `release_shape_le` and
  `release_theta*` repeat those of `SparseLowerBounds.Hamiltonian` and are cited with the
  `ODELowerBoundExtensions.Release.` prefix; `solverToRetry` is not named `Solver.toRetry`, since
  dot notation on `SparseLowerBounds.ODE.Solver` would not reach this namespace.
  `Padding.stageData` and `Release.stageData` share a short name in different namespaces. The
  generic names of `Dyson` (`oracle`, `select`, `encoding`, `matrixOracle`, `mass_nonneg`,
  `zero_solves`, `eventually_lt`, ...) are cited with the `ODELowerBoundExtensions.Dyson.`
  prefix outside this guide; its decidable-equality instance on the workspace is scoped to the
  namespace. The one global instance, `Release.heraldSpace_completeSpace`, is the completeness
  of a solver's success subspace (a `Prop`).
* Known duplicates, kept for module weight and elaboration time: `Psd.oneStageData D` is field
  for field `Release.reindexData D Prod.fst` (kept so that `Psd` does not import
  `Release/Refine` and with it `TimeDependentExtensions.ODE.Sampling`);
  `Release.comp_isometry` restates `SparseHamiltonian.UnitaryDilationTransfer.comp_isometry`
  (outside the import closure of `Release/Access`; importing it caused heartbeat timeouts); the
  proof of `Homogeneous.outer_general` follows that of `joint_general`; and
  `Homogeneous/Compile` parallels `Padding/StageCompile`. The small helpers
  `Dyson.norm_pow_le_norm_pow`, `Dyson.opNorm_eq_zero_of_subsingleton` and
  `Dyson.hasDerivWithinAt_Icc_self` sit next to the package's
  `SparseHamiltonian.GeneralODE.ExpBounds.norm_pow_le_pow` and Mathlib's `norm_pow_le'`;
  `norm_pow_le_norm_pow` generalises the former to `n = 0` on a possibly trivial space (no
  `NormOneClass`).
* Guide length. This guide covers five groups of results in one entry point and is longer than
  the ~400 lines of a module of the package (the longest earlier guide,
  `SparseLowerBounds/Hamiltonian/Statements.lean`, has 342 lines); it is kept as one file,
  since the package has no per-topic sub-guide inside one library, so that every result is read
  from one entry point.

**Not formalized.**

* For `odel:lem:dyson`: the literal sorted i.i.d. label sampling and multinomial counting of
  the proof (replaced by configurations with the same operator identity); a
  single-program `Solver` form of the Dyson algorithm (and with it a refutation of a uniform
  bound for the single-program `Forces`/`Witnesses` class alone, since `RetryForces → Forces`
  holds in one direction only); the Lipschitz mesh example `(1/2) ∑ L_j h_j²` of the lemma's
  discussion (the mesh enters only through the integrated certificate); gate counts and
  time-register costs (all gates are known gates, only queries are counted); and the discussion
  after eq. `odel:eq:fixed` (the constant-coefficient remark and the absence of a joint
  large-parameter comparison).
* For `odel:thm:psd`: the unpadded families (gadget family of sparsity at most `2m + 1`,
  three-sparse scalar family) as separate families, the scalar bound for `s < 32`, and the
  discussion after the theorem (no constant-error `Ω(√s τ)` bound for the
  dissipative constant-coefficient subclass, the necessity of the factor `ℓ` multiplying `τ_D`
  in eq. `odel:eq:refined`, a linear power of `L` in the sparsity-dependent dissipative cost).
* For `odel:rem:homogeneous`: the literal three-pulse flag sequence.
* Retry-protocol and released-oracle forms of Theorem `odel:thm:psd`, Proposition
  `odel:rem:homogeneous` and the padded families: these are stated for
  `SparseLowerBounds.ODE.Solver` only, for which, as in the released library, no lemma exhibits a
  solver of the hard families (the retry forms are non-vacuous: `Dyson.retrySolver_dyson`).
* A generic transfer of `Forces` from a zero-padded family to the original family: a padded
  value call on a padding address cannot be routed through one call of the original access
  without controlled calls, which `MultiOracleCircuit.Program` does not have; hardness is
  re-derived for each padded hard family instead. No assertion is made below a family's
  dimension (Section `odel:sec:main`). The common-dimension padding is not combined with the retry
  class or the bracket.
* Controlled oracle calls: covered by the documented reduction of the **Controlled calls**
  paragraph of `ODE/Model` only, which has no Lean lemma.
* The released solver: the constant-coefficient released solver
  `SparseHamiltonian.ODECompleteEndpoint.solver` (Theorem `ode:thm:main`) is not connected, only the
  general-mesh solver of `ode:thm:time`, which covers the same hard families; runs on meshes that
  cut across stage boundaries or with nonzero integrated sample errors; runs with input-dependent
  source interfaces; a release-oracle analogue of `time_release` (the joint family carries the time
  term, as in `combined_max`); the Boolean-cost conjunct of `Hamiltonian.release_theta`. For the
  joint family the retry class excludes general adaptive trees and purified protocols. The two-sided
  comparison at the end of Section `part:odel` beyond the bracket above.
* Gate, workspace and classical circuit-generation costs.

**Provenance.** These modules are an external development of the same origin as the ODE lower
bounds, written against the released package and added here: `Psd/`, `Homogeneous/`, `Padding/`,
`Release/` and `Dyson/`. No released Lean module was changed.
`SparseLowerBounds/ODE/Statements.lean` predates this library and lists Theorem `odel:thm:psd`,
Lemma `odel:lem:dyson` with eq. `odel:eq:fixed` and its consequence, Proposition
`odel:rem:homogeneous`, the padding remarks, the comparison with the upper bounds, the application
to the released ODE solvers and adaptive solvers as outside it; its note that there is no Lean
transport between the lower-bound access and the released solvers' flattenings no longer applies
(`Release.physicalOracle_normal_form`, `Dyson.familyLayout_matrix`).
-/
