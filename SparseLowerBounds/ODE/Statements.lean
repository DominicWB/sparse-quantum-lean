import SparseLowerBounds.ODE.Theorem
import SparseLowerBounds.ODE.Uniqueness

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Dissipative-ODE query lower bounds: paper-to-Lean entry point

Theorem `odel:thm:combined` of the accompanying paper (the combined
worst-case lower bound for the time-dependent dissipative ODE class, the row
"Dissipative ODE" of Table 1, Section `odel:sec:main`, manuscript lines
3654-3953, proof completed at lines 4001-4009) is formalized in
`SparseLowerBounds/ODE/Theorem.lean`: the headline family form is
`SparseLowerBounds.ODE.combined` and its quantitative core, the max form, is
`combined_max`. Its ingredients are Lemma `odel:lem:outer` (`outer_count_ge`,
`ODE/JointAdversary.lean`), Theorem `odel:thm:joint` (`joint_witness`,
`joint_forces`, `joint_general`, `ODE/JointTheorem.lean`) and Lemma
`odel:lem:herald` read in the ODE model (`herald_witness`, `herald_max`,
`precision_terms_witness`, `ODE/Precision.lean`). All declarations named below
without a namespace are in `SparseLowerBounds.ODE`; the generic adversary is in
`SparseLowerBounds.PositiveAdversary`. No result from another paper is used.
Line numbers refer to the manuscript version used by the Hamiltonian lower
bound (Theorem `hsl:thm:main` at line 2102, Section `part:odel` at line 3654);
in the current manuscript these sections are unchanged and shifted by 277 and
287 lines. The labels are the stable references.

**The class** (`ODE/Model.lean`, lines 3655-3688). The equation
`ẋ = A(t) x + b(t)`, `-A = D + iH`, `D ⪰ 0`, is written in the release's
convention `ẋ = -G(t) x + b(t)` with generator `G = -A`. A `Family X N Z K s`
has `K` public stages of lengths `len k ≥ 0` (breakpoints `start k`,
`T = start K`), the sampled-time sparse input
`data : NativeSparseBlockEncoding.Data (X × Fin K) N Z s` whose matrix
`data.matrix (x, k)` is the stage generator `G_k(x)` (row and column sparsity
at most `s` are built into `Data`: `Family.row_sparsity_le`,
`Family.col_sparsity_le`), public stage sources and a public initial state.
`Family.Solves x sol` is `sol 0 = x₀` and, on every closed stage interval, the
release's own `TimeDependentODE.SolvesODE` with the stage's constant generator
and source. `Family.InClass F η ḡ` (a Prop structure): every stage generator is
`TimeDependentODE.Accretive` (`D ⪰ 0`), every row and column of every sampled
matrix has Euclidean norm at most `η`, and every instance has a solution with
`x(T) ≠ 0` and `B ≤ ḡ ‖x(T)‖`, `B = ‖x₀‖ + Σ_k len k ‖b_k‖` (`Family.mass`),
i.e. `g ≤ ḡ` (eq. `odel:eq:params`). The parameters of the theorems are
`η = 1` and `τ = T η = T`.

**Access** (lines 3669-3673, 3685-3686). One call of label `l` on input `x` is
the coherent sampled-time oracle `Σ_{(i,k)} |i,k⟩⟨i,k| ⊗ O_l(x, k)`
(`Family.access ι F`, which is the release's `TimeDependentODE.labelOracle` of
the native primitives `NativeSparseBlockEncoding.oracles F.data` with
`TimeDependentODE.sample`), the branch register `ι` being an untouched
spectator. The released ODE solvers query the same primitives through other
fixed flattenings (`ODENativeCayley.oracle`) with spectator registers; there is
no Lean transport between the two forms. Inverse calls are counted
(`queryAdjoint`). Initial state and sources are public and free (lines
3672-3673, 3685-3686); only matrix queries are counted. Controlled calls are
covered by reduction, as for the Hamiltonian lower bound (paragraph
**Controlled calls** of `ODE/Model.lean`): a controlled locator call is a fixed gate (the hard
locators are input- and stage-independent, `jointData_locators_const`), and a
controlled value call is one value call between controlled swaps with a
uniform dummy word register (spectator `ι × Fin 2 × Z`); there is no Lean
lemma for this step.

**Solvers** (lines 3675-3678). A `Solver ι F G ε` is a non-adaptive
`SparseHamiltonian.MultiOracleCircuit.Program` over `Family.access ι F`, a seed
of norm at most one, an isometric readout onto system `ℂ^N` ⊗ garbage `G`, and
a herald projection, with success probability at least `2/3` on every input
and conditional accuracy `ε` (`Readout.HeraldedAccurate`, observable form of
trace distance, no division by the success probability) for the normalised
solution `x(T)/‖x(T)‖` of every solution. `ODE/Uniqueness.lean` proves that a
piecewise-constant instance has at most one solution on `[0, T]`
(`Family.solves_eqOn`, `Family.solves_endpoint_unique`,
`Family.forall_solves_iff`), so "every solution" is the paper's requirement
and is satisfiable by honest solvers; no proof of a lower bound uses that
module.
`Family.Forces F ε b`: every solver, for every branch register `ι` and every
garbage space `G`, makes at least `b` value queries (`labelCount .value`) and
at least `b` queries in total (`count`). `Family.Witnesses F τ ḡ ε b`: `F` is
in the class with `η = 1` and `ḡ`, `T = τ`, and forces `b`.

**Hard families.**

* The joint family (`ODE/JointInstance.lean`, lines 3800-3858;
  `jointFamily`, at the parameters `jointFamilyAt s τ ḡ` of
  `ODE/JointTheorem.lean`): `n + 2` stages on
  the promise problem of `ODE/Promise.lean` (hidden positions
  `j_{ak} ∈ ℤ_m`, exactly one odd candidate `a_*`, decide its half). Stage
  `k < n` has length `π/2` and generator `i H_k`, `H_k = ⊕_a S_{j_{ak}}`, the
  dilation `S_j` of the gadget `U_j` (`LinearSystems.gadget`, eqs.
  `odel:eq:gadget`, `odel:eq:dilation`, `odel:eq:stages`); then an idle stage
  and a unit source stage with `b = -(-i)^n |u_M, ω⟩` (eq. `odel:eq:force`).
  The explicit solution `jointSol` (no matrix exponential) has
  `x(T) = -2(-i)^n M^{-1/2} |a_*, ω⟩` (eq. `odel:eq:cancel`), `B = 2`,
  `g = √M ∈ [ḡ/√2, ḡ]` (`jointFamilyAt_g`, `joint_instance_props`), `D = 0`
  (`jointFamily_skew`), `η = 1` (`jointFamily_inClass`), exact complex dyadic
  entries `i · v/2^μ` (`jointData_dyadic`) and dimension
  `2Mm + s ≤ 3 ḡ² s`. Parameters (`ODE/Parameters.lean`, lines 3870-3876):
  `M = 2⌊ḡ²/2⌋` (`jointM`), `m = 2^⌊log₂ s⌋` (`2 ^ jointMu s`),
  `n = ⌊2(τ - 1)/π⌋` (`jointN`).
* The `g = 1` families (`ODE/Precision.lean`, lines 3954-3964): the three hard
  data of the Hamiltonian lower bound (`Hamiltonian.timeData`, `mixedMainData`,
  `precisionMainData`) read as one-stage homogeneous constant-coefficient ODEs
  `ẋ = -iH_x x` on `[0, τ]` (`timeFamilyAt`, `mixedFamilyAt`,
  `precisionFamilyAt`, built by `hamFamily` of
  `Helpers/Ode/Precision/Transfer.lean`: the same words and locators, decode
  `i · decode`), with `D = 0`, mass `1`, `‖x(T)‖ = 1`, so `g = 1`
  (`hamFamily_props`, `*FamilyAt_inClass`, `*FamilyAt_T`).
**Main theorems** (`CombinedRange s τ ḡ ε`: exactly `s ≥ 32`, `τ ≥ 4`,
`ḡ ≥ 2`, `0 < ε ≤ 1/64`, lines 3697-3699; `L = log(1/ε)`,
`h = log(e + L/τ)`, `r = L/h` is `Hamiltonian.hsR τ ε`).

* `combined` (Theorem `odel:thm:combined`, eq. `odel:eq:combined`, lines
  3697-3709 and 4001-4009): one of the joint, mixed and precision families
  `Witnesses τ ḡ ε (combinedBound s τ ḡ ε)`, where
  `combinedBound = c (ḡ √s τ + √(sτr) + r)` and
  `c = combinedConst = log 2/(8192π) = c₀/2` (`combinedConst_eq`).
* `combined_max`: for one solver of each of these three families, the largest
  value-query count is at least `combinedBound s τ ḡ ε`.
* `joint_witness` (Theorem `odel:thm:joint`, eq. `odel:eq:joint`, lines
  3860-3905, on the weaker `JointRange`: `s ≥ 4`): the joint family witnesses
  `c_J ḡ √s τ`, `c_J = jointConst = 1/400` (the first term of
  `odel:thm:combined`: inhomogeneous, time-dependent, `D = 0`, `g = Θ(ḡ)`).
  `joint_forces` is the native form for every even `M ≥ 2`, `n ≥ 1`,
  `1 ≤ μ` with `2^μ ≤ s`, `T ≥ n π/2 + 1` and `2ε ≤ 1`
  (`β² n √(M 2^μ)/16`), `joint_general` the form for any labelled family
  implementable by membership programs (Boolean cost `β² n √(M 2^μ)/8`), with
  `β = jointCorr ε = (2/3)(1 - 2ε) ≥ 31/48` (`jointCorr_ge`).
* `herald_witness`, `herald_max` (eq. `odel:eq:hsbound` in the ODE model, Lemma
  `odel:lem:herald`, lines 3954-3999, on `Hamiltonian.HSRange`, any `ḡ ≥ 1`): one of
  the three `g = 1` families witnesses `c₀ (√s τ + √(sτr) + r)`,
  `c₀ = log 2/(4096π)`; `precision_terms_witness`: one of them witnesses
  `c₀ (√(sτr) + r)` (the fourth sentence of `odel:thm:combined`, lines
  3707-3708). Per family: `time_forces` (`c_T √s τ`, `c_T = log 2/(192π)`),
  `mixed_forces` (`(log 2/(384√2)) √(sτr)`, for `L ≥ 64τ`, `s ≥ 64n/τ`),
  `precision_forces` (`r/32`, for `L ≥ 64τ`) and `precision_forces_sqrt`
  (`√(sτr)/(64√2)`, for `L ≥ 64τ`, `s < 64n/τ`).
* `outer_count_ge` (Lemma `odel:lem:outer`, lines 3743-3798): for `M ≥ 2`
  even, `m ≥ 2` even (the paper assumes `m ≥ 4`) and `n ≥ 1`, a Boolean
  program over the membership phase oracle
  whose final states have signed correlation `β ≥ 0` with the half answer
  makes at least `β² n √(Mm)/8` queries.

**Proof map.** Module paths are relative to `SparseLowerBounds/`.

* Generic additive adversary (`Query/PositiveAdversary`, helper
  `Helpers/Adversary/PhaseInner`): progress `W = Σ Γ_{xx'} δ_x δ_{x'} Re⟪ψ_x, ψ_{x'}⟫`
  (`progress`); a Schur certificate for each masked `Γ ∘ Δ_i` (`masked`,
  `SchurCert`, `schur_bound`); one query moves `W` by at most `2λ`
  (`abs_progress_query_sub_le`, `abs_progress_program_sub_le`); the observable
  gap `abs_re_inner_sub_le`, `norm_inner_le_of_gap`; the count bounds
  `count_ge`, `decision_count_ge`. It reuses the phase oracle of the shared
  Boolean-query layer (`Query/PhaseOracle`) and the projection-norm lemmas
  (`Helpers/Adversary/ProjNorm`).
* Lemma `odel:lem:outer` (lines 3743-3798): `ODE/Promise` (inputs, `oddCand`,
  `membership`, `halfSign`), `Helpers/Ode/OuterGraph/InnerGraph` (the inner parity
  graph, degree `d = nm/2`), `Helpers/Ode/OuterGraph/Halves`, `Helpers/Ode/OuterGraph/Counting`,
  `ODE/JointGraph` (outer `Γ`, `outerDeg_le_sum_outerGamma`: minimum degree
  `(M/2) d²`, eq. `odel:eq:outerdegree`; `outer_schurCert`:
  `λ = √(M/2) d √(m/2)`, eq. `odel:eq:outermask`), `ODE/JointAdversary`.
* The ODE encoding (lines 3800-3858): `Helpers/Ode/JointFamily/Defs`,
  `Helpers/Ode/JointFamily/Eigen` (dilation, eigen relation, norms, the half
  indicator `halfObs`), `Helpers/Ode/JointFamily/Solution` (stage derivatives,
  endpoints, `SolvesODE` per stage), `ODE/JointInstance` (data via
  `Hamiltonian.DataBuilder`, the family, `jointSol_solves`,
  `unitDirection_jointSol_T`), and `ODE/JointCompile` (`implementsOn_joint`:
  every sampled-time label is a `hardCost` membership program, `0` per locator
  and `2` per value call, by `PhaseCircuit.implementsOn_circuit`
  (`Query/PhaseCircuit`) and `Hamiltonian.bitWordGate`).
* Theorem `odel:thm:joint` (lines 3860-3905): `ODE/Parameters`
  (`joint_numeric`) and `ODE/JointTheorem`: the heralded half measurement
  through `Readout.heralded_correlation` (`Query/Readout`), compilation by
  `Reduction.exists_boolean_program_inner` and `hardCost` (`Query/Ancilla`),
  then `outer_count_ge`.
* Lemma `odel:lem:herald` in the ODE model (lines 3954-3999):
  `Helpers/Ode/Precision/Transfer` (`access_hamFamily`: the sampled-time access
  of `hamFamily D` is the spectated native access `specOracles (ι × Fin 1) D`
  of `Query/Ancilla`; `solves_evolve`: `t ↦ Hamiltonian.evolve H t x₀` solves
  `SolvesODE`) and `ODE/Precision` (`forces_of_spec` transfers
  `Hamiltonian.time_herald`,
  `mixed_herald`, `precision_herald`; `Hamiltonian.assembly` gives the max
  form; `forces_or_of_max` the family form).
* Theorem `odel:thm:combined`: `ODE/Theorem` (`combined_max` from
  `joint_witness`, `mixed_forces`, `precision_forces`,
  `precision_forces_sqrt` and `Hamiltonian.assembly`, with
  `c₀ ≤ c_J` (`c0_le_jointConst`) and `c_T ≤ c_J ḡ`; `combined` from
  `combined_max` by `forces_or_of_max`).

Every theorem of these modules, helpers included, and every Prop field of the
structures `Family`, `Family.InClass`, `Solver`, `Family.Witnesses`,
`JointRange` and `CombinedRange` is axiom-audited in
`SparseLowerBounds/ODE/Audit.lean`.

**Formalization choices.**

* Piecewise-constant model: the hard families are
  piecewise-constant in time with public breakpoints (lines 3686-3688), and a
  solution must satisfy the release's own `TimeDependentODE.SolvesODE` on every
  stage interval, with the release's `TimeDependentODE.Accretive`, the native
  primitives `NativeSparseBlockEncoding.Data (X × Fin K)` and the release's
  sampled-time oracle `TimeDependentODE.labelOracle`.
* Scope: the Table 1 row only, i.e. Theorem `odel:thm:combined` with its
  ingredients `odel:lem:outer`, `odel:thm:joint` and `odel:lem:herald` in the
  ODE model.
* The adversary of Lemma `odel:lem:outer` is the additive (positive-weight)
  adversary with weighted Schur certificates for the masked matrices
  (`Query/PositiveAdversary`), elementary (no operator norms, no
  Perron-Frobenius), with uniform weights and a minimum-degree bound instead
  of exact regularity of `Γ` on the promised inputs; the paper's norm bounds
  of eq. `odel:eq:outermask` enter as Schur certificates with the same `λ`.
* Explicit constants instead of the paper's unspecified absolute constants:
  `c = log 2/(8192π)` in `odel:thm:combined`, `c_J = 1/400` in
  `odel:thm:joint`, `β² n √(Mm)/8` in `odel:lem:outer`, the constants of the
  Hamiltonian lower bound in `odel:lem:herald`.
* One model, family form with max form: all hard families are instances of the
  one class `ODE/Model` with one oracle shape, so the headline `combined` is the
  paper's class-level worst-case claim in family form (one of the three
  concrete families, chosen by the parameters, forces the bound on every
  solver, value queries and total count). In the proof the max form
  `combined_max` is the quantitative core and `combined` is derived from it by
  `forces_or_of_max` (classically: if no family forced the bound, one cheap
  solver per family would contradict `combined_max`). The time family is not
  among the three: its term `√s τ` is dominated by the joint term `ḡ √s τ`.
  No single instance witnesses all terms and the bounds are not multiplied
  (lines 3715-3719, 4005-4008).
* No formal ODE `Θ` bracket. The general-mesh solver
  `TimeDependentExtensions.ODE.solver` (one generator and forcing piece per
  mesh interval, breakpoints at the mesh points) covers piecewise-constant
  instances with public breakpoints, hence the hard families here, but its
  outcome is not converted into a `Solver` and its query budget is not
  compared with `combinedBound`, so no matching upper bound is stated in Lean
  (for the Hamiltonian lower bound, `Hamiltonian.release_theta` gives such a
  bracket).
* `Solver.accurate` requires accuracy for every solution, as the release's
  `TimeDependentODE.Outcome`; `ODE/Uniqueness` shows this equals accuracy for
  the promised one.
* Lower bounds are on `Q = labelCount .value`, and also on `count`; locators
  are free fixed gates on the hard data.

**Not formalized.**

* Theorem `odel:thm:psd` (constant-coefficient PSD precision lower bound,
  `H = 0`, `D ⪰ 0`, lines 4012-4135), Remark `odel:rem:homogeneous` (the
  source-free variant of the joint family, lines 3907-3952) and Lemma
  `odel:lem:dyson` (fixed-parameter precision obstruction, lines 4155-4254).
* The comparison with the upper bounds `odel:eq:upper`, `odel:eq:refined`
  (lines 3710-3730): no ODE `Θ` bracket, see above.
* The application to the released ODE solvers (lines 3677-3679: Euclidean
  error for pure outputs implies the requirement; the bounds apply to
  `ode:thm:main` and `ode:thm:time`): there is no bridge from their oracle
  families and certificates to `Solver`, unlike the Hamiltonian lower bound's
  `main_max_endpoint` and `main_max_release`; and no lemma exhibits a `Solver`.
* The optional dense padding to maximum sparsity exactly `s`, padding to a
  qubit register (lines 3899-3904) and padding to a common dimension (lines
  4005-4006); the joint instances use zero padding and have at most
  `2^⌊log₂ s⌋` nonzeros per row.
* The discussion after Theorem `odel:thm:psd` (lines 4137-4142), equation
  `odel:eq:fixed` and its consequence (lines 4256-4275), and the two-sided
  comparison in "Scope and remaining gap" (lines 4277-4295).
* Adaptive solvers (classical trees of measured runs) for the ODE class;
  controlled calls are covered by the documented reduction only; gate,
  workspace and classical circuit-generation costs.

**Provenance.** These modules are an external development of the same origin
as the Hamiltonian lower bound, added in this package: `ODE/`, `Helpers/Ode/`,
`Helpers/Adversary/PhaseInner.lean` and `Query/PositiveAdversary.lean`. They
were split into modules from a single-file bundle (with descriptive names for
the helper directories), `private` was removed so that every theorem can be
audited, and process notes were removed from the documentation; the
statements and proofs are unchanged.
-/
end
