import DeferredMeasurementLowerBounds.Access.ControlTree
import DeferredMeasurementLowerBounds.Corollaries.Hamiltonian
import DeferredMeasurementLowerBounds.Corollaries.LinearSystem
import DeferredMeasurementLowerBounds.Corollaries.ODE
import DeferredMeasurementLowerBounds.Corollaries.Unitary
import DeferredMeasurementLowerBounds.Corollaries.TimeDependent
import DeferredMeasurementLowerBounds.NonVacuity
import AdaptiveODELowerBound.Release.Bridge

set_option autoImplicit false

/-!
# Lower bounds with measurements inside a run: paper-to-Lean entry point

The lower-bound sections of the manuscript state their query bounds for unitary algorithms and cover
measurements by a one-line reduction: "Purification and deferred measurement include adaptive and
randomised algorithms" (proof of Lemma `hsl:lem:precision`), "This argument also covers controlled
queries and adaptive algorithms after coherent purification and padding to their worst-case query
count" (proof of Lemma `qlsl:lem:xor`, the lemma behind Theorem `qlsl:thm:main`), and the solver
class of the ODE lower bounds (Section `odel:sec:main`: access with inverses and controls, a success
flag of probability at least `2/3`, conditional trace distance `ε`, a worst-case query bound). This
library formalises that reduction for a general model of **measured algorithms** and states the
headline lower bounds for them. All declarations below are in the namespace
`DeferredMeasurementLowerBounds`.

* The model and its containment of the adaptive protocols of the package: `Model.Measured`,
  `Model.ofTree` with `Model.successMass_ofTree`, `Model.successDensity_ofTree`,
  `Model.conditionalDensity_ofTree`, `Model.worstCost_ofTree`.
* The deferral (proof of Lemma `hsl:lem:precision` and proof of Lemma `qlsl:lem:xor`):
  `Deferral.deferral`, with the program `Deferral.deferredProgram`, its seed
  `Deferral.deferredSeed`, its readout `Deferral.deferredOutput` and its form as an adaptive
  protocol `Deferral.deferredTree`.
* Theorem `hsl:thm:main` (eq. `hsl:eq:main`) for measured algorithms:
  `Corollaries.main_max_measured` (max form), `Corollaries.main_exists_measured` (family
  form); over the coherent sampled-time access of the class of Theorem `hs:thm:time` and over
  its call forms: `Corollaries.main_max_measured_access`, `Corollaries.main_max_measured_calls`.
* Theorem `qlsl:thm:main` for measured algorithms:
  `Corollaries.lower_bound_sharp_measured` (constant `1/1536`) and
  `Corollaries.lower_bound_measured` (the manuscript's `1/3072`).
* Theorem `odel:thm:combined` (eq. `odel:eq:combined`) for measured solvers:
  `Corollaries.combined_measured` (family form), `Corollaries.combined_max_measured` (max form),
  and the witnesses of its third and fourth sentences,
  `Corollaries.joint_witness_measured` (Theorem `odel:thm:joint`) and
  `Corollaries.precision_terms_witness_measured` (Lemma `odel:lem:herald`); the
  transfer of every adaptive witness, `Corollaries.measuredForces_of_treeForces`,
  `Corollaries.measuredWitnesses_of_treeWitnesses`, and its converse
  `Corollaries.treeForces_of_measuredForces`.
* The lower half of the last sentence of Corollary `hs:cor:unitary` ("the constant-error worst-case
  complexity is `Θ(√N)`"; reduction in the proof of Corollary `hs:cor:unitary`) for measured
  algorithms: `Corollaries.entry_count_ge_measured`, `Corollaries.implementation_count_ge_measured`,
  their heralded forms `Corollaries.entry_count_ge_measured_heralded`,
  `Corollaries.implementation_count_ge_measured_heralded`, and the search forms
  `Corollaries.search_count_ge_measured_sharp`, `Corollaries.search_count_ge_measured`,
  `Corollaries.search_count_ge_measured_heralded`.
* Single-label controlled access: `Access.worstCost_ctrlTree`, `Access.worstCost_ctrlTree_conj`,
  `Access.worstCost_ctrlTreeOf`.
* Non-vacuity: `NonVacuity.deferral_midRun`, `NonVacuity.released_linear_system_measured`,
  `NonVacuity.released_unitary_measured`.

**Algorithm model.** `Model.Measured O E`: a finite tree on one persistent workspace `K` (any
complex Hilbert space) over a labelled oracle family `O : L → X → K →L[ℂ] K`, whose nodes are
`call l inverse next` (one call of label `l`, forward or inverse), `instrument n A next` (an
input-independent instrument with Kraus operators `A j`, `∑ j, A j† A j = 1`, `n` outcomes,
followed by the classically chosen continuation `next j`), `output out` (an isometry
`out : E → K`; the decoded output is `out† ψ`) and `reject`. Instruments cover multi-outcome
projective and generalised measurements in the middle of a run, classical randomness of any
finite law, known unitaries, every classically controlled known operation, resets of a
finite-dimensional workspace (`Model.reset`) and resets of a finite-dimensional register (an
instrument with Kraus operators `|ψ⟩⟨b_i| ⊗ 1`). On an initial vector `φ`,
`successDensity x φ` is the sum over transcripts of `|out† ψ⟩⟨out† ψ|` for the unnormalised
branch vector `ψ`, `successMass x φ` the sum of `‖out† ψ‖²`, `conditionalDensity x φ` their
quotient (`0` when the mass is `0`), and `worstCost w` the maximum over all transcripts,
including those of probability zero, of the weighted number of calls (inverse calls count as
calls), the convention of `SparseLinearSystems.Protocol.Tree.worstCost`
(`Model.worstCost_ofTree`). Replacing every subtree that is reached with probability zero on
every input by `reject` changes no success mass and no output, so the lower bounds below also
hold for the worst case over the transcripts of positive probability (not formalised).

**Guarantees.**

* `Deferral.deferral`: for unitary labels, a unit initial vector `φ` and every decidable set
  `counted` of counted labels, there are finite record types `R`, `J`, a program `p` over the
  selection family `Deferral.selFamily O counted R` (record-selected calls
  `Σ_r |r⟩⟨r| ⊗ O(π r)` and known unitaries) that is unitary on every input, a unit seed and an
  isometric readout `out` such that, for every input `x`, the record-wise pure states of
  `out† (p.eval x seed)` sum to `M.successDensity x φ`, its squared norm is
  `M.successMass x φ`, and `p.cost selWeight ≤ M.worstCost (countWeight counted)`: each
  record-selected call of counted labels counts once, the other calls not at all.
* `Corollaries.main_max_measured`: on `HSRange τ s ε` (`τ ≥ 1`, `s ≥ 32`, `0 < ε ≤ 1/64`), for
  three measured algorithms over admissible labels of the time, mixed and precision hard
  families, each with a unit initial vector, success probability at least `2/3` on every input
  and `DensityAccurate` conditional output at accuracy `ε`,
  `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` with `c₀ = log 2/(4096π)`.
  `Corollaries.main_exists_measured`: one of the three families forces every such algorithm.
* `Corollaries.lower_bound_sharp_measured`: for `κ ≥ 32`, `s ≥ 5`, `0 < ε ≤ 1/64`, native data
  of the hard family with input-independent locators and an entry-determined table, and a
  measured algorithm over admissible labels with a unit initial vector, success at least `2/3`
  and reduced conditional output within trace distance `ε` of `|x_A⟩⟨x_A|`:
  `κ √s ln(1/ε)/1536 < M.worstCost w`.
* `Corollaries.combined_measured`: on `CombinedRange` (`s ≥ 32`, `τ ≥ 4`, `ḡ ≥ 2`,
  `0 < ε ≤ 1/64`), one of the joint, mixed and precision families is in the class and forces
  every measured solver, over the sampled-time access or over its call forms, to make at least
  `combinedConst (ḡ √s τ + √(sτr) + r)` value calls and as many calls in total,
  `combinedConst = log 2/(8192π)`. `Corollaries.joint_witness_measured`: on `JointRange` the
  joint family witnesses `jointConst ḡ √s τ`; `Corollaries.precision_terms_witness_measured`:
  on `HSRange` with `ḡ ≥ 1` one of the `g = 1` families witnesses `c₀ (√(sτr) + r)`.
* `Corollaries.main_max_measured_access`, `Corollaries.main_max_measured_calls`: on
  `HSRange τ s ε`, for three measured algorithms over the coherent sampled-time native access
  of the constant time, mixed and precision data
  (`TimeDependentHamiltonianLowerBound.coherentAccess`, `constData`), or over its call forms,
  with unit initial vectors, success probability at least `2/3` on every input and
  conditional output `ε`-accurate for `U(τ) ψ_in` for every propagator `U` of the constant
  path, `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)`, with `Q` the worst-case number of
  value calls: the measured forms of `TimeDependentHamiltonianLowerBound.main_max_tree_access`
  and `main_max_tree_calls`.
* `Corollaries.implementation_count_ge_measured`, `Corollaries.entry_count_ge_measured`: for
  `N ≥ 2`, a measured algorithm over the released entry oracle of the search family (or over
  the ordinary entry lookup with any payload) that, on an isometric encoding `J`, for every unit
  input `ψ` succeeds with probability one and outputs a state within trace distance
  `ε₀ ≤ 1/2` of `U_m ψ`, satisfies `(1 - 2 √(ε₀ (1 - ε₀))) √(N - 1) ≤ 2 Q`, inverse calls
  counted. The heralded forms assume only, on the input `J|0⟩`, success probability at least
  `p₀` and conditional trace distance `ε₀ ≤ 1` from `|m⟩` with `p₀ (1 - ε₀) ≥ 1/2`, and give
  the same bound with `δ = 1 - p₀ (1 - ε₀)` in place of `ε₀`.
* `Access.worstCost_ctrlTree`: compiling the deferred program over single-label controlled
  calls of one counted label (the other labels uncounted) costs at most twice the worst-case
  count, and at most the worst-case count when the inverse is a known conjugation
  (`worstCost_ctrlTree_conj`); `worstCost_ctrlTreeOf`: at most `2 · #{counted labels}` times
  the worst-case count of all counted calls (an aligned slot may call every counted label, so
  a factor `2` per label does not hold in general).
* `NonVacuity.deferral_midRun`: the deferral applies to `NonVacuity.midRun`, a measured
  algorithm with a two-outcome measurement inside a run followed, on one outcome, by an oracle
  call, and gives a unitary program with at most one counted call.
  `NonVacuity.released_linear_system_measured`: the released algorithm of `qls:thm:main` as a
  measured algorithm (`Model.ofTree`) meets every hypothesis of
  `Corollaries.lower_bound_sharp_measured` on the hard family, with worst-case count between
  `κ √s ln(1/ε)/1536` and `4·10¹² √s κ ln(1/ε)`. `NonVacuity.released_unitary_measured`: the
  released circuit of `UnitaryImplementationExtensions.LowerBound.theta_of_error` at error
  `1/4`, as a measured algorithm, meets every hypothesis of
  `Corollaries.implementation_count_ge_measured` and obeys the released upper bound.

**Proof map.** Module paths are relative to `DeferredMeasurementLowerBounds/`.

* `Model/Measured`, `Model/Embed`, `Helpers/TreeContainment/Steps`: the model, its semantics
  and the containment `ofTree` (programs as chains of one-outcome instruments, resets
  `|ψ⟩⟨b_i|`, herald instruments `{F F†, 1 - F F†}`, uniform coins `c^{-1/2} 1`).
* `Deferral/Registers`: record registers `Rec W k` and the Halmos dilation
  `e₀ V† + V e₀† + (1 - e₀ e₀† - V V†)` of each instrument (`halmos_unitary`, `halmos_fresh`).
* `Deferral/Selection`, `Deferral/Schedule`, `Deferral/Align`, `Deferral/Defer`,
  `Deferral/Output`, `Deferral/Theorem`: the selection family of record-selected calls, the
  alignment of the `k`-th counted call of every branch into slot `k`, the deferred program and
  its output, and the deferral theorem.
* `Readout/Density`, `Readout/Trace`: the record register joins the garbage; trace-distance
  accuracy and partial traces transfer exactly (`Readout.densityAccurate_liftReadout`,
  `Readout.ptrace_liftEquiv`).
* `Access/Native`: a merged slot of admissible native labels is one native call
  (`Access.nativeCall_fiber`, `Access.admissible_selFamily`,
  `Access.native_admissible_selFamily`).
* `Access/Control`, `Access/Transport`, `Access/ControlTree`, `Access/Phase`,
  `Access/TimeAccess`, `Access/TimeCircuits`, `Helpers/OdeAccess/Calls`: compilation of the
  record-selected calls into controlled calls, for general labels, the phase oracle and the
  sampled-time access of the ODE class (`Access.star_access_value`: the inverse value call is a
  conjugated value call).
* `Corollaries/Hamiltonian`, `Corollaries/LinearSystem`, `Corollaries/ODESolver`,
  `Corollaries/ODE`, `Corollaries/UnitaryReadout`, `Corollaries/Unitary`,
  `Helpers/SearchReadout/Overlap`: the corollaries, from
  `AdaptiveHamiltonianLowerBound.main_max_tree`, `LinearSystemLowerBound.lower_bound_sharp`,
  `AdaptiveODELowerBound.combined_tree` with `Joint.joint_witness_tree` and
  `precision_terms_witness_tree`, and `UnitaryImplementationExtensions.Search.count_ge`.
* `Corollaries/TimeDependent`: `Corollaries.main_max_measured` with
  `TimeDependentHamiltonianLowerBound.admissible_coherentAccess`,
  `TimeDependentHamiltonianLowerBound.admissible_callFamily_coherentAccess` and
  `TimeDependentHamiltonianLowerBound.densityAccurate_propagator_iff`.
* `NonVacuity`: `Deferral.deferral` on `midRun`; `Model.ofTree` of
  `SparseLinearSystems.Endpoint.algorithm` with `LinearSystemLowerBound.exists_access`,
  `SparseLinearSystems.Endpoint.main` and `LinearSystemLowerBound.physOracle_admissible`;
  `Model.ofProgram` of the circuit of `UnitaryImplementationExtensions.LowerBound.theta_of_error`.

Every theorem of the library, and every `Prop`-valued field of its structures, is
axiom-audited in `DeferredMeasurementLowerBounds/Audit.lean`.

**Formalisation choices.**

* Deferral: one fresh record register per instrument along a transcript
  (`Rec W k = Fin k → Option (Fin W)`, `k = M.depth`, `W = M.width`); each instrument becomes
  its Halmos dilation, a known unitary in every dimension (for a projective measurement, the
  coherent copy of the outcome). The `k`-th counted call of every branch is placed in slot
  `k`; uncounted calls and known unitaries are in weight-zero free segments. A merged slot is
  one record-selected call `Σ_r |r⟩⟨r| ⊗ O(π r)`, itself a record-controlled call, so the
  deferred program makes no oracle call outside the selection family. The output records are
  part of the output and are discarded with the garbage.
* Cost per access model: one native call per slot for admissible native labels
  (`hsl:thm:main`, `qlsl:thm:main`), so no constant is lost; one controlled call per slot for
  the phase oracle (self-inverse) and for the sampled-time value call (its inverse is the
  value call conjugated by the known negation of the value register), so `odel:thm:combined`
  and the unitary bound lose no constant; for general single-label controlled access one or
  two controlled calls per counted label used in a slot (factor at most `2` for one counted
  label, `2 · #{counted labels}` in general). No headline corollary uses general controlled
  access.
* Containment of `SparseLinearSystems.Protocol.Tree` needs a finite-dimensional workspace,
  since an instrument has finitely many outcomes and a reset of an infinite-dimensional
  workspace to a fixed vector is not such an instrument; the deferral and every corollary hold
  for workspaces of any dimension.
* Corollary hypotheses are those of the lifted package theorems (`HSRange` with `τ ≥ 1`;
  `CombinedRange`; `JointRange`; `κ ≥ 32`, `s ≥ 5`, `0 < ε ≤ 1/64`), and the measured
  algorithms start from an input-independent unit vector in place of the trees' seeds.
* ODE solvers: `Corollaries.MeasuredSolver` mirrors `AdaptiveODELowerBound.Model.TreeSolver`
  field for field, with the system register in `Type`; `Corollaries.MeasuredForces` quantifies
  over measured solvers over `F.access ι` and over `callFamily (F.access ι)`. For families
  with an input, measured forcing and tree forcing are equivalent
  (`treeForces_of_measuredForces`).
* Unitary implementation: a measured algorithm has no operator to compare with `U_m`, so
  accuracy is per-input trace distance of the conditional output (`DensityAccurate`) on an
  isometric input encoding; only the input `|0⟩` is used. The overlap argument gives the
  factor `1 - 2 √(ε₀ (1 - ε₀))`, positive for every fixed `ε₀ < 1/2` and zero at `ε₀ = 1/2`,
  the endpoint of `hs:cor:unitary`. The operator-norm statements for unitary programs remain
  `UnitaryImplementationExtensions.LowerBound.entry_count_ge` and `implementation_count_ge`.

**Not formalised.**

* Containment of `Protocol.Tree` for infinite-dimensional workspaces (a fresh-copy primitive
  would be needed; no corollary uses it). The package's tree theorems for `hsl:thm:main` and
  `qlsl:thm:main` are not restated from the measured ones; on finite-dimensional workspaces each
  follows in a few lines from `Model.ofTree` (`successMass_ofTree`, `conditionalDensity_ofTree`,
  `worstCost_ofTree`, `exists_unit_of_successMass_pos`); for the ODE class it is
  `treeForces_of_measuredForces`.
* The endpoint `ε₀ = 1/2` of the measured unitary lower bound, where the factor
  `1 - 2 √(ε₀ (1 - ε₀))` vanishes, and a named operator-norm form of it. For unitary programs
  the passage from operator-norm error to per-input trace distance is
  `SparseLowerBounds.Hamiltonian.accurate_of_endpoint` with
  `AdaptiveHamiltonianLowerBound.densityAccurate_pure_iff`, with constant `ε` rather than the
  sharp `ε √(1 - ε²/4)`.
* Named measured forms over the call family `AdaptiveODELowerBound.Access.callFamily` of the
  released entry oracle (forward, inverse, controlled and controlled-inverse calls). A measured
  algorithm whose only label is the controlled phase oracle of the search family is covered by
  `Corollaries.search_count_ge_measured_sharp` with the projection family
  `AdaptiveODELowerBound.Access.ctrlFamily P` (`AdaptiveODELowerBound.Access.phase_ctrlFamily`).
* For several counted labels under general single-label controlled access, a worst-case bound
  that charges each aligned slot only for the labels it uses (`Access.selCircuit_cost` bounds
  one slot in this way; `worstCost_ctrlTreeOf` charges `2 · #{counted labels}` per slot).
* In this library, measured forms over the physical oracles of the released ODE solvers
  (`AdaptiveODELowerBound.Release.combined_max_release_tree`, `PhysicalODELowerBound`,
  `ConstantODELowerBound`): their forcing statements quantify over single-label calls of those
  oracles, so the record-selected calls would first have to be compiled into them (a spectator
  identity for the branch register and an inverse conjugation of the physical value call, as
  `Access.TimeCircuits` does for the sampled-time access); they do not follow from
  `measuredWitnesses_of_treeWitnesses`. The library `ReleasedODESolverLowerBounds` states them.
* Named measured forms for the time-dependent Hamiltonian classes over the released oracle
  families of the time-dependent simulators
  (`TimeDependentHamiltonianLowerBound.main_max_tree_uniform`, `main_max_tree_mesh`); they would
  follow from `Corollaries.main_max_measured` with that library's admissibility lemmas
  (`TimeDependentHamiltonianLowerBound.admissible_uniform`, `admissible_mesh`) as in
  `Corollaries/TimeDependent`, which covers the coherent sampled-time access and its call forms.
* Named measured forms of Theorem `odel:thm:psd`, of the padded families and of Proposition
  `odel:rem:homogeneous`, and other named measured corollaries beyond the headline bounds: every
  `AdaptiveODELowerBound.Model.TreeWitnesses` transfers by `measuredWitnesses_of_treeWitnesses`, and
  the deferral covers every program-level bound whose access class contains the selection family and
  whose accuracy is a property of the output with the records discarded.

**Provenance.** No result from another paper is used. The libraries `SparseLinearSystems`,
`LinearSystemLowerBound`, `SparseLowerBounds`, `AdaptiveHamiltonianLowerBound`,
`ODELowerBoundExtensions`, `AdaptiveODELowerBound`, `UnitaryImplementationExtensions` and
`TimeDependentHamiltonianLowerBound` are only imported; no released module is changed. The
linear-system, adaptive Hamiltonian and adaptive ODE lower-bound statement guides predate this
library and list measurements inside a run followed by classically controlled operations, and
measurements with more than two outcomes, as outside them (covered by a documented reduction); the
reduction is proved here and the headline bounds are stated for measured algorithms. The statement
guides of the time-dependent Hamiltonian, constant-coefficient ODE and physical-oracle ODE
lower-bound libraries, released after the base of this library, list the same measurements as
outside them; for the first the coherent sampled-time access and its call forms are covered by
`Corollaries/TimeDependent`, the others, over the oracles of the released ODE solvers, by the library `ReleasedODESolverLowerBounds`. References to the manuscript
use its labels.
-/
