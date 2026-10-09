import TimeDependentExtensions.Hamiltonian.Corollaries
import TimeDependentExtensions.ODE.Corollaries
import TimeDependentExtensions.BlockEncoding.Theorem
import TimeDependentExtensions.Coherent.Theorem

/-!
# Generalisations of the time-dependent theorems: paper-to-Lean entry point

The generalisations stated after Theorem `hs:thm:time` (paragraphs "Regularity and coherent
parameters" and "Relation to time-indexed block encodings") and in the proof of Theorem
`ode:thm:time` of the accompanying paper: nonuniform meshes, piecewise paths with breakpoints
and one-sided samples, integrated sample-error certificates, the nonuniform certified source
quadrature, coherent selection of durations and start times, and the time-indexed
block-encoding special case (equations `hs:eq:blockspecial` and `hs:eq:blockadditive`). The
released uniform-mesh theorems `SparseHamiltonian.TimeDependent.simulation` and
`SparseHamiltonian.TimeDependentODE.solver` (libraries `TimeDependentHamiltonian` and
`TimeDependentODE`, whose statement files predate this library) are unchanged. The corollary
`hs:cor:hybrid` relies on other papers and is not formalised. No result from another paper is
used. All declarations below are in the namespace `TimeDependentExtensions`.

* Theorem `hs:thm:time` on general meshes, with breakpoints and the integrated certificate:
  `Hamiltonian.simulation`; piecewise Lipschitz paths with one-sided samples:
  `Hamiltonian.simulation_lipschitz`; one path on `[0, T]`: `Hamiltonian.simulation_path`;
  untouched references: `Hamiltonian.simulation_with_reference`; an explicit slot count:
  `Hamiltonian.slotCount`, `Hamiltonian.slotCount_spec`.
* Theorem `ode:thm:time` on general meshes, with breakpoints, integrated certificates and the
  certified source quadrature on the mesh: `ODE.solver` (statement `ODE.Outcome`); piecewise
  Lipschitz generators and forcing: `ODE.solver_lipschitz` (`ODE.LipschitzOutcome`); the
  public part of the budget on a mesh of step at most `h`: `ODE.publicError_le`.
* Equation `hs:eq:blockspecial`: `BlockEncoding.resolvent_right`, `resolvent_left`,
  `resolvent_boundary`, `resolvent_moment`, `endpoint_norm_le`; equation
  `hs:eq:blockadditive`: `BlockEncoding.simulation`.
* Coherent selection of durations and start times: `Coherent.coherent_select`,
  `Coherent.coherent_windows`; for the ODE SELECT with any duration tables:
  `MeshSelect.select`.

**Meshes and refinement.** A mesh is `t : ℕ → ℝ` with `t 0 = 0`, `t M = T` and `t` monotone
on `ℕ` (`IsMesh`; a finite mesh is extended by `T` beyond `M`); intervals may be empty. The
clock runs on `N` slots of length `T / N`; slot `k` uses the sample of the mesh interval
containing `k T / N` (`pieceOf t T N hM k = slotPiece t T N M k`, the largest `r < M` with
`⌈t_r N / T⌉ ≤ k`). The private cells of slot `k` carry the time address `|σ k⟩` in the
fixed clean encoding (`Refined.embedding`, `MeshSelect.embedding`); the queries and native
programs are those of the released construction, so the query bounds are the released ones.
The slot product is the mesh product with interval lengths rounded to multiples of `T / N`
(`refined_evolution_eq`, `evolution_slotPiece`), within `M (T / N) Λ` of it for samples of
norm at most `Λ` (`refined_evolution_sub_le`, `ODEMesh.refinedPropagator_sub_le`).

**Access models.** As in the released theorems: `D : NativeSparseBlockEncoding.Data (X × Fin M)
n Z s` supplies one represented sample `D.matrix (x, r)` per mesh interval `r`, through the
coherent sampled-time native oracle `∑_r |r⟩⟨r| ⊗ O_r`; one call counts once with `r` in
superposition, and inverse calls are counted. For the ODE, the source interfaces `J₀ x` and
`Jb x r` are the released ones, with one forcing label per mesh interval. For block encodings,
the primitive is the controlled time-indexed oracle `|c, r⟩ ⊗ v ↦ |c, r⟩ ⊗ O_r^c v`
(`BlockEncoding.primitive`, with spectator registers `BlockEncoding.oracle`) for Hermitian
unitaries `O_r` on `ℂ^{B₀}` with `J† O_r J = H̃_r / α` (`BlockEncoding.blockSample`).

**Hypotheses and guarantees.**

* `Hamiltonian.simulation`: `0 < η`, `0 < T`, `0 < ε ≤ 1/2`, `0 < M`, `0 < N`, a mesh, the
  released sample promises (Hermitian, row and column norms at most `η`), and the slot
  conditions `4 s η T ≤ N`, `9 (√s η T)³ ≤ ε N²` and `9 M √s η T ≤ ε N`. For some
  admissible `γ` there is one program over `Hamiltonian.oracle D N γ η T ε` with at most
  `995328 (√s τ + √(s τ log(1/ε)) + log(1/ε))` queries, `τ = η T`, and an isometric clean
  encoding `ι = Hamiltonian.input D hM t N γ η T ε`; for every instance `x`, `p.eval x` is
  unitary and, for every path with one piece `H_r` per mesh interval, Hermitian and
  interval-integrable on `[t_r, t_{r+1}]`, with
  `∑_r ∫_{t_r}^{t_{r+1}} ‖H_r(u) - H̃_r‖ du ≤ ε / 9`, and for every propagator `U` of the
  path (`U 0 = 1`, `SolvesOn` on every closed interval, so one-sided derivatives at the
  breakpoints), `‖p.eval x ∘ ι - ι ∘ U(T)‖ ≤ ε`. `Hamiltonian.simulation_with_reference`:
  the same on inputs entangled with an untouched finite reference register.
* `Hamiltonian.simulation_lipschitz`: the same for `β_r`-Lipschitz pieces with one-sided
  samples `‖H_r(t_r) - H̃_r‖ ≤ δ_r` and `∑_r (β_r Δ_r² / 2 + δ_r Δ_r) ≤ ε / 9`,
  `Δ_r = t_{r+1} - t_r`; such a propagator exists.
* `ODE.solver`: the released hypotheses of `TimeDependentODE.solver`, a mesh, the slot
  conditions `8 s ρ T ≤ N` and `3 (√(2s) ρ T)³ ≤ ν N²`, where `g' = 2 g`, `ε' = ε / 2`,
  `R = 4 log (20000 g' / ε')`, `ν = ε' / (10000 g')` and `ρ = η_H + R η_D > 0`, and the
  source mass `B = r₀ + ∑_q Δ_q rb q > 0` (`MeshSampling.mass`). One public trial family
  satisfies the released complete certificate `ODECompleteTrial.Certificate` (success
  probability at least `2/3`, conditional trace distance at most `ε` from `x(T) / ‖x(T)‖`,
  at most `1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)` matrix queries with `Θ = T η_H + T η_D ℓ`
  and `ℓ = log (10000 g' / ε')`, and at most `40 g'` calls of each source interface, `80 g'`
  in total) for every instance with accretive, interval-integrable generator pieces `G_r`,
  interval-integrable forcing pieces `b_r` bounded by `b_max`, a solution of
  `x' = -G_r x + b_r` on every closed interval, the public source norms and prepared
  directions, `x(T) ≠ 0`, `B ≤ g ‖x(T)‖` and
  `(r₀ + b_max T) ∑_r ∫ ‖G_r - G̃_r‖ + ∑_r ∫ ‖b_r - b̃_r‖ + publicError ≤ ε B / (2000 g)`,
  where `publicError = s Λ (∑_q Δ_q² rb q / 2 + M (T / N) B)` with `Λ = D.scale`
  (`ODE.publicError`). If every `Δ_q ≤ h`, then `publicError ≤ s Λ (h / 2 + M T / N) B`
  (`ODE.publicError_le`).
* `ODE.solver_lipschitz`: the same for Lipschitz generator and forcing pieces with one-sided
  samples; a solution exists from every initial state (`ODE.exists_piecewise_solution`).
* `BlockEncoding.simulation`: `0 < α`, `0 < T`, `0 < ε ≤ 1`, a mesh and
  `4 α T ≤ N`, `9 (α T)³ ≤ ε N²`, `9 M α T ≤ ε N`: one program with at most
  `2304 (α T + 1 + log(3/ε))` controlled time-indexed queries, including inverse calls, and
  the guarantee of `Hamiltonian.simulation` with `H̃_r = α J† O_r J`.
* `Coherent.coherent_select`: under `0 < ε ≤ 1`, `8 s η T ≤ N` and `3 (√(2s) η T)³ ≤ ε N²`,
  one rescaling `γ` (hence one oracle family `MeshSelect.alignedOracle` and one clean
  encoding), fixed by the largest duration `T`, serves every public duration table
  `0 ≤ u_i(r) ≤ T`: for each table there is a program (its query-free gates depend on the
  table) with at most `663552 · shape (2s) (η T) (log (2/ε))` queries of the sampled-time
  native oracle with the branch label as spectator, whose full output is within `ε` of
  `∑_i |i⟩⟨i| ⊗ ∏_k exp(-i (u_i(σ k) / N) H̃_{σ k})`.
* `Coherent.coherent_windows`: one rescaling, oracle family and clean encoding serve every
  public table of windows `a_i ≤ b_i ≤ M`; for each table a program with at most
  `663552 · shape (2s) (η T) (log (6/ε))` queries has full output within `ε` of
  `∑_i |i⟩⟨i| ⊗ V_i(t_{b_i})` for every family of propagators of the path from the identity
  at `t_{a_i}`, under `∑_r ∫ ‖H_r - H̃_r‖ ≤ ε / 3` and the slot conditions `8 s η T ≤ N`,
  `9 (√(2s) η T)³ ≤ ε N²` and `3 M √s η T ≤ ε N`.

**Proof map.** Module paths are relative to `TimeDependentExtensions/`.

* Meshes, blocks of slots and the refined products: `Mesh/Refinement` (`blockStart`,
  `slotPiece`, `blockLength_sub_lt`, `evolution_slotPiece`, `refined_evolution_sub_le`).
* The integral form of the unitary Duhamel estimate, piecewise propagators, the integrated
  certificate and existence: `Mesh/Duhamel` (`duhamel_integral`, `mesh_error_integral`,
  `refined_error`, `integral_le_of_lipschitz'`, `exists_piecewise_propagator`).
* The released sampled native simulation with slot samples `σ`: `Hamiltonian/Native`
  (`Refined.implementsOn`, `Refined.exists_sampled_simulation`); rescaling, the error budget
  and the corollaries: `Hamiltonian/Theorem`, `Hamiltonian/Corollaries`.
* The released ODE SELECT and source layer on `N` slots: `ODE/Select` (`MeshSelect.select`),
  `ODE/Source` (`MeshSource.coefficient_trial_certificate`).
* Forced dissipative ODEs on a mesh: the one-step estimate with integrated sample errors
  (`ODEMesh.step_error_integral`), the energy bound across breakpoints
  (`ODEMesh.piecewise_norm_le`), the accumulated error (`ODEMesh.mesh_error`), masked
  propagators (`ODEMesh.meshRecurrence_eq_sum`) and the refinement
  (`ODEMesh.refinedPropagator_sub_le`): `ODE/Discretisation`.
* Mesh sources, slot generators, product families and the discretised target:
  `ODE/Sampling` (`MeshSampling.family`, `MeshSampling.branchEvolution_eq_family`),
  `ODE/Target` (`MeshSampling.target_error`); assembly: `ODE/Theorem`, `ODE/Corollaries`
  (including `ODE.publicError_le`).
* The block-encoding interface (`Q = ν = 1`, boundary moment `1/√2`) and one active layer
  with three primitive calls: `BlockEncoding/Native`; the chronological clock and the budget:
  `BlockEncoding/Theorem`.
* Rotated samples `i H̃` with the same oracles (`Coherent.rotate`,
  `Coherent.lchsHamiltonian_rotate`), the coherent SELECT and windows: `Coherent/Theorem`.

Every theorem of the library is axiom-audited in `TimeDependentExtensions/Audit.lean`.

**Formalisation choices.**

* Nonuniform meshes are realised by a uniform refinement into `N` slots with the slot-to-sample
  map `pieceOf` in the clean encoding (the manuscript uses such a "known map from each new
  time label to its original sample label" in the proof of `hs:cor:hybrid`). The rounding of
  the interval lengths to multiples of `T / N` costs `M (T / N) Λ`, `Λ = √s η` (Hamiltonian;
  condition `9 M √s η T ≤ ε N`) or `M (T / N) s Λ B` with `Λ = D.scale` (ODE, in
  `publicError`); the paper instead uses nonuniform Cayley steps `w_r = α Δ_r`. Increasing
  `N` changes neither the query bound nor the primitive sampled-time oracle; only the
  spectator clock register grows.
* Breakpoints: the path is one piece per mesh interval, given on the closed interval; the
  propagator or solution solves each piece on its closed interval, with one-sided
  derivatives at the mesh points. The one-sided sample of interval `r` is the value of piece
  `r` at `t_r`.
* Propagators and solutions are classical (`SolvesOn`, `SolvesODE`: a derivative at every
  point of each closed interval). Interval-integrable pieces are therefore covered when such
  a propagator or solution exists, for example for pieces continuous on each closed interval
  (`exists_piecewise_propagator`, `ODE.exists_piecewise_solution`); a piece with a jump
  inside its interval has none, so every discontinuity must be a mesh point.
* The integrated certificates are hypotheses on each instance, after the program is fixed;
  the ODE certificate uses the energy bound `‖x(u)‖ ≤ r₀ + b_max T` for the generator term.
* Source quadrature: left-endpoint weights `Δ_q`; the forcing samples `b̃_q` are any vectors
  with the public norms `rb q`, and the quadrature error is part of the certified error
  (`∑_r ∫ ‖b_r - b̃_r‖` and `s Λ ∑_q Δ_q² rb q / 2`). Coherent start times of the source
  branches are the first slots of their intervals, through the released duration table.
* Error budgets: Hamiltonian `2ε/3` (filter) `+ ε/9` (Cayley) `+ ε/9` (refinement)
  `+ ε/9` (certificate) `= ε`; block encodings the same; coherent windows `ε/3` (SELECT at
  precision `ε/3`) `+ ε/3` (refinement) `+ ε/3` (certificate).
* Block encodings: the active layers use the released masked compiler, with the dummy input
  `|0, 0⟩ ⊗ |b₀⟩` on which every controlled call is the identity; hence three calls per
  layer and the explicit constant `2304 = 6 · 3 · 128`.
* Coherent selection: the selection register is a branch label of the SELECT; the durations
  are public tables, at most the common `T` that fixes the filter schedule, and the
  program's query-free gates depend on the table. For Hamiltonian samples the SELECT of the
  ODE layer is applied to `i H̃`, whose LCHS Hamiltonian is `H̃` at every frequency; the
  rotation changes only the public decoder.

**Not formalised.** The hybrid bound `hs:cor:hybrid` (it relies on other papers); the sharper
block-encoding bound `hs:eq:prioroptimal` of Chen, Gao, Wang and Zhou and its recovery in the
involution case; Carathéodory (absolutely continuous) propagators and solutions of general
integrable paths; nonuniform Cayley steps without refinement; coherent selection of
parameters other than durations and start times at mesh points; the degenerate cases
`T = 0`, `η = 0` and `α = 0`; gate and workspace costs; and lower bounds for this class.
-/
