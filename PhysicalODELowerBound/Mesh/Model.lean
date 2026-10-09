import AdaptiveODELowerBound.Model.Solver
import ODELowerBoundExtensions.Release.Theta

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Forcing over the general-mesh physical oracle

Section `odel:sec:main` (manuscript lines 4105-4109: access "through a reversible value oracle
and in-place row/column locators, their inverses and controls, with a coherent time address when
needed"; lines 4111-4113: success flag of probability at least `2/3`, conditional trace distance
`ε`; lines 4114-4115: "The lower bounds thus apply to Theorems `ode:thm:main` and
`ode:thm:time`"; lines 4119-4122: public location lists and source preparation).

The adaptive solvers (`AdaptiveODELowerBound.Model.TreeSolver`) here call the physical oracle of
the released general-mesh solver `TimeDependentExtensions.ODE.solver`, run on the data of a
family `F` along any public placement `σ : Fin M → Fin K` of mesh pieces into stages
(`ODELowerBoundExtensions.Release.meshOracle F σ ι N d J₀ J_b`, any spectator index `ι`, slot
count `N`, degree `d`, public source interfaces `ODELowerBoundExtensions.Release.PublicSources`),
in one of two access shapes: the oracle family itself (with inverse calls), or its call forms
`AdaptiveODELowerBound.Access.callFamily` (plain, inverse, controlled and controlled-inverse
calls of every label on control ⊗ workspace; the controlled call of a label `l` is the branch
mask `SparseHamiltonian.MaskedProgram.masked (fun c => c)` of the physical label). Every call form
of a label is counted with the weight of the label. Two counts are bounded, as in
`AdaptiveODELowerBound.Release.combined_max_release_tree`: the worst-case number of value calls
(`ODESourceQueryBudget.matrixWeight valueWeight`: one per value call in any form, none per
location or source call) and the release's matrix count (`matrixWeight (fun _ => 1)`).

* `MeshForces F ε b`: every such solver, in both access shapes, makes at least `b` value calls
  and at least `b` matrix calls in the worst case. It has the shape of
  `AdaptiveODELowerBound.Model.TreeForces` with the physical oracle in place of the sampled-time
  access.
* `MeshWitnesses F τ ḡ ε b`: `F` is in the class (`η = 1`, `T = τ`, `g ≤ ḡ`) and mesh-forces `b`.
* `MeshCost F ε q`: `q` is the worst-case value count of some such solver; bookkeeping over the
  existing `Tree.worstCost` (as `AdaptiveODELowerBound.Model.TreeCost`). `MeshForces.le_cost` and
  `meshForces_of_cost` with the generic `AdaptiveODELowerBound.Model.forces_or_of_cost₂`,
  `forces_or_of_cost₃` turn max forms over realised counts into family forms.
* Containment: retry protocols (`ODELowerBoundExtensions.Release.RetrySolver`) are adaptive
  protocols (`AdaptiveODELowerBound.Model.retryToTree`), so `MeshForces` bounds every retry solver
  over the physical oracle or its call forms (`MeshForces.retry`, `MeshForces.retry_calls`). In
  particular, on a family all of whose inputs are solvable, it bounds every released protocol of
  the general-mesh solver (`ODELowerBoundExtensions.Release.ReleaseProtocol` over
  `releaseOracle F R = meshOracle F (stageOf K R)`) at any parameters `Θ`, `ℓ`, `g`
  (`MeshForces.releaseProtocol`), so also on the positive semidefinite and homogeneous families,
  and every `ODELowerBoundExtensions.Release.ReleaseRun` (`MeshForces.releaseRun`). Since
  `ReleaseRun` fixes `Θ = τ` and `ODELowerBoundExtensions.Release.exists_releaseProtocol` needs
  `D = 0`, `ReleaseRun` covers the released solver's runs on the joint, `g = 1` and padded
  families, not on the positive semidefinite and homogeneous ones. The retry-protocol forms of
  the family statements of this library are these lemmas applied to their `MeshForces`
  conclusions.
* `MeshCost.of_tree`: the worst-case value count of a solver over the oracle itself is a realised
  count, so the max forms over realised counts contain the released max forms over explicitly
  given solvers (`combined_max_release_tree_of_mesh`).
-/

namespace PhysicalODELowerBound.Mesh

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit SparseLinearSystems.Protocol
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open ODELowerBoundExtensions.Release (meshOracle PublicSources SysOp RetrySolver ReleaseRun
  releaseOracle ReleaseProtocol stageOf)
open AdaptiveODELowerBound.Model (TreeSolver)
open AdaptiveODELowerBound.Access (callFamily)

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K s : ℕ}

/-- **`F` forces `b` on the general-mesh physical oracle at accuracy `ε`**: every adaptive solver
over `meshOracle F σ ι N d J₀ J_b` (any placement `σ`, spectator index `ι`, slot count `N`,
degree `d`, public source interfaces, flag, output and garbage spaces), and every adaptive solver
over its call forms (plain, inverse, controlled and controlled-inverse calls), makes at least `b`
value calls and at least `b` matrix calls in the worst case over all transcripts. -/
def MeshForces (F : Family X N Z K s) (ε b : ℝ) : Prop :=
  (∀ (M : ℕ) (σ : Fin M → Fin K) (ι : Type) [Fintype ι] [DecidableEq ι] (Nsl d : ℕ)
      (J₀ : X → SysOp N) (Jb : X → Fin M → SysOp N), PublicSources J₀ Jb →
    ∀ (Fl E G : Type) [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
      [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (A : TreeSolver F (meshOracle F σ ι Nsl d J₀ Jb) Fl E G ε),
      b ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
        b ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) ∧
  (∀ (M : ℕ) (σ : Fin M → Fin K) (ι : Type) [Fintype ι] [DecidableEq ι] (Nsl d : ℕ)
      (J₀ : X → SysOp N) (Jb : X → Fin M → SysOp N), PublicSources J₀ Jb →
    ∀ (Fl E G : Type) [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
      [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (A : TreeSolver F (callFamily (meshOracle F σ ι Nsl d J₀ Jb)) Fl E G ε),
      b ≤ A.tree.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) ∧
        b ≤ A.tree.worstCost (fun c => ODESourceQueryBudget.matrixWeight (fun _ => 1) c.1))

/-- **`F` witnesses `b` on the general-mesh physical oracle** for the parameters `(τ, ḡ, ε)`: `F`
is in the class with `η = 1`, `T = τ` and `g ≤ ḡ`, and mesh-forces `b` at accuracy `ε`. -/
structure MeshWitnesses (F : Family X N Z K s) (τ gbar ε b : ℝ) : Prop where
  inClass : F.InClass 1 gbar
  time_eq : F.T = τ
  forces : MeshForces F ε b

/-- **A realised worst-case value count on the general-mesh physical oracle**: `q` is the
worst-case value count of some adaptive solver of `F` at accuracy `ε` over the physical oracle
(any placement, spectator index, slot count, degree and public source interfaces) or over its
call forms. -/
def MeshCost (F : Family X N Z K s) (ε q : ℝ) : Prop :=
  (∃ (M : ℕ) (σ : Fin M → Fin K) (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Nsl d : ℕ)
      (J₀ : X → SysOp N) (Jb : X → Fin M → SysOp N) (_ : PublicSources J₀ Jb) (Fl E G : Type)
      (_ : NormedAddCommGroup Fl) (_ : InnerProductSpace ℂ Fl) (_ : CompleteSpace Fl)
      (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (_ : CompleteSpace E)
      (_ : FiniteDimensional ℂ E) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G)
      (_ : CompleteSpace G) (A : TreeSolver F (meshOracle F σ ι Nsl d J₀ Jb) Fl E G ε),
      q = A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight)) ∨
  (∃ (M : ℕ) (σ : Fin M → Fin K) (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Nsl d : ℕ)
      (J₀ : X → SysOp N) (Jb : X → Fin M → SysOp N) (_ : PublicSources J₀ Jb) (Fl E G : Type)
      (_ : NormedAddCommGroup Fl) (_ : InnerProductSpace ℂ Fl) (_ : CompleteSpace Fl)
      (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (_ : CompleteSpace E)
      (_ : FiniteDimensional ℂ E) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G)
      (_ : CompleteSpace G)
      (A : TreeSolver F (callFamily (meshOracle F σ ι Nsl d J₀ Jb)) Fl E G ε),
      q = A.tree.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1))

/-- **The released solvers' counts are realised counts**: the worst-case value count of an
adaptive solver over the physical oracle itself (as in
`AdaptiveODELowerBound.Release.combined_max_release_tree`) is a `MeshCost`. -/
theorem MeshCost.of_tree {F : Family X N Z K s} {ε : ℝ} {M : ℕ} (σ : Fin M → Fin K) (ι : Type)
    [Fintype ι] [DecidableEq ι] (Nsl d : ℕ) {J₀ : X → SysOp N} {Jb : X → Fin M → SysOp N}
    (hJ : PublicSources J₀ Jb) {Fl E G : Type} [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl]
    [CompleteSpace Fl] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : TreeSolver F (meshOracle F σ ι Nsl d J₀ Jb) Fl E G ε) :
    MeshCost F ε (A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight)) := by
  exact Or.inl ⟨M, σ, ι, inferInstance, inferInstance, Nsl, d, J₀, Jb, hJ, Fl, E, G, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, A, rfl⟩

/-- Mesh-forcing is a lower bound on every realised value count. -/
theorem MeshForces.le_cost {F : Family X N Z K s} {ε b : ℝ} (h : MeshForces F ε b) {q : ℝ}
    (hq : MeshCost F ε q) : b ≤ q := by
  rcases hq with
    ⟨M, σ, ι, _, _, Nsl, d, J₀, Jb, hJ, Fl, E, G, _, _, _, _, _, _, _, _, _, _, A, rfl⟩ |
    ⟨M, σ, ι, _, _, Nsl, d, J₀, Jb, hJ, Fl, E, G, _, _, _, _, _, _, _, _, _, _, A, rfl⟩
  · exact (h.1 M σ ι Nsl d J₀ Jb hJ Fl E G A).1
  · exact (h.2 M σ ι Nsl d J₀ Jb hJ Fl E G A).1

/-- A lower bound on every realised value count is mesh-forcing (the matrix count is at least
the value count). -/
theorem meshForces_of_cost {F : Family X N Z K s} {ε b : ℝ}
    (h : ∀ q, MeshCost F ε q → b ≤ q) : MeshForces F ε b := by
  refine ⟨?_, ?_⟩
  · intro M σ ι _ _ Nsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    have hv : b ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) :=
      h _ (Or.inl ⟨M, σ, ι, inferInstance, inferInstance, Nsl, d, J₀, Jb, hJ, Fl, E, G,
        inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, inferInstance, inferInstance, inferInstance, A, rfl⟩)
    refine ⟨hv, hv.trans ?_⟩
    exact_mod_cast AdaptiveODELowerBound.Model.worstCost_mono_tree A.tree
      ODELowerBoundExtensions.Release.matrixWeight_value_le
  · intro M σ ι _ _ Nsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    have hv : b ≤ A.tree.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) :=
      h _ (Or.inr ⟨M, σ, ι, inferInstance, inferInstance, Nsl, d, J₀, Jb, hJ, Fl, E, G,
        inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, inferInstance, inferInstance, inferInstance, A, rfl⟩)
    refine ⟨hv, hv.trans ?_⟩
    exact_mod_cast AdaptiveODELowerBound.Model.worstCost_mono_tree A.tree
      (fun c => ODELowerBoundExtensions.Release.matrixWeight_value_le c.1)

/-- A mesh witness of `b` witnesses every smaller bound. -/
theorem MeshWitnesses.mono {F : Family X N Z K s} {τ gbar ε b b' : ℝ}
    (hW : MeshWitnesses F τ gbar ε b) (hb : b' ≤ b) : MeshWitnesses F τ gbar ε b' := by
  refine ⟨hW.inClass, hW.time_eq, ⟨?_, ?_⟩⟩
  · intro M σ ι _ _ Nsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    obtain ⟨h1, h2⟩ := hW.forces.1 M σ ι Nsl d J₀ Jb hJ Fl E G A
    exact ⟨hb.trans h1, hb.trans h2⟩
  · intro M σ ι _ _ Nsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    obtain ⟨h1, h2⟩ := hW.forces.2 M σ ι Nsl d J₀ Jb hJ Fl E G A
    exact ⟨hb.trans h1, hb.trans h2⟩

/-- **Retry protocols over the physical oracle**: mesh-forcing bounds the worst-case value and
matrix counts of every retry solver over `meshOracle F σ ι N d J₀ J_b`. -/
theorem MeshForces.retry {F : Family X N Z K s} {ε b : ℝ} (h : MeshForces F ε b) {M : ℕ}
    (σ : Fin M → Fin K) (ι : Type) [Fintype ι] [DecidableEq ι] (Nsl d : ℕ) {J₀ : X → SysOp N}
    {Jb : X → Fin M → SysOp N} (hJ : PublicSources J₀ Jb) {E G : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : RetrySolver F (meshOracle F σ ι Nsl d J₀ Jb) E G ε) :
    b ≤ A.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      b ≤ A.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := by
  exact h.1 _ σ ι Nsl d J₀ Jb hJ ℂ E G (AdaptiveODELowerBound.Model.retryToTree A ℂ)

/-- **Retry protocols over the call forms of the physical oracle**: mesh-forcing bounds the
worst-case value and matrix counts of every retry solver over
`callFamily (meshOracle F σ ι N d J₀ J_b)`. -/
theorem MeshForces.retry_calls {F : Family X N Z K s} {ε b : ℝ} (h : MeshForces F ε b) {M : ℕ}
    (σ : Fin M → Fin K) (ι : Type) [Fintype ι] [DecidableEq ι] (Nsl d : ℕ) {J₀ : X → SysOp N}
    {Jb : X → Fin M → SysOp N} (hJ : PublicSources J₀ Jb) {E G : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : RetrySolver F (callFamily (meshOracle F σ ι Nsl d J₀ Jb)) E G ε) :
    b ≤ A.prot.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) ∧
      b ≤ A.prot.worstCost (fun c => ODESourceQueryBudget.matrixWeight (fun _ => 1) c.1) := by
  exact h.2 _ σ ι Nsl d J₀ Jb hJ ℂ E G (AdaptiveODELowerBound.Model.retryToTree A ℂ)

/-- **Runs of the released general-mesh solver**: on a family all of whose inputs have a
solution, mesh-forcing bounds the worst-case value and matrix counts of every run
(`ODELowerBoundExtensions.Release.ReleaseRun`, the released four-attempt protocol over
`releaseOracle F R = meshOracle F (stageOf K R)` with `Θ = τ`; the released solver gives such
runs on families with `D = 0`, `ODELowerBoundExtensions.Release.exists_releaseProtocol`; for
released protocols at any parameters see `MeshForces.releaseProtocol`). -/
theorem MeshForces.releaseRun [DecidableEq Z] {F : Family X N Z K s} {ε b : ℝ}
    (h : MeshForces F ε b) {τ gbar : ℝ} (A : ReleaseRun F τ gbar ε)
    (hsol : ∀ x, ∃ sol, F.Solves x sol) :
    b ≤ A.valueQueries ∧ b ≤ A.matrixQueries := by
  exact h.retry (ODELowerBoundExtensions.Release.stageOf K A.R) _ A.slots A.degree
    A.sources_public (A.release.toRetrySolver hsol A.i₀)

/-- **Released protocols of the general-mesh solver at any parameters**: on a family all of whose
inputs have a solution, mesh-forcing bounds the worst-case value and matrix counts of every
released four-attempt protocol (`ODELowerBoundExtensions.Release.ReleaseProtocol`) over
`releaseOracle F R = meshOracle F (stageOf K R)` with public source interfaces, read by the clean
readout `endpointReadout 1 i₀` (`ODELowerBoundExtensions.Release.ReleaseProtocol.toRetrySolver`).
The bounds hold at every released protocol of the general-mesh solver at any parameters `Θ`,
`ell`, `g`, so also on the positive semidefinite and homogeneous families, where `ReleaseRun`
(which fixes `Θ = τ`) does not apply. -/
theorem MeshForces.releaseProtocol [DecidableEq Z] {F : Family X N Z K s} {ε b : ℝ}
    (h : MeshForces F ε b) {R : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {Nsl d : ℕ}
    {J₀ : X → SysOp N} {Jb : X → Fin (K * R) → SysOp N} (hJ : PublicSources J₀ Jb)
    {p : ODERepeatProtocol.Protocol (releaseOracle F R ι Nsl d J₀ Jb) (EuclideanSpace ℂ N)}
    {Θ ell g : ℝ} (hp : ReleaseProtocol F R ι Nsl d J₀ Jb p Θ ell g ε)
    (hsol : ∀ x, ∃ sol, F.Solves x sol) (i₀ : N) :
    b ≤ p.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      b ≤ p.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) :=
  h.retry (stageOf K R) ι Nsl d hJ (hp.toRetrySolver hsol i₀)

end

end PhysicalODELowerBound.Mesh
