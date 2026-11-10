import AdaptiveODELowerBound.Model.Solver
import ConstantODELowerBound.Runs

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Forcing over the constant-coefficient physical oracle

Section `odel:sec:main` (access with inverses and controls; success flag of probability at least
`2/3`, conditional trace distance `ε`; "the lower bounds apply to the upper bounds of the preceding
section") and Theorem `ode:thm:main`.

The adaptive solvers (`AdaptiveODELowerBound.Model.TreeSolver`) here call the physical oracle of
the released constant-coefficient solver `SparseHamiltonian.ODECompleteEndpoint.solver`, run on
the stage-`0` data of a one-stage family `F` (`ConstantODELowerBound.Oracle.constOracle F ι N_m
T_sl d J₀ J_b`, any branch register, mesh size, slot count, degree and public source interfaces
`ConstantODELowerBound.Oracle.PublicConstSources`), in one of two access shapes: the oracle family
itself (with inverse calls) or its call forms `AdaptiveODELowerBound.Access.callFamily` (plain,
inverse, controlled and controlled-inverse calls). The counts are those of
`ConstantODELowerBound.Herald`: value calls (`ODESourceQueryBudget.matrixWeight valueWeight`) and
matrix calls (`matrixWeight (fun _ => 1)`), every call form weighted as its label.

Only one-stage (constant-coefficient) families are concerned: the time-dependent hard families
(the joint family, the homogeneous variant, the padded joint families) are not
constant-coefficient equations (Section `odel:sec:main` and Proposition `odel:rem:homogeneous`).

* `ConstForces F ε b`, `ConstWitnesses F τ ḡ ε b`, `ConstCost F ε q`: as `Mesh.MeshForces`,
  `Mesh.MeshWitnesses`, `Mesh.MeshCost` for this oracle; `ConstForces.le_cost`,
  `constForces_of_cost`, `ConstWitnesses.mono`.
* `ConstForces.retry`, `ConstForces.retry_calls`: retry protocols over the oracle and its call
  forms; `ConstForces.constRun`: every run of the released constant-coefficient solver
  (`ConstantODELowerBound.Runs.ConstRun`, any split bounds `η_H`, `η_D`, so also on the
  positive semidefinite families) on a family all of whose inputs are solvable. The
  retry-protocol forms of the family statements of this library are these lemmas applied to
  their `ConstForces` conclusions.
* `ConstCost.of_tree`: the worst-case value count of a solver over the oracle itself is a
  realised count, so the max forms over realised counts contain the max forms of
  `ConstantODELowerBound` over explicitly given solvers (`herald_max_const_tree_of_const`,
  `psd_max_const_tree_of_const`).
-/

namespace PhysicalODELowerBound.Const

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit SparseLinearSystems.Protocol
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open ODELowerBoundExtensions.Release (SysOp RetrySolver)
open ConstantODELowerBound.Oracle (constOracle PublicConstSources)
open ConstantODELowerBound.Runs (ConstRun)
open AdaptiveODELowerBound.Model (TreeSolver)
open AdaptiveODELowerBound.Access (callFamily)

-- The released solver's physical workspace is a nested register product.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- **`F` forces `b` on the constant-coefficient physical oracle at accuracy `ε`**: every
adaptive solver over `constOracle F ι N_m T_sl d J₀ J_b` (any branch register, mesh size, slot
count, degree, public source interfaces, flag, output and garbage spaces), and every adaptive
solver over its call forms (plain, inverse, controlled and controlled-inverse calls), makes at
least `b` value calls and at least `b` matrix calls in the worst case over all transcripts. -/
def ConstForces (F : Family X N Z 1 s) (ε b : ℝ) : Prop :=
  (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Nm Tsl d : ℕ) (J₀ Jb : X → SysOp N),
    PublicConstSources J₀ Jb →
    ∀ (Fl E G : Type) [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
      [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (A : TreeSolver F (constOracle F ι Nm Tsl d J₀ Jb) Fl E G ε),
      b ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
        b ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) ∧
  (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Nm Tsl d : ℕ) (J₀ Jb : X → SysOp N),
    PublicConstSources J₀ Jb →
    ∀ (Fl E G : Type) [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
      [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (A : TreeSolver F (callFamily (constOracle F ι Nm Tsl d J₀ Jb)) Fl E G ε),
      b ≤ A.tree.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) ∧
        b ≤ A.tree.worstCost (fun c => ODESourceQueryBudget.matrixWeight (fun _ => 1) c.1))

/-- **`F` witnesses `b` on the constant-coefficient physical oracle** for `(τ, ḡ, ε)`: `F` is in
the class with `η = 1`, `T = τ` and `g ≤ ḡ`, and forces `b` on that oracle at accuracy `ε`. -/
structure ConstWitnesses (F : Family X N Z 1 s) (τ gbar ε b : ℝ) : Prop where
  inClass : F.InClass 1 gbar
  time_eq : F.T = τ
  forces : ConstForces F ε b

/-- **A realised worst-case value count on the constant-coefficient physical oracle**: `q` is the
worst-case value count of some adaptive solver of `F` at accuracy `ε` over the oracle (any
branch register, mesh size, slot count, degree and public source interfaces) or over its call
forms. -/
def ConstCost (F : Family X N Z 1 s) (ε q : ℝ) : Prop :=
  (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Nm Tsl d : ℕ) (J₀ Jb : X → SysOp N)
      (_ : PublicConstSources J₀ Jb) (Fl E G : Type)
      (_ : NormedAddCommGroup Fl) (_ : InnerProductSpace ℂ Fl) (_ : CompleteSpace Fl)
      (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (_ : CompleteSpace E)
      (_ : FiniteDimensional ℂ E) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G)
      (_ : CompleteSpace G) (A : TreeSolver F (constOracle F ι Nm Tsl d J₀ Jb) Fl E G ε),
      q = A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight)) ∨
  (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Nm Tsl d : ℕ) (J₀ Jb : X → SysOp N)
      (_ : PublicConstSources J₀ Jb) (Fl E G : Type)
      (_ : NormedAddCommGroup Fl) (_ : InnerProductSpace ℂ Fl) (_ : CompleteSpace Fl)
      (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (_ : CompleteSpace E)
      (_ : FiniteDimensional ℂ E) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G)
      (_ : CompleteSpace G)
      (A : TreeSolver F (callFamily (constOracle F ι Nm Tsl d J₀ Jb)) Fl E G ε),
      q = A.tree.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1))

/-- **The counts of the max forms of `ConstantODELowerBound` are realised counts**: the
worst-case value count of an adaptive solver over the physical oracle itself (as in
`ConstantODELowerBound.Herald.herald_max_const_tree` and
`ConstantODELowerBound.Psd.psd_max_const_tree`) is a `ConstCost`. -/
theorem ConstCost.of_tree {F : Family X N Z 1 s} {ε : ℝ} (ι : Type) [Fintype ι] [DecidableEq ι]
    (Nm Tsl d : ℕ) {J₀ Jb : X → SysOp N} (hJ : PublicConstSources J₀ Jb) {Fl E G : Type}
    [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G]
    [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : TreeSolver F (constOracle F ι Nm Tsl d J₀ Jb) Fl E G ε) :
    ConstCost F ε (A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight)) :=
  Or.inl ⟨ι, inferInstance, inferInstance, Nm, Tsl, d, J₀, Jb, hJ, Fl, E, G, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, A, rfl⟩

/-- Forcing on the constant-coefficient oracle is a lower bound on every realised value count. -/
theorem ConstForces.le_cost {F : Family X N Z 1 s} {ε b : ℝ} (h : ConstForces F ε b) {q : ℝ}
    (hq : ConstCost F ε q) : b ≤ q := by
  rcases hq with ⟨ι, _, _, Nm, Tsl, d, J₀, Jb, hJ, Fl, E, G, _, _, _, _, _, _, _, _, _, _, A, rfl⟩ |
    ⟨ι, _, _, Nm, Tsl, d, J₀, Jb, hJ, Fl, E, G, _, _, _, _, _, _, _, _, _, _, A, rfl⟩
  · exact (h.1 ι Nm Tsl d J₀ Jb hJ Fl E G A).1
  · exact (h.2 ι Nm Tsl d J₀ Jb hJ Fl E G A).1

/-- A lower bound on every realised value count is forcing on the constant-coefficient oracle
(the matrix count is at least the value count). -/
theorem constForces_of_cost {F : Family X N Z 1 s} {ε b : ℝ}
    (h : ∀ q, ConstCost F ε q → b ≤ q) : ConstForces F ε b := by
  have hw := ODELowerBoundExtensions.Release.matrixWeight_value_le
  refine ⟨?_, ?_⟩
  · intro ι _ _ Nm Tsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    have hv : b ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) :=
      h _ (ConstCost.of_tree ι Nm Tsl d hJ A)
    refine ⟨hv, hv.trans ?_⟩
    exact_mod_cast AdaptiveODELowerBound.Model.worstCost_mono_tree A.tree hw
  · intro ι _ _ Nm Tsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    have hv : b ≤ A.tree.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) :=
      h _ (Or.inr ⟨ι, inferInstance, inferInstance, Nm, Tsl, d, J₀, Jb, hJ, Fl, E, G,
        inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, inferInstance, inferInstance, inferInstance, A, rfl⟩)
    refine ⟨hv, hv.trans ?_⟩
    exact_mod_cast AdaptiveODELowerBound.Model.worstCost_mono_tree A.tree (fun c => hw c.1)

/-- A witness of `b` on the constant-coefficient oracle witnesses every smaller bound. -/
theorem ConstWitnesses.mono {F : Family X N Z 1 s} {τ gbar ε b b' : ℝ}
    (hW : ConstWitnesses F τ gbar ε b) (hb : b' ≤ b) : ConstWitnesses F τ gbar ε b' := by
  refine ⟨hW.inClass, hW.time_eq, ⟨?_, ?_⟩⟩
  · intro ι _ _ Nm Tsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    obtain ⟨h1, h2⟩ := hW.forces.1 ι Nm Tsl d J₀ Jb hJ Fl E G A
    exact ⟨hb.trans h1, hb.trans h2⟩
  · intro ι _ _ Nm Tsl d J₀ Jb hJ Fl E G _ _ _ _ _ _ _ _ _ _ A
    obtain ⟨h1, h2⟩ := hW.forces.2 ι Nm Tsl d J₀ Jb hJ Fl E G A
    exact ⟨hb.trans h1, hb.trans h2⟩

/-- **Retry protocols over the constant-coefficient oracle**: forcing bounds the worst-case value
and matrix counts of every retry solver over `constOracle F ι N_m T_sl d J₀ J_b`. -/
theorem ConstForces.retry {F : Family X N Z 1 s} {ε b : ℝ} (h : ConstForces F ε b) (ι : Type)
    [Fintype ι] [DecidableEq ι] (Nm Tsl d : ℕ) {J₀ Jb : X → SysOp N}
    (hJ : PublicConstSources J₀ Jb) {E G : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (A : RetrySolver F (constOracle F ι Nm Tsl d J₀ Jb) E G ε) :
    b ≤ A.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      b ≤ A.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) :=
  h.1 ι Nm Tsl d J₀ Jb hJ ℂ E G (AdaptiveODELowerBound.Model.retryToTree A ℂ)

/-- **Retry protocols over the call forms of the constant-coefficient oracle**: forcing bounds
the worst-case value and matrix counts of every retry solver over
`callFamily (constOracle F ι N_m T_sl d J₀ J_b)`. -/
theorem ConstForces.retry_calls {F : Family X N Z 1 s} {ε b : ℝ} (h : ConstForces F ε b)
    (ι : Type) [Fintype ι] [DecidableEq ι] (Nm Tsl d : ℕ) {J₀ Jb : X → SysOp N}
    (hJ : PublicConstSources J₀ Jb) {E G : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G] (A : RetrySolver F (callFamily (constOracle F ι Nm Tsl d J₀ Jb)) E G ε) :
    b ≤ A.prot.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) ∧
      b ≤ A.prot.worstCost (fun c => ODESourceQueryBudget.matrixWeight (fun _ => 1) c.1) :=
  h.2 ι Nm Tsl d J₀ Jb hJ ℂ E G (AdaptiveODELowerBound.Model.retryToTree A ℂ)

/-- **Runs of the released constant-coefficient solver**: on a family all of whose inputs have a
solution, forcing bounds the worst-case value and matrix counts of every run
(`ConstantODELowerBound.Runs.ConstRun`). -/
theorem ConstForces.constRun {F : Family X N Z 1 s} {ε b : ℝ} (h : ConstForces F ε b)
    {τ gbar etaH etaD : ℝ} (A : ConstRun F τ gbar ε etaH etaD)
    (hsol : ∀ x, ∃ sol, F.Solves x sol) :
    b ≤ A.valueQueries ∧ b ≤ A.matrixQueries :=
  h.retry (ConstantODELowerBound.Solver.RunIndex F τ gbar ε)
    (ConstantODELowerBound.Solver.runMesh F τ gbar ε) A.slots A.degree A.sources_public
    (A.release.toRetrySolver hsol A.i₀)

end

end PhysicalODELowerBound.Const
