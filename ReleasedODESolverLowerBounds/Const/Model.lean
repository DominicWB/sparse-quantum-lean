import PhysicalODELowerBound.Const.Model
import DeferredMeasurementLowerBounds.Corollaries.ODESolver

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Measured solvers over the constant-coefficient physical oracle

Manuscript Section `odel:sec:main` (access with inverses and controls, success flag of probability
at least `2/3`, conditional trace distance `ε`, worst-case query bound; the lower bounds apply to
Theorems `ode:thm:main` and `ode:thm:time`) and the end of the proof of Lemma `hsl:lem:precision`
(purification and deferred measurement); Theorem `ode:thm:main`.

The measured solvers (`DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver`) here call the
physical oracle of the released constant-coefficient solver
(`ConstantODELowerBound.Oracle.constOracle F ι N_m T_sl d J₀ J_b`, any branch register, mesh
size, slot count, degree and public source interfaces), in the two access shapes of
`PhysicalODELowerBound.Const.ConstForces`.

* `MeasuredConstForces F ε b`: every such measured solver, in both access shapes, makes at least
  `b` value calls and at least `b` matrix calls in the worst case over all transcripts.
* `MeasuredConstWitnesses F τ ḡ ε b`: `F` is in the class and measured-forces `b`.
* `MeasuredConstCost F ε q`: `q` is the worst-case value count of some measured solver over the
  oracle or its call forms; `MeasuredConstForces.le_cost`, `MeasuredConstWitnesses.mono`.
-/

namespace ReleasedODESolverLowerBounds.Const

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open ODELowerBoundExtensions.Release (SysOp)
open ConstantODELowerBound.Oracle (constOracle PublicConstSources)
open AdaptiveODELowerBound.Access (callFamily)
open DeferredMeasurementLowerBounds.Corollaries (MeasuredSolver)

-- The released solver's physical workspace is a nested register product.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- **`F` forces `b` on measured solvers over the constant-coefficient physical oracle at
accuracy `ε`**: every measured solver over `constOracle F ι N_m T_sl d J₀ J_b` (any branch
register, mesh size, slot count, degree, public source interfaces, output and garbage spaces),
and every measured solver over its call forms, makes at least `b` value calls and at least `b`
matrix calls in the worst case over all transcripts. -/
def MeasuredConstForces (F : Family X N Z 1 s) (ε b : ℝ) : Prop :=
  (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Nm Tsl d : ℕ) (J₀ Jb : X → SysOp N),
    PublicConstSources J₀ Jb →
    ∀ (E G : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (A : MeasuredSolver F (constOracle F ι Nm Tsl d J₀ Jb) E G ε),
      b ≤ A.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
        b ≤ A.alg.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) ∧
  (∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Nm Tsl d : ℕ) (J₀ Jb : X → SysOp N),
    PublicConstSources J₀ Jb →
    ∀ (E G : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
      [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (A : MeasuredSolver F (callFamily (constOracle F ι Nm Tsl d J₀ Jb)) E G ε),
      b ≤ A.alg.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1) ∧
        b ≤ A.alg.worstCost (fun c => ODESourceQueryBudget.matrixWeight (fun _ => 1) c.1))

/-- **`F` witnesses `b` on measured solvers over the constant-coefficient physical oracle** for
`(τ, ḡ, ε)`: `F` is in the class with `η = 1`, `T = τ` and `g ≤ ḡ`, and measured-forces `b`. -/
structure MeasuredConstWitnesses (F : Family X N Z 1 s) (τ gbar ε b : ℝ) : Prop where
  inClass : F.InClass 1 gbar
  time_eq : F.T = τ
  forces : MeasuredConstForces F ε b

/-- **A realised worst-case value count of a measured solver over the constant-coefficient
physical oracle** (any branch register, mesh size, slot count, degree and public source
interfaces) or over its call forms. -/
def MeasuredConstCost (F : Family X N Z 1 s) (ε q : ℝ) : Prop :=
  (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Nm Tsl d : ℕ) (J₀ Jb : X → SysOp N)
      (_ : PublicConstSources J₀ Jb) (E G : Type)
      (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (_ : CompleteSpace E)
      (_ : FiniteDimensional ℂ E) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G)
      (_ : CompleteSpace G) (A : MeasuredSolver F (constOracle F ι Nm Tsl d J₀ Jb) E G ε),
      q = A.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight)) ∨
  (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (Nm Tsl d : ℕ) (J₀ Jb : X → SysOp N)
      (_ : PublicConstSources J₀ Jb) (E G : Type)
      (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (_ : CompleteSpace E)
      (_ : FiniteDimensional ℂ E) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G)
      (_ : CompleteSpace G)
      (A : MeasuredSolver F (callFamily (constOracle F ι Nm Tsl d J₀ Jb)) E G ε),
      q = A.alg.worstCost (fun c => ODESourceQueryBudget.matrixWeight valueWeight c.1))

/-- The worst-case value count of a measured solver over the oracle is a realised measured
count. -/
theorem MeasuredConstCost.of_measured {F : Family X N Z 1 s} {ε : ℝ} (ι : Type) [Fintype ι]
    [DecidableEq ι] (Nm Tsl d : ℕ) {J₀ Jb : X → SysOp N} (hJ : PublicConstSources J₀ Jb)
    {E G : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : MeasuredSolver F (constOracle F ι Nm Tsl d J₀ Jb) E G ε) :
    MeasuredConstCost F ε (A.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight)) :=
  Or.inl ⟨ι, inferInstance, inferInstance, Nm, Tsl, d, J₀, Jb, hJ, E, G, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, A,
    rfl⟩

/-- Measured forcing is a lower bound on every realised measured value count. -/
theorem MeasuredConstForces.le_cost {F : Family X N Z 1 s} {ε b : ℝ}
    (h : MeasuredConstForces F ε b) {q : ℝ} (hq : MeasuredConstCost F ε q) : b ≤ q := by
  rcases hq with ⟨ι, _, _, Nm, Tsl, d, J₀, Jb, hJ, E, G, _, _, _, _, _, _, _, A, rfl⟩ |
    ⟨ι, _, _, Nm, Tsl, d, J₀, Jb, hJ, E, G, _, _, _, _, _, _, _, A, rfl⟩
  · exact (h.1 ι Nm Tsl d J₀ Jb hJ E G A).1
  · exact (h.2 ι Nm Tsl d J₀ Jb hJ E G A).1

/-- A measured witness of `b` witnesses every smaller bound. -/
theorem MeasuredConstWitnesses.mono {F : Family X N Z 1 s} {τ gbar ε b b' : ℝ}
    (hW : MeasuredConstWitnesses F τ gbar ε b) (hb : b' ≤ b) :
    MeasuredConstWitnesses F τ gbar ε b' :=
  ⟨hW.inClass, hW.time_eq,
    ⟨fun ι _ _ Nm Tsl d J₀ Jb hJ E G _ _ _ _ _ _ _ A =>
      (hW.forces.1 ι Nm Tsl d J₀ Jb hJ E G A).imp (le_trans hb) (le_trans hb),
    fun ι _ _ Nm Tsl d J₀ Jb hJ E G _ _ _ _ _ _ _ A =>
      (hW.forces.2 ι Nm Tsl d J₀ Jb hJ E G A).imp (le_trans hb) (le_trans hb)⟩⟩

end

end ReleasedODESolverLowerBounds.Const
