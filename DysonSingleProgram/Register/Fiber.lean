import ODELowerBoundExtensions.Release.Registers
import SparseLowerBounds.ODE.Model
import SparseHamiltonian.MultiOracleTransport
import GeneralODE.Block.Programs
import SparseLowerBounds.Query.PhaseCircuit
import SparseLowerBounds.Helpers.Adaptive.Access.Wrappers

set_option autoImplicit false

/-!
# Spectator registers for oracle programs

Manuscript lines 4105-4109 (Section `odel:sec:main`, the access model used by Lemma
`odel:lem:dyson`): access is through the reversible value oracle and the row/column locators with
a coherent time address; known unitaries, arithmetic and specified known state preparations are
free.

In the single-program class of the ODE lower bounds (`SparseLowerBounds.ODE.Solver`) the branch
register `ι` of `Family.access ι` is a spectator: the oracle does not touch it. This module
collects the facts about such untouched registers used by the single Dyson program.

* `fiberOracle J O`: the oracle family `O` acting on the last factor of `ℂ^J ⊗ W`, the register
  `J` an untouched spectator (`SparseLowerBounds.Joint.fiber`).
* `spectate J`: the lift of a program over `O` to a program over `fiberOracle J O` along the
  block-diagonal star-algebra homomorphism `U ↦ 1 ⊗ U` (`MultiOracleCircuit.Program.mapHom`,
  `GeneralODE.Registers.diagHom`; the constant block diagonal is the homogeneous spectator,
  `SparseLowerBounds.Helpers.Adaptive.Access.diagonal_const_eq_fiber`); it has the same calls.
  Unitarity of a homogeneous spectator is `SparseLowerBounds.PhaseCircuit.isUnitary_fiber`.
* `reflatten`: two nested spectators are one spectator on the product register
  (`ODELowerBoundExtensions.Release.fiber_fiber`, the fixed flattening `jointFlatten`).
* `accessLayout`, `toAccess`: the sampled-time access of the ODE lower-bound class with branch
  register `ι × J` is the access with branch register `ι` and spectator `J`, up to a fixed
  relabelling of the computational basis; every program over the spectator form is a program over
  `SparseLowerBounds.ODE.Family.access (ι × J)` with the same calls.
-/

namespace DysonSingleProgram.Register

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit NativeSparseBlockEncoding
open scoped InnerProduct

section Generic

variable {X L W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- **The spectator oracle**: `O l x` on the last factor of `ℂ^J ⊗ W`. -/
abbrev fiberOracle (J : Type*) [Fintype J] (O : L → X → W →L[ℂ] W) :
    L → X → Joint J W →L[ℂ] Joint J W :=
  fun l x => Joint.fiber (fun _ => O l x)

/-- **Spectator lift of a program**: fixed unitaries `U ↦ 1 ⊗ U`, calls kept; the program lift
`MultiOracleCircuit.Program.mapHom` along the block-diagonal star-algebra homomorphism
`GeneralODE.Registers.diagHom`. -/
def spectate (J : Type*) [Fintype J] {O : L → X → W →L[ℂ] W} :
    MultiOracleCircuit.Program O → MultiOracleCircuit.Program (fiberOracle J O) :=
  MultiOracleCircuit.Program.mapHom (O' := fiberOracle J O) (GeneralODE.Registers.diagHom J W) id

variable {J : Type*} [Fintype J] {O : L → X → W →L[ℂ] W}

/-- The lifted program evaluates to `1 ⊗ p(x)`. -/
@[simp] theorem eval_spectate (p : MultiOracleCircuit.Program O) (x : X) :
    (spectate J p).eval x = Joint.fiber (fun _ => p.eval x) := by
  have h := MultiOracleCircuit.Program.eval_mapHom (O' := fiberOracle J O)
    (GeneralODE.Registers.diagHom J W) id
    (fun l x => (Helpers.Adaptive.Access.diagonal_const_eq_fiber (ι := J) (O l x)).symm) p x
  exact h.trans (Helpers.Adaptive.Access.diagonal_const_eq_fiber (ι := J) (p.eval x))

/-- The lifted program has the same weighted cost. -/
@[simp] theorem cost_spectate (p : MultiOracleCircuit.Program O) (w : L → ℕ) :
    (spectate J p).cost w = p.cost w :=
  MultiOracleCircuit.Program.cost_mapHom (O' := fiberOracle J O)
    (GeneralODE.Registers.diagHom J W) id p w

/-- The lifted program has the same number of calls. -/
@[simp] theorem count_spectate (p : MultiOracleCircuit.Program O) :
    (spectate J p).count = p.count :=
  MultiOracleCircuit.Program.count_mapHom (O' := fiberOracle J O)
    (GeneralODE.Registers.diagHom J W) id p

/-- The lifted program has the same calls of every label. -/
@[simp] theorem labelCount_spectate [DecidableEq L] (p : MultiOracleCircuit.Program O) (l : L) :
    (spectate J p).labelCount l = p.labelCount l :=
  MultiOracleCircuit.Program.cost_mapHom (O' := fiberOracle J O)
    (GeneralODE.Registers.diagHom J W) id p _

end Generic

section Flatten

variable {X L W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  {O : L → X → W →L[ℂ] W}

/-- **Two nested spectators are one**: a program over `fiberOracle Ω₁ (fiberOracle Ω₂ O)`
read in the flattened coordinates `ℂ^{Ω₁ × Ω₂} ⊗ W` (`jointFlatten`), with the same calls. -/
def reflatten (Ω₁ Ω₂ : Type) [Fintype Ω₁] [Fintype Ω₂]
    (p : MultiOracleCircuit.Program (fiberOracle Ω₁ (fiberOracle Ω₂ O))) :
    MultiOracleCircuit.Program (fiberOracle (Ω₁ × Ω₂) O) :=
  (p.transport (ODELowerBoundExtensions.Release.jointFlatten Ω₁ Ω₂ W).symm).substitute
    (fun l => .query l)

variable (Ω₁ Ω₂ : Type) [Fintype Ω₁] [Fintype Ω₂]

/-- The flattened program evaluates to the flattened operator. -/
theorem eval_reflatten (p : MultiOracleCircuit.Program (fiberOracle Ω₁ (fiberOracle Ω₂ O)))
    (x : X) :
    (reflatten Ω₁ Ω₂ p).eval x =
      (ODELowerBoundExtensions.Release.jointFlatten Ω₁ Ω₂ W).symm.conjStarAlgEquiv (p.eval x) := by
  unfold reflatten
  rw [MultiOracleCircuit.Program.eval_substitute _ _ (fun l x => by ext Ψ a; rfl),
    MultiOracleCircuit.Program.eval_transport]

/-- Flattening keeps the number of calls. -/
@[simp] theorem count_reflatten
    (p : MultiOracleCircuit.Program (fiberOracle Ω₁ (fiberOracle Ω₂ O))) :
    (reflatten Ω₁ Ω₂ p).count = p.count := by
  unfold reflatten
  rw [MultiOracleCircuit.Program.count_substitute, MultiOracleCircuit.Program.cost_transport]
  exact (MultiOracleCircuit.Program.cost_const p 1).trans (mul_one _)

/-- Flattening keeps the calls of every label. -/
@[simp] theorem labelCount_reflatten [DecidableEq L]
    (p : MultiOracleCircuit.Program (fiberOracle Ω₁ (fiberOracle Ω₂ O))) (l : L) :
    (reflatten Ω₁ Ω₂ p).labelCount l = p.labelCount l := by
  unfold reflatten MultiOracleCircuit.Program.labelCount
  rw [MultiOracleCircuit.Program.cost_substitute]
  exact MultiOracleCircuit.Program.cost_transport _ p _

end Flatten

section Access

open SparseLowerBounds.ODE

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {K s : ℕ}

/-- The fixed relabelling `((i, j), k) ↦ (j, (i, k))` of the branch and time registers. -/
def accessEquiv (ι J : Type*) (K : ℕ) : (ι × J) × Fin K ≃ J × (ι × Fin K) where
  toFun b := (b.1.2, (b.1.1, b.2))
  invFun b := ((b.2.1, b.1), b.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The spectator layout of the sampled-time workspace**:
`Workspace (ι × J) ≃ ℂ^J ⊗ Workspace ι`. -/
def accessLayout (ι J : Type) [Fintype ι] [Fintype J] (N Z : Type*) [Fintype N] [Fintype Z]
    (K : ℕ) : Workspace (ι × J) N Z K ≃ₗᵢ[ℂ] Joint J (Workspace ι N Z K) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ (SparseFlagEmbedding.Space (N × N) Z)
    (accessEquiv ι J K)).trans
    (ODELowerBoundExtensions.Release.jointFlatten J (ι × Fin K)
      (SparseFlagEmbedding.Space (N × N) Z))

/-- **The access with branch register `ι × J` is the access with spectator `J`**. -/
theorem access_prod (ι J : Type) [Fintype ι] [Fintype J] (F : Family X N Z K s) (l : Query)
    (x : X) :
    F.access (ι × J) l x =
      (accessLayout ι J N Z K).symm.conjStarAlgEquiv (Joint.fiber (fun _ => F.access ι l x)) := by
  ext v b
  rfl

/-- **Programs with a spectator are programs over the class's access**: transport along
`accessLayout`, every call kept. -/
def toAccess (ι J : Type) [Fintype ι] [Fintype J] (F : Family X N Z K s)
    (p : MultiOracleCircuit.Program (fiberOracle J (F.access ι))) :
    MultiOracleCircuit.Program (F.access (ι × J)) :=
  (p.transport (accessLayout ι J N Z K).symm).substitute (fun l => .query l)

variable (ι J : Type) [Fintype ι] [Fintype J] (F : Family X N Z K s)

/-- The transported program evaluates to the transported operator. -/
theorem eval_toAccess (p : MultiOracleCircuit.Program (fiberOracle J (F.access ι))) (x : X) :
    (toAccess ι J F p).eval x = (accessLayout ι J N Z K).symm.conjStarAlgEquiv (p.eval x) := by
  unfold toAccess
  rw [MultiOracleCircuit.Program.eval_substitute]
  · exact MultiOracleCircuit.Program.eval_transport _ p x
  · intro l y
    exact access_prod ι J F l y

/-- The transported program has the same number of calls. -/
@[simp] theorem count_toAccess (p : MultiOracleCircuit.Program (fiberOracle J (F.access ι))) :
    (toAccess ι J F p).count = p.count := by
  unfold toAccess
  rw [MultiOracleCircuit.Program.count_substitute, MultiOracleCircuit.Program.cost_transport]
  exact (MultiOracleCircuit.Program.cost_const p 1).trans (mul_one _)

/-- The transported program has the same calls of every label. -/
@[simp] theorem labelCount_toAccess (p : MultiOracleCircuit.Program (fiberOracle J (F.access ι)))
    (l : Query) : (toAccess ι J F p).labelCount l = p.labelCount l := by
  unfold toAccess MultiOracleCircuit.Program.labelCount
  rw [MultiOracleCircuit.Program.cost_substitute]
  exact MultiOracleCircuit.Program.cost_transport _ p _

end Access

end

end DysonSingleProgram.Register
