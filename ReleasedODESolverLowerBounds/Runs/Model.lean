import ODELowerBoundExtensions.Release.Theta
import PhysicalODELowerBound.Mesh.Model

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Runs of the released general-mesh solver with split energy bounds

Manuscript Theorem `ode:thm:time` (line 2879) and Section `odel:sec:main`, lines 3678-3679 ("The
lower bounds thus apply to Theorems `ode:thm:main` and `ode:thm:time`"); the refined upper bound
with `Θ = τ_H + τ_D ℓ` (lines 3721-3730).

The released general-mesh solver `TimeDependentExtensions.ODE.solver` takes split energy bounds
`η_H`, `η_D` on the Hermitian and dissipative parts of every generator piece and certifies its
protocol with `Θ = theta(τ η_H, τ η_D, ratio ḡ, accuracy ε) = τ η_H + τ η_D ℓ` (`meshTheta`).
`ODELowerBoundExtensions.Release.ReleaseRun` is the run structure with `Θ = τ`, i.e.
`(η_H, η_D) = (1, 0)` (`meshTheta_one_zero`). The package obtains such runs from the solver only
for families with `D = 0` (`ODELowerBoundExtensions.Release.exists_releaseProtocol`, whose
hypotheses ask for a skew-Hermitian generator). On the positive semidefinite families of Theorem
`odel:thm:psd` (`D ⪰ 0`) and on the homogeneous family of Remark `odel:rem:homogeneous` (a
dissipative stage), the solver's hypotheses hold with `η_D = 1`, and its certified
`Θ = τ η_H + τ ℓ` (`meshTheta_eq`) is at least `τ ℓ > τ`; these runs are therefore stated as
`MeshRun`s.

* `MeshRun F τ ḡ ε η_H η_D`: the run structure of `ReleaseRun` with `Θ = meshTheta τ ḡ ε η_H η_D`
  (the counterpart, for the general-mesh oracle, of `ConstantODELowerBound.Runs.ConstRun`); its
  counts `matrixQueries`, `valueQueries` and the released upper bound `matrixQueries_le`.
* `MeshRun.ofReleaseRun`, `MeshRun.toReleaseRun`: `ReleaseRun` is exactly `MeshRun … 1 0`.
* `meshForces_meshRun`, `meshCost_meshRun`: every lower bound over the general-mesh physical
  oracle (`PhysicalODELowerBound.Mesh.MeshForces`) holds at every run, and the value count of a
  run is a realised count, on a family all of whose inputs are solvable. The first is
  `PhysicalODELowerBound.Mesh.MeshForces.releaseProtocol` (released protocols at any `Θ`) read
  at the run's protocol.
-/

namespace ReleasedODESolverLowerBounds.Runs

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE
open NativeSparseBlockEncoding OracleCircuit TimeDependentExtensions
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open ODELowerBoundExtensions.Release (ReleaseRun ReleaseProtocol releaseOracle refineData
  releaseLog PublicSources SysOp)
open PhysicalODELowerBound.Mesh (MeshForces MeshCost)

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

/-- **The released `Θ` with split energy bounds**: `theta(τ η_H, τ η_D, ratio ḡ, accuracy ε)`,
that is `τ η_H + τ η_D ℓ` with `ℓ = releaseLog ḡ ε`. -/
def meshTheta (τ gbar ε etaH etaD : ℝ) : ℝ :=
  ImprovedODEQueryBudget.theta (τ * etaH) (τ * etaD) (TimeDependentODE.ratio gbar)
    (TimeDependentODE.accuracy ε)

/-- With `η_H = 1`, `η_D = 0` the released `Θ` is `τ`. -/
theorem meshTheta_one_zero (τ gbar ε : ℝ) : meshTheta τ gbar ε 1 0 = τ := by
  unfold meshTheta
  rw [mul_one, mul_zero, ImprovedODEQueryBudget.theta_zero_dissipation]

/-- The released `Θ` is `τ η_H + τ η_D ℓ`. -/
theorem meshTheta_eq (τ gbar ε etaH etaD : ℝ) :
    meshTheta τ gbar ε etaH etaD = τ * etaH + τ * etaD * releaseLog gbar ε := by
  unfold meshTheta ImprovedODEQueryBudget.theta releaseLog
  ring

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {K s : ℕ}

/-- **A run of the released general-mesh solver with split energy bounds** `η_H`, `η_D` on the
family `F` at `(τ, ḡ, ε)`: a system index for the clean readout, a refinement `R > 0`, a slot
count, a degree, public source interfaces and a four-attempt protocol over the release's physical
oracle on the `R`-fold refinement with spectator index `Index (refineData F.data R) τ ḡ ε`,
carrying the released complete certificate for every input with `Θ = meshTheta τ ḡ ε η_H η_D`,
`ℓ = releaseLog ḡ ε` and `g = ratio ḡ`. -/
structure MeshRun (F : Family X N Z K s) (τ gbar ε etaH etaD : ℝ) where
  /-- A system index, the clean garbage register of the readout `endpointReadout 1 i₀`. -/
  i₀ : N
  /-- The refinement of the stages. -/
  R : ℕ
  R_pos : 0 < R
  /-- The number of slots of the SELECT. -/
  slots : ℕ
  /-- A degree for which the released certificate holds. -/
  degree : ℕ
  /-- The initial-state interface. -/
  J₀ : X → SysOp N
  /-- The forcing interface on the refined mesh. -/
  Jb : X → Fin (K * R) → SysOp N
  /-- The source interfaces are public (unitary and input-independent). -/
  sources_public : PublicSources J₀ Jb
  /-- A four-attempt protocol of the released form. -/
  prot : ODERepeatProtocol.Protocol
    (releaseOracle F R (TimeDependentODE.Index (refineData F.data R) τ gbar ε) slots degree J₀ Jb)
    (EuclideanSpace ℂ N)
  /-- The released complete certificate for every input, with the split-bound `Θ`. -/
  release : ReleaseProtocol F R (TimeDependentODE.Index (refineData F.data R) τ gbar ε) slots
    degree J₀ Jb prot (meshTheta τ gbar ε etaH etaD) (releaseLog gbar ε)
    (TimeDependentODE.ratio gbar) ε

variable {F : Family X N Z K s} {τ gbar ε etaH etaD : ℝ}

/-- The worst-case number of matrix queries of a run (row, column and value calls, inverses
included, over all transcripts). -/
def MeshRun.matrixQueries (A : MeshRun F τ gbar ε etaH etaD) : ℕ :=
  A.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))

/-- The worst-case number of value queries of a run. -/
def MeshRun.valueQueries (A : MeshRun F τ gbar ε etaH etaD) : ℕ :=
  A.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight)

/-- A run makes at most as many value queries as matrix queries. -/
theorem MeshRun.valueQueries_le (A : MeshRun F τ gbar ε etaH etaD) :
    A.valueQueries ≤ A.matrixQueries :=
  ODELowerBoundExtensions.Release.worstCost_mono A.prot fun l => by
    rcases l with q | b
    · cases q <;> simp [ODESourceQueryBudget.matrixWeight, valueWeight]
    · simp [ODESourceQueryBudget.matrixWeight]

/-- **The released query bound of a run**: on an input with a solution, the worst-case number of
matrix queries is at most `1274019840 · ratio ḡ · queryShape(s, Θ, ℓ)`. -/
theorem MeshRun.matrixQueries_le (A : MeshRun F τ gbar ε etaH etaD) (x : X)
    (sol : ℝ → EuclideanSpace ℂ N) (hs : F.Solves x sol) :
    (A.matrixQueries : ℝ) ≤ 1274019840 * TimeDependentODE.ratio gbar *
      ImprovedODEQueryBudget.queryShape s (meshTheta τ gbar ε etaH etaD) (releaseLog gbar ε) :=
  A.release.worstCost_le x sol hs

/-- **A release run is a run with `η_H = 1`, `η_D = 0`.** -/
def MeshRun.ofReleaseRun (A : ReleaseRun F τ gbar ε) :
    MeshRun F τ gbar ε 1 0 :=
  ⟨A.i₀, A.R, A.R_pos, A.slots, A.degree, A.J₀, A.Jb, A.sources_public, A.prot,
    (meshTheta_one_zero τ gbar ε).symm ▸ A.release⟩

/-- **A run with `η_H = 1`, `η_D = 0` is a release run.** -/
def MeshRun.toReleaseRun (A : MeshRun F τ gbar ε 1 0) : ReleaseRun F τ gbar ε :=
  ⟨A.i₀, A.R, A.R_pos, A.slots, A.degree, A.J₀, A.Jb, A.sources_public, A.prot,
    by have h := A.release; rwa [meshTheta_one_zero] at h⟩

/-- The counts of a release run are those of its run form. -/
theorem MeshRun.ofReleaseRun_queries (A : ReleaseRun F τ gbar ε) :
    (MeshRun.ofReleaseRun A).matrixQueries = A.matrixQueries ∧
      (MeshRun.ofReleaseRun A).valueQueries = A.valueQueries :=
  ⟨rfl, rfl⟩

/-- **The lower bounds over the general-mesh physical oracle hold at every run**, on a family
all of whose inputs have a solution (`PhysicalODELowerBound.Mesh.MeshForces.releaseProtocol` at
the run's released protocol). -/
theorem meshForces_meshRun {b : ℝ} (h : MeshForces F ε b) (A : MeshRun F τ gbar ε etaH etaD)
    (hsol : ∀ x, ∃ sol, F.Solves x sol) : b ≤ A.valueQueries ∧ b ≤ A.matrixQueries :=
  h.releaseProtocol A.sources_public A.release hsol A.i₀

/-- The value count of a run is a realised count over the general-mesh physical oracle, on a
family all of whose inputs have a solution. -/
theorem meshCost_meshRun (A : MeshRun F τ gbar ε etaH etaD)
    (hsol : ∀ x, ∃ sol, F.Solves x sol) : MeshCost F ε A.valueQueries := by
  have h := MeshCost.of_tree (ODELowerBoundExtensions.Release.stageOf K A.R)
    (TimeDependentODE.Index (refineData F.data A.R) τ gbar ε) A.slots A.degree A.sources_public
    (AdaptiveODELowerBound.Model.retryToTree (A.release.toRetrySolver hsol A.i₀) ℂ)
  rwa [AdaptiveODELowerBound.Model.worstCost_retryToTree] at h

end

end ReleasedODESolverLowerBounds.Runs
