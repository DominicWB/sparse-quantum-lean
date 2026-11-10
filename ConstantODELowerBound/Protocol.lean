import ConstantODELowerBound.Solution
import ODELowerBoundExtensions.Release.Strip
import AdaptiveODELowerBound.Model.Solver

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Released constant-coefficient protocols as solvers of the class

Manuscript: Section `odel:sec:main` (the output model of the lower bounds: success flag of
probability at least `2/3` on every input, conditional trace distance `ε` from the normalised
solution; "the lower bounds apply to the upper bounds of the preceding section") and Theorem
`ode:thm:main`. The released constant-coefficient solver
`SparseHamiltonian.ODECompleteEndpoint.solver` produces one public circuit family and the
four-attempt protocol `ODECompleteTrial.algorithm` with the complete certificate
`ODECompleteTrial.Certificate` for every input.

* `ConstProtocol F ι Nm Tsl d J₀ Jb p Θ ℓ g ε`: `p` is the released four-attempt protocol of one
  public circuit family over `Oracle.constOracle F ι Nm Tsl d J₀ Jb` that satisfies the released
  complete certificate for every input and every solution (target `x(T)`), with parameters `Θ`,
  `ℓ`, `g`, `ε` (as `ODELowerBoundExtensions.Release.ReleaseProtocol` for the general-mesh
  solver).
* `ConstProtocol.success`, `ConstProtocol.accurate` (the released trace distance read by the
  clean readout `Hamiltonian.endpointReadout 1 i₀`, from the oracle-generic
  `ODELowerBoundExtensions.Release.certificate_densityAccurate`),
  `ConstProtocol.worstCost_le` (at most `1274019840 g · queryShape(s, Θ, ℓ)` matrix queries,
  `Certificate.matrix_queries`), `ConstProtocol.toRetrySolver` and `ConstProtocol.toTreeSolver`
  (the released protocol is a retry solver, hence the adaptive solver `Tree.final`, of the
  family over the released oracle).

`ConstProtocol` is the counterpart, for the oracle `ODEFinalNativeSource.physicalOracle` of
`ODECompleteEndpoint.solver` and its workspace `ODEFinalNativeSource.Physical`, of
`ODELowerBoundExtensions.Release.ReleaseProtocol`, which is stated for the general-mesh oracle
`ODELowerBoundExtensions.Release.releaseOracle` and its workspace `MeshSource.PhysicalSpace`, and
so cannot be reused here. The bodies agree except for the oracle and workspace types and the
parameters (no refinement count `R`; split bounds `η_H`, `η_D` in place of a ratio).
-/

namespace ConstantODELowerBound.Protocol

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open ODELowerBoundExtensions.Release (SysOp RetrySolver)
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveODELowerBound.Model (TreeSolver retryToTree)
open ConstantODELowerBound.Oracle

-- The released solver's physical workspace is a nested register product; instance search and
-- elaboration over its types need the raised `synthInstance.maxSize` and `maxRecDepth`.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- **The released constant-coefficient protocol on a one-stage family**: `p` is the
four-attempt protocol `ODECompleteTrial.algorithm` of one public circuit family over the released
oracle `constOracle F ι Nm Tsl d J₀ Jb` that satisfies the released complete certificate for
every input and every solution (target `x(T)`), with parameters `Θ`, `ℓ`, `g`, `ε`. -/
def ConstProtocol (F : Family X N Z 1 s) (ι : Type) [Fintype ι] [DecidableEq ι] (Nm Tsl d : ℕ)
    (J₀ Jb : X → SysOp N)
    (p : ODERepeatProtocol.Protocol (constOracle F ι Nm Tsl d J₀ Jb) (EuclideanSpace ℂ N))
    (Θ ell g ε : ℝ) : Prop :=
  ∃ (q : ℕ → MultiOracleCircuit.Program (constOracle F ι Nm Tsl d J₀ Jb)) (M : ℕ)
    (ψ : ODEFinalNativeSource.Physical ι N Z Nm Tsl d)
    (Fo : EuclideanSpace ℂ N →L[ℂ] ODEFinalNativeSource.Physical ι N Z Nm Tsl d),
    ∀ x sol, F.Solves x sol →
      ∃ hC : ODECompleteTrial.Certificate q M ψ Fo x (sol F.T) (s : ℝ) Θ ell g ε,
        ODECompleteTrial.algorithm hC.trial = p

variable {F : Family X N Z 1 s} {ι : Type} [Fintype ι] [DecidableEq ι] {Nm Tsl d : ℕ}
  {J₀ Jb : X → SysOp N}
  {p : ODERepeatProtocol.Protocol (constOracle F ι Nm Tsl d J₀ Jb) (EuclideanSpace ℂ N)}
  {Θ ell g ε : ℝ}

/-- The released protocol succeeds with probability at least `2/3` on every input that has a
solution. -/
theorem ConstProtocol.success (hp : ConstProtocol F ι Nm Tsl d J₀ Jb p Θ ell g ε) (x : X)
    (sol : ℝ → EuclideanSpace ℂ N) (hs : F.Solves x sol) : 2 / 3 ≤ p.successMass x := by
  obtain ⟨q, M, ψ, Fo, h⟩ := hp
  obtain ⟨hC, hpC⟩ := h x sol hs
  subst hpC
  exact hC.success_two_thirds

/-- **The released protocol is `ε`-accurate** in the observable form of trace distance, read by
the clean readout `endpointReadout 1 i₀ : ℂ^N → ℂ^N ⊗ ℂ^N` (any garbage index `i₀`). -/
theorem ConstProtocol.accurate (hp : ConstProtocol F ι Nm Tsl d J₀ Jb p Θ ell g ε) (i₀ : N)
    (x : X) (sol : ℝ → EuclideanSpace ℂ N) (hs : F.Solves x sol) :
    DensityAccurate (Hamiltonian.endpointReadout (1 : SysOp N) i₀) (p.conditionalDensity x)
      (ODEStateNormalization.unitDirection (sol F.T)) ε := by
  obtain ⟨q, M, ψ, Fo, h⟩ := hp
  obtain ⟨hC, hpC⟩ := h x sol hs
  subst hpC
  exact ODELowerBoundExtensions.Release.certificate_densityAccurate hC i₀

/-- **The released query bound**: the worst-case number of matrix queries over all transcripts is
at most `1274019840 g · queryShape(s, Θ, ℓ)` (`Certificate.matrix_queries`). -/
theorem ConstProtocol.worstCost_le (hp : ConstProtocol F ι Nm Tsl d J₀ Jb p Θ ell g ε) (x : X)
    (sol : ℝ → EuclideanSpace ℂ N) (hs : F.Solves x sol) :
    (p.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
      1274019840 * g * ImprovedODEQueryBudget.queryShape s Θ ell := by
  obtain ⟨q, M, ψ, Fo, h⟩ := hp
  obtain ⟨hC, hpC⟩ := h x sol hs
  subst hpC
  exact hC.matrix_queries

/-- **The released protocol as a retry solver** of a family all of whose inputs have a
solution, read by the clean readout `endpointReadout 1 i₀`. -/
def ConstProtocol.toRetrySolver (hp : ConstProtocol F ι Nm Tsl d J₀ Jb p Θ ell g ε)
    (hsol : ∀ x, ∃ sol, F.Solves x sol) (i₀ : N) :
    RetrySolver F (constOracle F ι Nm Tsl d J₀ Jb) (EuclideanSpace ℂ N) (EuclideanSpace ℂ N)
      ε where
  prot := p
  readout := Hamiltonian.endpointReadout (1 : SysOp N) i₀
  readout_isometry := Hamiltonian.endpointReadout_isometry 1 (by ext; simp) i₀
  success x := (hsol x).elim fun sol hs => hp.success x sol hs
  accurate := hp.accurate i₀

/-- **The released protocol as an adaptive solver** (`Tree.final` of the retry solver, flag
space `ℂ`). -/
def ConstProtocol.toTreeSolver (hp : ConstProtocol F ι Nm Tsl d J₀ Jb p Θ ell g ε)
    (hsol : ∀ x, ∃ sol, F.Solves x sol) (i₀ : N) :
    TreeSolver F (constOracle F ι Nm Tsl d J₀ Jb) ℂ (EuclideanSpace ℂ N) (EuclideanSpace ℂ N)
      ε :=
  retryToTree (hp.toRetrySolver hsol i₀) ℂ

/-- The adaptive solver of a released protocol has the protocol's worst-case counts: the lemma
`AdaptiveODELowerBound.Model.worstCost_retryToTree` applied to the released protocol. -/
@[simp] theorem ConstProtocol.worstCost_toTreeSolver
    (hp : ConstProtocol F ι Nm Tsl d J₀ Jb p Θ ell g ε) (hsol : ∀ x, ∃ sol, F.Solves x sol)
    (i₀ : N) (w : Query ⊕ Bool → ℕ) :
    (hp.toTreeSolver hsol i₀).tree.worstCost w = p.worstCost w :=
  AdaptiveODELowerBound.Model.worstCost_retryToTree (hp.toRetrySolver hsol i₀) ℂ w

end

end ConstantODELowerBound.Protocol
