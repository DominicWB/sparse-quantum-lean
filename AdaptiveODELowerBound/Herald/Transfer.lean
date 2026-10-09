import AdaptiveODELowerBound.Model.Solver
import AdaptiveODELowerBound.Access.Admissible
import AdaptiveHamiltonianLowerBound.Theorem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Lemma `odel:lem:herald` for adaptive protocols: the `g = 1` families

Manuscript lines 4393-4435 (eq. `odel:eq:hsbound` and Lemma `odel:lem:herald`). The `g = 1`
families of `SparseLowerBounds/ODE/Precision` (`timeFamilyAt`, `mixedFamilyAt`,
`precisionFamilyAt`: the hard Hamiltonian data read as homogeneous constant-coefficient ODEs with
generator `iH`, `D = 0`, `‖x(T)‖ = 1`) force on adaptive solvers the per-family bounds of eqs.
`hsl:eq:timelower`, `hsl:eq:mixrbound`, `hsl:eq:rbound`, `hsl:eq:failedmix`, with the constants of
the Hamiltonian lower bound.

Route (`treeForces_of_ham`, the tree analogue of `Release.retryForces_of_tree`). The sampled-time
access of `hamFamily D` is the spectated native access `specOracles (ι × Fin 1) D`
(`access_hamFamily`); its labels are admissible for `D` with the value-query weight
(`AdaptiveHamiltonianLowerBound.Access.admissible_specOracles`), and so are all its call forms
(`Access.admissible_callFamily_spec`), since the hard data have input-independent locators. The
adaptive Hamiltonian lower bound (`AdaptiveHamiltonianLowerBound.time_tree`, `mixed_tree`,
`precision_tree`, which hold for every adaptive protocol over admissible labels) then gives the
bounds, since accuracy for `x(T)/‖x(T)‖` is accuracy for the unit vector `x(T) = e^{-iτH_x} x₀`
(`Model.TreeSolver.accurate_ham`). The total count is at least the value count.
-/

universe uN uZ

namespace AdaptiveODELowerBound.Model

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit SparseLinearSystems.Protocol
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open scoped InnerProduct InnerProductSpace

/-- **Accuracy of an adaptive solver on a `g = 1` family**: for Hermitian data and a unit initial
state the normalised solution is `exp(-iTH_x) x₀`, so the conditional output of every adaptive
solver of `hamFamily D T hT x₀` is `ε`-accurate for it. -/
theorem TreeSolver.accurate_ham {X N Z : Type*} [Fintype N] [DecidableEq N] {s : ℕ}
    (D : Data X N Z s) (T : ℝ) (hT : 0 ≤ T) (x₀ : EuclideanSpace ℂ N)
    (hH : ∀ x, (D.matrix x).IsHermitian) (hx₀ : ‖x₀‖ = 1) {L W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    {O : L → X → W →L[ℂ] W} {Fl E G : Type*}
    [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G] {ε : ℝ}
    (A : TreeSolver (hamFamily D T hT x₀) O Fl E G ε) (x : X) :
    DensityAccurate A.readout (A.tree.conditionalDensity x)
      (Hamiltonian.evolve (D.matrix x) T x₀) ε := by
  have h := A.accurate x _ (hamFamily_solves D T hT x₀ x)
  have hu : ODEStateNormalization.unitDirection (Hamiltonian.evolve (D.matrix x) T x₀) =
      Hamiltonian.evolve (D.matrix x) T x₀ := by
    rw [ODEStateNormalization.unitDirection, Hamiltonian.norm_evolve_apply (hH x), hx₀,
      inv_one, one_smul]
  rw [hamFamily_T, hu] at h
  exact h

end

end AdaptiveODELowerBound.Model

namespace AdaptiveODELowerBound.Herald

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit SparseLinearSystems.Protocol
open AdaptiveHamiltonianLowerBound (DensityAccurate)
open AdaptiveHamiltonianLowerBound.Access (Admissible valueWeight)
open AdaptiveODELowerBound.Model
open scoped InnerProduct InnerProductSpace

section Transfer

variable {X : Type*} {N : Type uN} {Z : Type uZ} [Fintype N] [DecidableEq N] [Fintype Z]
  [AddCommGroup Z] {s' : ℕ} (D : Data X N Z s') (T : ℝ) (hT : 0 ≤ T) (x₀ : EuclideanSpace ℂ N)

/-- **Adaptive-protocol transfer** (the tree analogue of `Release.retryForces_of_tree`): if every
adaptive protocol over an oracle family whose labels are admissible for `D` with weights `w`,
heralding success with probability `≥ 2/3` and `ε`-accurate for `e^{-iTH_x} x₀`, has worst-case
cost at least `b`, then `hamFamily D T x₀` tree-forces `b` (sampled-time access and call
forms). The workspaces range over the universe of the sampled-time workspace
`Workspace ι N Z 1` and of its call-form space, so `X`, `N` and `Z` are universe polymorphic
as in the released transfer. -/
theorem treeForces_of_ham {ε b : ℝ} (hH : ∀ x, (D.matrix x).IsHermitian) (hx₀ : ‖x₀‖ = 1)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (hb : ∀ (L : Type) (W : Type (max uN uZ)) (Fl E G : Type) [NormedAddCommGroup W]
      [InnerProductSpace ℂ W] [CompleteSpace W]
      [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
      [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
      [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
      (O : L → X → W →L[ℂ] W) (w : L → ℕ), (∀ l, Admissible D (O l) (w l)) →
      ∀ (P : Tree O Fl E) (e : E →L[ℂ] SysGarb N G), e† ∘L e = 1 →
      (∀ x, 2 / 3 ≤ P.successMass x) →
      (∀ x, DensityAccurate e (P.conditionalDensity x) (Hamiltonian.evolve (D.matrix x) T x₀) ε) →
      b ≤ P.worstCost w) :
    TreeForces (hamFamily D T hT x₀) ε b := by
  have hq : ∀ (ι : Type) [Fintype ι],
      (hamFamily D T hT x₀).access ι = specOracles (ι × Fin 1) D := fun ι _ =>
    funext fun q => funext fun x => access_hamFamily D T hT x₀ ι q x
  constructor
  · intro ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A
    have hO : ∀ q, Admissible D ((hamFamily D T hT x₀).access ι q) (valueWeight q) := by
      intro q
      rw [hq ι]
      exact AdaptiveHamiltonianLowerBound.Access.admissible_specOracles (ι × Fin 1) D hrow hcol q
    have h1 : b ≤ A.tree.worstCost valueWeight :=
      hb Query (Workspace ι N Z 1) Fl E G _ valueWeight hO A.tree A.readout
        A.readout_isometry A.success (A.accurate_ham D T hT x₀ hH hx₀)
    refine ⟨h1, h1.trans ?_⟩
    exact_mod_cast worstCost_mono_tree A.tree fun q => by cases q <;> simp [valueWeight]
  · intro ι _ Fl E G _ _ _ _ _ _ _ _ _ _ A
    have hO : ∀ c : Query × Access.CallForm,
        Admissible D (Access.callFamily ((hamFamily D T hT x₀).access ι) c) (valueWeight c.1) := by
      intro c
      rw [hq ι]
      exact Access.admissible_callFamily_spec (ι × Fin 1) D hrow hcol c
    have h1 : b ≤ A.tree.worstCost (fun c => valueWeight c.1) :=
      hb (Query × Access.CallForm) (Joint Bool (Workspace ι N Z 1)) Fl E G _
        (fun c => valueWeight c.1) hO A.tree A.readout A.readout_isometry A.success
        (A.accurate_ham D T hT x₀ hH hx₀)
    refine ⟨h1, h1.trans ?_⟩
    exact_mod_cast worstCost_mono_tree A.tree fun c => by
      rcases c with ⟨q, f⟩
      cases q <;> simp [valueWeight]

end Transfer

variable {τ ε : ℝ} {s : ℕ}

/-- **Lemma `odel:lem:herald` for adaptive protocols, time family** (eq. `hsl:eq:timelower`):
`Q ≥ c_T √s τ`, `c_T = log 2/(192π)`. -/
theorem time_forces_tree (h : HSRange τ s ε) :
    TreeForces (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) ε
      (cT * Real.sqrt s * τ) := by
  have hI := (hard_instances h).1
  have hA := AdaptiveHamiltonianLowerBound.Access.hardAccess_timeData τ s h.s_ge
  refine treeForces_of_ham _ _ _ _ hI.isHermitian (norm_searchInput _ _ _) hA.row_const
    hA.column_const ?_
  intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hO P e he hsucc hacc
  exact AdaptiveHamiltonianLowerBound.time_tree h O w hO P e he hsucc hacc

/-- **Lemma `odel:lem:herald` for adaptive protocols, mixed family** (eq. `hsl:eq:mixrbound`):
for `L ≥ 64τ` and `s ≥ 64n/τ`, `Q ≥ (log 2/(384√2)) √(sτr)`. -/
theorem mixed_forces_tree (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) :
    TreeForces (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε
      (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)) := by
  have hI := (hard_instances h).2.1
  have hA := AdaptiveHamiltonianLowerBound.Access.hardAccess_mixedMainData τ ε s h.s_ge
  refine treeForces_of_ham _ _ _ _ hI.isHermitian (norm_searchInput _ _ _) hA.row_const
    hA.column_const ?_
  intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hO P e he hsucc hacc
  exact AdaptiveHamiltonianLowerBound.mixed_tree h hL hs O w hO P e he hsucc hacc

/-- **Lemma `odel:lem:herald` for adaptive protocols, precision family** (eq. `hsl:eq:rbound`):
for `L ≥ 64τ`, `Q ≥ r/32`. -/
theorem precision_forces_tree (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) :
    TreeForces (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε
      (hsR τ ε / 32) := by
  have hI := (hard_instances h).2.2.1
  have hA := AdaptiveHamiltonianLowerBound.Access.hardAccess_precisionMainData τ ε s h.s_ge
  refine treeForces_of_ham _ _ _ _ hI.isHermitian (norm_scalarInput _ _) hA.row_const
    hA.column_const ?_
  intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hO P e he hsucc hacc
  exact (AdaptiveHamiltonianLowerBound.precision_tree h hL O w hO P e he hsucc hacc).1

/-- **Lemma `odel:lem:herald` for adaptive protocols, precision family, small sparsity**
(eq. `hsl:eq:failedmix`): for `L ≥ 64τ` and `s < 64n/τ`, `Q ≥ √(sτr)/(64√2)`. -/
theorem precision_forces_sqrt_tree (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs' : (s : ℝ) < 64 * precN τ ε / τ) :
    TreeForces (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε
      (Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2)) := by
  have hI := (hard_instances h).2.2.1
  have hA := AdaptiveHamiltonianLowerBound.Access.hardAccess_precisionMainData τ ε s h.s_ge
  refine treeForces_of_ham _ _ _ _ hI.isHermitian (norm_scalarInput _ _) hA.row_const
    hA.column_const ?_
  intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hO P e he hsucc hacc
  exact (AdaptiveHamiltonianLowerBound.precision_tree h hL O w hO P e he hsucc hacc).2 hs'

end

end AdaptiveODELowerBound.Herald
