import AdaptiveODELowerBound.Joint.General
import AdaptiveODELowerBound.Herald.Transfer
import AdaptiveODELowerBound.Bound
import ODELowerBoundExtensions.Release.Bridge

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Theorem `odel:thm:combined` for adaptive protocols over the released solver's oracle

Manuscript: Section `odel:sec:main` ("the lower bounds apply to the upper bounds of the preceding
section") and Theorem `odel:thm:combined`, for adaptive solvers (`Model.TreeSolver`) over the
physical oracle family of the released general-mesh solver `TimeDependentExtensions.ODE.solver`, run
on the hard family's data along any public placement `σ : Fin M → Fin K` of mesh pieces into stages
(`ODELowerBoundExtensions.Release.meshOracle`, any spectator index, slot count and degree), with
public source interfaces (`Release.PublicSources`). Two counts are bounded, as in
`Release.combined_max_release`: the worst-case number of value calls
`Tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight)` and the release's matrix count
`Tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))`.

* `joint_release_tree`: `c_J ḡ √s τ ≤ Q` on the joint family (`JointRange`), from
  `Joint.joint_general_tree` with the membership certificate `Release.implementsOn_release_joint`
  (Boolean cost `matrixWeight hardCost = 2 · matrixWeight valueWeight`).
* `mixed_release_tree`, `precision_release_tree`: the `g = 1` bounds, from
  `AdaptiveHamiltonianLowerBound.mixed_tree_general`, `precision_tree_general` with
  `Release.searchGrowth_release_ham` and the numerics `mixrbound`, `rbound`, `failedmix`.
* `combined_max_release_tree`: max form, `c (ḡ √s τ + √(sτr) + r) ≤ max(Q_J, Q_M, Q_P)` for both
  counts, `c = log 2/(8192π)`, from the per-family bounds by `combinedBound_le_max`.

**Scope.** Only the general-mesh released solver (Theorem `ode:thm:time`) is connected. The
constant-coefficient released solver `SparseHamiltonian.ODECompleteEndpoint.solver` (Theorem
`ode:thm:main`) is not; the general-mesh solver covers the same hard families, all of which have
piecewise-constant coefficients. The adaptive solvers here call the physical oracle family
`meshOracle` itself (with inverse calls); the call forms `Access.callFamily` of the physical
oracle (controlled calls) are not included, and the released solver does not use them.
The comparison with the upper bound (Section `odel:sec:main`, "within one logarithm") is
`ODELowerBoundExtensions.Release.release_theta`, whose lower half is proved there from
`Release.combined_max_release` at the retry solvers `A.release.toRetrySolver` of the runs. A
release run is a retry protocol, hence the adaptive protocol `Tree.final` (`Model.retryToTree`,
with the same worst-case counts, `Model.worstCost_retryToTree`), so `combined_max_release_tree`
applied to `Model.retryToTree` of those retry solvers gives the same lower half; this is not
restated as a separate theorem.
-/

namespace AdaptiveODELowerBound.Release

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE
open SparseLowerBounds.Hamiltonian (HSRange hsL hsR precN)
open NativeSparseBlockEncoding OracleCircuit TimeDependentExtensions
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open ODELowerBoundExtensions.Release (meshOracle PublicSources SysOp)
open AdaptiveODELowerBound.Model

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

/-- The value-call count of an adaptive protocol over release labels bounds its matrix-call count
from below. -/
theorem worstCost_value_le_matrix_tree {X W Fl E : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [CompleteSpace W] [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl]
    [CompleteSpace Fl] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {O : Query ⊕ Bool → X → W →L[ℂ] W} (T : SparseLinearSystems.Protocol.Tree O Fl E) :
    (T.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ) ≤
      T.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := by
  exact_mod_cast worstCost_mono_tree T ODELowerBoundExtensions.Release.matrixWeight_value_le

/-- **Theorem `odel:thm:joint` for adaptive protocols over the released solver's oracle**: on
`JointRange`, every adaptive solver over the release's physical oracle on the joint family along
any placement `σ`, with public source interfaces, makes at least `ḡ √s τ / 400` value calls, hence
as many matrix calls, in the worst case. -/
theorem joint_release_tree {s : ℕ} {τ gbar ε : ℝ} (h : JointRange s τ gbar ε) {M : ℕ}
    (σ : Fin M → Fin (jointN τ + 2)) (ι : Type) [Fintype ι] [DecidableEq ι] (Nsl d : ℕ)
    {J₀ : _ → SysOp _} {Jb : _ → Fin M → SysOp _} (hJ : PublicSources J₀ Jb) {Fl E G : Type}
    [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : TreeSolver (jointFamilyAt s τ gbar h.s_ge h.tau_ge)
      (meshOracle (jointFamilyAt s τ gbar h.s_ge h.tau_ge) σ ι Nsl d J₀ Jb) Fl E G ε) :
    jointConst * gbar * Real.sqrt s * τ ≤
        A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      jointConst * gbar * Real.sqrt s * τ ≤
        A.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := by
  have hs := h.s_ge
  have hT := jointN_time (by linarith [h.tau_ge] : (1 : ℝ) ≤ τ)
  have hM := four_le_jointM h.gbar_ge
  obtain ⟨B, _, _, _, P, Enc, hEnc, hw⟩ :=
    ODELowerBoundExtensions.Release.implementsOn_release_joint
    (one_le_jointMu (by omega : 2 ≤ s)) (two_pow_jointMu_le (by omega : 1 ≤ s)) hT σ ι Nsl d hJ
  have hU := MeshSource.physicalOracle_unitary (ι := ι)
    (ODELowerBoundExtensions.Release.stageData (jointFamilyAt s τ gbar h.s_ge h.tau_ge).data σ)
    Nsl d J₀ Jb
    hJ.initial_unitary
    hJ.forcing_unitary
  have hb := Joint.joint_general_tree (s := s) (ε := ε) (by omega) (even_jointM gbar)
    (one_le_jointN h.tau_ge) (one_le_jointMu (by omega)) (by linarith [h.eps_le]) P Enc hEnc _ hU
    _ hw A.tree A.readout A.readout_isometry A.success (fun x => by
      have hx := A.accurate x _ (jointSol_solves x)
      rwa [show (jointFamilyAt s τ gbar h.s_ge h.tau_ge).T = τ from jointFamily_T,
        unitDirection_jointSol_T hT] at hx)
  rw [ODELowerBoundExtensions.Release.matrixWeight_hardCost, worstCost_mul_tree] at hb
  push_cast at hb
  have hv : jointConst * gbar * Real.sqrt s * τ ≤
      A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := by
    linarith [joint_bound_le h]
  exact ⟨hv, hv.trans (worstCost_value_le_matrix_tree A.tree)⟩

/-- **Mixed family, adaptive protocols over the released solver's oracle**
(eq. `hsl:eq:mixrbound`): for `L ≥ 64τ` and `s ≥ 64n/τ`, at least
`(log 2/(384√2)) √(sτr)` value calls, hence as many matrix calls, in the worst case. -/
theorem mixed_release_tree {τ ε : ℝ} {s : ℕ} (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) {M : ℕ} (σ : Fin M → Fin 1) (ι : Type) [Fintype ι]
    [DecidableEq ι] (Nsl d : ℕ) {J₀ : _ → SysOp _} {Jb : _ → Fin M → SysOp _}
    (hJ : PublicSources J₀ Jb) {Fl E G : Type}
    [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : TreeSolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      (meshOracle (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) σ ι Nsl d J₀ Jb)
      Fl E G ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤
        A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤
        A.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := by
  have hτ0 : (0 : ℝ) ≤ τ := by linarith [h.one_le_tau]
  have hI := (Hamiltonian.hard_instances h).2.1
  have hO := ODELowerBoundExtensions.Release.searchGrowth_release_ham
    (AdaptiveHamiltonianLowerBound.even_two_pow_hsMu h.s_ge)
    (Hamiltonian.mixedMainData τ ε s h.s_ge) id
    (AdaptiveHamiltonianLowerBound.Access.hardAccess_mixedMainData τ ε s h.s_ge) τ hτ0
    (Hamiltonian.searchInput (precN τ ε) (Hamiltonian.hsMu s) s) σ ι Nsl d hJ
  have hU := MeshSource.physicalOracle_unitary (ι := ι)
    (ODELowerBoundExtensions.Release.stageData (mixedFamilyAt τ ε s h.s_ge hτ0).data σ)
    Nsl d J₀ Jb
    hJ.initial_unitary
    hJ.forcing_unitary
  have hb := AdaptiveHamiltonianLowerBound.mixed_tree_general (F := Fl) h hL hs
    (O := meshOracle (mixedFamilyAt τ ε s h.s_ge hτ0) σ ι Nsl d J₀ Jb) hU _ hO
    A.tree A.readout A.readout_isometry A.success
    (fun j => A.accurate_ham _ _ _ _ hI.isHermitian (Hamiltonian.norm_searchInput _ _ _) j)
  have hb' : Real.log 2 / 48 * Real.sqrt ((2 : ℝ) ^ Hamiltonian.hsMu s * precN τ ε * τ) ≤
      A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := hb
  have hX : 0 ≤ Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ Hamiltonian.hsMu s * precN τ ε * τ) :=
    mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num)) (Real.sqrt_nonneg _)
  have hv : Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤
      A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := by
    linarith [Hamiltonian.mixrbound h hL]
  exact ⟨hv, hv.trans (worstCost_value_le_matrix_tree A.tree)⟩

/-- **Precision family, adaptive protocols over the released solver's oracle**
(eqs. `hsl:eq:rbound`, `hsl:eq:failedmix`): for `L ≥ 64τ`, at least `r/32` value calls in the
worst case, and at least `√(sτr)/(64√2)` when `s < 64n/τ`; hence as many matrix calls. -/
theorem precision_release_tree {τ ε : ℝ} {s : ℕ} (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    {M : ℕ} (σ : Fin M → Fin 1) (ι : Type) [Fintype ι] [DecidableEq ι] (Nsl d : ℕ)
    {J₀ : _ → SysOp _} {Jb : _ → Fin M → SysOp _} (hJ : PublicSources J₀ Jb) {Fl E G : Type}
    [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : TreeSolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      (meshOracle (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) σ ι Nsl d J₀ Jb)
      Fl E G ε) :
    (hsR τ ε / 32 ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      hsR τ ε / 32 ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤
            A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
          Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤
            A.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) := by
  have hτ0 : (0 : ℝ) ≤ τ := by linarith [h.one_le_tau]
  have hI := (Hamiltonian.hard_instances h).2.2.1
  have hO := ODELowerBoundExtensions.Release.searchGrowth_release_ham even_two
    (Hamiltonian.precisionMainData τ ε s h.s_ge) AdaptiveHamiltonianLowerBound.Access.toBits
    (AdaptiveHamiltonianLowerBound.Access.hardAccess_precisionMainData τ ε s h.s_ge) τ hτ0
    (Hamiltonian.scalarInput (precN τ ε) s) σ ι Nsl d hJ
  have hU := MeshSource.physicalOracle_unitary (ι := ι)
    (ODELowerBoundExtensions.Release.stageData (precisionFamilyAt τ ε s h.s_ge hτ0).data σ)
    Nsl d J₀ Jb
    hJ.initial_unitary
    hJ.forcing_unitary
  have hb := AdaptiveHamiltonianLowerBound.precision_tree_general (F := Fl) h hL
    (O := meshOracle (precisionFamilyAt τ ε s h.s_ge hτ0) σ ι Nsl d J₀ Jb) hU _ hO
    A.tree A.readout A.readout_isometry A.success
    (fun x => A.accurate_ham _ _ _ _ hI.isHermitian (Hamiltonian.norm_scalarInput _ _) x)
  have hb' : (precN τ ε : ℝ) / 2 ≤
      A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := hb
  have hn0 : (0 : ℝ) ≤ precN τ ε := Nat.cast_nonneg _
  have hm := worstCost_value_le_matrix_tree A.tree
  refine ⟨⟨by linarith [Hamiltonian.rbound h hL], by linarith [Hamiltonian.rbound h hL]⟩,
    fun hs' => ⟨by linarith [Hamiltonian.failedmix h hL hs'],
      by linarith [Hamiltonian.failedmix h hL hs']⟩⟩

/-- **Theorem `odel:thm:combined` for adaptive protocols over the released solver's oracle, max
form** (the adaptive analogue of `Release.combined_max_release`): for any three adaptive solvers
over the release's physical oracle on the joint, mixed and precision families (any placements of
mesh pieces, spectator indices, slot counts, degrees, public source interfaces, flag, output and
garbage spaces), each accurate on its own family, the largest worst-case value count, and hence
the largest worst-case matrix count, is at least `c (ḡ √s τ + √(sτr) + r)`, `c = log 2/(8192π)`. -/
theorem combined_max_release_tree {s : ℕ} {τ gbar ε : ℝ} (h : CombinedRange s τ gbar ε)
    {MJ MM MP : ℕ} (σJ : Fin MJ → Fin (jointN τ + 2)) (σM : Fin MM → Fin 1)
    (σP : Fin MP → Fin 1) (ιJ ιM ιP : Type) [Fintype ιJ] [DecidableEq ιJ] [Fintype ιM]
    [DecidableEq ιM] [Fintype ιP] [DecidableEq ιP] (NJ dJ NM dM NP dP : ℕ)
    {J₀J : _ → SysOp _} {JbJ : _ → Fin MJ → SysOp _} (hJJ : PublicSources J₀J JbJ)
    {J₀M : _ → SysOp _} {JbM : _ → Fin MM → SysOp _} (hJM : PublicSources J₀M JbM)
    {J₀P : _ → SysOp _} {JbP : _ → Fin MP → SysOp _} (hJP : PublicSources J₀P JbP)
    {FlJ FlM FlP EJ EM EP GJ GM GP : Type}
    [NormedAddCommGroup FlJ] [InnerProductSpace ℂ FlJ] [CompleteSpace FlJ]
    [NormedAddCommGroup FlM] [InnerProductSpace ℂ FlM] [CompleteSpace FlM]
    [NormedAddCommGroup FlP] [InnerProductSpace ℂ FlP] [CompleteSpace FlP]
    [NormedAddCommGroup EJ] [InnerProductSpace ℂ EJ] [CompleteSpace EJ] [FiniteDimensional ℂ EJ]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GJ] [InnerProductSpace ℂ GJ] [CompleteSpace GJ]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AJ : TreeSolver (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge)
      (meshOracle (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) σJ ιJ NJ dJ J₀J JbJ)
      FlJ EJ GJ ε)
    (AM : TreeSolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
      (meshOracle (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) σM ιM NM dM J₀M JbM)
      FlM EM GM ε)
    (AP : TreeSolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
      (meshOracle (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) σP ιP NP dP J₀P
        JbP) FlP EP GP ε) :
    combinedBound s τ gbar ε ≤
        max (AJ.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
          (max (AM.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
            (AP.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight))) ∧
      combinedBound s τ gbar ε ≤
        max (AJ.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
          (max (AM.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
            (AP.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)))) := by
  have hH := h.toHSRange
  have hv := combinedBound_le_max h
    (joint_release_tree h.toJointRange σJ ιJ NJ dJ hJJ AJ).1
    (fun hL => ⟨(precision_release_tree hH hL σP ιP NP dP hJP AP).1.1,
      fun hs' => ((precision_release_tree hH hL σP ιP NP dP hJP AP).2 hs').1⟩)
    (fun hL hs => (mixed_release_tree hH hL hs σM ιM NM dM hJM AM).1)
  exact ⟨hv, hv.trans (max_le_max (worstCost_value_le_matrix_tree AJ.tree)
    (max_le_max (worstCost_value_le_matrix_tree AM.tree)
      (worstCost_value_le_matrix_tree AP.tree)))⟩

end

end AdaptiveODELowerBound.Release
