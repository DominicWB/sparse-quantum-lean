import PhysicalODELowerBound.Mesh.Combined
import PhysicalODELowerBound.Mesh.Psd
import ReleasedODESolverLowerBounds.Mesh.Upgrade

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The ODE lower bounds for measured solvers over the general-mesh physical oracle

Manuscript Section `odel:sec:main` ("the lower bounds apply to the upper bounds of the preceding
section"), with measurements inside a run (proof of Lemma `hsl:lem:precision`): Theorem
`odel:thm:combined` (eq. `odel:eq:combined`), Theorem `odel:thm:joint`, Proposition
`odel:rem:homogeneous`, Lemma `odel:lem:herald` and eq. `odel:eq:hsbound`, Theorem `odel:thm:psd`
(eq. `odel:eq:psd`), all over the physical oracle of the released general-mesh solver of Theorem
`ode:thm:time` and over its call forms.

Every statement is the corresponding statement of `PhysicalODELowerBound.Mesh` with
`MeasuredMeshWitnesses` in place of `MeshWitnesses` (`measuredMeshWitnesses_of_meshWitnesses`), or,
for the max forms, with realised measured counts in place of realised adaptive counts
(`MeasuredMeshCost.exists_meshCost_le`); hypotheses and constants are those of the lifted
statements. `combined_max_release_measured_mesh` is the measured form of
`AdaptiveODELowerBound.Release.combined_max_release_tree` (three measured solvers over the
physical oracle, both the value and the matrix count); `joint_release_measured_mesh`,
`mixed_release_measured_mesh` and `precision_release_measured_mesh` are the measured forms of
`joint_release_tree`, `mixed_release_tree` and `precision_release_tree` of that library, with
their sub-range conditions and constants.
-/

namespace ReleasedODESolverLowerBounds.Mesh

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open ODELowerBoundExtensions.Psd
open ODELowerBoundExtensions.Homogeneous (HomRange homFamilyAt homConst)
open ODELowerBoundExtensions.Padding (timePadFamilyAt jointPadFamilyAt mixedPadFamilyAt
  precisionPadFamilyAt)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open ODELowerBoundExtensions.Release (meshOracle PublicSources SysOp)
open DeferredMeasurementLowerBounds.Corollaries (MeasuredSolver)

open PhysicalODELowerBound.Mesh (herald_witness_mesh herald_witness_pad_mesh
  precision_terms_witness_mesh psd_mesh joint_witness_mesh hom_witness_mesh combined_mesh
  combined_pad_mesh herald_max_cost_mesh psd_max_cost_mesh combined_max_cost_mesh
  joint_forces_mesh mixed_forces_mesh precision_forces_mesh precision_forces_sqrt_mesh)
open ReleasedODESolverLowerBounds.Mesh renaming measuredMeshWitnesses_of_meshWitnesses → W

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **Eq. `odel:eq:hsbound` for measured solvers over the general-mesh physical oracle, family
form**: on `HSRange` and for any `ḡ ≥ 1`, one of the time, mixed and precision families
witnesses `c₀ (√s τ + √(sτr) + r)` on measured solvers, `c₀ = log 2/(4096π)`. -/
theorem herald_witness_measured_mesh (h : HSRange τ s ε) (hg : 1 ≤ gbar) :
    MeasuredMeshWitnesses (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredMeshWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredMeshWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar
        ε (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  exact (herald_witness_mesh h hg).imp
    W (Or.imp W W)

/-- **The padded `g = 1` families for measured solvers** (any known padding registers). -/
theorem herald_witness_pad_measured_mesh (h : HSRange τ s ε) (hg : 1 ≤ gbar)
    (PT PM PP : Type) [Fintype PT] [DecidableEq PT] [Fintype PM] [DecidableEq PM]
    [Fintype PP] [DecidableEq PP] :
    MeasuredMeshWitnesses (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredMeshWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) τ
        gbar ε (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredMeshWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) τ
        gbar ε (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  exact (herald_witness_pad_mesh h hg PT PM PP).imp
    W (Or.imp W W)

/-- **The precision terms of Theorem `odel:thm:combined` for measured solvers** (its fourth
sentence): on `HSRange` with `ḡ ≥ 1`, a `g = 1` family witnesses `c₀ (√(sτr) + r)`. -/
theorem precision_terms_witness_measured_mesh (h : HSRange τ s ε) (hg : 1 ≤ gbar) :
    MeasuredMeshWitnesses (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredMeshWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeasuredMeshWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar
        ε (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  exact (precision_terms_witness_mesh h hg).imp
    W (Or.imp W W)

/-- **Theorem `odel:thm:psd` for measured solvers over the general-mesh physical oracle**: on
`PsdRange` and for `ḡ ≥ √2`, the gadget or the scalar positive semidefinite family witnesses
`psdConst (√(sτr) + r)`. -/
theorem psd_measured_mesh (h : PsdRange τ s ε) (hg : Real.sqrt 2 ≤ gbar) :
    MeasuredMeshWitnesses (psdSearchFamilyAt h) τ gbar ε (psdBound s τ ε) ∨
      MeasuredMeshWitnesses (psdScalarFamilyAt h) τ gbar ε (psdBound s τ ε) := by
  exact (psd_mesh h hg).imp W W

/-- **Theorem `odel:thm:joint` for measured solvers over the general-mesh physical oracle**: on
`JointRange` the joint family witnesses `ḡ √s τ / 400`. -/
theorem joint_witness_measured_mesh (h : JointRange s τ gbar ε) :
    MeasuredMeshWitnesses (jointFamilyAt s τ gbar h.s_ge h.tau_ge) τ gbar ε
      (jointConst * gbar * Real.sqrt s * τ) := by
  exact W (joint_witness_mesh h)

/-- **Proposition `odel:rem:homogeneous` for measured solvers over the general-mesh physical
oracle**: on `HomRange` the homogeneous family witnesses `ḡ √s τ / 500`. -/
theorem hom_witness_measured_mesh (h : HomRange s τ gbar ε) :
    MeasuredMeshWitnesses (homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge) τ gbar ε
      (homConst * gbar * Real.sqrt s * τ) := by
  exact W (hom_witness_mesh h)

/-- **Theorem `odel:thm:combined` for measured solvers over the general-mesh physical oracle,
family form**: on `CombinedRange` one of the joint, mixed and precision families witnesses
`c (ḡ √s τ + √(sτr) + r)`, `c = log 2/(8192π)`. -/
theorem combined_measured_mesh (h : CombinedRange s τ gbar ε) :
    MeasuredMeshWitnesses (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      MeasuredMeshWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      MeasuredMeshWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) τ gbar ε
        (combinedBound s τ gbar ε) := by
  exact (combined_mesh h).imp
    W (Or.imp W W)

/-- **Theorem `odel:thm:combined` for measured solvers with the padded families** (dense flag
and known paddings, as `PhysicalODELowerBound.Mesh.combined_pad_mesh`). -/
theorem combined_pad_measured_mesh (h : CombinedRange s τ gbar ε) (dense : Bool) (PJ PM PP : Type)
    [Fintype PJ] [DecidableEq PJ] [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] :
    MeasuredMeshWitnesses (jointPadFamilyAt s τ gbar dense h.toJointRange.s_ge h.tau_ge PJ) τ gbar
        ε (combinedBound s τ gbar ε) ∨
      MeasuredMeshWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PM) τ gbar ε
        (combinedBound s τ gbar ε) ∨
      MeasuredMeshWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]) PP) τ
        gbar ε (combinedBound s τ gbar ε) := by
  exact (combined_pad_mesh h dense PJ PM PP).imp
    W (Or.imp W W)

/-- **Eq. `odel:eq:hsbound` for measured solvers, max form over realised counts.** -/
theorem herald_max_measured_mesh (h : HSRange τ s ε) {qT qM qP : ℝ}
    (hT : MeasuredMeshCost (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) ε qT)
    (hM : MeasuredMeshCost (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε qM)
    (hP : MeasuredMeshCost (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε qP) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ max qT (max qM qP) := by
  obtain ⟨T', hT', hTle⟩ := MeasuredMeshCost.exists_meshCost_le hT
  obtain ⟨M', hM', hMle⟩ := MeasuredMeshCost.exists_meshCost_le hM
  obtain ⟨P', hP', hPle⟩ := MeasuredMeshCost.exists_meshCost_le hP
  exact (herald_max_cost_mesh h hT' hM' hP').trans
    (max_le_max hTle (max_le_max hMle hPle))

/-- **Theorem `odel:thm:psd` for measured solvers, max form over realised counts.** -/
theorem psd_max_measured_mesh (h : PsdRange τ s ε) {qG qS : ℝ}
    (hG : MeasuredMeshCost (psdSearchFamilyAt h) ε qG)
    (hS : MeasuredMeshCost (psdScalarFamilyAt h) ε qS) :
    psdBound s τ ε ≤ max qG qS := by
  obtain ⟨G', hG', hGle⟩ := MeasuredMeshCost.exists_meshCost_le hG
  obtain ⟨S', hS', hSle⟩ := MeasuredMeshCost.exists_meshCost_le hS
  exact (psd_max_cost_mesh h hG' hS').trans (max_le_max hGle hSle)

/-- **Theorem `odel:thm:combined` for measured solvers, max form over realised counts.** -/
theorem combined_max_measured_mesh (h : CombinedRange s τ gbar ε) {qJ qM qP : ℝ}
    (hJ : MeasuredMeshCost (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) ε qJ)
    (hM : MeasuredMeshCost (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) ε qM)
    (hP : MeasuredMeshCost (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) ε qP) :
    combinedBound s τ gbar ε ≤ max qJ (max qM qP) := by
  obtain ⟨J', hJ', hJle⟩ := MeasuredMeshCost.exists_meshCost_le hJ
  obtain ⟨M', hM', hMle⟩ := MeasuredMeshCost.exists_meshCost_le hM
  obtain ⟨P', hP', hPle⟩ := MeasuredMeshCost.exists_meshCost_le hP
  exact (combined_max_cost_mesh h hJ' hM' hP').trans
    (max_le_max hJle (max_le_max hMle hPle))

/-- **Theorem `odel:thm:combined` at three measured solvers over the released general-mesh
oracle**: the measured form of `AdaptiveODELowerBound.Release.combined_max_release_tree`, for
the value counts and for the matrix counts. -/
theorem combined_max_release_measured_mesh (h : CombinedRange s τ gbar ε)
    {MJ MM MP : ℕ} (σJ : Fin MJ → Fin (jointN τ + 2)) (σM : Fin MM → Fin 1)
    (σP : Fin MP → Fin 1) (ιJ ιM ιP : Type) [Fintype ιJ] [DecidableEq ιJ] [Fintype ιM]
    [DecidableEq ιM] [Fintype ιP] [DecidableEq ιP] (NJ dJ NM dM NP dP : ℕ)
    {J₀J : _ → SysOp _} {JbJ : _ → Fin MJ → SysOp _} (hJJ : PublicSources J₀J JbJ)
    {J₀M : _ → SysOp _} {JbM : _ → Fin MM → SysOp _} (hJM : PublicSources J₀M JbM)
    {J₀P : _ → SysOp _} {JbP : _ → Fin MP → SysOp _} (hJP : PublicSources J₀P JbP)
    {EJ EM EP GJ GM GP : Type}
    [NormedAddCommGroup EJ] [InnerProductSpace ℂ EJ] [CompleteSpace EJ] [FiniteDimensional ℂ EJ]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GJ] [InnerProductSpace ℂ GJ] [CompleteSpace GJ]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AJ : MeasuredSolver (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge)
      (meshOracle (jointFamilyAt s τ gbar h.toJointRange.s_ge h.tau_ge) σJ ιJ NJ dJ J₀J JbJ)
      EJ GJ ε)
    (AM : MeasuredSolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
      (meshOracle (mixedFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) σM ιM NM dM J₀M JbM)
      EM GM ε)
    (AP : MeasuredSolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge]))
      (meshOracle (precisionFamilyAt τ ε s h.s_ge (by linarith [h.tau_ge])) σP ιP NP dP J₀P
        JbP) EP GP ε) :
    combinedBound s τ gbar ε ≤
        max (AJ.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
          (max (AM.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
            (AP.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight))) ∧
      combinedBound s τ gbar ε ≤
        max (AJ.alg.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
          (max (AM.alg.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
            (AP.alg.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)))) := by
  have hv := combined_max_measured_mesh h (MeasuredMeshCost.of_measured σJ ιJ NJ dJ hJJ AJ)
    (MeasuredMeshCost.of_measured σM ιM NM dM hJM AM)
    (MeasuredMeshCost.of_measured σP ιP NP dP hJP AP)
  refine ⟨hv, hv.trans (max_le_max ?_ (max_le_max ?_ ?_))⟩ <;>
    exact_mod_cast DeferredMeasurementLowerBounds.Model.Measured.worstCost_mono _
      ODELowerBoundExtensions.Release.matrixWeight_value_le

/-- **Theorem `odel:thm:joint` at a measured solver over the released general-mesh oracle**: the
measured form of `AdaptiveODELowerBound.Release.joint_release_tree`. On `JointRange`, every
measured solver over the release's physical oracle on the joint family (any placement, spectator
index, slot count, degree and public source interfaces) makes at least `ḡ √s τ / 400` value calls
and as many matrix calls in the worst case. -/
theorem joint_release_measured_mesh (h : JointRange s τ gbar ε) {M : ℕ}
    (σ : Fin M → Fin (jointN τ + 2)) (ι : Type) [Fintype ι] [DecidableEq ι] (Nsl d : ℕ)
    {J₀ : _ → SysOp _} {Jb : _ → Fin M → SysOp _} (hJ : PublicSources J₀ Jb) {E G : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : MeasuredSolver (jointFamilyAt s τ gbar h.s_ge h.tau_ge)
      (meshOracle (jointFamilyAt s τ gbar h.s_ge h.tau_ge) σ ι Nsl d J₀ Jb) E G ε) :
    jointConst * gbar * Real.sqrt s * τ ≤
        A.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      jointConst * gbar * Real.sqrt s * τ ≤
        A.alg.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := by
  exact (measuredMeshForces_of_meshForces (joint_forces_mesh h)).1 M σ ι Nsl d J₀ Jb hJ E G A

/-- **Mixed family at a measured solver over the released general-mesh oracle** (eq.
`hsl:eq:mixrbound`): the measured form of
`AdaptiveODELowerBound.Release.mixed_release_tree`. For `L ≥ 64τ` and `s ≥ 64n/τ`, at least
`(log 2/(384√2)) √(sτr)` value calls, and as many matrix calls, in the worst case. -/
theorem mixed_release_measured_mesh (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) {M : ℕ} (σ : Fin M → Fin 1) (ι : Type) [Fintype ι]
    [DecidableEq ι] (Nsl d : ℕ) {J₀ : _ → SysOp _} {Jb : _ → Fin M → SysOp _}
    (hJ : PublicSources J₀ Jb) {E G : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : MeasuredSolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      (meshOracle (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) σ ι Nsl d J₀ Jb)
      E G ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤
        A.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤
        A.alg.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := by
  exact (measuredMeshForces_of_meshForces (mixed_forces_mesh h hL hs)).1 M σ ι Nsl d J₀ Jb hJ E G A

/-- **Precision family at a measured solver over the released general-mesh oracle** (eqs.
`hsl:eq:rbound`, `hsl:eq:failedmix`): the measured form of
`AdaptiveODELowerBound.Release.precision_release_tree`. For `L ≥ 64τ`, at least `r/32` value
calls in the worst case, and at least `√(sτr)/(64√2)` when `s < 64n/τ`; and as many matrix
calls. -/
theorem precision_release_measured_mesh (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    {M : ℕ} (σ : Fin M → Fin 1) (ι : Type) [Fintype ι] [DecidableEq ι] (Nsl d : ℕ)
    {J₀ : _ → SysOp _} {Jb : _ → Fin M → SysOp _} (hJ : PublicSources J₀ Jb) {E G : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : MeasuredSolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      (meshOracle (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) σ ι Nsl d J₀ Jb)
      E G ε) :
    (hsR τ ε / 32 ≤ A.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      hsR τ ε / 32 ≤ A.alg.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤
            A.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
          Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤
            A.alg.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) := by
  exact ⟨(measuredMeshForces_of_meshForces (precision_forces_mesh h hL)).1 M σ ι Nsl d J₀ Jb hJ
      E G A,
    fun hs' => (measuredMeshForces_of_meshForces (precision_forces_sqrt_mesh h hL hs')).1 M σ ι
      Nsl d J₀ Jb hJ E G A⟩

end

end ReleasedODESolverLowerBounds.Mesh
