import ReleasedODESolverLowerBounds.Runs.Exists
import PhysicalODELowerBound.Mesh.Joint
import PhysicalODELowerBound.Mesh.Psd
import DeferredMeasurementLowerBounds.Corollaries.ODESolver

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Runs of the released general-mesh solver on the positive semidefinite and homogeneous families

Manuscript Theorem `odel:thm:psd` (`D_X ⪰ 0`, `‖D_X‖ = η_D = 1`, `T = τ`), Proposition
`odel:rem:homogeneous` (the known dissipative generator `-P_reject`) and Section `odel:sec:main`
("the lower bounds apply to the upper bounds of the preceding section"); Theorem `ode:thm:time`.

* `psd_meshRuns_exist`: on `PsdRange` with `ḡ ≥ √2`, runs of the released general-mesh solver
  on the gadget and scalar positive semidefinite families exist with `η_H = 0`, `η_D = 1`
  (`Θ = τ ℓ`).
* `psd_meshRun_bounds`: at such runs, `psdConst (√(sτr) + r) ≤ max(V_G, V_S) ≤ max(Q_G, Q_S)` and
  `max(Q_G, Q_S) ≤ 1274019840 · 2ḡ · queryShape(s, τℓ, ℓ)` (lower half
  `PhysicalODELowerBound.Mesh.psd_max_cost_mesh`, upper half the released certificate).
* `hom_meshRun_exists`, `hom_meshRun_bounds`: on `HomRange`, runs on the homogeneous family exist
  with `η_H = η_D = 1` (`Θ = τ + τ ℓ`), and every run satisfies
  `ḡ √s τ / 500 ≤ V ≤ Q ≤ 1274019840 · 2ḡ · queryShape(s, τ + τℓ, ℓ)` (lower half
  `PhysicalODELowerBound.Mesh.hom_witness_mesh`).
* `psd_meshRun_bracket`, `hom_meshRun_bracket`: the brackets are attained.
* `MeshRun.exists_measuredSolver`: every run is a measured solver over the physical oracle with
  the same worst-case counts (`DeferredMeasurementLowerBounds.Corollaries.MeasuredSolver.ofTreeSolver`),
  so the measured lower bounds of `ReleasedODESolverLowerBounds.Mesh` apply to the released
  solver itself.

As for `ConstantODELowerBound.Runs.psd_const_bounds`, the two sides are stated side by side
only: the manuscript proves no matching bound for the dissipative subclass.
-/

namespace ReleasedODESolverLowerBounds.Runs

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE
open NativeSparseBlockEncoding OracleCircuit TimeDependentExtensions
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open ODELowerBoundExtensions.Release (releaseOracle refineData releaseLog)
open ODELowerBoundExtensions.Psd (PsdRange psdSearchFamilyAt psdScalarFamilyAt psdBound)
open ODELowerBoundExtensions.Homogeneous (HomRange homFamilyAt homConst)
open DeferredMeasurementLowerBounds.Corollaries (MeasuredSolver)
open scoped ComplexOrder

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

variable {s : ℕ} {τ gbar ε : ℝ}

/-- **Runs on the positive semidefinite families exist** (`η_H = 0`, `η_D = 1`). -/
theorem psd_meshRuns_exist (h : PsdRange τ s ε) (hg : Real.sqrt 2 ≤ gbar) :
    Nonempty (MeshRun (psdSearchFamilyAt h) τ gbar ε 0 1) ∧
      Nonempty (MeshRun (psdScalarFamilyAt h) τ gbar ε 0 1) := by
  have hg1 : 1 ≤ gbar := le_trans (Real.one_le_sqrt.mpr (by norm_num)) hg
  have hτ : 0 < τ := by linarith [h.one_le_tau]
  have hε := h.eps_pos
  have hε1 : ε ≤ 1 := by linarith [h.toHSRange.eps_le]
  have hρ : 0 < 0 + TimeDependentODE.radius gbar ε * 1 := by
    rw [zero_add, mul_one]
    unfold TimeDependentODE.radius
    have hr : 1 ≤ TimeDependentODE.ratio gbar := by unfold TimeDependentODE.ratio; linarith
    have ha : 0 < TimeDependentODE.accuracy ε := by unfold TimeDependentODE.accuracy; linarith
    have ha1 : TimeDependentODE.accuracy ε ≤ 1 := by
      unfold TimeDependentODE.accuracy; linarith
    have h1 := ODEGaussianParameters.width_ge_two _ _ hr ha ha1
    have h2 := ODEGaussianParameters.cutoff_le_radius _ _ hr ha ha1
    linarith
  constructor
  · have hF := ODELowerBoundExtensions.Psd.psdSearchFamilyAt_inClass h hg
    have hH : ∀ j, ((ODELowerBoundExtensions.Psd.psdSearchDataAt h).matrix j).IsHermitian :=
      fun j => by
        rw [ODELowerBoundExtensions.Psd.psdSearchDataAt_matrix]
        exact (ODELowerBoundExtensions.Psd.psdSearchMat_posSemidef _ j).isHermitian
    have hz : ∀ x k, ODEMatrixEnergy.hamiltonianPart
        ((psdSearchFamilyAt h).data.matrix (x, k)) = 0 :=
      fun x _ => ConstantODELowerBound.Solution.hamiltonianPart_of_isHermitian (hH x)
    have hd : ∀ x k, ODEMatrixEnergy.dissipativePart
        ((psdSearchFamilyAt h).data.matrix (x, k)) = (psdSearchFamilyAt h).data.matrix (x, k) :=
      fun x _ => ConstantODELowerBound.Solution.dissipativePart_of_isHermitian (hH x)
    have hB : 0 < (psdSearchFamilyAt h).mass := by
      rw [psdSearchFamilyAt, ODELowerBoundExtensions.Psd.heatFamily_mass, Hamiltonian.norm_searchInput]
      norm_num
    exact meshRun_nonempty _ hF (ODELowerBoundExtensions.Psd.psdSearchFamilyAt_T h) hτ hg1 hε
      hε1 hB one_pos le_rfl zero_le_one hρ (fun x k i => by rw [hz]; simp)
      (fun x k j => by rw [hz]; simp) (fun x k i => by rw [hd]; exact hF.row_norm x k i)
      (fun x k j => by rw [hd]; exact hF.col_norm x k j) Hamiltonian.refZero
  · have hF := ODELowerBoundExtensions.Psd.psdScalarFamilyAt_inClass h hg
    have hH : ∀ j, ((ODELowerBoundExtensions.Psd.psdScalarDataAt h).matrix j).IsHermitian :=
      fun j => by
        rw [ODELowerBoundExtensions.Psd.psdScalarDataAt_matrix]
        exact (ODELowerBoundExtensions.Psd.psdScalarMat_posSemidef _ j).isHermitian
    have hz : ∀ x k, ODEMatrixEnergy.hamiltonianPart
        ((psdScalarFamilyAt h).data.matrix (x, k)) = 0 :=
      fun x _ => ConstantODELowerBound.Solution.hamiltonianPart_of_isHermitian (hH x)
    have hd : ∀ x k, ODEMatrixEnergy.dissipativePart
        ((psdScalarFamilyAt h).data.matrix (x, k)) = (psdScalarFamilyAt h).data.matrix (x, k) :=
      fun x _ => ConstantODELowerBound.Solution.dissipativePart_of_isHermitian (hH x)
    have hB : 0 < (psdScalarFamilyAt h).mass := by
      rw [psdScalarFamilyAt, ODELowerBoundExtensions.Psd.heatFamily_mass, Hamiltonian.norm_scalarInput]
      norm_num
    exact meshRun_nonempty _ hF (ODELowerBoundExtensions.Psd.psdScalarFamilyAt_T h) hτ hg1 hε
      hε1 hB one_pos le_rfl zero_le_one hρ (fun x k i => by rw [hz]; simp)
      (fun x k j => by rw [hz]; simp) (fun x k i => by rw [hd]; exact hF.row_norm x k i)
      (fun x k j => by rw [hd]; exact hF.col_norm x k j) Hamiltonian.refZero

/-- **Theorem `odel:thm:psd` at the released general-mesh solver's runs**: the lower bound
`psdConst (√(sτr) + r)` on the larger of the two counts and the released upper bound with
`Θ = τ ℓ`. -/
theorem psd_meshRun_bounds (h : PsdRange τ s ε)
    (AG : MeshRun (psdSearchFamilyAt h) τ gbar ε 0 1)
    (AS : MeshRun (psdScalarFamilyAt h) τ gbar ε 0 1) :
    psdBound s τ ε ≤ max (AG.matrixQueries : ℝ) (AS.matrixQueries : ℝ) ∧
      max (AG.matrixQueries : ℝ) (AS.matrixQueries : ℝ) ≤
        1274019840 * TimeDependentODE.ratio gbar * ImprovedODEQueryBudget.queryShape s
          (τ * releaseLog gbar ε) (releaseLog gbar ε) ∧
      psdBound s τ ε ≤ max (AG.valueQueries : ℝ) (AS.valueQueries : ℝ) ∧
      max (AG.valueQueries : ℝ) (AS.valueQueries : ℝ) ≤
        max (AG.matrixQueries : ℝ) (AS.matrixQueries : ℝ) := by
  have hg0 : Real.sqrt 2 ≤ Real.sqrt 2 := le_rfl
  have hsolG : ∀ x, ∃ sol, (psdSearchFamilyAt h).Solves x sol := fun x =>
    ((ODELowerBoundExtensions.Psd.psdSearchFamilyAt_inClass h hg0).solution x).elim
      fun sol hs => ⟨sol, hs.1⟩
  have hsolS : ∀ x, ∃ sol, (psdScalarFamilyAt h).Solves x sol := fun x =>
    ((ODELowerBoundExtensions.Psd.psdScalarFamilyAt_inClass h hg0).solution x).elim
      fun sol hs => ⟨sol, hs.1⟩
  have hlow := PhysicalODELowerBound.Mesh.psd_max_cost_mesh h (meshCost_meshRun AG hsolG)
    (meshCost_meshRun AS hsolS)
  have cG : (AG.valueQueries : ℝ) ≤ AG.matrixQueries := by exact_mod_cast AG.valueQueries_le
  have cS : (AS.valueQueries : ℝ) ≤ AS.matrixQueries := by exact_mod_cast AS.valueQueries_le
  have e : meshTheta τ gbar ε 0 1 = τ * releaseLog gbar ε := by rw [meshTheta_eq]; ring
  obtain ⟨solG, hsG⟩ := hsolG (fun _ => 0)
  obtain ⟨solS, hsS⟩ := hsolS (fun _ => false)
  have uG := AG.matrixQueries_le _ solG hsG
  have uS := AS.matrixQueries_le _ solS hsS
  rw [e] at uG uS
  exact ⟨hlow.trans (max_le_max cG cS), max_le uG uS, hlow, max_le_max cG cS⟩

/-- **The bracket on the positive semidefinite families is attained** at runs of the released
general-mesh solver. -/
theorem psd_meshRun_bracket (h : PsdRange τ s ε) (hg : Real.sqrt 2 ≤ gbar) :
    ∃ (AG : MeshRun (psdSearchFamilyAt h) τ gbar ε 0 1)
      (AS : MeshRun (psdScalarFamilyAt h) τ gbar ε 0 1),
      psdBound s τ ε ≤ max (AG.matrixQueries : ℝ) (AS.matrixQueries : ℝ) ∧
        max (AG.matrixQueries : ℝ) (AS.matrixQueries : ℝ) ≤
          1274019840 * TimeDependentODE.ratio gbar * ImprovedODEQueryBudget.queryShape s
            (τ * releaseLog gbar ε) (releaseLog gbar ε) := by
  obtain ⟨⟨AG⟩, ⟨AS⟩⟩ := psd_meshRuns_exist h hg
  obtain ⟨h1, h2, -⟩ := psd_meshRun_bounds h AG AS
  exact ⟨AG, AS, h1, h2⟩

/-- **Runs on the homogeneous family exist** (`η_H = η_D = 1`). -/
theorem hom_meshRun_exists (h : HomRange s τ gbar ε) :
    Nonempty (MeshRun (homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge) τ gbar ε 1 1) := by
  have hW := PhysicalODELowerBound.Mesh.hom_witness_mesh h
  have hM := four_le_jointM h.gbar_ge
  have hs := h.s_ge
  have hl : 0 ≤ Real.log gbar := Real.log_nonneg (by linarith [h.gbar_ge])
  have hτ : 0 < τ := by linarith [h.tau_ge]
  have hB : 0 < (homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge).mass := by
    rw [homFamilyAt, ODELowerBoundExtensions.Homogeneous.homFamily_mass,
      ODELowerBoundExtensions.Homogeneous.norm_homInit (by omega)]
    norm_num
  exact meshRun_nonempty_of_inClass _ hW.inClass hW.time_eq hτ (by linarith [h.gbar_ge])
    h.eps_pos (by linarith [h.eps_le]) hB (by omega) (false, Sum.inr ⟨0, by omega⟩)

/-- **Proposition `odel:rem:homogeneous` at the released general-mesh solver's runs**: every run on
the homogeneous family makes at least `ḡ √s τ / 500` value calls, and at most the released
`1274019840 · 2ḡ · queryShape(s, τ + τℓ, ℓ)` matrix calls. -/
theorem hom_meshRun_bounds (h : HomRange s τ gbar ε)
    (A : MeshRun (homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge) τ gbar ε 1 1) :
    homConst * gbar * Real.sqrt s * τ ≤ A.valueQueries ∧ A.valueQueries ≤ A.matrixQueries ∧
      (A.matrixQueries : ℝ) ≤ 1274019840 * TimeDependentODE.ratio gbar *
        ImprovedODEQueryBudget.queryShape s (τ + τ * releaseLog gbar ε) (releaseLog gbar ε) := by
  have hW := PhysicalODELowerBound.Mesh.hom_witness_mesh h
  have hsol : ∀ x, ∃ sol, (homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge).Solves x sol :=
    fun x => (hW.inClass.solution x).elim fun sol hs => ⟨sol, hs.1⟩
  have hlow := (meshForces_meshRun hW.forces A hsol).1
  have hM := four_le_jointM h.gbar_ge
  have hs := h.s_ge
  have hl : 0 ≤ Real.log gbar := Real.log_nonneg (by linarith [h.gbar_ge])
  have hX : Nonempty (Promised (jointM gbar) (ODELowerBoundExtensions.Homogeneous.homN τ)
      (2 ^ jointMu s)) := by
    refine nonempty_promised (by omega)
      (ODELowerBoundExtensions.Homogeneous.one_le_homN (by linarith [h.tau_ge])) ?_
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ jointMu s := Nat.pow_le_pow_right (by norm_num) (one_le_jointMu (by omega))
  obtain ⟨x⟩ := hX
  obtain ⟨sol, hsx⟩ := hsol x
  have u := A.matrixQueries_le x sol hsx
  have e : meshTheta τ gbar ε 1 1 = τ + τ * releaseLog gbar ε := by rw [meshTheta_eq]; ring
  rw [e] at u
  exact ⟨hlow, by exact_mod_cast A.valueQueries_le, u⟩

/-- **The bracket on the homogeneous family is attained** at a run of the released general-mesh
solver. -/
theorem hom_meshRun_bracket (h : HomRange s τ gbar ε) :
    ∃ A : MeshRun (homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge) τ gbar ε 1 1,
      homConst * gbar * Real.sqrt s * τ ≤ A.valueQueries ∧
        (A.matrixQueries : ℝ) ≤ 1274019840 * TimeDependentODE.ratio gbar *
          ImprovedODEQueryBudget.queryShape s (τ + τ * releaseLog gbar ε) (releaseLog gbar ε) := by
  obtain ⟨A⟩ := hom_meshRun_exists h
  obtain ⟨h1, -, h3⟩ := hom_meshRun_bounds h A
  exact ⟨A, h1, h3⟩

/-- **Every run is a measured solver over the physical oracle with the same worst-case counts**
(on a family with an input, all of whose inputs are solvable). -/
theorem MeshRun.exists_measuredSolver {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z]
    [AddCommGroup Z] [DecidableEq Z] [Nonempty X] {K : ℕ} {F : Family X N Z K s}
    {etaH etaD : ℝ} (A : MeshRun F τ gbar ε etaH etaD) (hsol : ∀ x, ∃ sol, F.Solves x sol) :
    ∃ M : MeasuredSolver F
        (releaseOracle F A.R (TimeDependentODE.Index (refineData F.data A.R) τ gbar ε) A.slots
          A.degree A.J₀ A.Jb) (EuclideanSpace ℂ N) (EuclideanSpace ℂ N) ε,
      M.alg.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) = A.valueQueries ∧
        M.alg.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = A.matrixQueries := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨φ, hφ⟩ := DeferredMeasurementLowerBounds.Model.exists_unit_of_successMass_pos
    (AdaptiveODELowerBound.Model.retryToTree (A.release.toRetrySolver hsol A.i₀) ℂ).tree x
    (by linarith [(AdaptiveODELowerBound.Model.retryToTree
      (A.release.toRetrySolver hsol A.i₀) ℂ).success x])
  have hU := MeshSource.physicalOracle_unitary
    (ι := TimeDependentODE.Index (refineData F.data A.R) τ gbar ε)
    (ODELowerBoundExtensions.Release.stageData F.data
      (ODELowerBoundExtensions.Release.stageOf K A.R)) A.slots A.degree A.J₀ A.Jb
    A.sources_public.initial_unitary A.sources_public.forcing_unitary
  refine ⟨MeasuredSolver.ofTreeSolver hU
    (AdaptiveODELowerBound.Model.retryToTree (A.release.toRetrySolver hsol A.i₀) ℂ) φ hφ,
    ?_, ?_⟩ <;>
  · rw [MeasuredSolver.ofTreeSolver, DeferredMeasurementLowerBounds.Model.worstCost_ofTree]
    rfl

end

end ReleasedODESolverLowerBounds.Runs
