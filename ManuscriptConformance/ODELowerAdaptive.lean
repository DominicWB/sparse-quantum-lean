import ManuscriptConformance.ODELower
import AdaptiveODELowerBound.Theorem
import AdaptiveODELowerBound.Psd.Theorem

/-!
# Conformance: differential-equation lower bounds for adaptive solvers

Theorems `odel:thm:combined`, `odel:thm:joint` and `odel:thm:psd` and Proposition
`odel:rem:homogeneous`, in the input class of `ManuscriptConformance.ODELower` (Section
`odel:sec:main`), for the adaptive solver class of `AdaptiveODELowerBound`:

* **Access.** The coherent sampled-time native sparse access `F.access ι` (value oracle and
  in-place locators, time address coherent, untouched branch register `ι`) with forward and
  inverse calls (`MultiOracleCircuit.Program`), and its call forms
  `AdaptiveODELowerBound.Access.callFamily (F.access ι)`: every label as a plain, inverse,
  controlled or controlled-inverse call on one control qubit ⊗ workspace.
* **Solvers** (`AdaptiveODELowerBound.Model.TreeSolver`, forcing `Model.TreeForces`). A finite
  classical decision tree of fresh measured runs (each a program on a public unit seed followed by
  a two-outcome flag measurement), branching on the outcomes, ending in a heralded fresh-trial
  protocol; an isometric readout into system ⊗ garbage; success probability at least `2/3` on
  every input; conditional output within `ε` of `x(T)/‖x(T)‖` in the observable form of trace
  distance (`AdaptiveHamiltonianLowerBound.DensityAccurate`: every system observable of norm at
  most one has expectation within `2ε`). This is the observable form of the manuscript's
  trace-distance requirement (trace-distance contractivity, as in
  `abs_corr_sub_le_of_traceDistanceLE`); the implication from the trace distance of the reduced
  output is not restated as a lemma here. The count is the worst case over transcripts
  (`Tree.worstCost`), every run, attempt and inverse call counted; value calls and all calls are
  both bounded below.

Every forcing statement here implies the corresponding one of `ManuscriptConformance.ODELower`
(`AdaptiveODELowerBound.Model.treeForces_forces`, then `forcesODE_of_forces`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding SparseLowerBounds
open SparseLowerBounds.Hamiltonian SparseLowerBounds.ODE
open AdaptiveODELowerBound.Model (TreeForces)
open scoped InnerProduct InnerProductSpace ComplexOrder

set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

set_option maxHeartbeats 4000000 in
/-- **Theorem `odel:thm:combined`, adaptive solvers** (eq. `odel:eq:combined`). For `s ≥ 32`,
`τ ≥ 4`, `ḡ ≥ 2` and `0 < ε ≤ 1/64`, every adaptive solver for the time-dependent class (`η = 1`,
`T = τ`, `g ≤ ḡ`) has worst-case matrix-query complexity `Q_A ≥ c (ḡ√s τ + √(sτr) + r)`,
`r = L/log(e + L/τ)`, with the absolute constant `c = log 2/(8192π)`: some family in the class
forces this bound. The first term is witnessed by an inhomogeneous time-dependent family with
`D = 0` and `ḡ/√2 ≤ g ≤ ḡ`; the last two terms by a homogeneous constant-coefficient family
(one stage) with `D = 0` and `g = 1`. Solvers: classical decision trees of fresh measured runs
ending in a heralded protocol, each run a circuit program over the coherent sampled-time access
with forward and inverse calls, or over its call forms (plain, inverse, controlled and
controlled-inverse calls); accuracy in the observable form of trace distance. Formal
restrictions: controlled calls have one control qubit per call; measurements inside a run with the
post-measurement state kept are not in this solver class. -/
theorem odel_thm_combined_adaptive :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : ℕ) (τ gbar ε : ℝ), 32 ≤ s → 4 ≤ τ → 2 ≤ gbar → 0 < ε →
      ε ≤ 1 / 64 →
      (∃ (X N Z : Type) (_ : Fintype N) (_ : DecidableEq N) (_ : Fintype Z) (_ : AddCommGroup Z)
          (K : ℕ) (F : Family X N Z K s),
        F.InClass 1 gbar ∧ F.T = τ ∧
          TreeForces F ε
            (c * (gbar * Real.sqrt s * τ + Real.sqrt (s * τ * hslR τ ε) + hslR τ ε))) ∧
      (∃ (X N Z : Type) (_ : Fintype N) (_ : DecidableEq N) (_ : Fintype Z) (_ : AddCommGroup Z)
          (K : ℕ) (F : Family X N Z K s),
        F.InClass 1 gbar ∧ F.T = τ ∧ (∃ k, F.src k ≠ 0) ∧
          (∀ x k, ∃ H : Matrix N N ℂ, H.IsHermitian ∧ F.data.matrix (x, k) = Complex.I • H) ∧
          (∀ x sol, F.Solves x sol →
            gbar / Real.sqrt 2 ≤ F.mass / ‖sol F.T‖ ∧ F.mass / ‖sol F.T‖ ≤ gbar) ∧
          TreeForces F ε (c * (gbar * Real.sqrt s * τ))) ∧
      (∃ (X N Z : Type) (_ : Fintype N) (_ : DecidableEq N) (_ : Fintype Z) (_ : AddCommGroup Z)
          (F : Family X N Z 1 s),
        F.InClass 1 1 ∧ F.T = τ ∧ (∀ k, F.src k = 0) ∧
          (∀ x k, ∃ H : Matrix N N ℂ, H.IsHermitian ∧ F.data.matrix (x, k) = Complex.I • H) ∧
          (∀ x sol, F.Solves x sol → F.mass / ‖sol F.T‖ = 1) ∧
          TreeForces F ε (c * (Real.sqrt (s * τ * hslR τ ε) + hslR τ ε))) := by
  refine ⟨combinedConst, combinedConst_pos, ?_⟩
  intro s τ gbar ε hs hτ hg hε hε1
  have h : CombinedRange s τ gbar ε := ⟨hs, hτ, hg, hε, hε1⟩
  have hH := h.toHSRange
  have hJ := h.toJointRange
  obtain ⟨hIT, hIM, hIP, -, -, -⟩ := hard_instances hH
  have hc0 : combinedConst ≤ c0 := by rw [combinedConst_eq]; linarith [c0_pos]
  have hr := hH.hsR_pos
  have hsr : 0 ≤ Real.sqrt (s * τ * hsR τ ε) + hsR τ ε := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rcases AdaptiveODELowerBound.combined_tree h with hw | hw | hw
    · exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _, _,
        hw.inClass, hw.time_eq, hw.forces⟩
    · exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _, _,
        hw.inClass, hw.time_eq, hw.forces⟩
    · exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _, _,
        hw.inClass, hw.time_eq, hw.forces⟩
  · have hw := AdaptiveODELowerBound.Joint.joint_witness_tree hJ
    obtain ⟨hsrc, hskew, hgr, -⟩ := joint_conformance hJ
    refine ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _, _,
      hw.inClass, hw.time_eq, hsrc, hskew, hgr, (hw.mono ?_).forces⟩
    have h1 : combinedConst ≤ jointConst := hc0.trans c0_le_jointConst
    have h2 : 0 ≤ gbar * Real.sqrt s * τ := by
      have := Real.sqrt_nonneg (s : ℝ)
      have : 0 ≤ gbar := by linarith
      have : 0 ≤ τ := by linarith
      positivity
    calc combinedConst * (gbar * Real.sqrt s * τ) ≤ jointConst * (gbar * Real.sqrt s * τ) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = jointConst * gbar * Real.sqrt s * τ := by ring
  · have hb : combinedConst * (Real.sqrt (s * τ * hslR τ ε) + hslR τ ε) ≤
        c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) := mul_le_mul_of_nonneg_right hc0 hsr
    rcases AdaptiveODELowerBound.precision_terms_witness_tree hH (le_refl (1 : ℝ)) with
      hw | hw | hw
    · obtain ⟨hsrc, hskew, hg1⟩ := hamFamily_conformance (timeData τ s hH.s_ge) τ
        (by linarith [hH.one_le_tau]) (searchInput (timeN τ) (hsMu s) s) hIT.isHermitian
        (norm_searchInput _ _ _)
      exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _,
        hw.inClass, hw.time_eq, hsrc, hskew, hg1, (hw.mono hb).forces⟩
    · obtain ⟨hsrc, hskew, hg1⟩ := hamFamily_conformance (mixedMainData τ ε s hH.s_ge) τ
        (by linarith [hH.one_le_tau]) (searchInput (precN τ ε) (hsMu s) s) hIM.isHermitian
        (norm_searchInput _ _ _)
      exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _,
        hw.inClass, hw.time_eq, hsrc, hskew, hg1, (hw.mono hb).forces⟩
    · obtain ⟨hsrc, hskew, hg1⟩ := hamFamily_conformance (precisionMainData τ ε s hH.s_ge) τ
        (by linarith [hH.one_le_tau]) (scalarInput (precN τ ε) s) hIP.isHermitian
        (norm_scalarInput _ _)
      exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _,
        hw.inClass, hw.time_eq, hsrc, hskew, hg1, (hw.mono hb).forces⟩

set_option maxHeartbeats 4000000 in
/-- **Theorem `odel:thm:joint`, adaptive solvers** (eq. `odel:eq:joint`). For `s ≥ 4`, `τ ≥ 4`,
`ḡ ≥ 2` and `0 < ε ≤ 1/64`, the ODE promise `g ≤ ḡ` requires `Q_A ≥ c ḡ√s τ` of every adaptive
solver, with the absolute constant `c = 1/400`. The hard family is in the class with `D = 0`,
`η = 1`, `T = τ` and `g ≥ ḡ/√2`, and has dimension at most `3ḡ²s` (`O(ḡ²s)`). Solvers: classical
decision trees of fresh measured runs ending in a heralded protocol, each run a circuit program
over the coherent sampled-time access with forward and inverse calls, or over its call forms
(plain, inverse, controlled and controlled-inverse calls); accuracy in the observable form of
trace distance. Formal restrictions: controlled calls have one control qubit per call;
measurements inside a run with the post-measurement state kept are not in this solver class. -/
theorem odel_thm_joint_adaptive :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : ℕ) (τ gbar ε : ℝ), 4 ≤ s → 4 ≤ τ → 2 ≤ gbar → 0 < ε →
      ε ≤ 1 / 64 →
      ∃ (X N Z : Type) (_ : Fintype N) (_ : DecidableEq N) (_ : Fintype Z) (_ : AddCommGroup Z)
          (K : ℕ) (F : Family X N Z K s),
        F.InClass 1 gbar ∧ F.T = τ ∧
          (∀ x k, ∃ H : Matrix N N ℂ, H.IsHermitian ∧ F.data.matrix (x, k) = Complex.I • H) ∧
          (∀ x sol, F.Solves x sol → gbar / Real.sqrt 2 ≤ F.mass / ‖sol F.T‖) ∧
          (Fintype.card N : ℝ) ≤ 3 * gbar ^ 2 * s ∧
          TreeForces F ε (c * gbar * Real.sqrt s * τ) := by
  refine ⟨jointConst, by norm_num [jointConst], ?_⟩
  intro s τ gbar ε hs hτ hg hε hε1
  have hJ : JointRange s τ gbar ε := ⟨hs, hτ, hg, hε, hε1⟩
  have hw := AdaptiveODELowerBound.Joint.joint_witness_tree hJ
  obtain ⟨-, hskew, hgr, hcard⟩ := joint_conformance hJ
  exact ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _, _, hw.inClass,
    hw.time_eq, hskew, fun x sol hs' => (hgr x sol hs').1, hcard, hw.forces⟩

set_option maxHeartbeats 4000000 in
/-- **Proposition `odel:rem:homogeneous`, adaptive solvers**. When `τ ≥ 20(1 + log ḡ)` (with
`s ≥ 4`, `ḡ ≥ 2`, `0 < ε ≤ 1/64`), the joint lower bound `Q_A ≥ c ḡ√s τ` (`c = 1/500`) for every
adaptive solver also has a homogeneous (`b = 0`) time-dependent witness in the class, with
`g = Θ(ḡ)`: `(4/√34) ḡ ≤ g ≤ ḡ`; its dimension is at most `6ḡ²s`. Solvers: classical decision
trees of fresh measured runs ending in a heralded protocol, each run a circuit program over the
coherent sampled-time access with forward and inverse calls, or over its call forms (plain,
inverse, controlled and controlled-inverse calls); accuracy in the observable form of trace
distance. Formal restrictions: controlled calls have one control qubit per call; measurements
inside a run with the post-measurement state kept are not in this solver class. -/
theorem odel_rem_homogeneous_adaptive :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : ℕ) (τ gbar ε : ℝ), 4 ≤ s → 2 ≤ gbar →
      20 * (1 + Real.log gbar) ≤ τ → 0 < ε → ε ≤ 1 / 64 →
      ∃ (X N Z : Type) (_ : Fintype N) (_ : DecidableEq N) (_ : Fintype Z) (_ : AddCommGroup Z)
          (K : ℕ) (F : Family X N Z K s),
        F.InClass 1 gbar ∧ F.T = τ ∧ (∀ k, F.src k = 0) ∧
          (∀ x sol, F.Solves x sol →
            4 / Real.sqrt 34 * gbar ≤ F.mass / ‖sol F.T‖ ∧ F.mass / ‖sol F.T‖ ≤ gbar) ∧
          (Fintype.card N : ℝ) ≤ 6 * gbar ^ 2 * s ∧
          TreeForces F ε (c * gbar * Real.sqrt s * τ) := by
  refine ⟨ODELowerBoundExtensions.Homogeneous.homConst,
    by norm_num [ODELowerBoundExtensions.Homogeneous.homConst], ?_⟩
  intro s τ gbar ε hs hg hτ hε hε1
  have h : ODELowerBoundExtensions.Homogeneous.HomRange s τ gbar ε := ⟨hs, hg, hτ, hε, hε1⟩
  have hw := AdaptiveODELowerBound.Joint.hom_witness_tree h
  have hT : (ODELowerBoundExtensions.Homogeneous.homFamilyAt s τ gbar h.s_ge h.gbar_ge
      h.tau_ge).T = τ := ODELowerBoundExtensions.Homogeneous.homFamily_T
  refine ⟨_, _, _, inferInstance, inferInstance, inferInstance, inferInstance, _, _, hw.inClass,
    hw.time_eq, ODELowerBoundExtensions.Homogeneous.homFamilyAt_src hs hg hτ, fun x sol hs' => ?_,
    (ODELowerBoundExtensions.Homogeneous.hom_instance_props hs hg).2.2, hw.forces⟩
  have hu : sol (ODELowerBoundExtensions.Homogeneous.homFamilyAt s τ gbar h.s_ge h.gbar_ge
      h.tau_ge).T = ODELowerBoundExtensions.Homogeneous.homSol (jointM gbar)
        (ODELowerBoundExtensions.Homogeneous.homN τ) (jointMu s) s x
        (ODELowerBoundExtensions.Homogeneous.homFamilyAt s τ gbar h.s_ge h.gbar_ge h.tau_ge).T :=
    (ODELowerBoundExtensions.Homogeneous.homFamilyAt s τ gbar h.s_ge h.gbar_ge
      h.tau_ge).solves_endpoint_unique hs'
      (ODELowerBoundExtensions.Homogeneous.homSol_solves _ _ _ x)
  rw [hu, hT]
  exact ODELowerBoundExtensions.Homogeneous.hom_g_theta h x

set_option maxHeartbeats 4000000 in
/-- **Theorem `odel:thm:psd`, adaptive solvers** (eq. `odel:eq:psd`). Let `s ≥ 32`, `τ ≥ 2` and
`L = log(1/ε) ≥ 64τ`. For the homogeneous equation `ẋ = -D_X x` there are hard families with
`D_X ⪰ 0`, `‖D_X‖ = η_D = 1`, `T = τ`, `1 ≤ g ≤ √2`, public supports and dyadic entries
(`HardInstance` of the data: real symmetric, exact dyadic words, operator norm exactly one,
row and column norms at most one, input-independent location lists and extensions), in the
class with `η = 1` and `ḡ = √2`, for which `Q_A ≥ c (√(sτr) + r)`, `c = log 2/(3072√2)`, for every
adaptive solver with the heralded output; the same range and constant as `odel_thm_psd`. Solvers:
classical decision trees of fresh measured runs ending in a heralded protocol, each run a circuit
program over the coherent sampled-time access with forward and inverse calls, or over its call
forms (plain, inverse, controlled and controlled-inverse calls); accuracy in the observable form
of trace distance. Formal restrictions: controlled calls have one control qubit per call;
measurements inside a run with the post-measurement state kept are not in this solver class (the
package's range is `τ ≥ 1`). -/
theorem odel_thm_psd_adaptive :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : ℕ) (τ ε : ℝ), 32 ≤ s → 2 ≤ τ → 0 < ε → 64 * τ ≤ logInv ε →
      ∃ (X N : Type) (_ : Fintype N) (_ : DecidableEq N) (B : ℕ) (F : Family X N (Word B) 1 s),
        HardInstance F.data ∧ (∀ y, (F.data.matrix y).PosSemidef) ∧ (∀ k, F.src k = 0) ∧
          F.T = τ ∧ F.InClass 1 (Real.sqrt 2) ∧
          (∀ x sol, F.Solves x sol →
            1 ≤ F.mass / ‖sol F.T‖ ∧ F.mass / ‖sol F.T‖ ≤ Real.sqrt 2) ∧
          TreeForces F ε (c * (Real.sqrt (s * τ * hslR τ ε) + hslR τ ε)) := by
  refine ⟨ODELowerBoundExtensions.Psd.psdConst, ODELowerBoundExtensions.Psd.psdConst_pos, ?_⟩
  intro s τ ε hs hτ hε hL
  have h := ODELowerBoundExtensions.Psd.PsdRange.of_paper hs hτ hε hL
  rcases AdaptiveODELowerBound.Psd.psd_tree h le_rfl with hw | hw
  · refine ⟨_, _, inferInstance, inferInstance, _, _,
      ODELowerBoundExtensions.Psd.hardInstance_oneStageData
        (ODELowerBoundExtensions.Psd.psdSearchData_hardInstance h.one_le_precN
          (ODELowerBoundExtensions.Psd.two_mul_psdM_add_one_le h.s_ge)),
      fun y => ODELowerBoundExtensions.Psd.psdSearchMat_posSemidef (τ / 2) y.1,
      fun _ => rfl, hw.time_eq, hw.inClass, fun x sol hs' => ?_, hw.forces⟩
    have hu : sol (ODELowerBoundExtensions.Psd.psdSearchFamilyAt h).T =
        ODELowerBoundExtensions.Psd.heat ((ODELowerBoundExtensions.Psd.psdSearchDataAt h).matrix x)
          (ODELowerBoundExtensions.Psd.psdSearchFamilyAt h).T
          (searchInput (precN τ ε) (ODELowerBoundExtensions.Psd.psdMu s) s) :=
      (ODELowerBoundExtensions.Psd.psdSearchFamilyAt h).solves_endpoint_unique hs'
        (ODELowerBoundExtensions.Psd.heatFamily_solves _ _ _ _ x)
    rw [hu, ODELowerBoundExtensions.Psd.psdSearchFamilyAt_T h]
    exact (ODELowerBoundExtensions.Psd.psdSearchFamilyAt_props h x).2.2.2.2
  · refine ⟨_, _, inferInstance, inferInstance, _, _,
      ODELowerBoundExtensions.Psd.hardInstance_oneStageData
        (ODELowerBoundExtensions.Psd.psdScalarData_hardInstance h.one_le_precN
          (by have := h.s_ge; omega)),
      fun y => ODELowerBoundExtensions.Psd.psdScalarMat_posSemidef (τ / 2) y.1,
      fun _ => rfl, hw.time_eq, hw.inClass, fun x sol hs' => ?_, hw.forces⟩
    have hu : sol (ODELowerBoundExtensions.Psd.psdScalarFamilyAt h).T =
        ODELowerBoundExtensions.Psd.heat ((ODELowerBoundExtensions.Psd.psdScalarDataAt h).matrix x)
          (ODELowerBoundExtensions.Psd.psdScalarFamilyAt h).T (scalarInput (precN τ ε) s) :=
      (ODELowerBoundExtensions.Psd.psdScalarFamilyAt h).solves_endpoint_unique hs'
        (ODELowerBoundExtensions.Psd.heatFamily_solves _ _ _ _ x)
    rw [hu, ODELowerBoundExtensions.Psd.psdScalarFamilyAt_T h]
    exact (ODELowerBoundExtensions.Psd.psdScalarFamilyAt_props h x).2.2.2.2

end

end ManuscriptConformance
