import PhysicalODELowerBound.Mesh.Transfer
import PhysicalODELowerBound.Families.Herald

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Eq. `odel:eq:hsbound` over the general-mesh physical oracle, with controlled calls

Manuscript lines 4105-4109 (access with inverses and controls), 4114-4115 ("The lower bounds thus
apply to Theorems `ode:thm:main` and `ode:thm:time`"), 4392-4400 (eq. `odel:eq:hsbound`) and
4403-4435 (Lemma `odel:lem:herald`), for the time, mixed and precision families (one-stage, constant
coefficient, `D = 0`, `g = 1`) and adaptive solvers over the physical oracle of the released
general-mesh solver and over its call forms (`MeshForces`).

* `time_forces_mesh`, `mixed_forces_mesh`, `precision_forces_mesh`, `precision_forces_sqrt_mesh`:
  the per-family bounds with the constants of the Hamiltonian lower bound, from
  `Families.time_solver`, `mixed_solver`, `precision_solver` through `meshForces_of_growth` with
  the access conditions `AdaptiveHamiltonianLowerBound.Access.hardAccess_timeData`,
  `hardAccess_mixedMainData`, `hardAccess_precisionMainData`. For the oracle itself (no call
  forms) the mixed and precision bounds are the released
  `AdaptiveODELowerBound.Release.mixed_release_tree`, `precision_release_tree`.
* `herald_max_cost_mesh` (max form over realised counts) and `herald_witness_mesh` (family form):
  `c₀ (√s τ + √(sτr) + r)`, `c₀ = log 2/(4096π)` (`SparseLowerBounds.Hamiltonian.assembly`).
* `precision_terms_witness_mesh`: the precision terms `c₀ (√(sτr) + r)` of Theorem
  `odel:thm:combined` are witnessed by one of the `g = 1` families (lines 4143-4144).
-/

namespace PhysicalODELowerBound.Mesh

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open AdaptiveODELowerBound.Model (forces_or_of_cost₃)

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

variable {τ ε : ℝ} {s : ℕ}

/-- **Time family over the physical oracle** (eq. `hsl:eq:timelower`): on `HSRange`, the time
family mesh-forces `c_T √s τ`, `c_T = log 2/(192π)`. -/
theorem time_forces_mesh (h : HSRange τ s ε) :
    MeshForces (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) ε
      (cT * Real.sqrt s * τ) :=
  meshForces_of_growth (AdaptiveHamiltonianLowerBound.even_two_pow_hsMu h.s_ge) _ (fun j => j)
    (ConstantODELowerBound.Oracle.hardAccess_constData_ham _ _
      (AdaptiveHamiltonianLowerBound.Access.hardAccess_timeData τ s h.s_ge) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact Families.time_solver h hU w hO A)

/-- **Mixed family over the physical oracle** (eq. `hsl:eq:mixrbound`): for `L ≥ 64τ` and
`s ≥ 64n/τ`, the mixed family mesh-forces `(log 2/(384√2)) √(sτr)`. -/
theorem mixed_forces_mesh (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) :
    MeshForces (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε
      (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)) :=
  meshForces_of_growth (AdaptiveHamiltonianLowerBound.even_two_pow_hsMu h.s_ge) _ (fun j => j)
    (ConstantODELowerBound.Oracle.hardAccess_constData_ham _ _
      (AdaptiveHamiltonianLowerBound.Access.hardAccess_mixedMainData τ ε s h.s_ge) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact Families.mixed_solver h hL hs hU w hO A)

/-- **Precision family over the physical oracle** (eq. `hsl:eq:rbound`): for `L ≥ 64τ`, the
precision family mesh-forces `r/32`. -/
theorem precision_forces_mesh (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) :
    MeshForces (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε
      (hsR τ ε / 32) :=
  meshForces_of_growth even_two _ AdaptiveHamiltonianLowerBound.Access.toBits
    (ConstantODELowerBound.Oracle.hardAccess_constData_ham _ _
      (AdaptiveHamiltonianLowerBound.Access.hardAccess_precisionMainData τ ε s h.s_ge) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact (Families.precision_solver h hL hU w hO A).1)

/-- **Precision family for small sparsity over the physical oracle** (eq. `hsl:eq:failedmix`):
for `L ≥ 64τ` and `s < 64n/τ`, the precision family mesh-forces `√(sτr)/(64√2)`. -/
theorem precision_forces_sqrt_mesh (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : (s : ℝ) < 64 * precN τ ε / τ) :
    MeshForces (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε
      (Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2)) :=
  meshForces_of_growth even_two _ AdaptiveHamiltonianLowerBound.Access.toBits
    (ConstantODELowerBound.Oracle.hardAccess_constData_ham _ _
      (AdaptiveHamiltonianLowerBound.Access.hardAccess_precisionMainData τ ε s h.s_ge) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact (Families.precision_solver h hL hU w hO A).2 hs)

/-- **Eq. `odel:eq:hsbound` over the physical oracle, max form over realised counts**: for
realised worst-case value counts of adaptive solvers of the time, mixed and precision families
over the physical oracle or its call forms, `c₀ (√s τ + √(sτr) + r) ≤ max(q_T, q_M, q_P)`,
`c₀ = log 2/(4096π)`. -/
theorem herald_max_cost_mesh (h : HSRange τ s ε) {qT qM qP : ℝ}
    (hT : MeshCost (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) ε qT)
    (hM : MeshCost (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε qM)
    (hP : MeshCost (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε qP) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ max qT (max qM qP) :=
  assembly h ((time_forces_mesh h).le_cost hT)
    (fun hL => ⟨(precision_forces_mesh h hL).le_cost hP,
      fun hs' => (precision_forces_sqrt_mesh h hL hs').le_cost hP⟩)
    (fun hL hs => (mixed_forces_mesh h hL hs).le_cost hM)

/-- **Eq. `odel:eq:hsbound` over the physical oracle, family form**: on `HSRange` and for any
`ḡ ≥ 1`, one of the time, mixed and precision families is in the class (`η = 1`, `T = τ`,
`g ≤ ḡ`) and forces `c₀ (√s τ + √(sτr) + r)` value calls (and as many matrix calls) on every
adaptive solver over the general-mesh physical oracle or its call forms,
`c₀ = log 2/(4096π)`. -/
theorem herald_witness_mesh (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar) :
    MeshWitnesses (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeshWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeshWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hf := forces_or_of_cost₃
    (P₁ := MeshCost (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) ε)
    (P₂ := MeshCost (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε)
    (P₃ := MeshCost (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε)
    (b := c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε))
    (fun _ _ _ hT hM hP => herald_max_cost_mesh h hT hM hP)
  rcases hf with hf | hf | hf
  · exact Or.inl ⟨timeFamilyAt_inClass h hg, timeFamilyAt_T h, meshForces_of_cost hf⟩
  · exact Or.inr (Or.inl ⟨mixedFamilyAt_inClass h hg, mixedFamilyAt_T h, meshForces_of_cost hf⟩)
  · exact Or.inr (Or.inr ⟨precisionFamilyAt_inClass h hg, precisionFamilyAt_T h,
      meshForces_of_cost hf⟩)

/-- **The precision terms of Theorem `odel:thm:combined` over the general-mesh physical oracle are
witnessed by `g = 1` families** (fourth sentence of the theorem, lines 4143-4144): on `HSRange`, for
any `ḡ ≥ 1`, one of the homogeneous constant-coefficient families with `D = 0` and `g = 1` (time,
mixed, precision) witnesses `c₀ (√(sτr) + r)` on every adaptive solver over the physical oracle or
its call forms. From `herald_witness_mesh` by `MeshWitnesses.mono`. -/
theorem precision_terms_witness_mesh (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar) :
    MeshWitnesses (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeshWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeshWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hS : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) h.tau_pos.le
  have hb : c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) :=
    mul_le_mul_of_nonneg_left (by linarith) c0_pos.le
  rcases herald_witness_mesh h hg with hw | hw | hw
  · exact Or.inl (hw.mono hb)
  · exact Or.inr (Or.inl (hw.mono hb))
  · exact Or.inr (Or.inr (hw.mono hb))

end

end PhysicalODELowerBound.Mesh
