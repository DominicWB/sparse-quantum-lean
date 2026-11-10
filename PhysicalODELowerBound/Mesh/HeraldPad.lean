import PhysicalODELowerBound.Mesh.Transfer
import PhysicalODELowerBound.Families.Herald

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The padded `g = 1` families over the general-mesh physical oracle, with controlled calls

Manuscript: eq. `odel:eq:hsbound`, Lemma `odel:lem:herald` and the proof of Theorem
`odel:thm:combined` ("Pad dimensions to a common known size if desired"), for the known zero
paddings of the time, mixed and precision families
(`ODELowerBoundExtensions.Padding.timePadFamilyAt`, `mixedPadFamilyAt`, `precisionPadFamilyAt`:
`ẋ = -i(H ⊕ 0) x`, `x(0) = ψ_in ⊕ 0`, one stage) and adaptive solvers over the physical oracle of
the released general-mesh solver and over its call forms (`MeshForces`).

* `time_forces_pad_mesh`, `mixed_forces_pad_mesh`, `precision_forces_pad_mesh`,
  `precision_forces_sqrt_pad_mesh`: from `Families.time_pad_solver`, `mixed_pad_solver`,
  `precision_pad_solver` through `meshForces_of_growth` with the access conditions
  `AdaptiveODELowerBound.Padding.hardAccess_timePadData`, `hardAccess_mixedPadData`,
  `hardAccess_precisionPadData`.
* `herald_max_cost_pad_mesh` (max form over realised counts) and `herald_witness_pad_mesh`
  (family form, the instance facts `ODELowerBoundExtensions.Padding.herald_instances_pad`).
* `precision_terms_witness_pad_mesh`: the precision terms `c₀ (√(sτr) + r)` of Theorem
  `odel:thm:combined` are witnessed by one of the padded `g = 1` families.

Known padding registers range over `Type`, the universe of the families in `MeshForces` and
`ConstForces` and of the released normal-form lemma
`ODELowerBoundExtensions.Release.physicalOracle_normal_form` (the released physical oracles are
universe polymorphic); the sampled-time forms in `AdaptiveODELowerBound` allow any universe.
Nothing is lost: the common-dimension forms use `PadTo S Nd : Type`.
-/

namespace PhysicalODELowerBound.Mesh

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open ODELowerBoundExtensions.Padding (timePadFamilyAt mixedPadFamilyAt precisionPadFamilyAt)
open AdaptiveODELowerBound.Model (forces_or_of_cost₃)

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

variable {τ ε : ℝ} {s : ℕ}

/-- **Padded time family over the physical oracle**: on `HSRange`, for every known padding `P`,
the padded time family mesh-forces `c_T √s τ`. -/
theorem time_forces_pad_mesh (h : HSRange τ s ε) (P : Type) [Fintype P] [DecidableEq P] :
    MeshForces (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) P) ε
      (cT * Real.sqrt s * τ) :=
  meshForces_of_growth (AdaptiveHamiltonianLowerBound.even_two_pow_hsMu h.s_ge) _ (fun j => j)
    (ConstantODELowerBound.Oracle.hardAccess_constData_ham _ _
      (AdaptiveODELowerBound.Padding.hardAccess_timePadData τ s h.s_ge P) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact Families.time_pad_solver h P hU w hO A)

/-- **Padded mixed family over the physical oracle**: for `L ≥ 64τ`, `s ≥ 64n/τ` and every known
padding `P`, the padded mixed family mesh-forces `(log 2/(384√2)) √(sτr)`. -/
theorem mixed_forces_pad_mesh (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) (P : Type) [Fintype P] [DecidableEq P] :
    MeshForces (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) P) ε
      (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)) :=
  meshForces_of_growth (AdaptiveHamiltonianLowerBound.even_two_pow_hsMu h.s_ge) _ (fun j => j)
    (ConstantODELowerBound.Oracle.hardAccess_constData_ham _ _
      (AdaptiveODELowerBound.Padding.hardAccess_mixedPadData τ ε s h.s_ge P) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact Families.mixed_pad_solver h hL hs P hU w hO A)

/-- **Padded precision family over the physical oracle**: for `L ≥ 64τ` and every known padding
`P`, the padded precision family mesh-forces `r/32`. -/
theorem precision_forces_pad_mesh (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) (P : Type)
    [Fintype P] [DecidableEq P] :
    MeshForces (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) P) ε
      (hsR τ ε / 32) :=
  meshForces_of_growth even_two _ AdaptiveHamiltonianLowerBound.Access.toBits
    (ConstantODELowerBound.Oracle.hardAccess_constData_ham _ _
      (AdaptiveODELowerBound.Padding.hardAccess_precisionPadData τ ε s h.s_ge P) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact (Families.precision_pad_solver h hL P hU w hO A).1)

/-- **Padded precision family for small sparsity over the physical oracle**: for `L ≥ 64τ`,
`s < 64n/τ` and every known padding `P`, the padded precision family mesh-forces
`√(sτr)/(64√2)`. -/
theorem precision_forces_sqrt_pad_mesh (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : (s : ℝ) < 64 * precN τ ε / τ) (P : Type) [Fintype P] [DecidableEq P] :
    MeshForces (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) P) ε
      (Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2)) :=
  meshForces_of_growth even_two _ AdaptiveHamiltonianLowerBound.Access.toBits
    (ConstantODELowerBound.Oracle.hardAccess_constData_ham _ _
      (AdaptiveODELowerBound.Padding.hardAccess_precisionPadData τ ε s h.s_ge P) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact (Families.precision_pad_solver h hL P hU w hO A).2 hs)

/-- **Eq. `odel:eq:hsbound` for the padded families over the physical oracle, max form over
realised counts**: for any known paddings and realised worst-case value counts of adaptive
solvers of the padded time, mixed and precision families over the physical oracle or its call
forms, `c₀ (√s τ + √(sτr) + r) ≤ max(q_T, q_M, q_P)`. -/
theorem herald_max_cost_pad_mesh (h : HSRange τ s ε) (PT PM PP : Type) [Fintype PT]
    [DecidableEq PT] [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] {qT qM qP : ℝ}
    (hT : MeshCost (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) ε qT)
    (hM : MeshCost (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) ε qM)
    (hP : MeshCost (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) ε qP) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ max qT (max qM qP) :=
  assembly h ((time_forces_pad_mesh h PT).le_cost hT)
    (fun hL => ⟨(precision_forces_pad_mesh h hL PP).le_cost hP,
      fun hs' => (precision_forces_sqrt_pad_mesh h hL hs' PP).le_cost hP⟩)
    (fun hL hs => (mixed_forces_pad_mesh h hL hs PM).le_cost hM)

/-- **Eq. `odel:eq:hsbound` for the padded families over the physical oracle, family form**: on
`HSRange`, for any `ḡ ≥ 1` and any known paddings, one of the padded time, mixed and precision
families (`D = 0`, `g = 1`) is in the class and forces `c₀ (√s τ + √(sτr) + r)` value calls (and
as many matrix calls) on every adaptive solver over the general-mesh physical oracle or its call
forms. The instance facts (class, `T = τ`, maximum sparsity exactly `s`) are
`ODELowerBoundExtensions.Padding.herald_instances_pad`. -/
theorem herald_witness_pad_mesh (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar)
    (PT PM PP : Type) [Fintype PT] [DecidableEq PT] [Fintype PM] [DecidableEq PM]
    [Fintype PP] [DecidableEq PP] :
    MeshWitnesses (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeshWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeshWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hf := forces_or_of_cost₃
    (P₁ := MeshCost (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) ε)
    (P₂ := MeshCost (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) ε)
    (P₃ := MeshCost (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) ε)
    (b := c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε))
    (fun _ _ _ hT hM hP => herald_max_cost_pad_mesh h PT PM PP hT hM hP)
  have hI := ODELowerBoundExtensions.Padding.herald_instances_pad (ε := ε) h hg PT PM PP
  rcases hf with hf | hf | hf
  · exact Or.inl ⟨hI.1.1, hI.1.2.1, meshForces_of_cost hf⟩
  · exact Or.inr (Or.inl ⟨hI.2.1.1, hI.2.1.2.1, meshForces_of_cost hf⟩)
  · exact Or.inr (Or.inr ⟨hI.2.2.1, hI.2.2.2.1, meshForces_of_cost hf⟩)

/-- **The precision terms of Theorem `odel:thm:combined` over the general-mesh physical oracle are
witnessed by padded `g = 1` families** (fourth sentence of the theorem, Theorem `odel:thm:combined`,
with the padding of the proof of Theorem `odel:thm:combined`): on `HSRange`, for any `ḡ ≥ 1` and any
known paddings, one of the padded homogeneous constant-coefficient families with `D = 0` and `g = 1`
(time, mixed, precision) witnesses `c₀ (√(sτr) + r)` on every adaptive solver over the physical
oracle or its call forms. From `herald_witness_pad_mesh` by `MeshWitnesses.mono`. -/
theorem precision_terms_witness_pad_mesh (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar)
    (PT PM PP : Type) [Fintype PT] [DecidableEq PT] [Fintype PM] [DecidableEq PM]
    [Fintype PP] [DecidableEq PP] :
    MeshWitnesses (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeshWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      MeshWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hS : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) h.tau_pos.le
  have hb : c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) :=
    mul_le_mul_of_nonneg_left (by linarith) c0_pos.le
  rcases herald_witness_pad_mesh h hg PT PM PP with hw | hw | hw
  · exact Or.inl (hw.mono hb)
  · exact Or.inr (Or.inl (hw.mono hb))
  · exact Or.inr (Or.inr (hw.mono hb))

end

end PhysicalODELowerBound.Mesh
