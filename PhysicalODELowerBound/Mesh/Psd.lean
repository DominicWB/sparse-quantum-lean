import PhysicalODELowerBound.Mesh.Transfer
import PhysicalODELowerBound.Families.Psd

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Theorem `odel:thm:psd` over the general-mesh physical oracle, with controlled calls

Manuscript lines 4114-4115 ("The lower bounds thus apply to Theorems `ode:thm:main` and
`ode:thm:time`") and 4452-4571 (Theorem `odel:thm:psd`, eq. `odel:eq:psd`): the homogeneous
constant-coefficient families `ẋ = -D_X x` with `D_X ⪰ 0`, `‖D_X‖ = 1`, `T = τ`, `1 ≤ g ≤ √2`
(`ODELowerBoundExtensions.Psd.psdSearchFamilyAt`, `psdScalarFamilyAt`, one stage) and adaptive
solvers over the physical oracle of the released general-mesh solver and over its call forms
(`MeshForces`; retry protocols and released protocols of the general-mesh solver by
`MeshForces.retry`, `MeshForces.releaseProtocol`).

* `psd_search_forces_mesh` (`s ≥ 512n/τ`: `psdGadgetConst √(sτr)`), `psd_scalar_forces_mesh`
  (`r/32`), `psd_scalar_forces_sqrt_mesh` (`s < 512n/τ`: `√(sτr)/256`): from
  `Families.psd_search_solver`, `psd_scalar_solver` through `meshForces_of_growth` with the access
  conditions `AdaptiveODELowerBound.Psd.hardAccess_psdSearchData`, `hardAccess_psdScalarData`.
* `psd_max_cost_mesh` (max form over realised counts) and `psd_mesh` (family form, eq.
  `odel:eq:psd`): `psdConst (√(sτr) + r)`, `psdConst = log 2/(3072√2)`
  (`ODELowerBoundExtensions.Psd.psd_assembly`), on `PsdRange` (`τ ≥ 1`, which contains the
  manuscript's `τ ≥ 2`).

As in the manuscript (lines 4573-4578), no constant-error `Ω(√s τ)` bound is asserted for the
purely dissipative subclass.
-/

namespace PhysicalODELowerBound.Mesh

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open ODELowerBoundExtensions.Psd
open AdaptiveODELowerBound.Model (forces_or_of_cost₂)

-- The release's physical workspace is a nested register product (as in `MeshSource`).
set_option synthInstance.maxSize 8192

variable {τ ε : ℝ} {s : ℕ}

/-- **The gadget family over the physical oracle** (lines 4547-4553): for `s ≥ 512n/τ`, the
gadget family mesh-forces `psdGadgetConst √(sτr)`, `psdGadgetConst = log 2/(1536√2)`. -/
theorem psd_search_forces_mesh (h : PsdRange τ s ε) (hs : 512 * (precN τ ε : ℝ) / τ ≤ s) :
    MeshForces (psdSearchFamilyAt h) ε (psdGadgetConst * Real.sqrt (s * τ * hsR τ ε)) :=
  meshForces_of_growth
    ((Nat.even_pow' (by have := one_le_psdMu h.s_ge; omega)).mpr even_two) _ (fun j => j)
    (ConstantODELowerBound.Oracle.hardAccess_constData_heat _ _
      (AdaptiveODELowerBound.Psd.hardAccess_psdSearchData (precN τ ε) (psdMu s) s (τ / 2)
        h.one_le_precN (two_mul_psdM_add_one_le h.s_ge)) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact Families.psd_search_solver h hs hU w hO A)

/-- **The scalar family over the physical oracle** (lines 4555-4562): the scalar family
mesh-forces `r/32`. -/
theorem psd_scalar_forces_mesh (h : PsdRange τ s ε) :
    MeshForces (psdScalarFamilyAt h) ε (hsR τ ε / 32) :=
  meshForces_of_growth even_two _ AdaptiveHamiltonianLowerBound.Access.toBits
    (ConstantODELowerBound.Oracle.hardAccess_constData_heat _ _
      (AdaptiveODELowerBound.Psd.hardAccess_psdScalarData (precN τ ε) s (τ / 2) h.one_le_precN
        (by have := h.s_ge; omega)) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact (Families.psd_scalar_solver h hU w hO A).1)

/-- **The scalar family for small sparsity over the physical oracle** (lines 4565-4568): for
`s < 512n/τ`, the scalar family mesh-forces `√(sτr)/256`. -/
theorem psd_scalar_forces_sqrt_mesh (h : PsdRange τ s ε) (hs : (s : ℝ) < 512 * precN τ ε / τ) :
    MeshForces (psdScalarFamilyAt h) ε (Real.sqrt (s * τ * hsR τ ε) / 256) :=
  meshForces_of_growth even_two _ AdaptiveHamiltonianLowerBound.Access.toBits
    (ConstantODELowerBound.Oracle.hardAccess_constData_heat _ _
      (AdaptiveODELowerBound.Psd.hardAccess_psdScalarData (precN τ ε) s (τ / 2) h.one_le_precN
        (by have := h.s_ge; omega)) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact (Families.psd_scalar_solver h hU w hO A).2 hs)

/-- **Theorem `odel:thm:psd` over the physical oracle, max form over realised counts**: for
realised worst-case value counts of adaptive solvers of the gadget and scalar families over the
general-mesh physical oracle or its call forms, `psdConst (√(sτr) + r) ≤ max(q_G, q_S)`,
`psdConst = log 2/(3072√2)`. -/
theorem psd_max_cost_mesh (h : PsdRange τ s ε) {qG qS : ℝ}
    (hG : MeshCost (psdSearchFamilyAt h) ε qG) (hS : MeshCost (psdScalarFamilyAt h) ε qS) :
    psdBound s τ ε ≤ max qG qS := by
  unfold psdBound
  exact psd_assembly h ((psd_scalar_forces_mesh h).le_cost hS)
    (fun hs => (psd_scalar_forces_sqrt_mesh h hs).le_cost hS)
    (fun hs => (psd_search_forces_mesh h hs).le_cost hG)

/-- **Theorem `odel:thm:psd` over the general-mesh physical oracle** (eq. `odel:eq:psd`): for
`s ≥ 32`, `τ ≥ 1`, `L ≥ 64τ` (`PsdRange`) and any `ḡ ≥ √2`, one of the two homogeneous
constant-coefficient PSD families (`D_X ⪰ 0`, `‖D_X‖ = 1`, `T = τ`, `1 ≤ g ≤ √2`) is in the class
(`η = 1`, `T = τ`, `g ≤ ḡ`) and forces `psdConst (√(sτr) + r)` value calls (and as many matrix
calls) on every adaptive solver with the heralded output over the physical oracle of the released
general-mesh solver (any placement, spectator index, slot count, degree, public source
interfaces) or over its call forms (controlled and controlled-inverse calls included),
`psdConst = log 2/(3072√2)`. The instance facts are those of the released families: no source,
`B = 1`, `T = τ` and `1 ≤ g ≤ √2` (`ODELowerBoundExtensions.Psd.psdSearchFamilyAt_props`,
`psdScalarFamilyAt_props`), `D_X ⪰ 0`, `‖D_X‖ = 1` and maximum sparsity exactly `s` by the dense
PSD padding (`ODELowerBoundExtensions.Psd.psd_hardInstance`, `psdSearchMat_props`,
`psdScalarMat_props`). -/
theorem psd_mesh (h : PsdRange τ s ε) {gbar : ℝ} (hg : Real.sqrt 2 ≤ gbar) :
    MeshWitnesses (psdSearchFamilyAt h) τ gbar ε (psdBound s τ ε) ∨
      MeshWitnesses (psdScalarFamilyAt h) τ gbar ε (psdBound s τ ε) := by
  rcases forces_or_of_cost₂ (P₁ := MeshCost (psdSearchFamilyAt h) ε)
      (P₂ := MeshCost (psdScalarFamilyAt h) ε) (b := psdBound s τ ε)
      (fun _ _ h₁ h₂ => psd_max_cost_mesh h h₁ h₂) with hf | hf
  · exact Or.inl
      ⟨psdSearchFamilyAt_inClass h hg, psdSearchFamilyAt_T h, meshForces_of_cost hf⟩
  · exact Or.inr
      ⟨psdScalarFamilyAt_inClass h hg, psdScalarFamilyAt_T h, meshForces_of_cost hf⟩

end

end PhysicalODELowerBound.Mesh
