import PhysicalODELowerBound.Const.Transfer
import PhysicalODELowerBound.Families.Psd

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Theorem `odel:thm:psd` over the constant-coefficient physical oracle, with controlled calls

Manuscript lines 4114-4115 ("The lower bounds thus apply to Theorems `ode:thm:main` and
`ode:thm:time`") and 4452-4571 (Theorem `odel:thm:psd`, eq. `odel:eq:psd`), for the two PSD
families (one stage, constant coefficient) and adaptive solvers over the physical oracle of the
released constant-coefficient solver and over its call forms (`ConstForces`; retry protocols and
the released runs by `ConstForces.retry`, `ConstForces.constRun`).

* `psd_search_forces_const`, `psd_scalar_forces_const`, `psd_scalar_forces_sqrt_const`: from
  `Families.psd_search_solver`, `psd_scalar_solver` through `constForces_of_growth`
  (`ConstantODELowerBound.Oracle.hardAccess_constData_heat` with
  `AdaptiveODELowerBound.Psd.hardAccess_psdSearchData`, `hardAccess_psdScalarData`).
* `psd_max_cost_const` (max form over realised counts) and `psd_const` (family form): without call
  forms the max form is the max form of `ConstantODELowerBound`
  (`ConstantODELowerBound.Psd.psd_max_const_tree`), restated with an identical statement and
  rederived from `psd_max_cost_const` by `ConstCost.of_tree` (`psd_max_const_tree_of_const`); here
  the call forms are included and the family form is stated. Both families have maximum sparsity
  exactly `s` by their dense PSD padding (`ODELowerBoundExtensions.Psd.psd_hardInstance`).

As in the manuscript (lines 4573-4578), no constant-error `Ω(√s τ)` bound is asserted for the
purely dissipative subclass.
-/

namespace PhysicalODELowerBound.Const

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open ODELowerBoundExtensions.Psd
open AdaptiveODELowerBound.Model (forces_or_of_cost₂ TreeSolver)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open ODELowerBoundExtensions.Release (SysOp)
open ConstantODELowerBound.Oracle (constOracle PublicConstSources)

-- The released solver's physical workspace is a nested register product.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

variable {τ ε : ℝ} {s : ℕ}

/-- **The gadget family over the constant-coefficient oracle** (lines 4547-4553): for
`s ≥ 512n/τ`, `psdGadgetConst √(sτr)`. -/
theorem psd_search_forces_const (h : PsdRange τ s ε) (hs : 512 * (precN τ ε : ℝ) / τ ≤ s) :
    ConstForces (psdSearchFamilyAt h) ε (psdGadgetConst * Real.sqrt (s * τ * hsR τ ε)) := by
  have hm : Even (2 ^ psdMu s) :=
    (Nat.even_pow' (by have := one_le_psdMu h.s_ge; omega)).mpr even_two
  exact constForces_of_growth hm _ (fun j => j)
    (ConstantODELowerBound.Oracle.hardAccess_constData_heat _ _
      (AdaptiveODELowerBound.Psd.hardAccess_psdSearchData (precN τ ε) (psdMu s) s (τ / 2)
        h.one_le_precN (two_mul_psdM_add_one_le h.s_ge)) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact Families.psd_search_solver h hs hU w hO A)

/-- **The scalar family over the constant-coefficient oracle** (lines 4555-4562): `r/32`. -/
theorem psd_scalar_forces_const (h : PsdRange τ s ε) :
    ConstForces (psdScalarFamilyAt h) ε (hsR τ ε / 32) := by
  exact constForces_of_growth even_two _ AdaptiveHamiltonianLowerBound.Access.toBits
    (ConstantODELowerBound.Oracle.hardAccess_constData_heat _ _
      (AdaptiveODELowerBound.Psd.hardAccess_psdScalarData (precN τ ε) s (τ / 2)
        h.one_le_precN (by have := h.s_ge; omega)) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact (Families.psd_scalar_solver h hU w hO A).1)

/-- **The scalar family for small sparsity over the constant-coefficient oracle** (lines
4565-4568): for `s < 512n/τ`, `√(sτr)/256`. -/
theorem psd_scalar_forces_sqrt_const (h : PsdRange τ s ε)
    (hs : (s : ℝ) < 512 * precN τ ε / τ) :
    ConstForces (psdScalarFamilyAt h) ε (Real.sqrt (s * τ * hsR τ ε) / 256) := by
  exact constForces_of_growth even_two _ AdaptiveHamiltonianLowerBound.Access.toBits
    (ConstantODELowerBound.Oracle.hardAccess_constData_heat _ _
      (AdaptiveODELowerBound.Psd.hardAccess_psdScalarData (precN τ ε) s (τ / 2)
        h.one_le_precN (by have := h.s_ge; omega)) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact (Families.psd_scalar_solver h hU w hO A).2 hs)

/-- **Theorem `odel:thm:psd` over the constant-coefficient oracle, max form over realised
counts**: `psdConst (√(sτr) + r) ≤ max(q_G, q_S)`, `psdConst = log 2/(3072√2)`. -/
theorem psd_max_cost_const (h : PsdRange τ s ε) {qG qS : ℝ}
    (hG : ConstCost (psdSearchFamilyAt h) ε qG) (hS : ConstCost (psdScalarFamilyAt h) ε qS) :
    psdBound s τ ε ≤ max qG qS := by
  unfold psdBound
  exact psd_assembly h ((psd_scalar_forces_const h).le_cost hS)
    (fun hs => (psd_scalar_forces_sqrt_const h hs).le_cost hS)
    (fun hs => (psd_search_forces_const h hs).le_cost hG)

/-- **Theorem `odel:thm:psd` over the constant-coefficient physical oracle** (eq. `odel:eq:psd`):
for `s ≥ 32`, `τ ≥ 1`, `L ≥ 64τ` (`PsdRange`) and any `ḡ ≥ √2`, one of the two homogeneous
constant-coefficient PSD families (`D_X ⪰ 0`, `‖D_X‖ = 1`, `T = τ`, `1 ≤ g ≤ √2`) is in the class
(`η = 1`, `T = τ`, `g ≤ ḡ`) and forces `psdConst (√(sτr) + r)` value calls (and as many matrix
calls) on every adaptive solver with the heralded output over the physical oracle of the released
constant-coefficient solver (any branch register, mesh size, slot count, degree, public source
interfaces) or over its call forms (controlled and controlled-inverse calls included),
`psdConst = log 2/(3072√2)`. The instance facts are those of the released families: no source,
`B = 1`, `T = τ` and `1 ≤ g ≤ √2` (`ODELowerBoundExtensions.Psd.psdSearchFamilyAt_props`,
`psdScalarFamilyAt_props`), `D_X ⪰ 0`, `‖D_X‖ = 1` and maximum sparsity exactly `s` by the dense
PSD padding (`ODELowerBoundExtensions.Psd.psd_hardInstance`, `psdSearchMat_props`,
`psdScalarMat_props`). -/
theorem psd_const (h : PsdRange τ s ε) {gbar : ℝ} (hg : Real.sqrt 2 ≤ gbar) :
    ConstWitnesses (psdSearchFamilyAt h) τ gbar ε (psdBound s τ ε) ∨
      ConstWitnesses (psdScalarFamilyAt h) τ gbar ε (psdBound s τ ε) := by
  rcases forces_or_of_cost₂ (P₁ := ConstCost (psdSearchFamilyAt h) ε)
      (P₂ := ConstCost (psdScalarFamilyAt h) ε) (b := psdBound s τ ε)
      (fun _ _ h₁ h₂ => psd_max_cost_const h h₁ h₂) with hf | hf
  · exact Or.inl
      ⟨psdSearchFamilyAt_inClass h hg, psdSearchFamilyAt_T h, constForces_of_cost hf⟩
  · exact Or.inr
      ⟨psdScalarFamilyAt_inClass h hg, psdScalarFamilyAt_T h, constForces_of_cost hf⟩

/-- **Containment of the max form of `ConstantODELowerBound`**: the statement of
`ConstantODELowerBound.Psd.psd_max_const_tree` (two adaptive solvers over the constant-coefficient
physical oracle itself), restated identically and rederived from `psd_max_cost_const` applied to
the realised counts `ConstCost.of_tree`, with the matrix count at least the value count
(`AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree`). -/
theorem psd_max_const_tree_of_const (h : PsdRange τ s ε) (ιG ιS : Type) [Fintype ιG]
    [DecidableEq ιG] [Fintype ιS] [DecidableEq ιS] (NG TG dG NS TS dS : ℕ)
    {J₀G JbG : _ → SysOp _} (hJG : PublicConstSources J₀G JbG)
    {J₀S JbS : _ → SysOp _} (hJS : PublicConstSources J₀S JbS)
    {FlG FlS EG ES GG GS : Type}
    [NormedAddCommGroup FlG] [InnerProductSpace ℂ FlG] [CompleteSpace FlG]
    [NormedAddCommGroup FlS] [InnerProductSpace ℂ FlS] [CompleteSpace FlS]
    [NormedAddCommGroup EG] [InnerProductSpace ℂ EG] [CompleteSpace EG] [FiniteDimensional ℂ EG]
    [NormedAddCommGroup ES] [InnerProductSpace ℂ ES] [CompleteSpace ES] [FiniteDimensional ℂ ES]
    [NormedAddCommGroup GG] [InnerProductSpace ℂ GG] [CompleteSpace GG]
    [NormedAddCommGroup GS] [InnerProductSpace ℂ GS] [CompleteSpace GS]
    (AG : TreeSolver (psdSearchFamilyAt h) (constOracle (psdSearchFamilyAt h) ιG NG TG dG J₀G JbG)
      FlG EG GG ε)
    (AS : TreeSolver (psdScalarFamilyAt h) (constOracle (psdScalarFamilyAt h) ιS NS TS dS J₀S JbS)
      FlS ES GS ε) :
    psdBound s τ ε ≤
        max (AG.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
          (AS.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ) ∧
      psdBound s τ ε ≤
        max (AG.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
          (AS.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) := by
  have hv := psd_max_cost_const h (ConstCost.of_tree ιG NG TG dG hJG AG)
    (ConstCost.of_tree ιS NS TS dS hJS AS)
  exact ⟨hv, hv.trans (max_le_max
    (by exact_mod_cast AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree AG.tree)
    (by exact_mod_cast AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree AS.tree))⟩

end

end PhysicalODELowerBound.Const
