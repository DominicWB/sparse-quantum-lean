import ConstantODELowerBound.Access
import AdaptiveODELowerBound.Psd.Theorem
import AdaptiveODELowerBound.Release.Bridge

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Theorem `odel:thm:psd` for the released constant-coefficient solver's oracle

Manuscript lines 4114-4115 ("The lower bounds thus apply to Theorems `ode:thm:main` and
`ode:thm:time`") and 4452-4571 (Theorem `odel:thm:psd`: the homogeneous equation `ẋ = -D_X x`
with `D_X ⪰ 0`, `‖D_X‖ = η_D = 1`, `T = τ`, `1 ≤ g ≤ √2`, public supports and dyadic entries,
`Q = Ω(√(sτr) + r)`, with the heralded output), for adaptive solvers
(`AdaptiveODELowerBound.Model.TreeSolver`) over the physical oracle family `Oracle.constOracle`
of the released constant-coefficient solver `SparseHamiltonian.ODECompleteEndpoint.solver` run on
the two PSD families (`ODELowerBoundExtensions.Psd.psdSearchFamilyAt`, `psdScalarFamilyAt`), with
public source interfaces. Both counts of `Herald` are bounded.

* `psd_search_const_tree`: for `s ≥ 512n/τ`, the gadget family forces
  `(log 2/(1536√2)) √(sτr)` (eq. `odel:eq:psdmixedlocal` and lines 4547-4550), from
  `AdaptiveODELowerBound.Psd.psd_search_tree_general` with `Access.searchGrowth_const_heat`.
* `psd_scalar_const_tree`: the scalar family forces `r/32`, and `√(sτr)/256` when
  `s < 512n/τ` (lines 4555-4568), from `AdaptiveODELowerBound.Psd.psd_scalar_tree_general`.
* `psd_max_const_tree`: max form, `psdConst (√(sτr) + r) ≤ max(Q_G, Q_S)` for both counts,
  `psdConst = log 2/(3072√2)` (`ODELowerBoundExtensions.Psd.psd_assembly`), on `PsdRange`.
* `psd_max_const_retry`: the same for retry protocols, through `Model.retryToTree`.

**Scope.** The adaptive solvers here call the physical oracle family `Oracle.constOracle` itself
(with inverse calls); the call forms `AdaptiveODELowerBound.Access.callFamily` of the physical
oracle (controlled calls) are not included, and the released solver does not use them.
Controlled calls, padding and family forms over this oracle are in the library
`PhysicalODELowerBound`.

As in the manuscript (lines 4573-4578), no constant-error `Ω(√s τ)` bound is asserted for the
purely dissipative subclass.
-/

namespace ConstantODELowerBound.Psd

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open SparseLowerBounds.Hamiltonian (hsR precN)
open ODELowerBoundExtensions.Release (SysOp RetrySolver)
open ODELowerBoundExtensions.Psd (PsdRange psdSearchFamilyAt psdScalarFamilyAt psdGadgetConst
  psdBound)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open AdaptiveODELowerBound.Model
open ConstantODELowerBound.Oracle

-- The released solver's physical workspace is a nested register product; instance search and
-- elaboration over its types need the raised `synthInstance.maxSize` and `maxRecDepth`.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

variable {τ ε : ℝ} {s : ℕ}

/-- **The gadget family, adaptive protocols over the released constant-coefficient oracle**
(lines 4542-4553): for `s ≥ 512n/τ`, at least `(log 2/(1536√2)) √(sτr)` value calls, hence as
many matrix calls, in the worst case. -/
theorem psd_search_const_tree (h : PsdRange τ s ε) (hs : 512 * (precN τ ε : ℝ) / τ ≤ s)
    (ι : Type) [Fintype ι] [DecidableEq ι] (Nm Tsl d : ℕ) {J₀ Jb : _ → SysOp _}
    (hJ : PublicConstSources J₀ Jb) {Fl E G : Type}
    [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : TreeSolver (psdSearchFamilyAt h) (constOracle (psdSearchFamilyAt h) ι Nm Tsl d J₀ Jb)
      Fl E G ε) :
    psdGadgetConst * Real.sqrt (s * τ * hsR τ ε) ≤
        A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      psdGadgetConst * Real.sqrt (s * τ * hsR τ ε) ≤
        A.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := by
  have hD := AdaptiveODELowerBound.Psd.hardAccess_psdSearchData (precN τ ε)
    (ODELowerBoundExtensions.Psd.psdMu s) s (τ / 2) h.one_le_precN
    (ODELowerBoundExtensions.Psd.two_mul_psdM_add_one_le h.s_ge)
  have heven : Even (2 ^ ODELowerBoundExtensions.Psd.psdMu s) :=
    (Nat.even_pow' (by have := ODELowerBoundExtensions.Psd.one_le_psdMu h.s_ge; omega)).mpr
      even_two
  have hO := Access.searchGrowth_const_heat heven (ODELowerBoundExtensions.Psd.psdSearchDataAt h)
    (fun j => j) hD τ (by linarith [h.one_le_tau])
    (SparseLowerBounds.Hamiltonian.searchInput (precN τ ε) (ODELowerBoundExtensions.Psd.psdMu s) s)
    ι Nm Tsl d hJ
  have hb := AdaptiveODELowerBound.Psd.psd_search_tree_general h
    (ODELowerBoundExtensions.Psd.psd_m_cond h hs)
    (fun l j => constOracle_unitary _ ι Nm Tsl d hJ l j) _ hO A.tree A.readout
    A.readout_isometry A.success (fun j => TreeSolver.accurate_heat _ _ _ _ A j)
  have hb' : Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ ODELowerBoundExtensions.Psd.psdMu s *
      precN τ ε * (τ / 2)) ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := hb
  have hX : 0 ≤ Real.log 2 / 192 * Real.sqrt ((2 : ℝ) ^ ODELowerBoundExtensions.Psd.psdMu s *
      precN τ ε * (τ / 2)) :=
    mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num)) (Real.sqrt_nonneg _)
  have hv : psdGadgetConst * Real.sqrt (s * τ * hsR τ ε) ≤
      A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := by
    linarith [ODELowerBoundExtensions.Psd.psd_gadget_arith h]
  exact ⟨hv, hv.trans (AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree A.tree)⟩

/-- **The scalar family, adaptive protocols over the released constant-coefficient oracle**
(lines 4555-4568): at least `r/32` value calls in the worst case, and at least `√(sτr)/256`
when `s < 512n/τ`; hence as many matrix calls. -/
theorem psd_scalar_const_tree (h : PsdRange τ s ε) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Nm Tsl d : ℕ) {J₀ Jb : _ → SysOp _} (hJ : PublicConstSources J₀ Jb) {Fl E G : Type}
    [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : TreeSolver (psdScalarFamilyAt h) (constOracle (psdScalarFamilyAt h) ι Nm Tsl d J₀ Jb)
      Fl E G ε) :
    (hsR τ ε / 32 ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      hsR τ ε / 32 ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) ∧
      ((s : ℝ) < 512 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / 256 ≤
            A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
          Real.sqrt (s * τ * hsR τ ε) / 256 ≤
            A.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) := by
  have hD := AdaptiveODELowerBound.Psd.hardAccess_psdScalarData (precN τ ε) s (τ / 2)
    h.one_le_precN (by have := h.s_ge; omega)
  have hO := Access.searchGrowth_const_heat even_two (ODELowerBoundExtensions.Psd.psdScalarDataAt h)
    AdaptiveHamiltonianLowerBound.Access.toBits hD τ (by linarith [h.one_le_tau])
    (SparseLowerBounds.Hamiltonian.scalarInput (precN τ ε) s) ι Nm Tsl d hJ
  have hb := AdaptiveODELowerBound.Psd.psd_scalar_tree_general h
    (fun l x => constOracle_unitary _ ι Nm Tsl d hJ l x) _ hO A.tree A.readout
    A.readout_isometry A.success (fun x => TreeSolver.accurate_heat _ _ _ _ A x)
  have hb' : (precN τ ε : ℝ) / 2 ≤
      A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := hb
  have hn0 : (0 : ℝ) ≤ precN τ ε := Nat.cast_nonneg _
  have hm := AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree A.tree
  have hr := SparseLowerBounds.Hamiltonian.rbound h.toHSRange h.hL
  refine ⟨⟨by linarith, by linarith⟩, fun hs => ?_⟩
  have hq := ODELowerBoundExtensions.Psd.psd_scalar_sqrt h hs
  exact ⟨by linarith, by linarith⟩

/-- **Theorem `odel:thm:psd` for the released constant-coefficient oracle, max form**: for one
adaptive solver of the gadget family and one of the scalar family over the released solver's
oracle (any branch registers, mesh sizes, slot counts, degrees and public source interfaces),
the larger worst-case value count, and hence the larger worst-case matrix count, is at least
`psdConst (√(sτr) + r)`, `psdConst = log 2/(3072√2)`. -/
theorem psd_max_const_tree (h : PsdRange τ s ε) (ιG ιS : Type) [Fintype ιG] [DecidableEq ιG]
    [Fintype ιS] [DecidableEq ιS] (NG TG dG NS TS dS : ℕ)
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
  have hv : psdBound s τ ε ≤
      max (AG.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
        (AS.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ) :=
    ODELowerBoundExtensions.Psd.psd_assembly h (psd_scalar_const_tree h ιS NS TS dS hJS AS).1.1
      (fun hs => ((psd_scalar_const_tree h ιS NS TS dS hJS AS).2 hs).1)
      (fun hs => (psd_search_const_tree h hs ιG NG TG dG hJG AG).1)
  exact ⟨hv, hv.trans (max_le_max
    (by exact_mod_cast AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree AG.tree)
    (by exact_mod_cast AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree AS.tree))⟩

/-- **Theorem `odel:thm:psd` for retry protocols over the released constant-coefficient oracle,
max form**: the retry-protocol form of `psd_max_const_tree` (`Model.retryToTree`). -/
theorem psd_max_const_retry (h : PsdRange τ s ε) (ιG ιS : Type) [Fintype ιG] [DecidableEq ιG]
    [Fintype ιS] [DecidableEq ιS] (NG TG dG NS TS dS : ℕ)
    {J₀G JbG : _ → SysOp _} (hJG : PublicConstSources J₀G JbG)
    {J₀S JbS : _ → SysOp _} (hJS : PublicConstSources J₀S JbS)
    {EG ES GG GS : Type}
    [NormedAddCommGroup EG] [InnerProductSpace ℂ EG] [CompleteSpace EG] [FiniteDimensional ℂ EG]
    [NormedAddCommGroup ES] [InnerProductSpace ℂ ES] [CompleteSpace ES] [FiniteDimensional ℂ ES]
    [NormedAddCommGroup GG] [InnerProductSpace ℂ GG] [CompleteSpace GG]
    [NormedAddCommGroup GS] [InnerProductSpace ℂ GS] [CompleteSpace GS]
    (AG : RetrySolver (psdSearchFamilyAt h)
      (constOracle (psdSearchFamilyAt h) ιG NG TG dG J₀G JbG) EG GG ε)
    (AS : RetrySolver (psdScalarFamilyAt h)
      (constOracle (psdScalarFamilyAt h) ιS NS TS dS J₀S JbS) ES GS ε) :
    psdBound s τ ε ≤
        max (AG.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
          (AS.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ) ∧
      psdBound s τ ε ≤
        max (AG.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
          (AS.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) :=
  psd_max_const_tree h ιG ιS NG TG dG NS TS dS hJG hJS (retryToTree AG ℂ) (retryToTree AS ℂ)

end

end ConstantODELowerBound.Psd
