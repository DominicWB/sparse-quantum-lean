import AdaptiveODELowerBound.Psd.Theorem

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The positive semidefinite families against adaptive solvers over any oracle with growth

Manuscript: Theorem `odel:thm:psd` (eq. `odel:eq:psd`): the homogeneous
constant-coefficient families `ẋ = -D_X x`, `D_X ⪰ 0`, `‖D_X‖ = 1`, `T = τ`, `1 ≤ g ≤ √2`
(`ODELowerBoundExtensions.Psd.psdSearchFamilyAt`, `psdScalarFamilyAt`), for one adaptive solver
(`AdaptiveODELowerBound.Model.TreeSolver`) over **any** unitary oracle family with search-weight
growth along the one-hot inputs (along `Access.toBits` for the scalar family). The access shape
is not fixed here; the physical oracles of the released solvers and their call forms qualify.

* `psd_search_solver` (proof of Theorem `odel:thm:psd`): for `s ≥ 512n/τ`, at least
  `psdGadgetConst √(sτr)` (`psdGadgetConst = log 2/(1536√2)`), from
  `AdaptiveODELowerBound.Psd.psd_search_tree_general` with `psd_m_cond` and `psd_gadget_arith`.
* `psd_scalar_solver` (proof of Theorem `odel:thm:psd`): at least `r/32`, and at least `√(sτr)/256`
  when `s < 512n/τ`, from `AdaptiveODELowerBound.Psd.psd_scalar_tree_general` with `rbound` and
  `psd_scalar_sqrt`.

The accuracy of a solver for the normalised endpoint `e^{-τD_X} x₀/‖·‖` is
`AdaptiveODELowerBound.Model.TreeSolver.accurate_heat`.
-/

namespace PhysicalODELowerBound.Families

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open ODELowerBoundExtensions.Psd
open AdaptiveHamiltonianLowerBound (SearchGrowth)
open AdaptiveHamiltonianLowerBound.Access (toBits)
open AdaptiveODELowerBound.Model (TreeSolver)

-- The nested spectator spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

variable {τ ε : ℝ} {s : ℕ}
variable {L W Fl E G : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- **The gadget family** (proof of Theorem `odel:thm:psd`): for `s ≥ 512n/τ`, an adaptive solver of
the gadget family over a unitary oracle family with search-weight growth `w` costs at least
`psdGadgetConst √(sτr)`, `psdGadgetConst = log 2/(1536√2)`. -/
theorem psd_search_solver (h : PsdRange τ s ε) (hs : 512 * (precN τ ε : ℝ) / τ ≤ s)
    {O : L → (Fin (precN τ ε) → Fin (2 ^ psdMu s)) → W →L[ℂ] W} (hU : ∀ l x, IsUnitary (O l x))
    (w : L → ℕ) (hO : SearchGrowth (2 ^ psdMu s) O w)
    (A : TreeSolver (psdSearchFamilyAt h) O Fl E G ε) :
    psdGadgetConst * Real.sqrt (s * τ * hsR τ ε) ≤ A.tree.worstCost w := by
  have hb := AdaptiveODELowerBound.Psd.psd_search_tree_general h (psd_m_cond h hs) hU w hO
    A.tree A.readout A.readout_isometry A.success
    (TreeSolver.accurate_heat _ _ _ _ A)
  have hX : 0 ≤ Real.sqrt ((2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2)) := Real.sqrt_nonneg _
  have hl : 0 ≤ Real.log 2 := (Real.log_pos one_lt_two).le
  have hlX := mul_nonneg hl hX
  have ha := psd_gadget_arith h
  linarith

/-- **The scalar family** (proof of Theorem `odel:thm:psd`): an adaptive solver of the scalar family
over a unitary oracle family with search-weight growth `w` along `toBits` costs at least `r/32`, and
at least `√(sτr)/256` when `s < 512n/τ`. -/
theorem psd_scalar_solver (h : PsdRange τ s ε)
    {O : L → (Fin (precN τ ε) → Bool) → W →L[ℂ] W} (hU : ∀ l x, IsUnitary (O l x))
    (w : L → ℕ) (hO : SearchGrowth 2 (fun l j => O l (toBits j)) w)
    (A : TreeSolver (psdScalarFamilyAt h) O Fl E G ε) :
    hsR τ ε / 32 ≤ A.tree.worstCost w ∧
      ((s : ℝ) < 512 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / 256 ≤ A.tree.worstCost w) := by
  have hb := AdaptiveODELowerBound.Psd.psd_scalar_tree_general h hU w hO A.tree A.readout
    A.readout_isometry A.success (TreeSolver.accurate_heat _ _ _ _ A)
  have hn : (0 : ℝ) ≤ precN τ ε := Nat.cast_nonneg _
  refine ⟨by linarith [rbound h.toHSRange h.hL], fun hs => ?_⟩
  linarith [psd_scalar_sqrt h hs]

end

end PhysicalODELowerBound.Families
