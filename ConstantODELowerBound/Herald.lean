import ConstantODELowerBound.Access
import AdaptiveODELowerBound.Herald.Transfer
import AdaptiveODELowerBound.Release.Bridge

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Eq. `odel:eq:hsbound` for the released constant-coefficient solver's oracle

Manuscript lines 4114-4115 ("The lower bounds thus apply to Theorems `ode:thm:main` and
`ode:thm:time`"), 4049-4050 ("Theorem `hsl:thm:main` applies to the anti-Hermitian subclass"),
4392-4400 (eq. `odel:eq:hsbound`: the families of Theorem `hsl:thm:main` read as
constant-coefficient ODEs `A = -iH_X`, `b = 0`, `g = 1`) and 4403-4435 (Lemma `odel:lem:herald`),
for adaptive solvers (`AdaptiveODELowerBound.Model.TreeSolver`) over the physical oracle family
`Oracle.constOracle` of the released constant-coefficient solver
`SparseHamiltonian.ODECompleteEndpoint.solver` (Theorem `ode:thm:main`) run on the hard family's
data (any branch register, mesh size, slot count and degree), with public source interfaces.
Two counts are bounded, as in `AdaptiveODELowerBound.Release.combined_max_release_tree`: the
worst-case number of value calls `Tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight)`
and the released matrix count `Tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))`
(row, column and value calls, inverses included, source calls not counted).

* `time_const_tree`, `mixed_const_tree`, `precision_const_tree`: the bounds of eqs.
  `hsl:eq:timelower`, `hsl:eq:mixrbound`, `hsl:eq:rbound`, `hsl:eq:failedmix` with the constants
  of the Hamiltonian lower bound, from `AdaptiveHamiltonianLowerBound.time_tree_general`,
  `mixed_tree_general`, `precision_tree_general` with `Access.searchGrowth_const_ham`.
* `herald_max_const_tree`: max form, `c₀ (√s τ + √(sτr) + r) ≤ max(Q_T, Q_M, Q_P)` for both
  counts, `c₀ = log 2/(4096π)` (`SparseLowerBounds.Hamiltonian.assembly`), on `HSRange`.
* `herald_max_const_retry`: the same for retry protocols (`Release.RetrySolver`), through
  `AdaptiveODELowerBound.Model.retryToTree`; the released four-attempt protocol is one.

**Scope.** The adaptive solvers here call the physical oracle family `Oracle.constOracle` itself
(with inverse calls); the call forms `AdaptiveODELowerBound.Access.callFamily` of the physical
oracle (controlled calls) are not included, and the released solver does not use them.
Controlled calls, padding and family forms over this oracle are in the library
`PhysicalODELowerBound`.

The joint term `ḡ √s τ` of Theorem `odel:thm:combined` is not part of this bound: its family is
time dependent, and the manuscript does not prove it for constant-coefficient equations (lines
4151-4155).
-/

namespace ConstantODELowerBound.Herald

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE NativeSparseBlockEncoding
open OracleCircuit
open SparseLowerBounds.Hamiltonian (HSRange hsL hsR precN c0 cT)
open ODELowerBoundExtensions.Release (SysOp RetrySolver)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open AdaptiveODELowerBound.Model
open ConstantODELowerBound.Oracle

-- The released solver's physical workspace is a nested register product; instance search and
-- elaboration over its types need the raised `synthInstance.maxSize` and `maxRecDepth`.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

variable {τ ε : ℝ} {s : ℕ}

/-- **Time family, adaptive protocols over the released constant-coefficient oracle** (eq.
`hsl:eq:timelower`): at least `c_T √s τ` value calls, hence as many matrix calls, in the worst
case, `c_T = log 2/(192π)`. -/
theorem time_const_tree (h : HSRange τ s ε) (ι : Type) [Fintype ι] [DecidableEq ι]
    (Nm Tsl d : ℕ) {J₀ Jb : _ → SysOp _} (hJ : PublicConstSources J₀ Jb) {Fl E G : Type}
    [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : TreeSolver (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]))
      (constOracle (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) ι Nm Tsl d J₀ Jb)
      Fl E G ε) :
    cT * Real.sqrt s * τ ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      cT * Real.sqrt s * τ ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := by
  have hτ0 : (0 : ℝ) ≤ τ := by linarith [h.one_le_tau]
  have hI := (Hamiltonian.hard_instances h).1
  have hO := Access.searchGrowth_const_ham
    (AdaptiveHamiltonianLowerBound.even_two_pow_hsMu h.s_ge) (Hamiltonian.timeData τ s h.s_ge) id
    (AdaptiveHamiltonianLowerBound.Access.hardAccess_timeData τ s h.s_ge) τ hτ0
    (Hamiltonian.searchInput (Hamiltonian.timeN τ) (Hamiltonian.hsMu s) s) ι Nm Tsl d hJ
  have hb := AdaptiveHamiltonianLowerBound.time_tree_general (F := Fl) h
    (fun l j => constOracle_unitary _ ι Nm Tsl d hJ l j) _ hO
    A.tree A.readout A.readout_isometry A.success
    (fun j => A.accurate_ham _ _ _ _ hI.isHermitian (Hamiltonian.norm_searchInput _ _ _) j)
  have hX : 0 ≤ Real.log 2 / 96 * (Hamiltonian.timeN τ : ℝ) *
      Real.sqrt ((2 : ℝ) ^ Hamiltonian.hsMu s) :=
    mul_nonneg (mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num))
      (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
  have hv : cT * Real.sqrt s * τ ≤
      A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := by
    have ht := Hamiltonian.time_final h.one_le_tau h.s_ge
    have e : Real.log 2 / 48 * (Hamiltonian.timeN τ : ℝ) *
        Real.sqrt ((2 : ℝ) ^ Hamiltonian.hsMu s) =
        2 * (Real.log 2 / 96 * (Hamiltonian.timeN τ : ℝ) *
          Real.sqrt ((2 : ℝ) ^ Hamiltonian.hsMu s)) := by
      ring
    have hb' : 2 * (Real.log 2 / 96 * (Hamiltonian.timeN τ : ℝ) *
        Real.sqrt ((2 : ℝ) ^ Hamiltonian.hsMu s)) ≤
        A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := by
      rw [← e]; exact hb
    linarith
  exact ⟨hv, hv.trans (AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree A.tree)⟩

/-- **Mixed family, adaptive protocols over the released constant-coefficient oracle** (eq.
`hsl:eq:mixrbound`): for `L ≥ 64τ` and `s ≥ 64n/τ`, at least `(log 2/(384√2)) √(sτr)` value
calls, hence as many matrix calls, in the worst case. -/
theorem mixed_const_tree (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) (ι : Type) [Fintype ι] [DecidableEq ι] (Nm Tsl d : ℕ)
    {J₀ Jb : _ → SysOp _} (hJ : PublicConstSources J₀ Jb) {Fl E G : Type}
    [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : TreeSolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      (constOracle (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ι Nm Tsl d J₀ Jb)
      Fl E G ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤
        A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤
        A.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := by
  have hτ0 : (0 : ℝ) ≤ τ := by linarith [h.one_le_tau]
  have hI := (Hamiltonian.hard_instances h).2.1
  have hO := Access.searchGrowth_const_ham
    (AdaptiveHamiltonianLowerBound.even_two_pow_hsMu h.s_ge)
    (Hamiltonian.mixedMainData τ ε s h.s_ge)
    id (AdaptiveHamiltonianLowerBound.Access.hardAccess_mixedMainData τ ε s h.s_ge) τ hτ0
    (Hamiltonian.searchInput (precN τ ε) (Hamiltonian.hsMu s) s) ι Nm Tsl d hJ
  have hb := AdaptiveHamiltonianLowerBound.mixed_tree_general (F := Fl) h hL hs
    (fun l j => constOracle_unitary _ ι Nm Tsl d hJ l j) _ hO
    A.tree A.readout A.readout_isometry A.success
    (fun j => A.accurate_ham _ _ _ _ hI.isHermitian (Hamiltonian.norm_searchInput _ _ _) j)
  have hb' : Real.log 2 / 48 * Real.sqrt ((2 : ℝ) ^ Hamiltonian.hsMu s * precN τ ε * τ) ≤
      A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := hb
  have hX : 0 ≤ Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ Hamiltonian.hsMu s * precN τ ε * τ) :=
    mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num)) (Real.sqrt_nonneg _)
  have hv : Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤
      A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := by
    linarith [Hamiltonian.mixrbound h hL]
  exact ⟨hv, hv.trans (AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree A.tree)⟩

/-- **Precision family, adaptive protocols over the released constant-coefficient oracle** (eqs.
`hsl:eq:rbound`, `hsl:eq:failedmix`): for `L ≥ 64τ`, at least `r/32` value calls in the worst
case, and at least `√(sτr)/(64√2)` when `s < 64n/τ`; hence as many matrix calls. -/
theorem precision_const_tree (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) (ι : Type) [Fintype ι]
    [DecidableEq ι] (Nm Tsl d : ℕ) {J₀ Jb : _ → SysOp _} (hJ : PublicConstSources J₀ Jb)
    {Fl E G : Type}
    [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (A : TreeSolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      (constOracle (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ι Nm Tsl d J₀
        Jb) Fl E G ε) :
    (hsR τ ε / 32 ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
      hsR τ ε / 32 ≤ A.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤
            A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) ∧
          Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤
            A.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) := by
  have hτ0 : (0 : ℝ) ≤ τ := by linarith [h.one_le_tau]
  have hI := (Hamiltonian.hard_instances h).2.2.1
  have hO := Access.searchGrowth_const_ham even_two (Hamiltonian.precisionMainData τ ε s h.s_ge)
    AdaptiveHamiltonianLowerBound.Access.toBits
    (AdaptiveHamiltonianLowerBound.Access.hardAccess_precisionMainData τ ε s h.s_ge) τ hτ0
    (Hamiltonian.scalarInput (precN τ ε) s) ι Nm Tsl d hJ
  have hb := AdaptiveHamiltonianLowerBound.precision_tree_general (F := Fl) h hL
    (fun l j => constOracle_unitary _ ι Nm Tsl d hJ l j) _ hO
    A.tree A.readout A.readout_isometry A.success
    (fun x => A.accurate_ham _ _ _ _ hI.isHermitian (Hamiltonian.norm_scalarInput _ _) x)
  have hb' : (precN τ ε : ℝ) / 2 ≤
      A.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) := hb
  have hn0 : (0 : ℝ) ≤ precN τ ε := Nat.cast_nonneg _
  have hm := AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree A.tree
  refine ⟨⟨by linarith [Hamiltonian.rbound h hL], by linarith [Hamiltonian.rbound h hL]⟩,
    fun hs' => ⟨by linarith [Hamiltonian.failedmix h hL hs'],
      by linarith [Hamiltonian.failedmix h hL hs']⟩⟩

/-- **Eq. `odel:eq:hsbound` for the released constant-coefficient oracle, max form** (Lemma
`odel:lem:herald`): for any three adaptive solvers over the released solver's oracle on the
time, mixed and precision families (any branch registers, mesh sizes, slot counts, degrees,
public source interfaces, flag, output and garbage spaces), each accurate on its own family, the
largest worst-case value count, and hence the largest worst-case matrix count, is at least
`c₀ (√s τ + √(sτr) + r)`, `c₀ = log 2/(4096π)`. -/
theorem herald_max_const_tree (h : HSRange τ s ε) (ιT ιM ιP : Type) [Fintype ιT]
    [DecidableEq ιT] [Fintype ιM] [DecidableEq ιM] [Fintype ιP] [DecidableEq ιP]
    (NT TT dT NM TM dM NP TP dP : ℕ)
    {J₀T JbT : _ → SysOp _} (hJT : PublicConstSources J₀T JbT)
    {J₀M JbM : _ → SysOp _} (hJM : PublicConstSources J₀M JbM)
    {J₀P JbP : _ → SysOp _} (hJP : PublicConstSources J₀P JbP)
    {FlT FlM FlP ET EM EP GT GM GP : Type}
    [NormedAddCommGroup FlT] [InnerProductSpace ℂ FlT] [CompleteSpace FlT]
    [NormedAddCommGroup FlM] [InnerProductSpace ℂ FlM] [CompleteSpace FlM]
    [NormedAddCommGroup FlP] [InnerProductSpace ℂ FlP] [CompleteSpace FlP]
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : TreeSolver (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]))
      (constOracle (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) ιT NT TT dT J₀T JbT)
      FlT ET GT ε)
    (AM : TreeSolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      (constOracle (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ιM NM TM dM J₀M
        JbM) FlM EM GM ε)
    (AP : TreeSolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      (constOracle (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ιP NP TP dP J₀P
        JbP) FlP EP GP ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (AT.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
          (max (AM.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
            (AP.tree.worstCost (ODESourceQueryBudget.matrixWeight valueWeight))) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (AT.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
          (max (AM.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
            (AP.tree.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)))) := by
  have hv := Hamiltonian.assembly h (time_const_tree h ιT NT TT dT hJT AT).1
    (fun hL => ⟨(precision_const_tree h hL ιP NP TP dP hJP AP).1.1,
      fun hs' => ((precision_const_tree h hL ιP NP TP dP hJP AP).2 hs').1⟩)
    (fun hL hs => (mixed_const_tree h hL hs ιM NM TM dM hJM AM).1)
  exact ⟨hv, hv.trans (max_le_max
    (by exact_mod_cast AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree AT.tree)
    (max_le_max
      (by exact_mod_cast AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree AM.tree)
      (by exact_mod_cast AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree AP.tree)))⟩

/-- **Eq. `odel:eq:hsbound` for retry protocols over the released constant-coefficient oracle,
max form**: the retry-protocol form of `herald_max_const_tree` (a retry protocol is the adaptive
protocol `Tree.final`, `Model.retryToTree`, with the same worst-case counts). -/
theorem herald_max_const_retry (h : HSRange τ s ε) (ιT ιM ιP : Type) [Fintype ιT]
    [DecidableEq ιT] [Fintype ιM] [DecidableEq ιM] [Fintype ιP] [DecidableEq ιP]
    (NT TT dT NM TM dM NP TP dP : ℕ)
    {J₀T JbT : _ → SysOp _} (hJT : PublicConstSources J₀T JbT)
    {J₀M JbM : _ → SysOp _} (hJM : PublicConstSources J₀M JbM)
    {J₀P JbP : _ → SysOp _} (hJP : PublicConstSources J₀P JbP)
    {ET EM EP GT GM GP : Type}
    [NormedAddCommGroup ET] [InnerProductSpace ℂ ET] [CompleteSpace ET] [FiniteDimensional ℂ ET]
    [NormedAddCommGroup EM] [InnerProductSpace ℂ EM] [CompleteSpace EM] [FiniteDimensional ℂ EM]
    [NormedAddCommGroup EP] [InnerProductSpace ℂ EP] [CompleteSpace EP] [FiniteDimensional ℂ EP]
    [NormedAddCommGroup GT] [InnerProductSpace ℂ GT] [CompleteSpace GT]
    [NormedAddCommGroup GM] [InnerProductSpace ℂ GM] [CompleteSpace GM]
    [NormedAddCommGroup GP] [InnerProductSpace ℂ GP] [CompleteSpace GP]
    (AT : RetrySolver (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]))
      (constOracle (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) ιT NT TT dT J₀T JbT)
      ET GT ε)
    (AM : RetrySolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      (constOracle (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ιM NM TM dM J₀M
        JbM) EM GM ε)
    (AP : RetrySolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]))
      (constOracle (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ιP NP TP dP J₀P
        JbP) EP GP ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (AT.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
          (max (AM.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight) : ℝ)
            (AP.prot.worstCost (ODESourceQueryBudget.matrixWeight valueWeight))) ∧
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
        max (AT.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
          (max (AM.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ)
            (AP.prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)))) :=
  herald_max_const_tree h ιT ιM ιP NT TT dT NM TM dM NP TP dP hJT hJM hJP
    (retryToTree AT ℂ) (retryToTree AM ℂ) (retryToTree AP ℂ)

end

end ConstantODELowerBound.Herald
