import AdaptiveODELowerBound.Padding.Herald

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `g = 1` families against adaptive solvers over any oracle with search-weight growth

Manuscript: eq. `odel:eq:hsbound` (the families of Theorem `hsl:thm:main` read as
constant-coefficient ODEs `A = -iH_X`, `b = 0`, `g = 1`), Lemma `odel:lem:herald` and the proof
of Theorem `odel:thm:combined` ("Pad dimensions to a common known size if desired").

The bounds of Lemma `odel:lem:herald` for one adaptive solver
(`AdaptiveODELowerBound.Model.TreeSolver`)
of the time, mixed or precision family, or of their known zero paddings
(`ODELowerBoundExtensions.Padding.timePadFamilyAt`, `mixedPadFamilyAt`, `precisionPadFamilyAt`),
over **any** unitary oracle family `O` whose labels have search-weight growth `w` along the
one-hot inputs (`AdaptiveHamiltonianLowerBound.SearchGrowth`; along `Access.toBits` for the
precision families). The access shape is not fixed here: the sampled-time access, the physical
oracles of the released solvers and their call forms all qualify (`PhysicalODELowerBound.Mesh`,
`PhysicalODELowerBound.Const`).

* `time_solver`, `mixed_solver`, `precision_solver`: eqs. `hsl:eq:timelower`, `hsl:eq:mixrbound`,
  `hsl:eq:rbound`, `hsl:eq:failedmix` with the constants of the Hamiltonian lower bound, from
  `AdaptiveHamiltonianLowerBound.time_tree_general`, `mixed_tree_general`,
  `precision_tree_general`, the accuracy transfer `Model.TreeSolver.accurate_ham` and the numerics
  `time_final`, `mixrbound`, `rbound`, `failedmix`.
* `time_pad_solver`, `mixed_pad_solver`, `precision_pad_solver`: the same for the padded
  families, through the padded readout `padReadout P G refZero ∘ readout`
  (`AdaptiveODELowerBound.Padding.densityAccurate_padReadout`, `evolve_padMat`).
-/

namespace PhysicalODELowerBound.Families

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open LowerBoundRemarks.HamiltonianPadding
open ODELowerBoundExtensions.Padding (timePadFamilyAt mixedPadFamilyAt precisionPadFamilyAt)
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

/-- **Time family** (eq. `hsl:eq:timelower`): an adaptive solver of the time family over a
unitary oracle family with search-weight growth `w` costs at least `c_T √s τ`,
`c_T = log 2/(192π)`. -/
theorem time_solver (h : HSRange τ s ε)
    {O : L → (Fin (timeN τ) → Fin (2 ^ hsMu s)) → W →L[ℂ] W} (hU : ∀ l x, IsUnitary (O l x))
    (w : L → ℕ) (hO : SearchGrowth (2 ^ hsMu s) O w)
    (A : TreeSolver (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) O Fl E G ε) :
    cT * Real.sqrt s * τ ≤ A.tree.worstCost w := by
  have hacc := A.accurate_ham (timeData τ s h.s_ge) τ _ _ (hard_instances h).1.isHermitian
    (norm_searchInput _ _ _)
  have hb := AdaptiveHamiltonianLowerBound.time_tree_general h hU w hO A.tree A.readout
    A.readout_isometry A.success hacc
  have hX : 0 ≤ Real.log 2 / 96 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) :=
    mul_nonneg (mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num))
      (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
  linarith [time_final h.one_le_tau h.s_ge]

/-- **Mixed family** (eq. `hsl:eq:mixrbound`): for `L ≥ 64τ` and `s ≥ 64n/τ`, an adaptive solver
of the mixed family over a unitary oracle family with search-weight growth `w` costs at least
`(log 2/(384√2)) √(sτr)`. -/
theorem mixed_solver (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s)
    {O : L → (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → W →L[ℂ] W} (hU : ∀ l x, IsUnitary (O l x))
    (w : L → ℕ) (hO : SearchGrowth (2 ^ hsMu s) O w)
    (A : TreeSolver (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) O Fl E G ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ A.tree.worstCost w := by
  have hacc := A.accurate_ham (mixedMainData τ ε s h.s_ge) τ _ _
    (hard_instances h).2.1.isHermitian (norm_searchInput _ _ _)
  have hb := AdaptiveHamiltonianLowerBound.mixed_tree_general h hL hs hU w hO A.tree A.readout
    A.readout_isometry A.success hacc
  have hX : 0 ≤ Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ hsMu s * precN τ ε * τ) :=
    mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num)) (Real.sqrt_nonneg _)
  linarith [mixrbound h hL]

/-- **Precision family** (eqs. `hsl:eq:rbound`, `hsl:eq:failedmix`): for `L ≥ 64τ`, an adaptive
solver of the precision family over a unitary oracle family with search-weight growth `w` along
`toBits` costs at least `r/32`, and at least `√(sτr)/(64√2)` when `s < 64n/τ`. -/
theorem precision_solver (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    {O : L → (Fin (precN τ ε) → Bool) → W →L[ℂ] W} (hU : ∀ l x, IsUnitary (O l x))
    (w : L → ℕ) (hO : SearchGrowth 2 (fun l j => O l (toBits j)) w)
    (A : TreeSolver (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) O Fl E G ε) :
    hsR τ ε / 32 ≤ A.tree.worstCost w ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ A.tree.worstCost w) := by
  have hacc := A.accurate_ham (precisionMainData τ ε s h.s_ge) τ _ _
    (hard_instances h).2.2.1.isHermitian (norm_scalarInput _ _)
  have hb := AdaptiveHamiltonianLowerBound.precision_tree_general h hL hU w hO A.tree A.readout
    A.readout_isometry A.success hacc
  have hn0 : (0 : ℝ) ≤ precN τ ε := Nat.cast_nonneg _
  refine ⟨by linarith [rbound h hL], fun hs' => ?_⟩
  linarith [failedmix h hL hs']

/-- **Padded time family**: for every known padding `P`, an adaptive solver of the padded time
family over a unitary oracle family with search-weight growth `w` costs at least `c_T √s τ`. -/
theorem time_pad_solver (h : HSRange τ s ε) (P : Type*) [Fintype P] [DecidableEq P]
    {O : L → (Fin (timeN τ) → Fin (2 ^ hsMu s)) → W →L[ℂ] W} (hU : ∀ l x, IsUnitary (O l x))
    (w : L → ℕ) (hO : SearchGrowth (2 ^ hsMu s) O w)
    (A : TreeSolver (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) P) O Fl E G ε) :
    cT * Real.sqrt s * τ ≤ A.tree.worstCost w := by
  have hacc := A.accurate_ham (timePadData τ s h.s_ge P) τ _ _
    (hard_instances_pad h P P P).1.isHermitian
    (by rw [ODELowerBoundExtensions.Padding.norm_inlOp]; exact norm_searchInput _ _ _)
  have hacc' : ∀ j, AdaptiveHamiltonianLowerBound.DensityAccurate
      (padReadout P G refZero ∘L A.readout) (A.tree.conditionalDensity j)
      (evolve (searchHam (timeN τ) (hsMu s) s (timeC τ) τ j) τ
        (searchInput (timeN τ) (hsMu s) s)) ε := by
    intro j
    have hj := hacc j
    rw [show (timePadData τ s h.s_ge P).matrix j =
      padMat P (searchHam (timeN τ) (hsMu s) s (timeC τ) τ j) from rfl, evolve_padMat] at hj
    exact AdaptiveODELowerBound.Padding.densityAccurate_padReadout refZero A.readout _ _ ε hj
  have hb := AdaptiveHamiltonianLowerBound.time_tree_general h hU w hO A.tree
    (padReadout P G refZero ∘L A.readout)
    (padReadout_comp_isometry refZero A.readout A.readout_isometry) A.success hacc'
  have hX : 0 ≤ Real.log 2 / 96 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) :=
    mul_nonneg (mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num))
      (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
  linarith [time_final h.one_le_tau h.s_ge]

/-- **Padded mixed family**: for `L ≥ 64τ`, `s ≥ 64n/τ` and every known padding `P`, an adaptive
solver of the padded mixed family over a unitary oracle family with search-weight growth `w`
costs at least `(log 2/(384√2)) √(sτr)`. -/
theorem mixed_pad_solver (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) (P : Type*) [Fintype P] [DecidableEq P]
    {O : L → (Fin (precN τ ε) → Fin (2 ^ hsMu s)) → W →L[ℂ] W} (hU : ∀ l x, IsUnitary (O l x))
    (w : L → ℕ) (hO : SearchGrowth (2 ^ hsMu s) O w)
    (A : TreeSolver (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) P) O Fl E G ε) :
    Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε) ≤ A.tree.worstCost w := by
  have hacc := A.accurate_ham (mixedPadData τ ε s h.s_ge P) τ _ _
    (hard_instances_pad h P P P).2.1.isHermitian
    (by rw [ODELowerBoundExtensions.Padding.norm_inlOp]; exact norm_searchInput _ _ _)
  have hacc' : ∀ j, AdaptiveHamiltonianLowerBound.DensityAccurate
      (padReadout P G refZero ∘L A.readout) (A.tree.conditionalDensity j)
      (evolve (searchHam (precN τ ε) (hsMu s) s 1 τ j) τ
        (searchInput (precN τ ε) (hsMu s) s)) ε := by
    intro j
    have hj := hacc j
    rw [show (mixedPadData τ ε s h.s_ge P).matrix j =
      padMat P (searchHam (precN τ ε) (hsMu s) s 1 τ j) from rfl, evolve_padMat] at hj
    exact AdaptiveODELowerBound.Padding.densityAccurate_padReadout refZero A.readout _ _ ε hj
  have hb := AdaptiveHamiltonianLowerBound.mixed_tree_general h hL hs hU w hO A.tree
    (padReadout P G refZero ∘L A.readout)
    (padReadout_comp_isometry refZero A.readout A.readout_isometry) A.success hacc'
  have hX : 0 ≤ Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ hsMu s * precN τ ε * τ) :=
    mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num)) (Real.sqrt_nonneg _)
  linarith [mixrbound h hL]

/-- **Padded precision family**: for `L ≥ 64τ` and every known padding `P`, an adaptive solver of
the padded precision family over a unitary oracle family with search-weight growth `w` along
`toBits` costs at least `r/32`, and at least `√(sτr)/(64√2)` when `s < 64n/τ`. -/
theorem precision_pad_solver (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) (P : Type*) [Fintype P]
    [DecidableEq P] {O : L → (Fin (precN τ ε) → Bool) → W →L[ℂ] W}
    (hU : ∀ l x, IsUnitary (O l x)) (w : L → ℕ)
    (hO : SearchGrowth 2 (fun l j => O l (toBits j)) w)
    (A : TreeSolver (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) P) O Fl E G
      ε) :
    hsR τ ε / 32 ≤ A.tree.worstCost w ∧
      ((s : ℝ) < 64 * precN τ ε / τ →
        Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2) ≤ A.tree.worstCost w) := by
  have hacc := A.accurate_ham (precisionPadData τ ε s h.s_ge P) τ _ _
    (hard_instances_pad h P P P).2.2.1.isHermitian
    (by rw [ODELowerBoundExtensions.Padding.norm_inlOp]; exact norm_scalarInput _ _)
  have hacc' : ∀ x, AdaptiveHamiltonianLowerBound.DensityAccurate
      (padReadout P G refZero ∘L A.readout) (A.tree.conditionalDensity x)
      (evolve (scalarHam (precN τ ε) s τ x) τ (scalarInput (precN τ ε) s)) ε := by
    intro x
    have hx := hacc x
    rw [show (precisionPadData τ ε s h.s_ge P).matrix x =
      padMat P (scalarHam (precN τ ε) s τ x) from rfl, evolve_padMat] at hx
    exact AdaptiveODELowerBound.Padding.densityAccurate_padReadout refZero A.readout _ _ ε hx
  have hb := AdaptiveHamiltonianLowerBound.precision_tree_general h hL hU w hO A.tree
    (padReadout P G refZero ∘L A.readout)
    (padReadout_comp_isometry refZero A.readout A.readout_isometry) A.success hacc'
  have hn0 : (0 : ℝ) ≤ precN τ ε := Nat.cast_nonneg _
  refine ⟨by linarith [rbound h hL], fun hs' => ?_⟩
  linarith [failedmix h hL hs']

end

end PhysicalODELowerBound.Families
