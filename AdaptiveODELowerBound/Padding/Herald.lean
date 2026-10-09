import AdaptiveODELowerBound.Herald.Transfer
import AdaptiveODELowerBound.Padding.Readout
import ODELowerBoundExtensions.Padding.Precision

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# The padded `g = 1` families against adaptive protocols

Manuscript lines 4437-4445 ("Pad dimensions to a common known size if desired") for the `g = 1`
families of Lemma `odel:lem:herald`: the released zero-padded families
`ODELowerBoundExtensions.Padding.timePadFamilyAt`, `mixedPadFamilyAt`, `precisionPadFamilyAt`
(`ẋ = -i(H ⊕ 0) x`, `x(0) = ψ_in ⊕ 0`), for adaptive solvers over the sampled-time access and
over its call forms, with the constants of the Hamiltonian lower bound.

Route. The padded data (`LowerBoundRemarks.HamiltonianPadding.timePadData`, `mixedPadData`,
`precisionPadData`) are built from the padded one-bit tables (`padTable`), so they satisfy the
access conditions of the weight method (`hardAccess_timePadData`, `hardAccess_mixedPadData`,
`hardAccess_precisionPadData`, by `AdaptiveHamiltonianLowerBound.Access.bitTable_value_bit`).
For an adaptive protocol over labels admissible for the padded data, the padded target is
`inlOp (e^{-iτH} ψ_in)` (`evolve_padMat`), the readout `padReadout P G refZero ∘ e` is accurate
for `e^{-iτH} ψ_in` (`densityAccurate_padReadout`), and the general bounds
`AdaptiveHamiltonianLowerBound.time_tree_general`, `mixed_tree_general`,
`precision_tree_general` with the numerics `time_final`, `mixrbound`, `rbound`, `failedmix` give
the bounds (`Herald.treeForces_of_ham`).

* `time_forces_pad_tree`, `mixed_forces_pad_tree`, `precision_forces_pad_tree`,
  `precision_forces_sqrt_pad_tree`: the per-family bounds for every known padding `P`.
* `herald_max_cost_pad_tree` (max form over realised value counts), `herald_witness_pad_tree`
  (family form of eq. `odel:eq:hsbound`) and `precision_terms_witness_pad_tree` (the fourth
  sentence of Theorem `odel:thm:combined`, lines 4143-4144, for the padded families).
-/

namespace AdaptiveODELowerBound.Padding

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open LowerBoundRemarks.HamiltonianPadding
open ODELowerBoundExtensions.Padding
open AdaptiveHamiltonianLowerBound.Access (HardAccess toBits)
open AdaptiveODELowerBound.Model

-- The nested spectator spaces over the search index exceed the default instance size.
set_option synthInstance.maxSize 1024

variable {τ ε : ℝ} {s : ℕ}

/-- **The padded time data satisfy the access conditions** along the identity. -/
theorem hardAccess_timePadData (τ : ℝ) (s : ℕ) (hs : 32 ≤ s) (P : Type*) [Fintype P]
    [DecidableEq P] : HardAccess (timePadData τ s hs P) (fun j => j) := by
  exact
    { row_const := fun _ _ => rfl
      column_const := fun _ _ => rfl
      table_bit := fun α => AdaptiveHamiltonianLowerBound.Access.bitTable_value_bit
        (padTable (searchTable (timeN τ) (hsMu s) s (timeC τ) τ) P) oneHotBits
        (fun ka => ⟨ka.1, ka.2, fun _ => rfl⟩) α
        (fun z => (z : Word (searchBits (timeN τ) (hsMu s) s (timeC τ) τ))) }

/-- **The padded mixed data satisfy the access conditions** along the identity. -/
theorem hardAccess_mixedPadData (τ ε : ℝ) (s : ℕ) (hs : 32 ≤ s) (P : Type*) [Fintype P]
    [DecidableEq P] : HardAccess (mixedPadData τ ε s hs P) (fun j => j) := by
  exact
    { row_const := fun _ _ => rfl
      column_const := fun _ _ => rfl
      table_bit := fun α => AdaptiveHamiltonianLowerBound.Access.bitTable_value_bit
        (padTable (searchTable (precN τ ε) (hsMu s) s 1 τ) P) oneHotBits
        (fun ka => ⟨ka.1, ka.2, fun _ => rfl⟩) α
        (fun z => (z : Word (searchBits (precN τ ε) (hsMu s) s 1 τ))) }

/-- **The padded precision data satisfy the access conditions** along `toBits`. -/
theorem hardAccess_precisionPadData (τ ε : ℝ) (s : ℕ) (hs : 32 ≤ s) (P : Type*) [Fintype P]
    [DecidableEq P] : HardAccess (precisionPadData τ ε s hs P) (toBits (n := precN τ ε)) := by
  exact
    { row_const := fun _ _ => rfl
      column_const := fun _ _ => rfl
      table_bit := fun α => AdaptiveHamiltonianLowerBound.Access.bitTable_value_bit
        (padTable (scalarTable (precN τ ε) s τ) P) (fun j => toBits j)
        (fun k => ⟨k, 1, fun _ => rfl⟩) α
        (fun z => (z : Word (scalarBits (precN τ ε) s τ))) }

/-- **Lemma `odel:lem:herald`, padded time family, adaptive protocols** (as `time_forces_tree`):
on `HSRange`, for every known padding `P`, `Q ≥ c_T √s τ`, `c_T = log 2/(192π)`. -/
theorem time_forces_pad_tree (h : HSRange τ s ε) (P : Type*) [Fintype P] [DecidableEq P] :
    TreeForces (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) P) ε
      (cT * Real.sqrt s * τ) := by
  have hI := (hard_instances_pad h P P P).1
  have hA := hardAccess_timePadData τ s h.s_ge P
  refine Herald.treeForces_of_ham (timePadData τ s h.s_ge P) τ _ _ hI.isHermitian
    (by rw [norm_inlOp]; exact norm_searchInput _ _ _) hA.row_const hA.column_const ?_
  intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hO T e he hsucc hacc
  have hacc' : ∀ j, AdaptiveHamiltonianLowerBound.DensityAccurate (padReadout P G refZero ∘L e)
      (T.conditionalDensity j)
      (evolve (searchHam (timeN τ) (hsMu s) s (timeC τ) τ j) τ
        (searchInput (timeN τ) (hsMu s) s)) ε := by
    intro j
    have hj := hacc j
    rw [show (timePadData τ s h.s_ge P).matrix j =
      padMat P (searchHam (timeN τ) (hsMu s) s (timeC τ) τ j) from rfl, evolve_padMat] at hj
    exact densityAccurate_padReadout refZero e _ _ ε hj
  have hb := AdaptiveHamiltonianLowerBound.time_tree_general h
    (fun l j => AdaptiveHamiltonianLowerBound.Access.admissible_unitary _ _ _ (hO l) j) w
    (AdaptiveHamiltonianLowerBound.searchGrowth_admissible
      (AdaptiveHamiltonianLowerBound.even_two_pow_hsMu h.s_ge) _ _ hA O w hO) T
    (padReadout P G refZero ∘L e) (padReadout_comp_isometry refZero e he) hsucc hacc'
  have hX : 0 ≤ Real.log 2 / 96 * timeN τ * Real.sqrt ((2 : ℝ) ^ hsMu s) :=
    mul_nonneg (mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num))
      (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)
  linarith [time_final h.one_le_tau h.s_ge]

/-- **Lemma `odel:lem:herald`, padded mixed family, adaptive protocols**: for `L ≥ 64τ` and
`s ≥ 64n/τ`, `Q ≥ (log 2/(384√2)) √(sτr)`. -/
theorem mixed_forces_pad_tree (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) (P : Type*) [Fintype P] [DecidableEq P] :
    TreeForces (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) P) ε
      (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)) := by
  have hI := (hard_instances_pad h P P P).2.1
  have hA := hardAccess_mixedPadData τ ε s h.s_ge P
  refine Herald.treeForces_of_ham (mixedPadData τ ε s h.s_ge P) τ _ _ hI.isHermitian
    (by rw [norm_inlOp]; exact norm_searchInput _ _ _) hA.row_const hA.column_const ?_
  intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hO T e he hsucc hacc
  have hacc' : ∀ j, AdaptiveHamiltonianLowerBound.DensityAccurate (padReadout P G refZero ∘L e)
      (T.conditionalDensity j)
      (evolve (searchHam (precN τ ε) (hsMu s) s 1 τ j) τ
        (searchInput (precN τ ε) (hsMu s) s)) ε := by
    intro j
    have hj := hacc j
    rw [show (mixedPadData τ ε s h.s_ge P).matrix j =
      padMat P (searchHam (precN τ ε) (hsMu s) s 1 τ j) from rfl, evolve_padMat] at hj
    exact densityAccurate_padReadout refZero e _ _ ε hj
  have hb := AdaptiveHamiltonianLowerBound.mixed_tree_general h hL hs
    (fun l j => AdaptiveHamiltonianLowerBound.Access.admissible_unitary _ _ _ (hO l) j) w
    (AdaptiveHamiltonianLowerBound.searchGrowth_admissible
      (AdaptiveHamiltonianLowerBound.even_two_pow_hsMu h.s_ge) _ _ hA O w hO) T
    (padReadout P G refZero ∘L e) (padReadout_comp_isometry refZero e he) hsucc hacc'
  have hX : 0 ≤ Real.log 2 / 96 * Real.sqrt ((2 : ℝ) ^ hsMu s * precN τ ε * τ) :=
    mul_nonneg (div_nonneg (Real.log_pos one_lt_two).le (by norm_num)) (Real.sqrt_nonneg _)
  linarith [mixrbound h hL]

/-- **Lemma `odel:lem:herald`, padded precision family, adaptive protocols**: for `L ≥ 64τ`,
`Q ≥ r/32`. -/
theorem precision_forces_pad_tree (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) (P : Type*)
    [Fintype P] [DecidableEq P] :
    TreeForces (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) P) ε
      (hsR τ ε / 32) := by
  have hI := (hard_instances_pad h P P P).2.2.1
  have hA := hardAccess_precisionPadData τ ε s h.s_ge P
  refine Herald.treeForces_of_ham (precisionPadData τ ε s h.s_ge P) τ _ _ hI.isHermitian
    (by rw [norm_inlOp]; exact norm_scalarInput _ _) hA.row_const hA.column_const ?_
  intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hO T e he hsucc hacc
  have hacc' : ∀ x, AdaptiveHamiltonianLowerBound.DensityAccurate (padReadout P G refZero ∘L e)
      (T.conditionalDensity x)
      (evolve (scalarHam (precN τ ε) s τ x) τ (scalarInput (precN τ ε) s)) ε := by
    intro x
    have hx := hacc x
    rw [show (precisionPadData τ ε s h.s_ge P).matrix x =
      padMat P (scalarHam (precN τ ε) s τ x) from rfl, evolve_padMat] at hx
    exact densityAccurate_padReadout refZero e _ _ ε hx
  have hb := AdaptiveHamiltonianLowerBound.precision_tree_general h hL
    (fun l x => AdaptiveHamiltonianLowerBound.Access.admissible_unitary _ _ _ (hO l) x) w
    (AdaptiveHamiltonianLowerBound.searchGrowth_admissible even_two _ _ hA O w hO) T
    (padReadout P G refZero ∘L e) (padReadout_comp_isometry refZero e he) hsucc hacc'
  have hn0 : (0 : ℝ) ≤ precN τ ε := Nat.cast_nonneg _
  linarith [rbound h hL]

/-- **Lemma `odel:lem:herald`, padded precision family, small sparsity, adaptive protocols**:
for `L ≥ 64τ` and `s < 64n/τ`, `Q ≥ √(sτr)/(64√2)`. -/
theorem precision_forces_sqrt_pad_tree (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs' : (s : ℝ) < 64 * precN τ ε / τ) (P : Type*) [Fintype P] [DecidableEq P] :
    TreeForces (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) P) ε
      (Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2)) := by
  have hI := (hard_instances_pad h P P P).2.2.1
  have hA := hardAccess_precisionPadData τ ε s h.s_ge P
  refine Herald.treeForces_of_ham (precisionPadData τ ε s h.s_ge P) τ _ _ hI.isHermitian
    (by rw [norm_inlOp]; exact norm_scalarInput _ _) hA.row_const hA.column_const ?_
  intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hO T e he hsucc hacc
  have hacc' : ∀ x, AdaptiveHamiltonianLowerBound.DensityAccurate (padReadout P G refZero ∘L e)
      (T.conditionalDensity x)
      (evolve (scalarHam (precN τ ε) s τ x) τ (scalarInput (precN τ ε) s)) ε := by
    intro x
    have hx := hacc x
    rw [show (precisionPadData τ ε s h.s_ge P).matrix x =
      padMat P (scalarHam (precN τ ε) s τ x) from rfl, evolve_padMat] at hx
    exact densityAccurate_padReadout refZero e _ _ ε hx
  have hb := AdaptiveHamiltonianLowerBound.precision_tree_general h hL
    (fun l x => AdaptiveHamiltonianLowerBound.Access.admissible_unitary _ _ _ (hO l) x) w
    (AdaptiveHamiltonianLowerBound.searchGrowth_admissible even_two _ _ hA O w hO) T
    (padReadout P G refZero ∘L e) (padReadout_comp_isometry refZero e he) hsucc hacc'
  have hn0 : (0 : ℝ) ≤ precN τ ε := Nat.cast_nonneg _
  linarith [failedmix h hL hs']

/-- **Eq. `odel:eq:hsbound` for the padded families, adaptive protocols, max form over realised
counts** (as `herald_max_cost_tree`): for any known paddings and realised worst-case value counts
`q_T`, `q_M`, `q_P` of adaptive solvers of the padded time, mixed and precision families, each
over the sampled-time access or over its call forms, `c₀ (√s τ + √(sτr) + r) ≤ max(q_T, q_M, q_P)`,
`c₀ = log 2/(4096π)`. -/
theorem herald_max_cost_pad_tree (h : HSRange τ s ε) (PT PM PP : Type*) [Fintype PT]
    [DecidableEq PT] [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] {qT qM qP : ℝ}
    (hT : TreeCost (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) ε qT)
    (hM : TreeCost (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) ε qM)
    (hP : TreeCost (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) ε qP) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ max qT (max qM qP) := by
  exact assembly h ((time_forces_pad_tree h PT).le_cost hT)
    (fun hL => ⟨(precision_forces_pad_tree h hL PP).le_cost hP,
      fun hs' => (precision_forces_sqrt_pad_tree h hL hs' PP).le_cost hP⟩)
    (fun hL hs => (mixed_forces_pad_tree h hL hs PM).le_cost hM)

/-- **Eq. `odel:eq:hsbound` for the padded families, adaptive protocols, family form**: on
`HSRange`, for any `ḡ ≥ 1` and known paddings, one of the padded time, mixed and precision
families is in the class and tree-forces `c₀ (√s τ + √(sτr) + r)`, `c₀ = log 2/(4096π)`. The
padded families have `D = 0` and `g = 1` (`ODELowerBoundExtensions.Padding.herald_pad_props`). -/
theorem herald_witness_pad_tree (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar)
    (PT PM PP : Type*) [Fintype PT] [DecidableEq PT] [Fintype PM] [DecidableEq PM]
    [Fintype PP] [DecidableEq PP] :
    TreeWitnesses (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      TreeWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      TreeWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hf := forces_or_of_cost₃
    (P₁ := TreeCost (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) ε)
    (P₂ := TreeCost (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) ε)
    (P₃ := TreeCost (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) ε)
    (b := c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε))
    (fun _ _ _ hT hM hP => herald_max_cost_pad_tree h PT PM PP hT hM hP)
  have hI := herald_instances_pad (ε := ε) h hg PT PM PP
  rcases hf with hf | hf | hf
  · exact Or.inl ⟨hI.1.1, hI.1.2.1, treeForces_of_cost hf⟩
  · exact Or.inr (Or.inl ⟨hI.2.1.1, hI.2.1.2.1, treeForces_of_cost hf⟩)
  · exact Or.inr (Or.inr ⟨hI.2.2.1, hI.2.2.2.1, treeForces_of_cost hf⟩)

/-- **The precision terms of Theorem `odel:thm:combined` for adaptive protocols are witnessed by
padded `g = 1` families** (fourth sentence of the theorem, lines 4143-4144, with the padding of
line 4441; as `precision_terms_witness_tree`): on `HSRange`, for any `ḡ ≥ 1` and any known
paddings, one of the padded homogeneous constant-coefficient families (`D = 0`, `g = 1`)
tree-witnesses `c₀ (√(sτr) + r)`. -/
theorem precision_terms_witness_pad_tree (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar)
    (PT PM PP : Type*) [Fintype PT] [DecidableEq PT] [Fintype PM] [DecidableEq PM]
    [Fintype PP] [DecidableEq PP] :
    TreeWitnesses (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      TreeWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      TreeWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hS : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) h.tau_pos.le
  have hb : c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) :=
    mul_le_mul_of_nonneg_left (by linarith) c0_pos.le
  rcases herald_witness_pad_tree h hg PT PM PP with hw | hw | hw
  · exact Or.inl (hw.mono hb)
  · exact Or.inr (Or.inl (hw.mono hb))
  · exact Or.inr (Or.inr (hw.mono hb))

end

end AdaptiveODELowerBound.Padding
