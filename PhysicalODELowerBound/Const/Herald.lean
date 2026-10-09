import PhysicalODELowerBound.Const.Transfer
import PhysicalODELowerBound.Families.Herald

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Eq. `odel:eq:hsbound` over the constant-coefficient physical oracle: controlled calls, padding

Manuscript lines 4114-4115 ("The lower bounds thus apply to Theorems `ode:thm:main` and
`ode:thm:time`"), 4392-4435 (eq. `odel:eq:hsbound`, Lemma `odel:lem:herald`) and 4441-4442 ("Pad
dimensions to a common known size if desired"), for the time, mixed and precision families and
their known zero paddings (one-stage, constant coefficient, `D = 0`, `g = 1`) and adaptive solvers
over the physical oracle of the released constant-coefficient solver and over its call forms
(`ConstForces`).

* `time_forces_const`, `mixed_forces_const`, `precision_forces_const`,
  `precision_forces_sqrt_const`, `herald_max_cost_const`, `herald_witness_const`: the unpadded
  families. Without call forms the per-family bounds are those of `ConstantODELowerBound`
  (`ConstantODELowerBound.Herald.time_const_tree`, `mixed_const_tree`, `precision_const_tree`),
  and the max form is the max form of `ConstantODELowerBound`
  (`ConstantODELowerBound.Herald.herald_max_const_tree`), restated with an identical statement and
  rederived from `herald_max_cost_const` by `ConstCost.of_tree`
  (`herald_max_const_tree_of_const`); here the call forms are included and the family form is
  stated.
* `time_forces_pad_const`, `mixed_forces_pad_const`, `precision_forces_pad_const`,
  `precision_forces_sqrt_pad_const`, `herald_max_cost_pad_const`, `herald_witness_pad_const`: the
  padded families, for any known paddings.
* `herald_common_dimension_const`, `herald_qubit_register_const` (lines 2794-2796): the three
  families padded by `PadTo S Nd` to one common dimension `Nd`, in particular `Nd = 2^q`.
* `precision_terms_witness_const`, `precision_terms_witness_pad_const`: the precision terms
  `c₀ (√(sτr) + r)` of Theorem `odel:thm:combined` are witnessed by one of the (padded) `g = 1`
  families (lines 4143-4144).

All per-family bounds come from `Families.time_solver`, `mixed_solver`, `precision_solver` and
their padded forms through `constForces_of_growth`, with the access conditions of the data
(`ConstantODELowerBound.Oracle.hardAccess_constData_ham`).

Known padding registers range over `Type`, the universe of the families in `MeshForces` and
`ConstForces` and of the released normal-form lemma
`ODELowerBoundExtensions.Release.physicalOracle_normal_form` (the released physical oracles are
universe polymorphic); the sampled-time forms in `AdaptiveODELowerBound` allow any universe.
Nothing is lost: the common-dimension forms use `PadTo S Nd : Type`.
-/

namespace PhysicalODELowerBound.Const

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE SparseLowerBounds.Hamiltonian
open NativeSparseBlockEncoding OracleCircuit
open ODELowerBoundExtensions.Padding (timePadFamilyAt mixedPadFamilyAt precisionPadFamilyAt
  SparsityAttained)
open LowerBoundRemarks.HamiltonianPadding (PadTo)
open AdaptiveODELowerBound.Model (forces_or_of_cost₃ TreeSolver)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open ODELowerBoundExtensions.Release (SysOp)
open ConstantODELowerBound.Oracle (constOracle PublicConstSources)

-- The released solver's physical workspace is a nested register product.
set_option synthInstance.maxSize 8192
set_option maxRecDepth 4096

variable {τ ε : ℝ} {s : ℕ}

/-- **Time family over the constant-coefficient oracle**: on `HSRange`, `c_T √s τ`. -/
theorem time_forces_const (h : HSRange τ s ε) :
    ConstForces (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) ε
      (cT * Real.sqrt s * τ) := by
  exact constForces_of_growth (AdaptiveHamiltonianLowerBound.even_two_pow_hsMu h.s_ge) _
    (fun j => j)
    (ConstantODELowerBound.Oracle.hardAccess_constData_ham _ _
      (AdaptiveHamiltonianLowerBound.Access.hardAccess_timeData τ s h.s_ge) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact Families.time_solver h hU w hO A)

/-- **Mixed family over the constant-coefficient oracle**: for `L ≥ 64τ` and `s ≥ 64n/τ`,
`(log 2/(384√2)) √(sτr)`. -/
theorem mixed_forces_const (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) :
    ConstForces (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε
      (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)) := by
  exact constForces_of_growth (AdaptiveHamiltonianLowerBound.even_two_pow_hsMu h.s_ge) _
    (fun j => j)
    (ConstantODELowerBound.Oracle.hardAccess_constData_ham _ _
      (AdaptiveHamiltonianLowerBound.Access.hardAccess_mixedMainData τ ε s h.s_ge) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact Families.mixed_solver h hL hs hU w hO A)

/-- **Precision family over the constant-coefficient oracle**: for `L ≥ 64τ`, `r/32`. -/
theorem precision_forces_const (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) :
    ConstForces (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε
      (hsR τ ε / 32) := by
  exact constForces_of_growth even_two _ AdaptiveHamiltonianLowerBound.Access.toBits
    (ConstantODELowerBound.Oracle.hardAccess_constData_ham _ _
      (AdaptiveHamiltonianLowerBound.Access.hardAccess_precisionMainData τ ε s h.s_ge) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact (Families.precision_solver h hL hU w hO A).1)

/-- **Precision family for small sparsity over the constant-coefficient oracle**: for
`L ≥ 64τ` and `s < 64n/τ`, `√(sτr)/(64√2)`. -/
theorem precision_forces_sqrt_const (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : (s : ℝ) < 64 * precN τ ε / τ) :
    ConstForces (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε
      (Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2)) := by
  exact constForces_of_growth even_two _ AdaptiveHamiltonianLowerBound.Access.toBits
    (ConstantODELowerBound.Oracle.hardAccess_constData_ham _ _
      (AdaptiveHamiltonianLowerBound.Access.hardAccess_precisionMainData τ ε s h.s_ge) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact (Families.precision_solver h hL hU w hO A).2 hs)

/-- **Eq. `odel:eq:hsbound` over the constant-coefficient oracle, max form over realised
counts**: `c₀ (√s τ + √(sτr) + r) ≤ max(q_T, q_M, q_P)`, `c₀ = log 2/(4096π)`. -/
theorem herald_max_cost_const (h : HSRange τ s ε) {qT qM qP : ℝ}
    (hT : ConstCost (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) ε qT)
    (hM : ConstCost (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε qM)
    (hP : ConstCost (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε qP) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ max qT (max qM qP) := by
  exact SparseLowerBounds.Hamiltonian.assembly h ((time_forces_const h).le_cost hT)
    (fun hL => ⟨(precision_forces_const h hL).le_cost hP,
      fun hs => (precision_forces_sqrt_const h hL hs).le_cost hP⟩)
    (fun hL hs => (mixed_forces_const h hL hs).le_cost hM)

/-- **Eq. `odel:eq:hsbound` over the constant-coefficient physical oracle, family form**: on
`HSRange` and for any `ḡ ≥ 1`, one of the time, mixed and precision families is in the class
(`η = 1`, `T = τ`, `g ≤ ḡ`) and forces `c₀ (√s τ + √(sτr) + r)` value calls (and as many matrix
calls) on every adaptive solver over the physical oracle of the released constant-coefficient
solver or over its call forms (controlled and controlled-inverse calls included). -/
theorem herald_witness_const (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar) :
    ConstWitnesses (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      ConstWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      ConstWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  rcases forces_or_of_cost₃
      (P₁ := ConstCost (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) ε)
      (P₂ := ConstCost (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε)
      (P₃ := ConstCost (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) ε)
      (b := c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε))
      (fun _ _ _ h₁ h₂ h₃ => herald_max_cost_const h h₁ h₂ h₃) with hf | hf | hf
  · exact Or.inl ⟨timeFamilyAt_inClass h hg, timeFamilyAt_T h, constForces_of_cost hf⟩
  · exact Or.inr (Or.inl ⟨mixedFamilyAt_inClass h hg, mixedFamilyAt_T h, constForces_of_cost hf⟩)
  · exact Or.inr (Or.inr
      ⟨precisionFamilyAt_inClass h hg, precisionFamilyAt_T h, constForces_of_cost hf⟩)

/-- **Padded time family over the constant-coefficient oracle**: on `HSRange`, for every known
padding `P`, `c_T √s τ`. -/
theorem time_forces_pad_const (h : HSRange τ s ε) (P : Type) [Fintype P] [DecidableEq P] :
    ConstForces (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) P) ε
      (cT * Real.sqrt s * τ) := by
  exact constForces_of_growth (AdaptiveHamiltonianLowerBound.even_two_pow_hsMu h.s_ge) _
    (fun j => j)
    (ConstantODELowerBound.Oracle.hardAccess_constData_ham _ _
      (AdaptiveODELowerBound.Padding.hardAccess_timePadData τ s h.s_ge P) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact Families.time_pad_solver h P hU w hO A)

/-- **Padded mixed family over the constant-coefficient oracle**: for `L ≥ 64τ`, `s ≥ 64n/τ` and
every known padding `P`, `(log 2/(384√2)) √(sτr)`. -/
theorem mixed_forces_pad_const (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : 64 * (precN τ ε : ℝ) / τ ≤ s) (P : Type) [Fintype P] [DecidableEq P] :
    ConstForces (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) P) ε
      (Real.log 2 / (384 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)) := by
  exact constForces_of_growth (AdaptiveHamiltonianLowerBound.even_two_pow_hsMu h.s_ge) _
    (fun j => j)
    (ConstantODELowerBound.Oracle.hardAccess_constData_ham _ _
      (AdaptiveODELowerBound.Padding.hardAccess_mixedPadData τ ε s h.s_ge P) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact Families.mixed_pad_solver h hL hs P hU w hO A)

/-- **Padded precision family over the constant-coefficient oracle**: for `L ≥ 64τ` and every
known padding `P`, `r/32`. -/
theorem precision_forces_pad_const (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) (P : Type)
    [Fintype P] [DecidableEq P] :
    ConstForces (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) P) ε
      (hsR τ ε / 32) := by
  exact constForces_of_growth even_two _ AdaptiveHamiltonianLowerBound.Access.toBits
    (ConstantODELowerBound.Oracle.hardAccess_constData_ham _ _
      (AdaptiveODELowerBound.Padding.hardAccess_precisionPadData τ ε s h.s_ge P) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact (Families.precision_pad_solver h hL P hU w hO A).1)

/-- **Padded precision family for small sparsity over the constant-coefficient oracle**: for
`L ≥ 64τ`, `s < 64n/τ` and every known padding `P`, `√(sτr)/(64√2)`. -/
theorem precision_forces_sqrt_pad_const (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε)
    (hs : (s : ℝ) < 64 * precN τ ε / τ) (P : Type) [Fintype P] [DecidableEq P] :
    ConstForces (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) P) ε
      (Real.sqrt (s * τ * hsR τ ε) / (64 * Real.sqrt 2)) := by
  exact constForces_of_growth even_two _ AdaptiveHamiltonianLowerBound.Access.toBits
    (ConstantODELowerBound.Oracle.hardAccess_constData_ham _ _
      (AdaptiveODELowerBound.Padding.hardAccess_precisionPadData τ ε s h.s_ge P) _ _ _)
    (by
      intro L W Fl E G _ _ _ _ _ _ _ _ _ _ _ _ _ O w hU hO A
      exact (Families.precision_pad_solver h hL P hU w hO A).2 hs)

/-- **Eq. `odel:eq:hsbound` for the padded families over the constant-coefficient oracle, max
form over realised counts**: for any known paddings,
`c₀ (√s τ + √(sτr) + r) ≤ max(q_T, q_M, q_P)`. -/
theorem herald_max_cost_pad_const (h : HSRange τ s ε) (PT PM PP : Type) [Fintype PT]
    [DecidableEq PT] [Fintype PM] [DecidableEq PM] [Fintype PP] [DecidableEq PP] {qT qM qP : ℝ}
    (hT : ConstCost (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) ε qT)
    (hM : ConstCost (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) ε qM)
    (hP : ConstCost (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) ε qP) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ max qT (max qM qP) := by
  exact SparseLowerBounds.Hamiltonian.assembly h ((time_forces_pad_const h PT).le_cost hT)
    (fun hL => ⟨(precision_forces_pad_const h hL PP).le_cost hP,
      fun hs => (precision_forces_sqrt_pad_const h hL hs PP).le_cost hP⟩)
    (fun hL hs => (mixed_forces_pad_const h hL hs PM).le_cost hM)

/-- **Eq. `odel:eq:hsbound` for the padded families over the constant-coefficient physical
oracle, family form**: on `HSRange`, for any `ḡ ≥ 1` and any known paddings, one of the padded
time, mixed and precision families (`D = 0`, `g = 1`) is in the class and forces
`c₀ (√s τ + √(sτr) + r)` value calls (and as many matrix calls) on every adaptive solver over the
physical oracle of the released constant-coefficient solver or over its call forms. The instance
facts (class, `T = τ`, maximum sparsity exactly `s`) are
`ODELowerBoundExtensions.Padding.herald_instances_pad`. -/
theorem herald_witness_pad_const (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar)
    (PT PM PP : Type) [Fintype PT] [DecidableEq PT] [Fintype PM] [DecidableEq PM]
    [Fintype PP] [DecidableEq PP] :
    ConstWitnesses (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      ConstWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      ConstWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) τ gbar ε
        (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hI := ODELowerBoundExtensions.Padding.herald_instances_pad h hg PT PM PP
  rcases forces_or_of_cost₃
      (P₁ := ConstCost (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) ε)
      (P₂ := ConstCost (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) ε)
      (P₃ := ConstCost (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) ε)
      (b := c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε))
      (fun _ _ _ h₁ h₂ h₃ => herald_max_cost_pad_const h PT PM PP h₁ h₂ h₃) with hf | hf | hf
  · exact Or.inl ⟨hI.1.1, hI.1.2.1, constForces_of_cost hf⟩
  · exact Or.inr (Or.inl ⟨hI.2.1.1, hI.2.1.2.1, constForces_of_cost hf⟩)
  · exact Or.inr (Or.inr ⟨hI.2.2.1, hI.2.2.2.1, constForces_of_cost hf⟩)

/-- **Eq. `odel:eq:hsbound` in one common dimension over the constant-coefficient oracle** (lines
2794-2796, "append known zeros to equalise dimensions across families or to obtain a qubit
register", and 4441-4442): for every `Nd` at least the dimensions of the three hard families, the
time, mixed and precision families padded by `PadTo S Nd` have dimension exactly `Nd` and maximum
sparsity exactly `s`, and for any `ḡ ≥ 1` one of them is in the class and forces
`c₀ (√s τ + √(sτr) + r)` value calls (and as many matrix calls) on every adaptive solver over the
constant-coefficient physical oracle or its call forms. -/
theorem herald_common_dimension_const (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar) (Nd : ℕ)
    (hT : Fintype.card (SearchIndex (timeN τ) (hsMu s) s) ≤ Nd)
    (hM : Fintype.card (SearchIndex (precN τ ε) (hsMu s) s) ≤ Nd)
    (hP : Fintype.card (ScalarIndex (precN τ ε) s) ≤ Nd) :
    Fintype.card (SearchIndex (timeN τ) (hsMu s) s ⊕
        PadTo (SearchIndex (timeN τ) (hsMu s) s) Nd) = Nd ∧
      Fintype.card (SearchIndex (precN τ ε) (hsMu s) s ⊕
        PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd) = Nd ∧
      Fintype.card (ScalarIndex (precN τ ε) s ⊕ PadTo (ScalarIndex (precN τ ε) s) Nd) = Nd ∧
      (SparsityAttained (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (SearchIndex (timeN τ) (hsMu s) s) Nd)) ∧
        SparsityAttained (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)) ∧
        SparsityAttained (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (ScalarIndex (precN τ ε) s) Nd))) ∧
      (ConstWitnesses (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (SearchIndex (timeN τ) (hsMu s) s) Nd)) τ gbar ε
          (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
        ConstWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)) τ gbar ε
          (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
        ConstWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (ScalarIndex (precN τ ε) s) Nd)) τ gbar ε
          (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε))) := by
  have hI := ODELowerBoundExtensions.Padding.herald_instances_pad h hg
    (PadTo (SearchIndex (timeN τ) (hsMu s) s) Nd) (PadTo (SearchIndex (precN τ ε) (hsMu s) s) Nd)
    (PadTo (ScalarIndex (precN τ ε) s) Nd)
  exact ⟨LowerBoundRemarks.HamiltonianPadding.card_padTo hT,
    LowerBoundRemarks.HamiltonianPadding.card_padTo hM,
    LowerBoundRemarks.HamiltonianPadding.card_padTo hP, ⟨hI.1.2.2, hI.2.1.2.2, hI.2.2.2.2⟩,
    herald_witness_pad_const h hg _ _ _⟩

/-- **Eq. `odel:eq:hsbound` on a qubit register over the constant-coefficient oracle** (lines
2794-2796 and 4441-4442): for every `q` with `4 s (τ + r + 1) ≤ 2^q`, the time, mixed and
precision families padded by `PadTo S (2^q)` have dimension exactly `2^q` and maximum sparsity
exactly `s`, and for any `ḡ ≥ 1` one of them is in the class and forces `c₀ (√s τ + √(sτr) + r)`
value calls (and as many matrix calls) on every adaptive solver over the constant-coefficient
physical oracle or its call forms. -/
theorem herald_qubit_register_const (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar) (q : ℕ)
    (hq : 4 * s * (τ + hsR τ ε + 1) ≤ (2 : ℝ) ^ q) :
    Fintype.card (SearchIndex (timeN τ) (hsMu s) s ⊕
        PadTo (SearchIndex (timeN τ) (hsMu s) s) (2 ^ q)) = 2 ^ q ∧
      Fintype.card (SearchIndex (precN τ ε) (hsMu s) s ⊕
        PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q)) = 2 ^ q ∧
      Fintype.card (ScalarIndex (precN τ ε) s ⊕
        PadTo (ScalarIndex (precN τ ε) s) (2 ^ q)) = 2 ^ q ∧
      (SparsityAttained (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (SearchIndex (timeN τ) (hsMu s) s) (2 ^ q))) ∧
        SparsityAttained (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q))) ∧
        SparsityAttained (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (ScalarIndex (precN τ ε) s) (2 ^ q)))) ∧
      (ConstWitnesses (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (SearchIndex (timeN τ) (hsMu s) s) (2 ^ q))) τ gbar ε
          (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
        ConstWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (SearchIndex (precN τ ε) (hsMu s) s) (2 ^ q))) τ gbar ε
          (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
        ConstWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])
          (PadTo (ScalarIndex (precN τ ε) s) (2 ^ q))) τ gbar ε
          (c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε))) := by
  obtain ⟨hT, hM, hP⟩ := LowerBoundRemarks.HamiltonianPadding.card_le_of_dim h (Nd := 2 ^ q)
    (by push_cast; exact hq)
  exact herald_common_dimension_const h hg (2 ^ q) hT hM hP

/-- **Containment of the max form of `ConstantODELowerBound`**: the statement of
`ConstantODELowerBound.Herald.herald_max_const_tree` (three adaptive solvers over the
constant-coefficient physical oracle itself), restated identically and rederived from
`herald_max_cost_const` applied to the realised counts `ConstCost.of_tree`, with the matrix count
at least the value count (`AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree`). -/
theorem herald_max_const_tree_of_const (h : HSRange τ s ε) (ιT ιM ιP : Type) [Fintype ιT]
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
  have hv := herald_max_cost_const h (ConstCost.of_tree ιT NT TT dT hJT AT)
    (ConstCost.of_tree ιM NM TM dM hJM AM) (ConstCost.of_tree ιP NP TP dP hJP AP)
  exact ⟨hv, hv.trans (max_le_max
    (by exact_mod_cast AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree AT.tree)
    (max_le_max
      (by exact_mod_cast AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree AM.tree)
      (by exact_mod_cast AdaptiveODELowerBound.Release.worstCost_value_le_matrix_tree AP.tree)))⟩

/-- **The precision terms of Theorem `odel:thm:combined` over the constant-coefficient physical
oracle are witnessed by `g = 1` families** (fourth sentence of the theorem, lines 4143-4144): on
`HSRange`, for any `ḡ ≥ 1`, one of the homogeneous constant-coefficient families with `D = 0` and
`g = 1` (time, mixed, precision) witnesses `c₀ (√(sτr) + r)` on every adaptive solver over the
physical oracle or its call forms. From `herald_witness_const` by `ConstWitnesses.mono`. -/
theorem precision_terms_witness_const (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar) :
    ConstWitnesses (timeFamilyAt τ s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      ConstWitnesses (mixedFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      ConstWitnesses (precisionFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau])) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hS : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) h.tau_pos.le
  have hb : c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) :=
    mul_le_mul_of_nonneg_left (by linarith) c0_pos.le
  rcases herald_witness_const h hg with hw | hw | hw
  · exact Or.inl (hw.mono hb)
  · exact Or.inr (Or.inl (hw.mono hb))
  · exact Or.inr (Or.inr (hw.mono hb))

/-- **The precision terms of Theorem `odel:thm:combined` over the constant-coefficient physical
oracle are witnessed by padded `g = 1` families** (fourth sentence of the theorem, lines 4143-4144,
with the padding of line 4441): on `HSRange`, for any `ḡ ≥ 1` and any known paddings, one of the
padded homogeneous constant-coefficient families with `D = 0` and `g = 1` (time, mixed, precision)
witnesses `c₀ (√(sτr) + r)` on every adaptive solver over the physical oracle or its call forms.
From `herald_witness_pad_const` by `ConstWitnesses.mono`. -/
theorem precision_terms_witness_pad_const (h : HSRange τ s ε) {gbar : ℝ} (hg : 1 ≤ gbar)
    (PT PM PP : Type) [Fintype PT] [DecidableEq PT] [Fintype PM] [DecidableEq PM]
    [Fintype PP] [DecidableEq PP] :
    ConstWitnesses (timePadFamilyAt τ s h.s_ge (by linarith [h.one_le_tau]) PT) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      ConstWitnesses (mixedPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PM) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) ∨
      ConstWitnesses (precisionPadFamilyAt τ ε s h.s_ge (by linarith [h.one_le_tau]) PP) τ gbar ε
        (c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)) := by
  have hS : 0 ≤ Real.sqrt s * τ := mul_nonneg (Real.sqrt_nonneg _) h.tau_pos.le
  have hb : c0 * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) :=
    mul_le_mul_of_nonneg_left (by linarith) c0_pos.le
  rcases herald_witness_pad_const h hg PT PM PP with hw | hw | hw
  · exact Or.inl (hw.mono hb)
  · exact Or.inr (Or.inl (hw.mono hb))
  · exact Or.inr (Or.inr (hw.mono hb))

end

end PhysicalODELowerBound.Const
