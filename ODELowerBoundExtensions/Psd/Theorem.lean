import ODELowerBoundExtensions.Psd.ScalarBound
import SparseLowerBounds.ODE.Precision

/-!
# Theorem `odel:thm:psd`: the constant-coefficient PSD precision lower bound

Manuscript lines 4016-4135 (the numbering of
`SparseLowerBounds/ODE/Statements.lean`; later versions of the manuscript shift Section
`part:odel`, whose labels are the stable references). For `s ≥ 32`, `τ ≥ 1` (the paper: `τ ≥ 2`),
`L = log(1/ε) ≥ 64τ` (`PsdRange`), the homogeneous equation `ẋ = -D_X x` has two hard families
(`psdSearchFamilyAt`, `psdScalarFamilyAt`) with

  `D_X ⪰ 0` (`H = 0`), `‖D_X‖ = η_D = 1`, `T = τ`, `1 ≤ g ≤ √2`,

public supports and dyadic entries (`psd_hardInstance` for the data, `psd_family_hardInstance`
for the families' own data, `psdSearchFamilyAt_props`, `psdScalarFamilyAt_props`), for
which (eq. `odel:eq:psd`)

  `Q_A ≥ psdConst (√(sτr) + r)`,  `psdConst = log 2/(3072√2)`,

in the heralded output model of `ODE.Solver`, counting value queries and all matrix queries.

**Direction of the proof.** As in `ODE.combined`: the quantitative core is the **max form**
`psd_max` (for one solver of each family, the larger value-query count is at least the bound),
assembled by `psd_assembly` from the gadget bound `psd_search_forces` (for `s ≥ 512n/τ`) and
the scalar bounds `psd_scalar_forces`, `psd_scalar_forces_sqrt` (for `s < 512n/τ`); the
**family form** `psd` (one of the two families witnesses the bound, `ODE.Family.Witnesses`
with `ḡ ≥ √2`) follows classically by `ODE.forces_or_of_max` (with the scalar family in the
second and third place). The per-family witnesses are `psd_search_witness` and
`psd_scalar_witness`.

**Dense padding** (lines 4132-4134). The known positive semidefinite dense padding of the
Hamiltonian lower bound's `fullMatrix` (`2^{-⌈log₂ s⌉} 𝟙𝟙ᵀ`, a nonnegative multiple of a
rank-one projection) is part of both generators; it keeps `D_X ⪰ 0`, `‖D_X‖ = 1` and the
row/column norms, and makes the maximum row and column sparsity exactly `s`
(`Hamiltonian.HardInstance.row_sparsity_attained`, `col_sparsity_attained` in
`psd_hardInstance`).

**Scope** (lines 4137-4142). This is precision-dependent hardness inside the purely
dissipative constant-coefficient subclass; it gives no constant-error `Ω(√s τ)` bound for that
subclass, nor the necessity of the factor `ℓ` multiplying `τ_D` in eq. `odel:eq:refined`; no
linear power of `L` in the sparsity-dependent dissipative cost is established. Controlled calls are covered as in `ODE/Model` (**Controlled calls**): the PSD
families have input-independent locators (`HardInstance.locators_const`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Psd

noncomputable section
open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit SparseLowerBounds
  SparseLowerBounds.Hamiltonian SparseLowerBounds.ODE Readout
open scoped ComplexOrder

set_option synthInstance.maxSize 1024

variable {τ ε : ℝ} {s : ℕ}

/-- **The bound of eq. `odel:eq:psd`** with explicit constant:
`psdConst (√(sτr) + r)`, `psdConst = log 2/(3072√2)`, `r = L/log(e + L/τ)`. -/
def psdBound (s : ℕ) (τ ε : ℝ) : ℝ :=
  psdConst * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε)

/-- **Instance properties of both PSD families** (lines 4019-4025, 4074-4077, 4120-4121,
4132-4134): `Hamiltonian.HardInstance` (real symmetric, so `H = 0`; operator norm exactly one;
row and column Euclidean norms at most one, maximum exactly one; maximum row and column
sparsity exactly `s` by the PSD dense padding; exact dyadic words with decode scale one;
input-independent locators, i.e. public supports) and `D ⪰ 0` for every hidden input. -/
theorem psd_hardInstance (h : PsdRange τ s ε) :
    HardInstance (psdSearchDataAt h) ∧ HardInstance (psdScalarDataAt h) ∧
      (∀ j, ((psdSearchDataAt h).matrix j).PosSemidef) ∧
      ∀ x, ((psdScalarDataAt h).matrix x).PosSemidef := by
  unfold psdSearchDataAt psdScalarDataAt
  exact ⟨psdSearchData_hardInstance _ _, psdScalarData_hardInstance _ _,
    fun j => psdSearchData_posSemidef _ _ j, fun x => psdScalarData_posSemidef _ _ x⟩

/-- **Instance properties of the families themselves**: the data of `psdSearchFamilyAt h` and
`psdScalarFamilyAt h` (the one-stage data `oneStageData` of `psdSearchDataAt h`,
`psdScalarDataAt h`) satisfy `Hamiltonian.HardInstance` (public supports, dyadic entries, norm
one, maximum sparsity exactly `s`, ...) and are positive semidefinite at every input and time
address (lines 4019-4025, 4132-4134). -/
theorem psd_family_hardInstance (h : PsdRange τ s ε) :
    HardInstance (psdSearchFamilyAt h).data ∧ HardInstance (psdScalarFamilyAt h).data ∧
      (∀ p, ((psdSearchFamilyAt h).data.matrix p).PosSemidef) ∧
      ∀ p, ((psdScalarFamilyAt h).data.matrix p).PosSemidef := by
  have hI := psd_hardInstance h
  rw [psdSearchFamilyAt_data, psdScalarFamilyAt_data]
  exact ⟨hardInstance_oneStageData hI.1, hardInstance_oneStageData hI.2.1,
    fun p => hI.2.2.1 p.1, fun p => hI.2.2.2 p.1⟩

/-- **The gadget family witnesses `(log 2/(1536√2)) √(sτr)`** for `s ≥ 512n/τ` and any
`ḡ ≥ √2` (line 4116). -/
theorem psd_search_witness (h : PsdRange τ s ε) (hs : 512 * (precN τ ε : ℝ) / τ ≤ s)
    {gbar : ℝ} (hg : Real.sqrt 2 ≤ gbar) :
    (psdSearchFamilyAt h).Witnesses τ gbar ε (psdGadgetConst * Real.sqrt (s * τ * hsR τ ε)) :=
  ⟨psdSearchFamilyAt_inClass h hg, psdSearchFamilyAt_T h, psd_search_forces h hs⟩

/-- **The scalar family witnesses `r/32`** for any `ḡ ≥ √2` (line 4125). -/
theorem psd_scalar_witness (h : PsdRange τ s ε) {gbar : ℝ} (hg : Real.sqrt 2 ≤ gbar) :
    (psdScalarFamilyAt h).Witnesses τ gbar ε (hsR τ ε / 32) :=
  ⟨psdScalarFamilyAt_inClass h hg, psdScalarFamilyAt_T h, psd_scalar_forces h⟩

/-- **Theorem `odel:thm:psd`, max form** (lines 4111-4132): for one solver of the gadget family
and one of the scalar family at `(s, τ, ε)`, the larger value-query count is at least
`psdConst (√(sτr) + r)`. -/
theorem psd_max (h : PsdRange τ s ε) {ιG ιS GG GS : Type} [Fintype ιG] [Fintype ιS]
    [NormedAddCommGroup GG] [InnerProductSpace ℂ GG] [CompleteSpace GG]
    [NormedAddCommGroup GS] [InnerProductSpace ℂ GS] [CompleteSpace GS]
    (AG : Solver ιG (psdSearchFamilyAt h) GG ε) (AS : Solver ιS (psdScalarFamilyAt h) GS ε) :
    psdBound s τ ε ≤
      max (AG.prog.labelCount .value : ℝ) (AS.prog.labelCount .value : ℝ) := by
  unfold psdBound
  exact psd_assembly h (psd_scalar_forces h ιS GS AS).1
    (fun hs => (psd_scalar_forces_sqrt h hs ιS GS AS).1)
    (fun hs => (psd_search_forces h hs ιG GG AG).1)

/-- **Theorem `odel:thm:psd`, family form** (eq. `odel:eq:psd`, lines 4016-4030): for
`s ≥ 32`, `τ ≥ 1`, `L ≥ 64τ` (`PsdRange`) and any `ḡ ≥ √2`, one of the two homogeneous
constant-coefficient PSD families (`D_X ⪰ 0`, `‖D_X‖ = 1`, `T = τ`, `1 ≤ g ≤ √2`) is in the
class (`η = 1`, `T = τ`, `g ≤ ḡ`) and forces `psdConst (√(sτr) + r)` value queries (and as many
matrix queries) on every heralded solver, `psdConst = log 2/(3072√2)`. Derived from `psd_max`
by `ODE.forces_or_of_max`. -/
theorem psd (h : PsdRange τ s ε) {gbar : ℝ} (hg : Real.sqrt 2 ≤ gbar) :
    (psdSearchFamilyAt h).Witnesses τ gbar ε (psdBound s τ ε) ∨
      (psdScalarFamilyAt h).Witnesses τ gbar ε (psdBound s τ ε) := by
  have hf := forces_or_of_max (psdSearchFamilyAt h) (psdScalarFamilyAt h) (psdScalarFamilyAt h)
    (ε := ε) (b := psdBound s τ ε) (by
      intro ι₁ ι₂ ι₃ G₁ G₂ G₃ _ _ _ _ _ _ _ _ _ _ _ _ A₁ A₂ A₃
      exact (psd_max h A₁ A₂).trans (max_le_max le_rfl (le_max_left _ _)))
  rcases hf with hf | hf | hf
  · exact Or.inl ⟨psdSearchFamilyAt_inClass h hg, psdSearchFamilyAt_T h, hf⟩
  · exact Or.inr ⟨psdScalarFamilyAt_inClass h hg, psdScalarFamilyAt_T h, hf⟩
  · exact Or.inr ⟨psdScalarFamilyAt_inClass h hg, psdScalarFamilyAt_T h, hf⟩

end

end ODELowerBoundExtensions.Psd
