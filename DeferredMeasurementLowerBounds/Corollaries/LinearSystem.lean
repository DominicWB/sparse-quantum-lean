import DeferredMeasurementLowerBounds.Deferral.Theorem
import DeferredMeasurementLowerBounds.Access.Native
import DeferredMeasurementLowerBounds.Readout.Trace
import LinearSystemLowerBound.Theorem

set_option autoImplicit false

/-!
# Theorem `qlsl:thm:main` for measured algorithms

Manuscript Theorem `qlsl:thm:main` (lines 5070-5100) and lines 5185-5186 of the proof of Lemma
`qlsl:lem:xor`, the lemma behind it ("This argument also
covers controlled queries and adaptive algorithms after coherent purification and padding to
their worst-case query count").

For the hard family of the linear-system lower bound and native data with input-independent
locators and an entry-determined value table, every **measured algorithm** (`Model.Measured`)
over admissible labels (`LinearSystemLowerBound.Native.Admissible`: native calls, including
controlled, masked and inverse native calls, of weight at least one, and input-independent
unitaries) that, from a unit initial vector, heralds success with probability at least `2/3`
on every input and, conditional on success, outputs a state whose reduced state on the output
register is within trace distance `ε` of `|x_A⟩⟨x_A|`, makes in the worst case over all
transcripts more than `κ √s ln(1/ε) / 1536` weighted calls (`lower_bound_sharp_measured`);
the manuscript's constant `1/3072` is `lower_bound_measured`. No constant is lost.

Proof: the deferred protocol (`Deferral.deferredTree`, counted labels the input-dependent ones)
has admissible labels (`Access.native_admissible_selFamily`), the same success mass, and, with
the record register joining the garbage (`Readout.liftEquiv`), the same reduced output
(`Readout.ptrace_liftEquiv`); `LinearSystemLowerBound.lower_bound_sharp` applies.
-/

namespace DeferredMeasurementLowerBounds.Corollaries

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct Matrix ComplexOrder
open SparseHamiltonian SparseLinearSystems.Protocol LinearSystemLowerBound
  LinearSystemLowerBound.Hard LinearSystemLowerBound.Params LinearSystemLowerBound.Native
open DeferredMeasurementLowerBounds.Model DeferredMeasurementLowerBounds.Deferral
open DeferredMeasurementLowerBounds.Access DeferredMeasurementLowerBounds.Readout

variable {Z : Type*} [Fintype Z] [AddCommGroup Z] {K L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **Theorem `qlsl:thm:main` for measured algorithms**, sharp constant: every accurate measured
algorithm over admissible labels makes more than `κ √s ln(1/ε) / 1536` weighted calls in the
worst case over all transcripts. -/
theorem lower_bound_sharp_measured (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64)
    (D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s) Z s)
    (hDm : D.matrix = family κ ε s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (henc : ∃ enc : (Ind κ ε s × Ind κ ε s) → ℂ → Z,
      ∀ x α, D.table x α = enc α (D.matrix x α.1 α.2))
    (O : L → Inp κ ε s → K →L[ℂ] K) (w : L → ℕ) (hO : ∀ l, Admissible D (O l) (w l))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {G : Type*} [Fintype G] [DecidableEq G]
    (V : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Ind κ ε s × G)) (M : Measured O E) (φ : K) (hφ : ‖φ‖ = 1)
    (hM : ∀ x, 2 / 3 ≤ M.successMass x φ ∧
      ∃ h : (ptrace (V.conjStarAlgEquiv (M.conditionalDensity x φ)) -
          ODEMixedOutput.pureOperator (target κ ε s x)).toLinearMap.IsSymmetric,
        ODEMixedOutput.hermitianTraceDistance
          (ptrace (V.conjStarAlgEquiv (M.conditionalDensity x φ)))
          (ODEMixedOutput.pureOperator (target κ ε s x)) h ≤ ε) :
    κ * Real.sqrt s * Real.log (1 / ε) / 1536 < M.worstCost w := by
  classical
  have hO' : ∀ l, AdaptiveHamiltonianLowerBound.Access.Admissible D (O l) (w l) := fun l =>
    (AdaptiveHamiltonianLowerBound.Access.admissible_iff_native D (O l) (w l)).mpr (hO l)
  have hcost : ((deferredTree (nativeCounted O) ℂ M φ hφ).worstCost selWeight : ℝ) ≤
      M.worstCost w := by
    exact_mod_cast (worstCost_deferredTree (counted := nativeCounted O) (F := ℂ) M hφ).trans
      (worstCost_countWeight_le M (nativeCounted O) fun l hl =>
        one_le_of_nativeCounted D hO' l hl)
  refine lt_of_lt_of_le (lower_bound_sharp κ ε s hκ hs hε hε1 D hDm hrow hcol henc
    (selFamily O (nativeCounted O) (DRec M)) selWeight
    (native_admissible_selFamily D hO (DRec M)) (liftEquiv (DOut M) V)
    (deferredTree (nativeCounted O) ℂ M φ hφ) fun x => ?_) hcost
  have heq : ptrace ((liftEquiv (DOut M) V).conjStarAlgEquiv
      ((deferredTree (nativeCounted O) ℂ M φ hφ).conditionalDensity x)) =
      ptrace (V.conjStarAlgEquiv (M.conditionalDensity x φ)) := by
    rw [conditionalDensity_deferredTree (counted := nativeCounted O) (F := ℂ) M hφ x,
      ptrace_liftEquiv, sum_pure_amplitude (counted := nativeCounted O) M x φ]
    rfl
  obtain ⟨hsucc, hacc⟩ := hM x
  refine ⟨?_, ?_⟩
  · rw [successMass_deferredTree (counted := nativeCounted O) (F := ℂ) M hφ x]
    exact hsucc
  · rw [heq]
    exact hacc

/-- **Theorem `qlsl:thm:main` for measured algorithms** with the manuscript's constant:
`Q > κ √s ln(1/ε) / 3072`. -/
theorem lower_bound_measured (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64)
    (D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s) Z s)
    (hDm : D.matrix = family κ ε s)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (henc : ∃ enc : (Ind κ ε s × Ind κ ε s) → ℂ → Z,
      ∀ x α, D.table x α = enc α (D.matrix x α.1 α.2))
    (O : L → Inp κ ε s → K →L[ℂ] K) (w : L → ℕ) (hO : ∀ l, Admissible D (O l) (w l))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {G : Type*} [Fintype G] [DecidableEq G]
    (V : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Ind κ ε s × G)) (M : Measured O E) (φ : K) (hφ : ‖φ‖ = 1)
    (hM : ∀ x, 2 / 3 ≤ M.successMass x φ ∧
      ∃ h : (ptrace (V.conjStarAlgEquiv (M.conditionalDensity x φ)) -
          ODEMixedOutput.pureOperator (target κ ε s x)).toLinearMap.IsSymmetric,
        ODEMixedOutput.hermitianTraceDistance
          (ptrace (V.conjStarAlgEquiv (M.conditionalDensity x φ)))
          (ODEMixedOutput.pureOperator (target κ ε s x)) h ≤ ε) :
    κ * Real.sqrt s * Real.log (1 / ε) / 3072 < M.worstCost w := by
  have h := lower_bound_sharp_measured κ ε s hκ hs hε hε1 D hDm hrow hcol henc O w hO V M φ hφ hM
  have hL : 0 < Real.log (1 / ε) := by
    have := L_ge ε hε hε1; have := log_64_gt; linarith
  have hs0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < s))
  have : 0 < κ * Real.sqrt s * Real.log (1 / ε) := by
    have : (0 : ℝ) < κ := by linarith
    positivity
  linarith

end

end DeferredMeasurementLowerBounds.Corollaries
