import SparseLinearSystems.Endpoint.Correctness
import SparseLinearSystems.Endpoint.Cost

/-!
# Theorem `qls:thm:main`: an optimal sparse-query linear-system algorithm

The data `D : NativeSparseBlockEncoding.Data X n Z s` supply, for every input
`x : X`, an `s`-sparse matrix `A_x = Aop D x` (exact finite-word entries,
padded injective in-place row and column locators with full unitary
extensions), and `Ub x` is the state preparation `U_b |0⟩ = |b⟩` with public
reference state `sv = |0⟩`.  The promise of equation `qls:eq:promise` for one
input is `Promise D κ x`: `‖A‖ ≤ 1`, `A` invertible and `‖A⁻¹‖ ≤ κ`.

`algorithm D Ub sv κ ε` is one bounded adaptive protocol, built from the public
parameters `s, κ, ε` only, whose circuits call the primitive matrix oracles and
the controlled source preparation (`physOracle`).  Theorem `main`:

* every transcript makes at most `4·10¹² √s κ log(1/ε)` matrix-oracle calls and
  `2·10¹¹ √s κ log(1/ε)` calls of the controlled `U_b` or `U_b†`;
* for every input satisfying the promise, every run is unitary, the heralded
  success probability is at least `2/3`, and the conditional output is a
  density operator within trace distance `ε` of `|x⟩⟨x|`,
  `x = A⁻¹ b / ‖A⁻¹ b‖`.

`main_exists` states the same with the protocol existentially quantified
before all unknown inputs.
-/

namespace SparseLinearSystems.Endpoint

noncomputable section
open SparseHamiltonian
open ContinuousLinearMap OracleCircuit HilbertAugmentation Augmented SparseBranch LogicalWalk
  Cells Step Run Facts Protocol
open scoped Ring
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- **The promise of equation `qls:eq:promise`** for one input `x`:
`‖A‖ ≤ 1`, `A` invertible and `‖A⁻¹‖ ≤ κ` (spectral norms). -/
structure Promise (D : NativeSparseBlockEncoding.Data X n Z s) (κ : ℝ) (x : X) : Prop where
  norm_le : ‖Aop D x‖ ≤ 1
  isUnit : IsUnit (Aop D x)
  inverse_norm_le : ‖(Aop D x)⁻¹ʳ‖ ≤ κ

/-- The normalised solution `|x⟩ = A⁻¹ b / ‖A⁻¹ b‖`, `b = U_b |0⟩`. -/
def solutionState (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (sv : V0) (x : X) : V0 :=
  ODEStateNormalization.unitDirection ((Aop D x)⁻¹ʳ (Ub x sv))

namespace Promise

variable {D : NativeSparseBlockEncoding.Data X n Z s} {κ : ℝ} {x : X}

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem inverse_apply (h : Promise D κ x) (v : V0) : (Aop D x)⁻¹ʳ (Aop D x v) = v := by
  have e := congrArg (fun f : V0 →L[ℂ] V0 => f v) (Ring.inverse_mul_cancel _ h.isUnit)
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using e

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem apply_inverse (h : Promise D κ x) (v : V0) : Aop D x ((Aop D x)⁻¹ʳ v) = v := by
  have e := congrArg (fun f : V0 →L[ℂ] V0 => f v) (Ring.mul_inverse_cancel _ h.isUnit)
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using e

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The lower bound `‖v‖ ≤ κ ‖A v‖` used by the analysis. -/
theorem lower (h : Promise D κ x) (v : V0) : ‖v‖ ≤ κ * ‖Aop D x v‖ :=
  calc ‖v‖ = ‖(Aop D x)⁻¹ʳ (Aop D x v)‖ := by rw [h.inverse_apply]
    _ ≤ ‖(Aop D x)⁻¹ʳ‖ * ‖Aop D x v‖ := le_opNorm _ _
    _ ≤ κ * ‖Aop D x v‖ := mul_le_mul_of_nonneg_right h.inverse_norm_le (norm_nonneg _)

end Promise

/-- **Theorem `qls:thm:main`.**  One public bounded protocol: worst-case query
counts over all transcripts, and for every input satisfying the promise,
unitary runs, success probability at least `2/3` and conditional trace distance
at most `ε` from the normalised solution. -/
theorem main (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ((algorithm D Ub sv κ ε).worstCost wMat : ℝ) ≤
        4 * 10 ^ 12 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ((algorithm D Ub sv κ ε).worstCost wSrc : ℝ) ≤
        2 * 10 ^ 11 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Promise D κ x →
        (algorithm D Ub sv κ ε).RunsUnitary x ∧
        2 / 3 ≤ (algorithm D Ub sv κ ε).successMass x ∧
        ODEMixedOutput.IsDensity ((algorithm D Ub sv κ ε).conditionalDensity x) ∧
        ∃ h : ((algorithm D Ub sv κ ε).conditionalDensity x -
            ODEMixedOutput.pureOperator (solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance ((algorithm D Ub sv κ ε).conditionalDensity x)
            (ODEMixedOutput.pureOperator (solutionState D Ub sv x)) h ≤ ε := by
  refine ⟨algorithm_matrix_queries D Ub sv κ ε hκ hε hε1,
    algorithm_source_queries D Ub sv κ ε hκ hε hε1, ?_⟩
  intro x hx
  have hU : (algorithm D Ub sv κ ε).RunsUnitary x :=
    Estimator.stages_runsUnitary x _ _ _ _ κ (fun j r => testRun_unitary D Ub hUb sv κ ε j r x) _ _
  obtain ⟨hM, hout⟩ := correctness D Ub hUb sv hsv κ ε hκ hε hε1 x hx.norm_le hx.lower
  obtain ⟨hdens, hsym, hdist⟩ := hout _ (hx.apply_inverse (Ub x sv))
  exact ⟨hU, hM, hdens, hsym, hdist⟩

/-- **Theorem `qls:thm:main`, existential form**: one counter size and one
protocol, chosen before every unknown input, satisfy all guarantees. -/
theorem main_exists (D : NativeSparseBlockEncoding.Data X n Z s) (Ub : X → V0 →L[ℂ] V0)
    (hUb : ∀ x, IsUnitary (Ub x)) (sv : V0) (hsv : ‖sv‖ = 1) (κ ε : ℝ) (hκ : 1 ≤ κ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ∃ (T : ℕ) (P : Tree (physOracle D Ub T) (PrivO n) V0),
      (P.worstCost wMat : ℝ) ≤ 4 * 10 ^ 12 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      (P.worstCost wSrc : ℝ) ≤ 2 * 10 ^ 11 * Real.sqrt s * κ * Real.log (1 / ε) ∧
      ∀ x : X, Promise D κ x →
        P.RunsUnitary x ∧ 2 / 3 ≤ P.successMass x ∧
        ODEMixedOutput.IsDensity (P.conditionalDensity x) ∧
        ∃ h : (P.conditionalDensity x -
            ODEMixedOutput.pureOperator (solutionState D Ub sv x)).toLinearMap.IsSymmetric,
          ODEMixedOutput.hermitianTraceDistance (P.conditionalDensity x)
            (ODEMixedOutput.pureOperator (solutionState D Ub sv x)) h ≤ ε :=
  ⟨Tw s κ ε, algorithm D Ub sv κ ε, main D Ub hUb sv hsv κ ε hκ hε hε1⟩

end

end SparseLinearSystems.Endpoint
