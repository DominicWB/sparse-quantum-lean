import ManuscriptConformance.Defs
import ManuscriptConformance.Readout
import SparseLinearSystems.Separate.Main

/-!
# Conformance: separate matrix and preparation query bounds

Corollary `qls:cor:separate`, in the native model of Theorem `qls:thm:main`, conditional on the
external solver of Gao, Ji and Liu.

* **Input.** As in `qls_thm_main`: native sparse data `D` for `A` (`s ≥ 1` slots), with
  `‖A‖ ≤ 1`, `A` invertible, `‖A⁻¹‖ ≤ κ`, `κ ≥ 1`; a preparation unitary `U_b` with known unit
  seed; `0 < ε ≤ 1/10`; and a public scalar `ν̂` with `ν/2 ≤ ν̂ ≤ 2ν`, `ν = ‖A⁻¹ b‖` (the cost
  of obtaining `ν̂` is not counted).
* **Hypothesis.** `ext_separateSolver : SparseLinearSystems.Separate.SeparateSolver cM cb q₀`, a
  uniform single-trial block-input solver for general (not necessarily Hermitian) finite systems
  with at most `cM κ_M log(2/δ)` block-encoding calls and `cb (1 + κ_M/η)` preparation calls,
  heralded success at least `q₀` and direction error `δ`, for estimates `η` of `‖M⁻¹ β‖` in the
  relaxed interval `[3/8, 5/2]`. It is a hypothesis of the theorem, not an axiom; the external
  solver theorem is not formalised in this package. This single-circuit form is stronger than
  the statement of Gao–Ji–Liu's theorem (success `2/3` by repeated measurement) and is intended
  to follow from its proof.
* **Algorithm.** One protocol (`SparseLinearSystems.Separate.protocol`, at most `⌈6/q₀⌉` fresh
  trials; the manuscript instead runs the measured solver five times) over the physical oracle
  family `SparseLinearSystems.Separate.sepOracle` (the three sparse primitives and the controlled
  preparation, with the weights `Step.wMat`, `Step.wSrc` of `qls_thm_main`), fixed before the
  instance.
* **Guarantee.** Success probability at least `2/3`; conditional on success a density operator
  within trace distance `ε` of `A⁻¹|b⟩/‖A⁻¹b‖`.
* **Cost.** On every completed history: at most `C_A √s κ log(1/ε)` matrix queries, on every
  input; at most `C_b κ/ν` calls of `U_b`, `U_b†` (controlled), on every valid input.
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian OracleCircuit
open scoped InnerProduct InnerProductSpace

universe u v w

set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 2048

set_option maxHeartbeats 4000000 in
/-- **Corollary `qls:cor:separate`**, conditional on the external solver interface
(`ext_separateSolver`, Gao–Ji–Liu). For native sparse data `D` with `s ≥ 1` slots, a unitary
preparation `U_b`, `κ ≥ 1`, `0 < ε ≤ 1/10` and a public scalar `ν̂`, one protocol, fixed before the
instance, uses on every completed history at most `C_A √s κ log(1/ε)` matrix queries, and on every
input with `‖A‖ ≤ 1`, `A` invertible, `‖A⁻¹‖ ≤ κ` and `ν/2 ≤ ν̂ ≤ 2ν` (`ν = ‖A⁻¹ b‖`) it uses on
every completed history at most `C_b κ/ν` calls of `U_b`, `U_b†`, succeeds with probability at least
`2/3`, and has conditional output a density operator within trace distance `ε` of `A⁻¹|b⟩/‖A⁻¹b‖`.
The constants are `C_A = 54 N (12 cM + 1)` and `C_b = (73/9) N cb` with `N = ⌈6/q₀⌉`. Formal
restrictions: the solver enters as the single-trial hypothesis `ext_separateSolver`, stronger than
the statement of Gao–Ji–Liu's theorem and not proved here; `N` single trials replace the
manuscript's five runs of the measured solver. -/
theorem qls_cor_separate (cM cb q₀ : ℝ) (hcM : 0 ≤ cM) (hcb : 0 < cb) (hq₀ : 0 < q₀)
    (ext_separateSolver : SparseLinearSystems.Separate.SeparateSolver.{v, max v w} cM cb q₀) :
    ∃ CA Cb : ℝ, 0 < CA ∧ 0 < Cb ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : NativeSparseBlockEncoding.Data X n Z s)
        (Ub : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), (∀ x, IsUnitary (Ub x)) →
        ∀ sv : EuclideanSpace ℂ n, ‖sv‖ = 1 →
        ∀ κ ε νh : ℝ, 1 ≤ κ → 0 < ε → ε ≤ 1 / 10 →
        ∃ (Tc : ℕ) (A : ODERepeatProtocol.Protocol (SparseLinearSystems.Separate.sepOracle D Ub Tc)
            (EuclideanSpace ℂ n)),
          (A.worstCost SparseLinearSystems.Step.wMat : ℝ) ≤
              CA * Real.sqrt s * κ * Real.log (1 / ε) ∧
          (∀ h : ODERepeatProtocol.Protocol.History A,
            (h.cost SparseLinearSystems.Step.wMat : ℝ) ≤ CA * Real.sqrt s * κ * Real.log (1 / ε)) ∧
          ∀ x : X,
            ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1 →
            IsUnit (SparseStateOverlap.matrixOperator (D.matrix x)) →
            ‖Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ κ →
            ‖Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x)) (Ub x sv)‖ / 2 ≤ νh →
            νh ≤ 2 * ‖Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x)) (Ub x sv)‖ →
            (A.worstCost SparseLinearSystems.Step.wSrc : ℝ) ≤
                Cb * κ / ‖Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x)) (Ub x sv)‖ ∧
            (∀ h : ODERepeatProtocol.Protocol.History A,
              (h.cost SparseLinearSystems.Step.wSrc : ℝ) ≤
                Cb * κ /
                  ‖Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x)) (Ub x sv)‖) ∧
            2 / 3 ≤ A.successMass x ∧ ODEMixedOutput.IsDensity (A.conditionalDensity x) ∧
              TraceDistanceLE (A.conditionalDensity x)
                (ODEStateNormalization.unitDirection
                  (Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x)) (Ub x sv))) ε := by
  refine ⟨SparseLinearSystems.Separate.constA cM q₀, SparseLinearSystems.Separate.constB cb q₀,
    SparseLinearSystems.Separate.constA_pos cM q₀ hcM hq₀,
    SparseLinearSystems.Separate.constB_pos cb q₀ hcb hq₀, ?_⟩
  intro X n Z _ _ _ _ _ s D Ub hUb sv hsv κ ε νh hκ hε hε1
  obtain ⟨Tc, A, hM, hA⟩ := SparseLinearSystems.Separate.main cM cb q₀ hcM hcb.le hq₀
    ext_separateSolver D Ub hUb sv hsv κ ε νh hκ hε hε1
  refine ⟨Tc, A, hM, fun h => (Nat.cast_le.mpr (h.cost_le_worstCost _)).trans hM,
    fun x h1 h2 h3 hlo hhi => ?_⟩
  obtain ⟨hS, hsucc, hdens, hsym, hdist⟩ := hA x ⟨h1, h2, h3⟩ hlo hhi
  exact ⟨hS, fun h => (Nat.cast_le.mpr (h.cost_le_worstCost _)).trans hS, hsucc, hdens, hsym,
    hdist⟩

end

end ManuscriptConformance
