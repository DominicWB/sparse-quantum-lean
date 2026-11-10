import ManuscriptConformance.Defs
import ManuscriptConformance.Readout
import QLSHoeffding.Main
import ChebyshevFilter.Proposition

/-!
# Conformance: the linear-system algorithm and the positive Chebyshev filter

Theorem `qls:thm:main` and Proposition `qls:prop:chebyshev`.

`qls:thm:main`, in the manuscript's model:

* **Input.** Native sparse data `D` for `A` (value oracle and in-place row and column locators,
  inverses included, `s ≥ 1` slots), with the promise `‖A‖ ≤ 1`, `A` invertible,
  `‖A⁻¹‖ ≤ κ`, `κ ≥ 1`; a preparation unitary `U_b` with `U_b |0⟩ = |b⟩` (`Ub x sv`, `sv` the
  known seed `|0⟩`), with its inverse and control.
* **Algorithm.** One adaptive protocol (`SparseLinearSystems.Protocol.Tree`: fresh measured runs
  with classical branching, then bounded fresh-trial preparations) over the physical oracle
  family (`SparseLinearSystems.Step.physOracle`: the three sparse primitives and the controlled
  source), fixed before the instance.
* **Guarantee.** Success probability at least `2/3`, and conditional on success a density
  operator within trace distance `ε` of `|x⟩ = A⁻¹|b⟩/‖A⁻¹b‖`.
* **Cost.** Worst case over all transcripts: matrix queries (`wMat`) and calls of `U_b`, `U_b†`
  (`wSrc`).
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
/-- **Theorem `qls:thm:main`** (eq. `qls:eq:main`). For native sparse data `D` with `s ≥ 1` slots, a
unitary preparation `U_b`, `κ ≥ 1` and `0 < ε ≤ 1/10`, one protocol, fixed before the instance, on
every input satisfying `‖A‖ ≤ 1`, `A` invertible, `‖A⁻¹‖ ≤ κ`, succeeds with probability at least
`2/3` and has conditional output a density operator within trace distance `ε` of `A⁻¹|b⟩/‖A⁻¹b‖`,
using in the worst case at most `C √s κ log(1/ε)` matrix queries and at most as many calls of `U_b`,
`U_b†`, with the absolute constant `C = 3.4·10⁹` and no hidden logarithm of `s` or `κ`. Formal
restrictions: none. -/
theorem qls_thm_main :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : NativeSparseBlockEncoding.Data X n Z s)
        (Ub : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n), (∀ x, IsUnitary (Ub x)) →
        ∀ sv : EuclideanSpace ℂ n, ‖sv‖ = 1 →
        ∀ κ ε : ℝ, 1 ≤ κ → 0 < ε → ε ≤ 1 / 10 →
        ∃ (Tc : ℕ) (A : SparseLinearSystems.Protocol.Tree
            (SparseLinearSystems.Step.physOracle D Ub Tc) (SparseLinearSystems.LogicalWalk.PrivO n)
            (EuclideanSpace ℂ n)),
          (A.worstCost SparseLinearSystems.Step.wMat : ℝ) ≤ C * Real.sqrt s * κ * Real.log (1 / ε) ∧
          (A.worstCost SparseLinearSystems.Step.wSrc : ℝ) ≤ C * Real.sqrt s * κ * Real.log (1 / ε) ∧
          ∀ x : X,
            ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ 1 →
            IsUnit (SparseStateOverlap.matrixOperator (D.matrix x)) →
            ‖Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ κ →
            2 / 3 ≤ A.successMass x ∧ ODEMixedOutput.IsDensity (A.conditionalDensity x) ∧
              TraceDistanceLE (A.conditionalDensity x)
                (ODEStateNormalization.unitDirection
                  (Ring.inverse (SparseStateOverlap.matrixOperator (D.matrix x)) (Ub x sv))) ε := by
  refine ⟨34 * 10 ^ 8, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ s D Ub hUb sv hsv κ ε hκ hε hε1
  obtain ⟨Tc, A, hM, hS, hA⟩ := QLSHoeffding.main_exactH_exists D Ub hUb sv hsv κ ε hκ hε hε1
  refine ⟨Tc, A, hM, hS.trans ?_, fun x h1 h2 h3 => ?_⟩
  · have hL : 0 ≤ Real.log (1 / ε) :=
      Real.log_nonneg (by rw [le_div_iff₀ hε]; linarith)
    have : 0 ≤ Real.sqrt s * κ * Real.log (1 / ε) := by
      have : (0 : ℝ) ≤ κ := by linarith
      positivity
    nlinarith
  · obtain ⟨-, hsucc, hdens, hsym, hdist⟩ := hA x ⟨h1, h2, h3⟩
    exact ⟨hsucc, hdens, hsym, hdist⟩

/-- **Eq. `qls:eq:chebfilter`**: `T_d((1 + λ) cos θ + λ)/T_d(1 + 2λ)`, `λ = b²/(1 - b²)`, is
`T_d((cos θ + b²)/(1 - b²))/T_d((1 + b²)/(1 - b²))`. -/
theorem filterFun_eq {b : ℝ} (hb : b ^ 2 < 1) (d : ℕ) (θ : ℝ) :
    ChebyshevFilter.filterFun b d θ =
      (Polynomial.Chebyshev.T ℝ d).eval ((Real.cos θ + b ^ 2) / (1 - b ^ 2)) /
        (Polynomial.Chebyshev.T ℝ d).eval ((1 + b ^ 2) / (1 - b ^ 2)) := by
  have h : (1 : ℝ) - b ^ 2 ≠ 0 := by linarith
  unfold ChebyshevFilter.filterFun ChebyshevFilter.filterVal ChebyshevFilter.filterNorm
    ChebyshevFilter.lam
  congr 2
  · field_simp
    ring
  · field_simp
    ring

/-- **Proposition `qls:prop:chebyshev`**. Let `W` be unitary on a finite-dimensional Hilbert space,
`P` the projection onto its eigenvalue-one subspace, `0 < b < 1` with `|sin(θ/2)| ≥ b` for every
nonzero eigenphase `θ`, and `0 < δ < 1`; put
`d = ⌈arcosh(1/δ)/(2 artanh b)⌉`. Then `F_{b,d}(e^{iθ}) =
T_d((cos θ + b²)/(1 - b²))/T_d((1 + b²)/(1 - b²))` is a Laurent polynomial on the powers
`-d, …, d` with nonnegative coefficients summing to one, `F_{b,d}(1) = 1`,
`‖F_{b,d}(W) - P‖ ≤ δ`, and its normalisation-one LCU circuit — an isometric seed and `d` signed
walk steps — has `F_{b,d}(W)` as its selected block. Formal restrictions: none. -/
theorem qls_prop_chebyshev {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] {W : V →L[ℂ] V}
    (hW : SparseLinearSystems.UnitaryFilter.Unitary W) {b δ : ℝ} (hb0 : 0 < b) (hb1 : b < 1)
    (hphase : ∀ (θ : ℝ) (z : V), z ≠ 0 → W z = Complex.exp (θ * Complex.I) • z →
      Complex.exp (θ * Complex.I) ≠ 1 → b ≤ |Real.sin (θ / 2)|)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    let d := ⌈Real.arcosh (1 / δ) / (2 * Real.artanh b)⌉₊
    (∀ j, 0 ≤ ChebyshevFilter.filterCoeff b d j) ∧
      (∀ j ∉ Finset.Icc (-(d : ℤ)) d, ChebyshevFilter.filterCoeff b d j = 0) ∧
      ∑ j ∈ Finset.Icc (-(d : ℤ)) d, ChebyshevFilter.filterCoeff b d j = 1 ∧
      (∀ θ : ℝ, ∑ j ∈ Finset.Icc (-(d : ℤ)) d,
          ((ChebyshevFilter.filterCoeff b d j : ℝ) : ℂ) * Complex.exp ((j : ℂ) * θ * Complex.I) =
        (((Polynomial.Chebyshev.T ℝ d).eval ((Real.cos θ + b ^ 2) / (1 - b ^ 2)) /
          (Polynomial.Chebyshev.T ℝ d).eval ((1 + b ^ 2) / (1 - b ^ 2)) : ℝ) : ℂ)) ∧
      ChebyshevFilter.filterFun b d 0 = 1 ∧
      ‖ChebyshevFilter.filterOp W b d - SparseLinearSystems.UnitaryFilter.fixedProj W‖ ≤ δ ∧
      ((ChebyshevFilter.seed (V := V) b d)†) ∘L ChebyshevFilter.seed b d = 1 ∧
      ((ChebyshevFilter.seed (V := V) b d)†) ∘L
          (ChebyshevFilter.signedSteps W d d ∘L ChebyshevFilter.seed b d) =
        ChebyshevFilter.filterOp W b d := by
  intro d
  have hb2 : b ^ 2 < 1 := by nlinarith
  obtain ⟨h1, h2, h3, h4, h5, h6, -, h8, h9⟩ :=
    ChebyshevFilter.chebyshev_filter hW hb0 hb1 hphase hδ0 hδ1
  refine ⟨h1, h2, h3, fun θ => ?_, h5, h6, h8, h9⟩
  have h := h4 θ
  rw [filterFun_eq hb2] at h
  exact h

end

end ManuscriptConformance
