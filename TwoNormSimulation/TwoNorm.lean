import TwoNormSimulation.Bounded
import TwoNormSimulation.Regimes
import LargeSparsityCore.NativeTwoNormCore

set_option autoImplicit false

/-!
# Theorem `hs:thm:two-norm`

Appendix B: with a supplied entry bound `‖H‖_max ≤ μ` and row and column
Euclidean norms at most `η`, `μ ≤ η ≤ √s μ` (`hs:eq:two-norm-promises`), `θ = η²|t|/μ ≥ 1`,
`0 < ε ≤ 1/64`, `L = log(1/ε)`, `h_μ = log(e + L/θ)` and `r_μ = L/h_μ`
(`hs:eq:two-norm-parameters`), the evolution `e^{-itH}` is simulated with full-output error at
most `ε` using `O(√s η|t| + √(sμ|t| r_μ) + r_μ)` native queries (`hs:eq:two-norm-bound`), here with
the explicit constant `2·10¹²`. With `σ = sμ²/η²` (`hs:eq:two-norm-rescaling`),
`√σ θ = √s η|t|` and `σθ = sμ|t|`. The three regimes of the proof of Theorem `hs:thm:two-norm`:

* `h_μ < 10⁴`: the baseline Cayley simulation with the moment parameter `σ`
  (`bounded_simulation`, `bounded_shape_le`);
* `h_μ ≥ 10⁴` and `σθ ≥ L h_μ`: the large-sparsity core at entry scale `μ`
  (`LargeSparsityCore.Native.core_simulation_two`);
* `h_μ ≥ 10⁴` and `σθ < L h_μ`: the native signed factor with entry scale `κ = μ`, `T = sμ|t|`
  and `b = √s η|t|` (`NativeSignedFactor.native_signed_simulation`), with the comparison
  `OptimalSparseSimulation.signed_bound` at `(σ, θ)`.

* `two_norm_simulation`: the theorem in the common form `Simulates (physOracle D)`.
* `two_norm_simulation_with_reference`: inputs entangled with an untouched finite reference.
-/

namespace TwoNormSimulation

noncomputable section

open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open LargeSparsityCore.Parameters SignedFactorSimulation OptimalSparseSimulation
open scoped InnerProduct
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096

variable {X : Type*} {n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

/-- The query bound of Theorem `hs:thm:two-norm`: `2·10¹² (√s η|t| + √(sμ|t| r_μ) + r_μ)` with
`r_μ = L/log(e + L/θ)` and `θ = η²|t|/μ`. -/
def bound (s : ℕ) (η μ t ε : ℝ) : ℝ :=
  2 * 10 ^ 12 * (Real.sqrt s * η * |t| + Real.sqrt (s * μ * |t| * rb (thetaT η μ t) ε) +
    rb (thetaT η μ t) ε)

theorem sigma_mul_theta (s : ℕ) {η μ : ℝ} (hη : 0 < η) (hμ : 0 < μ) (t : ℝ) :
    sigma s η μ * thetaT η μ t = s * μ * |t| := by
  unfold sigma thetaT
  field_simp

theorem sqrt_sigma_mul_theta (s : ℕ) {η μ : ℝ} (hη : 0 < η) (hμ : 0 < μ) (t : ℝ) :
    Real.sqrt (sigma s η μ) * thetaT η μ t = Real.sqrt s * η * |t| := by
  rw [sqrt_sigma s hη hμ.le]
  unfold thetaT
  field_simp

theorem sigma_eq (s : ℕ) {η μ : ℝ} (hη : 0 < η) :
    (s : ℝ) * μ ^ 2 = sigma s η μ * η ^ 2 := by
  unfold sigma
  field_simp

set_option maxHeartbeats 4000000 in
/-- **Theorem `hs:thm:two-norm`** (`hs:eq:two-norm-bound`). Let `H = D.matrix x` be Hermitian with
row and column Euclidean norms at most `η` and entries of modulus at most `μ`, `μ ≤ η ≤ √s μ`, and
let `t` be a real time with `θ = η²|t|/μ ≥ 1` and `0 < ε ≤ 1/64`. Then `e^{-itH}` is simulated in
the common form `Simulates (physOracle D)`: one known isometric input, one program whose only
oracle calls are the original native primitives with spectator registers, unitary for every
instance, with full-output error at most `ε` and at most
`2·10¹² (√s η|t| + √(sμ|t| r_μ) + r_μ)` calls, `r_μ = L/log(e + L/θ)`, `L = log(1/ε)`. -/
theorem two_norm_simulation (D : Data X n Z s) {η μ t ε : ℝ} (hμη : μ ≤ η)
    (hηs : η ≤ Real.sqrt s * μ) (hθ : 1 ≤ η ^ 2 * |t| / μ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hent : ∀ x i j, ‖D.matrix x i j‖ ≤ μ) :
    NativeSignedFactor.Simulates (NativeSignedFactor.physOracle D)
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x)) t ε (bound s η μ t ε) := by
  have hμ : 0 < μ := by
    by_contra h
    have h' : μ ≤ 0 := not_lt.mp h
    have : η ^ 2 * |t| / μ ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg η) (abs_nonneg t)) h'
    linarith
  have hη : 0 < η := lt_of_lt_of_le hμ hμη
  have hs : 1 ≤ s := D.slots_pos
  have hσ1 := one_le_sigma s hη hηs
  have hθ' : 1 ≤ thetaT η μ t := hθ
  have hr := r_pos hθ' hε hε1
  have hsθ : (0 : ℝ) ≤ s * μ * |t| := by positivity
  have hsθr := Real.sqrt_nonneg (s * μ * |t| * rval (thetaT η μ t) ε)
  have hb0 : 0 ≤ Real.sqrt s * η * |t| := by positivity
  have hB : bound s η μ t ε = 2 * 10 ^ 12 * (Real.sqrt s * η * |t| +
      Real.sqrt (s * μ * |t| * rval (thetaT η μ t) ε) + rval (thetaT η μ t) ε) := rfl
  have hST := sigma_mul_theta s hη hμ t
  have hSqT := sqrt_sigma_mul_theta s hη hμ t
  by_cases h1 : hval (thetaT η μ t) ε < 10 ^ 4
  · -- bounded `h_μ`: the baseline Cayley simulation with moment parameter `σ`
    refine (bounded_simulation D hμ hμη hηs hH hrow hcol hent hε (by linarith)).mono ?_
    have hsh := bounded_shape_le (by linarith : (0 : ℝ) ≤ sigma s η μ) hθ' hε hε1 h1
    rw [hSqT, hST] at hsh
    rw [hB]
    nlinarith
  · replace h1 : 10 ^ 4 ≤ hval (thetaT η μ t) ε := not_lt.mp h1
    by_cases h2 : Lval ε * hval (thetaT η μ t) ε ≤ sigma s η μ * thetaT η μ t
    · -- large `h_μ` and `σθ ≥ L h_μ`: the large-sparsity core at entry scale `μ`
      have R : Regime (sigma s η μ) (η ^ 2 * |t| / μ) ε := ⟨hσ1, hθ, hε, hε1, h1, h2⟩
      obtain ⟨hinp, p, hcount, hp⟩ :=
        LargeSparsityCore.Native.core_simulation_two D hμ hη (sigma_eq s hη) R hH
          (fun x => ⟨hrow x, hcol x⟩) hent
      refine simulates_of_spectatorForm (cayleyActive_form D _ _) _ t ε _ _ hinp p ?_ hp
      have hc : (p.count : ℝ) ≤ 6972480 * Real.sqrt (s * μ * |t| * rval (thetaT η μ t) ε) := by
        have h := hcount
        change (p.count : ℝ) ≤ 6972480 * Real.sqrt (sigma s η μ * thetaT η μ t *
          rval (thetaT η μ t) ε) at h
        rw [hST] at h
        exact h
      rw [hB]
      nlinarith
    · -- large `h_μ` and `σθ < L h_μ`: the native signed factor with entry scale `μ`
      replace h2 : sigma s η μ * thetaT η μ t < Lval ε * hval (thetaT η μ t) ε := not_le.mp h2
      refine (NativeSignedFactor.native_signed_simulation D hμ hη hηs hH hent hrow hcol t hε
        hε1).mono ?_
      have hsb := OptimalSparseSimulation.signed_bound hσ1 hθ' hε hε1 h1 h2
      rw [hSqT, hST] at hsb
      rw [hB]
      split_ifs
      · positivity
      · nlinarith

/-- **Theorem `hs:thm:two-norm` with an untouched reference.** The circuit of
`two_norm_simulation` keeps its full-output error on normalised inputs entangled with an arbitrary
finite reference register `R`; the reference does not enter the query bound. -/
theorem two_norm_simulation_with_reference {R : Type*} [Fintype R] (D : Data X n Z s)
    {η μ t ε : ℝ} (hμη : μ ≤ η) (hηs : η ≤ Real.sqrt s * μ) (hθ : 1 ≤ η ^ 2 * |t| / μ)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hent : ∀ x i j, ‖D.matrix x i j‖ ≤ μ) :
    ∃ (ι : Type) (_ : Fintype ι)
      (inp : EuclideanSpace ℂ n →L[ℂ] PiLp 2 (fun _ : ι => NativeSignedFactor.Phys n Z))
      (p : MultiOracleCircuit.Program
        (CoherentQuerySchedule.oracle (ι := ι) (NativeSignedFactor.physOracle D))),
      inp† ∘L inp = 1 ∧ (p.count : ℝ) ≤ bound s η μ t ε ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ∀ ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n), ‖ψ‖ = 1 →
          ‖FiniteReferenceLift.lift (p.eval x) (FiniteReferenceLift.lift inp ψ) -
            FiniteReferenceLift.lift inp (FiniteReferenceLift.lift (NormedSpace.exp
              ((-Complex.I * (t : ℂ)) • SparseStateOverlap.matrixOperator (D.matrix x))) ψ)‖ ≤
            ε := by
  obtain ⟨ι, hι, inp, p, hinp, hcount, hp⟩ :=
    two_norm_simulation D hμη hηs hθ hε hε1 hH hrow hcol hent
  refine ⟨ι, hι, inp, p, hinp, hcount, fun x => ⟨(hp x).1, fun ψ hψ => ?_⟩⟩
  simpa only [hψ, mul_one] using
    FiniteReferenceLift.same_embedding_error_le (p.eval x) inp _ ε (hp x).2 ψ

end

end TwoNormSimulation
