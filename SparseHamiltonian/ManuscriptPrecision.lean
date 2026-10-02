import SparseHamiltonian.ImprovedSparseHamiltonian

/-!
# Sparse Hamiltonian simulation in the manuscript precision convention

For `0 < ε ≤ 1 / 2`, the primitive-query bounds are expressed using
`log (1 / ε)`. The circuits, their clean encodings, and their error guarantees
are exactly those of `ImprovedSparseHamiltonian`; only the absolute query
constant changes.
-/

namespace SparseHamiltonian.ManuscriptPrecision

noncomputable section

/-- On the manuscript precision range, adding `log 2` increases the logarithm
by at most a factor of two. -/
theorem log_two_le_twice_log_one (ε : ℝ) (hε : 0 < ε)
    (hεHalf : ε ≤ 1 / 2) :
    Real.log (2 / ε) ≤ 2 * Real.log (1 / ε) := by
  have harg : (2 : ℝ) ≤ 1 / ε := by
    apply (le_div_iff₀ hε).mpr
    linarith
  have hlog2 : Real.log 2 ≤ Real.log (1 / ε) :=
    Real.log_le_log (by norm_num) harg
  have hsplit : Real.log (2 / ε) = Real.log 2 + Real.log (1 / ε) := by
    rw [show (2 : ℝ) / ε = 2 * (1 / ε) by ring,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (ne_of_gt (by positivity : (0 : ℝ) < 1 / ε))]
  linarith

/-- The full three-term primitive-query expression changes by at most two,
including its mixed square-root term and the zero-time case. -/
theorem query_shape_log_two_le (s τ ε : ℝ) (hs : 0 ≤ s) (hτ : 0 ≤ τ)
    (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) :
    Real.sqrt s * τ + Real.sqrt (s * τ * Real.log (2 / ε)) + Real.log (2 / ε) ≤
      2 * (Real.sqrt s * τ + Real.sqrt (s * τ * Real.log (1 / ε)) +
        Real.log (1 / ε)) := by
  have hargOne : (1 : ℝ) ≤ 1 / ε := by
    apply (le_div_iff₀ hε).mpr
    linarith
  have hargTwo : (1 : ℝ) ≤ 2 / ε := by
    apply (le_div_iff₀ hε).mpr
    linarith
  have hL := Real.log_nonneg hargOne
  have hB := Real.log_nonneg hargTwo
  have hBL := log_two_le_twice_log_one ε hε hεHalf
  have hprod := mul_le_mul_of_nonneg_left hBL (mul_nonneg hs hτ)
  have hsqB := Real.sq_sqrt (mul_nonneg (mul_nonneg hs hτ) hB)
  have hsqL := Real.sq_sqrt (mul_nonneg (mul_nonneg hs hτ) hL)
  have hrootB := Real.sqrt_nonneg (s * τ * Real.log (2 / ε))
  have hrootL := Real.sqrt_nonneg (s * τ * Real.log (1 / ε))
  have hroot : Real.sqrt (s * τ * Real.log (2 / ε)) ≤
      2 * Real.sqrt (s * τ * Real.log (1 / ε)) := by
    apply (sq_le_sq₀ hrootB (mul_nonneg (by norm_num) hrootL)).mp
    nlinarith [sq_nonneg (Real.sqrt (s * τ * Real.log (1 / ε)))]
  have htime := mul_nonneg (Real.sqrt_nonneg s) hτ
  linarith

/-- Transfer an explicit query count to the manuscript logarithm while
retaining the same circuit and the same precision parameter. -/
theorem query_count_log_one (q s τ ε : ℝ) (hs : 0 ≤ s) (hτ : 0 ≤ τ)
    (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hq : q ≤ 497664 *
      (Real.sqrt s * τ + Real.sqrt (s * τ * Real.log (2 / ε)) + Real.log (2 / ε))) :
    q ≤ 995328 *
      (Real.sqrt s * τ + Real.sqrt (s * τ * Real.log (1 / ε)) + Real.log (1 / ε)) := by
  have hshape := query_shape_log_two_le s τ ε hs hτ hε hεHalf
  linarith

end
end SparseHamiltonian.ManuscriptPrecision

namespace SparseHamiltonian.ImprovedSparseHamiltonian

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 3000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- The manuscript primitive sparse-query theorem, with `log (1 / ε)` and
`0 < ε ≤ 1 / 2`. This uses the actual simulation circuit and common clean
encoding of `simulation`, with no change to the error guarantee or oracle model. -/
theorem simulation_log_one (D : Data X n Z s) (η t ε : ℝ)
    (hη : 0 < η) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (K := Physical n Z s γ η t ε) (oracle D γ η t ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * |t|) +
            Real.sqrt ((s : ℝ) * (η * |t|) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D γ η t ε)† ∘L input D γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L input D γ η t ε - input D γ η t ε ∘L
            NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAction⟩ :=
    simulation D η t ε hη hε (by linarith) hH hrow hcol
  refine ⟨γ, hγ, hγOne, hWidth, p, ?_, hIn, hAction⟩
  exact ManuscriptPrecision.query_count_log_one (p.count : ℝ) (s : ℝ)
    (η * |t|) ε (Nat.cast_nonneg s) (mul_nonneg hη.le (abs_nonneg t))
    hε hεHalf hCount

/-- The manuscript precision form under a Hermitian spectral-norm promise.
Both energy promises are derived from that spectral-norm bound. -/
theorem simulation_spectral_log_one (D : Data X n Z s) (η t ε : ℝ)
    (hη : 0 < η) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hNorm : ∀ x, ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ η) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (K := Physical n Z s γ η t ε) (oracle D γ η t ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * |t|) +
            Real.sqrt ((s : ℝ) * (η * |t|) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D γ η t ε)† ∘L input D γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L input D γ η t ε - input D γ η t ε ∘L
            NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε :=
  simulation_log_one D η t ε hη hε hεHalf hH
    (SparseSpectralEnergy.native_energies D η hH hNorm).1
    (SparseSpectralEnergy.native_energies D η hH hNorm).2

/-- The manuscript precision form for arbitrary normalized entangled inputs.
The reference is untouched, and its dimension does not enter the query bound. -/
theorem simulation_with_reference_log_one {R : Type*} [Fintype R]
    (D : Data X n Z s) (η t ε : ℝ)
    (hη : 0 < η) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (K := Physical n Z s γ η t ε) (oracle D γ η t ε),
        (p.count : ℝ) ≤ 995328 *
          (Real.sqrt (s : ℝ) * (η * |t|) +
            Real.sqrt ((s : ℝ) * (η * |t|) * Real.log (1 / ε)) + Real.log (1 / ε)) ∧
        (input D γ η t ε)† ∘L input D γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ∀ ψ : PiLp 2 (fun _ : R => EuclideanSpace ℂ n), ‖ψ‖ = 1 →
            ‖FiniteReferenceLift.lift (p.eval x)
                (FiniteReferenceLift.lift (input D γ η t ε) ψ) -
              FiniteReferenceLift.lift (input D γ η t ε)
                (FiniteReferenceLift.lift (NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                  SparseStateOverlap.matrixOperator (D.matrix x))) ψ)‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hAction⟩ :=
    simulation_log_one D η t ε hη hε hεHalf hH hrow hcol
  refine ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, fun x => ⟨(hAction x).1, ?_⟩⟩
  intro ψ hψ
  simpa only [hψ, mul_one] using
    reference_error D γ η t ε p (fun x => (hAction x).2) x ψ

end
end SparseHamiltonian.ImprovedSparseHamiltonian
