import SparseHamiltonian.AmplificationCircuit

/-!
# Full-output error from the amplification overlap

The public input and circuit-output Hilbert spaces are independently typed.
This module derives the squared operator-norm error from the overlap of two
isometries, then applies the noncommutative amplification residual estimate.
The final theorem constructs the overlap from the explicit reflection circuit.
Constructing the sparse-oracle LCU with the specified input block remains a
separate obligation.
-/

namespace SparseHamiltonian

open ContinuousLinearMap
open scoped InnerProduct

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Factoring the target isometry out of the cubic amplification polynomial.
Only the left-unitary identity is needed for this algebraic step. -/
theorem amplification_factored_overlap (U E X : P →L[ℂ] P)
    (hU : star U * U = 1)
    (hBlock : (2 : ℂ) • X = U * (1 + E)) :
    (2 : ℂ) • (star U * ((3 : ℂ) • X - (4 : ℂ) • (X * star X * X))) =
      amplificationPolynomialTwice E := by
  have hX : X = (2 : ℂ)⁻¹ • (U * (1 + E)) := by
    rw [← hBlock, inv_smul_smul₀ (by norm_num : (2 : ℂ) ≠ 0)]
  have hCancel (Y : P →L[ℂ] P) : star U * (U * Y) = Y := by
    rw [← mul_assoc, hU, one_mul]
  rw [hX]
  simp only [star_smul, star_mul, smul_mul_assoc,
    mul_smul_comm, mul_sub, smul_sub, smul_smul, mul_assoc, hCancel]
  norm_num [amplificationPolynomialTwice, smul_add, add_smul]
  rw [show (3 : ℂ) = 1 + 1 + 1 by norm_num]
  simp only [add_smul, one_smul]
  noncomm_ring

/-- The Gram operator of the difference of two isometries. -/
theorem isometry_difference_gram (V W : P →L[ℂ] K)
    (hV : V† ∘L V = 1) (hW : W† ∘L W = 1) :
    (V - W)† ∘L (V - W) =
      (1 + 1 : P →L[ℂ] P) - W† ∘L V - V† ∘L W := by
  rw [map_sub, sub_comp, comp_sub, comp_sub, hV, hW]
  abel

/-- An amplified overlap gives the exact doubled squared-error operator. -/
theorem amplification_isometry_residual (V W : P →L[ℂ] K)
    (E : P →L[ℂ] P)
    (hV : V† ∘L V = 1) (hW : W† ∘L W = 1)
    (hOverlap : (2 : ℂ) • (W† ∘L V) = amplificationPolynomialTwice E) :
    (2 : ℂ) • ((V - W)† ∘L (V - W)) = amplificationResidualTwice E := by
  have hOverlapAdj : (2 : ℂ) • (V† ∘L W) =
      star (amplificationPolynomialTwice E) := by
    have h := congrArg star hOverlap
    simpa only [star_smul, star_ofNat, star_eq_adjoint, adjoint_comp,
      adjoint_adjoint] using h
  rw [isometry_difference_gram V W hV hW, smul_sub, smul_sub,
    hOverlap, hOverlapAdj, amplificationResidualTwice]
  simp only [smul_add, two_smul]
  abel

/-- The amplification overlap controls the genuine full-output operator norm.
There is no loss of a square root in the block-error parameter. -/
theorem amplification_isometry_error_le (V W : P →L[ℂ] K)
    (E : P →L[ℂ] P) {δ : ℝ}
    (hV : V† ∘L V = 1) (hW : W† ∘L W = 1)
    (hOverlap : (2 : ℂ) • (W† ∘L V) = amplificationPolynomialTwice E)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hE : ‖E‖ ≤ δ) :
    ‖V - W‖ ≤ 2 * δ := by
  have hResidual := amplification_residual_norm_le hδ hE
  rw [← amplification_isometry_residual V W E hV hW hOverlap,
    norm_smul, norm_adjoint_comp_self] at hResidual
  have hTwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hTwo] at hResidual
  apply amplification_error_le hδ hδ1
  nlinarith

/-- One explicit reflection-based amplification round has full-output error
at most twice the normalized public-block error. The input LCU is represented
by an isometry `T`; its successful block is specified by `hBlock`. -/
theorem reflectedAmplification_error_le (J T : P →L[ℂ] K)
    (U E : P →L[ℂ] P) {δ : ℝ}
    (hJ : J† ∘L J = 1) (hT : T† ∘L T = 1)
    (hU : star U * U = 1)
    (hBlock : (2 : ℂ) • (J† ∘L T) = U * (1 + E))
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hE : ‖E‖ ≤ δ) :
    ‖reflectedAmplification J T - J ∘L U‖ ≤ 2 * δ := by
  have hTarget : (J ∘L U)† ∘L (J ∘L U) = 1 := by
    rw [adjoint_comp, comp_assoc, ← comp_assoc (J†) J U, hJ, one_def, id_comp]
    exact hU
  have hOverlap : (2 : ℂ) • ((J ∘L U)† ∘L reflectedAmplification J T) =
      amplificationPolynomialTwice E := by
    rw [adjoint_comp, comp_assoc, reflectedAmplification_compression J T hJ hT]
    exact amplification_factored_overlap U E (J† ∘L T) hU hBlock
  exact amplification_isometry_error_le _ _ E
    (reflectedAmplification_isometry J T hJ hT) hTarget hOverlap hδ hδ1 hE

/-- The amplification theorem stated directly in terms of the successful-block
error. It controls the entire output, including the component outside the
clean subspace. -/
theorem reflectedAmplification_error_of_block_error (J T : P →L[ℂ] K)
    (U : P →L[ℂ] P) {δ : ℝ}
    (hJ : J† ∘L J = 1) (hT : T† ∘L T = 1)
    (hU : star U * U = 1) (hUU : U * star U = 1)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hBlockError : ‖(2 : ℂ) • (J† ∘L T) - U‖ ≤ δ) :
    ‖reflectedAmplification J T - J ∘L U‖ ≤ 2 * δ := by
  let E := star U * ((2 : ℂ) • (J† ∘L T) - U)
  have hUnorm : ‖U‖ ≤ 1 := by
    apply opNorm_le_bound U (by norm_num)
    intro x
    have hx := (norm_map_iff_adjoint_comp_self U).mpr hU x
    simpa only [one_mul] using hx.le
  have hE : ‖E‖ ≤ δ := by
    have hAdj : ‖star U‖ ≤ 1 := by
      rw [star_eq_adjoint, LinearIsometryEquiv.norm_map]
      exact hUnorm
    calc
      ‖E‖ ≤ ‖star U‖ * ‖(2 : ℂ) • (J† ∘L T) - U‖ := norm_mul_le _ _
      _ ≤ 1 * δ := mul_le_mul hAdj hBlockError (norm_nonneg _) (by norm_num)
      _ = δ := one_mul δ
  have hBlock : (2 : ℂ) • (J† ∘L T) = U * (1 + E) := by
    dsimp [E]
    rw [mul_add, mul_one, ← mul_assoc, hUU, one_mul]
    abel
  exact reflectedAmplification_error_le J T U E hJ hT hU hBlock hδ hδ1 hE

end SparseHamiltonian
