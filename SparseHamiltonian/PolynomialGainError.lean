import SparseHamiltonian.NativeSparseFailureOrthogonality

/-!
# Relative polynomial gains, including zero success

The gain at a zero signal is assigned the target value. This is an analytical
choice, not an operation performed by the circuit: its good component is zero.
Scalar relative approximation then bounds an actual diagonal perturbation.
-/

namespace SparseHamiltonian.PolynomialGainError

noncomputable section
open ContinuousLinearMap RelativeAmplitudeError ComplexAmplitudeRotation
open scoped InnerProduct

/-- Analytical gain; the zero-signal convention avoids an artificial error. -/
def gain (target : ℂ) (P : Polynomial ℂ) (x : ℝ) : ℂ :=
  if x = 0 then target else P.eval (x : ℂ) / (x : ℂ)

theorem gain_mul (target : ℂ) (P : Polynomial ℂ) (hP : P.eval 0 = 0) (x : ℝ) :
    gain target P x * (x : ℂ) = P.eval (x : ℂ) := by
  by_cases hx : x = 0
  · simp [gain, hx, hP]
  · simp [gain, hx, Complex.ofReal_ne_zero.mpr hx]

theorem gain_sub (target : ℂ) (P : Polynomial ℂ) (x : ℝ) (hx : x ≠ 0) :
    gain target P x - target = (P.eval (x : ℂ) - target * (x : ℂ)) / (x : ℂ) := by
  simp only [gain, if_neg hx]
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  field_simp

/-- Absolute gain error follows from relative error in the small signal. -/
theorem norm_gain_sub_le (target : ℂ) (P : Polynomial ℂ) (x δ : ℝ)
    (hδ : 0 ≤ δ)
    (herr : ‖P.eval (x : ℂ) - target * (x : ℂ)‖ ≤ δ * |x|) :
    ‖gain target P x - target‖ ≤ δ := by
  by_cases hx : x = 0
  · simpa [gain, hx] using hδ
  · rw [gain_sub target P x hx, norm_div, Complex.norm_real, Real.norm_eq_abs]
    exact (div_le_iff₀ (abs_pos.mpr hx)).mpr herr

/-- The perturbation is relative to the desired, nonzero amplification. -/
def relativeError (target : ℂ) (P : Polynomial ℂ) (x : ℝ) : ℂ :=
  gain target P x / target - 1

theorem relativeError_eq (target : ℂ) (ht : target ≠ 0) (P : Polynomial ℂ) (x : ℝ) :
    relativeError target P x = (gain target P x - target) / target := by
  unfold relativeError
  field_simp

theorem gain_eq (target : ℂ) (ht : target ≠ 0) (P : Polynomial ℂ) (x : ℝ) :
    gain target P x = target * (1 + relativeError target P x) := by
  unfold relativeError
  field_simp
  ring

/-- Relative multiplier error is uniform even at a zero success probability. -/
theorem norm_relativeError_le (target : ℂ) (ht : target ≠ 0)
    (P : Polynomial ℂ) (x δ : ℝ) (hδ : 0 ≤ δ)
    (herr : ‖P.eval (x : ℂ) - target * (x : ℂ)‖ ≤ (δ * ‖target‖) * |x|) :
    ‖relativeError target P x‖ ≤ δ := by
  rw [relativeError_eq target ht P x, norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr ht)).mpr
  exact norm_gain_sub_le target P x (δ * ‖target‖) (mul_nonneg hδ (norm_nonneg _)) herr

section Coordinates
variable {n : Type*} [Fintype n]

/-- A simultaneous scalar approximation controls the full diagonal operator. -/
theorem norm_relativeDiagonal_le (target : ℂ) (ht : target ≠ 0)
    (P : Polynomial ℂ) (x : n → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (herr : ∀ i, ‖P.eval (x i : ℂ) - target * (x i : ℂ)‖ ≤
      (δ * ‖target‖) * |x i|) :
    ‖complexDiagonal (fun i => relativeError target P (x i))‖ ≤ δ :=
  norm_complexDiagonal_le _ δ hδ (fun i =>
    norm_relativeError_le target ht P (x i) δ hδ (herr i))

/-- The actual gain operator has the desired scalar times a small perturbation. -/
theorem gainDiagonal_eq (target : ℂ) (ht : target ≠ 0)
    (P : Polynomial ℂ) (x : n → ℝ) :
    complexDiagonal (fun i => gain target P (x i)) =
      target • (1 + complexDiagonal (fun i => relativeError target P (x i))) := by
  ext v i
  simp only [complexDiagonal_apply, smul_apply, PiLp.smul_apply, smul_eq_mul,
    one_add_complexDiagonal_apply, gain_eq target ht P]
  ring

end Coordinates

section Output
variable {E K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Full polynomial output separates an analytical good gain and a bad gain.
Both zero and unit success are included without a nonzero-amplitude premise. -/
theorem column_decomposition (R : E →L[ℂ] K) (hR : R† ∘L R = 1)
    (Q : K →L[ℂ] K) (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q)
    (e : E) (x : ℝ) (hx : |x| ≤ 1)
    (he : (R†) (Q (R e)) = (x : ℂ) ^ 2 • e)
    (target : ℂ) (P B : Polynomial ℂ) (hP : P.eval 0 = 0) :
    PreparationInvariantPlane.plane (PreparationInvariantPlane.goodDirection R Q e x)
      (PreparationInvariantPlane.badDirection R Q e x)
      (AmplitudePolynomialSequence.column x P B) =
      gain target P x • Q (R e) + B.eval (x : ℂ) • ((1 - Q) (R e)) := by
  rw [← PreparationInvariantPlane.good_scale R Q hQ e x he,
    ← PreparationInvariantPlane.bad_scale R hR Q hQ e x hx he]
  simp only [PreparationInvariantPlane.plane_apply, AmplitudePolynomialSequence.column_false,
    AmplitudePolynomialSequence.column_true, smul_smul, gain_mul target P hP x]
  rw [mul_comm (badAmplitude (x : ℂ) : ℂ)]

end Output

section CompleteMap
variable {n K : Type*} [Fintype n] [DecidableEq n]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [Fintype n] in
/-- Coordinate gains act diagonally on the original label basis. -/
theorem diagonal_basis (d : n → ℂ) (i : n) :
    complexDiagonal d (EuclideanSpace.single i 1) = d i • EuclideanSpace.single i 1 := by
  ext j
  by_cases hij : i = j
  · subst j; simp
  · simp [hij]

/-- Basiswise polynomial action determines the entire prepared linear map. -/
theorem map_decomposition (M R : EuclideanSpace ℂ n →L[ℂ] K)
    (hR : R† ∘L R = 1) (Q : K →L[ℂ] K)
    (hQ : PhaseSubspaceGates.IsOrthogonalProjection Q)
    (x : n → ℝ) (hx : ∀ i, |x i| ≤ 1)
    (he : ∀ i, (R†) (Q (R (EuclideanSpace.single i 1))) =
      (x i : ℂ) ^ 2 • EuclideanSpace.single i 1)
    (target : ℂ) (P B : Polynomial ℂ) (hP : P.eval 0 = 0)
    (hM : ∀ i, M (EuclideanSpace.single i 1) =
      PreparationInvariantPlane.plane
        (PreparationInvariantPlane.goodDirection R Q (EuclideanSpace.single i 1) (x i))
        (PreparationInvariantPlane.badDirection R Q (EuclideanSpace.single i 1) (x i))
        (AmplitudePolynomialSequence.column (x i) P B)) :
    M = Q ∘L R ∘L complexDiagonal (fun i => gain target P (x i)) +
      (1 - Q) ∘L R ∘L complexDiagonal (fun i => B.eval (x i : ℂ)) := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun n ℂ).toBasis.ext
  intro i
  change M ((EuclideanSpace.basisFun n ℂ) i) =
    ((Q ∘L R ∘L complexDiagonal (fun i => gain target P (x i)) +
      (1 - Q) ∘L R ∘L complexDiagonal (fun i => B.eval (x i : ℂ))) :
        EuclideanSpace ℂ n →L[ℂ] K)
      ((EuclideanSpace.basisFun n ℂ) i)
  simp only [EuclideanSpace.basisFun_apply]
  rw [hM, column_decomposition R hR Q hQ (EuclideanSpace.single i 1)
    (x i) (hx i) (he i) target P B hP]
  simp only [add_apply, comp_apply, diagonal_basis, map_smul]

end CompleteMap
end
end SparseHamiltonian.PolynomialGainError
