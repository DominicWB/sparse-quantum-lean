import SparseHamiltonian.AveragingPolynomial

/-!
# Operator-norm control of smoothed transducer errors

The public and private Hilbert spaces are independently typed. All norms in this
module are continuous-linear-map operator norms. The main estimate concerns the
explicit residual obtained from transducer cancellation; it does not assume an
error bound or assert the existence of a circuit implementing that residual.
-/

namespace SparseHamiltonian

open ContinuousLinearMap
open scoped BigOperators InnerProduct

section Contractions

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]

/-- Every nonnegative power of a contraction is a contraction, including on the
zero space, where the identity can have norm zero. -/
theorem contraction_pow_norm_le (D : Q →L[ℂ] Q) (hD : ‖D‖ ≤ 1) (k : ℕ) :
    ‖D ^ k‖ ≤ 1 := by
  induction k with
  | zero =>
      rw [pow_zero]
      exact ContinuousLinearMap.norm_id_le
  | succ k hk =>
      calc
        ‖D ^ (k + 1)‖ = ‖D ^ k * D‖ := by rw [pow_succ]
        _ ≤ ‖D ^ k‖ * ‖D‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul hk hD (norm_nonneg D) (by norm_num)
        _ = 1 := by norm_num

/-- The elementary endpoint estimate used after the smoothing cancellation. -/
theorem norm_one_sub_contraction_pow_le (D : Q →L[ℂ] Q)
    (hD : ‖D‖ ≤ 1) (d : ℕ) :
    ‖1 - D ^ d‖ ≤ 2 := by
  have hI : ‖(1 : Q →L[ℂ] Q)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  calc
    ‖1 - D ^ d‖ ≤ ‖(1 : Q →L[ℂ] Q)‖ + ‖D ^ d‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add hI (contraction_pow_norm_le D hD d)
    _ = 2 := by norm_num

/-- The normalized average of the first `L` powers. The nonzero-length premise
belongs to its norm theorem, so this definition also has an unambiguous value
at zero. -/
noncomputable def averagedGeometricFilter (D : Q →L[ℂ] Q) (L : ℕ) : Q →L[ℂ] Q :=
  (L : ℂ)⁻¹ • ∑ j ∈ Finset.range L, D ^ j

/-- Averaging powers preserves contractivity. -/
theorem averagedGeometricFilter_norm_le (D : Q →L[ℂ] Q)
    (hD : ‖D‖ ≤ 1) {L : ℕ} (hL : 1 ≤ L) :
    ‖averagedGeometricFilter D L‖ ≤ 1 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have hsum : ‖∑ j ∈ Finset.range L, D ^ j‖ ≤ (L : ℝ) := by
    calc
      ‖∑ j ∈ Finset.range L, D ^ j‖ ≤ ∑ j ∈ Finset.range L, ‖D ^ j‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j ∈ Finset.range L, (1 : ℝ) :=
        Finset.sum_le_sum fun j _hj => contraction_pow_norm_le D hD j
      _ = L := by simp
  rw [averagedGeometricFilter, norm_smul, norm_inv, Complex.norm_natCast]
  calc
    (L : ℝ)⁻¹ * ‖∑ j ∈ Finset.range L, D ^ j‖ ≤ (L : ℝ)⁻¹ * L :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hLpos.le)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hLpos)

/-- Repeating the averaged geometric filter also remains contractive. -/
theorem averagedGeometricFilter_pow_norm_le (D : Q →L[ℂ] Q)
    (hD : ‖D‖ ≤ 1) {L : ℕ} (hL : 1 ≤ L) (k : ℕ) :
    ‖averagedGeometricFilter D L ^ k‖ ≤ 1 :=
  contraction_pow_norm_le _ (averagedGeometricFilter_norm_le D hD hL) k

end Contractions

section Residual

variable {P Q : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q] [CompleteSpace Q]

/-- The residual after smoothing and transducer cancellation. Composition order
is explicit: the catalyst enters the private space and its adjoint returns to
the public space. -/
noncomputable def smoothedTransducerResidual (U : P →L[ℂ] P) (Γ : P →L[ℂ] Q)
    (F D : Q →L[ℂ] Q) (d : ℕ) : P →L[ℂ] P :=
  (d : ℂ)⁻¹ • (U ∘L (Γ† ∘L (F ∘L ((1 - D ^ d) ∘L Γ))))

/-- The smoothing cancellation directly for bounded operators on independently
typed public and private Hilbert spaces. -/
theorem continuous_smoothing_cancellation (U : P →L[ℂ] P) (B : Q →L[ℂ] P)
    (Γ : P →L[ℂ] Q) (F D : Q →L[ℂ] Q) (d : ℕ)
    (hExit : B = U ∘L (Γ† ∘L (1 - D))) (hComm : D * F = F * D) :
    B ∘L (F ∘L ((∑ j ∈ Finset.range d, D ^ j) ∘L Γ)) =
      U ∘L (Γ† ∘L (F ∘L ((1 - D ^ d) ∘L Γ))) := by
  have hSwap : (1 - D) * F = F * (1 - D) := by
    rw [sub_mul, mul_sub, one_mul, mul_one, hComm]
  have hCancel : (1 - D) * (F * ∑ j ∈ Finset.range d, D ^ j) =
      F * (1 - D ^ d) := by
    rw [← mul_assoc, hSwap, mul_assoc, mul_neg_geom_sum]
  rw [hExit]
  have h := congrArg (fun T : Q →L[ℂ] Q => U ∘L (Γ† ∘L (T ∘L Γ))) hCancel
  simpa only [ContinuousLinearMap.mul_def, comp_assoc] using h

/-- Normalization turns the actual averaged expression into the residual whose
operator norm is estimated below. -/
theorem normalized_smoothing_cancellation (U : P →L[ℂ] P) (B : Q →L[ℂ] P)
    (Γ : P →L[ℂ] Q) (F D : Q →L[ℂ] Q) (d : ℕ)
    (hExit : B = U ∘L (Γ† ∘L (1 - D))) (hComm : D * F = F * D) :
    (d : ℂ)⁻¹ • (B ∘L (F ∘L ((∑ j ∈ Finset.range d, D ^ j) ∘L Γ))) =
      smoothedTransducerResidual U Γ F D d := by
  rw [continuous_smoothing_cancellation U B Γ F D d hExit hComm]
  rfl

/-- The cancellation residual is bounded in the genuine operator norm. No
commutation hypothesis on `F` is necessary for this estimate. -/
theorem smoothedTransducerResidual_norm_le (U : P →L[ℂ] P) (Γ : P →L[ℂ] Q)
    (F D : Q →L[ℂ] Q) {W : ℝ} {d : ℕ}
    (hU : ‖U‖ ≤ 1) (hD : ‖D‖ ≤ 1) (hΓ : ‖Γ‖ ^ 2 ≤ W) (hd : 1 ≤ d) :
    ‖smoothedTransducerResidual U Γ F D d‖ ≤ (2 * W / d) * ‖F‖ := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hΓadj : ‖Γ†‖ = ‖Γ‖ := LinearIsometryEquiv.norm_map _ _
  have hEndpoint := norm_one_sub_contraction_pow_le D hD d
  have hInner : ‖(1 - D ^ d) ∘L Γ‖ ≤ 2 * ‖Γ‖ :=
    (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right hEndpoint (norm_nonneg Γ))
  have hF : ‖F ∘L ((1 - D ^ d) ∘L Γ)‖ ≤ ‖F‖ * (2 * ‖Γ‖) :=
    (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left hInner (norm_nonneg F))
  have hAdj : ‖Γ† ∘L (F ∘L ((1 - D ^ d) ∘L Γ))‖ ≤
      ‖Γ‖ * (‖F‖ * (2 * ‖Γ‖)) := by
    calc
      _ ≤ ‖Γ†‖ * ‖F ∘L ((1 - D ^ d) ∘L Γ)‖ := opNorm_comp_le _ _
      _ ≤ ‖Γ†‖ * (‖F‖ * (2 * ‖Γ‖)) :=
        mul_le_mul_of_nonneg_left hF (norm_nonneg _)
      _ = ‖Γ‖ * (‖F‖ * (2 * ‖Γ‖)) := by rw [hΓadj]
  have hRaw : ‖U ∘L (Γ† ∘L (F ∘L ((1 - D ^ d) ∘L Γ)))‖ ≤ 2 * W * ‖F‖ := by
    calc
      _ ≤ ‖U‖ * ‖Γ† ∘L (F ∘L ((1 - D ^ d) ∘L Γ))‖ := opNorm_comp_le _ _
      _ ≤ 1 * (‖Γ‖ * (‖F‖ * (2 * ‖Γ‖))) :=
        mul_le_mul hU hAdj (norm_nonneg _) (by norm_num)
      _ = (2 * ‖Γ‖ ^ 2) * ‖F‖ := by ring
      _ ≤ (2 * W) * ‖F‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hΓ (by norm_num)) (norm_nonneg F)
  rw [smoothedTransducerResidual, norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (d : ℝ)⁻¹ * (2 * W * ‖F‖) :=
      mul_le_mul_of_nonneg_left hRaw (inv_nonneg.mpr hdpos.le)
    _ = (2 * W / d) * ‖F‖ := by ring

/-- With a smoothing length at least twice the catalyst cost, any established
filter norm bound transfers directly to the residual. -/
theorem smoothedTransducerResidual_norm_le_filter (U : P →L[ℂ] P)
    (Γ : P →L[ℂ] Q) (F D : Q →L[ℂ] Q) {W δ : ℝ} {d : ℕ}
    (hU : ‖U‖ ≤ 1) (hD : ‖D‖ ≤ 1) (hΓ : ‖Γ‖ ^ 2 ≤ W)
    (hd : 1 ≤ d) (hCost : 2 * W ≤ d) (hF : ‖F‖ ≤ δ) :
    ‖smoothedTransducerResidual U Γ F D d‖ ≤ δ := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hFactor : 2 * W / d ≤ 1 := (div_le_one hdpos).mpr hCost
  calc
    _ ≤ (2 * W / d) * ‖F‖ := smoothedTransducerResidual_norm_le U Γ F D hU hD hΓ hd
    _ ≤ 1 * ‖F‖ := mul_le_mul_of_nonneg_right hFactor (norm_nonneg F)
    _ ≤ δ := by simpa using hF

/-- The operator-norm estimate for the normalized averaged expression, with the
exit identity and commutation supplied explicitly. This theorem bridges the
algebraic cancellation to the norm bound without any matrix-norm convention. -/
theorem normalized_smoothing_norm_le (U : P →L[ℂ] P) (B : Q →L[ℂ] P)
    (Γ : P →L[ℂ] Q) (F D : Q →L[ℂ] Q) {W : ℝ} {d : ℕ}
    (hExit : B = U ∘L (Γ† ∘L (1 - D))) (hComm : D * F = F * D)
    (hU : ‖U‖ ≤ 1) (hD : ‖D‖ ≤ 1) (hΓ : ‖Γ‖ ^ 2 ≤ W) (hd : 1 ≤ d) :
    ‖(d : ℂ)⁻¹ • (B ∘L (F ∘L ((∑ j ∈ Finset.range d, D ^ j) ∘L Γ)))‖ ≤
      (2 * W / d) * ‖F‖ := by
  rw [normalized_smoothing_cancellation U B Γ F D d hExit hComm]
  exact smoothedTransducerResidual_norm_le U Γ F D hU hD hΓ hd

end Residual

end SparseHamiltonian
