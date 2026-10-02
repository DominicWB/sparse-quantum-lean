import SparseHamiltonian.SmoothingLCU

/-!
# An explicit amplified smoothing isometry

The full reuse circuits, signed preparations and a reflection round form a
concrete isometry. Its entire output is close to the clean target whenever the
already constructed smoothing residual is small. No successful-block promise
is assumed: that block is calculated from the actual coherent construction.
-/

namespace SparseHamiltonian.AmplifiedSmoothing

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct BigOperators

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The coherent SELECT applied to the initial weighted uniform preparation. -/
def prepared (L k : ℕ) (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) :=
  SmoothingLCU.circuit A B C D (k * (L - 1)) ∘L
    SmoothingLCU.input (AveragingPolynomial.filter L k).coeff (k * (L - 1))

/-- One reflection amplification round for the actual coherent smoothing. -/
def implementation (L k : ℕ) (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) :=
  reflectedAmplification
    (SmoothingLCU.output (P := P) (V := V) (AveragingPolynomial.filter L k).coeff (k * (L - 1)))
    (prepared L k A B C D)

theorem prepared_isometry (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < k * (L - 1))
    (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2) :
    (prepared L k A B C D)† ∘L prepared L k A B C D = 1 := by
  unfold prepared
  rw [adjoint_comp, comp_assoc, ← comp_assoc ((SmoothingLCU.circuit A B C D _)†),
    SmoothingLCU.circuit_isometry A B C D hStep, one_def, id_comp]
  exact SmoothingLCU.input_isometry _ _ hd (ReuseWeights.concrete_absolute_mass L k hL hd)

/-- The complete amplified output, including every private register, preserves
input norms. -/
theorem implementation_isometry (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < k * (L - 1))
    (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2) :
    (implementation L k A B C D)† ∘L implementation L k A B C D = 1 := by
  exact reflectedAmplification_isometry _ _
    (SmoothingLCU.output_isometry _ _ hd (ReuseWeights.concrete_absolute_mass L k hL hd))
    (prepared_isometry L k hL hd A B C D hStep)

/-- The actual reflection circuit has full-output error at most twice the
filter residual; the exact block identity is derived from coherent reuse. -/
theorem implementation_error (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < k * (L - 1))
    (A U : P →L[ℂ] P) (B : V →L[ℂ] P) (C Γ : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (hPublic : A + B ∘L Γ = U) (hPrivate : C + D ∘L Γ = Γ)
    (hExit : B = U ∘L (Γ† ∘L (1 - D)))
    (hU : star U * U = 1) (hUU : U * star U = 1)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hResidual : ‖smoothedTransducerResidual U Γ (averagedGeometricFilter D L ^ k)
      D (k * (L - 1))‖ ≤ δ) :
    ‖implementation L k A B C D -
      SmoothingLCU.output (P := P) (V := V) (AveragingPolynomial.filter L k).coeff (k * (L - 1)) ∘L U‖ ≤
      2 * δ := by
  apply reflectedAmplification_error_of_block_error _ _ U
    (SmoothingLCU.output_isometry _ _ hd (ReuseWeights.concrete_absolute_mass L k hL hd))
    (prepared_isometry L k hL hd A B C D hStep) hU hUU hδ hδ1
  change ‖(2 : ℂ) • SmoothingLCU.successfulBlock _ _ A B C D - U‖ ≤ δ
  rw [SmoothingLCU.successfulBlock_eq _ _ hd A U B C Γ D hPublic hPrivate,
    smul_smul, mul_inv_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul,
    norm_sub_rev, SmoothedReuse.concrete_filter_residual L k hL hd U B Γ D hExit]
  exact hResidual

/-- A separate public approximation error adds linearly to the full-output
smoothing error. This is used to pass from Cayley powers to the exponential. -/
theorem implementation_error_to_target (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < k * (L - 1))
    (A U E : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (δ ε : ℝ)
    (hImplementation : ‖implementation L k A B C D -
      SmoothingLCU.output (P := P) (V := V) (AveragingPolynomial.filter L k).coeff (k * (L - 1)) ∘L U‖ ≤ δ)
    (hTarget : ‖U - E‖ ≤ ε) :
    ‖implementation L k A B C D -
      SmoothingLCU.output (P := P) (V := V) (AveragingPolynomial.filter L k).coeff (k * (L - 1)) ∘L E‖ ≤
      δ + ε := by
  let J := SmoothingLCU.output (P := P) (V := V)
    (AveragingPolynomial.filter L k).coeff (k * (L - 1))
  have hJ : ‖J‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro p
    have hh := (norm_map_iff_adjoint_comp_self J).mpr
      (SmoothingLCU.output_isometry _ _ hd (ReuseWeights.concrete_absolute_mass L k hL hd)) p
    simpa only [one_mul] using hh.le
  calc
    ‖implementation L k A B C D - J ∘L E‖ ≤
      ‖implementation L k A B C D - J ∘L U‖ + ‖J ∘L U - J ∘L E‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ δ + ε := add_le_add hImplementation (by
      rw [← comp_sub]
      calc
        ‖J ∘L (U - E)‖ ≤ ‖J‖ * ‖U - E‖ := opNorm_comp_le _ _
        _ ≤ 1 * ‖U - E‖ := mul_le_mul_of_nonneg_right hJ (norm_nonneg _)
        _ ≤ ε := by simpa only [one_mul] using hTarget)

end
end SparseHamiltonian.AmplifiedSmoothing
