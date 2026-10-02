import SparseHamiltonian.Woodbury

/-!
# A quantitatively bounded local Woodbury inverse

The public feedback inverse is constructed by a convergent Neumann series.
Only the public space must be complete, and the statements allow zero spaces.
The private inverse and weighted endpoint estimates are explicit hypotheses.
-/

namespace SparseHamiltonian

noncomputable section

open ContinuousLinearMap

variable {P V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- A small public feedback has a two-sided inverse of norm at most `9/7`.
The proof uses `‖id‖ ≤ 1`, so no nontrivial-space assumption is necessary. -/
theorem exists_public_feedback_inverse [CompleteSpace P]
    (F : P →L[ℂ] P) {κ : ℝ}
    (hκ : 0 ≤ κ) (hκUpper : κ ≤ 2 / 9) (hF : ‖F‖ ≤ 1) :
    ∃ K : P →L[ℂ] P,
      (1 + (κ : ℂ) • F) ∘L K = 1 ∧
      K ∘L (1 + (κ : ℂ) • F) = 1 ∧ ‖K‖ ≤ 9 / 7 := by
  let T : P →L[ℂ] P := -((κ : ℂ) • F)
  have hκNorm : ‖(κ : ℂ)‖ = κ := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ]
  have hT : ‖T‖ ≤ 2 / 9 := by
    calc
      ‖T‖ = κ * ‖F‖ := by simp only [T, norm_neg, norm_smul, hκNorm]
      _ ≤ κ * 1 := mul_le_mul_of_nonneg_left hF hκ
      _ ≤ 2 / 9 := by simpa only [mul_one] using hκUpper
  have hLt : ‖T‖ < 1 := by linarith
  let K : P →L[ℂ] P := ∑' n : ℕ, T ^ n
  refine ⟨K, ?_, ?_, ?_⟩
  · simpa only [T, sub_neg_eq_add, mul_def] using mul_neg_geom_series T hLt
  · simpa only [T, sub_neg_eq_add, mul_def] using geom_series_mul_neg T hLt
  · have hSeries := tsum_geometric_le_of_norm_lt_one T hLt
    have hOne : ‖(1 : P →L[ℂ] P)‖ ≤ 1 := by
      simpa only [one_def] using (norm_id_le (𝕜 := ℂ) (E := P))
    have hInv : (1 - ‖T‖)⁻¹ ≤ (9 : ℝ) / 7 := by
      rw [inv_le_iff_one_le_mul₀ (by linarith : 0 < 1 - ‖T‖)]
      linarith
    exact hSeries.trans (by linarith)

/-- The correction is controlled by the two weighted endpoints, rather than
by separate bounds on the unperturbed inverse and the inclusion. -/
theorem norm_woodburyInverse_le (R : V →L[ℂ] V) (J : P →L[ℂ] V)
    (K : P →L[ℂ] P) (B : V →L[ℂ] P) {κ : ℝ} (hκ : 0 ≤ κ) :
    ‖woodburyInverse R J K B (κ : ℂ)‖ ≤
      ‖R‖ + κ * (‖R ∘L J‖ * ‖K‖ * ‖B ∘L R‖) := by
  have hCorrection : ‖R ∘L J ∘L K ∘L B ∘L R‖ ≤
      ‖R ∘L J‖ * ‖K‖ * ‖B ∘L R‖ := by
    calc
      _ = ‖((R ∘L J) ∘L K) ∘L (B ∘L R)‖ := by simp only [comp_assoc]
      _ ≤ ‖(R ∘L J) ∘L K‖ * ‖B ∘L R‖ := opNorm_comp_le _ _
      _ ≤ (‖R ∘L J‖ * ‖K‖) * ‖B ∘L R‖ :=
        mul_le_mul_of_nonneg_right (opNorm_comp_le _ _) (norm_nonneg _)
  have hκNorm : ‖(κ : ℂ)‖ = κ := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ]
  calc
    _ ≤ ‖R‖ + ‖(κ : ℂ) • (R ∘L J ∘L K ∘L B ∘L R)‖ :=
      norm_sub_le _ _
    _ = ‖R‖ + κ * ‖R ∘L J ∘L K ∘L B ∘L R‖ := by rw [norm_smul, hκNorm]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hCorrection hκ)

/-- The corrected right endpoint has the constant `12/7`. -/
theorem norm_woodbury_inclusion_le (R : V →L[ℂ] V) (J : P →L[ℂ] V)
    (K : P →L[ℂ] P) (B : V →L[ℂ] P) (κ : ℂ) {b : ℝ}
    (hb : 0 ≤ b) (hRJ : ‖R ∘L J‖ ≤ 4 * b / 3) (hK : ‖K‖ ≤ 9 / 7)
    (hLeft : K ∘L (1 + κ • (B ∘L R ∘L J)) = 1) :
    ‖woodburyInverse R J K B κ ∘L J‖ ≤ 12 * b / 7 := by
  rw [woodbury_inclusion_endpoint R J K B κ hLeft, ← comp_assoc]
  calc
    _ ≤ ‖R ∘L J‖ * ‖K‖ := opNorm_comp_le _ _
    _ ≤ (4 * b / 3) * (9 / 7) :=
      mul_le_mul hRJ hK (norm_nonneg _) (by positivity)
    _ = 12 * b / 7 := by ring

/-- The corrected left endpoint has the same constant. -/
theorem norm_woodbury_observation_le (R : V →L[ℂ] V) (J : P →L[ℂ] V)
    (K : P →L[ℂ] P) (B : V →L[ℂ] P) (κ : ℂ) {b : ℝ}
    (hBR : ‖B ∘L R‖ ≤ 4 * b / 3) (hK : ‖K‖ ≤ 9 / 7)
    (hRight : (1 + κ • (B ∘L R ∘L J)) ∘L K = 1) :
    ‖B ∘L woodburyInverse R J K B κ‖ ≤ 12 * b / 7 := by
  rw [woodbury_observation_endpoint R J K B κ hRight]
  calc
    _ ≤ ‖K‖ * ‖B ∘L R‖ := opNorm_comp_le _ _
    _ ≤ (9 / 7) * (4 * b / 3) :=
      mul_le_mul hK hBR (norm_nonneg _) (by norm_num)
    _ = 12 * b / 7 := by ring

/-- The weighted endpoint budget absorbs the entire finite-rank correction. -/
theorem norm_woodburyInverse_le_two_mul (R : V →L[ℂ] V) (J : P →L[ℂ] V)
    (K : P →L[ℂ] P) (B : V →L[ℂ] P) {κ Q b : ℝ}
    (hκ : 0 ≤ κ) (hκUpper : κ ≤ 2 / 9) (hb : 0 ≤ b)
    (hBudget : b ^ 2 ≤ Q / 2) (hR : ‖R‖ ≤ 4 * Q / 3)
    (hRJ : ‖R ∘L J‖ ≤ 4 * b / 3) (hBR : ‖B ∘L R‖ ≤ 4 * b / 3)
    (hK : ‖K‖ ≤ 9 / 7) :
    ‖woodburyInverse R J K B (κ : ℂ)‖ ≤ 2 * Q := by
  have hEnds : ‖R ∘L J‖ * ‖K‖ * ‖B ∘L R‖ ≤
      (4 * b / 3) * (9 / 7) * (4 * b / 3) := by
    apply mul_le_mul
    · exact mul_le_mul hRJ hK (norm_nonneg _) (by positivity)
    · exact hBR
    · exact norm_nonneg _
    · positivity
  calc
    _ ≤ ‖R‖ + κ * (‖R ∘L J‖ * ‖K‖ * ‖B ∘L R‖) :=
      norm_woodburyInverse_le R J K B hκ
    _ ≤ 4 * Q / 3 + (2 / 9) * ((4 * b / 3) * (9 / 7) * (4 * b / 3)) :=
      add_le_add hR (mul_le_mul hκUpper hEnds (by positivity) (by norm_num))
    _ = 4 * Q / 3 + 32 * b ^ 2 / 63 := by ring
    _ ≤ 2 * Q := by nlinarith [sq_nonneg b]

/-- A local inverse with both exact identities and all weighted norm estimates. -/
theorem exists_bounded_local_resolvent [CompleteSpace P]
    (X R : V →L[ℂ] V) (J : P →L[ℂ] V) (B : V →L[ℂ] P)
    {κ Q b : ℝ} (hκ : 0 ≤ κ) (hκUpper : κ ≤ 2 / 9) (hb : 0 ≤ b)
    (hBudget : b ^ 2 ≤ Q / 2)
    (hXR : X ∘L R = 1) (hRX : R ∘L X = 1)
    (hF : ‖B ∘L R ∘L J‖ ≤ 1) (hR : ‖R‖ ≤ 4 * Q / 3)
    (hRJ : ‖R ∘L J‖ ≤ 4 * b / 3) (hBR : ‖B ∘L R‖ ≤ 4 * b / 3) :
    ∃ (K : P →L[ℂ] P) (S : V →L[ℂ] V),
      (1 + (κ : ℂ) • (B ∘L R ∘L J)) ∘L K = 1 ∧
      K ∘L (1 + (κ : ℂ) • (B ∘L R ∘L J)) = 1 ∧ ‖K‖ ≤ 9 / 7 ∧
      S = woodburyInverse R J K B (κ : ℂ) ∧
      (X + (κ : ℂ) • (J ∘L B)) ∘L S = 1 ∧
      S ∘L (X + (κ : ℂ) • (J ∘L B)) = 1 ∧
      ‖S‖ ≤ 2 * Q ∧ ‖S ∘L J‖ ≤ 12 * b / 7 ∧ ‖B ∘L S‖ ≤ 12 * b / 7 := by
  obtain ⟨K, hRight, hLeft, hK⟩ :=
    exists_public_feedback_inverse (B ∘L R ∘L J) hκ hκUpper hF
  refine ⟨K, woodburyInverse R J K B (κ : ℂ), hRight, hLeft, hK, rfl,
    woodbury_right_inverse X R J K B (κ : ℂ) hXR hRight,
    woodbury_left_inverse X R J K B (κ : ℂ) hRX hLeft, ?_, ?_, ?_⟩
  · exact norm_woodburyInverse_le_two_mul R J K B hκ hκUpper hb hBudget hR hRJ hBR hK
  · exact norm_woodbury_inclusion_le R J K B (κ : ℂ) hb hRJ hK hLeft
  · exact norm_woodbury_observation_le R J K B (κ : ℂ) hBR hK hRight

end

end SparseHamiltonian
