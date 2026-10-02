import SparseHamiltonian.NativeAttenuatedPolynomialOverlap

/-!
# Conditional native sparse amplification with normalization `16 β`

A common row/column absolute-sum bound `β` fixes the signal threshold and
amplification gain before oracle access. An admissible normalized polynomial
pair with a relative approximation on the indicated interval yields one
uniform native circuit. Constructing that pair with the required degree is
an explicit remaining obligation, not a hidden assumption about row-sum access.
-/

namespace SparseHamiltonian.NativeSparseAmplifierCertificate

noncomputable section
open ContinuousLinearMap NativeSparseAttenuation NativeAttenuatedPhaseSequence
open NativeSparseBlockEncoding (Data Query)
open scoped BigOperators InnerProduct
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

/-- A scalar rescales an operator approximation by its norm. -/
theorem norm_smul_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a : ℂ) (M N : E) (η : ℝ) (h : ‖M - N‖ ≤ η) :
    ‖a • M - a • N‖ ≤ ‖a‖ * η := by
  rw [← smul_sub, norm_smul]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  {s : ℕ}

/-- Square root of the common success-probability upper bound. -/
def successBound (D : Data X n Z s) (β : ℝ) : ℝ :=
  Real.sqrt (β / ((s : ℝ) * D.scale))

/-- Quarter attenuation leaves a factor-two margin below this threshold. -/
def threshold (D : Data X n Z s) (β : ℝ) : ℝ := successBound D β / 2

/-- The public target gain depends only on known bounds. -/
def target (D : Data X n Z s) (β : ℝ) : ℂ := (1 / successBound D β : ℝ)

/-- The normalized target operator is `H/(16 β)`. -/
def normalized (D : Data X n Z s) (β : ℝ) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  (1 / (16 * β) : ℂ) • SparseStateOverlap.matrixOperator (D.matrix x)

theorem sparseScale_pos (D : Data X n Z s) : 0 < (s : ℝ) * D.scale :=
  mul_pos (by exact_mod_cast D.slots_pos) D.scale_pos

theorem successBound_pos (D : Data X n Z s) (β : ℝ) (hβ : 0 < β) :
    0 < successBound D β :=
  Real.sqrt_pos.2 (div_pos hβ (sparseScale_pos D))

theorem successBound_sq (D : Data X n Z s) (β : ℝ) (hβ : 0 ≤ β) :
    successBound D β ^ 2 = β / ((s : ℝ) * D.scale) :=
  Real.sq_sqrt (div_nonneg hβ (sparseScale_pos D).le)

theorem target_ne_zero (D : Data X n Z s) (β : ℝ) (hβ : 0 < β) : target D β ≠ 0 := by
  unfold target
  exact_mod_cast (one_div_ne_zero (successBound_pos D β hβ).ne')

theorem norm_target (D : Data X n Z s) (β : ℝ) (hβ : 0 < β) :
    ‖target D β‖ = 1 / successBound D β := by
  rw [target, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
  exact one_div_pos.2 (successBound_pos D β hβ)

/-- The gain squared is the original sparse normalization divided by `β`. -/
theorem norm_target_sq (D : Data X n Z s) (β : ℝ) (hβ : 0 < β) :
    ‖target D β‖ ^ 2 = ((s : ℝ) * D.scale) / β := by
  rw [norm_target D β hβ, div_pow, one_pow, successBound_sq D β hβ.le]
  field_simp

/-- If the public absolute-sum bound is at least the entry bound, the required
amplitude gain is at most `sqrt s`. -/
theorem norm_target_le_sqrt (D : Data X n Z s) (β : ℝ) (hβ : D.scale ≤ β) :
    ‖target D β‖ ≤ Real.sqrt s := by
  have hb : 0 < β := lt_of_lt_of_le D.scale_pos hβ
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hsq : ‖target D β‖ ^ 2 ≤ (s : ℝ) := by
    rw [norm_target_sq D β hb]
    apply (div_le_iff₀ hb).2
    exact mul_le_mul_of_nonneg_left hβ hs
  have hr := Real.sq_sqrt hs
  nlinarith [norm_nonneg (target D β), Real.sqrt_nonneg (s : ℝ)]

/-- This is exactly the desired gain `1/(2 Γ)`. -/
theorem target_threshold (D : Data X n Z s) (β : ℝ) :
    target D β = (1 / (2 * threshold D β) : ℝ) := by
  simp only [target, threshold]
  congr 1
  ring

/-- A row-sum bound controls every actual quarter-attenuated signal. -/
theorem rowSignal_le_half_threshold (D : Data X n Z s) (β : ℝ) (x : X)
    (hRow : ∀ i, ∑ j, ‖D.matrix x i j‖ ≤ β) (i : n) :
    rowSignal D x i ≤ threshold D β / 2 := by
  have hs : SparseSuccessProjection.rowSuccess (D.matrix x) D.scale (D.rowloc x) i ≤
      β / ((s : ℝ) * D.scale) := by
    rw [SparseSuccessProjection.rowSuccess_all _ _ _ (D.row_covers x)]
    exact div_le_div_of_nonneg_right (hRow i) (sparseScale_pos D).le
  have hh := Real.sqrt_le_sqrt hs
  unfold rowSignal NativeSparsePhaseSequence.rowSignal threshold successBound
  linarith

/-- The column signal obeys the same public interval. -/
theorem columnSignal_le_half_threshold (D : Data X n Z s) (β : ℝ) (x : X)
    (hCol : ∀ j, ∑ i, ‖D.matrix x i j‖ ≤ β) (j : n) :
    columnSignal D x j ≤ threshold D β / 2 := by
  have hs : SparseSuccessProjection.columnSuccess (D.matrix x) D.scale (D.colloc x) j ≤
      β / ((s : ℝ) * D.scale) := by
    rw [SparseSuccessProjection.columnSuccess_all _ _ _ (D.column_covers x)]
    exact div_le_div_of_nonneg_right (hCol j) (sparseScale_pos D).le
  have hh := Real.sqrt_le_sqrt hs
  unfold columnSignal NativeSparsePhaseSequence.columnSignal threshold successBound
  linarith

theorem threshold_pos (D : Data X n Z s) (β : ℝ) (hβ : 0 < β) :
    0 < threshold D β := div_pos (successBound_pos D β hβ) (by norm_num)

/-- The usual useful range `β ≤ s a` gives a threshold at most one half. -/
theorem threshold_le_half (D : Data X n Z s) (β : ℝ)
    (hβ : β ≤ (s : ℝ) * D.scale) : threshold D β ≤ 1 / 2 := by
  have h : β / ((s : ℝ) * D.scale) ≤ 1 := (div_le_one (sparseScale_pos D)).2 hβ
  have hh := Real.sqrt_le_sqrt h
  rw [Real.sqrt_one] at hh
  unfold threshold successBound
  linarith

/-- Quarter attenuation followed by the target gain gives the exact public
normalization `16 β`. -/
theorem normalization (D : Data X n Z s) (β : ℝ) (hβ : 0 < β) (x : X) :
    ((‖target D β‖ ^ 2 : ℝ) : ℂ) •
      NativeAttenuatedPolynomialOverlap.baseMatrix D x = normalized D β x := by
  have hs : (s : ℂ) ≠ 0 := by exact_mod_cast D.slots_pos.ne'
  have ha : (D.scale : ℂ) ≠ 0 := by exact_mod_cast D.scale_pos.ne' 
  have hb : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have hg : ((1 / successBound D β : ℝ) ^ 2 : ℂ) =
      ((s : ℂ) * D.scale) / β := by
    have h : (1 / successBound D β) ^ 2 = ((s : ℝ) * D.scale) / β := by
      rw [div_pow, one_pow, successBound_sq D β hβ.le]
      field_simp
    exact_mod_cast h
  rw [norm_target D β hβ, Complex.ofReal_pow, hg, NativeAttenuatedPolynomialOverlap.baseMatrix, smul_smul]
  ext v i
  simp only [normalized, smul_apply, PiLp.smul_apply, smul_eq_mul,
    SparseStateOverlap.matrixOperator_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  field_simp [hs, ha, hb]

/-- The same identity gives its exact norm, without a dimension factor. -/
theorem normalization_norm (D : Data X n Z s) (β : ℝ) (hβ : 0 < β) (x : X) :
    ‖target D β‖ ^ 2 * ‖NativeAttenuatedPolynomialOverlap.baseMatrix D x‖ =
      ‖normalized D β x‖ := by
  rw [← normalization D β hβ x, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]

/-- Common absolute row and column sum bounds make the target a contraction
with constant slack. -/
theorem normalized_norm_le (D : Data X n Z s) (β : ℝ) (hβ : 0 < β) (x : X)
    (hRow : ∀ i, ∑ j, ‖D.matrix x i j‖ ≤ β)
    (hCol : ∀ j, ∑ i, ‖D.matrix x i j‖ ≤ β) :
    ‖normalized D β x‖ ≤ 1 / 16 := by
  have hb : (1 / (16 * β) : ℝ) ≥ 0 := by positivity
  have hn : ‖(1 / (16 * β) : ℂ)‖ = (1 / (16 * β) : ℝ) := by
    rw [show (1 / (16 * β) : ℂ) = ((1 / (16 * β) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
  rw [normalized, norm_smul, hn]
  calc
    _ ≤ (1 / (16 * β)) * β := mul_le_mul_of_nonneg_left
      (SparseMatrixNorm.norm_matrixOperator_le _ β hβ hRow hCol) hb
    _ = _ := by field_simp

/-- Undoing the public normalization gives the corresponding Hamiltonian
operator error. -/
theorem rescaled_error (D : Data X n Z s) (β : ℝ) (hβ : 0 < β) (x : X)
    (M : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (η : ℝ)
    (herr : ‖M - normalized D β x‖ ≤ η / 16) :
    ‖(16 * β : ℂ) • M - SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ β * η := by
  have hb : (β : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have hn : (16 * β : ℂ) • normalized D β x =
      SparseStateOverlap.matrixOperator (D.matrix x) := by
    rw [normalized, smul_smul]
    field_simp
    simp
  have hc : ‖(16 * β : ℂ)‖ = 16 * β := by
    rw [show (16 * β : ℂ) = ((16 * β : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have he : ‖(16 * β : ℂ) • M - (16 * β : ℂ) • normalized D β x‖ ≤
      ‖(16 * β : ℂ)‖ * (η / 16) := norm_smul_sub_le _ _ _ _ herr
  rw [hn, hc] at he
  convert he using 1
  ring


variable [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

/-- A completed polynomial approximant on the public interval yields one
native sparse circuit with error `(2 δ + δ²)/16` in its `H/(16 β)` block.
The polynomial pair and its degree bound remain explicit premises. -/
theorem exists_program_of_pair (D : Data X n Z s) (β : ℝ) (hβ : 0 < β)
    (m : ℕ) (P B : Polynomial ℂ)
    (hP : P.natDegree ≤ 2 * m + 1) (hB : B.natDegree ≤ 2 * m)
    (hp : P.comp (-Polynomial.X) = -P) (hb : B.comp (-Polynomial.X) = B)
    (hnorm : PolynomialUnitarity.IsNormalized P B)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ≤ β)
    (hCol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ≤ β)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (herr : ∀ z : ℝ, |z| ≤ threshold D β / 2 →
      ‖P.eval (z : ℂ) - target D β * (z : ℂ)‖ ≤
        (δ * ‖target D β‖) * |z|) :
    ∃ p : MultiOracleCircuit.Program (oracles D), p.count = 6 * (2 * m + 1) ∧
      (∀ x, OracleCircuit.IsUnitary (p.eval x)) ∧
      (∀ x, ((input D).toContinuousLinearMap† ∘L p.eval x ∘L
        (input D).toContinuousLinearMap)† =
        (input D).toContinuousLinearMap† ∘L p.eval x ∘L (input D).toContinuousLinearMap) ∧
      ∀ x, ‖(input D).toContinuousLinearMap† ∘L p.eval x ∘L
        (input D).toContinuousLinearMap - normalized D β x‖ ≤ (2 * δ + δ ^ 2) / 16 := by
  have happ (x : X) (i : n) :
      ‖P.eval (rowSignal D x i : ℂ) - target D β * (rowSignal D x i : ℂ)‖ ≤
        (δ * ‖target D β‖) * |rowSignal D x i| := by
    apply herr
    rw [abs_of_nonneg (rowSignal_nonneg D x i)]
    exact rowSignal_le_half_threshold D β x (hRow x) i
  obtain ⟨p, hcount, hunitary, hselfadjoint, herror⟩ :=
    NativeAttenuatedPolynomialOverlap.exists_program_of_pair D m P B hP hB hp hb hnorm hH
      (target D β) (target_ne_zero D β hβ) δ hδ happ
  refine ⟨p, hcount, hunitary, hselfadjoint, ?_⟩
  intro x
  have he := herror x
  rw [normalization D β hβ x] at he
  calc
    _ ≤ ‖target D β‖ ^ 2 * ((2 * δ + δ ^ 2) *
        ‖NativeAttenuatedPolynomialOverlap.baseMatrix D x‖) := he
    _ = (2 * δ + δ ^ 2) * ‖normalized D β x‖ := by
      rw [← normalization_norm D β hβ x]
      ring
    _ ≤ (2 * δ + δ ^ 2) * (1 / 16) :=
      mul_le_mul_of_nonneg_left (normalized_norm_le D β hβ x (hRow x) (hCol x))
        (by positivity)
    _ = _ := by ring

end
end SparseHamiltonian.NativeSparseAmplifierCertificate
