import SparseHamiltonian.NativeSparseAmplifierCertificate

/-!
# Native sparse amplification with a bounded variable gain

The constructed polynomial need not have exactly the ideal gain `1/A`.
A gain within fixed constant factors gives normalization `Θ(β)` with the
same complete native sparse program and matrix-error guarantee.
-/

namespace SparseHamiltonian.NativeVariableGainCertificate

noncomputable section
open ContinuousLinearMap NativeSparseAttenuation NativeAttenuatedPhaseSequence
open NativeSparseBlockEncoding (Data Query)
open NativeSparseAmplifierCertificate (successBound sparseScale_pos successBound_sq)
open scoped BigOperators InnerProduct
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- Normalization resulting from a real gain after quarter attenuation. -/
def normalization (D : Data X n Z s) (g : ℝ) : ℝ := 16 * ((s : ℝ) * D.scale) / g ^ 2

/-- The target normalized matrix for the supplied public gain. -/
def normalized (D : Data X n Z s) (g : ℝ) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  (1 / normalization D g : ℂ) • SparseStateOverlap.matrixOperator (D.matrix x)

theorem normalization_pos (D : Data X n Z s) (g : ℝ) (hg : 0 < g) :
    0 < normalization D g := div_pos (mul_pos (by norm_num) (sparseScale_pos D)) (sq_pos_of_pos hg)

/-- The key normalization identity depends on the gain times `A`. -/
theorem normalization_gain_identity (D : Data X n Z s) (β g : ℝ)
    (hβ : 0 ≤ β) (hg : 0 < g) :
    normalization D g * (g * successBound D β) ^ 2 = 16 * β := by
  rw [mul_pow, successBound_sq D β hβ]
  unfold normalization
  field_simp [(sparseScale_pos D).ne', hg.ne']
  exact mul_div_cancel_left₀ β (sparseScale_pos D).ne'

/-- Constant-factor gain variation preserves normalization `Θ(β)`.
The explicit interval here is the one used by the constructive amplifier. -/
theorem normalization_bounds (D : Data X n Z s) (β g : ℝ)
    (hβ : 0 ≤ β) (hg : 0 < g)
    (hl : 1 / 8 ≤ g * successBound D β) (hu : g * successBound D β ≤ 3 / 2) :
    (64 / 9) * β ≤ normalization D g ∧ normalization D g ≤ 1024 * β := by
  have ha := normalization_pos D g hg
  have hid := normalization_gain_identity D β g hβ hg
  have hl2 : (1 / 64 : ℝ) ≤ (g * successBound D β) ^ 2 := by nlinarith
  have hu2 : (g * successBound D β) ^ 2 ≤ (9 / 4 : ℝ) := by nlinarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hu2 ha.le]
  · nlinarith [mul_le_mul_of_nonneg_left hl2 ha.le]

/-- The actual attenuated matrix overlap has its elementary scalar form. -/
theorem baseMatrix_scalar (D : Data X n Z s) (x : X) :
    NativeAttenuatedPolynomialOverlap.baseMatrix D x =
      (1 / (16 * ((s : ℂ) * D.scale))) • SparseStateOverlap.matrixOperator (D.matrix x) := by
  have hs : (s : ℂ) ≠ 0 := by exact_mod_cast D.slots_pos.ne'
  have ha : (D.scale : ℂ) ≠ 0 := by exact_mod_cast D.scale_pos.ne'
  ext v i
  simp only [NativeAttenuatedPolynomialOverlap.baseMatrix, smul_apply, PiLp.smul_apply,
    smul_eq_mul, SparseStateOverlap.matrixOperator_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  field_simp [hs, ha]

/-- The target gain produces exactly the stated normalized matrix. -/
theorem gain_normalization (D : Data X n Z s) (g : ℝ) (hg : 0 < g) (x : X) :
    ((g ^ 2 : ℝ) : ℂ) • NativeAttenuatedPolynomialOverlap.baseMatrix D x = normalized D g x := by
  have hs : (s : ℂ) ≠ 0 := by exact_mod_cast D.slots_pos.ne'
  have ha : (D.scale : ℂ) ≠ 0 := by exact_mod_cast D.scale_pos.ne'
  have hgc : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  rw [baseMatrix_scalar, smul_smul, normalized]
  congr 1
  simp only [normalization, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_natCast, Complex.ofReal_pow]
  field_simp [hs, ha, hgc]

/-- Norm form of the exact gain normalization. -/
theorem gain_normalization_norm (D : Data X n Z s) (g : ℝ) (hg : 0 < g) (x : X) :
    g ^ 2 * ‖NativeAttenuatedPolynomialOverlap.baseMatrix D x‖ = ‖normalized D g x‖ := by
  rw [← gain_normalization D g hg x, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]

/-- The matrix norm retains the original common row/column bound. -/
theorem normalized_norm_le (D : Data X n Z s) (β g : ℝ) (hβ : 0 < β) (hg : 0 < g) (x : X)
    (hRow : ∀ i, ∑ j, ‖D.matrix x i j‖ ≤ β)
    (hCol : ∀ j, ∑ i, ‖D.matrix x i j‖ ≤ β) :
    ‖normalized D g x‖ ≤ β / normalization D g := by
  have ha := normalization_pos D g hg
  have hc : ‖(1 / normalization D g : ℂ)‖ = 1 / normalization D g := by
    rw [show (1 / normalization D g : ℂ) = ((1 / normalization D g : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.2 ha)]
  rw [normalized, norm_smul, hc]
  calc
    _ ≤ (1 / normalization D g) * β := mul_le_mul_of_nonneg_left
      (SparseMatrixNorm.norm_matrixOperator_le _ β hβ hRow hCol) (one_div_nonneg.2 ha.le)
    _ = _ := by ring

/-- Rescaling a normalized block error recovers the Hamiltonian error. -/
theorem rescaled_error (D : Data X n Z s) (β g : ℝ) (hg : 0 < g) (x : X)
    (M : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (η : ℝ)
    (herr : ‖M - normalized D g x‖ ≤ η * (β / normalization D g)) :
    ‖(normalization D g : ℂ) • M - SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ β * η := by
  have ha := normalization_pos D g hg
  have hac : (normalization D g : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hn : (normalization D g : ℂ) • normalized D g x =
      SparseStateOverlap.matrixOperator (D.matrix x) := by
    rw [normalized, smul_smul]
    field_simp
    simp
  have hc : ‖(normalization D g : ℂ)‖ = normalization D g := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have he := NativeSparseAmplifierCertificate.norm_smul_sub_le
    (normalization D g : ℂ) M (normalized D g x) _ herr
  rw [hn, hc] at he
  convert he using 1
  field_simp

variable [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

/-- A normalized polynomial pair with variable public gain yields a single
actual native circuit. Its compression is Hermitian for every oracle input,
its query count is exact, and its operator error depends on `β`, not dimension. -/
theorem exists_program_of_pair (D : Data X n Z s) (β g : ℝ) (hβ : 0 < β) (hg : 0 < g)
    (m : ℕ) (P B : Polynomial ℂ)
    (hP : P.natDegree ≤ 2 * m + 1) (hB : B.natDegree ≤ 2 * m)
    (hp : P.comp (-Polynomial.X) = -P) (hb : B.comp (-Polynomial.X) = B)
    (hnorm : PolynomialUnitarity.IsNormalized P B)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ≤ β)
    (hCol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ≤ β)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (herr : ∀ z : ℝ, |z| ≤ successBound D β / 4 →
      ‖P.eval (z : ℂ) - (g : ℂ) * (z : ℂ)‖ ≤ (δ * g) * |z|) :
    ∃ p : MultiOracleCircuit.Program (oracles D), p.count = 6 * (2 * m + 1) ∧
      (∀ x, OracleCircuit.IsUnitary (p.eval x)) ∧
      (∀ x, ((input D).toContinuousLinearMap† ∘L p.eval x ∘L
        (input D).toContinuousLinearMap)† =
        (input D).toContinuousLinearMap† ∘L p.eval x ∘L (input D).toContinuousLinearMap) ∧
      ∀ x, ‖(input D).toContinuousLinearMap† ∘L p.eval x ∘L
        (input D).toContinuousLinearMap - normalized D g x‖ ≤
          (2 * δ + δ ^ 2) * (β / normalization D g) := by
  have hgn : ‖(g : ℂ)‖ = g := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg]
  have hgc : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have happ (x : X) (i : n) :
      ‖P.eval (rowSignal D x i : ℂ) - (g : ℂ) * (rowSignal D x i : ℂ)‖ ≤
        (δ * ‖(g : ℂ)‖) * |rowSignal D x i| := by
    rw [hgn]
    apply herr
    rw [abs_of_nonneg (rowSignal_nonneg D x i)]
    have h := NativeSparseAmplifierCertificate.rowSignal_le_half_threshold D β x (hRow x) i
    simpa only [NativeSparseAmplifierCertificate.threshold, div_div, show (2 : ℝ) * 2 = 4 by norm_num] using h
  obtain ⟨p, hcount, hunitary, hselfadjoint, herror⟩ :=
    NativeAttenuatedPolynomialOverlap.exists_program_of_pair D m P B hP hB hp hb hnorm hH
      (g : ℂ) hgc δ hδ happ
  refine ⟨p, hcount, hunitary, hselfadjoint, ?_⟩
  intro x
  have he := herror x
  rw [hgn, gain_normalization D g hg x] at he
  calc
    _ ≤ g ^ 2 * ((2 * δ + δ ^ 2) *
        ‖NativeAttenuatedPolynomialOverlap.baseMatrix D x‖) := he
    _ = (2 * δ + δ ^ 2) * ‖normalized D g x‖ := by
      rw [← gain_normalization_norm D g hg x]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (normalized_norm_le D β g hβ hg x (hRow x) (hCol x))
      (by positivity)

end
end SparseHamiltonian.NativeVariableGainCertificate
