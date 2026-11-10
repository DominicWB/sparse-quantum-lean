import TimeDependentODE.LCHS.Products

/-!
# The positive repair of a represented dissipative part

A represented sample `G̃ = D̃ + i H̃` of a dissipative path need not have a positive semidefinite
dissipative part `D̃`: a small representation error can move a zero eigenvalue below zero. If
`Re ⟨w, D̃ w⟩ ≥ -κ ‖w‖²` for some `κ ≥ 0` (a *negativity bound*), the operator

  `repair D̃ κ = (‖D̃‖ / (‖D̃‖ + κ)) (D̃ + κ)`

is self-adjoint and positive semidefinite, no larger in norm than `D̃`, and within `2κ` (and
within `2‖D̃‖`) of `D̃`. It serves the analysis only: the circuits keep the represented samples.

* `repair_selfAdjoint`, `repair_nonneg`, `norm_repair_le`, `norm_repair_sub_le`,
  `norm_repair_sub_le_two_norm`;
* `productFamily_sub_le`: at a real frequency `k` two product families with the same Hamiltonian
  parts differ by at most `|k| ∑_r τ_r ‖D_r - D'_r‖` (the LCHS branches are unitary).
-/

set_option autoImplicit false

namespace SparseHamiltonian.RepresentedSampleODE

noncomputable section
open ContinuousLinearMap
open SparseHamiltonian.TimeDependentODE.GaussianLCHS (productFamily productFamily_ofReal)
open scoped InnerProduct

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The positive repair `(‖A‖ / (‖A‖ + κ)) (A + κ)` of a self-adjoint operator with negativity
bound `κ`. -/
def repair (A : K →L[ℂ] K) (κ : ℝ) : K →L[ℂ] K :=
  ((‖A‖ / (‖A‖ + κ) : ℝ) : ℂ) • (A + (κ : ℂ) • (1 : K →L[ℂ] K))

theorem norm_one_op_le : ‖(1 : K →L[ℂ] K)‖ ≤ 1 := by
  rw [ContinuousLinearMap.one_def]
  exact ContinuousLinearMap.norm_id_le

theorem repair_coeff_nonneg (A : K →L[ℂ] K) {κ : ℝ} (hκ : 0 ≤ κ) :
    0 ≤ ‖A‖ / (‖A‖ + κ) :=
  div_nonneg (norm_nonneg A) (add_nonneg (norm_nonneg A) hκ)

theorem repair_selfAdjoint [CompleteSpace K] (A : K →L[ℂ] K) (hA : star A = A) (κ : ℝ) :
    star (repair A κ) = repair A κ := by
  unfold repair
  simp only [star_smul, star_add, hA, star_one, Complex.star_def, Complex.conj_ofReal]

/-- The repair is positive semidefinite. -/
theorem repair_nonneg (A : K →L[ℂ] K) {κ : ℝ} (hκ : 0 ≤ κ)
    (hneg : ∀ w : K, -κ * ‖w‖ ^ 2 ≤ (inner ℂ w (A w)).re) (w : K) :
    0 ≤ (inner ℂ w (repair A κ w)).re := by
  have hc := repair_coeff_nonneg A hκ
  have hw : (inner ℂ w w : ℂ).re = ‖w‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have h : (inner ℂ w (repair A κ w)).re =
      ‖A‖ / (‖A‖ + κ) * ((inner ℂ w (A w)).re + κ * ‖w‖ ^ 2) := by
    simp only [repair, smul_apply, add_apply, one_apply_eq_self, inner_smul_right,
      inner_add_right, Complex.re_ofReal_mul, Complex.add_re, hw]
  rw [h]
  have := hneg w
  exact mul_nonneg hc (by linarith)

/-- The repair is no larger in norm than the operator. -/
theorem norm_repair_le (A : K →L[ℂ] K) {κ : ℝ} (hκ : 0 ≤ κ) : ‖repair A κ‖ ≤ ‖A‖ := by
  have hc := repair_coeff_nonneg A hκ
  have hsum : ‖A + (κ : ℂ) • (1 : K →L[ℂ] K)‖ ≤ ‖A‖ + κ := by
    calc ‖A + (κ : ℂ) • (1 : K →L[ℂ] K)‖ ≤ ‖A‖ + ‖(κ : ℂ) • (1 : K →L[ℂ] K)‖ := norm_add_le _ _
      _ ≤ ‖A‖ + κ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hκ]
        have := norm_one_op_le (K := K)
        nlinarith
  unfold repair
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  rcases (add_nonneg (norm_nonneg A) hκ).eq_or_lt with h0 | hpos
  · rw [← h0, div_zero, zero_mul]
    exact norm_nonneg A
  · calc ‖A‖ / (‖A‖ + κ) * ‖A + (κ : ℂ) • (1 : K →L[ℂ] K)‖ ≤ ‖A‖ / (‖A‖ + κ) * (‖A‖ + κ) :=
          mul_le_mul_of_nonneg_left hsum hc
      _ = ‖A‖ := div_mul_cancel₀ _ hpos.ne'

/-- The repair moves the operator by at most twice the negativity bound. -/
theorem norm_repair_sub_le (A : K →L[ℂ] K) {κ : ℝ} (hκ : 0 ≤ κ) :
    ‖repair A κ - A‖ ≤ 2 * κ := by
  rcases (add_nonneg (norm_nonneg A) hκ).eq_or_lt with h0 | hpos
  · have hA : ‖A‖ = 0 := by linarith [norm_nonneg A]
    have hκ0 : κ = 0 := by linarith [norm_nonneg A]
    have hA0 : A = 0 := norm_eq_zero.mp hA
    simp [repair, hA0, hκ0]
  · set c : ℝ := ‖A‖ / (‖A‖ + κ) with hcdef
    have hc := repair_coeff_nonneg A hκ
    have hc1 : 1 - c = κ / (‖A‖ + κ) := by
      rw [hcdef]
      field_simp
      ring
    have hsplit : repair A κ - A =
        ((c - 1 : ℝ) : ℂ) • A + ((c * κ : ℝ) : ℂ) • (1 : K →L[ℂ] K) := by
      simp only [repair, ← hcdef, smul_add, smul_smul, Complex.ofReal_sub, Complex.ofReal_one,
        Complex.ofReal_mul, sub_smul, one_smul]
      abel
    have h1 : ‖((c - 1 : ℝ) : ℂ) • A‖ ≤ κ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg
        (by rw [hc1]; exact div_nonneg hκ hpos.le), hc1]
      rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
      nlinarith [norm_nonneg A]
    have h2 : ‖((c * κ : ℝ) : ℂ) • (1 : K →L[ℂ] K)‖ ≤ κ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc hκ)]
      have hone := norm_one_op_le (K := K)
      have hc1' : c ≤ 1 := by
        rw [hcdef, div_le_one hpos]
        linarith
      calc c * κ * ‖(1 : K →L[ℂ] K)‖ ≤ 1 * κ * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right hc1' hκ) hone (norm_nonneg _)
              (by positivity)
        _ = κ := by ring
    rw [hsplit]
    calc _ ≤ ‖((c - 1 : ℝ) : ℂ) • A‖ + ‖((c * κ : ℝ) : ℂ) • (1 : K →L[ℂ] K)‖ := norm_add_le _ _
      _ ≤ κ + κ := add_le_add h1 h2
      _ = 2 * κ := by ring

/-- The repair moves the operator by at most twice its norm. -/
theorem norm_repair_sub_le_two_norm (A : K →L[ℂ] K) {κ : ℝ} (hκ : 0 ≤ κ) :
    ‖repair A κ - A‖ ≤ 2 * ‖A‖ := by
  calc ‖repair A κ - A‖ ≤ ‖repair A κ‖ + ‖A‖ := norm_sub_le _ _
    _ ≤ ‖A‖ + ‖A‖ := add_le_add (norm_repair_le A hκ) le_rfl
    _ = 2 * ‖A‖ := by ring

/-- The repair moves the operator by at most `2 min(κ, ‖A‖)`. -/
theorem norm_repair_sub_le_min (A : K →L[ℂ] K) {κ : ℝ} (hκ : 0 ≤ κ) :
    ‖repair A κ - A‖ ≤ 2 * min κ ‖A‖ := by
  rcases le_total κ ‖A‖ with h | h
  · rw [min_eq_left h]
    exact norm_repair_sub_le A hκ
  · rw [min_eq_right h]
    exact norm_repair_sub_le_two_norm A hκ

/-! ### Product families with the same Hamiltonian parts -/

/-- At a real frequency two product families with the same Hamiltonian parts differ by at most
`|k| ∑_r τ_r ‖D_r - D'_r‖`. -/
theorem productFamily_sub_le [CompleteSpace K] (Hs Ds Ds' : ℕ → K →L[ℂ] K) (τ : ℕ → ℝ) (M : ℕ)
    (hH : ∀ r, star (Hs r) = Hs r) (hD : ∀ r, star (Ds r) = Ds r)
    (hD' : ∀ r, star (Ds' r) = Ds' r) (hτ : ∀ r, 0 ≤ τ r) (k : ℝ) :
    ‖productFamily Hs Ds τ M (k : ℂ) - productFamily Hs Ds' τ M (k : ℂ)‖ ≤
      |k| * ∑ r ∈ Finset.range M, τ r * ‖Ds r - Ds' r‖ := by
  rw [productFamily_ofReal, productFamily_ofReal]
  calc
    _ ≤ ∑ r ∈ Finset.range M, ‖ODEWeightedLCHS.evolution (Ds r) (Hs r) (τ r) k -
          ODEWeightedLCHS.evolution (Ds' r) (Hs r) (τ r) k‖ :=
      TimeDependent.evolution_sub_norm_le _ _
        (fun r => ODEWeightedLCHS.evolution_norm_le_one (Ds r) (Hs r) (hD r) (hH r) (τ r) k)
        (fun r => ODEWeightedLCHS.evolution_norm_le_one (Ds' r) (Hs r) (hD' r) (hH r) (τ r) k) M
    _ ≤ ∑ r ∈ Finset.range M, |k| * (τ r * ‖Ds r - Ds' r‖) := by
      apply Finset.sum_le_sum
      intro r _
      have h := HamiltonianStability.evolution_error_le (Hs r + (k : ℂ) • Ds r)
        (Hs r + (k : ℂ) • Ds' r) (τ r)
        (ODEWeightedLCHS.frequency_hamiltonian_selfAdjoint (Ds r) (Hs r) (hD r) (hH r) k)
        (ODEWeightedLCHS.frequency_hamiltonian_selfAdjoint (Ds' r) (Hs r) (hD' r) (hH r) k)
      have hdiff : (Hs r + (k : ℂ) • Ds r) - (Hs r + (k : ℂ) • Ds' r) =
          (k : ℂ) • (Ds r - Ds' r) := by
        rw [smul_sub]
        abel
      change ‖ODEWeightedLCHS.evolution (Ds r) (Hs r) (τ r) k -
          ODEWeightedLCHS.evolution (Ds' r) (Hs r) (τ r) k‖ ≤ _ at h
      rw [hdiff, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hτ r)] at h
      calc _ ≤ τ r * (|k| * ‖Ds r - Ds' r‖) := h
        _ = |k| * (τ r * ‖Ds r - Ds' r‖) := by ring
    _ = |k| * ∑ r ∈ Finset.range M, τ r * ‖Ds r - Ds' r‖ := by rw [Finset.mul_sum]

end

end SparseHamiltonian.RepresentedSampleODE
