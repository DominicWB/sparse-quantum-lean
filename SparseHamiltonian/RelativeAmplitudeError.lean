import SparseHamiltonian.SparseValuePrecision

/-!
# Relative amplitude errors as concrete Hamiltonian perturbations

Applying the same complex gain `1 + d i` to row and column amplitudes produces
the Hermitian matrix with entries `conj (1 + d i) * H i j * (1 + d j)`.
The general adjoint sandwich requires no reality assumption on the gain;
the original real-gain specialization is also retained.
Its actual operator error is at most `(2 * δ + δ²) * ‖H‖` when every
relative gain error is at most `δ`. These are conditional error-transfer
results and do not assert an amplification algorithm or synthesis theorem.
-/

namespace SparseHamiltonian.RelativeAmplitudeError

noncomputable section
open ContinuousLinearMap SparseStateOverlap
open scoped BigOperators InnerProduct

section Operators
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The operator produced by the same relative gain on its two sides. -/
def scaled (H D : V →L[ℂ] V) : V →L[ℂ] V := (1 + D) * H * (1 + D)

/-- A common self-adjoint relative gain preserves self-adjointness. -/
theorem scaled_adjoint (H D : V →L[ℂ] V) (hH : H† = H) (hD : D† = D) :
    (scaled H D)† = scaled H D := by
  rw [← star_eq_adjoint] at hH hD ⊢
  simp [scaled, hH, hD, mul_assoc]

omit [CompleteSpace V] in
/-- Exact expansion separates the two linear gain errors and the quadratic one. -/
theorem scaled_sub (H D : V →L[ℂ] V) :
    scaled H D - H = D * H + H * D + D * H * D := by
  unfold scaled
  noncomm_ring

omit [CompleteSpace V] in
/-- A relative gain error has a dimension-independent quadratic operator bound. -/
theorem norm_scaled_sub_le (H D : V →L[ℂ] V) (δ : ℝ)
    (hδ : 0 ≤ δ) (hD : ‖D‖ ≤ δ) :
    ‖scaled H D - H‖ ≤ (2 * δ + δ ^ 2) * ‖H‖ := by
  rw [scaled_sub]
  calc
    ‖D * H + H * D + D * H * D‖ ≤ ‖D * H + H * D‖ + ‖D * H * D‖ :=
      norm_add_le _ _
    _ ≤ (‖D * H‖ + ‖H * D‖) + ‖D * H * D‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (‖D‖ * ‖H‖ + ‖H‖ * ‖D‖) + (‖D‖ * ‖H‖) * ‖D‖ := by
      gcongr
      · exact norm_mul_le _ _
      · exact norm_mul_le _ _
      · exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (δ * ‖H‖ + ‖H‖ * δ) + (δ * ‖H‖) * δ := by gcongr
    _ = (2 * δ + δ ^ 2) * ‖H‖ := by ring

/-- The corresponding Schrödinger evolutions inherit the sharp time factor. -/
theorem evolution_error_le (H D : V →L[ℂ] V) (t δ : ℝ)
    (hH : H† = H) (hDadj : D† = D) (hδ : 0 ≤ δ) (hD : ‖D‖ ≤ δ) :
    ‖NormedSpace.exp ((-Complex.I * (t : ℂ)) • scaled H D) -
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)‖ ≤
      |t| * ((2 * δ + δ ^ 2) * ‖H‖) := by
  exact (HamiltonianStability.evolution_error_le _ _ t
    (by simpa only [star_eq_adjoint] using scaled_adjoint H D hH hDadj)
    (by simpa only [star_eq_adjoint] using hH)).trans
      (mul_le_mul_of_nonneg_left (norm_scaled_sub_le H D δ hδ hD) (abs_nonneg t))

/-- Complex relative gains must act by an adjoint sandwich. No assumption
that the gain or a polynomial realizing it is real is needed. -/
def conjugateScaled (H D : V →L[ℂ] V) : V →L[ℂ] V := (1 + D)† * H * (1 + D)

/-- An arbitrary complex gain preserves self-adjointness under the adjoint sandwich. -/
theorem conjugateScaled_adjoint (H D : V →L[ℂ] V) (hH : H† = H) :
    (conjugateScaled H D)† = conjugateScaled H D := by
  have hh : star H = H := hH
  change star (star (1 + D) * H * (1 + D)) = star (1 + D) * H * (1 + D)
  simp [hh, mul_assoc]

/-- Complex gain error separates into two first-order terms and one quadratic term. -/
theorem conjugateScaled_sub (H D : V →L[ℂ] V) :
    conjugateScaled H D - H = D† * H + H * D + D† * H * D := by
  simp only [conjugateScaled, map_add, adjoint_one]
  noncomm_ring

/-- The same dimension-independent error budget holds for arbitrary complex gains. -/
theorem norm_conjugateScaled_sub_le (H D : V →L[ℂ] V) (δ : ℝ)
    (hδ : 0 ≤ δ) (hD : ‖D‖ ≤ δ) :
    ‖conjugateScaled H D - H‖ ≤ (2 * δ + δ ^ 2) * ‖H‖ := by
  have hDa : ‖D†‖ = ‖D‖ := LinearIsometryEquiv.norm_map _ _
  rw [conjugateScaled_sub]
  calc
    ‖D† * H + H * D + D† * H * D‖ ≤ ‖D† * H + H * D‖ + ‖D† * H * D‖ :=
      norm_add_le _ _
    _ ≤ (‖D† * H‖ + ‖H * D‖) + ‖D† * H * D‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ (‖D†‖ * ‖H‖ + ‖H‖ * ‖D‖) + (‖D†‖ * ‖H‖) * ‖D‖ := by
      gcongr
      · exact norm_mul_le _ _
      · exact norm_mul_le _ _
      · exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (δ * ‖H‖ + ‖H‖ * δ) + (δ * ‖H‖) * δ := by
      rw [hDa]
      gcongr
    _ = (2 * δ + δ ^ 2) * ‖H‖ := by ring

/-- Complex amplitude errors induce sharp time-linear Hamiltonian evolution error. -/
theorem conjugateScaled_evolution_error_le (H D : V →L[ℂ] V) (t δ : ℝ)
    (hH : H† = H) (hδ : 0 ≤ δ) (hD : ‖D‖ ≤ δ) :
    ‖NormedSpace.exp ((-Complex.I * (t : ℂ)) • conjugateScaled H D) -
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)‖ ≤
      |t| * ((2 * δ + δ ^ 2) * ‖H‖) := by
  exact (HamiltonianStability.evolution_error_le _ _ t
    (by simpa only [star_eq_adjoint] using conjugateScaled_adjoint H D hH)
    (by simpa only [star_eq_adjoint] using hH)).trans
      (mul_le_mul_of_nonneg_left (norm_conjugateScaled_sub_le H D δ hδ hD)
        (abs_nonneg t))

end Operators

section Coordinates
variable {n : Type*} [Fintype n]

/-- A real coordinate gain error, realized as an actual diagonal Hilbert operator. -/
def realDiagonal (d : n → ℝ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  WeightedClock.diagonal (fun i => (d i : ℂ) • (1 : ℂ →L[ℂ] ℂ))

omit [Fintype n] in
@[simp] theorem realDiagonal_apply (d : n → ℝ) (v : EuclideanSpace ℂ n) (i : n) :
    realDiagonal d v i = (d i : ℂ) * v i := rfl

/-- A real coordinate gain is self-adjoint, including negative gain errors. -/
theorem realDiagonal_adjoint (d : n → ℝ) : (realDiagonal d)† = realDiagonal d := by
  simp only [realDiagonal, WeightedClock.diagonal_adjoint, map_smulₛₗ,
    Complex.conj_ofReal, adjoint_one]

/-- Bounding all relative errors bounds the norm of their actual diagonal operator. -/
theorem norm_realDiagonal_le (d : n → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : ∀ i, |d i| ≤ δ) : ‖realDiagonal d‖ ≤ δ := by
  apply WeightedClock.norm_diagonal_le _ δ hδ
  intro i
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    norm_one, mul_one] using hd i

/-- The row and column gain matrix, defined by its actual complex entries. -/
def gainMatrix (H : Matrix n n ℂ) (d : n → ℝ) : Matrix n n ℂ :=
  fun i j => (1 + (d i : ℂ)) * H i j * (1 + (d j : ℂ))

@[simp] theorem one_add_realDiagonal_apply (d : n → ℝ)
    (v : EuclideanSpace ℂ n) (i : n) :
    ((1 + realDiagonal d) v) i = (1 + (d i : ℂ)) * v i := by
  simp [add_mul]

/-- The gain on coordinates is exactly the matrix gain on both sides. -/
theorem scaled_matrixOperator (H : Matrix n n ℂ) (d : n → ℝ) :
    scaled (matrixOperator H) (realDiagonal d) = matrixOperator (gainMatrix H d) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  change ((1 + realDiagonal d) (matrixOperator H ((1 + realDiagonal d) v))) i = _
  rw [one_add_realDiagonal_apply]
  simp only [matrixOperator_apply, one_add_realDiagonal_apply, gainMatrix, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype n] in
/-- Shared real gains preserve Hermiticity directly at the matrix-entry level. -/
theorem gainMatrix_isHermitian (H : Matrix n n ℂ) (d : n → ℝ)
    (hH : H.IsHermitian) : (gainMatrix H d).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [gainMatrix, star_mul, star_add, star_one, Complex.star_def,
    Complex.conj_ofReal]
  rw [← Complex.star_def, hH.apply i j]
  ring

/-- Applying the same real coordinate gains to the good row and column
amplitudes gives precisely the two-sided gain matrix. All failure amplitudes
remain in disjoint sectors, so none contributes to this actual overlap. -/
theorem row_column_gain_overlap (r c : n → n → ℂ) (d : n → ℝ) :
    (row (fun i j => (1 + (d i : ℂ)) * r i j))† ∘L
      column (fun i j => (1 + (d j : ℂ)) * c i j) =
      matrixOperator (gainMatrix (fun i j => star (r i j) * c i j) d) := by
  rw [adjoint_column_eq_matrix]
  congr 1
  funext i j
  simp only [gainMatrix, star_mul, star_add, star_one, Complex.star_def,
    Complex.conj_ofReal]
  ring

/-- The concrete finite matrix inherits the relative amplitude error bound. -/
theorem norm_gainMatrix_sub_le (H : Matrix n n ℂ) (d : n → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hd : ∀ i, |d i| ≤ δ) :
    ‖matrixOperator (gainMatrix H d) - matrixOperator H‖ ≤
      (2 * δ + δ ^ 2) * ‖matrixOperator H‖ := by
  rw [← scaled_matrixOperator]
  exact norm_scaled_sub_le _ _ δ hδ (norm_realDiagonal_le d δ hδ hd)

/-- Time evolution for the actual amplified-entry matrix obeys the same budget. -/
theorem gainMatrix_evolution_error_le (H : Matrix n n ℂ) (d : n → ℝ) (t δ : ℝ)
    (hH : H.IsHermitian) (hδ : 0 ≤ δ) (hd : ∀ i, |d i| ≤ δ) :
    ‖NormedSpace.exp ((-Complex.I * (t : ℂ)) • matrixOperator (gainMatrix H d)) -
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • matrixOperator H)‖ ≤
      |t| * ((2 * δ + δ ^ 2) * ‖matrixOperator H‖) := by
  rw [← scaled_matrixOperator]
  apply evolution_error_le _ _ t δ
  · simpa only [star_eq_adjoint] using SparseValuePrecision.matrixOperator_star_eq H hH
  · exact realDiagonal_adjoint d
  · exact hδ
  · exact norm_realDiagonal_le d δ hδ hd

/-- A complex coordinate gain error as an actual bounded diagonal operator. -/
def complexDiagonal (d : n → ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  WeightedClock.diagonal (fun i => d i • (1 : ℂ →L[ℂ] ℂ))

omit [Fintype n] in
@[simp] theorem complexDiagonal_apply (d : n → ℂ) (v : EuclideanSpace ℂ n) (i : n) :
    complexDiagonal d v i = d i * v i := rfl

/-- The adjoint conjugates the coordinate gains, without assuming they are real. -/
theorem complexDiagonal_adjoint (d : n → ℂ) :
    (complexDiagonal d)† = complexDiagonal (fun i => star (d i)) := by
  simp only [complexDiagonal, WeightedClock.diagonal_adjoint, map_smulₛₗ,
    adjoint_one, Complex.star_def]

/-- The diagonal norm is bounded by a common complex gain-error bound. -/
theorem norm_complexDiagonal_le (d : n → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : ∀ i, ‖d i‖ ≤ δ) : ‖complexDiagonal d‖ ≤ δ := by
  apply WeightedClock.norm_diagonal_le _ δ hδ
  intro i
  simpa only [norm_smul, norm_one, mul_one] using hd i

@[simp] theorem one_add_complexDiagonal_apply (d : n → ℂ)
    (v : EuclideanSpace ℂ n) (i : n) :
    ((1 + complexDiagonal d) v) i = (1 + d i) * v i := by
  simp [add_mul]

/-- Complex row gains conjugate on the left side of the overlap. -/
def conjugateGainMatrix (H : Matrix n n ℂ) (d : n → ℂ) : Matrix n n ℂ :=
  fun i j => star (1 + d i) * H i j * (1 + d j)

/-- The complex diagonal sandwich realizes precisely the conjugated gain entries. -/
theorem conjugateScaled_matrixOperator (H : Matrix n n ℂ) (d : n → ℂ) :
    conjugateScaled (matrixOperator H) (complexDiagonal d) =
      matrixOperator (conjugateGainMatrix H d) := by
  simp only [conjugateScaled, map_add, adjoint_one, complexDiagonal_adjoint]
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  change ((1 + complexDiagonal (fun j => star (d j)))
    (matrixOperator H ((1 + complexDiagonal d) v))) i = _
  rw [one_add_complexDiagonal_apply]
  simp only [matrixOperator_apply, one_add_complexDiagonal_apply,
    conjugateGainMatrix, star_add, star_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype n] in
/-- Conjugated complex gains preserve Hermiticity of the entry matrix. -/
theorem conjugateGainMatrix_isHermitian (H : Matrix n n ℂ) (d : n → ℂ)
    (hH : H.IsHermitian) : (conjugateGainMatrix H d).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [conjugateGainMatrix, star_mul, star_star]
  rw [hH.apply i j]
  ring

/-- The actual row/column overlap conjugates complex gains on the row side.
No claim that polynomial gains are real is used in this identity. -/
theorem row_column_complex_gain_overlap (r c : n → n → ℂ) (d : n → ℂ) :
    (row (fun i j => (1 + d i) * r i j))† ∘L
      column (fun i j => (1 + d j) * c i j) =
      matrixOperator (conjugateGainMatrix (fun i j => star (r i j) * c i j) d) := by
  rw [adjoint_column_eq_matrix]
  congr 1
  funext i j
  simp only [conjugateGainMatrix, star_mul]
  ring

/-- Arbitrary complex relative entry gains obey the same quadratic norm budget. -/
theorem norm_conjugateGainMatrix_sub_le (H : Matrix n n ℂ) (d : n → ℂ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hd : ∀ i, ‖d i‖ ≤ δ) :
    ‖matrixOperator (conjugateGainMatrix H d) - matrixOperator H‖ ≤
      (2 * δ + δ ^ 2) * ‖matrixOperator H‖ := by
  rw [← conjugateScaled_matrixOperator]
  exact norm_conjugateScaled_sub_le _ _ δ hδ (norm_complexDiagonal_le d δ hδ hd)

/-- Actual finite-matrix evolution remains time-linearly stable for complex gains. -/
theorem conjugateGainMatrix_evolution_error_le (H : Matrix n n ℂ) (d : n → ℂ)
    (t δ : ℝ) (hH : H.IsHermitian) (hδ : 0 ≤ δ) (hd : ∀ i, ‖d i‖ ≤ δ) :
    ‖NormedSpace.exp ((-Complex.I * (t : ℂ)) • matrixOperator (conjugateGainMatrix H d)) -
      NormedSpace.exp ((-Complex.I * (t : ℂ)) • matrixOperator H)‖ ≤
      |t| * ((2 * δ + δ ^ 2) * ‖matrixOperator H‖) := by
  rw [← conjugateScaled_matrixOperator]
  apply conjugateScaled_evolution_error_le _ _ t δ
  · simpa only [star_eq_adjoint] using SparseValuePrecision.matrixOperator_star_eq H hH
  · exact hδ
  · exact norm_complexDiagonal_le d δ hδ hd

end Coordinates
end
end SparseHamiltonian.RelativeAmplitudeError
