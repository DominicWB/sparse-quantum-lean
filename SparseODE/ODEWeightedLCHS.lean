import SparseODE.ODEUniformQuadrature

/-!
# Uniform frequency stability of the actual LCHS integrand

The Hamiltonian stability estimate controls the quadrature mesh uniformly in
the unknown sparse matrix and all source durations up to the public final
time. These bounds concern the exact branch exponentials already simulated
by the native circuit. No Gaussian approximation is assumed or asserted.

-/

namespace SparseHamiltonian.ODEWeightedLCHS

noncomputable section
open ContinuousLinearMap NormedSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V]

/-- The unitary family in the LCHS frequency integral. -/
def evolution (D H : V →L[ℂ] V) (u k : ℝ) : V →L[ℂ] V :=
  exp ((-Complex.I * (u : ℂ)) • (H + (k : ℂ) • D))

/-- A scalar kernel weights one exact Hamiltonian branch. -/
def weighted (D H : V →L[ℂ] V) (u : ℝ) (f : ℝ → ℂ) (k : ℝ) :
    V →L[ℂ] V := f k • evolution D H u k

theorem frequency_hamiltonian_selfAdjoint (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H) (k : ℝ) :
    star (H + (k : ℂ) • D) = H + (k : ℂ) • D := by
  simp only [star_add, star_smul, hD, hH, Complex.star_def, Complex.conj_ofReal]

theorem evolution_norm_le_one (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H) (u k : ℝ) :
    ‖evolution D H u k‖ ≤ 1 := by
  exact CayleyApproximation.skew_exp_norm_le _
    (HamiltonianStability.generator_skew _ u
      (frequency_hamiltonian_selfAdjoint D H hD hH k))

/-- Frequency perturbations cost only the dissipative-part norm. No norm of
the Hamiltonian part and no exponential stability factor appear. -/
theorem frequency_error (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H) (u k l : ℝ) :
    ‖evolution D H u k - evolution D H u l‖ ≤
      (|u| * ‖D‖) * |k - l| := by
  have h := HamiltonianStability.evolution_error_le
    (H + (k : ℂ) • D) (H + (l : ℂ) • D) u
    (frequency_hamiltonian_selfAdjoint D H hD hH k)
    (frequency_hamiltonian_selfAdjoint D H hD hH l)
  have hdiff : (H + (k : ℂ) • D) - (H + (l : ℂ) • D) =
      ((k - l : ℝ) : ℂ) • D := by
    rw [Complex.ofReal_sub]
    module
  change ‖evolution D H u k - evolution D H u l‖ ≤ _ at h
  rw [hdiff, norm_smul, Complex.norm_real, Real.norm_eq_abs] at h
  calc
    _ ≤ |u| * (|k - l| * ‖D‖) := h
    _ = (|u| * ‖D‖) * |k - l| := by ring

theorem uniform_frequency_error (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H) (T u : ℝ)
    (hu : 0 ≤ u) (huT : u ≤ T) (k l : ℝ) :
    ‖evolution D H u k - evolution D H u l‖ ≤
      (T * ‖D‖) * |k - l| := by
  have h := frequency_error D H hD hH u k l
  rw [abs_of_nonneg hu] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right huT (norm_nonneg D)) (abs_nonneg _))

theorem evolution_continuous (D H : V →L[ℂ] V) (u : ℝ) :
    Continuous (evolution D H u) := by
  letI : NormedAlgebra ℚ (V →L[ℂ] V) := .restrictScalars ℚ ℂ _
  have hFrequency : Continuous (fun k : ℝ => H + (k : ℂ) • D) :=
    continuous_const.add (Complex.continuous_ofReal.smul continuous_const)
  have hGenerator : Continuous
      (fun k : ℝ => (-Complex.I * (u : ℂ)) • (H + (k : ℂ) • D)) :=
    (continuous_const : Continuous
      (fun _ : ℝ => (-Complex.I * (u : ℂ)))).smul hFrequency
  unfold evolution
  exact NormedSpace.exp_continuous.comp hGenerator

theorem weighted_continuous (D H : V →L[ℂ] V) (u : ℝ)
    (f : ℝ → ℂ) (hf : Continuous f) : Continuous (weighted D H u f) := by
  exact hf.smul (evolution_continuous D H u)

/-- A globally bounded Lipschitz kernel gives one explicit Lipschitz constant
for every source duration in the public interval. -/
theorem weighted_error (D H : V →L[ℂ] V)
    (hD : star D = D) (hH : star H = H) (T u : ℝ)
    (f : ℝ → ℂ) (K M : ℝ) (hu : 0 ≤ u) (huT : u ≤ T)
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hLip : ∀ k l, ‖f k - f l‖ ≤ K * |k - l|)
    (hBound : ∀ k, ‖f k‖ ≤ M) (k l : ℝ) :
    ‖weighted D H u f k - weighted D H u f l‖ ≤
      (K + M * T * ‖D‖) * |k - l| := by
  have hsplit : weighted D H u f k - weighted D H u f l =
      (f k - f l) • evolution D H u k +
        f l • (evolution D H u k - evolution D H u l) := by
    unfold weighted
    module
  rw [hsplit]
  calc
    _ ≤ ‖(f k - f l) • evolution D H u k‖ +
        ‖f l • (evolution D H u k - evolution D H u l)‖ := norm_add_le _ _
    _ = ‖f k - f l‖ * ‖evolution D H u k‖ +
        ‖f l‖ * ‖evolution D H u k - evolution D H u l‖ := by
      rw [norm_smul, norm_smul]
    _ ≤ (K * |k - l|) * 1 + M * ((T * ‖D‖) * |k - l|) := by
      apply add_le_add
      · exact mul_le_mul (hLip k l) (evolution_norm_le_one D H hD hH u k)
          (norm_nonneg _) (mul_nonneg hK (abs_nonneg _))
      · exact mul_le_mul (hBound l) (uniform_frequency_error D H hD hH T u hu huT k l)
          (norm_nonneg _) hM
    _ = (K + M * T * ‖D‖) * |k - l| := by ring

section Native

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- The exact native branch, with scalar frequency and duration parameters. -/
def nativeEvolution (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (u k : ℝ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  exp ((-Complex.I * (u : ℂ)) • SparseStateOverlap.matrixOperator
    (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k))

def nativeWeighted (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (u : ℝ) (f : ℝ → ℂ) (k : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  f k • nativeEvolution D x u k

theorem nativeEvolution_eq_evolution (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (u k : ℝ) :
    nativeEvolution D x u k =
      evolution (ODEHermitianReduction.dissipativePart
        (SparseStateOverlap.matrixOperator (D.matrix x)))
        (ODEHermitianReduction.hamiltonianPart
          (SparseStateOverlap.matrixOperator (D.matrix x))) u k := by
  unfold nativeEvolution evolution
  rw [ODEMatrixEnergy.matrixOperator_lchsHamiltonian,
    ODEHermitianReduction.lchsHamiltonian, add_comm]

theorem nativeEvolution_eq_branchEvolution {ι : Type*} [Fintype ι]
    (D : NativeSparseBlockEncoding.Data X n Z s) (k u : ι → ℝ)
    (x : X) (i : ι) :
    nativeEvolution D x (u i) (k i) = ODENativeLCU.branchEvolution D k u x i := rfl

/-- The original sparse-data bound is sufficient for a public frequency mesh.
Its coarseness affects free grid size, not the native matrix-query count. -/
theorem native_dissipative_norm_le (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) :
    ‖ODEHermitianReduction.dissipativePart
      (SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ (s : ℝ) * D.scale := by
  have hM : ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤
      (s : ℝ) * D.scale := by
    simpa only [ODEPublicSourceMesh.generator, norm_neg] using
      ODEPublicSourceMesh.norm_generator_le D x
  exact (ODEHermitianReduction.norm_dissipativePart_le _).trans hM

theorem native_evolution_norm_le_one (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (u k : ℝ) : ‖nativeEvolution D x u k‖ ≤ 1 := by
  rw [nativeEvolution_eq_evolution]
  exact evolution_norm_le_one _ _
    (ODEHermitianReduction.dissipativePart_selfAdjoint _)
    (ODEHermitianReduction.hamiltonianPart_selfAdjoint _) u k

theorem native_evolution_continuous (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (u : ℝ) : Continuous (nativeEvolution D x u) := by
  have heq : nativeEvolution D x u =
      evolution (ODEHermitianReduction.dissipativePart
        (SparseStateOverlap.matrixOperator (D.matrix x)))
        (ODEHermitianReduction.hamiltonianPart
          (SparseStateOverlap.matrixOperator (D.matrix x))) u := by
    funext k
    exact nativeEvolution_eq_evolution D x u k
  rw [heq]
  exact evolution_continuous _ _ _

theorem native_weighted_continuous (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (u : ℝ) (f : ℝ → ℂ) (hf : Continuous f) :
    Continuous (nativeWeighted D x u f) := by
  exact hf.smul (native_evolution_continuous D x u)

/-- One public scalar bounds every input matrix and every retained duration. -/
theorem native_weighted_error (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (T u : ℝ) (f : ℝ → ℂ) (K M : ℝ)
    (hu : 0 ≤ u) (huT : u ≤ T) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hLip : ∀ k l, ‖f k - f l‖ ≤ K * |k - l|)
    (hBound : ∀ k, ‖f k‖ ≤ M) (k l : ℝ) :
    ‖nativeWeighted D x u f k - nativeWeighted D x u f l‖ ≤
      (K + M * T * ((s : ℝ) * D.scale)) * |k - l| := by
  have h := weighted_error
    (ODEHermitianReduction.dissipativePart
      (SparseStateOverlap.matrixOperator (D.matrix x)))
    (ODEHermitianReduction.hamiltonianPart
      (SparseStateOverlap.matrixOperator (D.matrix x)))
    (ODEHermitianReduction.dissipativePart_selfAdjoint _)
    (ODEHermitianReduction.hamiltonianPart_selfAdjoint _)
    T u f K M hu huT hK hM hLip hBound k l
  have hEq (q : ℝ) : nativeWeighted D x u f q =
      weighted (ODEHermitianReduction.dissipativePart
        (SparseStateOverlap.matrixOperator (D.matrix x)))
        (ODEHermitianReduction.hamiltonianPart
          (SparseStateOverlap.matrixOperator (D.matrix x))) u f q := by
    unfold nativeWeighted weighted
    rw [nativeEvolution_eq_evolution]
  rw [hEq k, hEq l]
  exact h.trans (mul_le_mul_of_nonneg_right
    (add_le_add (le_refl K)
      (mul_le_mul_of_nonneg_left (native_dissipative_norm_le D x)
        (mul_nonneg hM (hu.trans huT)))) (abs_nonneg _))

end Native
end
end SparseHamiltonian.ODEWeightedLCHS
