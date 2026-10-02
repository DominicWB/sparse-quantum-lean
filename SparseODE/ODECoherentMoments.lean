import SparseODE.ODECoherentActive

/-!
# Moment bounds on the full coherent branch register

The public branch label is part of the Hilbert space. Uniform branch moments
therefore give the same operator bounds on superpositions, with no factor for
the number of LCHS nodes or source durations. This supplies the analytic input
for running one sharp simulator on the direct sum. Its native circuit
connection is still a separate obligation.

-/

namespace SparseHamiltonian.ODECoherentMoments

noncomputable section
open ContinuousLinearMap CoherentQuerySchedule
open scoped BigOperators InnerProduct

variable {ι P V : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem rectangular_adjoint (J : ι → P →L[ℂ] V) :
    (rectangular J)† = rectangular (fun i => (J i)†) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  simp only [ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply,
    rectangular_apply, ContinuousLinearMap.adjoint_inner_left]

omit [Fintype ι] [CompleteSpace P] [CompleteSpace V] in
theorem diagonal_rectangular (G : ι → V →L[ℂ] V) (J : ι → P →L[ℂ] V) :
    WeightedClock.diagonal G ∘L rectangular J =
      rectangular (fun i => G i ∘L J i) := by
  ext v i
  rfl

theorem compression (G : ι → V →L[ℂ] V) (J : ι → P →L[ℂ] V) :
    (rectangular J)† ∘L WeightedClock.diagonal G ∘L rectangular J =
      WeightedClock.diagonal (fun i => (J i)† ∘L G i ∘L J i) := by
  rw [rectangular_adjoint]
  ext v i
  rfl

theorem compressed_diagonal (G : ι → V →L[ℂ] V) (J : ι → P →L[ℂ] V)
    (γ : ℝ) :
    CayleyClockInterface.compressed (WeightedClock.diagonal G) (rectangular J) γ =
      WeightedClock.diagonal (fun i => CayleyClockInterface.compressed (G i) (J i) γ) := by
  unfold CayleyClockInterface.compressed CayleyClockInterface.scaled
  simp only [comp_smul, smul_comp]
  rw [compression]
  ext v i
  rfl

/-- The same norm and first/second boundary moments hold on coherent inputs. -/
theorem moment_certificate (G : ι → V →L[ℂ] V) (J : ι → P →L[ℂ] V)
    (H : ι → P →L[ℂ] P) (Q b : ℝ) (hQ : 0 ≤ Q) (hb : 0 ≤ b)
    (hJ : ∀ i, (J i)† ∘L J i = 1)
    (hSelf : ∀ i, (G i)† = G i)
    (hNorm : ∀ i, ‖G i‖ ≤ Q)
    (hMoment : ∀ i, ‖G i ∘L J i‖ ≤ b)
    (hCompression : ∀ i, (J i)† ∘L G i ∘L J i = H i) :
    (rectangular J)† ∘L rectangular J = 1 ∧
    (WeightedClock.diagonal G)† = WeightedClock.diagonal G ∧
    ‖WeightedClock.diagonal G‖ ≤ Q ∧
    ‖WeightedClock.diagonal G ∘L rectangular J‖ ≤ b ∧
    (rectangular J)† ∘L WeightedClock.diagonal G ∘L rectangular J =
      WeightedClock.diagonal H := by
  refine ⟨rectangular_isometry J hJ, ?_,
    WeightedClock.norm_diagonal_le G Q hQ hNorm, ?_, ?_⟩
  · rw [WeightedClock.diagonal_adjoint]
    congr 1
    funext i
    exact hSelf i
  · rw [diagonal_rectangular]
    exact rectangular_norm_le _ b hb hMoment
  · rw [compression]
    congr 1
    funext i
    exact hCompression i

section Native

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- The exponent of one global simulator is exactly the diagonal family of
physical exponents, with each branch retaining its own source duration. -/
theorem physical_exponent (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (k u : ι → ℝ) (ρ T γ : ℝ)
    (hρ : ρ ≠ 0) (hT : 0 < T) (hγ : γ ≠ 0) :
    let G := fun i => ODECommonDuration.generator D x
      (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)) ρ (u i / T)
    let J := rectangular (fun _ : ι => ODEFixedTaggedMoments.boundary D)
    (-Complex.I * (CayleyClockInterface.time (2 * (s : ℝ)) (ρ * T) γ : ℂ)) •
      CayleyClockInterface.compressed (WeightedClock.diagonal G) J γ =
        WeightedClock.diagonal (fun i => (-Complex.I * (u i : ℂ)) •
          SparseStateOverlap.matrixOperator
            (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i))) := by
  dsimp only
  rw [compressed_diagonal, CoherentQuerySchedule.smul_diagonal]
  congr 1
  funext i
  exact ODECommonDuration.physical_duration_exponent D x
    (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i))
    (ODEMatrixEnergy.lchsHamiltonian_isHermitian (D.matrix x) (k i))
    ρ T γ (u i) hρ hT hγ
    (ODEMatrixEnergy.lchsHamiltonian_eq_zero (D.matrix x) (k i))

/-- A single direct-sum generator covers every retained node and every source
duration. Its boundary depends only on the public sparse slot preparation. -/
theorem lchs_duration_certificate (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (etaH etaD R T : ℝ) (k u : ι → ℝ)
    (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hρ : 0 < etaH + R * etaD)
    (hT : 0 < T) (hk : ∀ i, |k i| ≤ R)
    (hu : ∀ i, 0 ≤ u i) (huT : ∀ i, u i ≤ T)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) :
    let G := fun i => ODECommonDuration.generator D x
      (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i))
      (etaH + R * etaD) (u i / T)
    let J := rectangular (fun _ : ι => ODEFixedTaggedMoments.boundary D)
    J† ∘L J = 1 ∧
    (WeightedClock.diagonal G)† = WeightedClock.diagonal G ∧
    ‖WeightedClock.diagonal G‖ ≤ Real.sqrt (2 * (s : ℝ)) ∧
    ‖WeightedClock.diagonal G ∘L J‖ ≤ 1 ∧
    J† ∘L WeightedClock.diagonal G ∘L J = WeightedClock.diagonal (fun i =>
      (((u i / T : ℝ) : ℂ) *
        (((etaH + R * etaD : ℝ) : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ))⁻¹) •
          SparseStateOverlap.matrixOperator
            (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i))) := by
  dsimp only
  have h := fun i => ODECommonDuration.lchs_duration_moment_certificate D x
    etaH etaD R (k i) (u i) T hH hD (hk i) hρ (hu i) (huT i) hT
    hrH hcH hrD hcD
  exact moment_certificate _ _ _ _ _ (Real.sqrt_nonneg _) (by norm_num)
    (fun i => (h i).1) (fun i => (h i).2.1)
    (fun i => (h i).2.2.1) (fun i => (h i).2.2.2.1)
    (fun i => (h i).2.2.2.2)

end Native
end
end SparseHamiltonian.ODECoherentMoments
