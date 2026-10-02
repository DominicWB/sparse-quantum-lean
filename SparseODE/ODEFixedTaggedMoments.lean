import SparseODE.ODETaggedLocators

/-!
# Tagged Cayley moments at a common known boundary

The original sparse locators transport the concrete tagged generator and its
explicit rational inverse to the input-independent preparation. These are
analytic identities for actual operators. Native circuit compilation and the
Gaussian LCHS approximation remain separate obligations.

-/

namespace SparseHamiltonian.ODEFixedTaggedMoments

noncomputable section
open ContinuousLinearMap OracleCircuit CayleyClockInterface
open scoped BigOperators InnerProduct
set_option maxHeartbeats 1000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- Conjugating the actual entry generator removes input dependence from
the public boundary, without changing its physical compression. -/
def generator (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (K : Matrix n n ℂ) (ρ : ℝ) :
    ODETaggedMoments.PrivateSpace n →L[ℂ] ODETaggedMoments.PrivateSpace n :=
  UnitaryCayleyTransport.conjugate (ODETaggedLocators.locator D x)
    (ODETaggedMoments.generator (D.matrix x) K s ρ)

def inverse (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (K : Matrix n n ℂ) (ρ γ : ℝ) :
    ODETaggedMoments.PrivateSpace n →L[ℂ] ODETaggedMoments.PrivateSpace n :=
  UnitaryCayleyTransport.conjugate (ODETaggedLocators.locator D x)
    (ODETaggedCayley.inverse (D.matrix x) K s ρ γ)

def action (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (K : Matrix n n ℂ) (ρ γ : ℝ) :
    ODETaggedMoments.PrivateSpace n →L[ℂ] ODETaggedMoments.PrivateSpace n :=
  UnitaryCayleyTransport.conjugate (ODETaggedLocators.locator D x)
    (ODETaggedCayley.action (D.matrix x) K s ρ γ)

/-- The preparation depends on the supplied public slot embedding only. -/
def boundary (D : NativeSparseBlockEncoding.Data X n Z s) :
    EuclideanSpace ℂ n →L[ℂ] ODETaggedMoments.PrivateSpace n :=
  ODETaggedLocators.fixedBoundary D.slot

theorem boundary_isometry (D : NativeSparseBlockEncoding.Data X n Z s) :
    (boundary D)† ∘L boundary D = 1 :=
  ODETaggedLocators.fixedBoundary_isometry D.slot D.slots_pos

theorem generator_adjoint (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (ρ : ℝ) :
    (generator D x K ρ)† = generator D x K ρ :=
  UnitaryCayleyTransport.conjugate_self_adjoint _ _
    (ODETaggedMoments.generator_adjoint _ _ _ _)

/-- The first moment retains its exact physical scale for every supported
Hermitian target K, including the actual LCHS branches below. -/
theorem compression (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (hHerm : K.IsHermitian) (ρ : ℝ)
    (hK : ∀ i j, D.matrix x i j = 0 → D.matrix x j i = 0 → K i j = 0) :
    (boundary D)† ∘L generator D x K ρ ∘L boundary D =
      ((ρ : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ))⁻¹ •
        SparseStateOverlap.matrixOperator K := by
  unfold generator boundary
  rw [UnitaryCayleyTransport.compression, ODETaggedLocators.locator_boundary]
  exact ODETaggedMoments.generator_compression D.slots_pos _ _ hHerm ρ _ _
    (D.row_covers x) (D.column_covers x) hK

/-- All normalized moment obligations follow from native sparse promises
and row/column energies; no implementation premise is supplied. -/
theorem native_moment_certificate (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (hHerm : K.IsHermitian) (ρ : ℝ) (hρ : 0 < ρ)
    (hK : ∀ i j, D.matrix x i j = 0 → D.matrix x j i = 0 → K i j = 0)
    (hr : ∀ i, ∑ j, ‖K i j‖ ^ 2 ≤ ρ ^ 2)
    (hc : ∀ j, ∑ i, ‖K i j‖ ^ 2 ≤ ρ ^ 2) :
    (boundary D)† ∘L boundary D = 1 ∧
    (generator D x K ρ)† = generator D x K ρ ∧
    ‖generator D x K ρ‖ ≤ Real.sqrt (2 * (s : ℝ)) ∧
    ‖generator D x K ρ ∘L boundary D‖ ≤ 1 ∧
    (boundary D)† ∘L generator D x K ρ ∘L boundary D =
      ((ρ : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ))⁻¹ •
        SparseStateOverlap.matrixOperator K := by
  rcases ODETaggedMoments.native_moment_certificate D x K hHerm ρ hρ hK hr hc with
    ⟨hJ, hSelf, hNorm, hMoment, hCompression⟩
  have hTransport := UnitaryCayleyTransport.moment_certificate
    (ODETaggedLocators.locator D x) (ODETaggedLocators.locator_unitary D x)
    (ODETaggedMoments.generator (D.matrix x) K s ρ)
    (ODETaggedLocators.fixedBoundary D.slot)
    (ODETaggedMoments.boundary (D.rowloc x) (D.colloc x))
    (Real.sqrt (2 * (s : ℝ))) 1 (ODETaggedLocators.locator_boundary D x)
    hJ hSelf hNorm hMoment
  rcases hTransport with ⟨hFree, hAdjoint, hBound, hResponse, hComp⟩
  exact ⟨hFree, hAdjoint, hBound, hResponse, hComp.trans hCompression⟩

/-- The original explicit denominator inverse transports to a right inverse
on the complete fixed-boundary workspace. -/
theorem inverse_right (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (ρ γ : ℝ) :
    (scaled (generator D x K ρ) γ - Complex.I •
      (1 : ODETaggedMoments.PrivateSpace n →L[ℂ] _)) * inverse D x K ρ γ = 1 :=
  UnitaryCayleyTransport.inverse_right _ (ODETaggedLocators.locator_unitary D x)
    _ _ γ (ODETaggedCayley.inverse_right (D.matrix x) K s ρ γ)

theorem inverse_left (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (ρ γ : ℝ) :
    inverse D x K ρ γ * (scaled (generator D x K ρ) γ - Complex.I •
      (1 : ODETaggedMoments.PrivateSpace n →L[ℂ] _)) = 1 :=
  UnitaryCayleyTransport.inverse_left _ (ODETaggedLocators.locator_unitary D x)
    _ _ γ (ODETaggedCayley.inverse_left (D.matrix x) K s ρ γ)

theorem action_unitary (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (ρ γ : ℝ) : IsUnitary (action D x K ρ γ) :=
  UnitaryCayleyTransport.conjugate_unitary _ _ (ODETaggedLocators.locator_unitary D x)
    (ODETaggedCayley.action_unitary (D.matrix x) K s ρ γ)

theorem action_eq_cayley (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (ρ γ : ℝ) :
    action D x K ρ γ = ImprovedCayleyMoments.cayleyAction
      (scaled (generator D x K ρ) γ) (inverse D x K ρ γ) := by
  unfold action generator inverse
  rw [ODETaggedCayley.action_eq_cayley]
  exact UnitaryCayleyTransport.cayleyAction_conjugate _
    (ODETaggedLocators.locator_unitary D x) _ _ γ

/-- The normalization rho sqrt(2s) and the Cayley rescaling cancel in
the simulated exponent. The target is the actual physical branch K. -/
theorem physical_exponent (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (hHerm : K.IsHermitian) (ρ t γ : ℝ)
    (hρ : ρ ≠ 0) (hγ : γ ≠ 0)
    (hK : ∀ i j, D.matrix x i j = 0 → D.matrix x j i = 0 → K i j = 0) :
    (-Complex.I * (time (2 * (s : ℝ)) (ρ * t) γ : ℂ)) •
        compressed (generator D x K ρ) (boundary D) γ =
      (-Complex.I * (t : ℂ)) • SparseStateOverlap.matrixOperator K := by
  rw [rescaled_exponent _ _ _ _ _ hγ, compression D x K hHerm ρ hK, smul_smul]
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hRoot : (Real.sqrt (2 * (s : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < 2 * (s : ℝ))).ne'
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
  congr 1
  simp only [Complex.ofReal_mul]
  field_simp [hRoot, hρC]

/-- A single public radius and separate H/D energy budgets certify every
quadrature node. The fixed preparation is the same for all real k in range. -/
theorem lchs_moment_certificate (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (etaH etaD R k : ℝ) (hH : 0 ≤ etaH) (hD : 0 ≤ etaD)
    (hk : |k| ≤ R) (hρ : 0 < etaH + R * etaD)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) :
    let K := ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k
    let ρ := etaH + R * etaD
    (boundary D)† ∘L boundary D = 1 ∧
    (generator D x K ρ)† = generator D x K ρ ∧
    ‖generator D x K ρ‖ ≤ Real.sqrt (2 * (s : ℝ)) ∧
    ‖generator D x K ρ ∘L boundary D‖ ≤ 1 ∧
    (boundary D)† ∘L generator D x K ρ ∘L boundary D =
      ((ρ : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ))⁻¹ •
        SparseStateOverlap.matrixOperator K := by
  dsimp only
  obtain ⟨hr, hc⟩ := ODEMatrixEnergy.lchs_energies_le_radius (D.matrix x)
    etaH etaD k R hH hD hk hrH hcH hrD hcD
  exact native_moment_certificate D x (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k)
    (ODEMatrixEnergy.lchsHamiltonian_isHermitian (D.matrix x) k)
    (etaH + R * etaD) hρ
    (ODEMatrixEnergy.lchsHamiltonian_eq_zero (D.matrix x) k) hr hc

end
end SparseHamiltonian.ODEFixedTaggedMoments
