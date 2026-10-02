import SparseODE.ODENativeActive

/-!
# Duration scaling at one fixed simulation horizon

A duration fraction in [0,1] scales the actual tagged generator, while the
boundary, the moment bounds and the global Cayley parameter remain common.
The corresponding Cayley circuit uses the local parameter `γ * a`; no inverse
of `a` occurs, so zero-duration branches are included. These are operator
identities and moment estimates, not an assumed coherent SELECT circuit.

-/

namespace SparseHamiltonian.ODECommonDuration

noncomputable section
open ContinuousLinearMap OracleCircuit CayleyClockInterface
open scoped BigOperators InnerProduct
set_option maxHeartbeats 1000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- A branch of duration `a * T` is simulated over the common horizon `T`. -/
def generator (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (K : Matrix n n ℂ) (ρ a : ℝ) :
    ODETaggedMoments.PrivateSpace n →L[ℂ] ODETaggedMoments.PrivateSpace n :=
  scaled (ODEFixedTaggedMoments.generator D x K ρ) a

/-- The explicit inverse is evaluated at the local Cayley parameter. -/
def inverse (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (K : Matrix n n ℂ) (ρ γ a : ℝ) :
    ODETaggedMoments.PrivateSpace n →L[ℂ] ODETaggedMoments.PrivateSpace n :=
  ODEFixedTaggedMoments.inverse D x K ρ (γ * a)

/-- This is the exact action already implemented by the native circuit. -/
def action (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (K : Matrix n n ℂ) (ρ γ a : ℝ) :
    ODETaggedMoments.PrivateSpace n →L[ℂ] ODETaggedMoments.PrivateSpace n :=
  ODEFixedTaggedMoments.action D x K ρ (γ * a)

theorem scaled_generator (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (ρ γ a : ℝ) :
    scaled (generator D x K ρ a) γ =
      scaled (ODEFixedTaggedMoments.generator D x K ρ) (γ * a) := by
  simp only [generator, scaled, smul_smul, Complex.ofReal_mul]

theorem generator_adjoint (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (ρ a : ℝ) :
    (generator D x K ρ a)† = generator D x K ρ a :=
  scaled_self_adjoint _ a (ODEFixedTaggedMoments.generator_adjoint D x K ρ)

theorem generator_norm (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (ρ a : ℝ) (ha : 0 ≤ a) (haOne : a ≤ 1)
    (hNorm : ‖ODEFixedTaggedMoments.generator D x K ρ‖ ≤
      Real.sqrt (2 * (s : ℝ))) :
    ‖generator D x K ρ a‖ ≤ Real.sqrt (2 * (s : ℝ)) := by
  calc
    ‖generator D x K ρ a‖ ≤ a * Real.sqrt (2 * (s : ℝ)) :=
      scaled_norm _ _ a ha hNorm
    _ ≤ 1 * Real.sqrt (2 * (s : ℝ)) :=
      mul_le_mul_of_nonneg_right haOne (Real.sqrt_nonneg _)
    _ = Real.sqrt (2 * (s : ℝ)) := one_mul _

theorem boundary_norm (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (ρ a : ℝ) (ha : 0 ≤ a) (haOne : a ≤ 1)
    (hMoment : ‖ODEFixedTaggedMoments.generator D x K ρ ∘L
      ODEFixedTaggedMoments.boundary D‖ ≤ 1) :
    ‖generator D x K ρ a ∘L ODEFixedTaggedMoments.boundary D‖ ≤ 1 :=
  (scaled_boundary_norm _ _ a ha hMoment).trans haOne

theorem compression (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (hHerm : K.IsHermitian) (ρ a : ℝ)
    (hK : ∀ i j, D.matrix x i j = 0 → D.matrix x j i = 0 → K i j = 0) :
    (ODEFixedTaggedMoments.boundary D)† ∘L generator D x K ρ a ∘L
      ODEFixedTaggedMoments.boundary D =
      ((a : ℂ) * ((ρ : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ))⁻¹) •
        SparseStateOverlap.matrixOperator K := by
  simp only [generator, scaled, comp_smul, smul_comp]
  rw [ODEFixedTaggedMoments.compression D x K hHerm ρ hK, smul_smul]

/-- Every duration fraction has the same upper moment bounds and preparation. -/
theorem native_moment_certificate (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (hHerm : K.IsHermitian) (ρ a : ℝ)
    (hρ : 0 < ρ) (ha : 0 ≤ a) (haOne : a ≤ 1)
    (hK : ∀ i j, D.matrix x i j = 0 → D.matrix x j i = 0 → K i j = 0)
    (hr : ∀ i, ∑ j, ‖K i j‖ ^ 2 ≤ ρ ^ 2)
    (hc : ∀ j, ∑ i, ‖K i j‖ ^ 2 ≤ ρ ^ 2) :
    (ODEFixedTaggedMoments.boundary D)† ∘L ODEFixedTaggedMoments.boundary D = 1 ∧
    (generator D x K ρ a)† = generator D x K ρ a ∧
    ‖generator D x K ρ a‖ ≤ Real.sqrt (2 * (s : ℝ)) ∧
    ‖generator D x K ρ a ∘L ODEFixedTaggedMoments.boundary D‖ ≤ 1 ∧
    (ODEFixedTaggedMoments.boundary D)† ∘L generator D x K ρ a ∘L
      ODEFixedTaggedMoments.boundary D =
      ((a : ℂ) * ((ρ : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ))⁻¹) •
        SparseStateOverlap.matrixOperator K := by
  rcases ODEFixedTaggedMoments.native_moment_certificate D x K hHerm ρ hρ hK hr hc with
    ⟨hJ, _, hNorm, hMoment, _⟩
  exact ⟨hJ, generator_adjoint D x K ρ a,
    generator_norm D x K ρ a ha haOne hNorm,
    boundary_norm D x K ρ a ha haOne hMoment,
    compression D x K hHerm ρ a hK⟩

theorem inverse_right (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (ρ γ a : ℝ) :
    (scaled (generator D x K ρ a) γ - Complex.I •
      (1 : ODETaggedMoments.PrivateSpace n →L[ℂ] _)) * inverse D x K ρ γ a = 1 := by
  rw [scaled_generator]
  exact ODEFixedTaggedMoments.inverse_right D x K ρ (γ * a)

theorem inverse_left (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (ρ γ a : ℝ) :
    inverse D x K ρ γ a * (scaled (generator D x K ρ a) γ - Complex.I •
      (1 : ODETaggedMoments.PrivateSpace n →L[ℂ] _)) = 1 := by
  rw [scaled_generator]
  exact ODEFixedTaggedMoments.inverse_left D x K ρ (γ * a)

theorem action_unitary (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (ρ γ a : ℝ) : IsUnitary (action D x K ρ γ a) :=
  ODEFixedTaggedMoments.action_unitary D x K ρ (γ * a)

theorem action_eq_cayley (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (ρ γ a : ℝ) :
    action D x K ρ γ a = ImprovedCayleyMoments.cayleyAction
      (scaled (generator D x K ρ a) γ) (inverse D x K ρ γ a) := by
  rw [scaled_generator]
  exact ODEFixedTaggedMoments.action_eq_cayley D x K ρ (γ * a)

/-- The one global simulator time produces the branch's physical duration.
Only the global Cayley parameter must be nonzero; `a = 0` is permitted. -/
theorem physical_exponent (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (hHerm : K.IsHermitian) (ρ T γ a : ℝ)
    (hρ : ρ ≠ 0) (hγ : γ ≠ 0)
    (hK : ∀ i j, D.matrix x i j = 0 → D.matrix x j i = 0 → K i j = 0) :
    (-Complex.I * (time (2 * (s : ℝ)) (ρ * T) γ : ℂ)) •
        compressed (generator D x K ρ a) (ODEFixedTaggedMoments.boundary D) γ =
      (-Complex.I * ((a * T : ℝ) : ℂ)) • SparseStateOverlap.matrixOperator K := by
  rw [rescaled_exponent _ _ _ _ _ hγ, compression D x K hHerm ρ a hK, smul_smul]
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hRoot : (Real.sqrt (2 * (s : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < 2 * (s : ℝ))).ne'
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ
  congr 1
  simp only [Complex.ofReal_mul]
  field_simp [hRoot, hρC]

/-- This scalar choice is valid for every source duration in the horizon. -/
theorem duration_fraction_bounds (u T : ℝ) (hu : 0 ≤ u) (huT : u ≤ T) (hT : 0 < T) :
    0 ≤ u / T ∧ u / T ≤ 1 :=
  ⟨div_nonneg hu hT.le, (div_le_one hT).mpr huT⟩

theorem physical_duration_exponent (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (K : Matrix n n ℂ) (hHerm : K.IsHermitian) (ρ T γ u : ℝ)
    (hρ : ρ ≠ 0) (hT : 0 < T) (hγ : γ ≠ 0)
    (hK : ∀ i j, D.matrix x i j = 0 → D.matrix x j i = 0 → K i j = 0) :
    (-Complex.I * (time (2 * (s : ℝ)) (ρ * T) γ : ℂ)) •
        compressed (generator D x K ρ (u / T)) (ODEFixedTaggedMoments.boundary D) γ =
      (-Complex.I * (u : ℂ)) • SparseStateOverlap.matrixOperator K := by
  simpa only [div_mul_cancel₀ u hT.ne'] using
    physical_exponent D x K hHerm ρ T γ (u / T) hρ hγ hK

/-- Both the LCHS node and the source duration vary under one public radius.
This theorem supplies the common analytic promises, independently of how
the finite branch labels are represented by the coherent query schedule. -/
theorem lchs_duration_moment_certificate (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (etaH etaD R k u T : ℝ) (hH : 0 ≤ etaH) (hD : 0 ≤ etaD)
    (hk : |k| ≤ R) (hρ : 0 < etaH + R * etaD)
    (hu : 0 ≤ u) (huT : u ≤ T) (hT : 0 < T)
    (hrH : ∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) :
    let K := ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k
    let ρ := etaH + R * etaD
    let a := u / T
    (ODEFixedTaggedMoments.boundary D)† ∘L ODEFixedTaggedMoments.boundary D = 1 ∧
    (generator D x K ρ a)† = generator D x K ρ a ∧
    ‖generator D x K ρ a‖ ≤ Real.sqrt (2 * (s : ℝ)) ∧
    ‖generator D x K ρ a ∘L ODEFixedTaggedMoments.boundary D‖ ≤ 1 ∧
    (ODEFixedTaggedMoments.boundary D)† ∘L generator D x K ρ a ∘L
      ODEFixedTaggedMoments.boundary D =
      ((a : ℂ) * ((ρ : ℂ) * (Real.sqrt (2 * (s : ℝ)) : ℂ))⁻¹) •
        SparseStateOverlap.matrixOperator K := by
  dsimp only
  obtain ⟨hr, hc⟩ := ODEMatrixEnergy.lchs_energies_le_radius (D.matrix x)
    etaH etaD k R hH hD hk hrH hcH hrD hcD
  obtain ⟨ha, haOne⟩ := duration_fraction_bounds u T hu huT hT
  exact native_moment_certificate D x (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k)
    (ODEMatrixEnergy.lchsHamiltonian_isHermitian (D.matrix x) k)
    (etaH + R * etaD) (u / T) hρ ha haOne
    (ODEMatrixEnergy.lchsHamiltonian_eq_zero (D.matrix x) k) hr hc

end
end SparseHamiltonian.ODECommonDuration
