import SparseLinearSystems.Foundations.HilbertRegularization

/-!
# The augmented Hamiltonian on Hilbert direct sums

For an invertible `M` and a vector `β`, the augmented row `[M, -c β]` acts on
`RightSpace V = V ⊕ ℂ`, and the Hermitian augmentation
`[[0, [M, -cβ]], [[M, -cβ]†, 0]]` acts on `FullSpace V = V ⊕ RightSpace V`
(`hamiltonian`, equation `qls:eq:augmented`).  Its kernel is the line through
the generator `(0, (c M⁻¹ β, 1))` (`kernel_eq_span`), with the normalized
generator in `normalizedGenerator`.
-/

namespace SparseLinearSystems.HilbertAugmentation

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The solution register together with the appended scalar coordinate. -/
abbrev RightSpace (V : Type*) := WithLp 2 (V × ℂ)

/-- Left and right sectors of the actual augmented Hermitian matrix. -/
abbrev FullSpace (V : Type*) := WithLp 2 (V × RightSpace V)

/-- Scalar-to-vector map for the appended column. -/
def ray (v : V) : ℂ →L[ℂ] V :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => z • v
      map_add' := by intro z w; exact add_smul z w v
      map_smul' := by
        intro z w
        simp only [RingHom.id_apply, smul_eq_mul, smul_smul] }

@[simp] theorem ray_apply (v : V) (z : ℂ) : ray v z = z • v := rfl

/-- Continuous augmented row `[M, -c β]` on the genuine Hilbert sum. -/
def column (M : V ≃L[ℂ] V) (β : V) (c : ℂ) : RightSpace V →L[ℂ] V :=
  M.toContinuousLinearMap ∘L WithLp.fstL 2 ℂ V ℂ -
    ray (c • β) ∘L WithLp.sndL 2 ℂ V ℂ

@[simp] theorem column_apply (M : V ≃L[ℂ] V) (β : V) (c : ℂ)
    (x : RightSpace V) : column M β c x = M x.fst - x.snd • (c • β) := rfl

theorem column_surjective (M : V ≃L[ℂ] V) (β : V) (c : ℂ) :
    Function.Surjective (column M β c) := by
  intro y
  refine ⟨WithLp.toLp 2 (M.symm y, (0 : ℂ)), ?_⟩
  change M (M.symm y) - (0 : ℂ) • (c • β) = y
  rw [M.apply_symm_apply, zero_smul, sub_zero]

/-- The kernel equation of `Augmentation.column_eq_zero_iff` on the Hilbert
direct sum. -/
theorem column_eq_zero_iff (M : V ≃L[ℂ] V) (β : V) (c : ℂ)
    (x : RightSpace V) :
    column M β c x = 0 ↔ x.fst = x.snd • (c • M.symm β) := by
  exact Augmentation.column_eq_zero_iff M.toLinearEquiv β c (x.fst, x.snd)

/-- Full augmented null vector with appended coordinate one. -/
def generator (M : V ≃L[ℂ] V) (β : V) (c : ℂ) : FullSpace V :=
  WithLp.toLp 2 (0, WithLp.toLp 2 (c • M.symm β, (1 : ℂ)))

/-- A convenient explicit parameterization of the full null line. -/
def parameter (M : V ≃L[ℂ] V) (β : V) (c z : ℂ) : FullSpace V :=
  WithLp.toLp 2 (0, WithLp.toLp 2 (z • (c • M.symm β), z))

theorem parameter_eq_smul_generator (M : V ≃L[ℂ] V) (β : V) (c z : ℂ) :
    parameter M β c z = z • generator M β c := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (0 : V) = z • (0 : V)
    exact (smul_zero z).symm
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · rfl
    · change z = z * 1
      exact (mul_one z).symm

theorem generator_ne_zero (M : V ≃L[ℂ] V) (β : V) (c : ℂ) :
    generator M β c ≠ 0 := by
  intro h
  have hz := congrArg (fun x : FullSpace V => x.snd.snd) h
  exact one_ne_zero (show (1 : ℂ) = 0 from hz)

theorem parameter_injective (M : V ≃L[ℂ] V) (β : V) (c : ℂ) :
    Function.Injective (parameter M β c) := by
  intro z w h
  exact congrArg (fun x : FullSpace V => x.snd.snd) h

/-- The normalization denominator uses the Hilbert norm, not a product sup
norm. No normalization assumption on β is needed for this identity. -/
theorem generator_norm_sq (M : V ≃L[ℂ] V) (β : V) (c : ℂ) :
    ‖generator M β c‖ ^ 2 = ‖c‖ ^ 2 * ‖M.symm β‖ ^ 2 + 1 := by
  simp only [generator, WithLp.prod_norm_sq_eq_of_L2, WithLp.fst, WithLp.snd,
    norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add, norm_smul,
    norm_one, one_pow, mul_pow]

/-- Substituting the reciprocal norm guess gives the manuscript's squared
normalization denominator. -/
theorem generator_norm_sq_reciprocal (M : V ≃L[ℂ] V) (β : V)
    (r : ℝ) (hr : 0 < r) :
    ‖generator M β ((r : ℂ)⁻¹)‖ ^ 2 = (‖M.symm β‖ / r) ^ 2 + 1 := by
  rw [generator_norm_sq, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr, div_eq_mul_inv, mul_pow]
  ring

/-- The corresponding normalized kernel state. -/
def normalizedGenerator (M : V ≃L[ℂ] V) (β : V) (c : ℂ) : FullSpace V :=
  ((‖generator M β c‖ : ℂ)⁻¹) • generator M β c

theorem normalizedGenerator_norm (M : V ≃L[ℂ] V) (β : V) (c : ℂ) :
    ‖normalizedGenerator M β c‖ = 1 := by
  rw [normalizedGenerator, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (generator_ne_zero M β c))

section Adjoint

variable [CompleteSpace V]

/-- Surjectivity of the augmented row rules out any left-sector zero mode. -/
theorem column_adjoint_eq_zero_iff (M : V ≃L[ℂ] V) (β : V) (c : ℂ) (y : V) :
    (ContinuousLinearMap.adjoint (column M β c)) y = 0 ↔ y = 0 := by
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := column_surjective M β c y
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    calc
      inner ℂ y y = inner ℂ (column M β c x) y := by rw [hx]
      _ = inner ℂ x ((ContinuousLinearMap.adjoint (column M β c)) y) :=
        (adjoint_inner_right (column M β c) x y).symm
      _ = 0 := by rw [hy, inner_zero_right]
  · rintro rfl
    exact map_zero _

theorem column_adjoint_injective (M : V ≃L[ℂ] V) (β : V) (c : ℂ) :
    Function.Injective ((ContinuousLinearMap.adjoint (column M β c))) := by
  intro x y h
  apply sub_eq_zero.mp
  apply (column_adjoint_eq_zero_iff M β c (x - y)).mp
  rw [map_sub, h, sub_self]

/-- The actual Hermitian augmentation, with the continuous adjoint in its
lower-left block. -/
def hamiltonian (M : V ≃L[ℂ] V) (β : V) (c : ℂ) :
    FullSpace V →L[ℂ] FullSpace V :=
  HilbertBlocks.blockMap 0 (column M β c) (ContinuousLinearMap.adjoint (column M β c)) 0

@[simp] theorem hamiltonian_apply (M : V ≃L[ℂ] V) (β : V) (c : ℂ)
    (x : FullSpace V) :
    hamiltonian M β c x =
      WithLp.toLp 2 (column M β c x.snd, (ContinuousLinearMap.adjoint (column M β c)) x.fst) := by
  simp only [hamiltonian, HilbertBlocks.blockMap_apply, zero_apply, zero_add, add_zero]

theorem hamiltonian_selfadjoint (M : V ≃L[ℂ] V) (β : V) (c : ℂ) :
    (ContinuousLinearMap.adjoint (hamiltonian M β c)) = hamiltonian M β c := by
  simp only [hamiltonian, HilbertBlocks.block_adjoint, map_zero, adjoint_adjoint]

/-- Both sector equations are discharged: the left sector vanishes by
surjectivity, and the right sector is the explicit augmented solution. -/
theorem hamiltonian_eq_zero_iff (M : V ≃L[ℂ] V) (β : V) (c : ℂ)
    (x : FullSpace V) :
    hamiltonian M β c x = 0 ↔
      x.fst = 0 ∧ x.snd.fst = x.snd.snd • (c • M.symm β) := by
  constructor
  · intro h
    rw [hamiltonian_apply] at h
    have hC := congrArg (fun y : FullSpace V => y.fst) h
    have hAdj := congrArg (fun y : FullSpace V => y.snd) h
    change column M β c x.snd = 0 at hC
    change (ContinuousLinearMap.adjoint (column M β c)) x.fst = 0 at hAdj
    exact ⟨(column_adjoint_eq_zero_iff M β c x.fst).mp hAdj,
      (column_eq_zero_iff M β c x.snd).mp hC⟩
  · rintro ⟨hLeft, hRight⟩
    rw [hamiltonian_apply]
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact (column_eq_zero_iff M β c x.snd).mpr hRight
    · change (ContinuousLinearMap.adjoint (column M β c)) x.fst = 0
      rw [hLeft, map_zero]

theorem hamiltonian_parameter (M : V ≃L[ℂ] V) (β : V) (c z : ℂ) :
    hamiltonian M β c (parameter M β c z) = 0 :=
  (hamiltonian_eq_zero_iff M β c (parameter M β c z)).mpr ⟨rfl, rfl⟩

theorem hamiltonian_generator (M : V ≃L[ℂ] V) (β : V) (c : ℂ) :
    hamiltonian M β c (generator M β c) = 0 := by
  apply (hamiltonian_eq_zero_iff M β c (generator M β c)).mpr
  constructor
  · rfl
  · change c • M.symm β = (1 : ℂ) • (c • M.symm β)
    exact (one_smul ℂ _).symm

theorem hamiltonian_normalizedGenerator (M : V ≃L[ℂ] V) (β : V) (c : ℂ) :
    hamiltonian M β c (normalizedGenerator M β c) = 0 := by
  rw [normalizedGenerator, map_smul, hamiltonian_generator, smul_zero]

theorem kernel_parameterization (M : V ≃L[ℂ] V) (β : V) (c : ℂ)
    (x : FullSpace V) :
    hamiltonian M β c x = 0 ↔ x = parameter M β c x.snd.snd := by
  constructor
  · intro h
    obtain ⟨hLeft, hRight⟩ := (hamiltonian_eq_zero_iff M β c x).mp h
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact hLeft
    · apply WithLp.ofLp_injective 2
      apply Prod.ext
      · exact hRight
      · rfl
  · intro h
    rw [h]
    exact hamiltonian_parameter M β c x.snd.snd

/-- Exact uniqueness of the scalar parameter, for the full Hermitian
augmentation rather than only its rectangular row. -/
theorem kernel_unique_parameter (M : V ≃L[ℂ] V) (β : V) (c : ℂ)
    (x : FullSpace V) :
    hamiltonian M β c x = 0 ↔ ∃! z : ℂ, parameter M β c z = x := by
  constructor
  · intro h
    have hx := (kernel_parameterization M β c x).mp h
    refine ⟨x.snd.snd, hx.symm, ?_⟩
    intro z hz
    exact parameter_injective M β c (hz.trans hx)
  · rintro ⟨z, hz, _⟩
    rw [← hz]
    exact hamiltonian_parameter M β c z

theorem kernel_eq_span (M : V ≃L[ℂ] V) (β : V) (c : ℂ) :
    LinearMap.ker (hamiltonian M β c).toLinearMap =
      Submodule.span ℂ {generator M β c} := by
  apply le_antisymm
  · intro x hx
    have hx' := (kernel_parameterization M β c x).mp hx
    rw [hx', parameter_eq_smul_generator]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · apply Submodule.span_le.mpr
    intro x hx
    have hx' : x = generator M β c := Set.mem_singleton_iff.mp hx
    rw [hx']
    exact hamiltonian_generator M β c

end Adjoint
end
end SparseLinearSystems.HilbertAugmentation
