import SparseHamiltonian.EncodedMultiOracle

/-!
# Fixed uniform preparation of the original sparse slots

The slot embedding and its amplitudes are independent of the unknown matrix.
The normalized input contains every supplied slot, including padded zero
entries. No filtered locator or row-sum oracle is used.
-/

namespace SparseHamiltonian.UniformSlotPreparation

noncomputable section
open ContinuousLinearMap
open scoped BigOperators InnerProduct

variable {I N : Type*} [Fintype I] [Fintype N] [DecidableEq N] {s : ℕ}

/-- The fixed set of valid slot labels. -/
def support (slot : Fin s ↪ N) : Finset N := Finset.univ.image slot

/-- Uniform amplitude on the original s slots. -/
def weight (s : ℕ) : ℂ := (Real.sqrt (s : ℝ) : ℂ)⁻¹

/-- The uniform slot vector is zero outside the supplied labels. -/
def amplitude (slot : Fin s ↪ N) (j : N) : ℂ :=
  if j ∈ support slot then weight s else 0

omit [Fintype N] in
@[simp] theorem support_card (slot : Fin s ↪ N) : (support slot).card = s := by
  rw [support, Finset.card_image_of_injective _ slot.injective]
  simp

theorem weight_normalization (hs : 0 < s) : (s : ℝ) * ‖weight s‖ ^ 2 = 1 := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hsq := Real.sq_sqrt hs'.le
  have hn := (Real.sqrt_pos.mpr hs').ne'
  simp only [weight, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  field_simp
  exact hsq.symm

theorem amplitude_normalization (slot : Fin s ↪ N) (hs : 0 < s) :
    ∑ j, ‖amplitude slot j‖ ^ 2 = 1 := by
  calc
    ∑ j, ‖amplitude slot j‖ ^ 2 =
        ∑ j ∈ support slot, ‖weight s‖ ^ 2 := by
      simp only [amplitude, apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_zero, zero_pow
        (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_ite_mem, Finset.univ_inter]
    _ = (s : ℝ) * ‖weight s‖ ^ 2 := by simp
    _ = 1 := weight_normalization hs

/-- Tensor the address state with the fixed uniform slot state. -/
def embedding (slot : Fin s ↪ N) (hs : 0 < s) :
    EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (I × N) where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (fun b => v b.1 * amplitude slot b.2)
      map_add' := by
        intro v w
        apply PiLp.ext
        intro b
        change (v b.1 + w b.1) * amplitude slot b.2 =
          v b.1 * amplitude slot b.2 + w b.1 * amplitude slot b.2
        exact add_mul _ _ _
      map_smul' := by
        intro z v
        apply PiLp.ext
        intro b
        change (z * v b.1) * amplitude slot b.2 = z * (v b.1 * amplitude slot b.2)
        exact mul_assoc _ _ _ }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2]
    change (∑ b : I × N, ‖v b.1 * amplitude slot b.2‖ ^ 2) = ∑ i, ‖v i‖ ^ 2
    simp only [Fintype.sum_prod_type, norm_mul, mul_pow]
    simp only [← Finset.mul_sum, amplitude_normalization slot hs, mul_one]

@[simp] theorem embedding_apply (slot : Fin s ↪ N) (hs : 0 < s)
    (v : EuclideanSpace ℂ I) (i : I) (j : N) :
    embedding slot hs v (i, j) = v i * amplitude slot j := rfl

theorem embedding_adjoint_comp (slot : Fin s ↪ N) (hs : 0 < s) :
    (embedding (I := I) slot hs).toContinuousLinearMap† ∘L
      (embedding (I := I) slot hs).toContinuousLinearMap = 1 :=
  LinearIsometry.adjoint_comp_self _

omit [Fintype N] in
/-- Injective slot labels make a finite basis sum select a single amplitude. -/
theorem sum_slot_ite (slot : Fin s ↪ N) (j : N) (c : ℂ) :
    (∑ k, if slot k = j then c else 0) = if j ∈ support slot then c else 0 := by
  classical
  by_cases hj : j ∈ support slot
  · obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hj
    rw [if_pos hj]
    rw [Finset.sum_eq_single k]
    · simp [hk]
    · intro l _ hl
      have hn : slot l ≠ j := by
        intro h
        exact hl (slot.injective (h.trans hk.symm))
      simp [hn]
    · simp
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro k _
    have hn : slot k ≠ j := by
      intro h
      exact hj (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, h⟩)
    simp [hn]

/-- Explicit computational-basis expansion, suitable for a valid-slot promise
on an otherwise arbitrary in-place location unitary. -/
theorem embedding_eq_sum [DecidableEq I] (slot : Fin s ↪ N) (hs : 0 < s)
    (v : EuclideanSpace ℂ I) :
    embedding slot hs v =
      ∑ i, ∑ k : Fin s, EuclideanSpace.single (i, slot k) (v i * weight s) := by
  classical
  apply PiLp.ext
  rintro ⟨i, j⟩
  simp only [embedding_apply, WithLp.ofLp_sum, Finset.sum_apply, PiLp.single_apply]
  have hsum : (∑ a : I, ∑ k : Fin s,
      if (i, j) = (a, slot k) then v a * weight s else 0) =
      ∑ k : Fin s, if slot k = j then v i * weight s else 0 := by
    rw [Finset.sum_eq_single i]
    · apply Finset.sum_congr rfl
      intro k _
      simp [eq_comm]
    · intro a _ ha
      apply Finset.sum_eq_zero
      intro k _
      simp [show i ≠ a from Ne.symm ha]
    · simp
  rw [hsum, sum_slot_ite]
  by_cases hj : j ∈ support slot <;> simp [amplitude, hj]

end
end SparseHamiltonian.UniformSlotPreparation
