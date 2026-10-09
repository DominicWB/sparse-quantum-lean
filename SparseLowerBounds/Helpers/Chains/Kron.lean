import SparseLowerBounds.Hamiltonian.Gadget

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Helpers for `Hamiltonian/Chains`: operators of matrices, `B ⊗ I`, conjugation

Generic facts about `SparseStateOverlap.matrixOperator`, the Kronecker product
with the identity on a register, and unitary conjugation of the Schrödinger
evolution `evolve`.
-/

namespace SparseLowerBounds.Helpers.Chains

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open SparseLowerBounds.Hamiltonian
open Kronecker

variable {S : Type*} [Fintype S] [DecidableEq S] {m : ℕ}

theorem mO_eq (M : Matrix S S ℂ) :
    SparseHamiltonian.SparseStateOverlap.matrixOperator M =
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S) M := by
  ext v i
  rw [SparseHamiltonian.SparseStateOverlap.matrixOperator_apply]
  rfl

theorem mO_mul (A B : Matrix S S ℂ) :
    SparseHamiltonian.SparseStateOverlap.matrixOperator (A * B) =
      SparseHamiltonian.SparseStateOverlap.matrixOperator A *
        SparseHamiltonian.SparseStateOverlap.matrixOperator B := by
  rw [mO_eq, mO_eq, mO_eq, map_mul]

theorem mO_conjTranspose (A : Matrix S S ℂ) :
    SparseHamiltonian.SparseStateOverlap.matrixOperator Aᴴ =
      star (SparseHamiltonian.SparseStateOverlap.matrixOperator A) := by
  rw [mO_eq, mO_eq, ← Matrix.star_eq_conjTranspose, map_star]

theorem mO_one : SparseHamiltonian.SparseStateOverlap.matrixOperator (1 : Matrix S S ℂ) = 1 := by
  rw [mO_eq, map_one]

/-- The register slice `a` of a vector on `S × Fin m`. -/
def slice (a : Fin m) (v : EuclideanSpace ℂ (S × Fin m)) : EuclideanSpace ℂ S :=
  WithLp.toLp 2 fun i => v (i, a)

omit [Fintype S] [DecidableEq S] in
theorem kron_eq (A : Matrix S S ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.kronecker A B = A ⊗ₖ B := rfl

omit [DecidableEq S] in
theorem mO_kronecker_one_apply (A : Matrix S S ℂ) (v : EuclideanSpace ℂ (S × Fin m))
    (p : S × Fin m) :
    SparseHamiltonian.SparseStateOverlap.matrixOperator
        (Matrix.kronecker A (1 : Matrix (Fin m) (Fin m) ℂ)) v p =
      SparseHamiltonian.SparseStateOverlap.matrixOperator A (slice p.2 v) p.1 := by
  obtain ⟨p1, p2⟩ := p
  rw [SparseHamiltonian.SparseStateOverlap.matrixOperator_apply,
    SparseHamiltonian.SparseStateOverlap.matrixOperator_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single p2]
  · rw [kron_eq, Matrix.kronecker_apply, Matrix.one_apply_eq, mul_one]
    rfl
  · intro b _ hb
    rw [kron_eq, Matrix.kronecker_apply, Matrix.one_apply_ne' hb, mul_zero, zero_mul]
  · simp

/-- `T ↦ T ⊗ I` on operators, as a ring homomorphism. -/
def kronOne (m : ℕ) : (EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) →+*
    (EuclideanSpace ℂ (S × Fin m) →L[ℂ] EuclideanSpace ℂ (S × Fin m)) where
  toFun T := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S × Fin m)
    (Matrix.kronecker ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S)).symm T)
      (1 : Matrix (Fin m) (Fin m) ℂ))
  map_one' := by
    simp only [map_one, kron_eq, Matrix.one_kronecker_one]
  map_mul' T T' := by
    have h := Matrix.mul_kronecker_mul ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S)).symm T)
      ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S)).symm T') (1 : Matrix (Fin m) (Fin m) ℂ)
      (1 : Matrix (Fin m) (Fin m) ℂ)
    rw [mul_one] at h
    rw [show (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S)).symm (T * T') =
        (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S)).symm T *
          (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S)).symm T' from map_mul _ T T',
      kron_eq, h, map_mul, kron_eq, kron_eq]
  map_zero' := by
    simp only [map_zero, kron_eq, Matrix.zero_kronecker]
  map_add' T T' := by
    simp only [map_add, kron_eq, Matrix.add_kronecker]

theorem kronOne_apply (T : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) :
    kronOne m T = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S × Fin m)
      (Matrix.kronecker ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := S)).symm T)
        (1 : Matrix (Fin m) (Fin m) ℂ)) := rfl

theorem kronOne_smul (c : ℂ) (T : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) :
    kronOne m (c • T) = c • kronOne m T := by
  simp only [kronOne_apply, map_smul, kron_eq, Matrix.smul_kronecker]

/-- `kronOne` as a linear map (for continuity). -/
def kronOneLin (m : ℕ) : (EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) →ₗ[ℂ]
    (EuclideanSpace ℂ (S × Fin m) →L[ℂ] EuclideanSpace ℂ (S × Fin m)) where
  toFun := kronOne m
  map_add' := map_add _
  map_smul' := kronOne_smul

theorem continuous_kronOne : Continuous (kronOne (S := S) m) :=
  (kronOneLin (S := S) m).continuous_of_finiteDimensional

theorem kronOne_mO (B : Matrix S S ℂ) :
    kronOne m (SparseHamiltonian.SparseStateOverlap.matrixOperator B) =
      SparseHamiltonian.SparseStateOverlap.matrixOperator
        (Matrix.kronecker B (1 : Matrix (Fin m) (Fin m) ℂ)) := by
  rw [kronOne_apply, mO_eq, mO_eq, StarAlgEquiv.symm_apply_apply]

theorem evolve_kronecker_one (B : Matrix S S ℂ) (τ : ℝ) :
    evolve (Matrix.kronecker B (1 : Matrix (Fin m) (Fin m) ℂ)) τ = kronOne m (evolve B τ) := by
  letI : NormedAlgebra ℚ (EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) :=
    .restrictScalars ℚ ℂ _
  unfold evolve
  rw [NormedSpace.map_exp _ continuous_kronOne, ← kronOne_mO, kronOne_smul]

omit [Fintype S] [DecidableEq S] in
theorem slice_apply (a : Fin m) (v : EuclideanSpace ℂ (S × Fin m)) (i : S) :
    slice a v i = v (i, a) := rfl

omit [DecidableEq S] in
theorem norm_sq_eq_sum_slice (v : EuclideanSpace ℂ (S × Fin m)) :
    ‖v‖ ^ 2 = ∑ a, ‖slice a v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  rfl

omit [DecidableEq S] in
theorem norm_mO_kronecker_one_apply_sq (A : Matrix S S ℂ) (v : EuclideanSpace ℂ (S × Fin m)) :
    ‖SparseHamiltonian.SparseStateOverlap.matrixOperator
        (Matrix.kronecker A (1 : Matrix (Fin m) (Fin m) ℂ)) v‖ ^ 2 =
      ∑ a, ‖SparseHamiltonian.SparseStateOverlap.matrixOperator A (slice a v)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mO_kronecker_one_apply]

/-- `‖B ⊗ I_m‖ = ‖B‖` for `m > 0`. -/
theorem norm_kronecker_one (hm0 : 0 < m) (B : Matrix S S ℂ) :
    ‖Matrix.kronecker B (1 : Matrix (Fin m) (Fin m) ℂ)‖ = ‖B‖ := by
  rw [Matrix.cstar_norm_def, Matrix.cstar_norm_def, ← mO_eq, ← mO_eq]
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp ?_
    rw [norm_mO_kronecker_one_apply_sq, mul_pow, norm_sq_eq_sum_slice, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((SparseHamiltonian.SparseStateOverlap.matrixOperator B).le_opNorm _) 2
  · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => ?_
    set a0 : Fin m := ⟨0, hm0⟩
    set v : EuclideanSpace ℂ (S × Fin m) :=
      WithLp.toLp 2 fun p => if p.2 = a0 then w p.1 else 0 with hvdef
    have hs : slice a0 v = w := by
      ext i
      simp [slice_apply, hvdef]
    have hz : ∀ b, b ≠ a0 → slice b v = 0 := by
      intro b hb
      ext i
      simp [slice_apply, hvdef, hb]
    have hv : ‖v‖ = ‖w‖ := by
      have h2 : ‖v‖ ^ 2 = ‖w‖ ^ 2 := by
        rw [norm_sq_eq_sum_slice, Finset.sum_eq_single a0, hs]
        · intro b _ hb
          rw [hz b hb, norm_zero]
          ring
        · simp
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2
    calc ‖SparseHamiltonian.SparseStateOverlap.matrixOperator B w‖
        = ‖SparseHamiltonian.SparseStateOverlap.matrixOperator B (slice a0 v)‖ := by rw [hs]
      _ ≤ ‖SparseHamiltonian.SparseStateOverlap.matrixOperator
            (Matrix.kronecker B (1 : Matrix (Fin m) (Fin m) ℂ)) v‖ := by
          refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
          rw [norm_mO_kronecker_one_apply_sq]
          exact Finset.single_le_sum
            (f := fun a => ‖SparseHamiltonian.SparseStateOverlap.matrixOperator B (slice a v)‖ ^ 2)
            (fun _ _ => by positivity) (Finset.mem_univ a0)
      _ ≤ ‖SparseHamiltonian.SparseStateOverlap.matrixOperator
            (Matrix.kronecker B (1 : Matrix (Fin m) (Fin m) ℂ))‖ * ‖v‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = _ := by rw [hv]

/-- `e^{-iτ(B ⊗ I)} = e^{-iτB} ⊗ I`, read on vectors. -/
theorem evolve_kronecker_one_apply (B : Matrix S S ℂ) (τ : ℝ)
    (v : EuclideanSpace ℂ (S × Fin m)) (p : S × Fin m) :
    evolve (Matrix.kronecker B (1 : Matrix (Fin m) (Fin m) ℂ)) τ v p =
      evolve B τ (WithLp.toLp 2 fun i => v (i, p.2)) p.1 := by
  rw [evolve_kronecker_one, kronOne_apply, ← mO_eq, mO_kronecker_one_apply, mO_eq,
    StarAlgEquiv.apply_symm_apply]
  rfl

/-- Evolution under a unitary similarity. -/
theorem evolve_unitary_conj {U : Matrix S S ℂ} (hU : U ∈ Matrix.unitaryGroup S ℂ)
    (K : Matrix S S ℂ) (τ : ℝ) :
    evolve (U * K * Uᴴ) τ =
      SparseHamiltonian.SparseStateOverlap.matrixOperator U ∘L evolve K τ ∘L
        SparseHamiltonian.SparseStateOverlap.matrixOperator Uᴴ := by
  letI : NormedAlgebra ℚ (EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) :=
    .restrictScalars ℚ ℂ _
  have h1 : SparseHamiltonian.SparseStateOverlap.matrixOperator U *
      SparseHamiltonian.SparseStateOverlap.matrixOperator Uᴴ = 1 := by
    rw [← mO_mul, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp hU, mO_one]
  have h2 : SparseHamiltonian.SparseStateOverlap.matrixOperator Uᴴ *
      SparseHamiltonian.SparseStateOverlap.matrixOperator U = 1 := by
    rw [← mO_mul, ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp hU, mO_one]
  let y : (EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S)ˣ := ⟨_, _, h1, h2⟩
  have h := NormedSpace.exp_units_conj y
    ((-Complex.I * (τ : ℂ)) • SparseHamiltonian.SparseStateOverlap.matrixOperator K)
  simp only [y, Units.inv_mk] at h
  have hc : SparseHamiltonian.SparseStateOverlap.matrixOperator U *
        ((-Complex.I * (τ : ℂ)) • SparseHamiltonian.SparseStateOverlap.matrixOperator K) *
        SparseHamiltonian.SparseStateOverlap.matrixOperator Uᴴ =
      (-Complex.I * (τ : ℂ)) • (SparseHamiltonian.SparseStateOverlap.matrixOperator U *
        SparseHamiltonian.SparseStateOverlap.matrixOperator K *
        SparseHamiltonian.SparseStateOverlap.matrixOperator Uᴴ) := by
    ext1 v
    simp only [mul_apply_eq_comp, smul_apply, map_smul]
  rw [hc] at h
  unfold evolve
  rw [mO_mul, mO_mul, h]
  rfl

/-- The `L²` operator norm is unitarily invariant. -/
theorem norm_unitary_conj {U : Matrix S S ℂ} (hU : U ∈ Matrix.unitaryGroup S ℂ)
    (K : Matrix S S ℂ) : ‖U * K * Uᴴ‖ = ‖K‖ := by
  have hU' : Uᴴ ∈ unitary (Matrix S S ℂ) := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hU
  rw [CStarRing.norm_mul_mem_unitary _ hU', CStarRing.norm_mem_unitary_mul _ hU]

end

end SparseLowerBounds.Helpers.Chains
end
