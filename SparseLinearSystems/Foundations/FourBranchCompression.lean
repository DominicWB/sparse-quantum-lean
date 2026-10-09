import SparseLinearSystems.Foundations.AugmentedMoments

/-!
# Four-branch Hilbert compression

The augmented construction uses four mutually orthogonal private branches.
This section constructs that direct sum rather than treating the branch
average as scalar bookkeeping.  The branch spaces may be different, which is
needed because the sparse-entry branch has an edge workspace whereas the
three known branches may use the system space itself.
-/

namespace SparseLinearSystems.FourBranchCompression

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct

variable {V P₀ P₁ P₂ P₃ : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable [NormedAddCommGroup P₀] [InnerProductSpace ℂ P₀] [CompleteSpace P₀]
variable [NormedAddCommGroup P₁] [InnerProductSpace ℂ P₁] [CompleteSpace P₁]
variable [NormedAddCommGroup P₂] [InnerProductSpace ℂ P₂] [CompleteSpace P₂]
variable [NormedAddCommGroup P₃] [InnerProductSpace ℂ P₃] [CompleteSpace P₃]

/-- The Hilbert direct sum of four possibly different private branch spaces. -/
abbrev FourSpace (P₀ P₁ P₂ P₃ : Type*) :=
  WithLp 2 (P₀ × WithLp 2 (P₁ × WithLp 2 (P₂ × P₃)))

/-- Put four isometric branch preparations into mutually orthogonal sectors,
with amplitude `1/2` on each sector. -/
def embedding (J₀ : V →ₗᵢ[ℂ] P₀) (J₁ : V →ₗᵢ[ℂ] P₁)
    (J₂ : V →ₗᵢ[ℂ] P₂) (J₃ : V →ₗᵢ[ℂ] P₃) :
    V →ₗᵢ[ℂ] FourSpace P₀ P₁ P₂ P₃ where
  toLinearMap :=
    { toFun := fun u => WithLp.toLp 2
        ((1 / 2 : ℂ) • J₀ u,
          WithLp.toLp 2
            ((1 / 2 : ℂ) • J₁ u,
              WithLp.toLp 2
                ((1 / 2 : ℂ) • J₂ u, (1 / 2 : ℂ) • J₃ u)))
      map_add' := by
        intro u v
        apply WithLp.ofLp_injective 2
        apply Prod.ext
        · simp [map_add, smul_add]
        · apply WithLp.ofLp_injective 2
          apply Prod.ext
          · simp [map_add, smul_add]
          · apply WithLp.ofLp_injective 2
            apply Prod.ext <;>
              simp [map_add, smul_add]
      map_smul' := by
        intro z u
        apply WithLp.ofLp_injective 2
        apply Prod.ext
        · simp [map_smul, smul_smul, mul_comm]
        · apply WithLp.ofLp_injective 2
          apply Prod.ext
          · simp [map_smul, smul_smul, mul_comm]
          · apply WithLp.ofLp_injective 2
            apply Prod.ext <;>
              simp [map_smul, smul_smul, mul_comm] }
  norm_map' := by
    intro u
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖WithLp.toLp 2
      ((1 / 2 : ℂ) • J₀ u,
        WithLp.toLp 2
          ((1 / 2 : ℂ) • J₁ u,
            WithLp.toLp 2
              ((1 / 2 : ℂ) • J₂ u, (1 / 2 : ℂ) • J₃ u)))‖ ^ 2 = ‖u‖ ^ 2
    simp only [WithLp.prod_norm_sq_eq_of_L2, WithLp.toLp_fst, WithLp.toLp_snd,
      norm_smul, LinearIsometry.norm_map]
    norm_num; ring

omit [CompleteSpace V] [CompleteSpace P₀] [CompleteSpace P₁] [CompleteSpace P₂] [CompleteSpace P₃] in
@[simp] theorem embedding_apply (J₀ : V →ₗᵢ[ℂ] P₀) (J₁ : V →ₗᵢ[ℂ] P₁)
    (J₂ : V →ₗᵢ[ℂ] P₂) (J₃ : V →ₗᵢ[ℂ] P₃) (u : V) :
    embedding J₀ J₁ J₂ J₃ u = WithLp.toLp 2
      ((1 / 2 : ℂ) • J₀ u,
        WithLp.toLp 2
          ((1 / 2 : ℂ) • J₁ u,
            WithLp.toLp 2
              ((1 / 2 : ℂ) • J₂ u, (1 / 2 : ℂ) • J₃ u))) := rfl

/-- The four-branch preparation is an isometry in the operator algebra. -/
theorem embedding_adjoint_comp_self
    (J₀ : V →ₗᵢ[ℂ] P₀) (J₁ : V →ₗᵢ[ℂ] P₁)
    (J₂ : V →ₗᵢ[ℂ] P₂) (J₃ : V →ₗᵢ[ℂ] P₃) :
    (ContinuousLinearMap.adjoint (embedding J₀ J₁ J₂ J₃).toContinuousLinearMap) ∘L
        (embedding J₀ J₁ J₂ J₃).toContinuousLinearMap = 1 :=
  LinearIsometry.adjoint_comp_self (embedding J₀ J₁ J₂ J₃)

/-- A generator acting independently on the four orthogonal branches. -/
def diagonal (K₀ : P₀ →L[ℂ] P₀) (K₁ : P₁ →L[ℂ] P₁)
    (K₂ : P₂ →L[ℂ] P₂) (K₃ : P₃ →L[ℂ] P₃) :
    FourSpace P₀ P₁ P₂ P₃ →L[ℂ] FourSpace P₀ P₁ P₂ P₃ :=
  HilbertBlocks.blockMap K₀ 0 0
    (HilbertBlocks.blockMap K₁ 0 0
      (HilbertBlocks.blockMap K₂ 0 0 K₃))

omit [CompleteSpace P₀] [CompleteSpace P₁] [CompleteSpace P₂] [CompleteSpace P₃] in
@[simp] theorem diagonal_apply
    (K₀ : P₀ →L[ℂ] P₀) (K₁ : P₁ →L[ℂ] P₁)
    (K₂ : P₂ →L[ℂ] P₂) (K₃ : P₃ →L[ℂ] P₃)
    (x : FourSpace P₀ P₁ P₂ P₃) :
    diagonal K₀ K₁ K₂ K₃ x = WithLp.toLp 2
      (K₀ x.fst,
        WithLp.toLp 2
          (K₁ x.snd.fst,
            WithLp.toLp 2 (K₂ x.snd.snd.fst, K₃ x.snd.snd.snd))) := by
  simp only [diagonal, HilbertBlocks.blockMap_apply, zero_apply, add_zero, zero_add,
    WithLp.fst, WithLp.snd]

omit [CompleteSpace P₀] [CompleteSpace P₁] [CompleteSpace P₂] [CompleteSpace P₃] in
/-- Multiplication of branch generators remains branchwise. -/
theorem diagonal_mul
    (K₀ L₀ : P₀ →L[ℂ] P₀) (K₁ L₁ : P₁ →L[ℂ] P₁)
    (K₂ L₂ : P₂ →L[ℂ] P₂) (K₃ L₃ : P₃ →L[ℂ] P₃) :
    diagonal K₀ K₁ K₂ K₃ * diagonal L₀ L₁ L₂ L₃ =
      diagonal (K₀ * L₀) (K₁ * L₁) (K₂ * L₂) (K₃ * L₃) := by
  ext x
  simp only [mul_apply_eq_comp, diagonal_apply, WithLp.fst, WithLp.snd]

/-- The adjoint of the four-branch generator is obtained branchwise. -/
theorem diagonal_adjoint
    (K₀ : P₀ →L[ℂ] P₀) (K₁ : P₁ →L[ℂ] P₁)
    (K₂ : P₂ →L[ℂ] P₂) (K₃ : P₃ →L[ℂ] P₃) :
    (ContinuousLinearMap.adjoint (diagonal K₀ K₁ K₂ K₃)) = diagonal (ContinuousLinearMap.adjoint K₀) (ContinuousLinearMap.adjoint K₁) (ContinuousLinearMap.adjoint K₂) (ContinuousLinearMap.adjoint K₃) := by
  simp only [diagonal, HilbertBlocks.block_adjoint, map_zero]

/-- Self-adjoint branch generators give a self-adjoint combined generator. -/
theorem diagonal_selfadjoint
    (K₀ : P₀ →L[ℂ] P₀) (K₁ : P₁ →L[ℂ] P₁)
    (K₂ : P₂ →L[ℂ] P₂) (K₃ : P₃ →L[ℂ] P₃)
    (h₀ : (ContinuousLinearMap.adjoint K₀) = K₀) (h₁ : (ContinuousLinearMap.adjoint K₁) = K₁)
    (h₂ : (ContinuousLinearMap.adjoint K₂) = K₂) (h₃ : (ContinuousLinearMap.adjoint K₃) = K₃) :
    (ContinuousLinearMap.adjoint (diagonal K₀ K₁ K₂ K₃)) = diagonal K₀ K₁ K₂ K₃ := by
  rw [diagonal_adjoint, h₀, h₁, h₂, h₃]

/-- Compression of one private branch back to the common system space. -/
def branchCompression {P : Type*}
    [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    (J : V →ₗᵢ[ℂ] P) (K : P →L[ℂ] P) : V →L[ℂ] V :=
  (ContinuousLinearMap.adjoint J.toContinuousLinearMap) ∘L K ∘L J.toContinuousLinearMap

/-- The arithmetic mean of the four individual compressions. -/
def compressed
    (J₀ : V →ₗᵢ[ℂ] P₀) (J₁ : V →ₗᵢ[ℂ] P₁)
    (J₂ : V →ₗᵢ[ℂ] P₂) (J₃ : V →ₗᵢ[ℂ] P₃)
    (K₀ : P₀ →L[ℂ] P₀) (K₁ : P₁ →L[ℂ] P₁)
    (K₂ : P₂ →L[ℂ] P₂) (K₃ : P₃ →L[ℂ] P₃) : V →L[ℂ] V :=
  (1 / 4 : ℂ) •
    (branchCompression J₀ K₀ + branchCompression J₁ K₁ +
      branchCompression J₂ K₂ + branchCompression J₃ K₃)

/-- Exact first-moment compression identity for four coherent branches. -/
theorem compression
    (J₀ : V →ₗᵢ[ℂ] P₀) (J₁ : V →ₗᵢ[ℂ] P₁)
    (J₂ : V →ₗᵢ[ℂ] P₂) (J₃ : V →ₗᵢ[ℂ] P₃)
    (K₀ : P₀ →L[ℂ] P₀) (K₁ : P₁ →L[ℂ] P₁)
    (K₂ : P₂ →L[ℂ] P₂) (K₃ : P₃ →L[ℂ] P₃) :
    (ContinuousLinearMap.adjoint (embedding J₀ J₁ J₂ J₃).toContinuousLinearMap) ∘L
        diagonal K₀ K₁ K₂ K₃ ∘L
        (embedding J₀ J₁ J₂ J₃).toContinuousLinearMap =
      compressed J₀ J₁ J₂ J₃ K₀ K₁ K₂ K₃ := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℂ
  intro v
  simp only [comp_apply, adjoint_inner_left, diagonal_apply,
    LinearIsometry.coe_toContinuousLinearMap, embedding_apply,
    WithLp.prod_inner_apply, WithLp.fst, WithLp.snd, map_smul,
    inner_smul_left, inner_smul_right, branchCompression, compressed, add_apply, smul_apply,
    inner_add_left, map_div₀, map_one, map_ofNat]
  ring

/-- Exact second-moment compression identity. -/
theorem secondCompression
    (J₀ : V →ₗᵢ[ℂ] P₀) (J₁ : V →ₗᵢ[ℂ] P₁)
    (J₂ : V →ₗᵢ[ℂ] P₂) (J₃ : V →ₗᵢ[ℂ] P₃)
    (K₀ : P₀ →L[ℂ] P₀) (K₁ : P₁ →L[ℂ] P₁)
    (K₂ : P₂ →L[ℂ] P₂) (K₃ : P₃ →L[ℂ] P₃) :
    (ContinuousLinearMap.adjoint (embedding J₀ J₁ J₂ J₃).toContinuousLinearMap) ∘L
        (diagonal K₀ K₁ K₂ K₃ * diagonal K₀ K₁ K₂ K₃) ∘L
        (embedding J₀ J₁ J₂ J₃).toContinuousLinearMap =
      compressed J₀ J₁ J₂ J₃ (K₀ * K₀) (K₁ * K₁) (K₂ * K₂) (K₃ * K₃) := by
  rw [diagonal_mul]
  exact compression J₀ J₁ J₂ J₃ (K₀ * K₀) (K₁ * K₁) (K₂ * K₂) (K₃ * K₃)

omit [CompleteSpace V] [CompleteSpace P₀] [CompleteSpace P₁] [CompleteSpace P₂] [CompleteSpace P₃] in
/-- Pointwise second moment of the block generator on an encoded system
vector.  This is the norm form of the exact second-compression identity. -/
theorem diagonal_embedding_norm_sq
    (J₀ : V →ₗᵢ[ℂ] P₀) (J₁ : V →ₗᵢ[ℂ] P₁)
    (J₂ : V →ₗᵢ[ℂ] P₂) (J₃ : V →ₗᵢ[ℂ] P₃)
    (K₀ : P₀ →L[ℂ] P₀) (K₁ : P₁ →L[ℂ] P₁)
    (K₂ : P₂ →L[ℂ] P₂) (K₃ : P₃ →L[ℂ] P₃) (u : V) :
    ‖diagonal K₀ K₁ K₂ K₃ (embedding J₀ J₁ J₂ J₃ u)‖ ^ 2 =
      (‖K₀ (J₀ u)‖ ^ 2 + ‖K₁ (J₁ u)‖ ^ 2 +
        ‖K₂ (J₂ u)‖ ^ 2 + ‖K₃ (J₃ u)‖ ^ 2) / 4 := by
  simp only [diagonal_apply, embedding_apply, WithLp.fst, WithLp.snd, map_smul,
    WithLp.prod_norm_sq_eq_of_L2, norm_smul]
  norm_num; ring

omit [CompleteSpace V] [CompleteSpace P₀] [CompleteSpace P₁] [CompleteSpace P₂] [CompleteSpace P₃] in
/-- Branchwise pointwise moment estimates combine without a maximum-cost or
interference term because the branch ranges are orthogonal. -/
theorem diagonal_embedding_norm_sq_le
    (J₀ : V →ₗᵢ[ℂ] P₀) (J₁ : V →ₗᵢ[ℂ] P₁)
    (J₂ : V →ₗᵢ[ℂ] P₂) (J₃ : V →ₗᵢ[ℂ] P₃)
    (K₀ : P₀ →L[ℂ] P₀) (K₁ : P₁ →L[ℂ] P₁)
    (K₂ : P₂ →L[ℂ] P₂) (K₃ : P₃ →L[ℂ] P₃)
    (m₀ m₁ m₂ m₃ : ℝ) (u : V)
    (h₀ : ‖K₀ (J₀ u)‖ ^ 2 ≤ m₀ * ‖u‖ ^ 2)
    (h₁ : ‖K₁ (J₁ u)‖ ^ 2 ≤ m₁ * ‖u‖ ^ 2)
    (h₂ : ‖K₂ (J₂ u)‖ ^ 2 ≤ m₂ * ‖u‖ ^ 2)
    (h₃ : ‖K₃ (J₃ u)‖ ^ 2 ≤ m₃ * ‖u‖ ^ 2) :
    ‖diagonal K₀ K₁ K₂ K₃ (embedding J₀ J₁ J₂ J₃ u)‖ ^ 2 ≤
      ((m₀ + m₁ + m₂ + m₃) / 4) * ‖u‖ ^ 2 := by
  rw [diagonal_embedding_norm_sq]
  nlinarith

omit [CompleteSpace V] [CompleteSpace P₀] [CompleteSpace P₁]
  [CompleteSpace P₂] [CompleteSpace P₃] in
/-- The scalar `66/256` estimate upgrades the four branchwise moment bounds
to the operator contraction required by the kernel-walk lemma.  The hypotheses
are exactly the four scaled branch estimates; subsequent sparse-circuit work
must construct the corresponding `K_j` and discharge them. -/
theorem augmented_moment_le_one
    (J₀ : V →ₗᵢ[ℂ] P₀) (J₁ : V →ₗᵢ[ℂ] P₁)
    (J₂ : V →ₗᵢ[ℂ] P₂) (J₃ : V →ₗᵢ[ℂ] P₃)
    (K₀ : P₀ →L[ℂ] P₀) (K₁ : P₁ →L[ℂ] P₁)
    (K₂ : P₂ →L[ℂ] P₂) (K₃ : P₃ →L[ℂ] P₃)
    (s σ r a : ℝ) (hs : 1 ≤ s) (hr : (1 : ℝ) / 8 ≤ r)
    (ha : a ^ 2 = 1 - σ ^ 2) (u : V)
    (h₀ : ‖K₀ (J₀ u)‖ ^ 2 ≤ (a ^ 2 / 64) * ‖u‖ ^ 2)
    (h₁ : ‖K₁ (J₁ u)‖ ^ 2 ≤ (σ ^ 2 / (64 * s)) * ‖u‖ ^ 2)
    (h₂ : ‖K₂ (J₂ u)‖ ^ 2 ≤ ((1 / r ^ 2) / (64 * s)) * ‖u‖ ^ 2)
    (h₃ : ‖K₃ (J₃ u)‖ ^ 2 ≤ (1 / (64 * s)) * ‖u‖ ^ 2) :
    ‖diagonal K₀ K₁ K₂ K₃ (embedding J₀ J₁ J₂ J₃ u)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  have hcombined := diagonal_embedding_norm_sq_le
    J₀ J₁ J₂ J₃ K₀ K₁ K₂ K₃
    (a ^ 2 / 64) (σ ^ 2 / (64 * s))
    ((1 / r ^ 2) / (64 * s)) (1 / (64 * s)) u h₀ h₁ h₂ h₃
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hcoefficient :
      ((a ^ 2 / 64 + σ ^ 2 / (64 * s) +
          (1 / r ^ 2) / (64 * s) + 1 / (64 * s)) / 4) =
        (s * a ^ 2 + σ ^ 2 + 1 / r ^ 2 + 1) / (256 * s) := by
    field_simp [ne_of_gt hspos, ne_of_gt hrpos]; ring
  rw [hcoefficient, ha] at hcombined
  have hscalar := AugmentedMoments.four_branch_moment_le s σ r hs hr
  have hconstant := AugmentedMoments.sixty_six_over_two_fifty_six_le_one
  calc
    ‖diagonal K₀ K₁ K₂ K₃ (embedding J₀ J₁ J₂ J₃ u)‖ ^ 2 ≤
        ((s * (1 - σ ^ 2) + σ ^ 2 + 1 / r ^ 2 + 1) / (256 * s)) *
          ‖u‖ ^ 2 := hcombined
    _ ≤ ((66 : ℝ) / 256) * ‖u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hscalar (sq_nonneg ‖u‖)
    _ ≤ 1 * ‖u‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hconstant (sq_nonneg ‖u‖)
    _ = ‖u‖ ^ 2 := one_mul _

end
end SparseLinearSystems.FourBranchCompression
