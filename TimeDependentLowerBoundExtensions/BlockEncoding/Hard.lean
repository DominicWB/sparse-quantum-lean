import TimeDependentLowerBoundExtensions.Core.Masked
import TimeDependentExtensions.BlockEncoding.Theorem
import SparseHamiltonian.HermitianDilation

set_option autoImplicit false

/-!
# Hermitian block encodings of the hard instances

The time-indexed block-encoding model of the manuscript (eqs. `hs:eq:blockspecial`,
`hs:eq:blockadditive`) supplies coherent
and controlled access to Hermitian unitaries `O_r` with `J† O_r J = H̃_r / α_BE` for a known
isometry `J`; the released form is `TimeDependentExtensions.BlockEncoding.simulation`, with the
controlled time-indexed oracle `TimeDependentExtensions.BlockEncoding.primitive`. A standard sparse
block encoding has normalisation `α_BE = sη` (the text after eq. `hs:eq:blockadditive`).

The hard instances of Theorem `hsl:thm:main` are given by native sparse data
(`SparseHamiltonian.NativeSparseBlockEncoding.Data`). Their released six-query block encoding
`W_x = (program D).eval x` (`NativeSparseBlockEncoding.compression`: `J₀† W_x J₀ = H_x/(s a)`,
`J₀ = input D`, `a = D.scale`) is unitary but not Hermitian. This module makes it Hermitian with
one extra qubit, by the package's Hermitian dilation
(`SparseHamiltonian.HermitianDilation.dilation W = diag(W, W†) ∘ swap`, blocks `[[0, W], [W†, 0]]`):

* `beOp D x`, on the flattened register `ℂ^{BEBasis N Z}` (`beLayout`): the dilation of the
  six-query program, Hermitian and unitary (`beOp_selfAdjoint`, `beOp_unitary`);
* `beJ D = |+⟩ ⊗ J₀` (`HermitianDilation.encodedPlus`), an isometry (`beJ_isometry`), with
  `beJ† (beOp D x) beJ = (A + A†)/2 = H_x/(s a)` for Hermitian `H_x` (`beJ_compress`), so the
  represented sample at `α_BE = s a` (`beAlpha`) is exactly `H_x` (`blockSample_beOp`);
* `beConst D M`: the constant time-indexed family, every sample equal to `beOp D x`.

The constant hard paths therefore belong to the block-encoding class with zero integrated sample
error, and every call of the time-indexed oracle is one controlled call of `beOp D x`.

The package's globally involutory native dilation
(`SparseHamiltonian.NativeHermitianDilation.program`) is a program over its own masked oracle
family at six times the weighted cost of the original program; the dilation used here costs two
masked runs of the six-query program per call (`implementsOn_beOp`).
-/

namespace TimeDependentLowerBoundExtensions.BlockEncoding

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit ContinuousLinearMap
open SparseLowerBounds
open scoped InnerProduct InnerProductSpace

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- The flattened basis of the block-encoding register: the dilation qubit and the native
sparse space `NSpace N Z` (address, value and flag). -/
abbrev BEBasis (N Z : Type) := Bool × (((N × N) × Z) × Fin 3)

/-- Fixed coordinates `ℂ^{BEBasis N Z} ≃ ℂ² ⊗ NSpace N Z`. -/
def beLayout (N Z : Type) [Fintype N] [Fintype Z] :
    EuclideanSpace ℂ (BEBasis N Z) ≃ₗᵢ[ℂ] Joint Bool (SparseFlagEmbedding.Space (N × N) Z) :=
  (RegisterEquivalences.productFlatten Bool (((N × N) × Z) × Fin 3)).symm.trans
    (LinearIsometryEquiv.piLpCongrRight 2
      (fun _ : Bool => (RegisterEquivalences.productFlatten ((N × N) × Z) (Fin 3)).symm))

/-- **The Hermitian block encoding of a sparse instance**: the Hermitian dilation
`HermitianDilation.dilation` of the released six-query block encoding `(program D).eval x`, in
the coordinates `beLayout`. -/
def beOp (D : Data X N Z s) (x : X) :
    EuclideanSpace ℂ (BEBasis N Z) →L[ℂ] EuclideanSpace ℂ (BEBasis N Z) :=
  (beLayout N Z).symm.conjStarAlgEquiv (HermitianDilation.dilation ((program D).eval x))

/-- **The boundary isometry** `J = |+⟩ ⊗ J₀`, `J₀ = input D` (`HermitianDilation.encodedPlus`),
in the coordinates `beLayout`; it depends only on public data. -/
def beJ (D : Data X N Z s) : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ (BEBasis N Z) :=
  (beLayout N Z).symm.toLinearIsometry.toContinuousLinearMap ∘L
    HermitianDilation.encodedPlus (input D).toContinuousLinearMap

/-- The block-encoding normalisation `α_BE = s a`, `a = D.scale`. -/
def beAlpha (D : Data X N Z s) : ℝ := s * D.scale

/-- **The constant time-indexed block encoding**: every sample `r` is `beOp D x`. -/
def beConst (D : Data X N Z s) (M : ℕ) :
    X → Fin M → EuclideanSpace ℂ (BEBasis N Z) →L[ℂ] EuclideanSpace ℂ (BEBasis N Z) :=
  fun x _ => beOp D x

section Transport

variable {H K P : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- A fixed isometric change of coordinates preserves self-adjointness. -/
theorem conj_star_of_star (e : H ≃ₗᵢ[ℂ] K) (A : H →L[ℂ] H) (hA : star A = A) :
    star (e.conjStarAlgEquiv A) = e.conjStarAlgEquiv A := by
  rw [← map_star, hA]

/-- Compressing a transported operator by a transported boundary is the original
compression. -/
theorem conj_compress (e : H ≃ₗᵢ[ℂ] K) (A : H →L[ℂ] H) (E : P →L[ℂ] H) :
    (e.toLinearIsometry.toContinuousLinearMap ∘L E)† ∘L e.conjStarAlgEquiv A ∘L
        (e.toLinearIsometry.toContinuousLinearMap ∘L E) = E† ∘L A ∘L E := by
  have h : (e.toLinearIsometry.toContinuousLinearMap)† = ((e.symm : K ≃ₗᵢ[ℂ] H) : K →L[ℂ] H) :=
    LinearIsometryEquiv.adjoint_eq_symm e
  apply ContinuousLinearMap.ext
  intro v
  simp [adjoint_comp, h, LinearIsometryEquiv.conjStarAlgEquiv_apply]

end Transport

omit [DecidableEq Z] in
/-- The hard block encodings are self-adjoint. -/
theorem beOp_selfAdjoint (D : Data X N Z s) (x : X) : star (beOp D x) = beOp D x :=
  conj_star_of_star _ _ (by
    rw [ContinuousLinearMap.star_eq_adjoint, HermitianDilation.dilation_selfAdjoint])

omit [DecidableEq Z] in
/-- The hard block encodings are unitary. -/
theorem beOp_unitary (D : Data X N Z s) (x : X) : IsUnitary (beOp D x) :=
  IsUnitary.transport (HermitianDilation.dilation_unitary _ (program_unitary D x)) _

/-- The boundary `beJ D` is an isometry. -/
theorem beJ_isometry (D : Data X N Z s) : (beJ D)† ∘L beJ D = 1 := by
  have h1 : ((beLayout N Z).symm.toLinearIsometry.toContinuousLinearMap)† ∘L
      (beLayout N Z).symm.toLinearIsometry.toContinuousLinearMap = 1 :=
    LinearIsometry.adjoint_comp_self _
  have h2 : (beJ D)† ∘L beJ D =
      (HermitianDilation.encodedPlus (input D).toContinuousLinearMap)† ∘L
        (((beLayout N Z).symm.toLinearIsometry.toContinuousLinearMap)† ∘L
          (beLayout N Z).symm.toLinearIsometry.toContinuousLinearMap) ∘L
        HermitianDilation.encodedPlus (input D).toContinuousLinearMap := by
    simp only [beJ, adjoint_comp, comp_assoc]
  rw [h2, h1, one_def, id_comp]
  exact HermitianDilation.encodedPlus_isometry _ (input_adjoint_comp D)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The normalisation `α_BE = s a` is positive. -/
theorem beAlpha_pos (D : Data X N Z s) : 0 < beAlpha D := by
  unfold beAlpha
  exact mul_pos (by exact_mod_cast D.slots_pos) D.scale_pos

/-- **Equation `hs:eq:blockspecial` on the hard instances**: for Hermitian `H_x`,
`J† (beOp D x) J = H_x / (s a)`. -/
theorem beJ_compress (D : Data X N Z s) (hH : ∀ x, (D.matrix x).IsHermitian) (x : X) :
    (beJ D)† ∘L beOp D x ∘L beJ D =
      SparseStateOverlap.matrixOperator (fun i j => D.matrix x i j / ((s : ℂ) * D.scale)) := by
  have hcore : (beJ D)† ∘L beOp D x ∘L beJ D =
      (HermitianDilation.encodedPlus (input D).toContinuousLinearMap)† ∘L
        HermitianDilation.dilation ((program D).eval x) ∘L
        HermitianDilation.encodedPlus (input D).toContinuousLinearMap :=
    conj_compress (beLayout N Z).symm _ _
  have hMh : (Matrix.of fun i j => D.matrix x i j / ((s : ℂ) * D.scale)).conjTranspose =
      Matrix.of fun i j => D.matrix x i j / ((s : ℂ) * D.scale) := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_div₀, star_mul',
      Complex.star_def, map_natCast, Complex.conj_ofReal]
    rw [← Complex.star_def, (hH x).apply i j]
  have hadjM : (SparseStateOverlap.matrixOperator
      (Matrix.of fun i j => D.matrix x i j / ((s : ℂ) * D.scale)))† =
      SparseStateOverlap.matrixOperator
        (Matrix.of fun i j => D.matrix x i j / ((s : ℂ) * D.scale)) := by
    rw [SparseHamiltonian.SparseValuePrecision.matrixOperator_adjoint, hMh]
  rw [hcore, HermitianDilation.encodedPlus_compression, compression D x]
  change HermitianDilation.hermitianPart (SparseStateOverlap.matrixOperator
    (Matrix.of fun i j => D.matrix x i j / ((s : ℂ) * D.scale))) = _
  rw [HermitianDilation.hermitianPart, hadjM, ← two_smul ℂ, smul_smul]
  norm_num
  rfl

/-- **The represented sample is the instance**: `α_BE J† (beOp D x) J = H_x`. -/
theorem blockSample_beOp (D : Data X N Z s) (hH : ∀ x, (D.matrix x).IsHermitian) (x : X) :
    TimeDependentExtensions.BlockEncoding.blockSample (beOp D x) (beJ D) (beAlpha D) =
      SparseStateOverlap.matrixOperator (D.matrix x) := by
  have hs : ((s : ℂ) * D.scale) ≠ 0 := by
    have h := beAlpha_pos D
    unfold beAlpha at h
    exact_mod_cast h.ne'
  unfold TimeDependentExtensions.BlockEncoding.blockSample
    TimeDependentExtensions.BlockEncoding.compressed
  rw [beJ_compress D hH x]
  ext v i
  simp only [smul_apply, PiLp.smul_apply,
    SparseStateOverlap.matrixOperator_apply, smul_eq_mul, Finset.mul_sum, beAlpha]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hs1 : (s : ℂ) ≠ 0 := left_ne_zero_of_mul hs
  have hs2 : (D.scale : ℂ) ≠ 0 := right_ne_zero_of_mul hs
  push_cast
  field_simp

end

end TimeDependentLowerBoundExtensions.BlockEncoding
