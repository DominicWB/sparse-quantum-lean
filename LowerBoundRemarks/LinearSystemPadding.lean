import LinearSystemLowerBound.Theorem

/-!
# Padding the hard linear systems to any larger dimension

This file formalises the remark that follows Theorem `qlsl:thm:main` (the matching linear-system
query lower bound) of *Root-sparsity scaling for Hamiltonian simulation, differential equations
and linear-system solvers* (Section `part:qlsl`):

> This is a worst-case bound in the stated parameter range, with dimension allowed to grow.
> Padding with a known identity block preserves the norm and inverse-norm promises and permits any
> larger dimension when the right-hand side is extended by zero.

The theorem itself is `LinearSystemLowerBound.lower_bound` (constant `1/3072`) and
`LinearSystemLowerBound.lower_bound_sharp` (constant `1/1536`), for the hard matrices
`A_X = family κ ε s X` on the index type `Ind κ ε s` (dimension `N = 4nm`), the right-hand side
`b = rhsVec κ ε s` and the normalised solutions `x_A = target κ ε s X`.

## The padded family

Let `P` be any finite type (the padding register).

* `emb I P : ℂ^I →ₗᵢ[ℂ] ℂ^{I ⊕ P}` is the isometric embedding `ι v = v ⊕ 0` (extension by
  zero).
* `padFamily κ ε s P X = A_X ⊕ I_P` (`Matrix.fromBlocks A_X 0 0 1`), `padRhs = b ⊕ 0 = ι b`, and
  `padTarget X = A'⁻¹ b' / ‖A'⁻¹ b'‖` for `A' = A_X ⊕ I_P`, `b' = b ⊕ 0`.

Its properties, in the forms of the corresponding properties of the hard family:
`padFamily_promise` (`‖A'‖ ≤ 1`, `A'` invertible, `‖A'⁻¹‖ ≤ κ`; generic form `block_promise`),
`padFamily_real_symm`, `padFamily_indefinite`, `padFamily_sparse` (input-independent row
supports `padSupport` of at most `s` indices), `padFamily_dimension` (`|Ind ⊕ P| = |Ind| + |P|
= 4nm + |P|`), `padRhs_apply`, `padRhs_norm`, and `padSolution_eq`, `padTarget_eq`: the padded
solution is the original one extended by zero, `A'⁻¹ b' = ι (A_X⁻¹ b)` and `x_{A'} = ι x_A`;
`padTarget_norm`: `x_{A'}` is a unit vector.

## The lower bound for the padded family

* `bound_of_access`: the counting step `LinearSystemLowerBound.lower_bound_of_bias` for native
  data `D` on an **arbitrary** index type `N`, assuming only `HardAccess D` (input-independent
  location oracles, and table entries that are fixed functions of at most one input bit).  The
  proof of `lower_bound_of_bias` uses the hard matrices only to obtain `HardAccess`; weight
  growth of admissible labels (`growth_admissible`) and the XOR bound for adaptive protocols
  (`xor_lower_bound_of_bias`) are generic in `N`.
* `padAccess`: native data with the padded matrices, input-independent locators and an
  entry-determined table has `HardAccess`: entries of the hard block are bit-determined
  (`bitDetermined_hard`), entries of the padding blocks are constant
  (`padFamily_bitDetermined`).
* The padded decoder `padDecoder = ι ∘ M ∘ ι†` (`M = decoderOf κ ε s`) is a contraction
  (`padDecoder_norm_le`) and its correlation with `ι t` is that of `M` with `t`
  (`inner_padDecoder`), so the signed correlation of `x_{A'}` is the answer probability `p`
  (`padTarget_correlation`).
* `pad_lower_bound_sharp` (`κ √s ln(1/ε) / 1536 < Q`), `pad_lower_bound` (`/ 3072`) and
  `pad_lower_bound_sharp_clean`: the hypotheses of `lower_bound_sharp`, `lower_bound` and
  `lower_bound_sharp_clean` (admissible labels, any adaptive protocol, output identified with
  the output register `Ind ⊕ P` and a garbage register by a fixed isometry, success at least
  `2/3`, reduced conditional output within trace distance `ε` of the target), with native data
  on `Ind ⊕ P` whose matrices are `padFamily κ ε s P` and target `padTarget`.  The proof combines
  `bound_of_access` and `padAccess` with `tree_bias_reduced` for the padded decoder.

## Non-vacuity

`exists_pad_access` (under the hypotheses of `exists_access`): native data on `Ind ⊕ P` with
the padded matrices, fixed permutation locators covering the row supports (`coverData`, a
generic construction from `exists_perm_cover`) and an address-independent word code in `ZMod 8`
with one more value for the identity entry `1` (`padEnc`, `padDec`, `padFamily_entry_cases`).
`exists_pad_hardAccess`: the hypothesis `HardAccess` of `bound_of_access` is satisfiable by data
with the padded matrices.

## A common dimension

For every `Nd ≥ |Ind κ ε s|` the padding register `PadReg κ ε s Nd = Fin (Nd - |Ind κ ε s|)`
gives dimension exactly `Nd` (`padReg_card`); every `Nd ≥ s κ ln(1/ε)` qualifies
(`card_ind_le`).  `common_dimension` collects exact dimension, promise, sparsity and satisfiable
access in dimension `Nd`, and `lower_bound_common_dimension` states the sharp bound there.  Thus
hard instances for all admissible `(κ, ε, s)` with `|Ind κ ε s| ≤ Nd` live in one common
dimension `Nd`.
-/

set_option autoImplicit false

namespace LowerBoundRemarks.LinearSystemPadding

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct Matrix ComplexOrder
open SparseHamiltonian SparseLinearSystems.Protocol LinearSystemLowerBound
  LinearSystemLowerBound.Hard LinearSystemLowerBound.Params LinearSystemLowerBound.Native

/-! ### The counting step for an arbitrary index type -/

section Counting

variable {Z : Type*} [Fintype Z] [AddCommGroup Z] {K F L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **The counting step for native data on any index type.**  For native data `D` on an
arbitrary index type `N` with input-independent locators and table entries that are fixed
functions of at most one input bit (`HardAccess D`), every adaptive protocol over admissible
oracle labels, with any output space and any decoder observable of norm at most one, whose
signed decoder correlation is at least `(2/3)(p - 2ε)` on every input (`p` the answer
probability), makes in the worst case more than `κ √s ln(1/ε) / 1536` weighted native queries.
This is `LinearSystemLowerBound.lower_bound_of_bias` without the hypothesis
`D.matrix = family κ ε s`. -/
theorem bound_of_access (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64) {N : Type*} [Fintype N] [DecidableEq N]
    (D : NativeSparseBlockEncoding.Data (Inp κ ε s) N Z s) (hacc : HardAccess D)
    (O : L → Inp κ ε s → K →L[ℂ] K) (w : L → ℕ) (hO : ∀ l, Admissible D (O l) (w l))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] (T : Tree O F E) (M : E →L[ℂ] E) (hM : ∀ v, ‖M v‖ ≤ ‖v‖)
    (hbias : ∀ x, 2 / 3 * (answerProb (rpar κ) (npar κ ε) - 2 * ε) ≤
      parSign x * corr M (T.successDensity x)) :
    κ * Real.sqrt s * Real.log (1 / ε) / 1536 < T.worstCost w := by
  set n := npar κ ε
  set m := mpar s
  have hn := npar_pos κ ε hκ hε hε1
  have hm4 := four_le_mpar s hs
  have hm0 : m ≠ 0 := by omega
  have hmeven := mpar_even s hs
  -- weight growth of all labels
  set C := (1 + 2 / Real.sqrt m) ^ 2
  have hC : 1 ≤ C := by
    have : (0 : ℝ) ≤ 2 / Real.sqrt m := by positivity
    nlinarith
  have hgrow := fun l => growth_admissible hm0 D hacc (O l) (w l) (hO l)
  obtain ⟨-, hbias'⟩ := bias_ge κ ε hκ hε hε1
  have hxor := xor_lower_bound_of_bias hmeven hm0 (fun l => (hgrow l).2.2) w C hC
    (fun l => (hgrow l).1) (fun l => (hgrow l).2.1) M hM T _ hbias
  rw [Fintype.card_fin] at hxor
  have hfin : ε ≤ (1 / 2) ^ n * ((1 + 2 / Real.sqrt m) ^ 2) ^ T.worstCost w :=
    hbias'.trans hxor
  have hq := q_bound n m (T.worstCost w) ε hε (by omega) hn (npar_ge_twoL κ ε hκ hε hε1) hfin
  have hngt := npar_gt κ ε hκ hε hε1
  have hsm := sqrt_mpar s hs
  have hL : 0 < Real.log (1 / ε) := by
    have := L_ge ε hε hε1; have := log_64_gt; linarith
  have hκL : 0 < κ * Real.log (1 / ε) / 32 := by positivity
  have h1 : κ * Real.sqrt s * Real.log (1 / ε) / 1536 =
      (κ * Real.log (1 / ε) / 32) * (Real.sqrt s / 2) / 24 := by ring
  rw [h1]
  calc (κ * Real.log (1 / ε) / 32) * (Real.sqrt s / 2) / 24
      < (n : ℝ) * Real.sqrt m / 24 := by
        apply div_lt_div_of_pos_right _ (by norm_num)
        exact mul_lt_mul'' hngt hsm hκL.le (by positivity)
    _ < T.worstCost w := hq

end Counting

/-! ### Extension by zero and the block operator `A ⊕ I` -/

/-- **The isometric embedding** `ι : ℂ^I → ℂ^{I ⊕ P}`, `v ↦ v ⊕ 0` (extension by zero). -/
def emb (I P : Type*) [Fintype I] [Fintype P] :
    EuclideanSpace ℂ I →ₗᵢ[ℂ] EuclideanSpace ℂ (I ⊕ P) where
  toFun v := WithLp.toLp 2 (Sum.elim (fun i => v i) 0)
  map_add' v w := by
    ext a
    cases a <;> simp
  map_smul' c v := by
    ext a
    cases a <;> simp
  norm_map' v := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fintype.sum_sum_type]
    simp

section Block

variable {I P : Type*} [Fintype I] [Fintype P]

/-- `ι v` agrees with `v` on the first block. -/
@[simp] theorem emb_inl (v : EuclideanSpace ℂ I) (i : I) : emb I P v (Sum.inl i) = v i := rfl

/-- `ι v` vanishes on the padding block. -/
@[simp] theorem emb_inr (v : EuclideanSpace ℂ I) (p : P) : emb I P v (Sum.inr p) = 0 := rfl

/-- The first block `v ∘ inl` of a vector on `I ⊕ P`. -/
def inlPart (v : EuclideanSpace ℂ (I ⊕ P)) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i => v (Sum.inl i))

/-- The second block `v ∘ inr` of a vector on `I ⊕ P`. -/
def inrPart (v : EuclideanSpace ℂ (I ⊕ P)) : EuclideanSpace ℂ P :=
  WithLp.toLp 2 (fun p => v (Sum.inr p))

/-- `‖v‖² = ‖v ∘ inl‖² + ‖v ∘ inr‖²`. -/
theorem norm_sq_split (v : EuclideanSpace ℂ (I ⊕ P)) :
    ‖v‖ ^ 2 = ‖inlPart v‖ ^ 2 + ‖inrPart v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fintype.sum_sum_type]
  rfl

/-- The inverse undoes an invertible operator. -/
theorem inverse_apply_self {J : Type*} [Fintype J]
    (B : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J) (hB : IsUnit B)
    (v : EuclideanSpace ℂ J) : Ring.inverse B (B v) = v := by
  have e := congrArg (fun f : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J => f v)
    (Ring.inverse_mul_cancel B hB)
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using e

/-- An invertible operator undoes its inverse. -/
theorem apply_inverse_self {J : Type*} [Fintype J]
    (B : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J) (hB : IsUnit B)
    (v : EuclideanSpace ℂ J) : B (Ring.inverse B v) = v := by
  have e := congrArg (fun f : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J => f v)
    (Ring.mul_inverse_cancel B hB)
  simpa only [mul_apply_eq_comp, one_apply_eq_self] using e

/-- An operator on a coordinate space with `‖v‖ ≤ c ‖B v‖` for all `v` is invertible with
`‖B⁻¹‖ ≤ c`. -/
theorem isUnit_of_lower {J : Type*} [Fintype J]
    (B : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ v, ‖v‖ ≤ c * ‖B v‖) : IsUnit B ∧ ‖Ring.inverse B‖ ≤ c := by
  have hinj : Function.Injective B := by
    intro v w hvw
    have hv := h (v - w)
    rw [map_sub, hvw, sub_self, norm_zero, mul_zero] at hv
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hv)
  have hsurj : Function.Surjective B := by
    have := LinearMap.injective_iff_surjective
      (f := (B : EuclideanSpace ℂ J →ₗ[ℂ] EuclideanSpace ℂ J))
    exact this.mp hinj
  have hU : IsUnit B := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, hsurj⟩
  refine ⟨hU, ContinuousLinearMap.opNorm_le_bound _ hc fun v => ?_⟩
  have hv := h (Ring.inverse B v)
  rwa [apply_inverse_self B hU] at hv

variable [DecidableEq P]

/-- The block operator `A ⊕ I` acts as `A` on the first block. -/
theorem inlPart_block (A : Matrix I I ℂ) (v : EuclideanSpace ℂ (I ⊕ P)) :
    inlPart (SparseStateOverlap.matrixOperator (Matrix.fromBlocks A 0 0 (1 : Matrix P P ℂ)) v) =
      SparseStateOverlap.matrixOperator A (inlPart v) := by
  ext i
  simp [inlPart, Fintype.sum_sum_type]

/-- The block operator `A ⊕ I` acts as the identity on the second block. -/
theorem inrPart_block (A : Matrix I I ℂ) (v : EuclideanSpace ℂ (I ⊕ P)) :
    inrPart (SparseStateOverlap.matrixOperator (Matrix.fromBlocks A 0 0 (1 : Matrix P P ℂ)) v) =
      inrPart v := by
  ext p
  simp [inrPart, Fintype.sum_sum_type, Matrix.one_apply]

/-- `(A ⊕ I) ∘ ι = ι ∘ A`. -/
theorem block_emb (A : Matrix I I ℂ) (v : EuclideanSpace ℂ I) :
    SparseStateOverlap.matrixOperator (Matrix.fromBlocks A 0 0 (1 : Matrix P P ℂ)) (emb I P v) =
      emb I P (SparseStateOverlap.matrixOperator A v) := by
  ext a
  rcases a with i | p <;> simp [Fintype.sum_sum_type]

/-- **The promise survives padding**: if `‖A‖ ≤ 1`, `A` is invertible and `‖A⁻¹‖ ≤ c` with
`c ≥ 1`, then `‖A ⊕ I‖ ≤ 1`, `A ⊕ I` is invertible and `‖(A ⊕ I)⁻¹‖ ≤ c`. -/
theorem block_promise (A : Matrix I I ℂ) (c : ℝ) (hc : 1 ≤ c)
    (h1 : ‖SparseStateOverlap.matrixOperator A‖ ≤ 1)
    (hU : IsUnit (SparseStateOverlap.matrixOperator A))
    (hinv : ‖Ring.inverse (SparseStateOverlap.matrixOperator A)‖ ≤ c) :
    ‖SparseStateOverlap.matrixOperator (Matrix.fromBlocks A 0 0 (1 : Matrix P P ℂ))‖ ≤ 1 ∧
      IsUnit (SparseStateOverlap.matrixOperator (Matrix.fromBlocks A 0 0 (1 : Matrix P P ℂ))) ∧
      ‖Ring.inverse (SparseStateOverlap.matrixOperator
        (Matrix.fromBlocks A 0 0 (1 : Matrix P P ℂ)))‖ ≤ c := by
  set MA := SparseStateOverlap.matrixOperator A
  set B := SparseStateOverlap.matrixOperator (Matrix.fromBlocks A 0 0 (1 : Matrix P P ℂ))
  have hc0 : 0 ≤ c := by linarith
  have hsq : ∀ v, ‖B v‖ ^ 2 = ‖MA (inlPart v)‖ ^ 2 + ‖inrPart v‖ ^ 2 := by
    intro v
    rw [norm_sq_split, inlPart_block, inrPart_block]
  -- `‖u‖ ≤ c ‖A u‖`, hence `‖v‖ ≤ c ‖(A ⊕ I) v‖` since `c ≥ 1`
  have hlow : ∀ u, ‖u‖ ≤ c * ‖MA u‖ := by
    intro u
    calc ‖u‖ = ‖Ring.inverse MA (MA u)‖ := by rw [inverse_apply_self MA hU]
      _ ≤ ‖Ring.inverse MA‖ * ‖MA u‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖MA u‖ := mul_le_mul_of_nonneg_right hinv (norm_nonneg _)
  have hB : ∀ v, ‖v‖ ≤ c * ‖B v‖ := by
    intro v
    have h4 : ‖inlPart v‖ ^ 2 ≤ c ^ 2 * ‖MA (inlPart v)‖ ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hlow _) 2
    have hc2 : 1 ≤ c ^ 2 := by nlinarith
    have h5 : ‖v‖ ^ 2 ≤ (c * ‖B v‖) ^ 2 := by
      rw [norm_sq_split, mul_pow, hsq]
      nlinarith [sq_nonneg ‖inrPart v‖]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg hc0 (norm_nonneg _))
      two_ne_zero).mp h5
  obtain ⟨hBU, hBinv⟩ := isUnit_of_lower B c hc0 hB
  refine ⟨ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_, hBU, hBinv⟩
  have h6 : ‖MA (inlPart v)‖ ≤ ‖inlPart v‖ := by
    calc ‖MA (inlPart v)‖ ≤ ‖MA‖ * ‖inlPart v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖inlPart v‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖inlPart v‖ := one_mul _
  have h5 : ‖B v‖ ^ 2 ≤ (1 * ‖v‖) ^ 2 := by
    rw [hsq, one_mul, norm_sq_split]
    nlinarith [norm_nonneg (MA (inlPart v))]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h5

/-- **The padded solution is the solution extended by zero**:
`(A ⊕ I)⁻¹ (b ⊕ 0) = A⁻¹ b ⊕ 0`. -/
theorem block_inverse_emb (A : Matrix I I ℂ) (hU : IsUnit (SparseStateOverlap.matrixOperator A))
    (hBU : IsUnit (SparseStateOverlap.matrixOperator (Matrix.fromBlocks A 0 0 (1 : Matrix P P ℂ))))
    (b : EuclideanSpace ℂ I) :
    Ring.inverse (SparseStateOverlap.matrixOperator (Matrix.fromBlocks A 0 0 (1 : Matrix P P ℂ)))
        (emb I P b) = emb I P (Ring.inverse (SparseStateOverlap.matrixOperator A) b) := by
  have h : SparseStateOverlap.matrixOperator (Matrix.fromBlocks A 0 0 (1 : Matrix P P ℂ))
      (emb I P (Ring.inverse (SparseStateOverlap.matrixOperator A) b)) = emb I P b := by
    rw [block_emb, apply_inverse_self _ hU]
  rw [← h, inverse_apply_self _ hBU]

omit [DecidableEq P] in
/-- Normalisation commutes with extension by zero. -/
theorem unitDirection_emb (y : EuclideanSpace ℂ I) :
    ODEStateNormalization.unitDirection (emb I P y) =
      emb I P (ODEStateNormalization.unitDirection y) := by
  unfold ODEStateNormalization.unitDirection
  rw [LinearIsometry.norm_map]
  ext a
  rcases a with i | p <;> simp

end Block

/-! ### The padded family -/

section Padded

/-- **The padded hard matrices** `A_X ⊕ I_P` on `Ind κ ε s ⊕ P`. -/
def padFamily (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P] (x : Inp κ ε s) :
    Matrix (Ind κ ε s ⊕ P) (Ind κ ε s ⊕ P) ℂ :=
  Matrix.fromBlocks (family κ ε s x) 0 0 1

/-- The padded right-hand side `b ⊕ 0 = ι b`, still input-independent. -/
def padRhs (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] : EuclideanSpace ℂ (Ind κ ε s ⊕ P) :=
  emb (Ind κ ε s) P (rhsVec κ ε s)

/-- The normalised padded solution `x_{A'} = A'⁻¹ b' / ‖A'⁻¹ b'‖`. -/
def padTarget (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P] (x : Inp κ ε s) :
    EuclideanSpace ℂ (Ind κ ε s ⊕ P) :=
  ODEStateNormalization.unitDirection
    (Ring.inverse (SparseStateOverlap.matrixOperator (padFamily κ ε s P x)) (padRhs κ ε s P))

/-- The padded right-hand side is `b` on the hard block and zero on the padding block. -/
theorem padRhs_apply (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] (i : Ind κ ε s) (p : P) :
    padRhs κ ε s P (Sum.inl i) = rhsVec κ ε s i ∧ padRhs κ ε s P (Sum.inr p) = 0 :=
  ⟨rfl, rfl⟩

/-- The padded right-hand side is a unit vector. -/
theorem padRhs_norm (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] (hs : 5 ≤ s) :
    ‖padRhs κ ε s P‖ = 1 := by
  rw [padRhs, LinearIsometry.norm_map, rhsVec_norm κ ε s hs]

/-- **The promise** for the padded matrices: `‖A'‖ ≤ 1`, `A'` invertible and `‖A'⁻¹‖ ≤ κ`. -/
theorem padFamily_promise (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P]
    (hκ : 32 ≤ κ) (x : Inp κ ε s) :
    ‖SparseStateOverlap.matrixOperator (padFamily κ ε s P x)‖ ≤ 1 ∧
      IsUnit (SparseStateOverlap.matrixOperator (padFamily κ ε s P x)) ∧
      ‖Ring.inverse (SparseStateOverlap.matrixOperator (padFamily κ ε s P x))‖ ≤ κ := by
  obtain ⟨h1, hU, hinv⟩ := family_promise κ ε s hκ x
  exact block_promise _ κ (by linarith) h1 hU hinv

/-- The padded matrices are real symmetric. -/
theorem padFamily_real_symm (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P]
    (x : Inp κ ε s) (a b : Ind κ ε s ⊕ P) :
    padFamily κ ε s P x a b = padFamily κ ε s P x b a ∧ (padFamily κ ε s P x a b).im = 0 := by
  rcases a with i | p <;> rcases b with j | q
  · exact family_real_symm κ ε s x i j
  · simp [padFamily]
  · simp [padFamily]
  · simp only [padFamily, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
    by_cases h : p = q
    · subst h; simp
    · simp [h, Ne.symm h]

/-- The padded matrices are indefinite. -/
theorem padFamily_indefinite (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P]
    (x : Inp κ ε s) :
    ∃ v w : EuclideanSpace ℂ (Ind κ ε s ⊕ P),
      0 < (⟪v, SparseStateOverlap.matrixOperator (padFamily κ ε s P x) v⟫_ℂ).re ∧
      (⟪w, SparseStateOverlap.matrixOperator (padFamily κ ε s P x) w⟫_ℂ).re < 0 := by
  obtain ⟨v, w, hv, hw⟩ := family_indefinite κ ε s x
  refine ⟨emb _ P v, emb _ P w, ?_, ?_⟩
  · rw [padFamily, block_emb, LinearIsometry.inner_map_map]
    exact hv
  · rw [padFamily, block_emb, LinearIsometry.inner_map_map]
    exact hw

/-- The possible nonzero positions of a padded row: the original support in the hard block,
the diagonal position in the padding block. -/
def padSupport (κ ε : ℝ) (s : ℕ) (P : Type*) : Ind κ ε s ⊕ P → Finset (Ind κ ε s ⊕ P)
  | Sum.inl i => (support i).map Function.Embedding.inl
  | Sum.inr p => {Sum.inr p}

/-- **Sparsity**: the possible nonzero positions of each padded row (and, by symmetry, column)
form an input-independent set of at most `s` indices. -/
theorem padFamily_sparse (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P]
    (hs : 5 ≤ s) (a : Ind κ ε s ⊕ P) :
    (padSupport κ ε s P a).card ≤ s ∧ ∀ (x : Inp κ ε s) (b : Ind κ ε s ⊕ P),
      (padFamily κ ε s P x a b ≠ 0 → b ∈ padSupport κ ε s P a) ∧
        (padFamily κ ε s P x b a ≠ 0 → b ∈ padSupport κ ε s P a) := by
  rcases a with i | p
  · obtain ⟨hcard, hsupp⟩ := family_sparse κ ε s hs i
    refine ⟨by simpa [padSupport] using hcard, fun x b => ?_⟩
    rcases b with j | q
    · simpa [padFamily, padSupport] using hsupp x j
    · simp [padFamily]
  · refine ⟨by simp [padSupport]; omega, fun x b => ?_⟩
    rcases b with j | q
    · simp [padFamily]
    · simp only [padFamily, Matrix.fromBlocks_apply₂₂, Matrix.one_apply, padSupport,
        Finset.mem_singleton, Sum.inr.injEq]
      constructor
      · intro h; by_contra hne; exact h (if_neg (Ne.symm hne))
      · intro h; by_contra hne; exact h (if_neg hne)

/-- **Dimension**: `|Ind ⊕ P| = |Ind| + |P| = 4nm + |P|`, which exceeds `s κ ln(1/ε) / 32`. -/
theorem padFamily_dimension (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] (hκ : 32 ≤ κ)
    (hs : 5 ≤ s) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    Fintype.card (Ind κ ε s ⊕ P) = Fintype.card (Ind κ ε s) + Fintype.card P ∧
      Fintype.card (Ind κ ε s ⊕ P) = 4 * npar κ ε * mpar s + Fintype.card P ∧
      s * κ * Real.log (1 / ε) / 32 < Fintype.card (Ind κ ε s ⊕ P) := by
  obtain ⟨h1, h2, -⟩ := family_dimension κ ε s hκ hs hε hε1
  refine ⟨Fintype.card_sum, by rw [Fintype.card_sum, h1], ?_⟩
  rw [Fintype.card_sum]
  push_cast
  have : (0 : ℝ) ≤ Fintype.card P := Nat.cast_nonneg _
  linarith

/-- **The padded solution** is the original solution extended by zero:
`A'⁻¹ b' = ι (A_X⁻¹ b)`. -/
theorem padSolution_eq (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P]
    (hκ : 32 ≤ κ) (x : Inp κ ε s) :
    Ring.inverse (SparseStateOverlap.matrixOperator (padFamily κ ε s P x)) (padRhs κ ε s P) =
      emb _ P (Ring.inverse (SparseStateOverlap.matrixOperator (family κ ε s x))
        (rhsVec κ ε s)) :=
  block_inverse_emb _ (family_promise κ ε s hκ x).2.1 (padFamily_promise κ ε s P hκ x).2.1 _

/-- **The padded target** is the original target extended by zero: `x_{A'} = ι x_A`. -/
theorem padTarget_eq (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P]
    (hκ : 32 ≤ κ) (x : Inp κ ε s) : padTarget κ ε s P x = emb _ P (target κ ε s x) := by
  rw [padTarget, padSolution_eq κ ε s P hκ x, unitDirection_emb]
  rfl

/-- The padded target is a unit vector (the padded solution `A'⁻¹ b'` is nonzero). -/
theorem padTarget_norm (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P]
    (hκ : 32 ≤ κ) (hs : 5 ≤ s) (x : Inp κ ε s) : ‖padTarget κ ε s P x‖ = 1 := by
  apply ODEStateNormalization.unitDirection_norm
  intro h0
  have hb := apply_inverse_self _ (padFamily_promise κ ε s P hκ x).2.1 (padRhs κ ε s P)
  rw [h0, map_zero] at hb
  have h1 := padRhs_norm κ ε s P hs
  rw [← hb, norm_zero] at h1
  exact zero_ne_one h1

/-! ### The padded decoder -/

/-- The padded decoder `ι ∘ M ∘ ι†`, with `M = decoderOf κ ε s`. -/
def padDecoder (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] :
    EuclideanSpace ℂ (Ind κ ε s ⊕ P) →L[ℂ] EuclideanSpace ℂ (Ind κ ε s ⊕ P) :=
  (emb (Ind κ ε s) P).toContinuousLinearMap ∘L decoderOf κ ε s ∘L
    ((emb (Ind κ ε s) P).toContinuousLinearMap)†

/-- The padded decoder is a contraction. -/
theorem padDecoder_norm_le (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P]
    (v : EuclideanSpace ℂ (Ind κ ε s ⊕ P)) : ‖padDecoder κ ε s P v‖ ≤ ‖v‖ := by
  set ι := (emb (Ind κ ε s) P).toContinuousLinearMap
  have hadj : ‖ι†‖ ≤ 1 := by
    rw [LinearIsometryEquiv.norm_map]
    exact LinearIsometry.norm_toContinuousLinearMap_le _
  simp only [padDecoder, ContinuousLinearMap.comp_apply]
  calc ‖ι (decoderOf κ ε s ((ι†) v))‖ = ‖decoderOf κ ε s ((ι†) v)‖ :=
        LinearIsometry.norm_map _ _
    _ ≤ ‖(ι†) v‖ := decoder_norm_le _
    _ ≤ ‖ι†‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hadj (norm_nonneg _)
    _ = ‖v‖ := one_mul _

/-- The padded decoder correlation of `ι t` is the decoder correlation of `t`. -/
theorem inner_padDecoder (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P]
    (t : EuclideanSpace ℂ (Ind κ ε s)) :
    ⟪emb _ P t, padDecoder κ ε s P (emb _ P t)⟫_ℂ = ⟪t, decoderOf κ ε s t⟫_ℂ := by
  set ι := (emb (Ind κ ε s) P).toContinuousLinearMap
  have h : (ι†) (ι t) = t :=
    congrArg (fun f : EuclideanSpace ℂ (Ind κ ε s) →L[ℂ] _ => f t)
      (LinearIsometry.adjoint_comp_self (emb (Ind κ ε s) P))
  simp only [padDecoder, ContinuousLinearMap.comp_apply]
  change ⟪emb _ P t, emb _ P (decoderOf κ ε s ((ι†) (ι t)))⟫_ℂ = _
  rw [h, LinearIsometry.inner_map_map]

/-- The signed padded decoder correlation of the padded target is the answer probability
`p = r^{2n} / (1 + r^{2n})`. -/
theorem padTarget_correlation (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P]
    (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (x : Inp κ ε s) :
    parSign x * (⟪padTarget κ ε s P x, padDecoder κ ε s P (padTarget κ ε s P x)⟫_ℂ).re =
      answerProb (rpar κ) (npar κ ε) := by
  rw [padTarget_eq κ ε s P hκ x, inner_padDecoder]
  exact target_correlation κ ε s hκ hs hε hε1 x

/-! ### Access conditions of padded data -/

/-- Every padded entry is a fixed function of at most one input bit: entries of the hard block
by `bitDetermined_hard`, entries of the padding blocks are constant. -/
theorem padFamily_bitDetermined (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P]
    (a b : Ind κ ε s ⊕ P) : BitDetermined (fun x : Inp κ ε s => padFamily κ ε s P x a b) := by
  rcases a with i | p <;> rcases b with j | q
  · exact bitDetermined_hard (n := npar κ ε) (rpar κ) i j
  · exact Or.inl ⟨0, fun x => by simp [padFamily]⟩
  · exact Or.inl ⟨0, fun x => by simp [padFamily]⟩
  · exact Or.inl ⟨(1 : Matrix P P ℂ) p q, fun x => by simp [padFamily]⟩

/-- **Hard access for padded data**: native data with the padded matrices, input-independent
locators and an entry-determined table satisfies the access conditions `HardAccess`. -/
theorem padAccess {Z : Type*} [Fintype Z] [AddCommGroup Z] (κ ε : ℝ) (s : ℕ) (P : Type*)
    [Fintype P] [DecidableEq P]
    (D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s ⊕ P) Z s)
    (hDm : D.matrix = padFamily κ ε s P)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (henc : ∃ enc : ((Ind κ ε s ⊕ P) × (Ind κ ε s ⊕ P)) → ℂ → Z,
      ∀ x α, D.table x α = enc α (D.matrix x α.1 α.2)) :
    HardAccess D := by
  obtain ⟨enc, henc⟩ := henc
  refine ⟨hrow, hcol, fun α => ?_⟩
  have hfun : (fun x => D.table x α) = fun x => enc α (padFamily κ ε s P x α.1 α.2) := by
    funext x
    rw [henc, hDm]
  rw [hfun]
  exact (padFamily_bitDetermined κ ε s P α.1 α.2).comp (enc α)

end Padded

/-! ### The padded lower bounds -/

section Bounds

variable {Z : Type*} [Fintype Z] [AddCommGroup Z] {K F L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Theorem `qlsl:thm:main` for the padded family, sharp form.**  Every adaptive protocol over
admissible oracle labels of native data for the padded family `A_X ⊕ I_P` (input-independent
locators, entry-determined table) that heralds success with probability at least `2/3` on every
input and outputs, conditional on success, a state whose reduced state on the output register
`Ind ⊕ P` is within trace distance `ε` of `|x_{A'}⟩⟨x_{A'}|` makes in the worst case more than
`κ √s ln(1/ε) / 1536` weighted native queries.  The output space `E` is identified with the
output register and a garbage register `G` by a fixed isometry `V`, as in
`LinearSystemLowerBound.lower_bound_sharp`. -/
theorem pad_lower_bound_sharp (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P]
    (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s ⊕ P) Z s)
    (hDm : D.matrix = padFamily κ ε s P)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (henc : ∃ enc : ((Ind κ ε s ⊕ P) × (Ind κ ε s ⊕ P)) → ℂ → Z,
      ∀ x α, D.table x α = enc α (D.matrix x α.1 α.2))
    (O : L → Inp κ ε s → K →L[ℂ] K) (w : L → ℕ) (hO : ∀ l, Admissible D (O l) (w l))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {G : Type*} [Fintype G] [DecidableEq G]
    (V : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ ((Ind κ ε s ⊕ P) × G)) (T : Tree O F E)
    (hT : ∀ x, 2 / 3 ≤ T.successMass x ∧
      ∃ h : (ptrace (V.conjStarAlgEquiv (T.conditionalDensity x)) -
          ODEMixedOutput.pureOperator (padTarget κ ε s P x)).toLinearMap.IsSymmetric,
        ODEMixedOutput.hermitianTraceDistance
          (ptrace (V.conjStarAlgEquiv (T.conditionalDensity x)))
          (ODEMixedOutput.pureOperator (padTarget κ ε s P x)) h ≤ ε) :
    κ * Real.sqrt s * Real.log (1 / ε) / 1536 < T.worstCost w := by
  obtain ⟨hpε, -⟩ := bias_ge κ ε hκ hε hε1
  exact bound_of_access κ ε s hκ hs hε hε1 D (padAccess κ ε s P D hDm hrow hcol henc) O w hO T
    (V.conjStarAlgEquiv.symm (ampl (G := G) (padDecoder κ ε s P)))
    (norm_conj_ampl_le V _ (padDecoder_norm_le κ ε s P)) fun x =>
      tree_bias_reduced V T x (padDecoder κ ε s P) (padDecoder_norm_le κ ε s P)
        (padTarget κ ε s P x) (parSign x) (parSign_pm x) _ ε
        (padTarget_correlation κ ε s P hκ hs hε hε1 x) hpε (hT x).1 (hT x).2

/-- **Theorem `qlsl:thm:main` for the padded family** with the paper's conservative constant:
`Q > κ √s ln(1/ε) / 3072`. -/
theorem pad_lower_bound (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P]
    (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s ⊕ P) Z s)
    (hDm : D.matrix = padFamily κ ε s P)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (henc : ∃ enc : ((Ind κ ε s ⊕ P) × (Ind κ ε s ⊕ P)) → ℂ → Z,
      ∀ x α, D.table x α = enc α (D.matrix x α.1 α.2))
    (O : L → Inp κ ε s → K →L[ℂ] K) (w : L → ℕ) (hO : ∀ l, Admissible D (O l) (w l))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {G : Type*} [Fintype G] [DecidableEq G]
    (V : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ ((Ind κ ε s ⊕ P) × G)) (T : Tree O F E)
    (hT : ∀ x, 2 / 3 ≤ T.successMass x ∧
      ∃ h : (ptrace (V.conjStarAlgEquiv (T.conditionalDensity x)) -
          ODEMixedOutput.pureOperator (padTarget κ ε s P x)).toLinearMap.IsSymmetric,
        ODEMixedOutput.hermitianTraceDistance
          (ptrace (V.conjStarAlgEquiv (T.conditionalDensity x)))
          (ODEMixedOutput.pureOperator (padTarget κ ε s P x)) h ≤ ε) :
    κ * Real.sqrt s * Real.log (1 / ε) / 3072 < T.worstCost w := by
  have h := pad_lower_bound_sharp κ ε s P hκ hs hε hε1 D hDm hrow hcol henc O w hO V T hT
  have hL : 0 < Real.log (1 / ε) := by
    have := L_ge ε hε hε1; have := log_64_gt; linarith
  have hs0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < s))
  have : 0 < κ * Real.sqrt s * Real.log (1 / ε) := by
    have : (0 : ℝ) < κ := by linarith
    positivity
  linarith

/-- **The padded lower bound for a clean output**, the case of a one-point garbage register:
the output space is the coordinate space of the padded family. -/
theorem pad_lower_bound_sharp_clean (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P]
    (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64)
    (D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s ⊕ P) Z s)
    (hDm : D.matrix = padFamily κ ε s P)
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (henc : ∃ enc : ((Ind κ ε s ⊕ P) × (Ind κ ε s ⊕ P)) → ℂ → Z,
      ∀ x α, D.table x α = enc α (D.matrix x α.1 α.2))
    (O : L → Inp κ ε s → K →L[ℂ] K) (w : L → ℕ) (hO : ∀ l, Admissible D (O l) (w l))
    (T : Tree O F (EuclideanSpace ℂ (Ind κ ε s ⊕ P)))
    (hT : ∀ x, 2 / 3 ≤ T.successMass x ∧
      ∃ h : (T.conditionalDensity x -
          ODEMixedOutput.pureOperator (padTarget κ ε s P x)).toLinearMap.IsSymmetric,
        ODEMixedOutput.hermitianTraceDistance (T.conditionalDensity x)
          (ODEMixedOutput.pureOperator (padTarget κ ε s P x)) h ≤ ε) :
    κ * Real.sqrt s * Real.log (1 / ε) / 1536 < T.worstCost w := by
  refine pad_lower_bound_sharp κ ε s P hκ hs hε hε1 D hDm hrow hcol henc O w hO unitGarbage T
    fun x => ?_
  rw [ptrace_unitGarbage]
  exact hT x

end Bounds

/-! ### Satisfiable access: permutation locators and a word code -/

section Cover

variable {X N Z : Type*} [Fintype N] [DecidableEq N] {s : ℕ}

omit [DecidableEq N] in
/-- A fixed embedding of the `s` slot labels into the indices. -/
def coverSlot (hs : s ≤ Fintype.card N) : Fin s ↪ N :=
  (Function.Embedding.nonempty_of_card_le (by simpa using hs)).some

/-- A fixed permutation of the indices mapping the slot labels onto a superset of `supp i`. -/
def coverPerm (supp : N → Finset N) (hsupp : ∀ i, (supp i).card ≤ s)
    (hs : s ≤ Fintype.card N) (i : N) : Equiv.Perm N :=
  Classical.choose (exists_perm_cover (Finset.univ.map (coverSlot hs)) (supp i)
    (by simpa using hsupp i))

/-- The slots of row `i` cover the support `supp i`. -/
theorem coverPerm_cover (supp : N → Finset N) (hsupp : ∀ i, (supp i).card ≤ s)
    (hs : s ≤ Fintype.card N) (i j : N) (hj : j ∈ supp i) :
    ∃ k, coverPerm supp hsupp hs i (coverSlot hs k) = j := by
  obtain ⟨a, ha, h⟩ := Classical.choose_spec (exists_perm_cover
    (Finset.univ.map (coverSlot hs)) (supp i) (by simpa using hsupp i)) j hj
  obtain ⟨k, -, rfl⟩ := Finset.mem_map.mp ha
  exact ⟨k, h⟩

/-- The location list of a row (and of a column): `k ↦ π_i (slot k)`. -/
def coverLoc (supp : N → Finset N) (hsupp : ∀ i, (supp i).card ≤ s)
    (hs : s ≤ Fintype.card N) (i : N) (k : Fin s) : N :=
  coverPerm supp hsupp hs i (coverSlot hs k)

/-- The location lists are injective. -/
theorem coverLoc_injective (supp : N → Finset N) (hsupp : ∀ i, (supp i).card ≤ s)
    (hs : s ≤ Fintype.card N) (i : N) : Function.Injective (coverLoc supp hsupp hs i) :=
  (coverPerm supp hsupp hs i).injective.comp (coverSlot hs).injective

/-- In-place row location as a basis permutation `(i, c) ↦ (i, π_i c)`. -/
def coverRowEquiv (supp : N → Finset N) (hsupp : ∀ i, (supp i).card ≤ s)
    (hs : s ≤ Fintype.card N) : (N × N) ≃ (N × N) :=
  Equiv.prodShear (Equiv.refl _) (coverPerm supp hsupp hs)

/-- In-place column location as a basis permutation `(j, c) ↦ (π_j c, j)`. -/
def coverColumnEquiv (supp : N → Finset N) (hsupp : ∀ i, (supp i).card ≤ s)
    (hs : s ≤ Fintype.card N) : (N × N) ≃ (N × N) :=
  (coverRowEquiv supp hsupp hs).trans (Equiv.prodComm _ _)

/-- **Native data with fixed permutation locators** covering input-independent supports `supp`
(of rows, and by `hcolM` of columns) and a fixed, address-independent word code `enc` of the
entries, decoded by `dec`; the generic form of `LinearSystemLowerBound.Hard.hardData`. -/
def coverData (supp : N → Finset N) (hsupp : ∀ i, (supp i).card ≤ s)
    (hs : s ≤ Fintype.card N) (hs0 : 0 < s) (M : X → Matrix N N ℂ)
    (hrowM : ∀ x i j, M x i j ≠ 0 → j ∈ supp i) (hcolM : ∀ x i j, M x i j ≠ 0 → i ∈ supp j)
    (enc : ℂ → Z) (dec : Z → ℂ) (hdec : ∀ z, ‖dec z‖ ≤ 1)
    (hde : ∀ x i j, dec (enc (M x i j)) = M x i j) :
    NativeSparseBlockEncoding.Data X N Z s where
  slot := coverSlot hs
  slots_pos := hs0
  scale := 1
  scale_pos := one_pos
  matrix := M
  table := fun x α => enc (M x α.1 α.2)
  decode := fun _ z => dec z
  decode_bound := fun _ z => hdec z
  decoded := fun x i j => hde x i j
  rowloc := fun _ => coverLoc supp hsupp hs
  colloc := fun _ => coverLoc supp hsupp hs
  row_injective := fun _ => coverLoc_injective supp hsupp hs
  column_injective := fun _ => coverLoc_injective supp hsupp hs
  row_covers := by
    intro x i j h
    obtain ⟨k, hk⟩ := coverPerm_cover supp hsupp hs i j (hrowM x i j h)
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
  column_covers := by
    intro x i j h
    obtain ⟨k, hk⟩ := coverPerm_cover supp hsupp hs j i (hcolM x i j h)
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
  rowOracle := fun _ => (LookupOracle.permutationUnitary
    (coverRowEquiv supp hsupp hs)).toLinearIsometry.toContinuousLinearMap
  columnOracle := fun _ => (LookupOracle.permutationUnitary
    (coverColumnEquiv supp hsupp hs)).toLinearIsometry.toContinuousLinearMap
  row_unitary := fun _ => LookupOracle.permutationUnitary_unitary _
  column_unitary := fun _ => LookupOracle.permutationUnitary_unitary _
  row_valid := by
    intro x i k
    change LookupOracle.permutationUnitary (coverRowEquiv supp hsupp hs) _ = _
    rw [LookupOracle.permutationUnitary_single]
    rfl
  column_valid := by
    intro x j k
    change LookupOracle.permutationUnitary (coverColumnEquiv supp hsupp hs) _ = _
    rw [LookupOracle.permutationUnitary_single]
    rfl

end Cover

section Code

/-- The word code of the padded entries: the code `enc` of the five hard entry values, and the
new value `5` for the identity entry `1`. -/
def padEnc (r : ℝ) (m : ℕ) (y : ℂ) : ZMod 8 := if y = 1 then 5 else enc r m y

/-- The fixed, address-independent decoder of the padded word code. -/
def padDec (r : ℝ) (m : ℕ) (z : ZMod 8) : ℂ := if z = 5 then 1 else dec r m z

/-- The code of the hard entries never uses the new value `5`. -/
theorem enc_ne_five (r : ℝ) (m : ℕ) (y : ℂ) : enc r m y ≠ 5 := by
  unfold enc
  split_ifs <;> decide

/-- The padded code decodes correctly on the six possible entry values. -/
theorem padDec_padEnc (r : ℝ) (m : ℕ) (y : ℂ)
    (hy : y = 1 ∨ (y = 0 ∨ y = 1 / 2 ∨ y = -((r : ℂ) / m) ∨ y = (r : ℂ) / 2 - (r : ℂ) / m ∨
      y = -((r : ℂ) / 2))) : padDec r m (padEnc r m y) = y := by
  unfold padEnc padDec
  by_cases h : y = 1
  · rw [if_pos h, if_pos rfl, h]
  · rw [if_neg h, if_neg (enc_ne_five r m y)]
    exact dec_enc r y (hy.resolve_left h)

/-- The decoded values have modulus at most one. -/
theorem norm_padDec_le (r : ℝ) (m : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hm2 : 2 ≤ m)
    (z : ZMod 8) : ‖padDec r m z‖ ≤ 1 := by
  unfold padDec
  split_ifs
  · simp
  · exact norm_dec_le r hr0 hr1 hm2 z

/-- The padded entries take the five hard values `0, 1/2, -r/m, r/2 - r/m, -r/2` and the
identity value `1`. -/
theorem padFamily_entry_cases (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P]
    (x : Inp κ ε s) (a b : Ind κ ε s ⊕ P) :
    padFamily κ ε s P x a b = 1 ∨ (padFamily κ ε s P x a b = 0 ∨
      padFamily κ ε s P x a b = 1 / 2 ∨
      padFamily κ ε s P x a b = -((rpar κ : ℂ) / (mpar s : ℂ)) ∨
      padFamily κ ε s P x a b = (rpar κ : ℂ) / 2 - (rpar κ : ℂ) / (mpar s : ℂ) ∨
      padFamily κ ε s P x a b = -((rpar κ : ℂ) / 2)) := by
  rcases a with i | p <;> rcases b with j | q
  · exact Or.inr (hard_entry_cases (rpar κ) x i j)
  · exact Or.inr (Or.inl (by simp [padFamily]))
  · exact Or.inr (Or.inl (by simp [padFamily]))
  · simp only [padFamily, Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

end Code

/-- **Access exists for the padded family**: native data on `Ind ⊕ P` with the padded
matrices, input-independent (fixed permutation) location oracles and a fixed word encoding of
the entries. -/
theorem exists_pad_access (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P]
    (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    ∃ D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s ⊕ P) (ZMod 8) s,
      D.matrix = padFamily κ ε s P ∧ (∀ x x', D.rowOracle x = D.rowOracle x') ∧
      (∀ x x', D.columnOracle x = D.columnOracle x') ∧
      ∃ enc : ℂ → ZMod 8, ∀ x α, D.table x α = enc (D.matrix x α.1 α.2) := by
  have hcount := clock_count κ ε hκ hε hε1
  have hm := mpar_le s hs
  have hm2 := lt_two_mpar s
  have hn := npar_pos κ ε hκ hε hε1
  have hcard : s ≤ Fintype.card (Ind κ ε s ⊕ P) := by
    rw [Fintype.card_sum]
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, hcount]
    have h1 : s ≤ 2 * mpar s := by omega
    have h2 : 2 * mpar s ≤ 2 * (2 * npar κ ε * mpar s) := by nlinarith
    omega
  have hm2' : 2 ≤ mpar s := by have := four_le_mpar s hs; omega
  have hr0 := rpar_nonneg κ hκ
  have hr1 := (rpar_lt_one κ hκ).le
  refine ⟨coverData (padSupport κ ε s P) (fun a => (padFamily_sparse κ ε s P hs a).1) hcard
    (by omega) (padFamily κ ε s P) (fun x a b h => ((padFamily_sparse κ ε s P hs a).2 x b).1 h)
    (fun x a b h => ((padFamily_sparse κ ε s P hs b).2 x a).2 h) (padEnc (rpar κ) (mpar s))
    (padDec (rpar κ) (mpar s)) (norm_padDec_le (rpar κ) (mpar s) hr0 hr1 hm2')
    (fun x a b => padDec_padEnc _ _ _ (padFamily_entry_cases κ ε s P x a b)), rfl,
    fun _ _ => rfl, fun _ _ => rfl, padEnc (rpar κ) (mpar s), fun _ _ => rfl⟩

/-- **The hypothesis of `bound_of_access` is satisfiable**: native data with the padded matrices
and `HardAccess` exists. -/
theorem exists_pad_hardAccess (κ ε : ℝ) (s : ℕ) (P : Type*) [Fintype P] [DecidableEq P]
    (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) :
    ∃ D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s ⊕ P) (ZMod 8) s,
      D.matrix = padFamily κ ε s P ∧ HardAccess D := by
  obtain ⟨D, hDm, hrow, hcol, enc, henc⟩ := exists_pad_access κ ε s P hκ hs hε hε1
  exact ⟨D, hDm, padAccess κ ε s P D hDm hrow hcol ⟨fun _ => enc, henc⟩⟩

/-! ### A common dimension -/

/-- The padding register `Fin (Nd - |Ind κ ε s|)` that brings the dimension to `Nd`. -/
abbrev PadReg (κ ε : ℝ) (s Nd : ℕ) : Type := Fin (Nd - Fintype.card (Ind κ ε s))

/-- **Exact dimension**: for `Nd ≥ |Ind κ ε s|`, the padded index type has exactly `Nd`
elements. -/
theorem padReg_card (κ ε : ℝ) (s Nd : ℕ) (hNd : Fintype.card (Ind κ ε s) ≤ Nd) :
    Fintype.card (Ind κ ε s ⊕ PadReg κ ε s Nd) = Nd := by
  rw [Fintype.card_sum, Fintype.card_fin]
  omega

/-- Every `Nd ≥ s κ ln(1/ε)` is at least the dimension of the hard family. -/
theorem card_ind_le (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64) (Nd : ℕ) (hNd : s * κ * Real.log (1 / ε) ≤ Nd) :
    Fintype.card (Ind κ ε s) ≤ Nd := by
  have h := (family_dimension κ ε s hκ hs hε hε1).2.2
  have : (Fintype.card (Ind κ ε s) : ℝ) < Nd := h.trans_le hNd
  exact_mod_cast this.le

/-- **The padded family in a prescribed dimension `Nd ≥ |Ind κ ε s|`**: on
`Ind κ ε s ⊕ PadReg κ ε s Nd` it has dimension exactly `Nd`, satisfies the promise and the
sparsity bound, and has native data with input-independent locators and an entry-determined
table. -/
theorem common_dimension (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 64) (Nd : ℕ) (hNd : Fintype.card (Ind κ ε s) ≤ Nd) :
    Fintype.card (Ind κ ε s ⊕ PadReg κ ε s Nd) = Nd ∧
      (∀ x : Inp κ ε s,
        ‖SparseStateOverlap.matrixOperator (padFamily κ ε s (PadReg κ ε s Nd) x)‖ ≤ 1 ∧
        IsUnit (SparseStateOverlap.matrixOperator (padFamily κ ε s (PadReg κ ε s Nd) x)) ∧
        ‖Ring.inverse (SparseStateOverlap.matrixOperator
          (padFamily κ ε s (PadReg κ ε s Nd) x))‖ ≤ κ) ∧
      (∀ a, (padSupport κ ε s (PadReg κ ε s Nd) a).card ≤ s) ∧
      ∃ D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s ⊕ PadReg κ ε s Nd)
          (ZMod 8) s,
        D.matrix = padFamily κ ε s (PadReg κ ε s Nd) ∧
        (∀ x x', D.rowOracle x = D.rowOracle x') ∧
        (∀ x x', D.columnOracle x = D.columnOracle x') ∧
        ∃ enc : ℂ → ZMod 8, ∀ x α, D.table x α = enc (D.matrix x α.1 α.2) :=
  ⟨padReg_card κ ε s Nd hNd, fun x => padFamily_promise κ ε s _ hκ x,
    fun a => (padFamily_sparse κ ε s _ hs a).1, exists_pad_access κ ε s _ hκ hs hε hε1⟩

section CommonBound

variable {Z : Type*} [Fintype Z] [AddCommGroup Z] {K F L : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **Theorem `qlsl:thm:main` in a prescribed dimension `Nd ≥ |Ind κ ε s|`**: the padded family
on `Ind κ ε s ⊕ PadReg κ ε s Nd` has dimension exactly `Nd`, and every algorithm as in
`pad_lower_bound_sharp` makes more than `κ √s ln(1/ε) / 1536` weighted native queries. -/
theorem lower_bound_common_dimension (κ ε : ℝ) (s : ℕ) (hκ : 32 ≤ κ) (hs : 5 ≤ s)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (Nd : ℕ) (hNd : Fintype.card (Ind κ ε s) ≤ Nd)
    (D : NativeSparseBlockEncoding.Data (Inp κ ε s) (Ind κ ε s ⊕ PadReg κ ε s Nd) Z s)
    (hDm : D.matrix = padFamily κ ε s (PadReg κ ε s Nd))
    (hrow : ∀ x x', D.rowOracle x = D.rowOracle x')
    (hcol : ∀ x x', D.columnOracle x = D.columnOracle x')
    (henc : ∃ enc : ((Ind κ ε s ⊕ PadReg κ ε s Nd) × (Ind κ ε s ⊕ PadReg κ ε s Nd)) → ℂ → Z,
      ∀ x α, D.table x α = enc α (D.matrix x α.1 α.2))
    (O : L → Inp κ ε s → K →L[ℂ] K) (w : L → ℕ) (hO : ∀ l, Admissible D (O l) (w l))
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [FiniteDimensional ℂ E] {G : Type*} [Fintype G] [DecidableEq G]
    (V : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ ((Ind κ ε s ⊕ PadReg κ ε s Nd) × G)) (T : Tree O F E)
    (hT : ∀ x, 2 / 3 ≤ T.successMass x ∧
      ∃ h : (ptrace (V.conjStarAlgEquiv (T.conditionalDensity x)) -
          ODEMixedOutput.pureOperator
            (padTarget κ ε s (PadReg κ ε s Nd) x)).toLinearMap.IsSymmetric,
        ODEMixedOutput.hermitianTraceDistance
          (ptrace (V.conjStarAlgEquiv (T.conditionalDensity x)))
          (ODEMixedOutput.pureOperator (padTarget κ ε s (PadReg κ ε s Nd) x)) h ≤ ε) :
    Fintype.card (Ind κ ε s ⊕ PadReg κ ε s Nd) = Nd ∧
      κ * Real.sqrt s * Real.log (1 / ε) / 1536 < T.worstCost w :=
  ⟨padReg_card κ ε s Nd hNd,
    pad_lower_bound_sharp κ ε s _ hκ hs hε hε1 D hDm hrow hcol henc O w hO V T hT⟩

end CommonBound

end

end LowerBoundRemarks.LinearSystemPadding
