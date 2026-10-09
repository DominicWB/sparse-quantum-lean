import SparseLowerBounds.Helpers.InstanceDecoder.Shape

set_option synthInstance.maxHeartbeats 400000

section
/-!
# The hard linear systems `A_X x = b`

Manuscript lines 5250-5318 and 5349-5388. For `n` hidden one-hot strings of
length `m = 2^μ` with marked positions `j : Fin n → Fin m`, and `R = 2^ρ`,
`r = 1 - 1/R` (`clockRatio ρ`):

* the clock transitions are `L_t = U_{j_t}` for `t < n` and `L_t = I` for
  `n ≤ t ≤ 2n - 2` (`hardTransition`; the manuscript indexes strings from 1, so
  its `U_{x^{(t+1)}}` is our `U_{j_t}`);
* `C_X = (I - r T_X)/2` on clock `Fin (2n)` ⊗ register `Fin m` (`hardC`,
  eq. `qlsl:eq:C`) and `A_X = [[0, C_X], [C_Xᵀ, 0]]` (`hardMatrix`,
  eq. `qlsl:eq:hermitian`) on `HardIndex n m = Fin 2 × Fin (2n) × Fin m`, so
  `N = 4mn`;
* the right-hand side `b = (b₀, 0)`, `b₀ = |0_L⟩ ⊗ |0⟩` (`hardRHS`), is
  input-independent, and the target is `x_A = A⁻¹ b / ‖A⁻¹ b‖`
  (`hardSolution`, eq. `qlsl:eq:target`), with `A` read as the release's
  bounded operator `SparseStateOverlap.matrixOperator A`.

Properties stated here: `A_X` is real symmetric (Hermitian) and indefinite,
has row and column sparsity at most `m + 1`, and satisfies the release QLS
promise `‖A‖ ≤ 1`, `A` invertible, `‖A⁻¹‖ ≤ 2R` (`2R ≤ κ` is
`two_hardR_le_kappa`); its actual condition number exceeds `R/4` once
`n ≥ R/2` (eq. `qlsl:eq:actualconditioning`).
-/

namespace SparseLowerBounds.LinearSystems

noncomputable section
open SparseHamiltonian
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace

/-- Sector × clock × register, `N = 4mn` (line 5302). -/
abbrev HardIndex (n m : ℕ) : Type := Fin 2 × Fin (2 * n) × Fin m

theorem card_hardIndex (n m : ℕ) : Fintype.card (HardIndex n m) = 4 * m * n := by
  simp only [HardIndex, Fintype.card_prod, Fintype.card_fin]
  ring

/-- The bounded operator of a matrix is `Matrix.toEuclideanCLM`, so its norm
is the `L²` operator norm of the matrix. -/
theorem matrixOperator_eq_toEuclideanCLM {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) :
    SparseStateOverlap.matrixOperator M = Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) M := by
  ext v i
  rw [SparseStateOverlap.matrixOperator_apply]
  rfl

theorem norm_matrixOperator {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) :
    ‖SparseStateOverlap.matrixOperator M‖ = ‖M‖ := by
  rw [matrixOperator_eq_toEuclideanCLM]
  rfl

variable {n μ : ℕ}

/-- The clock transitions `L_t` (line 5253). -/
def hardTransition (n μ : ℕ) (j : Fin n → Fin (2 ^ μ)) :
    ℕ → Matrix (Fin (2 ^ μ)) (Fin (2 ^ μ)) ℂ :=
  fun t => if h : t < n then gadget (2 ^ μ) (j ⟨t, h⟩) else 1

theorem hardTransition_mem_unitaryGroup (j : Fin n → Fin (2 ^ μ)) (t : ℕ) :
    hardTransition n μ j t ∈ Matrix.unitaryGroup (Fin (2 ^ μ)) ℂ := by
  unfold hardTransition
  split_ifs
  · exact gadget_mem_unitaryGroup _
  · exact one_mem _

/-- **Eq. `qlsl:eq:C`**: `C_X = (I - r T_X)/2`, `r = 1 - 1/2^ρ`. -/
def hardC (n μ ρ : ℕ) (j : Fin n → Fin (2 ^ μ)) :
    Matrix (Fin (2 * n) × Fin (2 ^ μ)) (Fin (2 * n) × Fin (2 ^ μ)) ℂ :=
  clockMatrix (2 * n) (clockRatio ρ) (hardTransition n μ j)

/-- **Eq. `qlsl:eq:hermitian`**: the hard matrix `A_X = [[0, C_X], [C_Xᵀ, 0]]`. -/
def hardMatrix (n μ ρ : ℕ) (j : Fin n → Fin (2 ^ μ)) :
    Matrix (HardIndex n (2 ^ μ)) (HardIndex n (2 ^ μ)) ℂ :=
  dilation (hardC n μ ρ j)

/-- The input-independent right-hand side `b = (b₀, 0)`, `b₀ = |0_L⟩ ⊗ |0⟩`
(lines 5266 and 5296). -/
def hardRHS (n μ : ℕ) : EuclideanSpace ℂ (HardIndex n (2 ^ μ)) :=
  WithLp.toLp 2 (sectorVec (atClock (2 * n) 0 (logical (2 ^ μ) false)) 0)

/-- The normalised solution `x_A = A⁻¹ b / ‖A⁻¹ b‖` (eq. `qlsl:eq:target`),
with the release's operator inverse; this is
`SparseLinearSystems.Endpoint.solutionState` for `b = hardRHS`. -/
def hardSolution (n μ ρ : ℕ) (j : Fin n → Fin (2 ^ μ)) : EuclideanSpace ℂ (HardIndex n (2 ^ μ)) :=
  ‖Ring.inverse (SparseStateOverlap.matrixOperator (hardMatrix n μ ρ j)) (hardRHS n μ)‖⁻¹ •
    Ring.inverse (SparseStateOverlap.matrixOperator (hardMatrix n μ ρ j)) (hardRHS n μ)

variable {ρ : ℕ}

theorem norm_hardRHS (hμ : 0 < μ) (hn : 0 < n) : ‖hardRHS n μ‖ = 1 := by
  rw [hardRHS, Helpers.InstanceDecoder.norm_sectorVec_zero_right,
    Helpers.InstanceDecoder.norm_atClock _ _ (by omega)]
  exact norm_logical (Nat.even_pow.mpr ⟨even_two, hμ.ne'⟩) (by positivity) false

/-- The transitions are real. -/
theorem star_hardTransition_apply (j : Fin n → Fin (2 ^ μ)) (t : ℕ) (a b : Fin (2 ^ μ)) :
    star (hardTransition n μ j t a b) = hardTransition n μ j t a b := by
  unfold hardTransition
  split_ifs
  · exact star_gadget_apply _ a b
  · rw [Matrix.one_apply]
    split_ifs <;> simp

theorem star_hardC_apply (j : Fin n → Fin (2 ^ μ)) (x y : Fin (2 * n) × Fin (2 ^ μ)) :
    star (hardC n μ ρ j x y) = hardC n μ ρ j x y :=
  Helpers.InstanceDecoder.star_clockMatrix_apply _ _ _ (star_hardTransition_apply j) x y

/-! ### Shape of the matrix (lines 5088, 5299-5309) -/

/-- `A_X` is real. -/
theorem star_hardMatrix_apply (j : Fin n → Fin (2 ^ μ)) (i i' : HardIndex n (2 ^ μ)) :
    star (hardMatrix n μ ρ j i i') = hardMatrix n μ ρ j i i' := by
  exact Helpers.InstanceDecoder.star_dilation_apply _ (star_hardC_apply j) i i'

/-- `A_X` is symmetric. -/
theorem hardMatrix_transpose (j : Fin n → Fin (2 ^ μ)) :
    (hardMatrix n μ ρ j)ᵀ = hardMatrix n μ ρ j := by
  exact Helpers.InstanceDecoder.dilation_transpose _ (star_hardC_apply j)

theorem hardMatrix_isHermitian (j : Fin n → Fin (2 ^ μ)) :
    Matrix.IsHermitian (hardMatrix n μ ρ j) := by
  exact isHermitian_dilation _

/-- `A_X` is indefinite: its quadratic form takes both signs (line 5088). -/
theorem hardMatrix_indefinite (hn : 0 < n) (j : Fin n → Fin (2 ^ μ)) :
    (∃ v : EuclideanSpace ℂ (HardIndex n (2 ^ μ)),
        0 < (⟪v, SparseStateOverlap.matrixOperator (hardMatrix n μ ρ j) v⟫_ℂ).re) ∧
      ∃ v : EuclideanSpace ℂ (HardIndex n (2 ^ μ)),
        (⟪v, SparseStateOverlap.matrixOperator (hardMatrix n μ ρ j) v⟫_ℂ).re < 0 := by
  classical
  set b : Fin (2 * n) × Fin (2 ^ μ) := (⟨0, by omega⟩, ⟨0, by positivity⟩) with hb
  have key : ∀ c : ℝ,
      ⟪EuclideanSpace.single ((0 : Fin 2), b) (1 : ℂ) + EuclideanSpace.single ((1 : Fin 2), b) (c : ℂ),
        SparseStateOverlap.matrixOperator (hardMatrix n μ ρ j)
          (EuclideanSpace.single ((0 : Fin 2), b) (1 : ℂ) +
            EuclideanSpace.single ((1 : Fin 2), b) (c : ℂ))⟫_ℂ = c := by
    intro c
    rw [inner_add_left, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left]
    simp only [SparseStateOverlap.matrixOperator_apply, PiLp.add_apply,
      PiLp.single_apply, mul_add, mul_ite, mul_one, mul_zero,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp [hardMatrix, dilation, hardC, clockMatrix, clockShift, hb]
    ring
  refine ⟨⟨EuclideanSpace.single ((0 : Fin 2), b) (1 : ℂ) +
    EuclideanSpace.single ((1 : Fin 2), b) ((1 : ℝ) : ℂ), ?_⟩,
    ⟨EuclideanSpace.single ((0 : Fin 2), b) (1 : ℂ) +
    EuclideanSpace.single ((1 : Fin 2), b) ((-1 : ℝ) : ℂ), ?_⟩⟩
  · rw [key 1]; simp
  · rw [key (-1)]; simp

/-- Row sparsity at most `m + 1` (lines 5306-5309). -/
theorem hardMatrix_row_sparse (j : Fin n → Fin (2 ^ μ)) (i : HardIndex n (2 ^ μ)) :
    (Finset.univ.filter fun i' => hardMatrix n μ ρ j i i' ≠ 0).card ≤ 2 ^ μ + 1 := by
  have h := Helpers.InstanceDecoder.dilation_clockMatrix_row_sparse (2 * n) (clockRatio ρ)
    (hardTransition n μ j) i
  rw [Fintype.card_fin] at h
  exact h

/-- Column sparsity at most `m + 1` (lines 5306-5309). -/
theorem hardMatrix_column_sparse (j : Fin n → Fin (2 ^ μ)) (i' : HardIndex n (2 ^ μ)) :
    (Finset.univ.filter fun i => hardMatrix n μ ρ j i i' ≠ 0).card ≤ 2 ^ μ + 1 := by
  have hsym : ∀ i, hardMatrix n μ ρ j i i' = hardMatrix n μ ρ j i' i := fun i => by
    conv_lhs => rw [← hardMatrix_transpose j]
    rfl
  simp only [hsym]
  exact hardMatrix_row_sparse j i'

/-! ### The QLS promise (eq. `qlsl:eq:Cpromise`, lines 5270-5275 and 5350-5351) -/

/-- `‖A_X‖ ≤ (1 + r)/2 ≤ 1`. -/
theorem norm_hardMatrix_le (j : Fin n → Fin (2 ^ μ)) :
    ‖SparseStateOverlap.matrixOperator (hardMatrix n μ ρ j)‖ ≤ 1 := by
  rw [norm_matrixOperator, hardMatrix, norm_dilation, hardC]
  have := norm_clockMatrix_le (T := 2 * n) (clockRatio_nonneg ρ) (fun t =>
    Helpers.InstanceDecoder.norm_le_one_of_mem_unitaryGroup (hardTransition_mem_unitaryGroup j t))
  linarith [clockRatio_lt_one ρ]

theorem isUnit_hardMatrix_matrix (j : Fin n → Fin (2 ^ μ)) :
    IsUnit (hardMatrix n μ ρ j) :=
  isUnit_dilation (isUnit_clockMatrix _)

theorem isUnit_hardMatrix (j : Fin n → Fin (2 ^ μ)) :
    IsUnit (SparseStateOverlap.matrixOperator (hardMatrix n μ ρ j)) := by
  rw [matrixOperator_eq_toEuclideanCLM]
  exact (isUnit_hardMatrix_matrix j).map _

/-- `‖A_X⁻¹‖ = ‖C_X⁻¹‖ ≤ 2R`. -/
theorem norm_inverse_hardMatrix_le (j : Fin n → Fin (2 ^ μ)) :
    ‖Ring.inverse (SparseStateOverlap.matrixOperator (hardMatrix n μ ρ j))‖ ≤ 2 * 2 ^ ρ := by
  rw [matrixOperator_eq_toEuclideanCLM,
    Helpers.InstanceDecoder.ringInverse_toEuclideanCLM (isUnit_hardMatrix_matrix j),
    ← Matrix.cstar_norm_def, hardMatrix, hardC, norm_inv_dilation (isUnit_clockMatrix _)]
  have h := norm_inv_clockMatrix_le (T := 2 * n) (clockRatio_nonneg ρ) (clockRatio_lt_one ρ)
    (fun t => Helpers.InstanceDecoder.norm_le_one_of_mem_unitaryGroup
      (hardTransition_mem_unitaryGroup j t)) (L := hardTransition n μ j)
  have he : 2 / (1 - clockRatio ρ) = 2 * 2 ^ ρ := by
    rw [clockRatio]; field_simp; ring
  rw [he] at h
  exact h

/-- **Actual conditioning** (eq. `qlsl:eq:actualconditioning`, lines 5368-5388):
for `n ≥ R/2`, `‖C_X⁻¹‖ > R/2` and `‖C_X‖ ≥ 1/2`, so
`R/4 < ‖A_X‖ ‖A_X⁻¹‖`. -/
theorem quarter_lt_cond (hn : 2 ^ ρ ≤ 2 * n) (j : Fin n → Fin (2 ^ μ)) :
    (2 ^ ρ : ℝ) / 4 <
      ‖SparseStateOverlap.matrixOperator (hardMatrix n μ ρ j)‖ *
        ‖Ring.inverse (SparseStateOverlap.matrixOperator (hardMatrix n μ ρ j))‖ := by
  haveI : Nonempty (Fin (2 ^ μ)) := ⟨⟨0, by positivity⟩⟩
  have hn' : 0 < 2 * n := by have := Nat.one_le_two_pow (n := ρ); omega
  rw [matrixOperator_eq_toEuclideanCLM]
  have hU : IsUnit (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := HardIndex n (2 ^ μ))
      (hardMatrix n μ ρ j)) := (isUnit_hardMatrix_matrix j).map _
  have h1 := Helpers.InstanceDecoder.half_le_norm_dilation hn' (clockRatio ρ) (hardTransition n μ j)
  have h2 := Helpers.InstanceDecoder.lt_norm_ringInverse_dilation hn (hardTransition n μ j)
    (hardTransition_mem_unitaryGroup j) hU
  have h3 : (0 : ℝ) < 2 ^ ρ / 2 := by positivity
  calc (2 ^ ρ : ℝ) / 4 = 1 / 2 * (2 ^ ρ / 2) := by ring
    _ < _ := mul_lt_mul' h1 h2 h3.le (by linarith)

/-- **The solution is the history state** (eqs. `qlsl:eq:history` and
`qlsl:eq:hermitian`): `A_X⁻¹ b = (0, C_X⁻¹ b₀)` with
`C_X⁻¹ b₀ = 2 Σ_{t<2n} r^t |t⟩ ⊗ ψ_t`. -/
theorem inverse_hardRHS (j : Fin n → Fin (2 ^ μ)) :
    Ring.inverse (SparseStateOverlap.matrixOperator (hardMatrix n μ ρ j)) (hardRHS n μ) =
      WithLp.toLp 2 (sectorVec 0 ((2 : ℂ) • ∑ t ∈ Finset.range (2 * n),
        ((clockRatio ρ : ℂ) ^ t) •
          atClock (2 * n) t (walk (hardTransition n μ j) (logical (2 ^ μ) false) t))) := by
  rw [matrixOperator_eq_toEuclideanCLM,
    Helpers.InstanceDecoder.ringInverse_toEuclideanCLM (isUnit_hardMatrix_matrix j), hardRHS,
    Matrix.toEuclideanCLM_toLp]
  congr 1
  rw [hardMatrix, hardC, inv_dilation_mulVec_sectorVec (isUnit_clockMatrix _), history]

end

end SparseLowerBounds.LinearSystems
end
