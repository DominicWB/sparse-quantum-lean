import SparseHamiltonian.SparseDyadicRounding

/-!
# Actual amplified magnitude bands with common native sparse access

The band masks alter only fixed decoder gates. All amplified bands and the
retained exact tail use literally the original row, column and value oracles,
with the same clean input and physical workspace. Band normalizations and
query bounds follow from the constructed sparse amplifier, not assumed costs.
-/
namespace SparseHamiltonian.ActualAmplifiedBands

noncomputable section
open ContinuousLinearMap NativeSparseAttenuation
open NativeSparseBlockEncoding (Data)
open scoped BigOperators InnerProduct
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- Locator coverage implies a support-cardinality bound; padded slots cause no issue. -/
theorem sparse_of_coverage (f : n → ℂ) (loc : Fin s → n)
    (h : ∀ i, f i ≠ 0 → ∃ k, loc k = i) : (nonzeroPositions f).card ≤ s := by
  classical
  have hsub : nonzeroPositions f ⊆ Finset.univ.image loc := by
    intro i hi
    have hf : f i ≠ 0 := by simpa [nonzeroPositions] using hi
    obtain ⟨k, hk⟩ := h i hf
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩
  exact (Finset.card_le_card hsub).trans (by simpa using
    (Finset.card_image_le : (Finset.univ.image loc).card ≤ (Finset.univ : Finset (Fin s)).card))

/-- Native row coverage supplies the sparsity promise used in band estimates. -/
theorem row_sparse (D : Data X n Z s) (x : X) (i : n) :
    (nonzeroPositions (D.matrix x i)).card ≤ s :=
  sparse_of_coverage (D.matrix x i) (D.rowloc x i) (fun j hj => by simpa [SparseSlotStates.selected] using D.row_covers x i j hj)

/-- The independent column locator supplies its own sparsity promise. -/
theorem column_sparse (D : Data X n Z s) (x : X) (j : n) :
    (nonzeroPositions (fun i => D.matrix x i j)).card ≤ s :=
  sparse_of_coverage (fun i => D.matrix x i j) (D.colloc x j)
    (fun i hi => by simpa [SparseSlotStates.selected] using D.column_covers x i j hi)

/-- The two existing dyadic scale definitions agree exactly. -/
theorem threshold_eq (η : ℝ) (j : ℕ) : BandCost.threshold η j = dyadicScale η j := rfl

/-- Public positive slot count, in the form used by scalar band accounting. -/
theorem one_le_s (D : Data X n Z s) : (1 : ℝ) ≤ s := by
  exact_mod_cast D.slots_pos

variable [Fintype Z] [AddCommGroup Z] [DecidableEq Z]

omit [DecidableEq Z] in
/-- Spectator extension does not change equality of the original oracle families. -/
@[simp] theorem band_oracles (D : Data X n Z s) (a : ℝ) (ha : 0 < a) :
    oracles (NativeBandEncoding.band D a ha) = oracles D := rfl

omit [DecidableEq Z] in
@[simp] theorem tail_oracles (D : Data X n Z s) (a : ℝ) (ha : 0 < a) :
    oracles (NativeBandEncoding.tail D a ha) = oracles D := rfl

/-- Every band uses the same clean input in the enlarged physical workspace. -/
@[simp] theorem band_input (D : Data X n Z s) (a : ℝ) (ha : 0 < a) :
    input (NativeBandEncoding.band D a ha) = input D := rfl

@[simp] theorem tail_input (D : Data X n Z s) (a : ℝ) (ha : 0 < a) :
    input (NativeBandEncoding.tail D a ha) = input D := rfl

/-- Common physical compression for all programs in the family. -/
def block (D : Data X n Z s) (p : MultiOracleCircuit.Program (oracles D)) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  (input D).toContinuousLinearMap† ∘L p.eval x ∘L (input D).toContinuousLinearMap

/-- Target operator for one dyadic magnitude band. -/
def bandOperator (D : Data X n Z s) (η : ℝ) (j : ℕ) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  SparseStateOverlap.matrixOperator (bandMatrix (BandCost.threshold η j) (D.matrix x))

/-- Target operator for the exact low-magnitude tail. -/
def tailOperator (D : Data X n Z s) (η : ℝ) (b : ℕ) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  SparseStateOverlap.matrixOperator (tailMatrix (BandCost.threshold η b) (D.matrix x))

/-- One concrete amplified band, with its normalization, native query count,
Hermiticity and dimension-free matrix error. -/
theorem exists_band (D : Data X n Z s) (η : ℝ) (hη : 0 < η)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hCol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (j : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ α : ℝ, ∃ p : MultiOracleCircuit.Program (oracles D),
      0 < α ∧ (64 / 9) * BandCost.normalization s η j ≤ α ∧
      α ≤ 1024 * BandCost.normalization s η j ∧
      (p.count : ℝ) < 24 * BandCost.queryRatio s η j *
        (Real.log (2 / δ) / Real.log 4 + 1) ∧
      (∀ x, OracleCircuit.IsUnitary (p.eval x)) ∧
      (∀ x, (block D p x)† = block D p x) ∧
      ∀ x, ‖(α : ℂ) • block D p x - bandOperator D η j x‖ ≤
        BandCost.normalization s η j * (2 * δ + δ ^ 2) := by
  let a := BandCost.threshold η j
  have ha : 0 < a := BandCost.threshold_pos hη j
  let E := NativeBandEncoding.band D a ha
  have hs := one_le_s D
  have hb := BandCost.normalization_pos hs hη j
  have hbu : BandCost.normalization s η j ≤ (s : ℝ) * E.scale := min_le_left _ _
  have hEH : ∀ x, (E.matrix x).IsHermitian := fun x =>
    bandMatrix_isHermitian (D.matrix x) (hH x) a
  have hER : ∀ x i, ∑ k, ‖E.matrix x i k‖ ≤ BandCost.normalization s η j := by
    intro x i
    exact bandMatrix_row_sum_le (D.matrix x) a η s ha (row_sparse D x) (hRow x) i
  have hEC : ∀ x k, ∑ i, ‖E.matrix x i k‖ ≤ BandCost.normalization s η j := by
    intro x k
    exact bandMatrix_column_sum_le (D.matrix x) a η s ha (column_sparse D x) (hCol x) k
  exact ActualSparseAmplifier.exists_program E (BandCost.normalization s η j)
    hb hbu hEH hER hEC δ hδ hδ1

/-- The exact tail uses the same enlarged workspace, at unit attenuation. -/
def tailProgram (D : Data X n Z s) (η : ℝ) (hη : 0 < η) (b : ℕ) :
    MultiOracleCircuit.Program (oracles D) :=
  NativeSparseAttenuation.program
    (NativeBandEncoding.tail D (BandCost.threshold η b) (BandCost.threshold_pos hη b))
    1 (by norm_num)

@[simp] theorem tailProgram_count (D : Data X n Z s) (η : ℝ) (hη : 0 < η) (b : ℕ) :
    (tailProgram D η hη b).count = 6 :=
  NativeSparseAttenuation.program_count _ 1 _

/-- No small entries are discarded; rescaling the tail compression is exact. -/
theorem tail_exact (D : Data X n Z s) (η : ℝ) (hη : 0 < η) (b : ℕ) (x : X) :
    (BandCost.tailNormalization s η b : ℂ) • block D (tailProgram D η hη b) x =
      tailOperator D η b x := by
  let E := NativeBandEncoding.tail D (BandCost.threshold η b) (BandCost.threshold_pos hη b)
  have hc := NativeSparseAttenuation.compression E 1 (by norm_num) x
  change block D (tailProgram D η hη b) x = _ at hc
  simp only [Complex.ofReal_one, one_pow, one_smul] at hc
  rw [hc]
  have hp : (s : ℝ) * E.scale ≠ 0 :=
    ne_of_gt (mul_pos (by exact_mod_cast D.slots_pos) E.scale_pos)
  have hscale : (BandCost.tailNormalization s η b : ℂ) = (s : ℂ) * E.scale := by
    simp only [BandCost.tailNormalization, E, NativeBandEncoding.tail, BandCost.threshold,
      Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_pow,
      Complex.ofReal_ofNat]
    ring
  rw [hscale]
  simpa only [Complex.ofReal_mul, Complex.ofReal_natCast, tailOperator, E,
    NativeBandEncoding.tail] using
    (SparseMatrixNorm.matrixOperator_scale_normalized (E.matrix x) ((s : ℝ) * E.scale) hp).symm

/-- The tail circuit is globally unitary for all oracle inputs. -/
theorem tail_unitary (D : Data X n Z s) (η : ℝ) (hη : 0 < η) (b : ℕ) (x : X) :
    OracleCircuit.IsUnitary ((tailProgram D η hη b).eval x) :=
  NativeSparseAttenuation.program_unitary _ 1 (by norm_num) x


/-- The retained tail has a Hermitian compressed block. -/
theorem tail_selfadjoint (D : Data X n Z s) (η : ℝ) (hη : 0 < η) (b : ℕ)
    (hH : ∀ x, (D.matrix x).IsHermitian) (x : X) :
    (block D (tailProgram D η hη b) x)† = block D (tailProgram D η hη b) x := by
  let E := NativeBandEncoding.tail D (BandCost.threshold η b) (BandCost.threshold_pos hη b)
  have hc := NativeSparseAttenuation.compression E 1 (by norm_num) x
  change block D (tailProgram D η hη b) x = _ at hc
  simp only [Complex.ofReal_one, one_pow, one_smul] at hc
  rw [hc]
  exact SparseValuePrecision.matrixOperator_star_eq _
    (NativePolynomialOverlap.normalized_isHermitian E x
      (tailMatrix_isHermitian (D.matrix x) (hH x) _))

/-- Actual band circuits and the exact tail, all with the same physical oracle family.
This structure records proved circuit properties; `family` constructs it below. -/
structure Family (D : Data X n Z s) (η : ℝ) (b : ℕ) (δ : ℝ) where
  normalization : Fin b → ℝ
  program : Fin b → MultiOracleCircuit.Program (oracles D)
  normalization_pos : ∀ j : Fin b, 0 < normalization j
  normalization_lower : ∀ j : Fin b, (64 / 9) * BandCost.normalization s η j ≤ normalization j
  normalization_upper : ∀ j : Fin b, normalization j ≤ 1024 * BandCost.normalization s η j
  count_lt : ∀ j : Fin b, ((program j).count : ℝ) < 24 * BandCost.queryRatio s η j *
    (Real.log (2 / δ) / Real.log 4 + 1)
  unitary : ∀ (j : Fin b) x, OracleCircuit.IsUnitary ((program j).eval x)
  selfadjoint : ∀ (j : Fin b) x, (block D (program j) x)† = block D (program j) x
  error : ∀ (j : Fin b) x, ‖(normalization j : ℂ) • block D (program j) x - bandOperator D η j x‖ ≤
    BandCost.normalization s η j * (2 * δ + δ ^ 2)
  tailProgram : MultiOracleCircuit.Program (oracles D)
  tail_count : tailProgram.count = 6
  tail_unitary : ∀ x, OracleCircuit.IsUnitary (tailProgram.eval x)
  tail_selfadjoint : ∀ x, (block D tailProgram x)† = block D tailProgram x
  tail_exact : ∀ x, (BandCost.tailNormalization s η b : ℂ) • block D tailProgram x =
    tailOperator D η b x

/-- Public matrix bounds construct the entire counted band family. No program,
normalization or query-cost bound is supplied as an assumption. -/
def family (D : Data X n Z s) (η : ℝ) (hη : 0 < η)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hCol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (b : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) : Family D η b δ := by
  classical
  choose α p hpos hlo hup hc hu hsa he using
    (fun j : Fin b => exists_band D η hη hH hRow hCol j δ hδ hδ1)
  exact {
    normalization := α
    program := p
    normalization_pos := hpos
    normalization_lower := hlo
    normalization_upper := hup
    count_lt := hc
    unitary := hu
    selfadjoint := hsa
    error := he
    tailProgram := tailProgram D η hη b
    tail_count := tailProgram_count D η hη b
    tail_unitary := tail_unitary D η hη b
    tail_selfadjoint := tail_selfadjoint D η hη b hH
    tail_exact := tail_exact D η hη b }

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The zero-energy case is exactly the zero Hamiltonian, before any normalization. -/
theorem matrix_zero_of_energy_zero (D : Data X n Z s)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 0) :
    ∀ x, D.matrix x = 0 := by
  intro x
  ext i j
  apply norm_eq_zero.mp
  have h := norm_le_of_energy_le 0 (D.matrix x i) le_rfl (by simpa using hRow x i) j
  exact le_antisymm h (norm_nonneg _)


omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- Exact operator decomposition into all dyadic bands and the retained tail. -/
theorem operator_decomposition (D : Data X n Z s) (η : ℝ) (hη : 0 ≤ η)
    (hRow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2) (b : ℕ) (x : X) :
    (∑ j : Fin b, bandOperator D η j x) + tailOperator D η b x =
      SparseStateOverlap.matrixOperator (D.matrix x) := by
  ext v i
  simp only [bandOperator, tailOperator, _root_.add_apply,
    _root_.sum_apply, PiLp.add_apply, WithLp.ofLp_sum, Finset.sum_apply,
    SparseStateOverlap.matrixOperator_apply]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_mul, ← add_mul]
  congr 1
  have hsum := Fin.sum_univ_eq_sum_range
    (fun j : ℕ => bandMatrix (BandCost.threshold η j) (D.matrix x) i k) b
  exact (congrArg (fun z : ℂ => z + tailMatrix (BandCost.threshold η b)
    (D.matrix x) i k) hsum).trans
    (bandMatrix_decomposition (D.matrix x) η hη (hRow x) b i k)

end
end SparseHamiltonian.ActualAmplifiedBands
