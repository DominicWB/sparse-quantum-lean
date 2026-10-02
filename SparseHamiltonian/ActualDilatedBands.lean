import SparseHamiltonian.NativeDilationLayout

/-!
# Counted native reflections for the actual amplified band family

Bands and the retained tail are placed in one common computational basis.
Every physical program is a genuine full-space unitary involution. Its
compression is exactly the original Hermitian block, and its primitive query
count is exactly six times the supplied actual band count. All query labels
still name only the original sparse primitives with spectator registers.
-/
namespace SparseHamiltonian.ActualDilatedBands

noncomputable section
open ContinuousLinearMap OracleCircuit
open ActualAmplifiedBands ActualAmplifiedBandResources
open NativeSparseBlockEncoding (Data Query)
open scoped BigOperators InnerProduct
set_option maxRecDepth 2000
set_option maxHeartbeats 800000

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z]
  [AddCommGroup Z] [DecidableEq Z] {s b : ℕ} {η δ : ℝ}

/-- A single finite index contains every amplified band and the retained tail. -/
abbrev Index (b : ℕ) := Fin (b + 1)

/-- The actual programs before Hermitian dilation. -/
abbrev baseProgram {D : Data X n Z s} (F : Family D η b δ) := termProgram F

/-- The original actual normalizations are unchanged by dilation. -/
abbrev normalization {D : Data X n Z s} (F : Family D η b δ) := termNormalization F

/-- Target operators in the same index order as the actual resource family. -/
def target (D : Data X n Z s) : Index b → X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  Fin.lastCases (tailOperator D η b) (fun j x => bandOperator D η j x)

/-- Only the amplified bands have a nonzero error budget. -/
def errorBudget : Index b → ℝ :=
  Fin.lastCases 0 (fun j => BandCost.normalization s η j * (2 * δ + δ ^ 2))

/-- One fixed physical basis for the entire reflected family. -/
abbrev Basis (n Z : Type*) := NativeDilationLayout.Basis (NativeAttenuatedLayout.Basis n Z)

/-- Decidable equality is derived explicitly for the nested spectator basis. -/
instance instDecidableEqBasis : DecidableEq (Basis n Z) :=
  @instDecidableEqProd _ _ inferInstance
    (@instDecidableEqProd _ _
      (@instDecidableEqProd _ _
        (@instDecidableEqProd _ _ inferInstance inferInstance) inferInstance) inferInstance)


/-- Original primitive labels survive both fixed layout changes and spectator extension. -/
abbrev oracle (D : Data X n Z s) (l : Query) (x : X) :=
  NativeDilationLayout.oracle (NativeAttenuatedLayout.oracle D) l x

/-- Fixed valid input for every primitive in the final common basis. -/
def cleanBasis (D : Data X n Z s) : Basis n Z :=
  NativeDilationLayout.cleanBasis (NativeAttenuatedLayout.cleanBasis D)

/-- Only the original primitive's image label depends on the matrix oracle. -/
def image (D : Data X n Z s) (l : Query) (x : X) : Basis n Z :=
  NativeDilationLayout.imageBasis (NativeAttenuatedLayout.cleanBasis D)
    (NativeAttenuatedLayout.image D l x)

omit [DecidableEq Z] in
/-- Full-space unitarity of the original spectator queries. -/
theorem oracle_unitary (D : Data X n Z s) (l : Query) (x : X) :
    IsUnitary (oracle D l x) :=
  NativeDilationLayout.oracle_unitary _ (NativeAttenuatedLayout.oracle_unitary D) l x

/-- Exact valid-basis promises are inherited, ready for native clock masking. -/
theorem valid (D : Data X n Z s) (l : Query) (x : X) :
    oracle D l x (EuclideanSpace.single (cleanBasis D) 1) =
      EuclideanSpace.single (image D l x) 1 :=
  NativeDilationLayout.valid _ (NativeAttenuatedLayout.cleanBasis D)
    (NativeAttenuatedLayout.image D) (NativeAttenuatedLayout.valid D) l x

/-- One common fixed public input, independent of band and oracle input. -/
def input (D : Data X n Z s) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ (Basis n Z) :=
  NativeDilationLayout.input (NativeAttenuatedLayout.cleanBasis D) (NativeAttenuatedLayout.input D)

/-- The common input is an isometry. -/
theorem input_isometry (D : Data X n Z s) : (input D)† ∘L input D = 1 :=
  NativeDilationLayout.input_isometry _ _ (NativeAttenuatedLayout.input_isometry D)

/-- Actual native reflection for either an amplified band or the exact tail. -/
def program {D : Data X n Z s} (F : Family D η b δ) (i : Index b) :
    MultiOracleCircuit.Program (oracle D) :=
  NativeDilationLayout.program (NativeAttenuatedLayout.oracle D)
    (NativeAttenuatedLayout.cleanBasis D) (NativeAttenuatedLayout.program D (baseProgram F i))

/-- Dilation uses exactly six native calls per original counted primitive. -/
@[simp] theorem program_count {D : Data X n Z s} (F : Family D η b δ) (i : Index b) :
    (program F i).count = 6 * (baseProgram F i).count := by
  simp [program]

/-- The same factor holds for arbitrary per-label native query weights. -/
@[simp] theorem program_cost {D : Data X n Z s} (F : Family D η b δ)
    (i : Index b) (w : Query → ℕ) :
    (program F i).cost w = 6 * (baseProgram F i).cost w := by
  simp [program]

/-- Every full physical band program is unitary. -/
theorem program_unitary {D : Data X n Z s} (F : Family D η b δ) (i : Index b) (x : X) :
    IsUnitary ((program F i).eval x) :=
  NativeDilationLayout.program_unitary _ (NativeAttenuatedLayout.oracle_unitary D) _ _ x

/-- The reflection identity holds on the complete enlarged Hilbert space. -/
theorem program_involution {D : Data X n Z s} (F : Family D η b δ) (i : Index b) (x : X) :
    (program F i).eval x ∘L (program F i).eval x = 1 :=
  NativeDilationLayout.program_involution _ (NativeAttenuatedLayout.oracle_unitary D) _ _ x

/-- Exact full-space self-adjointness, with no compressed-space qualification. -/
theorem program_selfadjoint {D : Data X n Z s} (F : Family D η b δ)
    (i : Index b) (x : X) : ((program F i).eval x)† = (program F i).eval x :=
  NativeDilationLayout.program_selfAdjoint _ _ _ x

/-- Both branch cases have a Hermitian block before dilation. -/
theorem base_selfadjoint {D : Data X n Z s} (F : Family D η b δ) (i : Index b) (x : X) :
    (block D (baseProgram F i) x)† = block D (baseProgram F i) x := by
  exact term_selfadjoint F i x

/-- Native Hermitian dilation preserves each original compressed band exactly. -/
theorem compression {D : Data X n Z s} (F : Family D η b δ) (i : Index b) (x : X) :
    (input D)† ∘L (program F i).eval x ∘L input D = block D (baseProgram F i) x := by
  have hH : ((NativeAttenuatedLayout.input D)† ∘L
      (NativeAttenuatedLayout.program D (baseProgram F i)).eval x ∘L
      NativeAttenuatedLayout.input D)† =
      (NativeAttenuatedLayout.input D)† ∘L
      (NativeAttenuatedLayout.program D (baseProgram F i)).eval x ∘L
      NativeAttenuatedLayout.input D := by
    rw [NativeAttenuatedLayout.compression]
    exact base_selfadjoint F i x
  have h := NativeDilationLayout.compression_eq (NativeAttenuatedLayout.oracle D)
    (NativeAttenuatedLayout.oracle_unitary D) (NativeAttenuatedLayout.cleanBasis D)
    (NativeAttenuatedLayout.image D) (NativeAttenuatedLayout.valid D)
    (NativeAttenuatedLayout.program D (baseProgram F i)) (NativeAttenuatedLayout.input D) x hH
  simpa only [NativeAttenuatedLayout.compression, input, program, block] using h

/-- Positive normalizations for all indices, including the exact tail. -/
theorem normalization_pos {D : Data X n Z s} (F : Family D η b δ) (hη : 0 < η)
    (i : Index b) : 0 < normalization F i := by
  exact termNormalization_pos F hη i

/-- The physical reflected encodings inherit the proved matrix error budgets. -/
theorem error {D : Data X n Z s} (F : Family D η b δ) (i : Index b) (x : X) :
    ‖(normalization F i : ℂ) • ((input D)† ∘L (program F i).eval x ∘L input D) -
      target (η := η) D i x‖ ≤ errorBudget (s := s) (η := η) (δ := δ) i := by
  rw [compression]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [normalization, baseProgram, termNormalization, termProgram, target,
      errorBudget, Fin.lastCases_last, F.tail_exact, sub_self, norm_zero, le_refl]
  · simpa only [normalization, baseProgram, termNormalization, termProgram, target,
      errorBudget, Fin.lastCases_castSucc] using F.error j x

/-- The exact tail now requires thirty-six original native calls. -/
@[simp] theorem tail_count {D : Data X n Z s} (F : Family D η b δ) :
    (program F (Fin.last b)).count = 36 := by
  simp [baseProgram, termProgram, F.tail_count]


/-- The common public input as the linear isometry required by the clock API. -/
def inputIsometry (D : Data X n Z s) : EuclideanSpace ℂ n →ₗᵢ[ℂ] EuclideanSpace ℂ (Basis n Z) where
  toLinearMap := (input D).toLinearMap
  norm_map' := (input D).norm_map_iff_adjoint_comp_self.mpr (input_isometry D)

@[simp] theorem inputIsometry_toContinuousLinearMap (D : Data X n Z s) :
    (inputIsometry D).toContinuousLinearMap = input D := rfl

/-- Public weights preserve each actual branch's individual normalization. -/
def weights {D : Data X n Z s} (F : Family D η b δ) (i : Index b) : ℝ :=
  termNormalization F i / totalNormalization F

/-- All weights are positive, including the retained tail. -/
theorem weights_pos {D : Data X n Z s} (F : Family D η b δ) (hη : 0 < η) (i : Index b) :
    0 < weights F i :=
  div_pos (termNormalization_pos F hη i) (totalNormalization_pos F hη)

/-- The normalized family weights sum to one exactly. -/
theorem weights_sum {D : Data X n Z s} (F : Family D η b δ) (hη : 0 < η) :
    ∑ i, weights F i = 1 := by
  simp only [weights, ← Finset.sum_div]
  exact div_self (totalNormalization_pos F hη).ne'

/-- The weighted reflected clock generates the actual approximate Hamiltonian
scaled by its public total normalization. -/
theorem generator_scale {D : Data X n Z s} (F : Family D η b δ) (hη : 0 < η) (x : X) :
    (totalNormalization F : ℂ) • MultiWeightedProgramClockBounds.generator
      (weights F) (program F) (fun _ => inputIsometry D) x = approximateHamiltonian F x := by
  rw [MultiWeightedProgramClockBounds.generator_eq_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [inputIsometry_toContinuousLinearMap, compression, smul_smul]
  have hcancel : (totalNormalization F : ℂ) * (weights F i : ℂ) =
      (termNormalization F i : ℂ) := by
    rw [weights, Complex.ofReal_div]
    have hn : (totalNormalization F : ℂ) ≠ 0 := by
      exact_mod_cast (totalNormalization_pos F hη).ne'
    field_simp
  rw [hcancel]

/-- The generator identity also preserves the weighted heterogeneous clock budget. -/
theorem averageLength_scale_le {D : Data X n Z s} (F : Family D η b δ) (hη : 0 < η) :
    totalNormalization F * MultiWeightedProgramClockBounds.averageLength
      (weights F) (program F) ≤ 6 * weightedLength F := by
  unfold MultiWeightedProgramClockBounds.averageLength weightedLength
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hpos := (termNormalization_pos F hη i).le
  have hcancel : totalNormalization F * weights F i = termNormalization F i := by
    unfold weights
    calc
      totalNormalization F * (termNormalization F i / totalNormalization F) =
          termNormalization F i * (totalNormalization F / totalNormalization F) := by ring
      _ = termNormalization F i := by rw [div_self (totalNormalization_pos F hη).ne', mul_one]
  rw [← mul_assoc, hcancel]
  have hslot : (MultiQueryClock.slots (program F i) : ℝ) ≤
      6 * (((termProgram F i).count + 2 : ℕ) : ℝ) := by
    simp only [MultiQueryClock.slots, program_count, baseProgram, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat]
    linarith
  exact (mul_le_mul_of_nonneg_left hslot hpos).trans_eq (by ring)

/-- A single public clock length bound covers every fully dilated branch. -/
theorem slots_le {D : Data X n Z s} (F : Family D η b δ) (hη : 0 < η)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (i : Index b) :
    MultiQueryClock.slots (program F i) ≤ 6 * clockBound s δ := by
  have h := term_count_le_clockBound F hη hδ hδ1 i
  simp only [MultiQueryClock.slots, program_count, baseProgram]
  omega

end
end SparseHamiltonian.ActualDilatedBands
