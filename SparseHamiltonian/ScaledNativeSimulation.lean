import SparseHamiltonian.NativeSparseRescaling

/-!
# General normalization and signed time for the improved native simulation

Public normalization changes only the exact-entry decoder. Its original native
oracle family and fixed workspace embeddings are preserved. Circuit reversal
then covers either sign of time with no increase in primitive query count.
-/

namespace SparseHamiltonian.ScaledNativeSimulation

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Normalizing by a positive row/column energy bound leaves the actual native
queries unchanged. The simulated exponent is exactly that of the original
matrix, with no perturbation or extra error allocation. -/
theorem exists_positive_time_simulation (D : Data X n Z s)
    (η : ℝ) (hη : 0 < η)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (t ε : ℝ) (ht : 0 ≤ t) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (K := NativeCayleyActive.Physical n Z
            (ImprovedNativeSimulation.slots (s : ℝ) γ (η * t) ε)
            (ImprovedNativeSimulation.degree (s : ℝ) γ (η * t) ε))
          (ImprovedNativeSimulation.oracle D γ (η * t) ε),
        (p.count : ℝ) ≤ 497664 * ImprovedPrecisionBudget.shape
          (s : ℝ) (η * t) (ImprovedPrecisionBudget.targetLog ε) ∧
        (ImprovedNativeSimulation.input D γ (η * t) ε)† ∘L
          ImprovedNativeSimulation.input D γ (η * t) ε = 1 ∧
        (ImprovedNativeSimulation.output D γ (η * t) ε)† ∘L
          ImprovedNativeSimulation.output D γ (η * t) ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L ImprovedNativeSimulation.input D γ (η * t) ε -
            ImprovedNativeSimulation.output D γ (η * t) ε ∘L
              NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hOut, hAction⟩ :=
    ImprovedNativeSimulation.exists_native_simulation
      (NativeSparseRescaling.normalize D η hη)
      (fun x => NativeSparseRescaling.normalize_hermitian D η hη x (hH x))
      (fun x i => NativeSparseRescaling.normalized_row_energy D η hη x i (hrow x i))
      (fun x j => NativeSparseRescaling.normalized_column_energy D η hη x j (hcol x j))
      (η * t) ε (mul_nonneg hη.le ht) hε hεOne
  change MultiOracleCircuit.Program
    (K := NativeCayleyActive.Physical n Z
      (ImprovedNativeSimulation.slots (s : ℝ) γ (η * t) ε)
      (ImprovedNativeSimulation.degree (s : ℝ) γ (η * t) ε))
    (ImprovedNativeSimulation.oracle D γ (η * t) ε) at p
  refine ⟨γ, hγ, hγOne, hWidth, p, hCount, ?_, ?_, fun x => ?_⟩
  · simpa only [NativeSparseRescaling.input_normalize] using hIn
  · simpa only [NativeSparseRescaling.output_normalize] using hOut
  · refine ⟨(hAction x).1, ?_⟩
    rw [← NativeSparseRescaling.exponent_cancel D η hη x t]
    exact (hAction x).2

/-- The scheduled physical oracle contains the original primitive sparse
queries, including the same unchanged unitary extensions on dirty inputs. -/
abbrev oracle (D : Data X n Z s) (γ η t ε : ℝ) :
    Query → X → NativeCayleyActive.Physical n Z
      (ImprovedNativeSimulation.slots (s : ℝ) γ (η * |t|) ε)
      (ImprovedNativeSimulation.degree (s : ℝ) γ (η * |t|) ε) →L[ℂ]
      NativeCayleyActive.Physical n Z
        (ImprovedNativeSimulation.slots (s : ℝ) γ (η * |t|) ε)
        (ImprovedNativeSimulation.degree (s : ℝ) γ (η * |t|) ε) :=
  ImprovedNativeSimulation.oracle D γ (η * |t|) ε

/-- Known input preparation, selected only by the public time's sign. -/
def signedInput (D : Data X n Z s) (γ η t ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] NativeCayleyActive.Physical n Z
      (ImprovedNativeSimulation.slots (s : ℝ) γ (η * |t|) ε)
      (ImprovedNativeSimulation.degree (s : ℝ) γ (η * |t|) ε) :=
  LabeledAdjointSimulation.signedInput
    (ImprovedNativeSimulation.input D γ (η * |t|) ε)
    (ImprovedNativeSimulation.output D γ (η * |t|) ε) t

/-- Known output preparation for the same public schedule and time sign. -/
def signedOutput (D : Data X n Z s) (γ η t ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ] NativeCayleyActive.Physical n Z
      (ImprovedNativeSimulation.slots (s : ℝ) γ (η * |t|) ε)
      (ImprovedNativeSimulation.degree (s : ℝ) γ (η * |t|) ε) :=
  LabeledAdjointSimulation.signedOutput
    (ImprovedNativeSimulation.input D γ (η * |t|) ε)
    (ImprovedNativeSimulation.output D γ (η * |t|) ε) t

omit [DecidableEq Z] in
theorem oracle_unitary (D : Data X n Z s) (γ η t ε : ℝ) (l : Query) (x : X) :
    IsUnitary (oracle D γ η t ε l x) :=
  NativeCayleyActive.oracle_unitary D
    (ImprovedNativeSimulation.slots (s : ℝ) γ (η * |t|) ε)
    (ImprovedNativeSimulation.degree (s : ℝ) γ (η * |t|) ε) l x

/-- The improved primitive query bound for arbitrary real time and positive
public row/column normalization. The fixed preparations are uniform over every
unknown oracle input. Adjoint reversal has the exact same literal query count. -/
theorem exists_native_simulation (D : Data X n Z s)
    (η : ℝ) (hη : 0 < η)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ η ^ 2)
    (t ε : ℝ) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (K := NativeCayleyActive.Physical n Z
            (ImprovedNativeSimulation.slots (s : ℝ) γ (η * |t|) ε)
            (ImprovedNativeSimulation.degree (s : ℝ) γ (η * |t|) ε))
          (oracle D γ η t ε),
        (p.count : ℝ) ≤ 497664 * ImprovedPrecisionBudget.shape
          (s : ℝ) (η * |t|) (ImprovedPrecisionBudget.targetLog ε) ∧
        (signedInput D γ η t ε)† ∘L signedInput D γ η t ε = 1 ∧
        (signedOutput D γ η t ε)† ∘L signedOutput D γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L signedInput D γ η t ε - signedOutput D γ η t ε ∘L
            NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  obtain ⟨γ, hγ, hγOne, hWidth, p, hCount, hIn, hOut, hAction⟩ :=
    exists_positive_time_simulation D η hη hH hrow hcol |t| ε
      (abs_nonneg t) hε hεOne
  have hIso := LabeledAdjointSimulation.signed_isometries
    (ImprovedNativeSimulation.input D γ (η * |t|) ε)
    (ImprovedNativeSimulation.output D γ (η * |t|) ε) hIn hOut t
  refine ⟨γ, hγ, hγOne, hWidth, LabeledAdjointSimulation.signedProgram p t,
    ?_, hIso.1, hIso.2, fun x => ?_⟩
  · rw [LabeledAdjointSimulation.signedProgram_count]
    exact hCount
  · refine ⟨(LabeledAdjointSimulation.signedProgram p t).eval_unitary
      (oracle_unitary D γ η t ε) x, ?_⟩
    exact LabeledAdjointSimulation.signed_program_error p
      (oracle_unitary D γ η t ε)
      (ImprovedNativeSimulation.input D γ (η * |t|) ε)
      (ImprovedNativeSimulation.output D γ (η * |t|) ε)
      (fun x => SparseStateOverlap.matrixOperator (D.matrix x))
      (fun x => SparseValuePrecision.matrixOperator_star_eq _ (hH x)) t ε
      (fun x => (hAction x).2) x

/-- The standard spectral bound supplies all row/column energy promises. -/
theorem exists_native_simulation_of_spectral_bound (D : Data X n Z s)
    (η : ℝ) (hη : 0 < η)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hNorm : ∀ x, ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ η)
    (t ε : ℝ) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      ∃ p : MultiOracleCircuit.Program
          (K := NativeCayleyActive.Physical n Z
            (ImprovedNativeSimulation.slots (s : ℝ) γ (η * |t|) ε)
            (ImprovedNativeSimulation.degree (s : ℝ) γ (η * |t|) ε))
          (oracle D γ η t ε),
        (p.count : ℝ) ≤ 497664 * ImprovedPrecisionBudget.shape
          (s : ℝ) (η * |t|) (ImprovedPrecisionBudget.targetLog ε) ∧
        (signedInput D γ η t ε)† ∘L signedInput D γ η t ε = 1 ∧
        (signedOutput D γ η t ε)† ∘L signedOutput D γ η t ε = 1 ∧
        ∀ x, IsUnitary (p.eval x) ∧
          ‖p.eval x ∘L signedInput D γ η t ε - signedOutput D γ η t ε ∘L
            NormedSpace.exp ((-Complex.I * (t : ℂ)) •
              SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε :=
  exists_native_simulation D η hη hH
    (SparseSpectralEnergy.native_energies D η hH hNorm).1
    (SparseSpectralEnergy.native_energies D η hH hNorm).2 t ε hε hεOne

end
end SparseHamiltonian.ScaledNativeSimulation
