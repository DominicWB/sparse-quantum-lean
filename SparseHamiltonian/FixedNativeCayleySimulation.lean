import SparseHamiltonian.UnitaryCayleyTransport

/-!
# Uniform sparse simulation with a fixed boundary preparation

Conjugating the full edge generator and its explicit inverse by the actual
locator unitary removes the unknown input from the boundary preparation.
The rescaling and schedule are selected once from public bounds and work
for every input in the oracle family. This establishes operator correctness
and the improved filter degree. `NativeCayleyProgram` constructs the
common-workspace implementation of the conjugated edge action, and
`ImprovedNativeSimulation` combines it with these bounds.
-/

namespace SparseHamiltonian.FixedNativeCayleySimulation

noncomputable section
open ContinuousLinearMap CayleyClockInterface
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- The generator in coordinates with an input-independent boundary. -/
def generator (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :=
  UnitaryCayleyTransport.conjugate (FixedLocatorConjugation.locator D x)
    (SparseEdgeMoments.generator (D.matrix x) s)

/-- The inverse is explicit on the entire private space, then conjugated. -/
def inverse (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (γ : ℝ) :=
  UnitaryCayleyTransport.conjugate (FixedLocatorConjugation.locator D x)
    (OrientedEdgeCayley.inverse (D.matrix x) s γ)

/-- Exact entrywise action preceded and followed by the locator and its inverse. -/
def action (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (γ : ℝ) :=
  UnitaryCayleyTransport.conjugate (FixedLocatorConjugation.locator D x)
    (OrientedEdgeCayley.action (D.matrix x) s γ)

/-- This preparation uses only the known slot embedding and sparsity. -/
def boundary (D : NativeSparseBlockEncoding.Data X n Z s) :=
  FixedLocatorConjugation.fixedBoundary D.slot

theorem boundary_isometry (D : NativeSparseBlockEncoding.Data X n Z s) :
    (boundary D)† ∘L boundary D = 1 :=
  FixedLocatorConjugation.fixedBoundary_isometry D.slot D.slots_pos

theorem generator_self_adjoint (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    star (generator D x) = generator D x :=
  UnitaryCayleyTransport.conjugate_self_adjoint _ _
    (SparseEdgeMoments.generator_adjoint (D.matrix x) s)

theorem generator_norm_le (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1) :
    ‖generator D x‖ ≤ Real.sqrt (s : ℝ) := by
  exact (UnitaryCayleyTransport.conjugate_norm_le _
    (FixedLocatorConjugation.locator_unitary D x) _).trans
    (SparseEdgeMoments.generator_norm_le (D.matrix x) s
      (NativeCayleySimulation.entry_norm_le_one_of_row_energy (D.matrix x) hrow))

theorem generator_boundary_norm_le (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1) :
    ‖generator D x ∘L boundary D‖ ≤ 1 := by
  have h := UnitaryCayleyTransport.boundary_norm_le
    (FixedLocatorConjugation.locator D x) (FixedLocatorConjugation.locator_unitary D x)
    (SparseEdgeMoments.generator (D.matrix x) s) (boundary D)
  change ‖generator D x ∘L boundary D‖ ≤
    ‖SparseEdgeMoments.generator (D.matrix x) s ∘L
      (FixedLocatorConjugation.locator D x ∘L
        FixedLocatorConjugation.fixedBoundary D.slot)‖ at h
  rw [FixedLocatorConjugation.locator_boundary D x] at h
  exact h.trans (SparseEdgeMoments.native_generator_boundary_norm_le D x hrow hcol)

theorem compression (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hH : (D.matrix x).IsHermitian) :
    (boundary D)† ∘L generator D x ∘L boundary D =
      (Real.sqrt (s : ℝ) : ℂ)⁻¹ • SparseStateOverlap.matrixOperator (D.matrix x) := by
  unfold generator boundary
  rw [UnitaryCayleyTransport.compression,
    FixedLocatorConjugation.locator_boundary D x]
  exact SparseEdgeMoments.generator_compression D.slots_pos (D.matrix x) hH
    (D.rowloc x) (D.colloc x) (D.row_covers x) (D.column_covers x)

theorem inverse_right (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (γ : ℝ) :
    (scaled (generator D x) γ - Complex.I •
      (1 : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n)) *
      inverse D x γ = 1 :=
  UnitaryCayleyTransport.inverse_right _ (FixedLocatorConjugation.locator_unitary D x)
    _ _ γ (OrientedEdgeCayley.inverse_right (D.matrix x) s γ)

theorem inverse_left (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (γ : ℝ) :
    inverse D x γ * (scaled (generator D x) γ - Complex.I •
      (1 : SparseEdgeMoments.OrientedSpace n →L[ℂ] SparseEdgeMoments.OrientedSpace n)) = 1 :=
  UnitaryCayleyTransport.inverse_left _ (FixedLocatorConjugation.locator_unitary D x)
    _ _ γ (OrientedEdgeCayley.inverse_left (D.matrix x) s γ)

theorem action_eq_cayley (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) (γ : ℝ) :
    action D x γ = ImprovedCayleyMoments.cayleyAction
      (scaled (generator D x) γ) (inverse D x γ) := by
  unfold action generator inverse
  rw [OrientedEdgeCayley.action_eq_cayley]
  exact UnitaryCayleyTransport.cayleyAction_conjugate _
    (FixedLocatorConjugation.locator_unitary D x) _ _ γ

/-- Sparse normalization and rescaling both cancel in the physical target. -/
theorem physical_exponent (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hH : (D.matrix x).IsHermitian) (τ γ : ℝ) (hγ : γ ≠ 0) :
    (-Complex.I * (time (s : ℝ) τ γ : ℂ)) • compressed (generator D x) (boundary D) γ =
      (-Complex.I * (τ : ℂ)) • SparseStateOverlap.matrixOperator (D.matrix x) := by
  rw [rescaled_exponent _ _ _ _ _ hγ]
  have hComp : (boundary D)† ∘L generator D x ∘L boundary D =
      (SparseEdgeMoments.boundary (D.rowloc x) (D.colloc x))† ∘L
        SparseEdgeMoments.generator (D.matrix x) s ∘L
        SparseEdgeMoments.boundary (D.rowloc x) (D.colloc x) := by
    unfold generator boundary
    rw [UnitaryCayleyTransport.compression,
      FixedLocatorConjugation.locator_boundary D x]
  rw [hComp]
  exact NativeCayleySimulation.physical_exponent D x hH τ

def implementation (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (γ τ ε : ℝ) :=
  SharpClockSimulation.evolutionImplementation (action D x γ) (boundary D)
    (time (s : ℝ) τ γ) (width (s : ℝ) γ) (moment γ) ε

def output (γ τ ε : ℝ) :=
  SharpClockSimulation.evolutionOutput (P := EuclideanSpace ℂ n)
    (V := SparseEdgeMoments.OrientedSpace n)
    (time (s : ℝ) τ γ) (width (s : ℝ) γ) (moment γ) ε

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- One public rescaling, fixed boundary, and schedule serve the whole oracle
family.  No inverse-existence, boundary-moment, or target-unitary premise is
assumed.  The resource here is the filter degree, not yet primitive queries. -/
theorem exists_uniform_precise_simulation
    (D : NativeSparseBlockEncoding.Data X n Z s)
    (hH : ∀ x, (D.matrix x).IsHermitian)
    (hrow : ∀ x i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ x j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      (boundary D)† ∘L boundary D = 1 ∧
      (output (n := n) (s := s) γ τ ε)† ∘L output (n := n) (s := s) γ τ ε = 1 ∧
      (SharpFilterSchedule.degree (width (s : ℝ) γ)
        (time (s : ℝ) τ γ * moment γ) (ε / 3) : ℝ) ≤
        1536 * ImprovedPrecisionBudget.shape (s : ℝ) τ (ImprovedPrecisionBudget.targetLog ε) ∧
      ∀ x, (implementation D x γ τ ε)† ∘L implementation D x γ τ ε = 1 ∧
        ‖implementation D x γ τ ε - output (n := n) (s := s) γ τ ε ∘L
          NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
            SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  have hs : (1 : ℝ) ≤ s := by
    have hsNat : 1 ≤ s := D.slots_pos
    exact_mod_cast hsNat
  obtain ⟨γ, hγ, hγOne, hWidth, hBudget⟩ :=
    ImprovedPrecisionBudget.exists_rescaling_for_precision (s : ℝ) τ ε hs hτ hε hεOne
  have ht : 0 ≤ time (s : ℝ) τ γ :=
    div_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _)) hγ.le
  refine ⟨γ, hγ, hγOne, hWidth, boundary_isometry D,
    SharpClockSimulation.evolutionOutput_isometry _ _ _ _ (width_ge_one (s : ℝ) γ),
    ?_, fun x => ?_⟩
  · have hMoment := moment_nonneg γ
    have hDegree := SharpFilterSchedule.degree_le (width (s : ℝ) γ)
      (time (s : ℝ) τ γ * moment γ) (ε / 3) (width_ge_one (s : ℝ) γ)
      (mul_nonneg ht hMoment) (by positivity) (by linarith)
    have hArg : 1 / (ε / 3) = 3 / ε := by ring
    unfold SharpFilterSchedule.logBudget at hDegree
    rw [hArg] at hDegree
    change time (s : ℝ) τ γ * moment γ + width (s : ℝ) γ *
      (1 + Real.log (3 / ε)) ≤
        12 * ImprovedPrecisionBudget.shape (s : ℝ) τ (ImprovedPrecisionBudget.targetLog ε)
      at hBudget
    have hMul := mul_le_mul_of_nonneg_left hBudget (by norm_num : (0 : ℝ) ≤ 128)
    calc
      _ ≤ 128 * (time (s : ℝ) τ γ * moment γ + width (s : ℝ) γ *
          (1 + Real.log (3 / ε))) := hDegree
      _ ≤ 128 * (12 * ImprovedPrecisionBudget.shape (s : ℝ) τ
          (ImprovedPrecisionBudget.targetLog ε)) := hMul
      _ = _ := by ring
  · obtain ⟨hIso, hError, _hDegree⟩ := CayleyClockInterface.evolution_error
      (generator D x) (inverse D x γ) (boundary D) (s : ℝ) γ
      (time (s : ℝ) τ γ) ε hγ.le hγOne (generator_self_adjoint D x)
      (boundary_isometry D) (generator_norm_le D x (hrow x))
      (generator_boundary_norm_le D x (hrow x) (hcol x))
      (inverse_right D x γ) (inverse_left D x γ) ht hε hεOne
    rw [physical_exponent D x (hH x) τ γ hγ.ne'] at hError
    rw [← action_eq_cayley D x γ] at hIso hError
    exact ⟨hIso, hError⟩

end
end SparseHamiltonian.FixedNativeCayleySimulation
