import SparseHamiltonian.OrientedEdgeCayley

/-!
# Actual sparse Cayley simulation and the improved filter degree

Here the input matrix has row and column Euclidean energies at most one.
The actual sparse lists determine the boundary, and the actual entries
determine the edge generator and explicit Cayley inverse.  Thus all the
analytic promises in the abstract improved simulator are discharged.

This is an operator-level correctness and filter-degree theorem.  Its
boundary still depends on the instance's locators.  Conjugating that boundary
to a fixed preparation and implementing the complete controlled clock layer
are required before this becomes the native sparse-oracle query theorem.
-/

namespace SparseHamiltonian.NativeCayleySimulation

noncomputable section
open ContinuousLinearMap SparseEdgeMoments CayleyClockInterface
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

omit [DecidableEq n] in
/-- A common row Euclidean bound includes a bound on every individual entry. -/
theorem entry_norm_le_one_of_row_energy (H : Matrix n n ℂ)
    (hrow : ∀ i, ∑ j, ‖H i j‖ ^ 2 ≤ 1) (i j : n) : ‖H i j‖ ≤ 1 := by
  exact SparseHamiltonian.norm_le_of_energy_le 1 (H i) zero_le_one
    (by simpa only [one_pow] using hrow i) j

/-- Exact cancellation of the sparse normalization in the target evolution. -/
theorem physical_exponent (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (hH : (D.matrix x).IsHermitian) (τ : ℝ) :
    (-Complex.I * ((τ * Real.sqrt (s : ℝ) : ℝ) : ℂ)) •
      ((boundary (D.rowloc x) (D.colloc x))† ∘L
        generator (D.matrix x) s ∘L boundary (D.rowloc x) (D.colloc x)) =
      (-Complex.I * (τ : ℂ)) • SparseStateOverlap.matrixOperator (D.matrix x) := by
  rw [generator_compression D.slots_pos (D.matrix x) hH (D.rowloc x) (D.colloc x)
    (D.row_covers x) (D.column_covers x), smul_smul]
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hRoot : (Real.sqrt (s : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hs).ne'
  congr 1
  simp only [Complex.ofReal_mul]
  field_simp [hRoot]

/-- An explicit simulator on the actual oriented sparse-edge Hilbert space. -/
def implementation (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (γ τ ε : ℝ) :=
  SharpClockSimulation.evolutionImplementation
    (OrientedEdgeCayley.action (D.matrix x) s γ)
    (boundary (D.rowloc x) (D.colloc x))
    (time (s : ℝ) τ γ) (width (s : ℝ) γ) (moment γ) ε

/-- The final clean output embedding depends only on the chosen public schedule. -/
def output (γ τ ε : ℝ) :=
  SharpClockSimulation.evolutionOutput (P := EuclideanSpace ℂ n) (V := OrientedSpace n)
    (time (s : ℝ) τ γ) (width (s : ℝ) γ) (moment γ) ε

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Full-output accuracy for an actual sparse matrix, with no assumed inverse,
moment certificate, or target unitary.  The bound is on the filter degree;
constant-cost native implementation of its complete reuse layers is separate. -/
theorem exists_precise_simulation (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (hH : (D.matrix x).IsHermitian)
    (hrow : ∀ i, ∑ j, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (hcol : ∀ j, ∑ i, ‖D.matrix x i j‖ ^ 2 ≤ 1)
    (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (s : ℝ) ∧
      (implementation D x γ τ ε)† ∘L implementation D x γ τ ε = 1 ∧
      (output (n := n) (s := s) γ τ ε)† ∘L output (n := n) (s := s) γ τ ε = 1 ∧
      ‖implementation D x γ τ ε - output (n := n) (s := s) γ τ ε ∘L
        NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
          SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε ∧
      (SharpFilterSchedule.degree (width (s : ℝ) γ)
        (time (s : ℝ) τ γ * moment γ) (ε / 3) : ℝ) ≤
        1536 * ImprovedPrecisionBudget.shape (s : ℝ) τ (ImprovedPrecisionBudget.targetLog ε) := by
  have hs : (1 : ℝ) ≤ s := by
    have hsNat : 1 ≤ s := D.slots_pos
    exact_mod_cast hsNat
  have hSelf : star (generator (D.matrix x) s) = generator (D.matrix x) s :=
    generator_adjoint (D.matrix x) s
  have hJ := boundary_isometry D.slots_pos (D.rowloc x) (D.colloc x)
    (D.row_injective x) (D.column_injective x)
  have hK := generator_norm_le (D.matrix x) s
    (entry_norm_le_one_of_row_energy (D.matrix x) hrow)
  have hKJ := native_generator_boundary_norm_le D x hrow hcol
  obtain ⟨γ, hγ, hγOne, hWidth, hIso, hError, hDegree⟩ :=
    CayleyClockInterface.exists_optimized_implementation
      (generator (D.matrix x) s) (boundary (D.rowloc x) (D.colloc x))
      (fun γ => OrientedEdgeCayley.inverse (D.matrix x) s γ)
      (s : ℝ) τ ε hs hτ hε hεOne hSelf hJ hK hKJ
      (fun γ _ _ => OrientedEdgeCayley.inverse_right (D.matrix x) s γ)
      (fun γ _ _ => OrientedEdgeCayley.inverse_left (D.matrix x) s γ)
  rw [physical_exponent D x hH τ] at hError
  rw [← OrientedEdgeCayley.action_eq_cayley (D.matrix x) s γ] at hIso hError
  refine ⟨γ, hγ, hγOne, hWidth, hIso, ?_, hError, hDegree⟩
  exact SharpClockSimulation.evolutionOutput_isometry _ _ _ _ (width_ge_one (s : ℝ) γ)

end
end SparseHamiltonian.NativeCayleySimulation
