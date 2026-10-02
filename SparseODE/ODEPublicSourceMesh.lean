import SparseODE.ODESourcePadding

/-!
# A public source mesh for the actual sparse ODE

The sparse oracle represents M, and the differential-equation generator is
A = -M. Its known decoder scale gives a uniform operator-norm bound, hence a
single source mesh chosen before the unknown matrix or source vectors. The
mesh refines only the coherent source register; it adds no matrix-query
factor. Source quadrature, source mass, duration bounds and the actual
Duhamel solution's norm are conclusions of the certificate below.

-/

namespace SparseHamiltonian.ODEPublicSourceMesh

noncomputable section
open ContinuousLinearMap NativeSparseBlockEncoding SparseStateOverlap
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n] {s : ℕ}

/-- The differential-equation generator represented by the original matrix
oracle. The sign is the one used by the LCHS Hamiltonian reduction. -/
def generator (D : Data X n Z s) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  -matrixOperator (D.matrix x)

/-- The original decoder and locator promises give a public operator-norm
bound. This intentionally coarse bound is used only to choose free mesh
labels; the sharper row/column energies still control the query count. -/
theorem norm_generator_le (D : Data X n Z s) (x : X) :
    ‖generator D x‖ ≤ (s : ℝ) * D.scale := by
  rw [generator, norm_neg]
  apply SparseValuePrecision.norm_matrixOperator_le_nonneg _ _
    (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
  · intro i
    exact SparseValuePrecision.sum_norm_le_of_sparse (D.matrix x i) s D.scale
      D.scale_pos.le (NativeRoundedEncoding.row_sparse D x i)
      (NativeRoundedEncoding.entry_bound D x i)
  · intro j
    exact SparseValuePrecision.sum_norm_le_of_sparse (fun i => D.matrix x i j) s D.scale
      D.scale_pos.le (NativeRoundedEncoding.column_sparse D x j)
      (fun i => NativeRoundedEncoding.entry_bound D x i j)

/-- Positivity of the represented matrix's Hermitian real part gives
contractivity of the canonical negative generator. -/
theorem generator_dissipative (D : Data X n Z s) (x : X)
    (hPSD : ∀ v : EuclideanSpace ℂ n,
      0 ≤ (inner ℂ v
        (matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) v)).re) :
    ODEDissipative.Dissipative (generator D x) := by
  apply ODEHermitianReduction.negative_generator_dissipative (matrixOperator (D.matrix x))
  intro v
  simpa only [ODEMatrixEnergy.matrixOperator_dissipativePart] using hPSD v

/-- A fixed positive number of source branches, depending only on public
sparsity, decoder scale, time and tolerance. -/
def meshSize (D : Data X n Z s) (T ν : ℝ) : ℕ :=
  Nat.ceil (T * ((s : ℝ) * D.scale) / ν) + 1

theorem meshSize_pos (D : Data X n Z s) (T ν : ℝ) :
    0 < meshSize D T ν := by
  exact Nat.zero_lt_succ _

/-- The chosen mesh is strictly larger than the sufficient real threshold. -/
theorem meshSize_strict (D : Data X n Z s) (T ν : ℝ) :
    T * ((s : ℝ) * D.scale) / ν < (meshSize D T ν : ℝ) := by
  calc
    _ ≤ (Nat.ceil (T * ((s : ℝ) * D.scale) / ν) : ℝ) := Nat.le_ceil _
    _ < (meshSize D T ν : ℝ) := by
      simp only [meshSize, Nat.cast_add, Nat.cast_one]
      linarith

/-- The mesh budget required to bound the complete source integral. -/
theorem meshSize_bound (D : Data X n Z s) (T ν : ℝ) (hν : 0 < ν) :
    T * ((s : ℝ) * D.scale) ≤ ν * (meshSize D T ν : ℝ) := by
  have h := (div_lt_iff₀ hν).mp (meshSize_strict D T ν)
  simpa only [mul_comm] using h.le

/-- The actual exponential quadrature on the public mesh attains relative
source tolerance uniformly over the unknown matrix and both source vectors.
No division by a source norm is used, so zero source terms cause no exception. -/
theorem approximation_error (D : Data X n Z s) (T ν : ℝ)
    (hT : 0 ≤ T) (hν : 0 < ν) (x : X)
    (hA : ODEDissipative.Dissipative (generator D x))
    (v b : EuclideanSpace ℂ n) :
    ‖ODESourceQuadrature.approximation (generator D x) v b T (meshSize D T ν) -
        ODEConstantForcing.solution (generator D x) v b T‖ ≤
      ν * (‖v‖ + T * ‖b‖) := by
  have hN := meshSize_pos D T ν
  have hNr : 0 < (meshSize D T ν : ℝ) := by exact_mod_cast hN
  have hMesh := meshSize_bound D T ν hν
  have hTb : 0 ≤ T * ‖b‖ := mul_nonneg hT (norm_nonneg b)
  have hNumerator : T ^ 2 * ‖generator D x‖ * ‖b‖ ≤
      (ν * (‖v‖ + T * ‖b‖)) * (meshSize D T ν : ℝ) := by
    calc
      T ^ 2 * ‖generator D x‖ * ‖b‖ ≤
          T ^ 2 * ((s : ℝ) * D.scale) * ‖b‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (norm_generator_le D x) (sq_nonneg T))
          (norm_nonneg b)
      _ = (T * ((s : ℝ) * D.scale)) * (T * ‖b‖) := by ring
      _ ≤ (ν * (meshSize D T ν : ℝ)) * (T * ‖b‖) :=
        mul_le_mul_of_nonneg_right hMesh hTb
      _ = (ν * (T * ‖b‖)) * (meshSize D T ν : ℝ) := by ring
      _ ≤ (ν * (‖v‖ + T * ‖b‖)) * (meshSize D T ν : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (norm_nonneg v)) hν.le) hNr.le
  exact (ODESourceQuadrature.approximation_error (generator D x) hA v b T hT
    (meshSize D T ν) hN).trans ((div_le_iff₀ hNr).mpr hNumerator)

/-- The complete source-branch certificate for the original sparse ODE.
Its mesh is fixed before x, v and b; all norm and quadrature statements are
proved from the original oracle data and dissipativity of its generator. -/
theorem branches_certificate (D : Data X n Z s) (T ν : ℝ)
    (hT : 0 ≤ T) (hν : 0 < ν) (x : X)
    (hA : ODEDissipative.Dissipative (generator D x))
    (v b : EuclideanSpace ℂ n) :
    let N := meshSize D T ν
    0 < N ∧
      ODESourceBranches.mass (ODESourceBranches.sourceVector v b T N) = ‖v‖ + T * ‖b‖ ∧
      (∀ a : Option (Fin N),
        0 ≤ ODESourceBranches.duration T N a ∧ ODESourceBranches.duration T N a ≤ T) ∧
      ‖ODEConstantForcing.solution (generator D x) v b T‖ ≤
        ODESourceBranches.mass (ODESourceBranches.sourceVector v b T N) ∧
      ‖(∑ a, ODESourceBranches.propagation (generator D x) T N a
          (ODESourceBranches.sourceVector v b T N a)) -
        ODEConstantForcing.solution (generator D x) v b T‖ ≤
        ν * ODESourceBranches.mass (ODESourceBranches.sourceVector v b T N) := by
  let N := meshSize D T ν
  have hN : 0 < N := meshSize_pos D T ν
  have hmass := ODESourceBranches.mass_sourceVector v b T hT N hN
  refine ⟨hN, hmass, ?_, ?_, ?_⟩
  · intro a
    cases a with
    | none => exact ⟨hT, le_rfl⟩
    | some i => exact ⟨ODESourceQuadrature.time_nonneg T hT N i,
        ODESourceQuadrature.time_le T hT N hN i⟩
  · rw [hmass]
    exact ODEConstantForcing.solution_norm_le (generator D x) hA v b T hT
  · have hsum :
        (∑ a, ODESourceBranches.propagation (generator D x) T N a
          (ODESourceBranches.sourceVector v b T N a)) =
        ODEErrorBudget.finiteDuhamel (NormedSpace.exp (T • generator D x))
          (fun i : Fin N => NormedSpace.exp (ODESourceQuadrature.time T N i • generator D x))
          v (ODESourceQuadrature.weight T N) (fun _ => b) := by
      simpa only [ODESourceBranches.propagation, ODESourceBranches.duration] using
        ODESourceBranches.source_sum_eq_finiteDuhamel v b T N
          (ODESourceBranches.propagation (generator D x) T N)
    rw [hsum, ODESourceQuadrature.finiteDuhamel_eq_approximation, hmass]
    exact approximation_error D T ν hT hν x hA v b

end
end SparseHamiltonian.ODEPublicSourceMesh
