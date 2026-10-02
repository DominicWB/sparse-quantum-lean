import SparseHamiltonian.SparseFlagEmbedding

/-!
# Block encodings from counted preparation programs

Composing a row-preparation program's adjoint with a column-preparation program
gives their exact overlap on a common fixed input encoding. The full physical
program is unitary, and its query counts are the sums of the two preparation
counts. Any extra common clean-output encoding cancels by isometry.
-/

namespace SparseHamiltonian.PreparedOverlapProgram

noncomputable section
open ContinuousLinearMap MultiOracleCircuit
open scoped InnerProduct

variable {X L K P V : Type*}
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  {O : L → X → K →L[ℂ] K}

/-- Run the column preparation followed by the inverse row preparation. -/
def program (r c : Program O) : Program O := .seq r.adjoint c

@[simp] theorem program_count (r c : Program O) :
    (program r c).count = r.count + c.count := by simp [program]

@[simp] theorem program_cost (r c : Program O) (w : L → ℕ) :
    (program r c).cost w = r.cost w + c.cost w := by simp [program]

@[simp] theorem program_labelCount [DecidableEq L] (r c : Program O) (l : L) :
    (program r c).labelCount l = r.labelCount l + c.labelCount l := by simp [program]

@[simp] theorem program_eval (r c : Program O) (x : X) :
    (program r c).eval x = (r.eval x)† ∘L c.eval x := by
  simp only [program, Program.eval_seq, Program.eval_adjoint,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def]

/-- Unitarity holds on all physical inputs, not only the clean subspace. -/
theorem program_unitary (r c : Program O) (hO : ∀ l x, OracleCircuit.IsUnitary (O l x))
    (x : X) : OracleCircuit.IsUnitary ((program r c).eval x) :=
  (program r c).eval_unitary hO x

/-- The compressed physical circuit is the overlap of its two actual outputs. -/
theorem compression (r c : Program O) (E : P →L[ℂ] K) (x : X) :
    E† ∘L (program r c).eval x ∘L E =
      (r.eval x ∘L E)† ∘L (c.eval x ∘L E) := by
  rw [program_eval, adjoint_comp]
  simp only [comp_assoc]

/-- A shared isometric output encoding, including clean ancillary registers,
cancels in the overlap. All input encodings are fixed independently of x. -/
theorem compression_of_preparations (r c : Program O) (E : P →L[ℂ] K)
    (J : V →ₗᵢ[ℂ] K) (R C : P →L[ℂ] V) (x : X)
    (hR : r.eval x ∘L E = J.toContinuousLinearMap ∘L R)
    (hC : c.eval x ∘L E = J.toContinuousLinearMap ∘L C) :
    E† ∘L (program r c).eval x ∘L E = R† ∘L C := by
  rw [compression, hR, hC, adjoint_comp]
  have hJ := LinearIsometry.adjoint_comp_self J
  calc
    (R† ∘L J.toContinuousLinearMap†) ∘L (J.toContinuousLinearMap ∘L C) =
        R† ∘L (J.toContinuousLinearMap† ∘L J.toContinuousLinearMap) ∘L C := by
      simp only [comp_assoc]
    _ = R† ∘L C := by rw [hJ]; rfl

/-- The local sparse-slot overlaps give the normalized matrix block of the
actual counted circuit, once its two preparation equations are supplied. -/
theorem sparse_compression {n : Type*} [Fintype n] [DecidableEq n] {s : ℕ}
    (r c : Program O) (E : EuclideanSpace ℂ n →L[ℂ] K)
    (J : SparseSlotStates.Space n →ₗᵢ[ℂ] K)
    (H : Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (rowloc colloc : n → Fin s → n)
    (hrow : ∀ i j, H i j ≠ 0 → SparseSlotStates.selected rowloc i j)
    (hcol : ∀ i j, H i j ≠ 0 → SparseSlotStates.selected colloc j i)
    (x : X)
    (hR : r.eval x ∘L E = J.toContinuousLinearMap ∘L SparseSlotStates.row H a rowloc)
    (hC : c.eval x ∘L E = J.toContinuousLinearMap ∘L SparseSlotStates.column H a colloc) :
    E† ∘L (program r c).eval x ∘L E =
      SparseStateOverlap.matrixOperator (fun i j => H i j / ((s : ℂ) * a)) := by
  rw [compression_of_preparations r c E J _ _ x hR hC]
  exact SparseSlotStates.overlap_eq_matrix H a ha rowloc colloc hrow hcol

end
end SparseHamiltonian.PreparedOverlapProgram
