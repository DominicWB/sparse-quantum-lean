import SparseHamiltonian.ScaledNativeSimulation

/-!
# Query-free alignment of two fixed clean isometries

One extra Boolean spectator suffices to align any two fixed isometric
encodings.  The gate is explicit, works in infinite dimension, and depends
on neither the unknown oracle input nor its simulated evolution.
-/

namespace SparseHamiltonian.CleanOutputAlignment

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

abbrev Double (K : Type*) := HermitianDilation.Double K

/-- A Boolean spectator initialized to false. -/
def includeZero : K →L[ℂ] Double K :=
  WeightedClock.boundary (fun b : Bool => if b then 0 else 1) (fun _ => 1)

omit [CompleteSpace K] in
@[simp] theorem includeZero_apply_false (v : K) : includeZero v false = v := by
  simp [includeZero]

omit [CompleteSpace K] in
@[simp] theorem includeZero_apply_true (v : K) : includeZero v true = 0 := by
  simp [includeZero]

/-- The additional spectator preserves the entire vector norm. -/
theorem includeZero_isometry :
    (includeZero : K →L[ℂ] Double K)† ∘L includeZero = 1 := by
  apply WeightedClock.boundary_isometry
  · intro b; cases b <;> norm_num
  · norm_num [Fintype.sum_bool]
  · intro b; simp only [one_def, adjoint_id, id_comp]

/-- The self-adjoint partial-isometry completion with off-diagonal block
`F E†`.  No relationship between the ranges of `E` and `F` is required. -/
def completion (E F : P →L[ℂ] K) : Double K →L[ℂ] Double K :=
  WeightedClock.diagonal (fun b : Bool =>
    if b then E ∘L E† - 1 else 1 - F ∘L F†) +
      HermitianDilation.dilation (F ∘L E†)

@[simp] theorem completion_apply_false (E F : P →L[ℂ] K) (v : Double K) :
    completion E F v false = v false - F ((F†) (v false)) + F ((E†) (v true)) := by
  simp [completion]

@[simp] theorem completion_apply_true (E F : P →L[ℂ] K) (v : Double K) :
    completion E F v true = E ((E†) (v true)) - v true + E ((F†) (v false)) := by
  simp [completion, adjoint_comp]

/-- Self-adjointness holds for every pair of maps, even before the isometry
identities are imposed. -/
theorem completion_selfAdjoint (E F : P →L[ℂ] K) :
    (completion E F)† = completion E F := by
  simp only [completion, map_add, WeightedClock.diagonal_adjoint,
    HermitianDilation.dilation_selfAdjoint]
  congr 1
  apply congrArg WeightedClock.diagonal
  funext b
  cases b <;> simp [adjoint_comp]

/-- The explicit completion squares to identity on every workspace vector. -/
theorem completion_involution (E F : P →L[ℂ] K)
    (hE : E† ∘L E = 1) (hF : F† ∘L F = 1) (v : Double K) :
    completion E F (completion E F v) = v := by
  have hEv (u : P) : (E†) (E u) = u := by
    exact congrArg (fun A : P →L[ℂ] P => A u) hE
  have hFv (u : P) : (F†) (F u) = u := by
    exact congrArg (fun A : P →L[ℂ] P => A u) hF
  apply PiLp.ext
  intro b
  cases b <;>
    simp only [completion_apply_false, completion_apply_true, map_add, map_sub,
      hEv, hFv] <;> abel

/-- The completed gate is a full two-sided unitary. -/
theorem completion_unitary (E F : P →L[ℂ] K)
    (hE : E† ∘L E = 1) (hF : F† ∘L F = 1) :
    IsUnitary (completion E F) := by
  have hsq : completion E F ∘L completion E F = 1 := by
    apply ContinuousLinearMap.ext
    intro v
    exact completion_involution E F hE hF v
  change (completion E F)† ∘L completion E F = 1 ∧
    completion E F ∘L (completion E F)† = 1
  rw [completion_selfAdjoint]
  exact ⟨hsq, hsq⟩

/-- A fixed gate returning the simulated output to the original clean
encoding while also returning the additional spectator to false. -/
def align (E F : P →L[ℂ] K) : Double K →L[ℂ] Double K :=
  HermitianDilation.swap ∘L completion E F

theorem align_unitary (E F : P →L[ℂ] K)
    (hE : E† ∘L E = 1) (hF : F† ∘L F = 1) : IsUnitary (align E F) := by
  exact HermitianDilation.swap_unitary.mul (completion_unitary E F hE hF)

/-- Exact action on the complete output subspace. -/
theorem align_output (E F : P →L[ℂ] K)
    (_hE : E† ∘L E = 1) (hF : F† ∘L F = 1) :
    align E F ∘L includeZero ∘L F = includeZero ∘L E := by
  have hFv (u : P) : (F†) (F u) = u := by
    exact congrArg (fun A : P →L[ℂ] P => A u) hF
  ext u b
  cases b <;> simp [align, hFv]

/-- The common clean preparation is still an isometry. -/
theorem clean_isometry (E : P →L[ℂ] K) (hE : E† ∘L E = 1) :
    (includeZero ∘L E)† ∘L (includeZero ∘L E) = 1 := by
  rw [adjoint_comp, comp_assoc,
    ← comp_assoc ((includeZero : K →L[ℂ] Double K)†), includeZero_isometry]
  simpa only [one_def, id_comp] using hE

set_option maxHeartbeats 1000000 in
/-- Alignment preserves the full-output error exactly, including all
components orthogonal to the intended output subspace. -/
theorem align_error (E F : P →L[ℂ] K)
    (hE : E† ∘L E = 1) (hF : F† ∘L F = 1)
    (A : P →L[ℂ] K) (V : P →L[ℂ] P) :
    ‖align E F ∘L includeZero ∘L A - includeZero ∘L E ∘L V‖ = ‖A - F ∘L V‖ := by
  have hFV : align E F ∘L includeZero ∘L (F ∘L V) = includeZero ∘L E ∘L V := by
    rw [← comp_assoc (includeZero : K →L[ℂ] Double K),
      ← comp_assoc (align E F), align_output E F hE hF, comp_assoc]
  calc
    ‖align E F ∘L includeZero ∘L A - includeZero ∘L E ∘L V‖ =
        ‖align E F ∘L (includeZero ∘L (A - F ∘L V))‖ := by
          rw [comp_sub, comp_sub, hFV]
    _ = ‖includeZero ∘L (A - F ∘L V)‖ :=
      EncodedOracle.norm_comp_eq (P := Double K) (K := Double K) (H := P)
        (align E F) (align_unitary E F hE hF).1
        ((includeZero : K →L[ℂ] Double K) ∘L (A - F ∘L V))
    _ = ‖A - F ∘L V‖ :=
      EncodedOracle.norm_comp_eq (P := K) (K := Double K) (H := P)
        (includeZero : K →L[ℂ] Double K) (includeZero_isometry (K := K))
        (A - F ∘L V)

end
end SparseHamiltonian.CleanOutputAlignment
