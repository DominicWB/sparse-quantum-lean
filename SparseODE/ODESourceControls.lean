import SparseODE.ODESourceAmplification

/-!
# Two controlled source-preparation calls

The initial source preparation is controlled on the `none` label. The
constant forcing preparation is controlled on the `some` labels. Their
product realizes the source branch selector without one source query per
quadrature or LCHS node. Each factor is one of the supplied controlled
source-preparation calls, not a free gate or an oracle for the whole selector.
The supplied maps may depend on the unknown input: instantiate them at that
input before applying these pointwise identities.

-/

namespace SparseHamiltonian.ODESourceControls

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {ι P : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- A source label and a coherent LCHS label, with the public payload. -/
abbrev BranchSpace (ι P : Type*) [Fintype ι]
    [NormedAddCommGroup P] (N : ℕ) :=
  PiLp 2 (fun _ : Option (Fin N) × ι => P)

/-- The supplied initial preparation, controlled on the initial source. -/
def initial (J₀ : P →L[ℂ] P) (N : ℕ) :
    BranchSpace ι P N →L[ℂ] BranchSpace ι P N :=
  WeightedClock.diagonal
    (fun a : Option (Fin N) × ι => ODESourcePreparations.branch J₀ 1 N a.1)

/-- The supplied forcing preparation, controlled on every forcing source. -/
def forcing (Jb : P →L[ℂ] P) (N : ℕ) :
    BranchSpace ι P N →L[ℂ] BranchSpace ι P N :=
  WeightedClock.diagonal
    (fun a : Option (Fin N) × ι => ODESourcePreparations.branch 1 Jb N a.1)

theorem initial_unitary (J₀ : P →L[ℂ] P) (N : ℕ)
    (hJ₀ : IsUnitary J₀) : IsUnitary (initial (ι := ι) J₀ N) := by
  apply CoherentQuerySchedule.diagonal_unitary
  intro a
  rcases a with ⟨a, i⟩
  cases a with
  | none => exact hJ₀
  | some j => exact isUnitary_one

theorem forcing_unitary (Jb : P →L[ℂ] P) (N : ℕ)
    (hJb : IsUnitary Jb) : IsUnitary (forcing (ι := ι) Jb N) := by
  apply CoherentQuerySchedule.diagonal_unitary
  intro a
  rcases a with ⟨a, i⟩
  cases a with
  | none => exact isUnitary_one
  | some j => exact hJb

/-- Exactly two controlled calls, in the operator multiplication convention. -/
def combined (J₀ Jb : P →L[ℂ] P) (N : ℕ) :
    BranchSpace ι P N →L[ℂ] BranchSpace ι P N :=
  initial J₀ N * forcing Jb N

theorem combined_unitary (J₀ Jb : P →L[ℂ] P) (N : ℕ)
    (hJ₀ : IsUnitary J₀) (hJb : IsUnitary Jb) :
    IsUnitary (combined (ι := ι) J₀ Jb N) :=
  (initial_unitary (ι := ι) J₀ N hJ₀).mul
    (forcing_unitary (ι := ι) Jb N hJb)

omit [CompleteSpace P] in
/-- The two supported controls give the desired branch map on every vector. -/
theorem combined_eq_diagonal (J₀ Jb : P →L[ℂ] P) (N : ℕ) :
    combined (ι := ι) J₀ Jb N =
      WeightedClock.diagonal (fun a : Option (Fin N) × ι =>
        ODESourcePreparations.branch J₀ Jb N a.1) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro a
  change ODESourcePreparations.branch J₀ 1 N a.1
      (ODESourcePreparations.branch 1 Jb N a.1 (v a)) =
    ODESourcePreparations.branch J₀ Jb N a.1 (v a)
  rcases a with ⟨a, i⟩
  cases a <;> rfl

omit [CompleteSpace P] in
/-- Applying the two calls after the known coefficient preparation creates
the same input embedding used by the verified source-correctness theorem. -/
theorem combined_inputEmbedding (J₀ Jb : P →L[ℂ] P) (N : ℕ)
    (c : Option (Fin N) × ι → ℂ) :
    combined J₀ Jb N ∘L
        ODECoherentLCU.inputEmbedding c (fun _ => (1 : P →L[ℂ] P)) =
      ODECoherentLCU.inputEmbedding c (fun a =>
        ODESourcePreparations.branch J₀ Jb N a.1) := by
  rw [combined_eq_diagonal]
  unfold ODECoherentLCU.inputEmbedding
  rw [WeightedClock.diagonal_boundary]
  simp only [one_def, comp_id]

end
end SparseHamiltonian.ODESourceControls
