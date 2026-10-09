import SparseODE.ODEPrimitiveSourceJoin

/-!
# Two controlled source-preparation calls with a label-dependent forcing

Time-dependent counterpart of `SparseHamiltonian.ODESourceControls`. The
initial source preparation is the released call
`SparseHamiltonian.ODESourceControls.initial`, controlled on the `none` label.
The forcing preparation may now depend coherently on the quadrature label: on
every forcing label `some q` it applies the supplied preparation `Jb q`, and it
is the identity on the initial label. This label-controlled operator is one
supplied source call, exactly as the constant forcing call of the released
module. The product of the two calls realizes the time-dependent source branch
selector `branchTD` without one source query per quadrature or LCHS node. The
supplied maps may depend on the unknown input: instantiate them at that input
before applying these pointwise identities.
-/

namespace SparseHamiltonian.TimeDependentODE.SourceTD

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {ι P : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  {N : ℕ}

/-- The initial preparation on `none`, and the forcing preparation of the
quadrature node `q` on the label `some q`. -/
def branchTD (J₀ : P →L[ℂ] P) (Jb : Fin N → P →L[ℂ] P) :
    Option (Fin N) → P →L[ℂ] P
  | none => J₀
  | some q => Jb q

/-- The supplied label-dependent forcing preparation, controlled on every
forcing source: it applies `Jb q` on the label `some q`. -/
def forcing (Jb : Fin N → P →L[ℂ] P) :
    ODESourceControls.BranchSpace ι P N →L[ℂ] ODESourceControls.BranchSpace ι P N :=
  WeightedClock.diagonal
    (fun a : Option (Fin N) × ι => branchTD 1 Jb a.1)

omit [CompleteSpace P] in
/-- The forcing call is literally the label-controlled diagonal operator. -/
theorem forcing_eq (Jb : Fin N → P →L[ℂ] P) :
    forcing (ι := ι) Jb =
      WeightedClock.diagonal (fun a : Option (Fin N) × ι =>
        match a.1 with
        | none => 1
        | some q => Jb q) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro a
  rcases a with ⟨a, i⟩
  cases a <;> rfl

theorem forcing_unitary (Jb : Fin N → P →L[ℂ] P)
    (hJb : ∀ q, IsUnitary (Jb q)) : IsUnitary (forcing (ι := ι) Jb) := by
  apply CoherentQuerySchedule.diagonal_unitary
  intro a
  rcases a with ⟨a, i⟩
  cases a with
  | none => exact isUnitary_one
  | some q => exact hJb q

/-- Exactly two controlled calls, in the operator multiplication convention.
The initial call is the released `ODESourceControls.initial`. -/
def combined (J₀ : P →L[ℂ] P) (Jb : Fin N → P →L[ℂ] P) :
    ODESourceControls.BranchSpace ι P N →L[ℂ] ODESourceControls.BranchSpace ι P N :=
  ODESourceControls.initial J₀ N * forcing Jb

theorem combined_unitary (J₀ : P →L[ℂ] P) (Jb : Fin N → P →L[ℂ] P)
    (hJ₀ : IsUnitary J₀) (hJb : ∀ q, IsUnitary (Jb q)) :
    IsUnitary (combined (ι := ι) J₀ Jb) :=
  (ODESourceControls.initial_unitary (ι := ι) J₀ N hJ₀).mul
    (forcing_unitary (ι := ι) Jb hJb)

omit [CompleteSpace P] in
/-- The two supported controls give the desired branch map on every vector. -/
theorem combined_eq_diagonal (J₀ : P →L[ℂ] P) (Jb : Fin N → P →L[ℂ] P) :
    combined (ι := ι) J₀ Jb =
      WeightedClock.diagonal (fun a : Option (Fin N) × ι => branchTD J₀ Jb a.1) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro a
  change ODESourcePreparations.branch J₀ 1 N a.1 (branchTD 1 Jb a.1 (v a)) =
    branchTD J₀ Jb a.1 (v a)
  rcases a with ⟨a, i⟩
  cases a <;> rfl

omit [CompleteSpace P] in
/-- Applying the two calls after the known coefficient preparation creates
the same input embedding used by the verified source-correctness theorem. -/
theorem combined_inputEmbedding (J₀ : P →L[ℂ] P) (Jb : Fin N → P →L[ℂ] P)
    (c : Option (Fin N) × ι → ℂ) :
    combined J₀ Jb ∘L
        ODECoherentLCU.inputEmbedding c (fun _ => (1 : P →L[ℂ] P)) =
      ODECoherentLCU.inputEmbedding c (fun a => branchTD J₀ Jb a.1) := by
  rw [combined_eq_diagonal]
  unfold ODECoherentLCU.inputEmbedding
  rw [WeightedClock.diagonal_boundary]
  simp only [one_def, comp_id]

end
end SparseHamiltonian.TimeDependentODE.SourceTD
