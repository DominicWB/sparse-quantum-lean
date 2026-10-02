import SparseODE.ODETaggedValueDecoder

/-!
# Four original value queries implement the tagged LCHS Cayley action

This specializes the paired-entry program to the original sparse matrix.
Each primitive is the original additive lookup with an untouched tag and
scratch word. Both value words are restored exactly, on coherent inputs.
Locator conjugation and the common simulator schedule are separate tasks.
-/

namespace SparseHamiltonian.ODETaggedValueProgram

noncomputable section
open ContinuousLinearMap OracleCircuit ODETaggedValueDecoder
open scoped InnerProduct
set_option maxHeartbeats 1000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

abbrev Space (n Z : Type*) :=
  ODEPairedValueQuery.Space (Address n) Z ExactEdgeCayley.Qubit

/-- The queried operation adds one original entry; the tag and first value
word are spectators. The transposed entry is obtained by fixed routing. -/
def oracle (D : NativeSparseBlockEncoding.Data X n Z s) :
    X → Space n Z →L[ℂ] Space n Z :=
  ODEPairedValueQuery.oracle (K := ExactEdgeCayley.Qubit) (table D)

omit [DecidableEq Z] in
@[simp] theorem oracle_apply (D : NativeSparseBlockEncoding.Data X n Z s)
    (x : X) (v : Space n Z) (a : Address n) (u z : Z) :
    oracle D x v ((a, u), z) = v ((a, u), z - D.table x (edge a)) := rfl

omit [DecidableEq Z] in
theorem oracle_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    IsUnitary (oracle D x) := ODEPairedValueQuery.oracle_unitary (table D) x

/-- Literal compute-both, rotate, and uncompute program over this primitive. -/
def program (D : NativeSparseBlockEncoding.Data X n Z s) (k γ ρ : ℝ) :
    Program (oracle D) :=
  ODEPairedValueQuery.program (exchange n) (gates D k γ ρ)
    (gates_unitary D k γ ρ) (table D)

omit [DecidableEq Z] in
theorem program_count (D : NativeSparseBlockEncoding.Data X n Z s) (k γ ρ : ℝ) :
    (program D k γ ρ).count = 4 :=
  ODEPairedValueQuery.program_count (exchange n) (gates D k γ ρ)
    (gates_unitary D k γ ρ) (table D)

omit [DecidableEq Z] in
theorem program_unitary (D : NativeSparseBlockEncoding.Data X n Z s)
    (k γ ρ : ℝ) (x : X) : IsUnitary ((program D k γ ρ).eval x) :=
  (program D k γ ρ).eval_unitary (oracle_unitary D) x

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The support-tag entries are precisely those of the analytic diagonal. -/
theorem actualEntry_eq_entries (D : NativeSparseBlockEncoding.Data X n Z s)
    (k : ℝ) (x : X) (a : Address n) :
    actualEntry D k x a = ODETaggedCayley.entries (D.matrix x)
      (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) a := by
  cases a <;> rfl

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The public scale and the analytic moment scale agree identically. -/
theorem scaledEntry_correct (D : NativeSparseBlockEncoding.Data X n Z s)
    (k γ ρ : ℝ) (x : X) (a : Address n) :
    (scale s γ ρ : ℂ) * actualEntry D k x a =
      ODETaggedCayley.scaledEntries (D.matrix x)
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) s ρ γ a := by
  have hscale : scale s γ ρ = γ * (Real.sqrt (2 * (s : ℝ)) / ρ) := by
    unfold scale
    ring
  rw [actualEntry_eq_entries, hscale]
  rfl

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The logical operation of the actual lookup program is the required direct
sum of exact Cayley gates. No entry-dependent gate is treated as free. -/
theorem logical_eq_diagonal (D : NativeSparseBlockEncoding.Data X n Z s)
    (k γ ρ : ℝ) (x : X) :
    ODEPairedValueQuery.logical (exchange n) (gates D k γ ρ) (table D) x =
      WeightedClock.diagonal (fun a => ExactEdgeCayley.action
        (ODETaggedCayley.scaledEntries (D.matrix x)
          (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) s ρ γ a)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro a
  simp only [ODEPairedValueQuery.logical_apply, WeightedClock.diagonal_apply,
    gates_correct, scaledEntry_correct]

/-- The clean encoding is fixed: exchange register order and append two zero
value words. It is independent of the input matrix and the LCHS parameters. -/
def clean : ODETaggedMoments.PrivateSpace n →ₗᵢ[ℂ] Space n Z :=
  (ODEPairedValueQuery.clean (A := Address n) (Z := Z) (K := ExactEdgeCayley.Qubit)).comp
    (ODETaggedCayley.regroup (ι := Address n)).toLinearIsometry

omit [DecidableEq n] in
theorem clean_isometry :
    (clean (n := n) (Z := Z)).toContinuousLinearMap† ∘L
      (clean (n := n) (Z := Z)).toContinuousLinearMap = 1 :=
  LinearIsometry.adjoint_comp_self _

/-- Exact encoded correctness for the entire tagged Cayley action. Both value
registers return to their fixed zero state for every coherent input. -/
theorem program_intertwines (D : NativeSparseBlockEncoding.Data X n Z s)
    (k γ ρ : ℝ) (x : X) :
    (program D k γ ρ).eval x ∘L (clean (n := n) (Z := Z)).toContinuousLinearMap =
      clean.toContinuousLinearMap ∘L ODETaggedCayley.action (D.matrix x)
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) s ρ γ := by
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg
    (fun F : ODEPairedValueQuery.Public (Address n) ExactEdgeCayley.Qubit →L[ℂ]
        Space n Z => F (ODETaggedCayley.regroup v))
    (ODEPairedValueQuery.program_intertwines (exchange n) (gates D k γ ρ)
      (gates_unitary D k γ ρ) (table D) x)
  change (program D k γ ρ).eval x (clean v) = _ at h
  rw [logical_eq_diagonal] at h
  change (program D k γ ρ).eval x (clean v) = clean
    (ODETaggedCayley.action (D.matrix x)
      (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) s ρ γ v)
  change (program D k γ ρ).eval x (clean v) =
    ODEPairedValueQuery.clean (ODETaggedCayley.regroup
      (ODETaggedCayley.action (D.matrix x)
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) s ρ γ v))
  rw [ODETaggedCayley.regroup_action]
  exact h

/-- A concrete four-value-query certificate for every known node and scale.
No matrix norm or nonzero-entry promise is needed for this exact unitary. -/
theorem implementsOn (D : NativeSparseBlockEncoding.Data X n Z s) (k γ ρ : ℝ) :
    EncodedOracle.ImplementsOn (oracle D)
      (fun x => ODETaggedCayley.action (D.matrix x)
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) s ρ γ)
      (clean (n := n) (Z := Z)).toContinuousLinearMap 4 :=
  ⟨program D k γ ρ, program_intertwines D k γ ρ, by rw [program_count]⟩

end
end SparseHamiltonian.ODETaggedValueProgram
