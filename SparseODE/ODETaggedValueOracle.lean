import SparseODE.ODETaggedValueProgram

/-!
# Removing the support tag from the queried address

A fixed register equivalence moves the support tag and the first value word
into the untouched payload of the original matrix-entry oracle. The literal
four-query tagged gate program therefore uses the original table, without
a derived entry oracle or a coherent selection of oracle labels.
-/

namespace SparseHamiltonian.ODETaggedValueOracle

noncomputable section
open ContinuousLinearMap OracleCircuit ODETaggedValueDecoder
open scoped InnerProduct
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- Reconstruct a tagged address from its known support bit and matrix edge. -/
def address {n : Type*} (b : Bool) (e : n × n) : Address n :=
  if b then Sum.inr e else Sum.inl e

/-- The queried address is the original edge. Both extra registers become
spectators of its value lookup. -/
def basisLayout (n Z : Type*) :
    ((Address n × Z) × Z) ≃ (((n × n) × Z) × (Bool × Z)) where
  toFun w := ((edge w.1.1, w.2), (tag w.1.1, w.1.2))
  invFun w := ((address w.2.1 w.1.1, w.2.2), w.1.2)
  left_inv := by
    intro w
    rcases w with ⟨⟨a, u⟩, z⟩
    cases a <;> rfl
  right_inv := by
    intro w
    rcases w with ⟨⟨e, z⟩, ⟨b, u⟩⟩
    cases b <;> rfl

abbrev Payload (Z : Type*) := PiLp 2 (fun _ : Bool × Z => ExactEdgeCayley.Qubit)
abbrev Space (n Z : Type*) := PiLp 2 (fun _ : (n × n) × Z => Payload Z)

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- A public permutation followed by currying; it has no matrix dependence. -/
def layout : ODETaggedValueProgram.Space n Z ≃ₗᵢ[ℂ] Space n Z :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ExactEdgeCayley.Qubit
    (basisLayout n Z)).trans
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ExactEdgeCayley.Qubit
      (Equiv.sigmaEquivProd ((n × n) × Z) (Bool × Z)).symm).trans
      (LinearIsometryEquiv.piLpCurry ℂ 2
        (fun (_ : (n × n) × Z) (_ : Bool × Z) => ExactEdgeCayley.Qubit)))

omit [DecidableEq n] [AddCommGroup Z] [DecidableEq Z] in
@[simp] theorem layout_apply (v : ODETaggedValueProgram.Space n Z)
    (e : n × n) (z : Z) (b : Bool) (u : Z) :
    layout v (e, z) (b, u) = v ((address b e, u), z) := rfl

/-- This is exactly the original additive matrix-entry lookup, with a larger
untouched Hilbert payload. The native queried address remains `n × n`. -/
def oracle (D : NativeSparseBlockEncoding.Data X n Z s) :
    X → Space n Z →L[ℂ] Space n Z :=
  LookupControlledGate.oracle (K := Payload Z) D.table

omit [DecidableEq Z] in
theorem oracle_unitary (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    IsUnitary (oracle D x) := LookupControlledGate.oracle_unitary D.table x

omit [DecidableEq Z] in
/-- One tagged primitive is one original matrix lookup under a fixed layout. -/
theorem oracle_intertwines (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    oracle D x ∘L (layout (n := n) (Z := Z)).toLinearIsometry.toContinuousLinearMap =
      layout.toLinearIsometry.toContinuousLinearMap ∘L ODETaggedValueProgram.oracle D x := by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro ez
  apply PiLp.ext
  intro bu
  rcases ez with ⟨e, z⟩
  rcases bu with ⟨b, u⟩
  cases b <;> rfl

omit [DecidableEq Z] in
/-- Inverse queries are also the original inverse lookup, at the same cost. -/
theorem oracle_adjoint_intertwines
    (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    (oracle D x)† ∘L (layout (n := n) (Z := Z)).toLinearIsometry.toContinuousLinearMap =
      layout.toLinearIsometry.toContinuousLinearMap ∘L
        (ODETaggedValueProgram.oracle D x)† := by
  simpa only [star_eq_adjoint] using
    EncodedOracle.adjoint_intertwines _ _ _ (oracle_unitary D x)
      (ODETaggedValueProgram.oracle_unitary D x) (oracle_intertwines D x)

omit [DecidableEq Z] in
theorem oracle_conjugate (D : NativeSparseBlockEncoding.Data X n Z s) (x : X) :
    (layout (n := n) (Z := Z)).conjStarAlgEquiv (ODETaggedValueProgram.oracle D x) =
      oracle D x := by
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg
    (fun F : ODETaggedValueProgram.Space n Z →L[ℂ] Space n Z => F (layout.symm v))
    (oracle_intertwines D x)
  change oracle D x (layout (layout.symm v)) =
    layout (ODETaggedValueProgram.oracle D x (layout.symm v)) at h
  rw [LinearIsometryEquiv.apply_symm_apply] at h
  exact h.symm

omit [DecidableEq Z] in
/-- Reinterpreting identical oracle operators changes no evaluated gate. -/
private theorem retarget_eval
    (D : NativeSparseBlockEncoding.Data X n Z s)
    (p : Program (fun x => (layout (n := n) (Z := Z)).conjStarAlgEquiv
      (ODETaggedValueProgram.oracle D x))) (x : X) :
    (p.retarget (oracle D)).eval x = p.eval x := by
  induction p with
  | fixed U hU => rfl
  | query => exact (oracle_conjugate D x).symm
  | queryAdjoint =>
    simp only [Program.retarget, Program.eval_queryAdjoint, oracle_conjugate]
  | seq p q hp hq =>
    simp only [Program.retarget, Program.eval_seq, hp, hq]

/-- The same fixed circuit syntax on the original matrix-entry primitive. -/
def program (D : NativeSparseBlockEncoding.Data X n Z s) (k γ ρ : ℝ) :
    Program (oracle D) :=
  ((ODETaggedValueProgram.program D k γ ρ).transport
    (layout (n := n) (Z := Z))).retarget (oracle D)

omit [DecidableEq Z] in
theorem program_count (D : NativeSparseBlockEncoding.Data X n Z s) (k γ ρ : ℝ) :
    (program D k γ ρ).count = 4 := by
  rw [program, Program.count_retarget, Program.count_transport,
    ODETaggedValueProgram.program_count]

omit [DecidableEq Z] in
theorem program_eval (D : NativeSparseBlockEncoding.Data X n Z s)
    (k γ ρ : ℝ) (x : X) :
    (program D k γ ρ).eval x =
      layout.conjStarAlgEquiv ((ODETaggedValueProgram.program D k γ ρ).eval x) := by
  rw [program, retarget_eval, Program.eval_transport]

def clean : ODETaggedMoments.PrivateSpace n →ₗᵢ[ℂ] Space n Z :=
  (layout (n := n) (Z := Z)).toLinearIsometry.comp
    (ODETaggedValueProgram.clean (n := n) (Z := Z))

/-- The four original value calls implement the exact tagged Cayley action,
with the tag and both value words coherently restored in the fixed encoding. -/
theorem program_intertwines (D : NativeSparseBlockEncoding.Data X n Z s)
    (k γ ρ : ℝ) (x : X) :
    (program D k γ ρ).eval x ∘L (clean (n := n) (Z := Z)).toContinuousLinearMap =
      clean.toContinuousLinearMap ∘L ODETaggedCayley.action (D.matrix x)
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) s ρ γ := by
  rw [program_eval]
  apply ContinuousLinearMap.ext
  intro v
  change layout ((ODETaggedValueProgram.program D k γ ρ).eval x
      (layout.symm (layout (ODETaggedValueProgram.clean v)))) =
    layout (ODETaggedValueProgram.clean
      (ODETaggedCayley.action (D.matrix x)
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) s ρ γ v))
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact congrArg layout (congrArg
    (fun F : ODETaggedMoments.PrivateSpace n →L[ℂ] ODETaggedValueProgram.Space n Z => F v)
    (ODETaggedValueProgram.program_intertwines D k γ ρ x))

omit [DecidableEq Z] in
theorem program_unitary (D : NativeSparseBlockEncoding.Data X n Z s)
    (k γ ρ : ℝ) (x : X) : IsUnitary ((program D k γ ρ).eval x) :=
  (program D k γ ρ).eval_unitary (oracle_unitary D) x

/-- A certificate directly over the original sparse matrix-value family. -/
theorem implementsOn (D : NativeSparseBlockEncoding.Data X n Z s) (k γ ρ : ℝ) :
    EncodedOracle.ImplementsOn (oracle D)
      (fun x => ODETaggedCayley.action (D.matrix x)
        (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) s ρ γ)
      (clean (n := n) (Z := Z)).toContinuousLinearMap 4 :=
  ⟨program D k γ ρ, program_intertwines D k γ ρ, by rw [program_count]⟩

end
end SparseHamiltonian.ODETaggedValueOracle
