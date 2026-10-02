import SparseHamiltonian.ComplexAmplitudeRotation

/-!
# Two-query coherent preparation of complex table amplitudes

A fixed decoder supplies bounded complex amplitudes. One ordinary lookup, a
fixed decoded rotation, and the inverse lookup prepare those amplitudes on an
arbitrary coherent address state. The value register is returned exactly to
zero. Both the good and bad flag amplitudes, the full isometry, and the exact
two-query count are proved; no sparse location oracle is assumed or constructed.
-/

namespace SparseHamiltonian.LookupAmplitudePreparation

noncomputable section
open ContinuousLinearMap OracleCircuit ComplexAmplitudeRotation
open scoped InnerProduct

/-- Fixed scalar-to-qubit encoding into the clean false state. -/
def cleanQubit : ℂ →ₗᵢ[ℂ] Qubit where
  toLinearMap :=
    { toFun := fun z => WithLp.toLp 2 (fun b : Bool => if b then 0 else z)
      map_add' := by
        intro z w
        apply PiLp.ext
        intro b
        cases b <;> simp
      map_smul' := by
        intro z w
        apply PiLp.ext
        intro b
        cases b <;> simp }
  norm_map' := by
    intro z
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp [PiLp.norm_sq_eq_of_L2]

@[simp] theorem cleanQubit_false (z : ℂ) : cleanQubit z false = z := rfl
@[simp] theorem cleanQubit_true (z : ℂ) : cleanQubit z true = 0 := rfl

variable {X A Z : Type*} [Fintype A] [Fintype Z] [AddCommGroup Z]

/-- Address, value, and amplitude flag registers in the physical lookup layout. -/
abbrev Space (A Z : Type*) := PiLp 2 (fun _ : A × Z => Qubit)

/-- Append a fixed clean amplitude flag to every coherent address amplitude. -/
def flagEmbedding : EuclideanSpace ℂ A →ₗᵢ[ℂ] PiLp 2 (fun _ : A => Qubit) where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (fun a => cleanQubit (v a))
      map_add' := by
        intro v w
        apply PiLp.ext
        intro a
        exact cleanQubit.map_add _ _
      map_smul' := by
        intro z v
        apply PiLp.ext
        intro a
        exact cleanQubit.map_smul z _ }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2]
    change (∑ a, ∑ b : Bool, ‖cleanQubit (v a) b‖ ^ 2) = ∑ a, ‖v a‖ ^ 2
    simp

@[simp] theorem flagEmbedding_apply (v : EuclideanSpace ℂ A) (a : A) :
    flagEmbedding v a = cleanQubit (v a) := rfl

/-- The decoder determines a fixed gate for every address and encoded value. -/
def gates (decode : A → Z → ℂ) (a : A) (z : Z) : Qubit →L[ℂ] Qubit :=
  rotation (decode a z)

omit [Fintype A] [Fintype Z] [AddCommGroup Z] in
/-- Bounded decoded amplitudes make every gate unitary on both flag states. -/
theorem gates_unitary (decode : A → Z → ℂ)
    (hdecode : ∀ a z, ‖decode a z‖ ≤ 1) (a : A) (z : Z) : IsUnitary (gates decode a z) :=
  rotation_unitary _ (hdecode a z)

/-- Explicit compute/decoded-rotation/uncompute program. All fixed gates are
independent of the unknown oracle input. -/
def program (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → A → Z) : Program (LookupControlledGate.oracle (K := Qubit) f) :=
  LookupControlledGate.program (gates decode) (gates_unitary decode hdecode) f

/-- The amplitude-preparation program uses exactly two ordinary lookup queries. -/
theorem program_count (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → A → Z) : (program decode hdecode f).count = 2 := rfl

/-- The complete physical program is unitary, including on nonzero value registers. -/
theorem program_unitary (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → A → Z) (x : X) : IsUnitary ((program decode hdecode f).eval x) :=
  (program decode hdecode f).eval_unitary (LookupControlledGate.oracle_unitary f) x

variable [DecidableEq Z]

/-- Fixed initialization of both the value register and amplitude flag. -/
def input : EuclideanSpace ℂ A →ₗᵢ[ℂ] Space A Z :=
  (CleanValueEmbedding.embedding (I := A) (K := Qubit) (0 : Z)).comp flagEmbedding

@[simp] theorem input_apply (v : EuclideanSpace ℂ A) (a : A) (z : Z) :
    input (Z := Z) v (a, z) = if z = 0 then cleanQubit (v a) else 0 := rfl

/-- The physical input preparation is a fixed isometry. -/
theorem input_isometry :
    (input (A := A) (Z := Z)).toContinuousLinearMap† ∘L input.toContinuousLinearMap = 1 :=
  LinearIsometry.adjoint_comp_self _

/-- The actual complete output map produced by the two-query program. -/
def preparation (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → A → Z) (x : X) : EuclideanSpace ℂ A →L[ℂ] Space A Z :=
  (program decode hdecode f).eval x ∘L (input (A := A) (Z := Z)).toContinuousLinearMap

/-- Exact full-output amplitudes for every address superposition. The value
register is clean for both the good and bad outcomes. -/
theorem preparation_apply (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → A → Z) (x : X) (v : EuclideanSpace ℂ A) (a : A) (z : Z) (b : Bool) :
    preparation decode hdecode f x v (a, z) b =
      if z = 0 then v a * (if b then (badAmplitude (decode a (f x a)) : ℂ)
        else decode a (f x a)) else 0 := by
  change ((program decode hdecode f).eval x
    (CleanValueEmbedding.embedding (0 : Z) (flagEmbedding v))) (a, z) b = _
  rw [program, LookupControlledGate.program_eval, LookupControlledGate.circuit_clean_apply]
  by_cases hz : z = 0
  · subst z
    cases b <;> simp [gates, mul_comm]
  · simp [hz]

/-- The complex good amplitude, with no phase discarded. -/
theorem preparation_good (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → A → Z) (x : X) (v : EuclideanSpace ℂ A) (a : A) :
    preparation decode hdecode f x v (a, 0) false = v a * decode a (f x a) := by
  simp [preparation_apply]

/-- The complete orthogonal bad amplitude. -/
theorem preparation_bad (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → A → Z) (x : X) (v : EuclideanSpace ℂ A) (a : A) :
    preparation decode hdecode f x v (a, 0) true =
      v a * (Real.sqrt (1 - ‖decode a (f x a)‖ ^ 2) : ℂ) := by
  simp [preparation_apply, badAmplitude]

/-- The lookup value is restored exactly, independently of the flag outcome. -/
theorem preparation_value_restored (decode : A → Z → ℂ)
    (hdecode : ∀ a z, ‖decode a z‖ ≤ 1) (f : X → A → Z) (x : X)
    (v : EuclideanSpace ℂ A) (a : A) (z : Z) (hz : z ≠ 0) (b : Bool) :
    preparation decode hdecode f x v (a, z) b = 0 := by
  simp [preparation_apply, hz]

/-- All output branches jointly preserve the norm of the input superposition. -/
theorem preparation_norm (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → A → Z) (x : X) (v : EuclideanSpace ℂ A) :
    ‖preparation decode hdecode f x v‖ = ‖v‖ := by
  rw [preparation, comp_apply,
    ((program decode hdecode f).eval x).norm_map_iff_adjoint_comp_self.mpr
      (program_unitary decode hdecode f x).1]
  exact input.norm_map v

/-- The state-preparation map is a genuine isometry without postselection. -/
theorem preparation_isometry (decode : A → Z → ℂ) (hdecode : ∀ a z, ‖decode a z‖ ≤ 1)
    (f : X → A → Z) (x : X) :
    (preparation decode hdecode f x)† ∘L preparation decode hdecode f x = 1 :=
  (preparation decode hdecode f x).norm_map_iff_adjoint_comp_self.mp
    (preparation_norm decode hdecode f x)

end
end SparseHamiltonian.LookupAmplitudePreparation
