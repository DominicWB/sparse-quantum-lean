import SparseHamiltonian.LookupControlledGate

/-!
# Fixed complex-amplitude rotations

For a known complex number `z` of norm at most one, the explicit two-dimensional
unitary has columns `(z, sqrt(1-‖z‖²))` and `(-sqrt(1-‖z‖²), conj z)`.
The false Boolean state is the clean input and the good output. A fixed value
decoder gives a fixed finite family of these unitaries, ready to be selected
by the separately counted lookup/controlled-gate/uncompute construction.
-/

namespace SparseHamiltonian.ComplexAmplitudeRotation

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct ComplexConjugate

/-- The amplitude qubit uses the Hilbert norm, not the function-space sup norm. -/
abbrev Qubit := PiLp 2 (fun _ : Bool => ℂ)

/-- Explicit two-by-two complex linear map in false/true coordinate order. -/
def matrixLinear (a b c d : ℂ) : Qubit →ₗ[ℂ] Qubit where
  toFun x := WithLp.toLp 2 (fun t : Bool =>
    if t then c * x false + d * x true else a * x false + b * x true)
  map_add' x y := by
    apply PiLp.ext
    intro t
    cases t <;> simp only [Bool.false_eq_true, ↓reduceIte, PiLp.add_apply] <;> ring
  map_smul' z x := by
    apply PiLp.ext
    intro t
    cases t <;> simp only [Bool.false_eq_true, ↓reduceIte, PiLp.smul_apply,
      RingHom.id_apply, smul_eq_mul] <;> ring

/-- Every such map is bounded on the genuine finite-dimensional Hilbert space. -/
def matrix (a b c d : ℂ) : Qubit →L[ℂ] Qubit :=
  (matrixLinear a b c d).toContinuousLinearMap

@[simp] theorem matrix_false (a b c d : ℂ) (x : Qubit) :
    matrix a b c d x false = a * x false + b * x true := rfl

@[simp] theorem matrix_true (a b c d : ℂ) (x : Qubit) :
    matrix a b c d x true = c * x false + d * x true := rfl

/-- The continuous adjoint agrees with the explicit conjugate transpose. -/
theorem matrix_adjoint (a b c d : ℂ) :
    (matrix a b c d)† = matrix (conj a) (conj c) (conj b) (conj d) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [adjoint_inner_left]
  simp only [PiLp.inner_apply, Fintype.sum_bool, matrix_false, matrix_true,
    RCLike.inner_apply, map_add, map_mul]
  simp only [Complex.conj_conj]
  ring

/-- The real nonnegative amplitude allocated to the bad flag. -/
def badAmplitude (z : ℂ) : ℝ := Real.sqrt (1 - ‖z‖ ^ 2)

theorem badAmplitude_nonneg (z : ℂ) : 0 ≤ badAmplitude z := Real.sqrt_nonneg _

/-- The good and bad probabilities add to one on the permitted unit disk. -/
theorem probability_sum (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖z‖ ^ 2 + badAmplitude z ^ 2 = 1 := by
  have hsq : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  rw [badAmplitude, Real.sq_sqrt (sub_nonneg.mpr hsq)]
  ring

/-- The normalization identity in the coefficient field. -/
theorem coefficient_sum (z : ℂ) (hz : ‖z‖ ≤ 1) :
    z * conj z + (badAmplitude z : ℂ) ^ 2 = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  exact_mod_cast probability_sum z hz

/-- The fixed rotation permits a complex phase in its good amplitude. -/
def rotation (z : ℂ) : Qubit →L[ℂ] Qubit :=
  matrix z (-(badAmplitude z : ℂ)) (badAmplitude z) (conj z)

@[simp] theorem rotation_false (z : ℂ) (x : Qubit) :
    rotation z x false = z * x false - (badAmplitude z : ℂ) * x true := by
  simp [rotation, sub_eq_add_neg]

@[simp] theorem rotation_true (z : ℂ) (x : Qubit) :
    rotation z x true = (badAmplitude z : ℂ) * x false + conj z * x true := rfl

/-- The exact inverse is the conjugate transpose with the opposite off-diagonal signs. -/
theorem rotation_adjoint (z : ℂ) :
    (rotation z)† = matrix (conj z) (badAmplitude z) (-(badAmplitude z : ℂ)) z := by
  rw [rotation, matrix_adjoint]
  simp

/-- Multiplication by the adjoint on the left is exactly identity. -/
theorem rotation_adjoint_comp (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (rotation z)† ∘L rotation z = 1 := by
  ext x t
  cases t
  · simp only [comp_apply, rotation_adjoint, matrix_false, rotation_false, rotation_true,
      one_def, id_apply]
    calc
      _ = (z * conj z + (badAmplitude z : ℂ) ^ 2) * x false := by ring
      _ = x false := by rw [coefficient_sum z hz, one_mul]
  · simp only [comp_apply, rotation_adjoint, matrix_true, rotation_false, rotation_true,
      one_def, id_apply]
    calc
      _ = (z * conj z + (badAmplitude z : ℂ) ^ 2) * x true := by ring
      _ = x true := by rw [coefficient_sum z hz, one_mul]

/-- Multiplication by the adjoint on the right is also exactly identity. -/
theorem rotation_comp_adjoint (z : ℂ) (hz : ‖z‖ ≤ 1) :
    rotation z ∘L (rotation z)† = 1 := by
  ext x t
  cases t
  · simp only [comp_apply, rotation_adjoint, rotation_false, matrix_false, matrix_true,
      one_def, id_apply]
    calc
      _ = (z * conj z + (badAmplitude z : ℂ) ^ 2) * x false := by ring
      _ = x false := by rw [coefficient_sum z hz, one_mul]
  · simp only [comp_apply, rotation_adjoint, rotation_true, matrix_false, matrix_true,
      one_def, id_apply]
    calc
      _ = (z * conj z + (badAmplitude z : ℂ) ^ 2) * x true := by ring
      _ = x true := by rw [coefficient_sum z hz, one_mul]

/-- The explicit rotation is a legal fixed unitary whenever the decoded amplitude is bounded. -/
theorem rotation_unitary (z : ℂ) (hz : ‖z‖ ≤ 1) : IsUnitary (rotation z) :=
  ⟨rotation_adjoint_comp z hz, rotation_comp_adjoint z hz⟩

/-- The clean false basis state. -/
def clean : Qubit := WithLp.toLp 2 (fun b : Bool => if b then 0 else 1)

@[simp] theorem clean_false : clean false = 1 := rfl
@[simp] theorem clean_true : clean true = 0 := rfl

/-- The good amplitude has the specified complex phase and magnitude. -/
@[simp] theorem rotation_clean_good (z : ℂ) : rotation z clean false = z := by simp

/-- The orthogonal flag carries precisely the remaining nonnegative amplitude. -/
@[simp] theorem rotation_clean_bad (z : ℂ) :
    rotation z clean true = (badAmplitude z : ℂ) := by simp

/-- The complete prepared vector is specified, rather than only its good projection. -/
theorem rotation_clean (z : ℂ) :
    rotation z clean = WithLp.toLp 2 (fun b : Bool => if b then (badAmplitude z : ℂ) else z) := by
  apply PiLp.ext
  intro b
  cases b <;> simp

/-- A known decoder defines a fixed gate at every encoded value. There is no
unknown-input parameter in this gate family. -/
def decoded {Z : Type*} (decode : Z → ℂ) (value : Z) : Qubit →L[ℂ] Qubit :=
  rotation (decode value)

/-- A bounded decoder supplies a unitary for every value, including unused encodings. -/
theorem decoded_unitary {Z : Type*} (decode : Z → ℂ)
    (hdecode : ∀ value, ‖decode value‖ ≤ 1) (value : Z) : IsUnitary (decoded decode value) :=
  rotation_unitary _ (hdecode value)

/-- The entire finite value-controlled gate is a fixed operator. -/
def valueControlled {Z : Type*} [Fintype Z] (decode : Z → ℂ) :
    PiLp 2 (fun _ : Z => Qubit) →L[ℂ] PiLp 2 (fun _ : Z => Qubit) :=
  WeightedClock.diagonal (decoded decode)

/-- Both full-space unitary identities hold for the fixed value-controlled rotation. -/
theorem valueControlled_unitary {Z : Type*} [Fintype Z] (decode : Z → ℂ)
    (hdecode : ∀ value, ‖decode value‖ ≤ 1) : IsUnitary (valueControlled decode) := by
  constructor
  · exact WeightedClock.diagonal_isometry _ (fun value => (decoded_unitary decode hdecode value).1)
  · change valueControlled decode ∘L (valueControlled decode)† = 1
    rw [valueControlled, WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
    have hh (value : Z) : decoded decode value ∘L (decoded decode value)† = 1 :=
      (decoded_unitary decode hdecode value).2
    simp only [hh, WeightedClock.diagonal_one]

end
end SparseHamiltonian.ComplexAmplitudeRotation
