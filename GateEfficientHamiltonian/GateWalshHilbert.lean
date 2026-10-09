import GateEfficientHamiltonian.GateConstantCompareNumeric
/-!
# The actual Walsh gate list on a finite Hilbert register

A layout change below only exposes the one bit acted on by a gate.  It is
not charged as a circuit operation: the coordinate identity proves that the
operator is precisely that single-qubit rotation on the original wires.
The word circuit is then relabelled by the proved binary encoding, with an
untouched attenuation flag.  No uniform-state preparation is an assumption.
-/

namespace SparseHamiltonian.GateWalshHilbert

noncomputable section
open ContinuousLinearMap OracleCircuit ComplexAmplitudeRotation
open scoped BigOperators InnerProduct ComplexConjugate

abbrev Word (r : ℕ) := GateWalshWords.Word r
abbrev ScalarSpace (r : ℕ) := EuclideanSpace ℂ (Word r)

/-- Delete one bit by setting its representative value to false. -/
abbrev Rest {r : ℕ} (j : Fin r) := {x : Word r // x j = false}

/-- Isolate a chosen physical bit while retaining all other bits. -/
def splitBit {r : ℕ} (j : Fin r) : Word r ≃ Rest j × Bool where
  toFun x := (⟨Function.update x j false, by simp⟩, x j)
  invFun y := Function.update y.1.val j y.2
  left_inv x := by
    funext k
    by_cases hk : k = j
    · subst k; simp
    · simp [Function.update_of_ne hk]
  right_inv y := by
    rcases y with ⟨⟨x, hx⟩, b⟩
    apply Prod.ext
    · apply Subtype.ext
      funext k
      by_cases hk : k = j
      · subst k; simp [hx]
      · simp [Function.update_of_ne hk]
    · simp

/-- The Hilbert direct-sum decomposition exposing exactly one word bit. -/
def bitLayout {r : ℕ} (j : Fin r) :
    ScalarSpace r ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Rest j => Qubit) :=
  (LookupOracle.permutationUnitary (splitBit j)).trans
    (RegisterEquivalences.productFlatten (Rest j) Bool).symm

@[simp] theorem bitLayout_apply {r : ℕ} (j : Fin r)
    (v : ScalarSpace r) (x : Rest j) (b : Bool) :
    bitLayout j v x b = v (Function.update x.val j b) := rfl

@[simp] theorem bitLayout_symm_apply {r : ℕ} (j : Fin r)
    (v : PiLp 2 (fun _ : Rest j => Qubit)) (x : Word r) :
    (bitLayout j).symm v x = v ⟨Function.update x j false, by simp⟩ (x j) := by
  obtain ⟨w, rfl⟩ := (bitLayout j).surjective v
  simp only [LinearIsometryEquiv.symm_apply_apply, bitLayout_apply,
    Function.update_idem, Function.update_eq_self]

/-- The same explicit two-dimensional rotation as in the coordinate circuit. -/
def localRotation : Qubit →L[ℂ] Qubit :=
  matrix (GateWalshWords.half : ℂ) (-(GateWalshWords.half : ℂ))
    GateWalshWords.half GateWalshWords.half

theorem localRotation_unitary : IsUnitary localRotation := by
  have hh : (GateWalshWords.half : ℂ) ^ 2 +
      (GateWalshWords.half : ℂ) ^ 2 = 1 := by
    exact_mod_cast GateWalshWords.half_unit
  have hleft : localRotation† ∘L localRotation = 1 := by
    ext v b
    cases b <;>
      simp only [localRotation, matrix_adjoint, map_neg, Complex.conj_ofReal,
        comp_apply, matrix_false, matrix_true, one_def, id_apply]
    · linear_combination hh * v false
    · linear_combination hh * v true
  have hright : localRotation ∘L localRotation† = 1 := by
    ext v b
    cases b <;>
      simp only [localRotation, matrix_adjoint, map_neg, Complex.conj_ofReal,
        comp_apply, matrix_false, matrix_true, one_def, id_apply]
    · linear_combination hh * v false
    · linear_combination hh * v true
  exact ⟨hleft, hright⟩

/-- The one-bit rotation on the entire physical word Hilbert space. -/
def gate {r : ℕ} (j : Fin r) : ScalarSpace r →L[ℂ] ScalarSpace r :=
  (bitLayout j).symm.conjStarAlgEquiv
    (WeightedClock.diagonal (fun _ : Rest j => localRotation))

theorem gate_unitary {r : ℕ} (j : Fin r) : IsUnitary (gate j) := by
  have hd : IsUnitary (WeightedClock.diagonal (fun _ : Rest j => localRotation)) := by
    constructor
    · exact WeightedClock.diagonal_isometry _ (fun _ => localRotation_unitary.1)
    · change WeightedClock.diagonal (fun _ : Rest j => localRotation) ∘L
        (WeightedClock.diagonal (fun _ : Rest j => localRotation))† = 1
      have hi : localRotation ∘L localRotation† = 1 := localRotation_unitary.2
      rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
      simp only [hi, WeightedClock.diagonal_one]
  exact hd.transport (bitLayout j).symm

/-- This identifies the constructed Hilbert operator with the literal one-bit
matrix action, ruling out a hidden whole-register gate. -/
theorem gate_apply {r : ℕ} (j : Fin r) (v : ScalarSpace r) (x : Word r) :
    gate j v x = GateWalshWords.Gate.eval j (fun y => v y) x := by
  rw [gate, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  simp only [LinearIsometryEquiv.symm_symm, bitLayout_symm_apply,
    WeightedClock.diagonal_apply]
  cases hx : x j <;>
    simp [localRotation, bitLayout_apply, GateWalshWords.Gate.eval,
      GateWalshWords.coefficients, GateDyadicUnitary.rotationCoefficients,
      hx, Function.update_idem, add_comm]

/-- Execute the actual one-bit operators in the given order. -/
def run {r : ℕ} : List (Fin r) → ScalarSpace r →L[ℂ] ScalarSpace r
  | [] => 1
  | j :: js => run js * gate j

theorem run_unitary {r : ℕ} (js : List (Fin r)) : IsUnitary (run js) := by
  induction js with
  | nil => exact isUnitary_one
  | cons j js ih => exact ih.mul (gate_unitary j)

/-- Agreement with the previously proved coordinate-level gate semantics. -/
theorem run_apply {r : ℕ} (js : List (Fin r)) (v : ScalarSpace r) (x : Word r) :
    run js v x = GateWalshWords.run js (fun y => v y) x := by
  induction js generalizing v with
  | nil => rfl
  | cons j js ih =>
      change run js (gate j v) x =
        GateWalshWords.run js (GateWalshWords.Gate.eval j (fun y => v y)) x
      rw [ih]
      have hg : (fun y => gate j v y) =
          GateWalshWords.Gate.eval j (fun y => v y) := by
        funext y
        exact gate_apply j v y
      rw [hg]

/-- The scalar word transform consists of exactly the existing `r`-gate list. -/
def wordTransform (r : ℕ) : ScalarSpace r →L[ℂ] ScalarSpace r :=
  run (GateWalshWords.circuit r le_rfl)

theorem wordTransform_unitary (r : ℕ) : IsUnitary (wordTransform r) :=
  run_unitary _

def wordRelabel (r : ℕ) : ScalarSpace r ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (2 ^ r)) :=
  LookupOracle.permutationUnitary (GatePointerEncoding.wordEquivFin r)

@[simp] theorem wordRelabel_symm_apply (r : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 ^ r))) (x : Word r) :
    (wordRelabel r).symm v x = v (GatePointerEncoding.wordEquivFin r x) := by
  change (LookupOracle.permutationUnitary (GatePointerEncoding.wordEquivFin r)).symm
    v x = _
  rw [← LookupOracle.permutationUnitary_symm]
  rfl

/-- The word transform after its established little-endian basis relabelling. -/
def finiteTransform (r : ℕ) :
    EuclideanSpace ℂ (Fin (2 ^ r)) →L[ℂ] EuclideanSpace ℂ (Fin (2 ^ r)) :=
  (wordRelabel r).conjStarAlgEquiv (wordTransform r)

theorem finiteTransform_unitary (r : ℕ) : IsUnitary (finiteTransform r) :=
  (wordTransform_unitary r).transport (wordRelabel r)

/-- Exchange the word and attenuation-flag tensor factors. -/
def flagLayout (r : ℕ) : GateUniformRange.Space (2 ^ r) ≃ₗᵢ[ℂ]
    PiLp 2 (fun _ : Bool => EuclideanSpace ℂ (Fin (2 ^ r))) :=
  (RegisterEquivalences.productFlatten (Fin (2 ^ r)) Bool).trans
    ((LookupOracle.permutationUnitary (Equiv.prodComm (Fin (2 ^ r)) Bool)).trans
      (RegisterEquivalences.productFlatten Bool (Fin (2 ^ r))).symm)

@[simp] theorem flagLayout_apply (r : ℕ) (v : GateUniformRange.Space (2 ^ r))
    (b : Bool) (j : Fin (2 ^ r)) : flagLayout r v b j = v j b := rfl

@[simp] theorem flagLayout_symm_apply (r : ℕ)
    (v : PiLp 2 (fun _ : Bool => EuclideanSpace ℂ (Fin (2 ^ r))))
    (j : Fin (2 ^ r)) (b : Bool) : (flagLayout r).symm v j b = v b j := rfl

/-- The physical word-preparation operator with the flag untouched. -/
def uniformWords (r : ℕ) :
    GateUniformRange.Space (2 ^ r) →L[ℂ] GateUniformRange.Space (2 ^ r) :=
  (flagLayout r).symm.conjStarAlgEquiv
    (WeightedClock.diagonal (fun _ : Bool => finiteTransform r))

theorem uniformWords_unitary (r : ℕ) : IsUnitary (uniformWords r) := by
  have hd : IsUnitary (WeightedClock.diagonal (fun _ : Bool => finiteTransform r)) := by
    constructor
    · exact WeightedClock.diagonal_isometry _ (fun _ => (finiteTransform_unitary r).1)
    · change WeightedClock.diagonal (fun _ : Bool => finiteTransform r) ∘L
        (WeightedClock.diagonal (fun _ : Bool => finiteTransform r))† = 1
      have hi : finiteTransform r ∘L (finiteTransform r)† = 1 :=
        (finiteTransform_unitary r).2
      rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
      simp only [hi, WeightedClock.diagonal_one]
  exact hd.transport (flagLayout r).symm

/-- Full-coordinate correctness, for arbitrary word amplitudes and flag state. -/
theorem uniformWords_apply (r : ℕ) (v : GateUniformRange.Space (2 ^ r))
    (j : Fin (2 ^ r)) (b : Bool) :
    uniformWords r v j b =
      GateWalshWords.run (GateWalshWords.circuit r le_rfl)
        (fun x => v (GatePointerEncoding.wordEquivFin r x) b)
        ((GatePointerEncoding.wordEquivFin r).symm j) := by
  change wordTransform r
    ((wordRelabel r).symm (flagLayout r v b))
    ((GatePointerEncoding.wordEquivFin r).symm j) = _
  rw [wordTransform, run_apply]
  simp only [wordRelabel_symm_apply, flagLayout_apply]

/-- The actual clean input: zero on the word register and on the flag. -/
def cleanInput (r : ℕ) : GateUniformRange.Space (2 ^ r) :=
  WithLp.toLp 2 (fun j =>
    if j = GatePointerEncoding.wordEquivFin r (GateWalshWords.zeroWord r)
      then clean else 0)

theorem cleanInput_norm (r : ℕ) : ‖cleanInput r‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  simp [cleanInput, apply_ite, AmplitudePolynomialSequence.clean_norm]

theorem cleanInput_slice (r : ℕ) (b : Bool) :
    (fun x => cleanInput r (GatePointerEncoding.wordEquivFin r x) b) =
      (clean b) • GateWalshWords.zeroState := by
  funext x
  change (if GatePointerEncoding.wordEquivFin r x =
      GatePointerEncoding.wordEquivFin r (GateWalshWords.zeroWord r)
      then clean else 0) b =
    clean b * (if x = GateWalshWords.zeroWord r then (1 : ℂ) else 0)
  by_cases hx : x = GateWalshWords.zeroWord r
  · subst x
    simp
  · have he : GatePointerEncoding.wordEquivFin r x ≠
        GatePointerEncoding.wordEquivFin r (GateWalshWords.zeroWord r) :=
      fun h => hx ((GatePointerEncoding.wordEquivFin r).injective h)
    simp only [if_neg he, if_neg hx, PiLp.zero_apply, mul_zero]

/-- Uniform words are derived from the literal bit-gate list, with the
normalisation and the attenuation flag both accounted for. -/
theorem uniformWords_prepares (r : ℕ) :
    uniformWords r (cleanInput r) = CoherentReuse.uniformEmbedding (2 ^ r) clean := by
  ext j b
  rw [uniformWords_apply, cleanInput_slice, map_smul,
    GateWalshWords.circuit_prepares_constant]
  simp only [Pi.smul_apply, smul_eq_mul, CoherentReuse.uniformEmbedding_apply,
    PiLp.smul_apply, GateWalshWords.complex_half_pow_eq_uniformAmplitude]
  ring

/-- The formerly assumed uniform-word preparation interface is now supplied
by the concrete word circuit.  The remaining range-comparator and reflection
macros retain their separate elementary-gate construction obligations. -/
theorem actual_rangeProgram_prepares (n r : ℕ) (hn : 0 < n)
    (hnN : n ≤ 2 ^ r) (hN : 2 ^ r ≤ 4 * n) :
    (GateUniformRange.rangeProgram n (2 ^ r) hn hN
      (uniformWords r) (cleanInput r) (cleanInput_norm r)).eval () (cleanInput r) =
      GateUniformRange.target n (2 ^ r) :=
  GateUniformRange.rangeProgram_prepares n (2 ^ r) hn hnN hN
    (uniformWords r) (uniformWords_unitary r) (cleanInput r)
    (cleanInput_norm r) (uniformWords_prepares r)

/-- The actual preparation leaves its attenuation flag exactly clean. -/
theorem actual_rangeProgram_flag_clean (n r : ℕ) (hn : 0 < n)
    (hnN : n ≤ 2 ^ r) (hN : 2 ^ r ≤ 4 * n) (j : Fin (2 ^ r)) :
    ((GateUniformRange.rangeProgram n (2 ^ r) hn hN
      (uniformWords r) (cleanInput r) (cleanInput_norm r)).eval ()
      (cleanInput r)) j true = 0 := by
  rw [actual_rangeProgram_prepares n r hn hnN hN]
  exact GateUniformRange.target_true n (2 ^ r) j

/-- Expanding the three word-preparation occurrences contributes `3*r`
one-bit rotations.  This counts that component only; the separately exposed
attenuation and reflection components are not assigned zero gate cost. -/
theorem actual_rangeProgram_word_rotations (n r : ℕ) (hn : 0 < n)
    (hN : 2 ^ r ≤ 4 * n) :
    (GateUniformRange.rangeProgram n (2 ^ r) hn hN
      (uniformWords r) (cleanInput r) (cleanInput_norm r)).count *
        (GateWalshWords.circuit r le_rfl).length = 3 * r := by
  rw [GateUniformRange.rangeProgram_word_preparations, GateWalshWords.circuit_length]

end
end SparseHamiltonian.GateWalshHilbert
