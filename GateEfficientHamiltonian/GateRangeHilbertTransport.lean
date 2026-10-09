import GateEfficientHamiltonian.GateRangePhaseCoordinates
/-!
# Hilbert-space transport of the literal range circuits

The comparison lists above were proved on finitely supported coordinate
amplitudes.  Here they are lifted to the common finite Hilbert register as
genuine basis-permutation unitaries.  The marked wire is exposed by an
isometric layout, its normalised minus state is prepared and unprepared by
two known one-qubit gates, and the accepted-range and initial-state
reflections are proved on that normalised state.  Thus the two reflections
used by range amplification act on exactly the same physical workspace.
-/

namespace SparseHamiltonian.GateRangeHilbertTransport

noncomputable section
open ContinuousLinearMap OracleCircuit ComplexAmplitudeRotation
open scoped BigOperators InnerProduct ComplexConjugate
set_option maxRecDepth 8192

/- The algebraic comparator did not require enumeration.  Its Hilbert-space
lift does, so supply the finite configuration instances here without changing
the externally checked comparator section. -/
local instance comparatorDecidableEq (r : ℕ) :
    DecidableEq (GateConstantCompare.Configuration r) := Classical.decEq _

local instance comparatorFintype (r : ℕ) :
    Fintype (GateConstantCompare.Configuration r) :=
  Fintype.ofEquiv ((Fin r → Bool) × (Fin (r + 1) → Bool) × Bool)
    { toFun := fun z => ⟨z.1, z.2.1, z.2.2⟩
      invFun := fun z => (z.pointer, z.borrow, z.marked)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

abbrev Configuration (r : ℕ) := GateControlledCompare.Configuration r
abbrev Word (r : ℕ) := GateControlledCompare.Word r
abbrev Physical (r : ℕ) := EuclideanSpace ℂ (Configuration r)

section DiagonalAlgebra
variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
  [∀ i, InnerProductSpace ℂ (V i)] [∀ i, CompleteSpace (V i)]

omit [Fintype ι] [∀ (i : ι), CompleteSpace (V i)] in
/-- `WeightedClock.diagonal_comp` in ring notation. -/
theorem diagonal_mul' (A B : ∀ i, V i →L[ℂ] V i) :
    WeightedClock.diagonal A * WeightedClock.diagonal B =
      WeightedClock.diagonal (fun i => A i * B i) :=
  WeightedClock.diagonal_comp A B

/-- `WeightedClock.diagonal_adjoint` in star notation. -/
theorem diagonal_star' (A : ∀ i, V i →L[ℂ] V i) :
    star (WeightedClock.diagonal A) = WeightedClock.diagonal (fun i => star (A i)) :=
  WeightedClock.diagonal_adjoint A

end DiagonalAlgebra

/-- A reversible literal gate list is a basis permutation on the complete
physical register, including dirty borrow and marked wires. -/
def rangeEquiv (threshold : ℕ) (gs : List (GateControlledCompare.RangeGate r)) :
    Configuration r ≃ Configuration r where
  toFun := GateControlledCompare.rangeExec threshold gs
  invFun := GateControlledCompare.rangeExec threshold gs.reverse
  left_inv := GateControlledCompare.rangeExec_reverse_exec threshold gs
  right_inv := GateControlledCompare.rangeExec_exec_reverse threshold gs

/-- Hilbert-space unitary induced by the actual bounded-arity gate list. -/
def rangeUnitary (threshold : ℕ) (gs : List (GateControlledCompare.RangeGate r)) :
    Physical r →L[ℂ] Physical r :=
  (LookupOracle.permutationUnitary (rangeEquiv threshold gs)).toLinearIsometry.toContinuousLinearMap

theorem rangeUnitary_unitary (threshold : ℕ)
    (gs : List (GateControlledCompare.RangeGate r)) :
    IsUnitary (rangeUnitary threshold gs) := by
  exact LookupOracle.permutationUnitary_unitary (rangeEquiv threshold gs)

@[simp] theorem rangeUnitary_single (threshold : ℕ)
    (gs : List (GateControlledCompare.RangeGate r))
    (z : Configuration r) (a : ℂ) :
    rangeUnitary threshold gs (EuclideanSpace.single z a) =
      EuclideanSpace.single (GateControlledCompare.rangeExec threshold gs z) a := by
  exact LookupOracle.permutationUnitary_single (rangeEquiv threshold gs) z a

/-- The same phase-kickback vector as before, now in the genuine finite
Hilbert space rather than the algebraic finitely supported model. -/
def hilbertKickback (threshold : ℕ) (flag : Bool) (x : Word r)
    (a : ℂ) : Physical r :=
  EuclideanSpace.single (GateControlledCompare.encoded threshold 0 flag x false) a -
    EuclideanSpace.single (GateControlledCompare.encoded threshold 0 flag x true) a

theorem encoded_false_ne_true (threshold : ℕ) (flag : Bool) (x : Word r) :
    GateControlledCompare.encoded threshold 0 flag x false ≠
      GateControlledCompare.encoded threshold 0 flag x true := by
  intro h
  have hm := congrArg
    (fun z : Configuration r => z.2.marked) h
  change false = true at hm
  contradiction

/-- The two marked-wire components are orthogonal. -/
theorem hilbertKickback_norm_sq (threshold : ℕ) (flag : Bool)
    (x : Word r) (a : ℂ) :
    ‖hilbertKickback threshold flag x a‖ ^ 2 = 2 * ‖a‖ ^ 2 := by
  classical
  have hne := encoded_false_ne_true threshold flag x
  have hpoint (z : Configuration r) :
      ‖hilbertKickback threshold flag x a z‖ ^ 2 =
        (if z = GateControlledCompare.encoded threshold 0 flag x false
          then ‖a‖ ^ 2 else 0) +
        (if z = GateControlledCompare.encoded threshold 0 flag x true
          then ‖a‖ ^ 2 else 0) := by
    by_cases hf : z = GateControlledCompare.encoded threshold 0 flag x false
    · subst z
      simp [hilbertKickback, hne]
    · by_cases ht : z = GateControlledCompare.encoded threshold 0 flag x true
      · subst z
        simp [hilbertKickback, Ne.symm hne]
      · simp [hilbertKickback, hf, ht]
  rw [PiLp.norm_sq_eq_of_L2]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- The reusable marked wire in its unit minus state. -/
def minusQubit : Qubit :=
  WithLp.toLp 2 (fun b : Bool =>
    if b then -(GateWalshWords.half : ℂ) else GateWalshWords.half)

@[simp] theorem minusQubit_false : minusQubit false = GateWalshWords.half := rfl
@[simp] theorem minusQubit_true : minusQubit true = -(GateWalshWords.half : ℂ) := rfl

theorem minusQubit_norm : ‖minusQubit‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  simpa [minusQubit, Fintype.sum_bool, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg GateWalshWords.half_nonneg] using GateWalshWords.half_unit

/-- Normalised physical phase-kickback state. -/
def normalizedKickback (threshold : ℕ) (flag : Bool) (x : Word r) : Physical r :=
  hilbertKickback threshold flag x (GateWalshWords.half : ℂ)

theorem normalizedKickback_norm (threshold : ℕ) (flag : Bool) (x : Word r) :
    ‖normalizedKickback threshold flag x‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [normalizedKickback, hilbertKickback_norm_sq]
  simpa [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg GateWalshWords.half_nonneg, two_mul] using GateWalshWords.half_unit

/-- A clean borrow register is independent of the public comparator
threshold.  Consequently every comparison and reflection uses literally the
same physical phase-kickback states. -/
theorem encoded_zero_threshold_independent (threshold threshold' : ℕ)
    (flag : Bool) (x : Word r) (b : Bool) :
    GateControlledCompare.encoded threshold 0 flag x b =
      GateControlledCompare.encoded threshold' 0 flag x b := by
  apply Prod.ext
  · rfl
  · apply GateConstantCompare.Configuration.ext
    · rfl
    · change (GateConstantCompare.encoded threshold 0 x b).borrow =
        (GateConstantCompare.encoded threshold' 0 x b).borrow
      rw [GateConstantCompare.encoded_zero, GateConstantCompare.encoded_zero]
    · rfl

theorem normalizedKickback_threshold_independent
    (threshold threshold' : ℕ) (flag : Bool) (x : Word r) :
    normalizedKickback threshold flag x =
      normalizedKickback threshold' flag x := by
  simp [normalizedKickback, hilbertKickback,
    encoded_zero_threshold_independent threshold threshold']

/-- The literal accepted-range circuit has the required phase on the
normalised physical state, with every borrow wire returned clean. -/
theorem acceptedCompare_normalized (threshold : ℕ) (flag : Bool)
    (x : Word r) (h : threshold ≤ 2 ^ r) :
    rangeUnitary threshold (GateControlledCompare.acceptedCompareCircuit threshold r)
        (normalizedKickback threshold flag x) =
      (if flag = false ∧ GatePointerEncoding.wordValue x < threshold
        then (-1 : ℂ) else 1) • normalizedKickback threshold flag x := by
  unfold normalizedKickback hilbertKickback
  rw [map_sub, rangeUnitary_single, rangeUnitary_single,
    GateControlledCompare.acceptedCompareCircuit_correct threshold flag x false h,
    GateControlledCompare.acceptedCompareCircuit_correct threshold flag x true h]
  cases flag <;>
    by_cases hx : GatePointerEncoding.wordValue x < threshold <;>
    simp [hx]

/-- The literal zero-state reflection has the required sign convention on
the same normalised physical register. -/
theorem zeroReflection_normalized (flag : Bool) (x : Word r) :
    rangeUnitary 1 (GateControlledCompare.zeroStateReflectionCircuit r)
        (normalizedKickback 1 flag x) =
      (if flag = false ∧ GatePointerEncoding.wordValue x = 0
        then (1 : ℂ) else -1) • normalizedKickback 1 flag x := by
  unfold normalizedKickback hilbertKickback
  rw [map_sub, rangeUnitary_single, rangeUnitary_single,
    GateControlledCompare.zeroStateReflectionCircuit_correct flag x false,
    GateControlledCompare.zeroStateReflectionCircuit_correct flag x true]
  by_cases h : flag = false ∧ GatePointerEncoding.wordValue x = 0 <;>
    simp [h]

/-- The two literal reflections on their common physical register, in the
chronological order used by one amplification round. -/
def reflectionPair (n r : ℕ) : Physical r →L[ℂ] Physical r :=
  rangeUnitary 1 (GateControlledCompare.zeroStateReflectionCircuit r) *
    rangeUnitary n (GateControlledCompare.acceptedCompareCircuit n r)

theorem reflectionPair_unitary (n r : ℕ) : IsUnitary (reflectionPair n r) :=
  (rangeUnitary_unitary 1 (GateControlledCompare.zeroStateReflectionCircuit r)).mul
    (rangeUnitary_unitary n (GateControlledCompare.acceptedCompareCircuit n r))

/-- Exact common-register action of the reflection pair. -/
theorem reflectionPair_normalized (n r : ℕ) (flag : Bool) (x : Word r)
    (hn : n ≤ 2 ^ r) :
    reflectionPair n r (normalizedKickback n flag x) =
      ((if flag = false ∧ GatePointerEncoding.wordValue x < n
          then (-1 : ℂ) else 1) *
        (if flag = false ∧ GatePointerEncoding.wordValue x = 0
          then (1 : ℂ) else -1)) • normalizedKickback n flag x := by
  change rangeUnitary 1 (GateControlledCompare.zeroStateReflectionCircuit r)
      (rangeUnitary n (GateControlledCompare.acceptedCompareCircuit n r)
        (normalizedKickback n flag x)) = _
  rw [acceptedCompare_normalized n flag x hn, map_smul]
  have hz : rangeUnitary 1 (GateControlledCompare.zeroStateReflectionCircuit r)
      (normalizedKickback n flag x) =
      (if flag = false ∧ GatePointerEncoding.wordValue x = 0
        then (1 : ℂ) else -1) • normalizedKickback n flag x := by
    rw [normalizedKickback_threshold_independent n 1]
    exact zeroReflection_normalized flag x
  rw [hz, smul_smul]

/-- The known one-qubit phase which changes the positive Walsh column into
the marked-wire minus state. -/
def minusPhase : Qubit →L[ℂ] Qubit := matrix 1 0 0 (-1)

theorem minusPhase_unitary : IsUnitary minusPhase := by
  constructor
  · ext v b
    cases b <;>
      simp [minusPhase, ContinuousLinearMap.star_eq_adjoint, matrix_adjoint, one_def]
  · ext v b
    cases b <;>
      simp [minusPhase, ContinuousLinearMap.star_eq_adjoint, matrix_adjoint, one_def]

/-- One positive Walsh rotation followed by one known phase prepares the
normalised minus wire. -/
def minusPreparation : Qubit →L[ℂ] Qubit :=
  minusPhase * GateWalshHilbert.localRotation

theorem minusPreparation_unitary : IsUnitary minusPreparation :=
  minusPhase_unitary.mul GateWalshHilbert.localRotation_unitary

theorem minusPreparation_clean :
    minusPreparation ComplexAmplitudeRotation.clean = minusQubit := by
  apply PiLp.ext
  intro b
  cases b <;>
    simp [minusPreparation, minusPhase, GateWalshHilbert.localRotation,
      minusQubit, ComplexAmplitudeRotation.clean]

/-- The adjoint unprepares the minus wire exactly; it is not discarded. -/
theorem minusPreparation_adjoint_minus :
    (minusPreparation†) minusQubit = ComplexAmplitudeRotation.clean := by
  have h := congrArg
    (fun F : Qubit →L[ℂ] Qubit => F ComplexAmplitudeRotation.clean)
    minusPreparation_unitary.1
  change (minusPreparation†)
    (minusPreparation ComplexAmplitudeRotation.clean) =
      ComplexAmplitudeRotation.clean at h
  simpa only [minusPreparation_clean] using h

/-- All physical data other than the marked wire. -/
@[ext] structure Payload (r : ℕ) where
  flag : Bool
  pointer : Word r
  borrow : Fin (r + 1) → Bool
  deriving DecidableEq, Fintype

/-- Expose the marked wire without changing any physical information. -/
def markedSplit (r : ℕ) : Configuration r ≃ Payload r × Bool where
  toFun z := (⟨z.1, z.2.pointer, z.2.borrow⟩, z.2.marked)
  invFun z := (z.1.flag,
    { pointer := z.1.pointer, borrow := z.1.borrow, marked := z.2 })
  left_inv z := by rcases z with ⟨flag, z⟩; rcases z; rfl
  right_inv z := by rcases z with ⟨p, b⟩; rcases p; rfl

/-- Common normalised Hilbert-space layout for both literal reflections. -/
def markedLayout (r : ℕ) :
    Physical r ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Payload r => Qubit) :=
  (LookupOracle.permutationUnitary (markedSplit r)).trans
    (RegisterEquivalences.productFlatten (Payload r) Bool).symm

@[simp] theorem markedLayout_apply (r : ℕ) (v : Physical r)
    (p : Payload r) (b : Bool) :
    markedLayout r v p b = v ((markedSplit r).symm (p, b)) := rfl

/-- Lift one actual marked-wire gate while leaving the flag, pointer and
borrow registers untouched. -/
def markedGate (r : ℕ) (U : Qubit →L[ℂ] Qubit) : Physical r →L[ℂ] Physical r :=
  (markedLayout r).symm.conjStarAlgEquiv
    (WeightedClock.diagonal (fun _ : Payload r => U))

theorem markedGate_unitary (r : ℕ) (U : Qubit →L[ℂ] Qubit)
    (hU : IsUnitary U) : IsUnitary (markedGate r U) := by
  have hd : IsUnitary (WeightedClock.diagonal (fun _ : Payload r => U)) := by
    constructor
    · exact WeightedClock.diagonal_isometry _ (fun _ => hU.1)
    · change WeightedClock.diagonal (fun _ : Payload r => U) ∘L
        (WeightedClock.diagonal (fun _ : Payload r => U))† = 1
      have hi : U ∘L U† = 1 := hU.2
      rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
      simp only [hi, WeightedClock.diagonal_one]
  exact hd.transport (markedLayout r).symm

/-- Coordinate semantics of the actual common-register marked-wire gate. -/
theorem markedGate_layout_apply (r : ℕ) (U : Qubit →L[ℂ] Qubit)
    (v : Physical r) (p : Payload r) (b : Bool) :
    markedLayout r (markedGate r U v) p b = U (markedLayout r v p) b := by
  rw [markedGate, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  simp only [LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.apply_symm_apply, WeightedClock.diagonal_apply]

def prepareMinus (r : ℕ) : Physical r →L[ℂ] Physical r :=
  markedGate r minusPreparation

theorem prepareMinus_unitary (r : ℕ) : IsUnitary (prepareMinus r) :=
  markedGate_unitary r minusPreparation minusPreparation_unitary

/-- Exact full-register preparation semantics in the exposed marked-wire
layout, valid coherently for every payload. -/
theorem prepareMinus_layout_apply (r : ℕ) (v : Physical r)
    (p : Payload r) (b : Bool) :
    markedLayout r (prepareMinus r v) p b =
      minusPreparation (markedLayout r v p) b :=
  markedGate_layout_apply r minusPreparation v p b

/-- Preparation followed by its actual adjoint is the identity on the whole
physical register, including dirty workspaces. -/
theorem prepareMinus_adjoint_comp (r : ℕ) :
    (prepareMinus r)† ∘L prepareMinus r = 1 :=
  (prepareMinus_unitary r).1

/-- A vector supported on one non-marked payload, with arbitrary marked-wire
state.  The surrounding layout is an isometry, so this is the canonical
tensoring operation for the reusable marked ancilla. -/
def packet (r : ℕ) (p : Payload r) (q : Qubit) : Physical r :=
  (markedLayout r).symm
    (WithLp.toLp 2 (fun p' : Payload r => if p' = p then q else 0))

@[simp] theorem markedLayout_packet (r : ℕ) (p p' : Payload r) (q : Qubit) :
    markedLayout r (packet r p q) p' = if p' = p then q else 0 := by
  simp [packet]

theorem packet_norm (r : ℕ) (p : Payload r) (q : Qubit) :
    ‖packet r p q‖ = ‖q‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [packet, LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2]
  simp [apply_ite]

def cleanPacket (r : ℕ) (p : Payload r) : Physical r :=
  packet r p ComplexAmplitudeRotation.clean

def minusPacket (r : ℕ) (p : Payload r) : Physical r :=
  packet r p minusQubit

theorem cleanPacket_norm (r : ℕ) (p : Payload r) : ‖cleanPacket r p‖ = 1 := by
  rw [cleanPacket, packet_norm, AmplitudePolynomialSequence.clean_norm]

theorem minusPacket_norm (r : ℕ) (p : Payload r) : ‖minusPacket r p‖ = 1 := by
  rw [minusPacket, packet_norm, minusQubit_norm]

/-- Clean physical payload carried by an encoded pointer word. -/
def encodedPayload (flag : Bool) (x : Word r) : Payload r where
  flag := flag
  pointer := x
  borrow := fun _ => false

theorem markedSplit_encoded (threshold : ℕ) (flag : Bool) (x : Word r)
    (b : Bool) :
    markedSplit r (GateControlledCompare.encoded threshold 0 flag x b) =
      (encodedPayload flag x, b) := by
  apply Prod.ext
  · apply Payload.ext
    · rfl
    · rfl
    · exact GateConstantCompare.encoded_zero threshold x b
  · rfl

theorem markedSplit_symm_encoded (threshold : ℕ) (flag : Bool) (x : Word r)
    (b : Bool) :
    (markedSplit r).symm (encodedPayload flag x, b) =
      GateControlledCompare.encoded threshold 0 flag x b := by
  apply (markedSplit r).injective
  simp only [Equiv.apply_symm_apply, markedSplit_encoded]

/-- In the marked-wire layout the normalised kickback vector is exactly one
payload basis state tensored with `minusQubit`. -/
theorem markedLayout_normalizedKickback (threshold : ℕ) (flag : Bool)
    (x : Word r) (p : Payload r) (b : Bool) :
    markedLayout r (normalizedKickback threshold flag x) p b =
      if p = encodedPayload flag x then minusQubit b else 0 := by
  classical
  rw [markedLayout_apply]
  by_cases hp : p = encodedPayload flag x
  · subst p
    rw [markedSplit_symm_encoded threshold flag x b]
    cases b <;>
      simp [normalizedKickback, hilbertKickback,
        encoded_false_ne_true threshold flag x,
        Ne.symm (encoded_false_ne_true threshold flag x)]
  · have hfalse : (markedSplit r).symm (p, b) ≠
        GateControlledCompare.encoded threshold 0 flag x false := by
      intro h
      apply hp
      have h' := congrArg (fun z => (markedSplit r z).1) h
      simpa only [Equiv.apply_symm_apply, markedSplit_encoded] using h'
    have htrue : (markedSplit r).symm (p, b) ≠
        GateControlledCompare.encoded threshold 0 flag x true := by
      intro h
      apply hp
      have h' := congrArg (fun z => (markedSplit r z).1) h
      simpa only [Equiv.apply_symm_apply, markedSplit_encoded] using h'
    simp [normalizedKickback, hilbertKickback, hp, hfalse, htrue,
      ]

theorem normalizedKickback_eq_minusPacket (threshold : ℕ) (flag : Bool)
    (x : Word r) :
    normalizedKickback threshold flag x =
      minusPacket r (encodedPayload flag x) := by
  apply (markedLayout r).injective
  apply PiLp.ext
  intro p
  apply PiLp.ext
  intro b
  rw [markedLayout_normalizedKickback]
  by_cases hp : p = encodedPayload flag x <;> simp [minusPacket, hp]

/-- Physical computational input with clean borrow and marked wires. -/
def cleanComputational (threshold : ℕ) (flag : Bool) (x : Word r) : Physical r :=
  EuclideanSpace.single
    (GateControlledCompare.encoded threshold 0 flag x false) 1

theorem cleanComputational_eq_cleanPacket (threshold : ℕ) (flag : Bool)
    (x : Word r) :
    cleanComputational threshold flag x = cleanPacket r (encodedPayload flag x) := by
  apply (markedLayout r).injective
  apply PiLp.ext
  intro p
  apply PiLp.ext
  intro b
  rw [cleanPacket, markedLayout_packet]
  rw [markedLayout_apply]
  by_cases hp : p = encodedPayload flag x
  · subst p
    rw [markedSplit_symm_encoded threshold flag x b]
    cases b <;>
      simp [cleanComputational,
        
        Ne.symm (encoded_false_ne_true threshold flag x),
        ComplexAmplitudeRotation.clean]
  · have hne : (markedSplit r).symm (p, b) ≠
        GateControlledCompare.encoded threshold 0 flag x false := by
      intro h
      apply hp
      have h' := congrArg (fun z => (markedSplit r z).1) h
      simpa only [Equiv.apply_symm_apply, markedSplit_encoded] using h'
    simp [cleanComputational, hp, hne]

/-- The common-register preparation maps every clean payload basis state to
the corresponding unit minus packet, without changing its other wires. -/
theorem prepareMinus_cleanPacket (r : ℕ) (p : Payload r) :
    prepareMinus r (cleanPacket r p) = minusPacket r p := by
  apply (markedLayout r).injective
  apply PiLp.ext
  intro p'
  apply PiLp.ext
  intro b
  rw [prepareMinus_layout_apply]
  by_cases hp : p' = p
  · subst p'
    simp [cleanPacket, minusPacket, minusPreparation_clean]
  · simp [cleanPacket, minusPacket, hp]

/-- The actual adjoint restores the clean marked wire on every payload. -/
theorem prepareMinus_adjoint_minusPacket (r : ℕ) (p : Payload r) :
    ((prepareMinus r)†) (minusPacket r p) = cleanPacket r p := by
  have h := congrArg
    (fun F : Physical r →L[ℂ] Physical r => F (cleanPacket r p))
    (prepareMinus_adjoint_comp r)
  change ((prepareMinus r)†) (prepareMinus r (cleanPacket r p)) =
    cleanPacket r p at h
  simpa only [prepareMinus_cleanPacket] using h

/-- End-to-end preparation of the normalised comparator phase state on the
actual physical register. -/
theorem prepareMinus_cleanComputational (threshold : ℕ) (flag : Bool)
    (x : Word r) :
    prepareMinus r (cleanComputational threshold flag x) =
      normalizedKickback threshold flag x := by
  rw [cleanComputational_eq_cleanPacket, prepareMinus_cleanPacket,
    normalizedKickback_eq_minusPacket]

/-- The same physical circuit is uncomputed exactly after the comparison
and reflection sequence. -/
theorem prepareMinus_adjoint_normalized (threshold : ℕ) (flag : Bool)
    (x : Word r) :
    ((prepareMinus r)†) (normalizedKickback threshold flag x) =
      cleanComputational threshold flag x := by
  rw [normalizedKickback_eq_minusPacket, prepareMinus_adjoint_minusPacket,
    ← cleanComputational_eq_cleanPacket]

/-- Literal one-wire instructions used to prepare the marked minus state. -/
inductive MarkedWireGate
  | walsh
  | walshAdjoint
  | phase

def MarkedWireGate.eval : MarkedWireGate → Qubit →L[ℂ] Qubit
  | .walsh => GateWalshHilbert.localRotation
  | .walshAdjoint => GateWalshHilbert.localRotation†
  | .phase => minusPhase

def MarkedWireGate.arity : MarkedWireGate → ℕ
  | .walsh => 1
  | .walshAdjoint => 1
  | .phase => 1

theorem MarkedWireGate.arity_eq_one (g : MarkedWireGate) : g.arity = 1 := by
  cases g <;> rfl

def MarkedWireGate.inverse : MarkedWireGate → MarkedWireGate
  | .walsh => .walshAdjoint
  | .walshAdjoint => .walsh
  | .phase => .phase

@[simp] theorem MarkedWireGate.inverse_inverse (g : MarkedWireGate) :
    g.inverse.inverse = g := by
  cases g <;> rfl

theorem minusPhase_adjoint : minusPhase† = minusPhase := by
  simp [minusPhase, matrix_adjoint]

theorem MarkedWireGate.eval_inverse (g : MarkedWireGate) :
    g.inverse.eval = g.eval† := by
  cases g <;> simp [MarkedWireGate.inverse, MarkedWireGate.eval,
    minusPhase_adjoint]

def markedWireRun : List MarkedWireGate → Qubit →L[ℂ] Qubit
  | [] => 1
  | g :: gs => markedWireRun gs * g.eval

def minusPreparationCircuit : List MarkedWireGate := [.walsh, .phase]

def markedWireInverse (gs : List MarkedWireGate) : List MarkedWireGate :=
  gs.reverse.map MarkedWireGate.inverse

def minusUnpreparationCircuit : List MarkedWireGate :=
  markedWireInverse minusPreparationCircuit

theorem minusPreparationCircuit_length : minusPreparationCircuit.length = 2 := rfl

theorem markedWireInverse_length (gs : List MarkedWireGate) :
    (markedWireInverse gs).length = gs.length := by
  simp [markedWireInverse]

theorem minusUnpreparationCircuit_length : minusUnpreparationCircuit.length = 2 := by
  rw [minusUnpreparationCircuit, markedWireInverse_length,
    minusPreparationCircuit_length]

theorem minusPreparationCircuit_eval :
    markedWireRun minusPreparationCircuit = minusPreparation := by
  simp [minusPreparationCircuit, markedWireRun, MarkedWireGate.eval,
    minusPreparation]

theorem markedWireRun_append (gs hs : List MarkedWireGate) :
    markedWireRun (gs ++ hs) = markedWireRun hs * markedWireRun gs := by
  induction gs with
  | nil => simp [markedWireRun]
  | cons g gs ih => simp [markedWireRun, ih, mul_assoc]

theorem markedWireRun_inverse (gs : List MarkedWireGate) :
    markedWireRun (markedWireInverse gs) = (markedWireRun gs)† := by
  induction gs with
  | nil => simp [markedWireInverse, markedWireRun]
  | cons g gs ih =>
      change markedWireRun (gs.reverse.map MarkedWireGate.inverse) =
        (markedWireRun gs)† at ih
      rw [markedWireInverse, List.reverse_cons, List.map_append,
        markedWireRun_append]
      simp only [List.map_cons, List.map_nil, markedWireRun, one_mul,
        MarkedWireGate.eval_inverse, ih]
      change star g.eval * star (markedWireRun gs) =
        star (markedWireRun gs * g.eval)
      rw [star_mul]

theorem minusUnpreparationCircuit_eval :
    markedWireRun minusUnpreparationCircuit = minusPreparation† := by
  rw [minusUnpreparationCircuit, markedWireRun_inverse,
    minusPreparationCircuit_eval]

theorem markedGate_mul (r : ℕ) (U V : Qubit →L[ℂ] Qubit) :
    markedGate r (U * V) = markedGate r U * markedGate r V := by
  unfold markedGate
  rw [← map_mul]
  exact congrArg ((markedLayout r).symm.conjStarAlgEquiv)
    (WeightedClock.diagonal_comp
      (fun _ : Payload r => U) (fun _ : Payload r => V)).symm

theorem markedGate_adjoint (r : ℕ) (U : Qubit →L[ℂ] Qubit) :
    markedGate r (U†) = (markedGate r U)† := by
  unfold markedGate
  rw [← WeightedClock.diagonal_adjoint (fun _ : Payload r => U)]
  exact map_star ((markedLayout r).symm.conjStarAlgEquiv) _

def physicalMarkedRun (r : ℕ) : List MarkedWireGate → Physical r →L[ℂ] Physical r
  | [] => 1
  | g :: gs => physicalMarkedRun r gs * markedGate r g.eval

theorem physicalMarkedRun_append (r : ℕ) (gs hs : List MarkedWireGate) :
    physicalMarkedRun r (gs ++ hs) =
      physicalMarkedRun r hs * physicalMarkedRun r gs := by
  induction gs with
  | nil => simp [physicalMarkedRun]
  | cons g gs ih => simp [physicalMarkedRun, ih, mul_assoc]

theorem physicalMarkedRun_inverse (r : ℕ) (gs : List MarkedWireGate) :
    physicalMarkedRun r (markedWireInverse gs) = (physicalMarkedRun r gs)† := by
  induction gs with
  | nil => simp [markedWireInverse, physicalMarkedRun]
  | cons g gs ih =>
      change physicalMarkedRun r (gs.reverse.map MarkedWireGate.inverse) =
        (physicalMarkedRun r gs)† at ih
      rw [markedWireInverse, List.reverse_cons, List.map_append,
        physicalMarkedRun_append]
      simp only [List.map_cons, List.map_nil, physicalMarkedRun, one_mul,
        MarkedWireGate.eval_inverse, markedGate_adjoint, ih]
      change star (markedGate r g.eval) * star (physicalMarkedRun r gs) =
        star (physicalMarkedRun r gs * markedGate r g.eval)
      rw [star_mul]

/-- The charged two-gate physical circuit is exactly the previously defined
common-register preparation operator. -/
theorem physicalMinusPreparationCircuit_eval (r : ℕ) :
    physicalMarkedRun r minusPreparationCircuit = prepareMinus r := by
  simp [physicalMarkedRun, minusPreparationCircuit, MarkedWireGate.eval,
    prepareMinus, minusPreparation, markedGate_mul]

theorem physicalMinusUnpreparationCircuit_eval (r : ℕ) :
    physicalMarkedRun r minusUnpreparationCircuit = (prepareMinus r)† := by
  rw [minusUnpreparationCircuit, physicalMarkedRun_inverse,
    physicalMinusPreparationCircuit_eval]

/-! ### Exact known-gate budget of one range preparation -/

/-- The gate count obtained by substituting the literal Walsh, attenuation,
zero-reflection, accepted-range and reusable-minus circuits into the three
preparation occurrences of `GateUniformRange.rangeProgram`. -/
def rangePreparationKnownGates (n r : ℕ) : ℕ :=
  3 * ((GateWalshWords.circuit r le_rfl).length + 1) +
    (GateControlledCompare.zeroStateReflectionCircuit r).length +
    (GateControlledCompare.acceptedCompareCircuit n r).length +
    minusPreparationCircuit.length + minusUnpreparationCircuit.length

/-- One exact range preparation uses at most `7r+14` known bounded-arity
gates.  This is independent of the value of the endpoint `n`; its only use
is as public data in the comparator gates. -/
theorem rangePreparationKnownGates_le (n r : ℕ) :
    rangePreparationKnownGates n r ≤ 7 * r + 14 := by
  have hz := GateControlledCompare.zeroStateReflectionCircuit_length r
  have hg := GateControlledCompare.acceptedCompareCircuit_length n r
  rw [rangePreparationKnownGates, GateWalshWords.circuit_length,
    minusPreparationCircuit_length, minusUnpreparationCircuit_length]
  omega

/-- The same estimate includes only actual gates of arity at most three:
Walsh, attenuation, and marked-wire preparation gates have arity one, while
the two comparison circuits have their arity bounds proved above. -/
theorem rangePreparation_gate_arity_bound :
    (∀ g : MarkedWireGate, g.arity ≤ 3) ∧
    (∀ g : GateControlledCompare.RangeGate r, g.arity ≤ 3) := by
  constructor
  · intro g
    rw [MarkedWireGate.arity_eq_one]
    omega
  · exact GateControlledCompare.RangeGate.arity_le_three

/-! ### Isometric embedding of the logical range register -/

/-- Tensor an arbitrary finite register with a fixed computational-basis
ancilla.  No algebraic structure on the ancilla alphabet is required. -/
def fixedBasisEmbedding {B Z : Type*} [Fintype B] [Fintype Z]
    [DecidableEq Z] (z₀ : Z) :
    EuclideanSpace ℂ B →ₗᵢ[ℂ] EuclideanSpace ℂ (B × Z) where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (fun bz => if bz.2 = z₀ then v bz.1 else 0)
      map_add' := by
        intro v w
        apply PiLp.ext
        intro bz
        by_cases h : bz.2 = z₀ <;> simp [h]
      map_smul' := by
        intro c v
        apply PiLp.ext
        intro bz
        by_cases h : bz.2 = z₀ <;> simp [h] }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : B × Z => ℂ),
      PiLp.norm_sq_eq_of_L2 (fun _ : B => ℂ), Fintype.sum_prod_type]
    change (∑ b : B, ∑ z : Z,
      ‖if z = z₀ then v b else 0‖ ^ 2) = ∑ b : B, ‖v b‖ ^ 2
    apply Finset.sum_congr rfl
    intro b hb
    calc
      (∑ z : Z, ‖if z = z₀ then v b else 0‖ ^ 2) =
          ∑ z : Z, if z = z₀ then ‖v b‖ ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro z hz
        by_cases h : z = z₀ <;>
          simp only [h, if_true, if_false, norm_zero, pow_two, zero_mul]
      _ = ‖v b‖ ^ 2 := by simp

@[simp] theorem fixedBasisEmbedding_apply {B Z : Type*} [Fintype B]
    [Fintype Z] [DecidableEq Z] (z₀ : Z) (v : EuclideanSpace ℂ B)
    (b : B) (z : Z) :
    fixedBasisEmbedding z₀ v (b, z) = if z = z₀ then v b else 0 := rfl

abbrev LogicalIndex (r : ℕ) := Fin (2 ^ r) × Bool
abbrev BorrowRegister (r : ℕ) := Fin (r + 1) → Bool

/-- The established little-endian word equivalence, attenuation flag and
borrow register together form exactly the non-marked physical payload. -/
def payloadEquiv (r : ℕ) :
    LogicalIndex r × BorrowRegister r ≃ Payload r where
  toFun z :=
    { flag := z.1.2
      pointer := (GatePointerEncoding.wordEquivFin r).symm z.1.1
      borrow := z.2 }
  invFun p := ((GatePointerEncoding.wordEquivFin r p.pointer, p.flag), p.borrow)
  left_inv z := by
    rcases z with ⟨⟨j, b⟩, borrow⟩
    change (((GatePointerEncoding.wordEquivFin r)
      ((GatePointerEncoding.wordEquivFin r).symm j), b), borrow) = ((j, b), borrow)
    rw [Equiv.apply_symm_apply]
  right_inv p := by
    rcases p with ⟨b, x, borrow⟩
    change (⟨b, (GatePointerEncoding.wordEquivFin r).symm
      (GatePointerEncoding.wordEquivFin r x), borrow⟩ : Payload r) = ⟨b, x, borrow⟩
    rw [Equiv.symm_apply_apply]

def cleanBorrow (r : ℕ) : BorrowRegister r := fun _ => false

/-- Relabel the logical word and flag, while inserting every borrow wire in
its clean computational state. -/
def payloadEmbedding (r : ℕ) :
    EuclideanSpace ℂ (LogicalIndex r) →ₗᵢ[ℂ] EuclideanSpace ℂ (Payload r) :=
  (LookupOracle.permutationUnitary (payloadEquiv r)).toLinearIsometry.comp
    (fixedBasisEmbedding (cleanBorrow r))

@[simp] theorem payloadEmbedding_apply (r : ℕ)
    (v : EuclideanSpace ℂ (LogicalIndex r)) (p : Payload r) :
    payloadEmbedding r v p =
      if p.borrow = cleanBorrow r
      then v (GatePointerEncoding.wordEquivFin r p.pointer, p.flag)
      else 0 := rfl

/-- Tensor a coherent payload state with the already normalised marked-wire
minus state. -/
def minusEmbedding (r : ℕ) :
    EuclideanSpace ℂ (Payload r) →ₗᵢ[ℂ]
      PiLp 2 (fun _ : Payload r => Qubit) where
  toLinearMap :=
    { toFun := fun v => WithLp.toLp 2 (fun p => v p • minusQubit)
      map_add' := by
        intro v w
        apply PiLp.ext
        intro p
        simp [add_smul]
      map_smul' := by
        intro c v
        apply PiLp.ext
        intro p
        simp [smul_smul] }
  norm_map' := by
    intro v
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2 (fun _ : Payload r => Qubit),
      PiLp.norm_sq_eq_of_L2 (fun _ : Payload r => ℂ)]
    change (∑ p : Payload r, ‖v p • minusQubit‖ ^ 2) =
      ∑ p : Payload r, ‖v p‖ ^ 2
    simp only [norm_smul, minusQubit_norm, mul_one]

@[simp] theorem minusEmbedding_apply (r : ℕ)
    (v : EuclideanSpace ℂ (Payload r)) (p : Payload r) (b : Bool) :
    minusEmbedding r v p b = v p * minusQubit b := rfl

/-- Complete normalised embedding of the logical word/attenuation register
into the comparator workspace.  Its borrow wires are clean and its marked
wire is the reusable minus ancilla. -/
def logicalEmbedding (r : ℕ) :
    GateUniformRange.Space (2 ^ r) →ₗᵢ[ℂ] Physical r :=
  (markedLayout r).symm.toLinearIsometry.comp
    ((minusEmbedding r).comp
      ((payloadEmbedding r).comp
        (RegisterEquivalences.productFlatten (Fin (2 ^ r)) Bool).toLinearIsometry))

theorem logicalEmbedding_norm (r : ℕ)
    (v : GateUniformRange.Space (2 ^ r)) :
    ‖logicalEmbedding r v‖ = ‖v‖ :=
  (logicalEmbedding r).norm_map v

/-- Full coordinate formula for the common embedding. -/
theorem markedLayout_logicalEmbedding_apply (r : ℕ)
    (v : GateUniformRange.Space (2 ^ r)) (p : Payload r) (b : Bool) :
    markedLayout r (logicalEmbedding r v) p b =
      (if p.borrow = cleanBorrow r
        then v (GatePointerEncoding.wordEquivFin r p.pointer) p.flag
        else 0) * minusQubit b := by
  change (markedLayout r ((markedLayout r).symm
    (minusEmbedding r (payloadEmbedding r
      (RegisterEquivalences.productFlatten (Fin (2 ^ r)) Bool v))))) p b = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- Computational basis state of one logical pointer word and attenuation
flag. -/
def logicalBasis (x : Word r) (flag : Bool) :
    GateUniformRange.Space (2 ^ r) :=
  WithLp.toLp 2 (fun j : Fin (2 ^ r) =>
    WithLp.toLp 2 (fun b : Bool =>
      if j = GatePointerEncoding.wordEquivFin r x ∧ b = flag then 1 else 0))

@[simp] theorem logicalBasis_apply (x : Word r) (flag : Bool)
    (j : Fin (2 ^ r)) (b : Bool) :
    logicalBasis x flag j b =
      if j = GatePointerEncoding.wordEquivFin r x ∧ b = flag then 1 else 0 := rfl

theorem logicalBasis_norm (x : Word r) (flag : Bool) :
    ‖logicalBasis x flag‖ = 1 := by
  classical
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    (∑ j : Fin (2 ^ r), ‖logicalBasis x flag j‖ ^ 2) =
        ∑ j : Fin (2 ^ r),
          if j = GatePointerEncoding.wordEquivFin r x then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [logicalBasis_apply]
      by_cases h : j = GatePointerEncoding.wordEquivFin r x
      · simp only [h, true_and, if_true]
        cases flag <;> norm_num [Fintype.sum_bool]
      · simp only [h, false_and, if_false, norm_zero, pow_two, zero_mul,
          Finset.sum_const_zero]
    _ = (1 : ℝ) ^ 2 := by
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, one_pow]

/-- The complete isometry maps each logical basis state to precisely the
normalised clean phase-kickback state used by the actual comparison lists. -/
theorem logicalEmbedding_basis (threshold : ℕ) (x : Word r) (flag : Bool) :
    logicalEmbedding r (logicalBasis x flag) =
      normalizedKickback threshold flag x := by
  apply (markedLayout r).injective
  apply PiLp.ext
  intro p
  apply PiLp.ext
  intro b
  rw [markedLayout_logicalEmbedding_apply,
    markedLayout_normalizedKickback, logicalBasis_apply]
  have hp : p = encodedPayload flag x ↔
      p.borrow = cleanBorrow r ∧
        (GatePointerEncoding.wordEquivFin r p.pointer =
          GatePointerEncoding.wordEquivFin r x ∧ p.flag = flag) := by
    constructor
    · intro h
      subst p
      exact ⟨rfl, rfl, rfl⟩
    · rintro ⟨hb, hx, hf⟩
      have hx' : p.pointer = x := (GatePointerEncoding.wordEquivFin r).injective hx
      rcases p with ⟨pflag, pointer, borrow⟩
      change borrow = cleanBorrow r at hb
      change pointer = x at hx'
      change pflag = flag at hf
      subst pflag
      subst pointer
      subst borrow
      rfl
  by_cases hb : p.borrow = cleanBorrow r <;>
    by_cases hx : GatePointerEncoding.wordEquivFin r p.pointer =
        GatePointerEncoding.wordEquivFin r x ∧ p.flag = flag <;>
      simp only [hp, hb, hx, true_and, false_and, if_true, if_false,
        one_mul, zero_mul]

theorem goodPhase_logicalBasis (threshold : ℕ) (x : Word r) (flag : Bool) :
    PhaseSubspaceGates.phase
        (GateUniformRange.goodProjection threshold (2 ^ r)) (-1)
        (logicalBasis x flag) =
      (if flag = false ∧ GatePointerEncoding.wordValue x < threshold
        then (-1 : ℂ) else 1) • logicalBasis x flag := by
  apply PiLp.ext
  intro j
  apply PiLp.ext
  intro b
  simp only [PiLp.smul_apply, smul_eq_mul]
  by_cases hbasis : j = GatePointerEncoding.wordEquivFin r x ∧ b = flag
  · rcases hbasis with ⟨hj, hb⟩
    subst j
    subst b
    exact GateUniformRange.goodPhase_word threshold r (logicalBasis x flag) x flag
  · rw [GateUniformRange.goodPhase_apply]
    simp only [logicalBasis_apply, if_neg hbasis, mul_zero]

/-- Basis-level intertwining of the actual accepted-range circuit and its
logical phase predicate.  The remaining full-operator theorem is the finite
linear extension of these basis identities. -/
theorem acceptedCompare_logicalBasis (threshold : ℕ) (x : Word r)
    (flag : Bool) (h : threshold ≤ 2 ^ r) :
    rangeUnitary threshold (GateControlledCompare.acceptedCompareCircuit threshold r)
        (logicalEmbedding r (logicalBasis x flag)) =
      (if flag = false ∧ GatePointerEncoding.wordValue x < threshold
        then (-1 : ℂ) else 1) •
          logicalEmbedding r (logicalBasis x flag) := by
  let s : ℂ := if flag = false ∧ GatePointerEncoding.wordValue x < threshold
    then -1 else 1
  calc
    _ = rangeUnitary threshold
        (GateControlledCompare.acceptedCompareCircuit threshold r)
        (normalizedKickback threshold flag x) := by
          rw [logicalEmbedding_basis threshold]
    _ = s • normalizedKickback threshold flag x :=
      acceptedCompare_normalized threshold flag x h
    _ = s • logicalEmbedding r (logicalBasis x flag) := by
      rw [logicalEmbedding_basis threshold]

/-- Exact basis intertwining with the released logical successful-subspace
phase. -/
theorem acceptedCompare_basis_intertwines (threshold : ℕ) (x : Word r)
    (flag : Bool) (h : threshold ≤ 2 ^ r) :
    rangeUnitary threshold (GateControlledCompare.acceptedCompareCircuit threshold r)
        (logicalEmbedding r (logicalBasis x flag)) =
      logicalEmbedding r
        (PhaseSubspaceGates.phase
          (GateUniformRange.goodProjection threshold (2 ^ r)) (-1)
          (logicalBasis x flag)) := by
  rw [goodPhase_logicalBasis, map_smul]
  exact acceptedCompare_logicalBasis threshold x flag h

/-- Basis-level intertwining of the actual initial-state reflection. -/
theorem zeroReflection_logicalBasis (x : Word r) (flag : Bool) :
    rangeUnitary 1 (GateControlledCompare.zeroStateReflectionCircuit r)
        (logicalEmbedding r (logicalBasis x flag)) =
      (if flag = false ∧ GatePointerEncoding.wordValue x = 0
        then (1 : ℂ) else -1) •
          logicalEmbedding r (logicalBasis x flag) := by
  let s : ℂ := if flag = false ∧ GatePointerEncoding.wordValue x = 0
    then 1 else -1
  calc
    _ = rangeUnitary 1 (GateControlledCompare.zeroStateReflectionCircuit r)
        (normalizedKickback 1 flag x) := by
          rw [logicalEmbedding_basis 1]
    _ = s • normalizedKickback 1 flag x := zeroReflection_normalized flag x
    _ = s • logicalEmbedding r (logicalBasis x flag) := by
      rw [logicalEmbedding_basis 1]

theorem logicalZeroReflection_basis (x : Word r) (flag : Bool) :
    GateUniformRange.stateReflection (GateWalshHilbert.cleanInput r)
        (logicalBasis x flag) =
      (if flag = false ∧ GatePointerEncoding.wordValue x = 0
        then (1 : ℂ) else -1) • logicalBasis x flag := by
  apply PiLp.ext
  intro j
  apply PiLp.ext
  intro b
  simp only [PiLp.smul_apply, smul_eq_mul]
  by_cases hbasis : j = GatePointerEncoding.wordEquivFin r x ∧ b = flag
  · rcases hbasis with ⟨hj, hb⟩
    subst j
    subst b
    exact GateWalshHilbert.zeroReflection_word r (logicalBasis x flag) x flag
  · rw [GateWalshHilbert.zeroReflection_apply]
    simp only [logicalBasis_apply, if_neg hbasis, mul_zero]

/-- Exact basis intertwining with the released logical initial-state
reflection. -/
theorem zeroReflection_basis_intertwines (x : Word r) (flag : Bool) :
    rangeUnitary 1 (GateControlledCompare.zeroStateReflectionCircuit r)
        (logicalEmbedding r (logicalBasis x flag)) =
      logicalEmbedding r
        (GateUniformRange.stateReflection (GateWalshHilbert.cleanInput r)
          (logicalBasis x flag)) := by
  rw [logicalZeroReflection_basis, map_smul]
  exact zeroReflection_logicalBasis x flag

/-- Basis relabelling which makes the finite linear-extension step explicit. -/
def logicalWordLayout (r : ℕ) :
    EuclideanSpace ℂ (Word r × Bool) ≃ₗᵢ[ℂ]
      GateUniformRange.Space (2 ^ r) :=
  (LookupOracle.permutationUnitary
      (Equiv.prodCongr (GatePointerEncoding.wordEquivFin r) (Equiv.refl Bool))).trans
    (RegisterEquivalences.productFlatten (Fin (2 ^ r)) Bool).symm

theorem logicalWordLayout_single (r : ℕ) (x : Word r) (flag : Bool) :
    logicalWordLayout r (EuclideanSpace.single (x, flag) 1) =
      logicalBasis x flag := by
  classical
  change
    (RegisterEquivalences.productFlatten (Fin (2 ^ r)) Bool).symm
      (LookupOracle.permutationUnitary
        (Equiv.prodCongr (GatePointerEncoding.wordEquivFin r) (Equiv.refl Bool))
        (EuclideanSpace.single (x, flag) 1)) = logicalBasis x flag
  rw [LookupOracle.permutationUnitary_single]
  apply PiLp.ext
  intro j
  apply PiLp.ext
  intro b
  simp [RegisterEquivalences.productFlatten_symm_apply,
    logicalBasis_apply, PiLp.single_apply, Prod.ext_iff, eq_comm]

/-- Full operator intertwining for the successful-subspace reflection. -/
theorem acceptedCompare_intertwines (threshold r : ℕ) (h : threshold ≤ 2 ^ r) :
    rangeUnitary threshold (GateControlledCompare.acceptedCompareCircuit threshold r) ∘L
        (logicalEmbedding r).toContinuousLinearMap =
      (logicalEmbedding r).toContinuousLinearMap ∘L
        PhaseSubspaceGates.phase
          (GateUniformRange.goodProjection threshold (2 ^ r)) (-1) := by
  classical
  let L := (logicalWordLayout r).toLinearIsometry.toContinuousLinearMap
  have hflat :
      (rangeUnitary threshold
          (GateControlledCompare.acceptedCompareCircuit threshold r) ∘L
        (logicalEmbedding r).toContinuousLinearMap) ∘L L =
      ((logicalEmbedding r).toContinuousLinearMap ∘L
        PhaseSubspaceGates.phase
          (GateUniformRange.goodProjection threshold (2 ^ r)) (-1)) ∘L L := by
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Word r × Bool) ℂ).toBasis.ext
    intro i
    rcases i with ⟨x, flag⟩
    change
      rangeUnitary threshold
          (GateControlledCompare.acceptedCompareCircuit threshold r)
        (logicalEmbedding r
          (logicalWordLayout r
            ((EuclideanSpace.basisFun (Word r × Bool) ℂ) (x, flag)))) =
      logicalEmbedding r
        (PhaseSubspaceGates.phase
          (GateUniformRange.goodProjection threshold (2 ^ r)) (-1)
          (logicalWordLayout r
            ((EuclideanSpace.basisFun (Word r × Bool) ℂ) (x, flag))))
    rw [EuclideanSpace.basisFun_apply, logicalWordLayout_single]
    exact acceptedCompare_basis_intertwines threshold x flag h
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := (logicalWordLayout r).surjective v
  have hw := congrArg
    (fun F : EuclideanSpace ℂ (Word r × Bool) →L[ℂ] Physical r => F w) hflat
  simpa [comp_apply, L] using hw

/-- Full operator intertwining for the initial-state reflection. -/
theorem zeroReflection_intertwines (r : ℕ) :
    rangeUnitary 1 (GateControlledCompare.zeroStateReflectionCircuit r) ∘L
        (logicalEmbedding r).toContinuousLinearMap =
      (logicalEmbedding r).toContinuousLinearMap ∘L
        GateUniformRange.stateReflection (GateWalshHilbert.cleanInput r) := by
  classical
  let L := (logicalWordLayout r).toLinearIsometry.toContinuousLinearMap
  have hflat :
      (rangeUnitary 1 (GateControlledCompare.zeroStateReflectionCircuit r) ∘L
        (logicalEmbedding r).toContinuousLinearMap) ∘L L =
      ((logicalEmbedding r).toContinuousLinearMap ∘L
        GateUniformRange.stateReflection (GateWalshHilbert.cleanInput r)) ∘L L := by
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Word r × Bool) ℂ).toBasis.ext
    intro i
    rcases i with ⟨x, flag⟩
    change
      rangeUnitary 1 (GateControlledCompare.zeroStateReflectionCircuit r)
        (logicalEmbedding r
          (logicalWordLayout r
            ((EuclideanSpace.basisFun (Word r × Bool) ℂ) (x, flag)))) =
      logicalEmbedding r
        (GateUniformRange.stateReflection (GateWalshHilbert.cleanInput r)
          (logicalWordLayout r
            ((EuclideanSpace.basisFun (Word r × Bool) ℂ) (x, flag))))
    rw [EuclideanSpace.basisFun_apply, logicalWordLayout_single]
    exact zeroReflection_basis_intertwines x flag
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨w, rfl⟩ := (logicalWordLayout r).surjective v
  have hw := congrArg
    (fun F : EuclideanSpace ℂ (Word r × Bool) →L[ℂ] Physical r => F w) hflat
  simpa [comp_apply, L] using hw



/-! ### Clean computational transport of the full logical register -/

/-- Remove the reusable minus wire by its actual two-gate adjoint.  This
embedding has the same logical amplitudes as `logicalEmbedding`, with all
borrow wires and the marked wire now in their zero computational state. -/
def cleanLogicalEmbedding (r : ℕ) :
    GateUniformRange.Space (2 ^ r) →L[ℂ] Physical r :=
  (prepareMinus r)† ∘L (logicalEmbedding r).toContinuousLinearMap

theorem cleanLogicalEmbedding_norm (r : ℕ)
    (v : GateUniformRange.Space (2 ^ r)) :
    ‖cleanLogicalEmbedding r v‖ = ‖v‖ := by
  have hi : ((prepareMinus r)†)† ∘L (prepareMinus r)† = 1 := by
    rw [adjoint_adjoint]
    exact (prepareMinus_unitary r).2
  change ‖((prepareMinus r)†) (logicalEmbedding r v)‖ = ‖v‖
  rw [(norm_map_iff_adjoint_comp_self _).mpr hi, logicalEmbedding_norm]

/-- The literal two marked-wire preparation gates recover the normalised
kickback embedding for every logical superposition. -/
theorem prepareMinus_cleanLogicalEmbedding (r : ℕ)
    (v : GateUniformRange.Space (2 ^ r)) :
    prepareMinus r (cleanLogicalEmbedding r v) = logicalEmbedding r v := by
  have h := congrArg (fun F : Physical r →L[ℂ] Physical r =>
    F (logicalEmbedding r v)) (prepareMinus_unitary r).2
  exact h

/-- Coordinate formula showing that the adjoint restores a clean marked
wire on arbitrary logical inputs, not just on computational basis states. -/
theorem markedLayout_cleanLogicalEmbedding (r : ℕ)
    (v : GateUniformRange.Space (2 ^ r)) (p : Payload r) (b : Bool) :
    markedLayout r (cleanLogicalEmbedding r v) p b =
      (if p.borrow = cleanBorrow r
        then v (GatePointerEncoding.wordEquivFin r p.pointer) p.flag
        else 0) * ComplexAmplitudeRotation.clean b := by
  have hvec : markedLayout r (logicalEmbedding r v) p =
      (if p.borrow = cleanBorrow r
        then v (GatePointerEncoding.wordEquivFin r p.pointer) p.flag
        else 0) • minusQubit := by
    apply PiLp.ext
    intro c
    exact markedLayout_logicalEmbedding_apply r v p c
  change markedLayout r (((markedGate r minusPreparation)†)
    (logicalEmbedding r v)) p b = _
  rw [← markedGate_adjoint, markedGate_layout_apply, hvec, map_smul,
    minusPreparation_adjoint_minus]
  rfl

/-- No amplitude is left on a dirty comparator borrow register. -/
theorem cleanLogicalEmbedding_borrow_clean (r : ℕ)
    (v : GateUniformRange.Space (2 ^ r)) (p : Payload r) (b : Bool)
    (hp : p.borrow ≠ cleanBorrow r) :
    markedLayout r (cleanLogicalEmbedding r v) p b = 0 := by
  rw [markedLayout_cleanLogicalEmbedding]
  simp only [if_neg hp, zero_mul]

/-- No amplitude is left on the marked ancilla being one. -/
theorem cleanLogicalEmbedding_marked_clean (r : ℕ)
    (v : GateUniformRange.Space (2 ^ r)) (p : Payload r) :
    markedLayout r (cleanLogicalEmbedding r v) p true = 0 := by
  rw [markedLayout_cleanLogicalEmbedding]
  simp [ComplexAmplitudeRotation.clean]

theorem cleanLogicalEmbedding_basis (threshold : ℕ) (x : Word r) (flag : Bool) :
    cleanLogicalEmbedding r (logicalBasis x flag) =
      cleanComputational threshold flag x := by
  change ((prepareMinus r)†) (logicalEmbedding r (logicalBasis x flag)) = _
  rw [logicalEmbedding_basis threshold, prepareMinus_adjoint_normalized]

/-- The uniform-range target also resets its separate attenuation flag. -/
theorem cleanLogicalEmbedding_target_flag_clean (n r : ℕ) (p : Payload r)
    (b : Bool) (hp : p.flag = true) :
    markedLayout r (cleanLogicalEmbedding r (GateUniformRange.target n (2 ^ r)))
      p b = 0 := by
  rw [markedLayout_cleanLogicalEmbedding, hp]
  simp only [GateUniformRange.target_true, ite_self, zero_mul]

/-- Restoring the marked ancilla is valid with an arbitrary finite reference
register, including entangled logical inputs.  The reference is untouched. -/
theorem prepareMinus_cleanLogicalEmbedding_reference {R : Type*} [Fintype R]
    (r : ℕ) (v : PiLp 2 (fun _ : R => GateUniformRange.Space (2 ^ r))) :
    WeightedClock.diagonal (fun _ : R => prepareMinus r)
        (CoherentQuerySchedule.rectangular (fun _ : R => cleanLogicalEmbedding r) v) =
      CoherentQuerySchedule.rectangular
        (fun _ : R => (logicalEmbedding r).toContinuousLinearMap) v := by
  apply PiLp.ext
  intro j
  change prepareMinus r (cleanLogicalEmbedding r (v j)) =
    logicalEmbedding r (v j)
  exact prepareMinus_cleanLogicalEmbedding r (v j)

/-- The released logical input is the zero word with zero attenuation flag. -/
theorem cleanInput_eq_logicalBasis (r : ℕ) :
    GateWalshHilbert.cleanInput r =
      logicalBasis (GateWalshWords.zeroWord r) false := by
  apply PiLp.ext
  intro j
  apply PiLp.ext
  intro b
  change (if j = GatePointerEncoding.wordEquivFin r (GateWalshWords.zeroWord r)
    then ComplexAmplitudeRotation.clean else 0) b =
    if j = GatePointerEncoding.wordEquivFin r (GateWalshWords.zeroWord r) ∧ b = false
      then (1 : ℂ) else 0
  by_cases hj : j = GatePointerEncoding.wordEquivFin r (GateWalshWords.zeroWord r)
  · cases b <;> simp [hj, ComplexAmplitudeRotation.clean]
  · simp only [GatePointerEncoding.wordEquivFin_apply] at hj
    simp [hj]

/-- Initialisation is the ordinary all-zero computational configuration;
the clean logical embedding does not hide a state-preparation operation. -/
theorem cleanLogicalEmbedding_cleanInput (r : ℕ) :
    cleanLogicalEmbedding r (GateWalshHilbert.cleanInput r) =
      cleanComputational 0 false (GateWalshWords.zeroWord r) := by
  rw [cleanInput_eq_logicalBasis]
  exact cleanLogicalEmbedding_basis 0 (GateWalshWords.zeroWord r) false


/-! ### One elementary circuit for the complete uniform-range preparation

The helper `logicalLift`
is tensor extension, not an elementary instruction.  The instruction set
below permits it only for a literal one-bit Walsh gate or a one-bit
attenuation rotation.  Comparator and marked-wire instructions are the
existing bounded-arity instructions, with their actual lists retained.
-/

abbrev Spectators (r : ℕ) := BorrowRegister r × Bool

/-- Merely expose the two workspace factors: the borrow and marked wires,
and the original pointer and attenuation flag. -/
def workspaceSplit (r : ℕ) :
    Configuration r ≃ Spectators r × LogicalIndex r where
  toFun z := ((z.2.borrow, z.2.marked),
    (GatePointerEncoding.wordEquivFin r z.2.pointer, z.1))
  invFun z := (z.2.2, (⟨(GatePointerEncoding.wordEquivFin r).symm z.2.1,
    z.1.1, z.1.2⟩ : GateConstantCompare.Configuration r))
  left_inv z := by
    rcases z with ⟨flag, pointer, borrow, marked⟩
    change (flag, (⟨(GatePointerEncoding.wordEquivFin r).symm
      (GatePointerEncoding.wordEquivFin r pointer), borrow, marked⟩ :
        GateConstantCompare.Configuration r)) = _
    rw [Equiv.symm_apply_apply]
  right_inv z := by
    rcases z with ⟨⟨borrow, marked⟩, j, flag⟩
    change ((borrow, marked),
      (GatePointerEncoding.wordEquivFin r
        ((GatePointerEncoding.wordEquivFin r).symm j), flag)) = _
    rw [Equiv.apply_symm_apply]

def workspaceLayout (r : ℕ) : Physical r ≃ₗᵢ[ℂ]
    PiLp 2 (fun _ : Spectators r => EuclideanSpace ℂ (LogicalIndex r)) :=
  (LookupOracle.permutationUnitary (workspaceSplit r)).trans
    (RegisterEquivalences.productFlatten (Spectators r) (LogicalIndex r)).symm

@[simp] theorem workspaceLayout_apply (r : ℕ) (v : Physical r)
    (a : Spectators r) (i : LogicalIndex r) :
    workspaceLayout r v a i = v ((workspaceSplit r).symm (a, i)) := rfl

/-- The complete workspace factorisation of the previously proved clean
embedding; no new preparation assumption is introduced. -/
theorem workspaceLayout_logicalEmbedding (r : ℕ)
    (v : GateUniformRange.Space (2 ^ r)) (a : Spectators r) :
    workspaceLayout r (logicalEmbedding r v) a =
      (if a.1 = cleanBorrow r then minusQubit a.2 else 0) •
        RegisterEquivalences.productFlatten (Fin (2 ^ r)) Bool v := by
  apply PiLp.ext
  intro i
  have h := markedLayout_logicalEmbedding_apply r v
    (⟨i.2, (GatePointerEncoding.wordEquivFin r).symm i.1, a.1⟩ : Payload r) a.2
  change logicalEmbedding r v
    (i.2, ⟨(GatePointerEncoding.wordEquivFin r).symm i.1, a.1, a.2⟩) = _ at h
  change logicalEmbedding r v
    (i.2, ⟨(GatePointerEncoding.wordEquivFin r).symm i.1, a.1, a.2⟩) = _
  rw [h]
  simp only [Equiv.apply_symm_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases ha : a.1 = cleanBorrow r <;> simp [ha, mul_comm]; exact Or.inl rfl

/-- Semantic tensor extension, used only to describe identified local gates. -/
def logicalLift (r : ℕ)
    (U : GateUniformRange.Space (2 ^ r) →L[ℂ] GateUniformRange.Space (2 ^ r)) :
    Physical r →L[ℂ] Physical r :=
  (workspaceLayout r).symm.conjStarAlgEquiv
    (WeightedClock.diagonal (fun _ : Spectators r =>
      (RegisterEquivalences.productFlatten (Fin (2 ^ r)) Bool).conjStarAlgEquiv U))

theorem logicalLift_mul (r : ℕ)
    (U V : GateUniformRange.Space (2 ^ r) →L[ℂ] GateUniformRange.Space (2 ^ r)) :
    logicalLift r (U * V) = logicalLift r U * logicalLift r V := by
  have h : WeightedClock.diagonal (fun _ : Spectators r =>
        (RegisterEquivalences.productFlatten (Fin (2 ^ r)) Bool).conjStarAlgEquiv (U * V)) =
      WeightedClock.diagonal (fun _ : Spectators r =>
        (RegisterEquivalences.productFlatten (Fin (2 ^ r)) Bool).conjStarAlgEquiv U) *
      WeightedClock.diagonal (fun _ : Spectators r =>
        (RegisterEquivalences.productFlatten (Fin (2 ^ r)) Bool).conjStarAlgEquiv V) := by
    rw [diagonal_mul', map_mul]
  unfold logicalLift
  rw [h, map_mul]

@[simp] theorem logicalLift_one (r : ℕ) : logicalLift r 1 = 1 := by
  simp [logicalLift, WeightedClock.diagonal_one]

theorem logicalLift_adjoint (r : ℕ)
    (U : GateUniformRange.Space (2 ^ r) →L[ℂ] GateUniformRange.Space (2 ^ r)) :
    logicalLift r (U†) = (logicalLift r U)† := by
  unfold logicalLift
  change _ = star _
  rw [← map_star, diagonal_star']
  congr 2
  funext a
  exact map_star _ U

/-- Every tensor-extended operation acts coherently on the original logical
register and leaves the clean borrow/minus workspace exactly unchanged. -/
theorem logicalLift_intertwines_apply (r : ℕ)
    (U : GateUniformRange.Space (2 ^ r) →L[ℂ] GateUniformRange.Space (2 ^ r))
    (v : GateUniformRange.Space (2 ^ r)) :
    logicalLift r U (logicalEmbedding r v) = logicalEmbedding r (U v) := by
  apply (workspaceLayout r).injective
  apply PiLp.ext
  intro a
  rw [logicalLift, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  simp only [LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.apply_symm_apply, WeightedClock.diagonal_apply]
  rw [workspaceLayout_logicalEmbedding, map_smul,
    workspaceLayout_logicalEmbedding]
  congr 1
  try rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]

/-- Tensor extension preserves multiplication and the adjoint on the whole
workspace, including inputs with nonzero borrow wires. -/
theorem logicalLift_unitary (r : ℕ)
    (U : GateUniformRange.Space (2 ^ r) →L[ℂ] GateUniformRange.Space (2 ^ r))
    (hU : IsUnitary U) : IsUnitary (logicalLift r U) := by
  constructor
  · change (logicalLift r U)† * logicalLift r U = 1
    rw [← logicalLift_adjoint, ← logicalLift_mul]
    change logicalLift r (star U * U) = 1
    rw [hU.1, logicalLift_one]
  · change logicalLift r U * (logicalLift r U)† = 1
    rw [← logicalLift_adjoint, ← logicalLift_mul]
    change logicalLift r (U * star U) = 1
    rw [hU.2, logicalLift_one]

/-- Extend one *literal* signed word-bit rotation with the flag untouched. -/
def logicalWordGate {r : ℕ} (g : GateWalshInverse.Gate r) :
    GateUniformRange.Space (2 ^ r) →L[ℂ] GateUniformRange.Space (2 ^ r) :=
  (GateWalshHilbert.flagLayout r).symm.conjStarAlgEquiv
    (WeightedClock.diagonal (fun _ : Bool =>
      (GateWalshHilbert.wordRelabel r).conjStarAlgEquiv
        (GateWalshHilbert.signedGate g)))

/-- The helper is exactly the original one-bit matrix action, not an
arbitrary operation on the word register. -/
theorem logicalWordGate_apply {r : ℕ} (g : GateWalshInverse.Gate r)
    (v : GateUniformRange.Space (2 ^ r)) (x : Word r) (flag : Bool) :
    logicalWordGate g v (GatePointerEncoding.wordEquivFin r x) flag =
      g.eval (fun y => v (GatePointerEncoding.wordEquivFin r y) flag) x := by
  change GateWalshHilbert.signedGate g
    ((GateWalshHilbert.wordRelabel r).symm
      (GateWalshHilbert.flagLayout r v flag))
      ((GatePointerEncoding.wordEquivFin r).symm
        (GatePointerEncoding.wordEquivFin r x)) = _
  rw [Equiv.symm_apply_apply, GateWalshHilbert.signedGate_apply]
  simp only [GateWalshHilbert.wordRelabel_symm_apply, GateWalshHilbert.flagLayout_apply]

def logicalWordRun {r : ℕ} : List (GateWalshInverse.Gate r) →
    GateUniformRange.Space (2 ^ r) →L[ℂ] GateUniformRange.Space (2 ^ r)
  | [] => 1
  | g :: gs => logicalWordRun gs * logicalWordGate g

theorem logicalWordRun_apply {r : ℕ} (gs : List (GateWalshInverse.Gate r))
    (v : GateUniformRange.Space (2 ^ r)) (x : Word r) (flag : Bool) :
    logicalWordRun gs v (GatePointerEncoding.wordEquivFin r x) flag =
      GateWalshInverse.run gs
        (fun y => v (GatePointerEncoding.wordEquivFin r y) flag) x := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
      change logicalWordRun gs (logicalWordGate g v)
        (GatePointerEncoding.wordEquivFin r x) flag = _
      rw [ih]
      have h : (fun y => logicalWordGate g v
          (GatePointerEncoding.wordEquivFin r y) flag) =
          g.eval (fun y => v (GatePointerEncoding.wordEquivFin r y) flag) := by
        funext y
        exact logicalWordGate_apply g v y flag
      rw [h]
      rfl

theorem logicalWordRun_forward (r : ℕ) :
    logicalWordRun (GateWalshInverse.circuit r) = GateWalshHilbert.uniformWords r := by
  ext v j flag
  obtain ⟨x, rfl⟩ := (GatePointerEncoding.wordEquivFin r).surjective j
  rw [logicalWordRun_apply, GateWalshHilbert.uniformWords_apply]
  rw [Equiv.symm_apply_apply]
  simp only [GateWalshInverse.circuit, GateWalshInverse.run_forward]

/-- A whole-space map identity for signed word circuits, used to identify
literal reversal with the Hilbert adjoint. -/
theorem logicalWordRun_eq (r : ℕ) (gs : List (GateWalshInverse.Gate r)) :
    logicalWordRun gs =
      (GateWalshHilbert.flagLayout r).symm.conjStarAlgEquiv
        (WeightedClock.diagonal (fun _ : Bool =>
          (GateWalshHilbert.wordRelabel r).conjStarAlgEquiv
            (GateWalshHilbert.signedRun gs))) := by
  induction gs with
  | nil => simp [logicalWordRun, GateWalshHilbert.signedRun,
      WeightedClock.diagonal_one]
  | cons g gs ih =>
      rw [logicalWordRun, ih, GateWalshHilbert.signedRun, map_mul]
      unfold logicalWordGate
      rw [← map_mul, diagonal_mul']

theorem logicalWordRun_inverse (r : ℕ) :
    logicalWordRun (GateWalshInverse.inverseCircuit r) =
      (GateWalshHilbert.uniformWords r)† := by
  rw [logicalWordRun_eq, GateWalshHilbert.signedRun_inverseCircuit]
  change _ = star (GateWalshHilbert.uniformWords r)
  rw [GateWalshHilbert.uniformWords, ← map_star, diagonal_star']
  congr 1
  apply congrArg WeightedClock.diagonal
  funext flag
  exact map_star _ _

/-- Tensor extension acts independently in each spectator slice.  The
layout is a coordinate convention, not a charged gate. -/
theorem workspaceLayout_logicalLift (r : ℕ)
    (U : GateUniformRange.Space (2 ^ r) →L[ℂ] GateUniformRange.Space (2 ^ r))
    (v : Physical r) (a : Spectators r) :
    workspaceLayout r (logicalLift r U v) a =
      RegisterEquivalences.productFlatten (Fin (2 ^ r)) Bool
        (U ((RegisterEquivalences.productFlatten (Fin (2 ^ r)) Bool).symm
          (workspaceLayout r v a))) := by
  rw [logicalLift, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  simp only [LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.apply_symm_apply, WeightedClock.diagonal_apply]
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

/-- Literal coordinate action on the original physical pointer wires.
Every other wire is a spectator.  `g.eval` was already proved to be a
single chosen one-bit matrix, for both forward and inverse orientations. -/
theorem physicalWordGate_apply {r : ℕ} (g : GateWalshInverse.Gate r)
    (v : Physical r) (flag : Bool) (x : Word r)
    (borrow : BorrowRegister r) (marked : Bool) :
    logicalLift r (logicalWordGate g) v (flag, ⟨x, borrow, marked⟩) =
      g.eval (fun y => v (flag, ⟨y, borrow, marked⟩)) x := by
  let V := (RegisterEquivalences.productFlatten (Fin (2 ^ r)) Bool).symm
    (workspaceLayout r v (borrow, marked))
  have h := congrArg
    (fun f : EuclideanSpace ℂ (LogicalIndex r) =>
      f (GatePointerEncoding.wordEquivFin r x, flag))
    (workspaceLayout_logicalLift r (logicalWordGate g) v (borrow, marked))
  change logicalLift r (logicalWordGate g) v
    (flag, ⟨(GatePointerEncoding.wordEquivFin r).symm
      (GatePointerEncoding.wordEquivFin r x), borrow, marked⟩) =
      logicalWordGate g V (GatePointerEncoding.wordEquivFin r x) flag at h
  rw [Equiv.symm_apply_apply, logicalWordGate_apply] at h
  rw [h]
  have hs : (fun y => V (GatePointerEncoding.wordEquivFin r y) flag) =
      fun y => v (flag, ⟨y, borrow, marked⟩) := by
    funext y
    change v (flag, ⟨(GatePointerEncoding.wordEquivFin r).symm
      (GatePointerEncoding.wordEquivFin r y), borrow, marked⟩) = _
    rw [Equiv.symm_apply_apply]
  rw [hs]

/-- The attenuation instruction acts only on the original flag wire;
the pointer and every workspace bit remain fixed. -/
theorem physicalAttenuation_apply (n r : ℕ)
    (v : Physical r) (flag : Bool) (x : Word r)
    (borrow : BorrowRegister r) (marked : Bool) :
    logicalLift r (GateUniformRange.attenuationGate n (2 ^ r)) v
      (flag, ⟨x, borrow, marked⟩) =
      ComplexAmplitudeRotation.rotation
        (GateUniformRange.attenuation n (2 ^ r) : ℂ)
        (WithLp.toLp 2 (fun b : Bool => v (b, ⟨x, borrow, marked⟩))) flag := by
  let V := (RegisterEquivalences.productFlatten (Fin (2 ^ r)) Bool).symm
    (workspaceLayout r v (borrow, marked))
  have h := congrArg
    (fun f : EuclideanSpace ℂ (LogicalIndex r) =>
      f (GatePointerEncoding.wordEquivFin r x, flag))
    (workspaceLayout_logicalLift r
      (GateUniformRange.attenuationGate n (2 ^ r)) v (borrow, marked))
  change logicalLift r (GateUniformRange.attenuationGate n (2 ^ r)) v
    (flag, ⟨(GatePointerEncoding.wordEquivFin r).symm
      (GatePointerEncoding.wordEquivFin r x), borrow, marked⟩) =
      GateUniformRange.attenuationGate n (2 ^ r) V
        (GatePointerEncoding.wordEquivFin r x) flag at h
  rw [Equiv.symm_apply_apply] at h
  rw [h]
  have hs : V (GatePointerEncoding.wordEquivFin r x) =
      WithLp.toLp 2 (fun b : Bool => v (b, ⟨x, borrow, marked⟩)) := by
    apply PiLp.ext
    intro b
    change v (b, ⟨(GatePointerEncoding.wordEquivFin r).symm
      (GatePointerEncoding.wordEquivFin r x), borrow, marked⟩) = _
    rw [Equiv.symm_apply_apply]
  change ComplexAmplitudeRotation.rotation
    (GateUniformRange.attenuation n (2 ^ r) : ℂ)
    (V (GatePointerEncoding.wordEquivFin r x)) flag = _
  rw [hs]

/-- The reverse attenuation is the literal adjoint one-qubit matrix on
the same wire. -/
theorem physicalAttenuation_adjoint_apply (n r : ℕ)
    (v : Physical r) (flag : Bool) (x : Word r)
    (borrow : BorrowRegister r) (marked : Bool) :
    logicalLift r ((GateUniformRange.attenuationGate n (2 ^ r))†) v
      (flag, ⟨x, borrow, marked⟩) =
      ((ComplexAmplitudeRotation.rotation
        (GateUniformRange.attenuation n (2 ^ r) : ℂ))†)
        (WithLp.toLp 2 (fun b : Bool => v (b, ⟨x, borrow, marked⟩))) flag := by
  let V := (RegisterEquivalences.productFlatten (Fin (2 ^ r)) Bool).symm
    (workspaceLayout r v (borrow, marked))
  have h := congrArg
    (fun f : EuclideanSpace ℂ (LogicalIndex r) =>
      f (GatePointerEncoding.wordEquivFin r x, flag))
    (workspaceLayout_logicalLift r
      ((GateUniformRange.attenuationGate n (2 ^ r))†) v (borrow, marked))
  change logicalLift r ((GateUniformRange.attenuationGate n (2 ^ r))†) v
    (flag, ⟨(GatePointerEncoding.wordEquivFin r).symm
      (GatePointerEncoding.wordEquivFin r x), borrow, marked⟩) =
      ((GateUniformRange.attenuationGate n (2 ^ r))†) V
        (GatePointerEncoding.wordEquivFin r x) flag at h
  rw [Equiv.symm_apply_apply] at h
  rw [h, GateUniformRange.attenuationGate, WeightedClock.diagonal_adjoint]
  have hs : V (GatePointerEncoding.wordEquivFin r x) =
      WithLp.toLp 2 (fun b : Bool => v (b, ⟨x, borrow, marked⟩)) := by
    apply PiLp.ext
    intro b
    change v (b, ⟨(GatePointerEncoding.wordEquivFin r).symm
      (GatePointerEncoding.wordEquivFin r x), borrow, marked⟩) = _
    rw [Equiv.symm_apply_apply]
  rw [WeightedClock.diagonal_apply, hs]

/-- Full physical instruction set for fixed-range preparation.  The only
rotation instructions are the identified one-bit word, flag and marked-wire
rotations.  There is no arbitrary-unitary instruction. -/
inductive PreparationGate (r : ℕ)
  | word (g : GateWalshInverse.Gate r)
  | attenuation (n : ℕ) (inverse : Bool)
  | compare (threshold : ℕ) (g : GateControlledCompare.RangeGate r)
  | marked (g : MarkedWireGate)

def PreparationGate.arity : PreparationGate r → ℕ
  | .word _ => 1
  | .attenuation _ _ => 1
  | .compare _ g => g.arity
  | .marked g => g.arity

def PreparationGate.eval : PreparationGate r → Physical r →L[ℂ] Physical r
  | .word g => logicalLift r (logicalWordGate g)
  | .attenuation n false => logicalLift r (GateUniformRange.attenuationGate n (2 ^ r))
  | .attenuation n true => logicalLift r ((GateUniformRange.attenuationGate n (2 ^ r))†)
  | .compare threshold g => rangeUnitary threshold [g]
  | .marked g => markedGate r g.eval

theorem PreparationGate.arity_le_three (g : PreparationGate r) : g.arity ≤ 3 := by
  cases g with
  | word _ => simp [PreparationGate.arity]
  | attenuation _ _ => simp [PreparationGate.arity]
  | compare _ g => exact GateControlledCompare.RangeGate.arity_le_three g
  | marked g => rw [PreparationGate.arity, MarkedWireGate.arity_eq_one]; omega

def preparationRun : List (PreparationGate r) → Physical r →L[ℂ] Physical r
  | [] => 1
  | g :: gs => preparationRun gs * g.eval

theorem preparationRun_append (gs hs : List (PreparationGate r)) :
    preparationRun (gs ++ hs) = preparationRun hs * preparationRun gs := by
  induction gs with
  | nil => simp [preparationRun]
  | cons g gs ih => simp [preparationRun, ih, mul_assoc]

theorem preparationRun_words (gs : List (GateWalshInverse.Gate r)) :
    preparationRun (gs.map PreparationGate.word) = logicalLift r (logicalWordRun gs) := by
  induction gs with
  | nil => simp [preparationRun, logicalWordRun]
  | cons g gs ih => simp [preparationRun, logicalWordRun,
      PreparationGate.eval, ih, logicalLift_mul]

theorem preparationRun_marked (gs : List MarkedWireGate) :
    preparationRun (gs.map (PreparationGate.marked (r := r))) = physicalMarkedRun r gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [preparationRun, physicalMarkedRun, PreparationGate.eval, ih]

/-- Splitting a literal comparator list into instructions preserves its
full-space basis-permutation semantics. -/
theorem preparationRun_compare (threshold : ℕ)
    (gs : List (GateControlledCompare.RangeGate r)) :
    preparationRun (gs.map (PreparationGate.compare threshold)) =
      rangeUnitary threshold gs := by
  induction gs with
  | nil =>
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Configuration r) ℂ).toBasis.ext
      intro z
      simp [EuclideanSpace.basisFun_apply, preparationRun,
        rangeUnitary_single, GateControlledCompare.rangeExec,
        ]
  | cons g gs ih =>
      rw [List.map_cons, preparationRun, ih]
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Configuration r) ℂ).toBasis.ext
      intro z
      simp [EuclideanSpace.basisFun_apply, PreparationGate.eval,
        rangeUnitary_single, GateControlledCompare.rangeExec,
        ]

/-- A forward attenuated word preparation consists of exactly `r+1` local
rotations. -/
def attenuatedPreparationCircuit (n r : ℕ) : List (PreparationGate r) :=
  (GateWalshInverse.circuit r).map PreparationGate.word ++ [.attenuation n false]

/-- Actual reverse word list and inverse one-qubit attenuation rotation. -/
def attenuatedUnpreparationCircuit (n r : ℕ) : List (PreparationGate r) :=
  [.attenuation n true] ++
    (GateWalshInverse.inverseCircuit r).map PreparationGate.word

theorem attenuatedPreparationCircuit_eval (n r : ℕ) :
    preparationRun (attenuatedPreparationCircuit n r) =
      logicalLift r (GateUniformRange.prepare n (2 ^ r) (GateWalshHilbert.uniformWords r)) := by
  rw [attenuatedPreparationCircuit, preparationRun_append, preparationRun_words,
    logicalWordRun_forward]
  simp only [preparationRun, one_mul, PreparationGate.eval]
  rw [← logicalLift_mul]
  rfl

theorem attenuatedUnpreparationCircuit_eval (n r : ℕ) :
    preparationRun (attenuatedUnpreparationCircuit n r) =
      (logicalLift r (GateUniformRange.prepare n (2 ^ r)
        (GateWalshHilbert.uniformWords r)))† := by
  rw [attenuatedUnpreparationCircuit, preparationRun_append, preparationRun_words,
    logicalWordRun_inverse]
  simp only [preparationRun, one_mul, PreparationGate.eval]
  rw [← logicalLift_mul, ← logicalLift_adjoint]
  congr 1
  change star (GateWalshHilbert.uniformWords r) *
    star (GateUniformRange.attenuationGate n (2 ^ r)) =
      star (GateUniformRange.attenuationGate n (2 ^ r) * GateWalshHilbert.uniformWords r)
  rw [star_mul]

/-- The entire chronological fixed-range preparation, including both
operations on the marked ancilla.  This is one list on one workspace. -/
def physicalRangeCircuit (n r : ℕ) : List (PreparationGate r) :=
  minusPreparationCircuit.map PreparationGate.marked ++
  attenuatedPreparationCircuit n r ++
  (GateControlledCompare.acceptedCompareCircuit n r).map (PreparationGate.compare n) ++
  attenuatedUnpreparationCircuit n r ++
  (GateControlledCompare.zeroStateReflectionCircuit r).map (PreparationGate.compare 1) ++
  attenuatedPreparationCircuit n r ++
  minusUnpreparationCircuit.map PreparationGate.marked

theorem attenuatedPreparationCircuit_length (n r : ℕ) :
    (attenuatedPreparationCircuit n r).length = r + 1 := by
  simp [attenuatedPreparationCircuit, GateWalshInverse.circuit_length]

theorem attenuatedUnpreparationCircuit_length (n r : ℕ) :
    (attenuatedUnpreparationCircuit n r).length = r + 1 := by
  simp [attenuatedUnpreparationCircuit, GateWalshInverse.inverseCircuit_length]

/-- Unlike the earlier component arithmetic, this counts an actual single
list of elementary instructions with a defined whole-register semantics. -/
theorem physicalRangeCircuit_length (n r : ℕ) :
    (physicalRangeCircuit n r).length = rangePreparationKnownGates n r := by
  simp [physicalRangeCircuit, rangePreparationKnownGates,
    attenuatedPreparationCircuit_length, attenuatedUnpreparationCircuit_length,
    GateWalshWords.circuit_length]
  omega

theorem physicalRangeCircuit_length_le (n r : ℕ) :
    (physicalRangeCircuit n r).length ≤ 7 * r + 14 := by
  rw [physicalRangeCircuit_length]
  exact rangePreparationKnownGates_le n r

theorem physicalRangeCircuit_arity (n r : ℕ)
    (g : PreparationGate r) (_hg : g ∈ physicalRangeCircuit n r) : g.arity ≤ 3 :=
  g.arity_le_three

/-- Complete physical range preparation: both types of workspace flags
return clean, with exact target amplitudes and no success postselection. -/
theorem physicalRangeCircuit_prepares (n r : ℕ) (hn : 0 < n)
    (hnN : n ≤ 2 ^ r) (hN : 2 ^ r ≤ 4 * n) :
    preparationRun (physicalRangeCircuit n r)
      (cleanLogicalEmbedding r (GateWalshHilbert.cleanInput r)) =
      cleanLogicalEmbedding r (GateUniformRange.target n (2 ^ r)) := by
  let U := GateUniformRange.prepare n (2 ^ r) (GateWalshHilbert.uniformWords r)
  have hg (v : GateUniformRange.Space (2 ^ r)) := congrArg
    (fun F : GateUniformRange.Space (2 ^ r) →L[ℂ] Physical r => F v)
    (acceptedCompare_intertwines n r hnN)
  have hz (v : GateUniformRange.Space (2 ^ r)) := congrArg
    (fun F : GateUniformRange.Space (2 ^ r) →L[ℂ] Physical r => F v)
    (zeroReflection_intertwines r)
  simp only [comp_apply, LinearIsometry.coe_toContinuousLinearMap] at hg hz
  rw [physicalRangeCircuit]
  simp only [preparationRun_append, preparationRun_marked,
    preparationRun_compare, physicalMinusPreparationCircuit_eval,
    physicalMinusUnpreparationCircuit_eval,
    attenuatedPreparationCircuit_eval, attenuatedUnpreparationCircuit_eval,
    mul_apply_eq_comp]
  rw [prepareMinus_cleanLogicalEmbedding,
    logicalLift_intertwines_apply, hg, ← logicalLift_adjoint,
    logicalLift_intertwines_apply, hz, logicalLift_intertwines_apply]
  have ht := GateUniformRange.prepare_reflect_inverse_reflect_prepare
    n (2 ^ r) hn hnN hN U
    (GateUniformRange.prepare_unitary n (2 ^ r) hn hN
      (GateWalshHilbert.uniformWords r) (GateWalshHilbert.uniformWords_unitary r))
    (GateWalshHilbert.cleanInput r)
    (GateUniformRange.prepare_apply n (2 ^ r) (GateWalshHilbert.uniformWords r)
      (GateWalshHilbert.cleanInput r) (GateWalshHilbert.uniformWords_prepares r))
  change U (GateUniformRange.stateReflection (GateWalshHilbert.cleanInput r)
    ((U†) (PhaseSubspaceGates.phase (GateUniformRange.goodProjection n (2 ^ r)) (-1)
      (U (GateWalshHilbert.cleanInput r))))) = GateUniformRange.target n (2 ^ r) at ht
  change ((prepareMinus r)†) (logicalEmbedding r
    (U (GateUniformRange.stateReflection (GateWalshHilbert.cleanInput r)
      ((U†) (PhaseSubspaceGates.phase (GateUniformRange.goodProjection n (2 ^ r)) (-1)
        (U (GateWalshHilbert.cleanInput r))))))) = _
  rw [ht]
  rfl


/-! ### Valid elementary gates and the literal inverse range circuit -/

/-- A flag rotation is an elementary unitary only in its stated parameter
range.  All other constructors already name unconditional unitary gates. -/
def PreparationGate.Valid : PreparationGate r → Prop
  | .attenuation n _ => 0 < n ∧ 2 ^ r ≤ 4 * n
  | _ => True

/-- Signed word gates are the previously proved one-bit unitary and its
actual Hilbert adjoint, with unchanged flag and workspace wires. -/
theorem logicalWordGate_unitary (g : GateWalshInverse.Gate r) :
    IsUnitary (logicalWordGate g) := by
  have hg : IsUnitary (GateWalshHilbert.signedGate g) := by
    cases g with
    | forward j => exact GateWalshHilbert.gate_unitary j
    | backward j => exact (GateWalshHilbert.gate_unitary j).adjoint
  exact (CoherentQuerySchedule.diagonal_unitary
    (fun _ : Bool => (GateWalshHilbert.wordRelabel r).conjStarAlgEquiv
      (GateWalshHilbert.signedGate g))
    (fun _ => hg.transport (GateWalshHilbert.wordRelabel r))).transport
      (GateWalshHilbert.flagLayout r).symm

theorem MarkedWireGate.eval_unitary (g : MarkedWireGate) : IsUnitary g.eval := by
  cases g with
  | walsh => exact GateWalshHilbert.localRotation_unitary
  | walshAdjoint => exact GateWalshHilbert.localRotation_unitary.adjoint
  | phase => exact minusPhase_unitary

/-- The validity test supplies the only parameter restriction needed for
unitarity of every actual instruction in this syntax. -/
theorem PreparationGate.eval_unitary (g : PreparationGate r) (hg : g.Valid) :
    IsUnitary g.eval := by
  cases g with
  | word g => exact logicalLift_unitary r _ (logicalWordGate_unitary g)
  | attenuation n inverse =>
      have hn : 0 < n := hg.1
      have hN : 2 ^ r ≤ 4 * n := hg.2
      cases inverse with
      | false =>
          exact logicalLift_unitary r _
            (GateUniformRange.attenuationGate_unitary n (2 ^ r) hn hN)
      | true =>
          exact logicalLift_unitary r _
            (GateUniformRange.attenuationGate_unitary n (2 ^ r) hn hN).adjoint
  | compare threshold g => exact rangeUnitary_unitary threshold [g]
  | marked g => exact markedGate_unitary r _ g.eval_unitary

theorem preparationRun_unitary (gs : List (PreparationGate r))
    (hgs : ∀ g ∈ gs, g.Valid) : IsUnitary (preparationRun gs) := by
  revert hgs
  induction gs with
  | nil =>
      intro _
      exact isUnitary_one
  | cons g gs ih =>
      intro hgs
      have hg : g.Valid := hgs g (by simp)
      have ht : ∀ q ∈ gs, q.Valid := by
        intro q hq
        exact hgs q (by simp [hq])
      exact (ih ht).mul (g.eval_unitary hg)

theorem preparationWords_valid (gs : List (GateWalshInverse.Gate r)) :
    ∀ g ∈ gs.map PreparationGate.word, g.Valid := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  trivial

theorem preparationMarked_valid (gs : List MarkedWireGate) :
    ∀ g ∈ gs.map (PreparationGate.marked (r := r)), g.Valid := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  trivial

theorem preparationCompare_valid (threshold : ℕ)
    (gs : List (GateControlledCompare.RangeGate r)) :
    ∀ g ∈ gs.map (PreparationGate.compare threshold), g.Valid := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  trivial

theorem attenuatedPreparationCircuit_valid (n r : ℕ) (hn : 0 < n)
    (hN : 2 ^ r ≤ 4 * n) :
    ∀ g ∈ attenuatedPreparationCircuit n r, g.Valid := by
  intro g hg
  rcases List.mem_append.mp hg with hw | ha
  · exact preparationWords_valid _ g hw
  · have he : g = PreparationGate.attenuation n false := by simpa using ha
    subst g
    exact ⟨hn, hN⟩

theorem attenuatedUnpreparationCircuit_valid (n r : ℕ) (hn : 0 < n)
    (hN : 2 ^ r ≤ 4 * n) :
    ∀ g ∈ attenuatedUnpreparationCircuit n r, g.Valid := by
  intro g hg
  rcases List.mem_append.mp hg with ha | hw
  · have he : g = PreparationGate.attenuation n true := by simpa using ha
    subst g
    exact ⟨hn, hN⟩
  · exact preparationWords_valid _ g hw

/-- Every instruction in the charged physical range list is a genuine
unitary of its declared bounded arity under the range promises. -/
theorem physicalRangeCircuit_valid (n r : ℕ) (hn : 0 < n)
    (hN : 2 ^ r ≤ 4 * n) :
    ∀ g ∈ physicalRangeCircuit n r, g.Valid := by
  simp only [physicalRangeCircuit, List.mem_append, or_imp, forall_and]
  repeat' constructor
  all_goals first
    | exact preparationMarked_valid _
    | exact attenuatedPreparationCircuit_valid n r hn hN
    | exact attenuatedUnpreparationCircuit_valid n r hn hN
    | exact preparationCompare_valid _ _

/-- Full-space unitarity, rather than only correctness on the clean input. -/
theorem physicalRangeCircuit_unitary (n r : ℕ) (hn : 0 < n)
    (hN : 2 ^ r ≤ 4 * n) :
    IsUnitary (preparationRun (physicalRangeCircuit n r)) :=
  preparationRun_unitary _ (physicalRangeCircuit_valid n r hn hN)

/-- Reversing the comparator's literal involutive gate list gives its
Hilbert adjoint, including arbitrary dirty workspaces. -/
theorem rangeUnitary_reverse (threshold : ℕ)
    (gs : List (GateControlledCompare.RangeGate r)) :
    rangeUnitary threshold gs.reverse = (rangeUnitary threshold gs)† := by
  have hleft : rangeUnitary threshold gs.reverse * rangeUnitary threshold gs = 1 := by
    apply ContinuousLinearMap.coe_injective
    apply (EuclideanSpace.basisFun (Configuration r) ℂ).toBasis.ext
    intro z
    change (rangeUnitary threshold gs.reverse * rangeUnitary threshold gs)
        ((EuclideanSpace.basisFun (Configuration r) ℂ) z) =
      (1 : Physical r →L[ℂ] Physical r)
        ((EuclideanSpace.basisFun (Configuration r) ℂ) z)
    rw [EuclideanSpace.basisFun_apply]
    change rangeUnitary threshold gs.reverse
      (rangeUnitary threshold gs (EuclideanSpace.single z 1)) =
        EuclideanSpace.single z 1
    rw [rangeUnitary_single, rangeUnitary_single,
      GateControlledCompare.rangeExec_reverse_exec]
  have hright : rangeUnitary threshold gs * (rangeUnitary threshold gs)† = 1 :=
    (rangeUnitary_unitary threshold gs).2
  calc
    rangeUnitary threshold gs.reverse = rangeUnitary threshold gs.reverse *
        (rangeUnitary threshold gs * (rangeUnitary threshold gs)†) := by
      rw [hright, mul_one]
    _ = (rangeUnitary threshold gs.reverse * rangeUnitary threshold gs) *
        (rangeUnitary threshold gs)† := (mul_assoc _ _ _).symm
    _ = (rangeUnitary threshold gs)† := by rw [hleft, one_mul]

/-- Reversing the signed one-bit instruction is exactly its Hilbert
adjoint after the same flag and word register layouts. -/
theorem logicalWordGate_inverse (g : GateWalshInverse.Gate r) :
    logicalWordGate g.inverse = (logicalWordGate g)† := by
  unfold logicalWordGate
  rw [GateWalshHilbert.signedGate_inverse]
  have hinner : (GateWalshHilbert.wordRelabel r).conjStarAlgEquiv
      ((GateWalshHilbert.signedGate g)†) =
      ((GateWalshHilbert.wordRelabel r).conjStarAlgEquiv
        (GateWalshHilbert.signedGate g))† :=
    map_star (GateWalshHilbert.wordRelabel r).conjStarAlgEquiv _
  simp_rw [hinner]
  rw [← WeightedClock.diagonal_adjoint
    (fun _ : Bool => (GateWalshHilbert.wordRelabel r).conjStarAlgEquiv
      (GateWalshHilbert.signedGate g))]
  exact map_star (GateWalshHilbert.flagLayout r).symm.conjStarAlgEquiv _

/-- Inverse syntax keeps the same physical wires.  Comparator instructions
are involutions, so their inverse is the same single instruction. -/
def PreparationGate.inverse : PreparationGate r → PreparationGate r
  | .word g => .word g.inverse
  | .attenuation n inverse => .attenuation n (!inverse)
  | .compare threshold g => .compare threshold g
  | .marked g => .marked g.inverse

@[simp] theorem PreparationGate.inverse_inverse (g : PreparationGate r) :
    g.inverse.inverse = g := by
  cases g <;> simp [PreparationGate.inverse]

theorem PreparationGate.inverse_valid (g : PreparationGate r) (hg : g.Valid) :
    g.inverse.Valid := by
  cases g <;> exact hg

@[simp] theorem PreparationGate.inverse_arity (g : PreparationGate r) :
    g.inverse.arity = g.arity := by
  cases g with
  | word g => rfl
  | attenuation n inverse => rfl
  | compare threshold g => rfl
  | marked g => simp [PreparationGate.inverse, PreparationGate.arity,
      MarkedWireGate.arity_eq_one]

/-- The syntactic inverse is the actual adjoint of the instruction, not a
separately supplied inverse implementation. -/
theorem PreparationGate.eval_inverse (g : PreparationGate r) :
    g.inverse.eval = g.eval† := by
  cases g with
  | word g =>
      simp only [PreparationGate.inverse, PreparationGate.eval,
        logicalWordGate_inverse, logicalLift_adjoint]
  | attenuation n inverse =>
      cases inverse <;>
        simp [PreparationGate.inverse, PreparationGate.eval, logicalLift_adjoint]
  | compare threshold g =>
      change rangeUnitary threshold [g] = (rangeUnitary threshold [g])†
      simpa using rangeUnitary_reverse threshold [g]
  | marked g =>
      simp only [PreparationGate.inverse, PreparationGate.eval,
        MarkedWireGate.eval_inverse, markedGate_adjoint]

/-- Reverse the real instruction list and invert each elementary gate. -/
def preparationInverse (gs : List (PreparationGate r)) : List (PreparationGate r) :=
  gs.reverse.map PreparationGate.inverse

@[simp] theorem preparationInverse_length (gs : List (PreparationGate r)) :
    (preparationInverse gs).length = gs.length := by
  simp [preparationInverse]

theorem preparationInverse_valid (gs : List (PreparationGate r))
    (hgs : ∀ g ∈ gs, g.Valid) : ∀ g ∈ preparationInverse gs, g.Valid := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  exact q.inverse_valid (hgs q (by simpa using hq))

/-- Exact full-space adjoint semantics of the reversed elementary list. -/
theorem preparationInverse_eval (gs : List (PreparationGate r)) :
    preparationRun (preparationInverse gs) = (preparationRun gs)† := by
  induction gs with
  | nil => simp [preparationInverse, preparationRun]
  | cons g gs ih =>
      change preparationRun (gs.reverse.map PreparationGate.inverse) =
        (preparationRun gs)† at ih
      rw [preparationInverse, List.reverse_cons, List.map_append,
        preparationRun_append]
      simp only [List.map_cons, List.map_nil, preparationRun, one_mul,
        PreparationGate.eval_inverse, ih]
      change star g.eval * star (preparationRun gs) =
        star (preparationRun gs * g.eval)
      rw [star_mul]

/-- The actual reversed list restores the all-zero computational input from
the prepared range target, with no new inverse-circuit assumption. -/
theorem physicalRangeCircuit_unprepares (n r : ℕ) (hn : 0 < n)
    (hnN : n ≤ 2 ^ r) (hN : 2 ^ r ≤ 4 * n) :
    preparationRun (preparationInverse (physicalRangeCircuit n r))
      (cleanLogicalEmbedding r (GateUniformRange.target n (2 ^ r))) =
      cleanLogicalEmbedding r (GateWalshHilbert.cleanInput r) := by
  rw [preparationInverse_eval]
  have h := congrArg (fun U : Physical r →L[ℂ] Physical r =>
    U (cleanLogicalEmbedding r (GateWalshHilbert.cleanInput r)))
    (physicalRangeCircuit_unitary n r hn hN).1
  change ((preparationRun (physicalRangeCircuit n r))†)
    (preparationRun (physicalRangeCircuit n r)
      (cleanLogicalEmbedding r (GateWalshHilbert.cleanInput r))) = _ at h
  rw [physicalRangeCircuit_prepares n r hn hnN hN] at h
  exact h

theorem physicalRangeCircuit_inverse_length_le (n r : ℕ) :
    (preparationInverse (physicalRangeCircuit n r)).length ≤ 7 * r + 14 := by
  rw [preparationInverse_length]
  exact physicalRangeCircuit_length_le n r



/-! ### Actual clean input and output amplitudes -/

/-- The complete elementary circuit starts on the ordinary all-zero
configuration, including its borrow and marked workspace. -/
theorem physicalRangeCircuit_cleanInput (n r : ℕ) (hn : 0 < n)
    (hnN : n ≤ 2 ^ r) (hN : 2 ^ r ≤ 4 * n) :
    preparationRun (physicalRangeCircuit n r)
      (cleanComputational 0 false (GateWalshWords.zeroWord r)) =
      cleanLogicalEmbedding r (GateUniformRange.target n (2 ^ r)) := by
  rw [← cleanLogicalEmbedding_cleanInput]
  exact physicalRangeCircuit_prepares n r hn hnN hN

/-- Exact amplitudes on the original physical wires.  The pointer is
uniform on the accepted range, and every temporary wire is zero. -/
theorem physicalRangeCircuit_amplitude (n r : ℕ) (hn : 0 < n)
    (hnN : n ≤ 2 ^ r) (hN : 2 ^ r ≤ 4 * n)
    (flag : Bool) (x : Word r) (borrow : BorrowRegister r) (marked : Bool) :
    preparationRun (physicalRangeCircuit n r)
      (cleanComputational 0 false (GateWalshWords.zeroWord r))
      (flag, ⟨x, borrow, marked⟩) =
      if borrow = cleanBorrow r ∧ marked = false ∧ flag = false ∧
          GatePointerEncoding.wordValue x < n
        then (CoherentReuse.uniformAmplitude n : ℂ) else 0 := by
  rw [physicalRangeCircuit_cleanInput n r hn hnN hN]
  have h := markedLayout_cleanLogicalEmbedding r
    (GateUniformRange.target n (2 ^ r)) (⟨flag, x, borrow⟩ : Payload r) marked
  change cleanLogicalEmbedding r (GateUniformRange.target n (2 ^ r))
      (flag, ⟨x, borrow, marked⟩) =
      (if borrow = cleanBorrow r
        then GateUniformRange.target n (2 ^ r)
          (GatePointerEncoding.wordEquivFin r x) flag
        else 0) * ComplexAmplitudeRotation.clean marked at h
  rw [h]
  by_cases hb : borrow = cleanBorrow r <;>
    by_cases hx : GatePointerEncoding.wordValue x < n <;>
      cases flag <;> cases marked <;>
        simp [hb, hx, GateUniformRange.target_false, GateUniformRange.target_true,
          GatePointerEncoding.wordEquivFin_apply, GatePointerEncoding.wordFin_val,
          ComplexAmplitudeRotation.clean]

/-- The exact forward preparation is stable under an untouched finite
reference.  Reference amplitudes are neither measured nor renormalised. -/
theorem physicalRangeCircuit_reference {R : Type*} [Fintype R]
    (n r : ℕ) (hn : 0 < n) (hnN : n ≤ 2 ^ r) (hN : 2 ^ r ≤ 4 * n)
    (a : EuclideanSpace ℂ R) :
    WeightedClock.diagonal (fun _ : R => preparationRun (physicalRangeCircuit n r))
        (WithLp.toLp 2 (fun j : R => a j •
          cleanComputational 0 false (GateWalshWords.zeroWord r))) =
      WithLp.toLp 2 (fun j : R => a j •
        cleanLogicalEmbedding r (GateUniformRange.target n (2 ^ r))) := by
  apply PiLp.ext
  intro j
  change preparationRun (physicalRangeCircuit n r)
      (a j • cleanComputational 0 false (GateWalshWords.zeroWord r)) = _
  rw [map_smul, physicalRangeCircuit_cleanInput n r hn hnN hN]

/-- The physical representation consists of the `r` pointer bits, `r+1`
borrow bits, one attenuation flag and one marked ancilla. -/
theorem rangeWorkspace_card (r : ℕ) :
    Fintype.card (Configuration r) = 2 ^ (2 * r + 3) := by
  rw [Fintype.card_congr (workspaceSplit r)]
  change Fintype.card (((Fin (r + 1) → Bool) × Bool) ×
    (Fin (2 ^ r) × Bool)) = _
  have hborrow : Fintype.card (Fin (r + 1) → Bool) = 2 ^ (r + 1) :=
    GatePointerEncoding.card_word (r + 1)
  have hbool : Fintype.card Bool = 2 := by decide
  simp only [Fintype.card_prod, Fintype.card_fin, hborrow, hbool]
  calc
    (2 ^ (r + 1) * 2) * (2 ^ r * 2) = 2 ^ (r + 2) * 2 ^ (r + 1) := by
      simp only [pow_succ]
    _ = 2 ^ ((r + 2) + (r + 1)) := (pow_add 2 (r + 2) (r + 1)).symm
    _ = 2 ^ (2 * r + 3) := by congr 1; omega

/-- Concrete constant-range preparation with its actual elementary list,
exact amplitudes, gate count and physical workspace size.  No state-loading
or reflection-correctness hypothesis is assumed by this result. -/
theorem physicalRangePreparation (n r : ℕ) (hn : 0 < n)
    (hnN : n ≤ 2 ^ r) (hN : 2 ^ r ≤ 4 * n) :
    IsUnitary (preparationRun (physicalRangeCircuit n r)) ∧
    preparationRun (physicalRangeCircuit n r)
        (cleanComputational 0 false (GateWalshWords.zeroWord r)) =
      cleanLogicalEmbedding r (GateUniformRange.target n (2 ^ r)) ∧
    (physicalRangeCircuit n r).length ≤ 7 * r + 14 ∧
    (∀ g ∈ physicalRangeCircuit n r, g.arity ≤ 3) ∧
    Fintype.card (Configuration r) = 2 ^ (2 * r + 3) := by
  exact ⟨physicalRangeCircuit_unitary n r hn hN,
    physicalRangeCircuit_cleanInput n r hn hnN hN,
    physicalRangeCircuit_length_le n r,
    physicalRangeCircuit_arity n r, rangeWorkspace_card r⟩

end
end SparseHamiltonian.GateRangeHilbertTransport
