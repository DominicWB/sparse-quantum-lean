import GateEfficientHamiltonian.GateTableSplit
/-!
The literal filter-tree instructions on one finite Hilbert register.

The layout equivalences below are used only to prove the semantics of a
one-control one-qubit gate. They are not extra whole-register primitives.
Every instruction remains the existing `GateFilterTree.Gate`, with arity
at most three, and the list length is unchanged.
-/

namespace SparseHamiltonian.GateFilterHilbert

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct

abbrev Configuration (w : ℕ) := GateFilterTree.Configuration w
abbrev Physical (w : ℕ) := EuclideanSpace ℂ (Configuration w)
abbrev Coefficients := GateFilterTree.Coefficients

variable {w : ℕ}

/-- Replace just the target slot, leaving all other slots and flags alone. -/
def put (j : Fin w) (z : Configuration w) (b : Bool) : Configuration w :=
  ⟨Function.update z.slot j b, z.flags⟩

@[simp] theorem put_slot (j : Fin w) (z : Configuration w) (b : Bool) :
    (put j z b).slot j = b := by simp [put]

@[simp] theorem put_flags (j : Fin w) (z : Configuration w) (b : Bool) :
    (put j z b).flags = z.flags := rfl

@[simp] theorem put_put (j : Fin w) (z : Configuration w) (b c : Bool) :
    put j (put j z b) c = put j z c := by
  apply GatePrefixCircuit.Configuration.ext
  · simp [put, Function.update_idem]
  · rfl

@[simp] theorem put_self (j : Fin w) (z : Configuration w) :
    put j z (z.slot j) = z := by
  apply GatePrefixCircuit.Configuration.ext
  · simp [put]
  · rfl

abbrev Rest (j : Fin w) := {z : Configuration w // z.slot j = false}

/-- Expose the target qubit; its control flag is retained in `Rest`. -/
def split (j : Fin w) : Configuration w ≃ Rest j × Bool where
  toFun z := (⟨put j z false, by simp⟩, z.slot j)
  invFun y := put j y.1.val y.2
  left_inv z := by simp
  right_inv y := by
    rcases y with ⟨⟨z, hz⟩, b⟩
    apply Prod.ext
    · apply Subtype.ext
      simp only [put_put]
      rw [← hz, put_self]
    · simp

def layout (j : Fin w) :
    Physical w ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Rest j => ComplexAmplitudeRotation.Qubit) :=
  (LookupOracle.permutationUnitary (split j)).trans
    (RegisterEquivalences.productFlatten (Rest j) Bool).symm

@[simp] theorem layout_apply (j : Fin w) (v : Physical w)
    (q : Rest j) (b : Bool) : layout j v q b = v (put j q.val b) := rfl

@[simp] theorem layout_symm_apply (j : Fin w)
    (v : PiLp 2 (fun _ : Rest j => ComplexAmplitudeRotation.Qubit))
    (z : Configuration w) :
    (layout j).symm v z = v ⟨put j z false, by simp⟩ (z.slot j) := by
  obtain ⟨u, rfl⟩ := (layout j).surjective v
  simp only [LinearIsometryEquiv.symm_apply_apply, layout_apply, put_put, put_self]

/-- A known two-by-two coefficient matrix, acting only on one qubit. -/
def localOperator (a : Coefficients) :
    ComplexAmplitudeRotation.Qubit →L[ℂ] ComplexAmplitudeRotation.Qubit :=
  SparseStateOverlap.matrixOperator a

theorem localOperator_mul (a b : Coefficients) :
    localOperator (a * b) = localOperator a * localOperator b := by
  ext v c
  cases c <;>
    simp [localOperator, SparseStateOverlap.matrixOperator_apply,
      Matrix.mul_apply, mul_apply_eq_comp] <;> ring

@[simp] theorem localOperator_one : localOperator (1 : Coefficients) = 1 := by
  ext v b
  simp [localOperator, SparseStateOverlap.matrixOperator_apply, Matrix.one_apply]

theorem localOperator_adjoint (a : Coefficients) :
    (localOperator a)† = localOperator a.conjTranspose :=
  SparseValuePrecision.matrixOperator_adjoint a

theorem localOperator_unitary (a : Coefficients)
    (ha : GatePrefixCircuit.Coefficients.IsUnitary a) :
    IsUnitary (localOperator a) := by
  constructor
  · change (localOperator a)† * localOperator a = 1
    rw [localOperator_adjoint, ← localOperator_mul, ha.1, localOperator_one]
  · change localOperator a * (localOperator a)† = 1
    rw [localOperator_adjoint, ← localOperator_mul, ha.2, localOperator_one]

/-- The one-control gate has the identity on the disabled flag sector. -/
def block (j : Fin w) (a : Coefficients) (q : Rest j) :
    ComplexAmplitudeRotation.Qubit →L[ℂ] ComplexAmplitudeRotation.Qubit :=
  if q.val.flags j then localOperator a else 1

theorem block_adjoint (j : Fin w) (a : Coefficients) (q : Rest j) :
    (block j a q)† = block j a.conjTranspose q := by
  cases h : q.val.flags j <;> simp [block, h, localOperator_adjoint]

theorem block_unitary (j : Fin w) (a : Coefficients)
    (ha : GatePrefixCircuit.Coefficients.IsUnitary a) (q : Rest j) :
    IsUnitary (block j a q) := by
  cases h : q.val.flags j
  · simp [block, h]
  · simpa [block, h] using localOperator_unitary a ha

/-- Physical meaning of the literal controlled rotation, with no hidden
many-controlled operation. -/
def rotation (j : Fin w) (a : Coefficients) : Physical w →L[ℂ] Physical w :=
  (layout j).symm.conjStarAlgEquiv (WeightedClock.diagonal (block j a))

theorem rotation_unitary (j : Fin w) (a : Coefficients)
    (ha : GatePrefixCircuit.Coefficients.IsUnitary a) :
    IsUnitary (rotation j a) := by
  have hd : IsUnitary (WeightedClock.diagonal (block j a)) := by
    constructor
    · exact WeightedClock.diagonal_isometry _ (fun q => (block_unitary j a ha q).1)
    · change WeightedClock.diagonal (block j a) ∘L
        (WeightedClock.diagonal (block j a))† = 1
      rw [WeightedClock.diagonal_adjoint, WeightedClock.diagonal_comp]
      have hb : (fun q => block j a q ∘L (block j a q)†) = fun _ => 1 := by
        funext q
        exact (block_unitary j a ha q).2
      rw [hb, WeightedClock.diagonal_one]
  exact hd.transport (layout j).symm

theorem rotation_adjoint (j : Fin w) (a : Coefficients) :
    (rotation j a)† = rotation j a.conjTranspose := by
  change star ((layout j).symm.conjStarAlgEquiv
      (WeightedClock.diagonal (block j a))) = _
  rw [← map_star]
  congr 1
  rw [star_eq_adjoint, WeightedClock.diagonal_adjoint]
  congr 1
  funext q
  exact block_adjoint j a q

/-- Coordinate formula identifies exactly the read control and target wires. -/
theorem rotation_apply (j : Fin w) (a : Coefficients)
    (v : Physical w) (z : Configuration w) :
    rotation j a v z =
      if z.flags j then ∑ b : Bool, a (z.slot j) b * v (put j z b)
      else v z := by
  rw [rotation, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  simp only [LinearIsometryEquiv.symm_symm, layout_symm_apply,
    WeightedClock.diagonal_apply]
  cases hz : z.flags j <;>
    simp [block, put, hz, localOperator,
      SparseStateOverlap.matrixOperator_apply, layout_apply,
      Function.update_idem, Function.update_eq_self]

/-- Two target updates agree precisely when their spectator configurations
and their target bits agree. -/
theorem put_eq_iff (j : Fin w) (z y : Configuration w) (b : Bool) :
    put j z b = y ↔ put j z false = put j y false ∧ b = y.slot j := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h, hb⟩
    rw [hb]
    calc
      put j z (y.slot j) = put j (put j z false) (y.slot j) := by simp
      _ = put j (put j y false) (y.slot j) := by rw [h]
      _ = y := by simp

/-- The Hilbert rotation has exactly the same basis columns as the literal
controlled two-by-two gate in the finitely supported semantics. -/
theorem rotation_single (j : Fin w) (a : Coefficients)
    (z : Configuration w) (c : ℂ) :
    rotation j a (EuclideanSpace.single z c) =
      if z.flags j then
        ∑ b : Bool, a b (z.slot j) • EuclideanSpace.single (put j z b) c
      else EuclideanSpace.single z c := by
  classical
  apply PiLp.ext
  intro y
  rw [rotation_apply]
  have hin (b : Bool) : z = put j y b ↔
      put j y false = put j z false ∧ b = z.slot j := by
    rw [eq_comm, put_eq_iff]
  have hout (b : Bool) : put j z b = y ↔
      put j z false = put j y false ∧ b = y.slot j := put_eq_iff j z y b
  by_cases h : put j y false = put j z false
  · have hf : y.flags = z.flags := by
      have := congrArg (fun q : Configuration w => q.flags) h
      simpa using this
    have hin' (b : Bool) : (put j y b = z ↔ b = z.slot j) := by
      rw [put_eq_iff]
      simp [h]
    have hout' (b : Bool) : (y = put j z b ↔ b = y.slot j) := by
      rw [eq_comm, put_eq_iff]
      simp [h.symm]
    have hyz : (y = z ↔ y.slot j = z.slot j) := by
      constructor
      · rintro rfl
        rfl
      · intro hb
        calc y = put j y (y.slot j) := (put_self j y).symm
          _ = z := (hin' _).mpr hb
    have hfj : y.flags j = z.flags j := by rw [hf]
    by_cases hz : z.flags j = true
    · have hy : y.flags j = true := hfj.trans hz
      simp only [hy, hz, if_true, Fintype.sum_bool, PiLp.add_apply, PiLp.smul_apply,
        PiLp.single_apply, hin', hout', smul_eq_mul]
      cases hyb : y.slot j <;> cases hzb : z.slot j <;> simp
    · have hy : ¬ y.flags j = true := fun hy => hz (hfj.symm.trans hy)
      simp only [hy, hz, if_false, Bool.false_eq_true, PiLp.single_apply]
  · have hzy : z ≠ y := by
      intro he
      subst z
      exact h rfl
    have hin' (b : Bool) : ¬ put j y b = z := by
      rw [put_eq_iff]
      exact fun hb => h hb.1
    have hout' (b : Bool) : ¬ y = put j z b := by
      rw [eq_comm, put_eq_iff]
      exact fun hb => h hb.1.symm
    by_cases hy : y.flags j = true <;> by_cases hz : z.flags j = true <;>
      simp [hy, hz, hin', hout', Ne.symm hzy]

/-- Normalised computational-basis identification with the genuine finite
Hilbert space. No rescaling of amplitudes is introduced. -/
def coordinates : GateFilterTree.State w →ₗ[ℂ] Physical w :=
  Finsupp.linearCombination ℂ (fun z => EuclideanSpace.single z 1)

@[simp] theorem coordinates_single (z : Configuration w) (c : ℂ) :
    coordinates (Finsupp.single z c) = EuclideanSpace.single z c := by
  classical
  simp only [coordinates, Finsupp.linearCombination_single]
  ext y
  simp [PiLp.single_apply]

@[simp] theorem coordinates_apply (v : GateFilterTree.State w) (z : Configuration w) :
    coordinates v z = v z := by
  classical
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf, hg]
  | single y c =>
      rcases eq_or_ne y z with h | h
      · subst h
        simp [coordinates_single]
      · simp [coordinates_single, Ne.symm h]

theorem coordinates_injective : Function.Injective (coordinates (w := w)) := by
  intro v u h
  ext z
  simpa using congrArg (fun q : Physical w => q z) h

theorem coordinates_surjective : Function.Surjective (coordinates (w := w)) := by
  classical
  intro v
  refine ⟨∑ z, Finsupp.single z (v z), ?_⟩
  ext z
  simp

/-- The amplitude identification uses the usual counting-basis Hilbert norm. -/
theorem coordinates_norm_sq (v : GateFilterTree.State w) :
    ‖coordinates v‖ ^ 2 = ∑ z, ‖v z‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [coordinates_apply]

def prefixEquiv (p : GateFilterTree.Word w) (j : Fin w) :
    Configuration w ≃ Configuration w where
  toFun := GateFilterTree.togglePath p j
  invFun := GateFilterTree.togglePath p j
  left_inv := GateFilterTree.togglePath_involutive p j
  right_inv := GateFilterTree.togglePath_involutive p j

def gate : GateFilterTree.Gate w → Physical w →L[ℂ] Physical w
  | .prefix p j => (LookupOracle.permutationUnitary
      (prefixEquiv p j)).toLinearIsometry.toContinuousLinearMap
  | .rotate j a => rotation j a

theorem gate_unitary (g : GateFilterTree.Gate w) (hg : g.Valid) :
    IsUnitary (gate g) := by
  cases g with
  | «prefix» p j => exact LookupOracle.permutationUnitary_unitary (prefixEquiv p j)
  | rotate j a => exact rotation_unitary j a hg

/-- Agreement of the actual physical instruction with the algebraic gate
on arbitrary superpositions, not just clean computational inputs. -/
theorem gate_intertwines (g : GateFilterTree.Gate w) :
    (gate g).toLinearMap.comp coordinates = coordinates.comp g.eval := by
  apply Finsupp.lhom_ext
  intro z c
  cases g with
  | «prefix» p j =>
      simp [LinearMap.comp_apply, gate, GateFilterTree.Gate.eval,
        prefixEquiv, coordinates_single, Finsupp.linearCombination_single,
        LookupOracle.permutationUnitary_single]
  | rotate j a =>
      simp only [LinearMap.comp_apply, coordinates_single, gate,
        ContinuousLinearMap.coe_coe]
      rw [rotation_single]
      simp only [GateFilterTree.Gate.eval, GatePrefixCircuit.Gate.eval,
        Finsupp.linearCombination_single, GatePrefixCircuit.rotateBasis]
      cases hz : z.flags j <;>
        simp [coordinates_single, put,
          mul_comm]
      all_goals
        apply PiLp.ext
        intro y
        simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]
        split_ifs <;> ring

theorem gate_coordinates (g : GateFilterTree.Gate w) (v : GateFilterTree.State w) :
    gate g (coordinates v) = coordinates (g.eval v) :=
  congrArg (fun A : GateFilterTree.State w →ₗ[ℂ] Physical w => A v)
    (gate_intertwines g)

theorem gate_inverse (g : GateFilterTree.Gate w) :
    gate g.inverse = (gate g)† := by
  cases g with
  | «prefix» p j =>
      change (LookupOracle.permutationUnitary (prefixEquiv p j)).toLinearIsometry.toContinuousLinearMap =
        ((LookupOracle.permutationUnitary (prefixEquiv p j)).toLinearIsometry.toContinuousLinearMap)†
      rw [LookupOracle.permutationUnitary_adjoint]
      rw [← LookupOracle.permutationUnitary_symm]
      rfl
  | rotate j a => exact (rotation_adjoint j a).symm

/-- Execute precisely the previously charged list, in chronological order. -/
def run : List (GateFilterTree.Gate w) → Physical w →L[ℂ] Physical w
  | [] => 1
  | g :: gs => run gs * gate g

theorem run_append (gs hs : List (GateFilterTree.Gate w)) :
    run (gs ++ hs) = run hs * run gs := by
  induction gs with
  | nil => simp [run]
  | cons g gs ih => simp [run, ih, mul_assoc]

theorem run_coordinates (gs : List (GateFilterTree.Gate w))
    (v : GateFilterTree.State w) :
    run gs (coordinates v) = coordinates (GateFilterTree.run gs v) := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
      change run gs (gate g (coordinates v)) =
        coordinates (GateFilterTree.run gs (g.eval v))
      rw [gate_coordinates, ih]

/-- The complete physical traversal obeys the already-proved clean-prefix
intertwining identity. Thus this is the same tree preparation, not another
unitary with an unrelated gate count. -/
theorem compile_coordinates {h : ℕ} (t : GateFilterTree.RotationTree h)
    (offset : ℕ) (hfit : offset + h ≤ w) (p : GateFilterTree.Word w)
    (v : GatePrefixCircuit.SlotState w) :
    run (GateFilterTree.compile t offset hfit p)
        (coordinates (GateFilterTree.embed p offset v)) =
      coordinates (GateFilterTree.embed p offset
        (GateFilterTree.idealTraversal t offset hfit p v)) := by
  rw [run_coordinates]
  congr 1
  exact congrArg (fun A : GatePrefixCircuit.SlotState w →ₗ[ℂ]
      GateFilterTree.State w => A v)
    (GateFilterTree.compile_intertwines t offset hfit p)

theorem run_unitary (gs : List (GateFilterTree.Gate w))
    (hgs : GateFilterTree.GatesValid gs) : IsUnitary (run gs) := by
  revert hgs
  induction gs with
  | nil => intro _; exact isUnitary_one
  | cons g gs ih =>
      intro hgs
      exact (ih (fun q hq => hgs q (List.mem_cons_of_mem g hq))).mul
        (gate_unitary g (hgs g List.mem_cons_self))

/-- Literal reverse instructions, not a newly assumed inverse primitive,
implement the Hilbert adjoint on the entire workspace, including dirty flags. -/
theorem run_inverse (gs : List (GateFilterTree.Gate w)) :
    run (GateFilterTree.inverse gs) = (run gs)† := by
  induction gs with
  | nil => simp [run]
  | cons g gs ih =>
      rw [GateFilterTree.inverse_cons, run_append]
      simp only [run, one_mul, ih, gate_inverse]
      change star (gate g) * star (run gs) = star (run gs * gate g)
      rw [star_mul]

/-- A valid table traversal is a genuine unitary built from its actual
bounded-arity instructions. The existing gate count remains exact. -/
theorem compile_unitary {h : ℕ} (t : GateFilterTree.RotationTree h)
    (ht : t.Valid) (offset : ℕ) (hfit : offset + h ≤ w)
    (p : GateFilterTree.Word w) :
    IsUnitary (run (GateFilterTree.compile t offset hfit p)) :=
  run_unitary _ (GateFilterTree.compile_valid t ht offset hfit p)

theorem compile_adjoint_count {h : ℕ} (t : GateFilterTree.RotationTree h)
    (offset : ℕ) (hfit : offset + h ≤ w) (p : GateFilterTree.Word w) :
    run (GateFilterTree.inverse (GateFilterTree.compile t offset hfit p)) =
      (run (GateFilterTree.compile t offset hfit p))† ∧
    (GateFilterTree.compile t offset hfit p).length = 3 * (2 ^ h - 1) ∧
    (GateFilterTree.inverse (GateFilterTree.compile t offset hfit p)).length =
      3 * (2 ^ h - 1) :=
  ⟨run_inverse _, GateFilterTree.compile_length t offset hfit p,
    GateFilterTree.compile_inverse_length t offset hfit p⟩

section Reference

variable {R : Type*} [Fintype R]

/-- The same physical list with a spectator register. Each instruction acts
on exactly its original wires and does not read a reference label. -/
def referenceRun : List (GateFilterTree.Gate w) →
    PiLp 2 (fun _ : R => Physical w) →L[ℂ] PiLp 2 (fun _ : R => Physical w)
  | [] => 1
  | g :: gs => referenceRun gs * FiniteReferenceLift.lift (gate g)

omit [Fintype R] in
theorem referenceRun_apply (gs : List (GateFilterTree.Gate w))
    (ψ : PiLp 2 (fun _ : R => Physical w)) (r : R) :
    referenceRun gs ψ r = run gs (ψ r) := by
  induction gs generalizing ψ with
  | nil => rfl
  | cons g gs ih =>
      change referenceRun gs (FiniteReferenceLift.lift (gate g) ψ) r =
        run gs (gate g (ψ r))
      rw [ih]
      rfl

omit [Fintype R] in
theorem referenceRun_eq (gs : List (GateFilterTree.Gate w)) :
    referenceRun (R := R) gs = FiniteReferenceLift.lift (run gs) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply PiLp.ext
  intro r
  exact referenceRun_apply gs ψ r

theorem referenceRun_unitary (gs : List (GateFilterTree.Gate w))
    (hgs : GateFilterTree.GatesValid gs) :
    IsUnitary (referenceRun (R := R) gs) := by
  rw [referenceRun_eq]
  exact FiniteReferenceLift.lift_unitary _ (run_unitary gs hgs)

theorem referenceRun_inverse (gs : List (GateFilterTree.Gate w)) :
    referenceRun (R := R) (GateFilterTree.inverse gs) =
      (referenceRun (R := R) gs)† := by
  rw [referenceRun_eq, referenceRun_eq, run_inverse,
    FiniteReferenceLift.lift_eq_diagonal, FiniteReferenceLift.lift_eq_diagonal,
    WeightedClock.diagonal_adjoint]

omit [Fintype R] in
/-- Joint, possibly entangled, input amplitudes obey the same exact clean
intertwining identity. The reference dimension does not enter the list size. -/
theorem reference_compile_coordinates {h : ℕ} (t : GateFilterTree.RotationTree h)
    (offset : ℕ) (hfit : offset + h ≤ w) (p : GateFilterTree.Word w)
    (v : R → GatePrefixCircuit.SlotState w) :
    referenceRun (GateFilterTree.compile t offset hfit p)
        (WithLp.toLp 2 (fun r => coordinates (GateFilterTree.embed p offset (v r)))) =
      WithLp.toLp 2 (fun r => coordinates (GateFilterTree.embed p offset
        (GateFilterTree.idealTraversal t offset hfit p (v r)))) := by
  apply PiLp.ext
  intro r
  rw [referenceRun_apply]
  exact compile_coordinates t offset hfit p (v r)

end Reference

end
end SparseHamiltonian.GateFilterHilbert


/-! ### Clean table-register coordinates and workspace -/

namespace SparseHamiltonian.GateFilterTree
noncomputable section

variable {w : ℕ}

/-- The physical table register consists of a word and an equally sized
register of reusable path flags. This is a register identification, not a
whole-register elementary gate. -/
def configurationRegisters (w : ℕ) : Configuration w ≃ Word w × Word w where
  toFun z := (z.slot, z.flags)
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exactly `w` data bits and `w` temporary flags suffice for the whole
depth-first traversal, independently of the number of leaves. -/
theorem filterWorkspace_card (w : ℕ) :
    Fintype.card (Configuration w) = 2 ^ (2 * w) := by
  rw [Fintype.card_congr (configurationRegisters w), Fintype.card_prod]
  change Fintype.card (Fin w → Bool) * Fintype.card (Fin w → Bool) = _
  simp only [GatePointerEncoding.card_word]
  rw [← pow_add]
  congr 1
  omega

/-- At depth zero, the path-invariant embedding is the ordinary clean
computational encoding, independent of the public path used for compilation. -/
theorem encoded_zero_eq_iff (p x : Word w) (z : Configuration w) :
    encoded p 0 x = z ↔ x = z.slot ∧ z.flags = fun _ => false := by
  constructor
  · intro h
    constructor
    · simpa only [encoded_slot] using congrArg (fun q : Configuration w => q.slot) h
    · simpa only [encoded_zero_flags] using
        (congrArg (fun q : Configuration w => q.flags) h).symm
  · rintro ⟨hx, hf⟩
    apply GatePrefixCircuit.Configuration.ext
    · simpa only [encoded_slot] using hx
    · simpa only [encoded_zero_flags] using hf.symm

/-- The actual clean encoding has zero amplitude on every dirty flag state.
This formula applies to arbitrary coherent amplitudes, not just a basis input. -/
theorem embed_zero_apply (p : Word w) (f : GatePrefixCircuit.SlotState w)
    (z : Configuration w) :
    embed p 0 f z = if z.flags = (fun _ => false) then f z.slot else 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add]
      simp only [Finsupp.add_apply, hf, hg]
      split_ifs <;> simp
  | single x c =>
      simp only [embed, Finsupp.linearCombination_single, Finsupp.smul_apply,
        smul_eq_mul, Finsupp.single_apply, encoded_zero_eq_iff]
      by_cases hz : z.flags = (fun _ => false) <;>
        by_cases hx : x = z.slot <;> simp [hz, hx]

end
end SparseHamiltonian.GateFilterTree


/-! ### Clean physical preparation of a probability table -/

namespace SparseHamiltonian.GateFilterHilbert
noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct

variable {w : ℕ}

/-- Coherent table amplitudes with all path flags initialised to zero. -/
def cleanState (v : GatePrefixCircuit.SlotState w) : Physical w :=
  coordinates (GateFilterTree.embed (fun _ => false) 0 v)

theorem cleanState_apply (v : GatePrefixCircuit.SlotState w)
    (z : Configuration w) :
    cleanState v z = if z.flags = (fun _ => false) then v z.slot else 0 := by
  rw [cleanState, coordinates_apply, GateFilterTree.embed_zero_apply]

/-- The actual computational input of the preparation circuit. -/
def tableInput (w : ℕ) : Physical w :=
  cleanState (Finsupp.single (fun _ => false) 1)

theorem tableInput_eq_single (w : ℕ) :
    tableInput w = EuclideanSpace.single
      (⟨fun _ => false, fun _ => false⟩ : Configuration w) 1 := by
  classical
  rw [tableInput, cleanState]
  simp only [GateFilterTree.embed, Finsupp.linearCombination_single, one_smul,
    coordinates_single]
  congr 1

theorem tableInput_norm (w : ℕ) : ‖tableInput w‖ = 1 := by
  rw [tableInput_eq_single]
  simp

/-- The target state in the ordinary counting-basis Hilbert space. -/
def tableState (a : GateFilterTree.Word w → ℝ) : Physical w :=
  cleanState (∑ x, Finsupp.single x (Real.sqrt (a x) : ℂ))

/-- Each clean coordinate is its prescribed square-root amplitude, and
every dirty flag coordinate has zero amplitude. -/
theorem tableState_apply (a : GateFilterTree.Word w → ℝ)
    (z : Configuration w) :
    tableState a z = if z.flags = (fun _ => false)
      then (Real.sqrt (a z.slot) : ℂ) else 0 := by
  classical
  rw [tableState, cleanState_apply]
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- Literal prefix-compute/rotation/uncompute instructions for the table. -/
def tableCircuit (a : GateFilterTree.Word w → ℝ) (ha : ∀ x, 0 ≤ a x) :
    List (GateFilterTree.Gate w) :=
  GateFilterTree.compile (GateFilterTree.MassTree.fromTable w a ha).rotations
    0 (by omega) (fun _ => false)

theorem tableCircuit_valid (a : GateFilterTree.Word w → ℝ)
    (ha : ∀ x, 0 ≤ a x) : GateFilterTree.GatesValid (tableCircuit a ha) :=
  (GateFilterTree.MassTree.fromTable w a ha).compile_valid
    0 (by omega) (fun _ => false)

theorem tableCircuit_unitary (a : GateFilterTree.Word w → ℝ)
    (ha : ∀ x, 0 ≤ a x) : IsUnitary (run (tableCircuit a ha)) :=
  run_unitary _ (tableCircuit_valid a ha)

/-- Physical preparation is derived from the action of the actual gate
list, including every flag operation; no loader correctness is assumed. -/
theorem tableCircuit_prepares (a : GateFilterTree.Word w → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hmass : ∑ x, a x = 1) :
    run (tableCircuit a ha) (tableInput w) = tableState a := by
  rw [tableInput, cleanState, run_coordinates]
  exact congrArg coordinates (GateFilterTree.MassTree.compile_full_table a ha hmass)

/-- The prepared counting-basis vector has norm one. This follows from
the actual circuit's unitarity, not a separate normalisation promise. -/
theorem tableState_norm (a : GateFilterTree.Word w → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hmass : ∑ x, a x = 1) : ‖tableState a‖ = 1 := by
  rw [← tableCircuit_prepares a ha hmass]
  have hi : ((run (tableCircuit a ha))†).comp (run (tableCircuit a ha)) = 1 :=
    (tableCircuit_unitary a ha).1
  rw [(norm_map_iff_adjoint_comp_self _).mpr hi, tableInput_norm]

/-- Unpreparation uses the reversed physical list with conjugate-transposed
two-by-two rotations; it is not a separately supplied primitive. -/
theorem tableCircuit_unprepares (a : GateFilterTree.Word w → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hmass : ∑ x, a x = 1) :
    run (GateFilterTree.inverse (tableCircuit a ha)) (tableState a) =
      tableInput w := by
  rw [tableState, cleanState, run_coordinates]
  exact congrArg coordinates
    (GateFilterTree.MassTree.compile_full_table_inverse a ha hmass)

theorem tableCircuit_adjoint_unprepares (a : GateFilterTree.Word w → ℝ)
    (ha : ∀ x, 0 ≤ a x) (hmass : ∑ x, a x = 1) :
    ((run (tableCircuit a ha))†) (tableState a) = tableInput w := by
  rw [← run_inverse]
  exact tableCircuit_unprepares a ha hmass

theorem tableCircuit_length (a : GateFilterTree.Word w → ℝ)
    (ha : ∀ x, 0 ≤ a x) :
    (tableCircuit a ha).length = 3 * (2 ^ w - 1) :=
  GateFilterTree.compile_length _ 0 (by omega) (fun _ => false)

theorem tableCircuit_inverse_length (a : GateFilterTree.Word w → ℝ)
    (ha : ∀ x, 0 ≤ a x) :
    (GateFilterTree.inverse (tableCircuit a ha)).length = 3 * (2 ^ w - 1) := by
  rw [GateFilterTree.inverse_length, tableCircuit_length]

/-- The same list leaves an arbitrary reference/payload register untouched.
The reference size does not change its elementary gate count. -/
theorem reference_tableCircuit_prepares {R : Type*} [Fintype R]
    (a : GateFilterTree.Word w → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hmass : ∑ x, a x = 1) (v : R → ℂ) :
    referenceRun (tableCircuit a ha)
        (WithLp.toLp 2 (fun r => v r • tableInput w)) =
      WithLp.toLp 2 (fun r => v r • tableState a) := by
  apply PiLp.ext
  intro r
  rw [referenceRun_apply]
  change run (tableCircuit a ha) (v r • tableInput w) = v r • tableState a
  rw [map_smul, tableCircuit_prepares a ha hmass]

end
end SparseHamiltonian.GateFilterHilbert


/-! ### The actual smoothing coefficients on a physical Boolean register

The two signed families are laid out consecutively, without an arbitrary
finite enumeration. Unused Boolean words have coefficient zero and a legal
one-slot reuse duration. The table is public classical data; its preparation
is the existing bounded-arity mass-tree traversal, not a lookup oracle.
-/

namespace SparseHamiltonian.GateFilterTable

noncomputable section
open scoped BigOperators InnerProduct

abbrev Word (r : ℕ) := GateFilterTree.Word r

/-- Public numeric labels for the positive and negative smoothing families. -/
def indexNumber (d : ℕ) : ReuseWeights.Index d → ℕ
  | .inl j => j.val
  | .inr j => d + 1 + j.val

theorem indexNumber_lt (d : ℕ) (i : ReuseWeights.Index d) :
    indexNumber d i < 2 * (d + 1) := by
  rcases i with j | j <;> simp only [indexNumber] <;> have := j.isLt <;> omega

theorem indexNumber_injective (d : ℕ) : Function.Injective (indexNumber d) := by
  intro i j hij
  rcases i with i | i <;> rcases j with j | j
  · simp only [indexNumber] at hij
    exact congrArg Sum.inl (Fin.ext hij)
  · simp only [indexNumber] at hij
    have := i.isLt
    omega
  · simp only [indexNumber] at hij
    have := j.isLt
    omega
  · simp only [indexNumber] at hij
    exact congrArg Sum.inr (Fin.ext (by omega))

/-- The numerical encoding uses the already constructed little-endian word
equivalence. It is a public labelling, not a physical gate. -/
def indexEmbedding (d r : ℕ) (hfit : 2 * (d + 1) ≤ 2 ^ r) :
    ReuseWeights.Index d ↪ Word r where
  toFun i := (GatePointerEncoding.wordEquivFin r).symm
    ⟨indexNumber d i, lt_of_lt_of_le (indexNumber_lt d i) hfit⟩
  inj' := by
    intro i j hij
    have hv := congrArg (fun x => (GatePointerEncoding.wordEquivFin r x).val) hij
    simp only [Equiv.apply_symm_apply] at hv
    exact indexNumber_injective d hv

@[simp] theorem indexEmbedding_value (d r : ℕ)
    (hfit : 2 * (d + 1) ≤ 2 ^ r) (i : ReuseWeights.Index d) :
    (GatePointerEncoding.wordEquivFin r (indexEmbedding d r hfit i)).val =
      indexNumber d i := by
  change (GatePointerEncoding.wordEquivFin r
    ((GatePointerEncoding.wordEquivFin r).symm _)).val = _
  simp only [Equiv.apply_symm_apply]

section ZeroExtension

variable {ι : Type*} [Fintype ι] {r : ℕ}

/-- Zero-extension through an explicit injective physical-word labelling. -/
def zeroExtend (e : ι ↪ Word r) (a : ι → ℝ) (x : Word r) : ℝ :=
  ∑ i, if e i = x then a i else 0

@[simp] theorem zeroExtend_at (e : ι ↪ Word r) (a : ι → ℝ) (i : ι) :
    zeroExtend e a (e i) = a i := by
  classical
  unfold zeroExtend
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have he : e j ≠ e i := fun hh => hji (e.injective hh)
    simp [he]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem zeroExtend_outside (e : ι ↪ Word r) (a : ι → ℝ) (x : Word r)
    (hx : ∀ i, e i ≠ x) : zeroExtend e a x = 0 := by
  classical
  simp [zeroExtend, hx]

theorem zeroExtend_abs (e : ι ↪ Word r) (a : ι → ℝ) (x : Word r) :
    |zeroExtend e a x| = zeroExtend e (fun i => |a i|) x := by
  classical
  by_cases hx : ∃ i, e i = x
  · obtain ⟨i, rfl⟩ := hx
    simp only [zeroExtend_at]
  · have hout : ∀ i, e i ≠ x := by
      intro i hi
      exact hx ⟨i, hi⟩
    rw [zeroExtend_outside e a x hout,
      zeroExtend_outside e (fun i => |a i|) x hout, abs_zero]

/-- Padding preserves the signed coefficient sum exactly. -/
theorem zeroExtend_sum (e : ι ↪ Word r) (a : ι → ℝ) :
    (∑ x, zeroExtend e a x) = ∑ i, a i := by
  classical
  simp only [zeroExtend]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp

/-- Padding preserves absolute mass, not merely an upper estimate. -/
theorem zeroExtend_abs_sum (e : ι ↪ Word r) (a : ι → ℝ) :
    (∑ x, |zeroExtend e a x|) = ∑ i, |a i| := by
  simp only [zeroExtend_abs]
  exact zeroExtend_sum e (fun i => |a i|)

/-- Coefficient relabelling preserves every operator-valued weighted sum.
No correctness property of SELECT is assumed in this elementary identity. -/
theorem zeroExtend_weighted_sum {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (e : ι ↪ Word r) (a : ι → ℝ) (R : Word r → E) :
    (∑ x, zeroExtend e a x • R x) = ∑ i, a i • R (e i) := by
  classical
  simp only [zeroExtend, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single (e i)]
  · simp
  · intro x hx hxi
    have hne : e i ≠ x := Ne.symm hxi
    simp [hne]
  · intro hi
    exact (hi (Finset.mem_univ (e i))).elim

end ZeroExtension

/-- The original, uncoalesced smoothing table on Boolean branch words. -/
def coefficient (a : ℕ → ℝ) (d r : ℕ)
    (hfit : 2 * (d + 1) ≤ 2 ^ r) : Word r → ℝ :=
  zeroExtend (indexEmbedding d r hfit) (ReuseWeights.weight a d)

@[simp] theorem coefficient_at (a : ℕ → ℝ) (d r : ℕ)
    (hfit : 2 * (d + 1) ≤ 2 ^ r) (i : ReuseWeights.Index d) :
    coefficient a d r hfit (indexEmbedding d r hfit i) =
      ReuseWeights.weight a d i :=
  zeroExtend_at _ _ _

theorem coefficient_zero_padding (a : ℕ → ℝ) (d r : ℕ)
    (hfit : 2 * (d + 1) ≤ 2 ^ r) (x : Word r)
    (hx : 2 * (d + 1) ≤ (GatePointerEncoding.wordEquivFin r x).val) :
    coefficient a d r hfit x = 0 := by
  apply zeroExtend_outside
  intro i hi
  have hval := indexEmbedding_value d r hfit i
  rw [hi] at hval
  have hlt := indexNumber_lt d i
  omega

theorem coefficient_absolute_mass (L k r : ℕ) (hL : 1 ≤ L)
    (hd : 0 < k * (L - 1))
    (hfit : 2 * (k * (L - 1) + 1) ≤ 2 ^ r) :
    (∑ x, |coefficient (AveragingPolynomial.filter L k).coeff
      (k * (L - 1)) r hfit x|) = 2 := by
  unfold coefficient
  rw [zeroExtend_abs_sum]
  exact ReuseWeights.concrete_absolute_mass L k hL hd

theorem coefficient_signed_mass (L k r : ℕ) (hL : 1 ≤ L)
    (hd : 0 < k * (L - 1))
    (hfit : 2 * (k * (L - 1) + 1) ≤ 2 ^ r) :
    (∑ x, coefficient (AveragingPolynomial.filter L k).coeff
      (k * (L - 1)) r hfit x) = 1 := by
  unfold coefficient
  rw [zeroExtend_sum]
  exact ReuseWeights.concrete_signed_mass L k hL hd

/-- The duration table retains exactly the two original branch families;
unused words receive a harmless legal one-slot duration. -/
def duration (d r : ℕ) (x : Word r) : ℕ :=
  let n := (GatePointerEncoding.wordEquivFin r x).val
  if n < d + 1 then n + d
  else if n < 2 * (d + 1) then max 1 (n - (d + 1)) else 1

theorem duration_at (d r : ℕ) (hfit : 2 * (d + 1) ≤ 2 ^ r)
    (i : ReuseWeights.Index d) :
    duration d r (indexEmbedding d r hfit i) = ReuseWeights.length d i := by
  unfold duration
  rw [indexEmbedding_value]
  rcases i with j | j
  · have hj := j.isLt
    simp only [indexNumber, ReuseWeights.length, Sum.elim_inl]
    rw [if_pos hj]
  · have hj := j.isLt
    simp only [indexNumber, ReuseWeights.length, Sum.elim_inr]
    rw [if_neg (by omega), if_pos (by omega)]
    congr 1
    omega

theorem duration_pos (d r : ℕ) (hd : 0 < d) (x : Word r) :
    0 < duration d r x := by
  unfold duration
  dsimp only
  split_ifs <;> omega

theorem duration_le (d r : ℕ) (hd : 0 < d) (x : Word r) :
    duration d r x ≤ 2 * d := by
  unfold duration
  dsimp only
  split_ifs <;> omega

/-- The padded branch list is exactly the smoothing operator already used
by the native query proof. No extra branch term survives zero padding. -/
theorem smoothing_operator_eq {P : Type*} [NormedAddCommGroup P]
    [InnerProductSpace ℂ P] (a : ℕ → ℝ) (d r : ℕ)
    (hfit : 2 * (d + 1) ≤ 2 ^ r) (R : ℕ → P →L[ℂ] P) :
    (∑ x, coefficient a d r hfit x • R (duration d r x)) =
      SmoothedReuse.weightedReuse a d R := by
  unfold coefficient
  rw [zeroExtend_weighted_sum]
  simp only [duration_at]
  exact ReuseWeights.weighted_sum_eq a d R

/-- The concrete probability table for the actual averaging-polynomial
coefficients, with no premise asserting preparation or normalisation. -/
def massTree (L k r : ℕ)
    (hfit : 2 * (k * (L - 1) + 1) ≤ 2 ^ r) : GateFilterTree.MassTree r :=
  GateFilterTree.MassTree.fromTable r
    (CoherentLCU.coefficientProbability
      (coefficient (AveragingPolynomial.filter L k).coeff (k * (L - 1)) r hfit))
    (CoherentLCU.coefficientProbability_nonneg _)

theorem massTree_mass (L k r : ℕ) (hL : 1 ≤ L)
    (hd : 0 < k * (L - 1))
    (hfit : 2 * (k * (L - 1) + 1) ≤ 2 ^ r) :
    (massTree L k r hfit).mass = 1 := by
  apply GateFilterTree.MassTree.coefficientTable_mass
  exact coefficient_absolute_mass L k r hL hd hfit

theorem massTree_value (L k r : ℕ)
    (hfit : 2 * (k * (L - 1) + 1) ≤ 2 ^ r) (x : Word r) :
    (massTree L k r hfit).value x =
      |coefficient (AveragingPolynomial.filter L k).coeff
        (k * (L - 1)) r hfit x| / 2 := by
  exact GateFilterTree.MassTree.fromTable_value r _ _ x

/-- On every populated branch, the tree contains precisely the probability
used by CoherentLCU.inputEmbedding and CoherentLCU.outputEmbedding. -/
theorem massTree_value_at (L k r : ℕ)
    (hfit : 2 * (k * (L - 1) + 1) ≤ 2 ^ r)
    (i : ReuseWeights.Index (k * (L - 1))) :
    (massTree L k r hfit).value
      (indexEmbedding (k * (L - 1)) r hfit i) =
        CoherentLCU.coefficientProbability
          (ReuseWeights.weight (AveragingPolynomial.filter L k).coeff
            (k * (L - 1))) i := by
  rw [massTree_value, coefficient_at]
  rfl

theorem massTree_zero_padding (L k r : ℕ)
    (hfit : 2 * (k * (L - 1) + 1) ≤ 2 ^ r) (x : Word r)
    (hx : 2 * (k * (L - 1) + 1) ≤
      (GatePointerEncoding.wordEquivFin r x).val) :
    (massTree L k r hfit).value x = 0 := by
  rw [massTree_value, coefficient_zero_padding _ _ _ hfit x hx]
  norm_num

private theorem nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hp : 0 < 2 ^ n := by positivity
      rw [pow_succ]
      omega

private theorem power_exists (n : ℕ) : ∃ r : ℕ, n ≤ 2 ^ r :=
  ⟨n, nat_le_two_pow n⟩

/-- Minimal public branch-register width. This is classical preprocessing,
not a run-time arithmetic or oracle call. -/
def branchBits (d : ℕ) : ℕ := Nat.find (power_exists (2 * (d + 1)))

theorem branchBits_fits (d : ℕ) : 2 * (d + 1) ≤ 2 ^ branchBits d :=
  Nat.find_spec (power_exists (2 * (d + 1)))

theorem branchBits_pos (d : ℕ) : 0 < branchBits d := by
  have hf := branchBits_fits d
  by_contra h
  have hz : branchBits d = 0 := by omega
  have hb : 2 * (d + 1) ≤ 1 := by simpa only [hz, pow_zero] using hf
  omega

/-- Power-of-two padding costs less than a factor two over the original
two signed families; it cannot introduce a dimension-sized gate overhead. -/
theorem branchBits_small (d : ℕ) : 2 ^ branchBits d < 4 * (d + 1) := by
  have hp := branchBits_pos d
  have hmin : ¬ 2 * (d + 1) ≤ 2 ^ (branchBits d - 1) :=
    Nat.find_min (power_exists (2 * (d + 1))) (by
      change branchBits d - 1 < branchBits d
      omega)
  have he : branchBits d - 1 + 1 = branchBits d := by omega
  have hpow : 2 ^ branchBits d = 2 ^ (branchBits d - 1) * 2 := by
    calc
      2 ^ branchBits d = 2 ^ (branchBits d - 1 + 1) := by rw [he]
      _ = 2 ^ (branchBits d - 1) * 2 := pow_succ _ _
  rw [hpow]
  omega

theorem branchBits_bounds (d : ℕ) :
    2 * (d + 1) ≤ 2 ^ branchBits d ∧
      2 ^ branchBits d < 4 * (d + 1) :=
  ⟨branchBits_fits d, branchBits_small d⟩

/-- Literal elementary-gate list for the concrete smoothing mass tree. -/
def circuit (L k : ℕ) : List (GateFilterTree.Gate (branchBits (k * (L - 1)))) :=
  GateFilterTree.compile
    (massTree L k (branchBits (k * (L - 1)))
      (branchBits_fits (k * (L - 1)))).rotations 0 (by omega) (fun _ => false)

theorem circuit_valid (L k : ℕ) : GateFilterTree.GatesValid (circuit L k) :=
  GateFilterTree.MassTree.compile_valid _ _ _ _

theorem circuit_length (L k : ℕ) :
    (circuit L k).length = 3 * (2 ^ branchBits (k * (L - 1)) - 1) :=
  GateFilterTree.compile_length _ _ _ _

/-- The actual preparation list uses fewer than twelve gates per original
polynomial coefficient. Prefix computation/uncomputation is included. -/
theorem circuit_length_lt (L k : ℕ) :
    (circuit L k).length < 12 * (k * (L - 1) + 1) := by
  rw [circuit_length]
  have := branchBits_small (k * (L - 1))
  omega

theorem circuit_inverse_length_lt (L k : ℕ) :
    (GateFilterTree.inverse (circuit L k)).length <
      12 * (k * (L - 1) + 1) := by
  rw [GateFilterTree.inverse_length]
  exact circuit_length_lt L k

theorem circuit_gate_arity (L k : ℕ)
    (g : GateFilterTree.Gate (branchBits (k * (L - 1)))) : g.arity ≤ 3 :=
  GateFilterTree.Gate.arity_le_three g

end
end SparseHamiltonian.GateFilterTable


/-! ### Physical preparation of the actual smoothing-filter branch table -/

namespace SparseHamiltonian.GateReuseFilterPhysical

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct

abbrev degree (L k : ℕ) := k * (L - 1)
abbrev width (L k : ℕ) := GateFilterTable.branchBits (degree L k)

/-- The probabilities are fixed by the released averaging-polynomial
coefficients. They are not a supplied state-preparation certificate. -/
def probability (L k : ℕ) : GateFilterTable.Word (width L k) → ℝ :=
  CoherentLCU.coefficientProbability
    (GateFilterTable.coefficient (AveragingPolynomial.filter L k).coeff
      (degree L k) (width L k) (GateFilterTable.branchBits_fits (degree L k)))

theorem probability_nonneg (L k : ℕ) (x : GateFilterTable.Word (width L k)) :
    0 ≤ probability L k x :=
  CoherentLCU.coefficientProbability_nonneg _ x

theorem probability_sum (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < degree L k) :
    (∑ x, probability L k x) = 1 := by
  apply CoherentLCU.coefficientProbability_sum
  exact GateFilterTable.coefficient_absolute_mass L k (width L k) hL hd
    (GateFilterTable.branchBits_fits (degree L k))

/-- The full physical output includes the clean prefix-flag register. -/
def state (L k : ℕ) : GateFilterHilbert.Physical (width L k) :=
  GateFilterHilbert.tableState (probability L k)

/-- The concrete smoothing gate list is exactly the generic physical
probability-table construction, including its prefix compute/uncompute. -/
theorem circuit_eq_tableCircuit (L k : ℕ) :
    GateFilterTable.circuit L k =
      GateFilterHilbert.tableCircuit (probability L k) (probability_nonneg L k) := rfl

theorem prepares (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < degree L k) :
    GateFilterHilbert.run (GateFilterTable.circuit L k)
        (GateFilterHilbert.tableInput (width L k)) = state L k := by
  rw [circuit_eq_tableCircuit]
  exact GateFilterHilbert.tableCircuit_prepares (probability L k)
    (probability_nonneg L k) (probability_sum L k hL hd)

/-- The very same physical list, literally reversed, unprepares the state. -/
theorem unprepares (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < degree L k) :
    GateFilterHilbert.run (GateFilterTree.inverse (GateFilterTable.circuit L k))
        (state L k) = GateFilterHilbert.tableInput (width L k) := by
  rw [circuit_eq_tableCircuit]
  exact GateFilterHilbert.tableCircuit_unprepares (probability L k)
    (probability_nonneg L k) (probability_sum L k hL hd)

theorem adjoint_unprepares (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < degree L k) :
    ((GateFilterHilbert.run (GateFilterTable.circuit L k))†) (state L k) =
      GateFilterHilbert.tableInput (width L k) := by
  rw [circuit_eq_tableCircuit]
  exact GateFilterHilbert.tableCircuit_adjoint_unprepares (probability L k)
    (probability_nonneg L k) (probability_sum L k hL hd)

theorem state_norm (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < degree L k) :
    ‖state L k‖ = 1 :=
  GateFilterHilbert.tableState_norm (probability L k)
    (probability_nonneg L k) (probability_sum L k hL hd)

/-- On each original signed branch the actual physical amplitude is the
square-root absolute weight used by the original coherent-LCU proof. -/
theorem prepares_original_amplitude (L k : ℕ) (hL : 1 ≤ L)
    (hd : 0 < degree L k) (i : ReuseWeights.Index (degree L k)) :
    GateFilterHilbert.run (GateFilterTable.circuit L k)
        (GateFilterHilbert.tableInput (width L k))
        (⟨GateFilterTable.indexEmbedding (degree L k) (width L k)
          (GateFilterTable.branchBits_fits (degree L k)) i, fun _ => false⟩ :
            GateFilterHilbert.Configuration (width L k)) =
      (Real.sqrt (|ReuseWeights.weight (AveragingPolynomial.filter L k).coeff
        (degree L k) i| / 2) : ℂ) := by
  rw [prepares L k hL hd, state, GateFilterHilbert.tableState_apply]
  simp only [↓reduceIte, probability, CoherentLCU.coefficientProbability,
    GateFilterTable.coefficient_at]

/-- No amplitude leaks into a nonzero prefix workspace. -/
theorem prepares_clean_flags (L k : ℕ) (hL : 1 ≤ L)
    (hd : 0 < degree L k) (z : GateFilterHilbert.Configuration (width L k))
    (hz : z.flags ≠ (fun _ => false)) :
    GateFilterHilbert.run (GateFilterTable.circuit L k)
      (GateFilterHilbert.tableInput (width L k)) z = 0 := by
  rw [prepares L k hL hd, state, GateFilterHilbert.tableState_apply, if_neg hz]

/-- Unused physical word labels carry exactly zero amplitude, not an
additional error term or an unnormalised component. -/
theorem prepares_zero_padding (L k : ℕ) (hL : 1 ≤ L)
    (hd : 0 < degree L k) (z : GateFilterHilbert.Configuration (width L k))
    (hz : 2 * (degree L k + 1) ≤
      (GatePointerEncoding.wordEquivFin (width L k) z.slot).val) :
    GateFilterHilbert.run (GateFilterTable.circuit L k)
      (GateFilterHilbert.tableInput (width L k)) z = 0 := by
  rw [prepares L k hL hd, state, GateFilterHilbert.tableState_apply]
  have hzero : probability L k z.slot = 0 := by
    unfold probability CoherentLCU.coefficientProbability
    rw [GateFilterTable.coefficient_zero_padding _ _ _ _ _ hz]
    norm_num
  rw [hzero]
  simp

/-- Reference amplitudes are unaffected by the same list; no new gates
or controlled opaque-oracle calls are introduced by this extension. -/
theorem reference_prepares {R : Type*} [Fintype R]
    (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < degree L k) (v : R → ℂ) :
    GateFilterHilbert.referenceRun (GateFilterTable.circuit L k)
        (WithLp.toLp 2 (fun r => v r • GateFilterHilbert.tableInput (width L k))) =
      WithLp.toLp 2 (fun r => v r • state L k) := by
  rw [circuit_eq_tableCircuit]
  exact GateFilterHilbert.reference_tableCircuit_prepares (probability L k)
    (probability_nonneg L k) (probability_sum L k hL hd) v

/-- The concrete physical table layout is exactly two r-qubit registers:
the branch word and the reusable prefix flags. -/
theorem workspace_card (L k : ℕ) :
    Fintype.card (GateFilterHilbert.Configuration (width L k)) =
      2 ^ (2 * width L k) :=
  GateFilterTree.filterWorkspace_card (width L k)

/-- Joint certificate for the actual unsigned smoothing-filter preparation.
All normalisation, workspace cleanliness, inversion and list counts are
derived from the public averaging-polynomial coefficients. -/
theorem physical_preparation (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < degree L k) :
    IsUnitary (GateFilterHilbert.run (GateFilterTable.circuit L k)) ∧
    GateFilterHilbert.run (GateFilterTable.circuit L k)
      (GateFilterHilbert.tableInput (width L k)) = state L k ∧
    GateFilterHilbert.run (GateFilterTree.inverse (GateFilterTable.circuit L k))
      (state L k) = GateFilterHilbert.tableInput (width L k) ∧
    (GateFilterTable.circuit L k).length < 12 * (degree L k + 1) ∧
    (GateFilterTree.inverse (GateFilterTable.circuit L k)).length <
      12 * (degree L k + 1) ∧
    (∀ g ∈ GateFilterTable.circuit L k, g.arity ≤ 3) ∧
    Fintype.card (GateFilterHilbert.Configuration (width L k)) =
      2 ^ (2 * width L k) := by
  refine ⟨GateFilterHilbert.run_unitary _ (GateFilterTable.circuit_valid L k),
    prepares L k hL hd, unprepares L k hL hd,
    GateFilterTable.circuit_length_lt L k,
    GateFilterTable.circuit_inverse_length_lt L k, ?_, workspace_card L k⟩
  intro g hg
  exact GateFilterTree.Gate.arity_le_three g

end
end SparseHamiltonian.GateReuseFilterPhysical




/-! ### Literal bounded-arity coefficient-sign loading

Only the bottom layer of the traversal has nontrivial diagonal rotations.
Every longer control is computed and uncomputed by the existing prefix
gate lists. No arbitrary whole-register diagonal is charged as one gate.
-/

namespace SparseHamiltonian.GateFilterTree
noncomputable section
open scoped BigOperators InnerProduct

def signCoefficients (a : Bool → ℝ) : Coefficients :=
  fun b c => if b = c then CoherentLCU.coefficientPhase (a b) else 0

theorem signCoefficients_unitary (a : Bool → ℝ) :
    GatePrefixCircuit.Coefficients.IsUnitary (signCoefficients a) := by
  constructor <;> ext b c <;> cases b <;> cases c <;>
    simp [signCoefficients, Matrix.mul_apply, Matrix.conjTranspose_apply,
      CoherentLCU.coefficientPhase_conj,
      CoherentLCU.coefficientPhase_sq]

theorem idealStep_sign_single {w : ℕ} (p x : Word w) (j : Fin w)
    (a : Bool → ℝ) (c : ℂ)
    (hactive : GatePrefixCircuit.prefixBit (twistWord p x) j.val = true) :
    idealStep p j (signCoefficients a) (Finsupp.single x c) =
      CoherentLCU.coefficientPhase (a (x j)) • Finsupp.single x c := by
  classical
  have hb : idealBasis p j (signCoefficients a) x =
      CoherentLCU.coefficientPhase (a (x j)) • Finsupp.single x 1 := by
    unfold idealBasis
    rw [if_pos hactive, Finset.sum_eq_single (x j)]
    · simp [signCoefficients, Function.update_eq_self]
    · intro b hb hne
      simp only [signCoefficients, if_neg hne, zero_smul]
    · simp
  simp only [idealStep, Finsupp.linearCombination_single, hb]
  simp [Finsupp.smul_single, smul_eq_mul, mul_comm]

theorem idealStep_identity_single {w : ℕ} (p x : Word w) (j : Fin w) (c : ℂ) :
    idealStep p j GateZeroControls.identityCoefficients (Finsupp.single x c) =
      Finsupp.single x c := by
  have hc : signCoefficients (fun _ => 0) = GateZeroControls.identityCoefficients := by
    ext b d
    simp [signCoefficients, CoherentLCU.coefficientPhase,
      GateZeroControls.identityCoefficients]
  cases hp : GatePrefixCircuit.prefixBit (twistWord p x) j.val
  · exact idealStep_single_inactive p j _ x c hp
  · rw [← hc, idealStep_sign_single p x j (fun _ => 0) c hp]
    simp [CoherentLCU.coefficientPhase]

/-- Nonempty sign table: the final target bit carries a diagonal two-by-two
sign matrix, while all earlier traversal rotations are identities. -/
def signTree : (r : ℕ) → (Word (r + 1) → ℝ) → RotationTree (r + 1)
  | 0, a => .node (signCoefficients (fun b => a (Fin.cons b (fun j => Fin.elim0 j))))
      .leaf .leaf
  | r + 1, a => .node GateZeroControls.identityCoefficients
      (signTree r (fun x => a (Fin.cons false x)))
      (signTree r (fun x => a (Fin.cons true x)))

theorem signTree_valid (r : ℕ) (a : Word (r + 1) → ℝ) :
    (signTree r a).Valid := by
  induction r with
  | zero => exact ⟨signCoefficients_unitary _, trivial, trivial⟩
  | succ r ih =>
      exact ⟨GateZeroControls.identityCoefficients_unitary, ih _, ih _⟩

def readWindow {w h : ℕ} (offset : ℕ) (hfit : offset + h ≤ w)
    (x : Word w) : Word h := fun i => x ⟨offset + i.val, by omega⟩

theorem readWindow_cons {w h : ℕ} (offset : ℕ) (hfit : offset + (h + 1) ≤ w)
    (x : Word w) :
    readWindow offset hfit x = Fin.cons (x ⟨offset, by omega⟩)
      (readWindow (offset + 1) (show offset + 1 + h ≤ w by omega) x) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [readWindow, Fin.cons_succ, Fin.val_succ]
    congr 1
    apply Fin.ext
    simp only
    omega

theorem readWindow_full {w : ℕ} (x : Word w) :
    readWindow 0 (show 0 + w ≤ w by omega) x = x := by
  funext i
  simp only [readWindow, Nat.zero_add]

/-- The tree acts diagonally on every active basis word, with exactly the
coefficient sign prescribed by its actual bits. No zero-input condition is
needed; the same circuit therefore loads signs coherently. -/
theorem signTree_single {w : ℕ} (r : ℕ) (a : Word (r + 1) → ℝ)
    (offset : ℕ) (hfit : offset + (r + 1) ≤ w) (p x : Word w) (c : ℂ)
    (hactive : GatePrefixCircuit.prefixBit (twistWord p x) offset = true) :
    idealTraversal (signTree r a) offset hfit p (Finsupp.single x c) =
      CoherentLCU.coefficientPhase (a (readWindow offset hfit x)) •
        Finsupp.single x c := by
  induction r generalizing offset p with
  | zero =>
      let j : Fin w := ⟨offset, by omega⟩
      change idealStep p j
        (signCoefficients (fun b => a (Fin.cons b (fun i => Fin.elim0 i))))
        (Finsupp.single x c) = _
      rw [idealStep_sign_single p x j _ c hactive]
      have hw : Fin.cons (x j) (fun i => Fin.elim0 i) =
          readWindow offset hfit x := by
        funext i
        refine Fin.cases ?_ (fun i => Fin.elim0 i) i
        rfl
      rw [hw]
  | succ r ih =>
      let j : Fin w := ⟨offset, by omega⟩
      have hchild : offset + 1 + (r + 1) ≤ w := by omega
      let pL := Function.update p j false
      let pR := Function.update p j true
      have hread : readWindow offset hfit x =
          Fin.cons (x j) (readWindow (offset + 1) hchild x) :=
        readWindow_cons offset hfit x
      have haChild (b : Bool) (hb : x j = b) :
          GatePrefixCircuit.prefixBit
            (twistWord (Function.update p j b) x) (offset + 1) = true := by
        have he := child_prefix_active p x j b hactive
        have hu : Function.update x j b = x := by
          rw [← hb]
          exact Function.update_eq_self j x
        rw [hu] at he
        exact he
      change idealTraversal (signTree r (fun y => a (Fin.cons true y)))
          (offset + 1) hchild pR
          (idealTraversal (signTree r (fun y => a (Fin.cons false y)))
            (offset + 1) hchild pL
            (idealStep p j GateZeroControls.identityCoefficients
              (Finsupp.single x c))) = _
      rw [idealStep_identity_single]
      cases hb : x j
      · have hright : GatePrefixCircuit.prefixBit (twistWord pR x)
            (offset + 1) = false := by
          apply pathPrefix_false_of_ne pR x (offset + 1) (by omega) j
            (by simp [j])
          simp [pR, hb]
        rw [ih (fun y => a (Fin.cons false y)) (offset + 1) hchild pL
          (haChild false hb), map_smul,
          idealTraversal_single_inactive _ (offset + 1) hchild pR x c hright]
        rw [hread, hb]
      · have hleft : GatePrefixCircuit.prefixBit (twistWord pL x)
            (offset + 1) = false := by
          apply pathPrefix_false_of_ne pL x (offset + 1) (by omega) j
            (by simp [j])
          simp [pL, hb]
        rw [idealTraversal_single_inactive _ (offset + 1) hchild pL x c hleft,
          ih (fun y => a (Fin.cons true y)) (offset + 1) hchild pR
            (haChild true hb)]
        rw [hread, hb]

/-- Concrete known-sign circuit on a nonempty register. -/
def signCircuit (r : ℕ) (a : Word (r + 1) → ℝ) : List (Gate (r + 1)) :=
  compile (signTree r a) 0 (by omega) (fun _ => false)

theorem signCircuit_valid (r : ℕ) (a : Word (r + 1) → ℝ) :
    GatesValid (signCircuit r a) :=
  compile_valid _ (signTree_valid r a) 0 (by omega) (fun _ => false)

/-- Basis action of the literal elementary sign-loader, including the
clean restoration of every prefix ancilla. -/
theorem signCircuit_single (r : ℕ) (a : Word (r + 1) → ℝ)
    (x : Word (r + 1)) (c : ℂ) :
    run (signCircuit r a) (embed (fun _ => false) 0 (Finsupp.single x c)) =
      embed (fun _ => false) 0
        (CoherentLCU.coefficientPhase (a x) • Finsupp.single x c) := by
  have he := congrArg (fun F : GatePrefixCircuit.SlotState (r + 1) →ₗ[ℂ]
      State (r + 1) => F (Finsupp.single x c))
    (compile_intertwines (signTree r a) 0 (show 0 + (r + 1) ≤ r + 1 by omega)
      (fun _ => false))
  change run (signCircuit r a) (embed (fun _ => false) 0 (Finsupp.single x c)) =
    embed (fun _ => false) 0
      (idealTraversal (signTree r a) 0 (by omega) (fun _ => false)
        (Finsupp.single x c)) at he
  rw [signTree_single r a 0 _ (fun _ => false) x c rfl, readWindow_full] at he
  exact he

/-- Actual reverse-list correctness, not an assumed phase-loader inverse. -/
theorem signCircuit_inverse_single (r : ℕ) (a : Word (r + 1) → ℝ)
    (x : Word (r + 1)) (c : ℂ) :
    run (inverse (signCircuit r a))
        (embed (fun _ => false) 0
          (CoherentLCU.coefficientPhase (a x) • Finsupp.single x c)) =
      embed (fun _ => false) 0 (Finsupp.single x c) := by
  rw [← signCircuit_single r a x c]
  exact congrArg (fun F : State (r + 1) →ₗ[ℂ] State (r + 1) =>
    F (embed (fun _ => false) 0 (Finsupp.single x c)))
    (run_inverse_comp _ (signCircuit_valid r a))

theorem signCircuit_length (r : ℕ) (a : Word (r + 1) → ℝ) :
    (signCircuit r a).length = 3 * (2 ^ (r + 1) - 1) :=
  compile_length _ 0 (by omega) (fun _ => false)

/-- Diagonal specification of known coefficient signs. This is not a
primitive gate: `signCircuit_intertwines` supplies its elementary list. -/
def signMap {w : ℕ} (a : Word w → ℝ) :
    GatePrefixCircuit.SlotState w →ₗ[ℂ] GatePrefixCircuit.SlotState w :=
  Finsupp.linearCombination ℂ
    (fun x => CoherentLCU.coefficientPhase (a x) • Finsupp.single x 1)

theorem signMap_single {w : ℕ} (a : Word w → ℝ) (x : Word w) (c : ℂ) :
    signMap a (Finsupp.single x c) =
      CoherentLCU.coefficientPhase (a x) • Finsupp.single x c := by
  simp [signMap, Finsupp.smul_single, smul_eq_mul, mul_comm]

/-- Whole-space coherent action follows by linearity of the actual list,
so the sign loader is valid on every superposition of coefficient labels. -/
theorem signCircuit_intertwines (r : ℕ) (a : Word (r + 1) → ℝ) :
    (run (signCircuit r a)).comp (embed (fun _ => false) 0) =
      (embed (fun _ => false) 0).comp (signMap a) := by
  apply Finsupp.lhom_ext
  intro x c
  simp only [LinearMap.comp_apply, signMap_single]
  exact signCircuit_single r a x c

theorem signMap_sqrtTable {w : ℕ} (a p : Word w → ℝ) :
    signMap a (∑ x : Word w, Finsupp.single x (Real.sqrt (p x) : ℂ)) =
      ∑ x : Word w, Finsupp.single x
        (CoherentLCU.coefficientPhase (a x) * (Real.sqrt (p x) : ℂ)) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [signMap_single]
  simp only [Finsupp.smul_single, smul_eq_mul]

/-- The input-weight preparation followed by its actual coefficient-sign
loader is the output-weight preparation needed by coherent signed LCU. -/
def signedCoefficientCircuit (r : ℕ) (a : Word (r + 1) → ℝ) :
    List (Gate (r + 1)) :=
  compile (MassTree.fromTable (r + 1) (CoherentLCU.coefficientProbability a)
    (CoherentLCU.coefficientProbability_nonneg a)).rotations 0 (by omega)
      (fun _ => false) ++ signCircuit r a

theorem signedCoefficientCircuit_valid (r : ℕ) (a : Word (r + 1) → ℝ) :
    GatesValid (signedCoefficientCircuit r a) := by
  apply (gatesValid_append _ _).mpr
  exact ⟨(MassTree.fromTable (r + 1) (CoherentLCU.coefficientProbability a)
    (CoherentLCU.coefficientProbability_nonneg a)).compile_valid 0 (by omega)
      (fun _ => false), signCircuit_valid r a⟩

/-- Exact signed square-root amplitudes of the complete output-preparation
list, with every prefix flag returned to zero. -/
theorem signedCoefficientCircuit_prepares (r : ℕ) (a : Word (r + 1) → ℝ)
    (ha : ∑ x, |a x| = 2) :
    run (signedCoefficientCircuit r a)
        (embed (fun _ => false) 0 (Finsupp.single (fun _ => false) 1)) =
      embed (fun _ => false) 0 (∑ x : Word (r + 1), Finsupp.single x
        (CoherentLCU.coefficientPhase (a x) *
          (Real.sqrt (CoherentLCU.coefficientProbability a x) : ℂ))) := by
  rw [signedCoefficientCircuit, run_append]
  simp only [LinearMap.comp_apply]
  rw [MassTree.compile_full_table _ (CoherentLCU.coefficientProbability_nonneg a)
    (CoherentLCU.coefficientProbability_sum a ha)]
  have he := congrArg
    (fun F : GatePrefixCircuit.SlotState (r + 1) →ₗ[ℂ] State (r + 1) =>
      F (∑ x : Word (r + 1), Finsupp.single x
        (Real.sqrt (CoherentLCU.coefficientProbability a x) : ℂ)))
    (signCircuit_intertwines r a)
  simp only [LinearMap.comp_apply] at he
  rw [he, signMap_sqrtTable]

theorem signedCoefficientCircuit_unprepares (r : ℕ) (a : Word (r + 1) → ℝ)
    (ha : ∑ x, |a x| = 2) :
    run (inverse (signedCoefficientCircuit r a))
        (embed (fun _ => false) 0 (∑ x : Word (r + 1), Finsupp.single x
          (CoherentLCU.coefficientPhase (a x) *
            (Real.sqrt (CoherentLCU.coefficientProbability a x) : ℂ)))) =
      embed (fun _ => false) 0 (Finsupp.single (fun _ => false) 1) := by
  rw [← signedCoefficientCircuit_prepares r a ha]
  exact congrArg (fun F : State (r + 1) →ₗ[ℂ] State (r + 1) =>
    F (embed (fun _ => false) 0 (Finsupp.single (fun _ => false) 1)))
    (run_inverse_comp _ (signedCoefficientCircuit_valid r a))

theorem signedCoefficientCircuit_length (r : ℕ) (a : Word (r + 1) → ℝ) :
    (signedCoefficientCircuit r a).length = 6 * (2 ^ (r + 1) - 1) := by
  rw [signedCoefficientCircuit, List.length_append, compile_length, signCircuit_length]
  omega

/-- Width-indexed interface for the actual padded filter register.  The
positivity proof only excludes the empty register, where an arbitrary
global sign could not be implemented by these one-qubit instructions. -/
def signCircuitOfPos : (w : ℕ) → 0 < w → (Word w → ℝ) → List (Gate w)
  | 0, hw, _ => False.elim (by omega)
  | r + 1, _, a => signCircuit r a

theorem signCircuitOfPos_valid (w : ℕ) (hw : 0 < w) (a : Word w → ℝ) :
    GatesValid (signCircuitOfPos w hw a) := by
  cases w with
  | zero => omega
  | succ r => exact signCircuit_valid r a

theorem signCircuitOfPos_intertwines (w : ℕ) (hw : 0 < w) (a : Word w → ℝ) :
    (run (signCircuitOfPos w hw a)).comp (embed (fun _ => false) 0) =
      (embed (fun _ => false) 0).comp (signMap a) := by
  cases w with
  | zero => omega
  | succ r => exact signCircuit_intertwines r a

theorem signCircuitOfPos_single (w : ℕ) (hw : 0 < w) (a : Word w → ℝ)
    (x : Word w) (c : ℂ) :
    run (signCircuitOfPos w hw a) (embed (fun _ => false) 0 (Finsupp.single x c)) =
      embed (fun _ => false) 0
        (CoherentLCU.coefficientPhase (a x) • Finsupp.single x c) := by
  cases w with
  | zero => omega
  | succ r => exact signCircuit_single r a x c

theorem signCircuitOfPos_length (w : ℕ) (hw : 0 < w) (a : Word w → ℝ) :
    (signCircuitOfPos w hw a).length = 3 * (2 ^ w - 1) := by
  cases w with
  | zero => omega
  | succ r => exact signCircuit_length r a

end
end SparseHamiltonian.GateFilterTree


/-! ### The actual sign-loader on the physical table register -/

namespace SparseHamiltonian.GateFilterHilbert
noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct

/-- Physical clean-basis action of the literal sign traversal. -/
theorem signCircuit_clean_single (r : ℕ) (a : GateFilterTree.Word (r + 1) → ℝ)
    (x : GateFilterTree.Word (r + 1)) (c : ℂ) :
    run (GateFilterTree.signCircuit r a) (cleanState (Finsupp.single x c)) =
      CoherentLCU.coefficientPhase (a x) • cleanState (Finsupp.single x c) := by
  rw [cleanState, run_coordinates, GateFilterTree.signCircuit_single]
  simp only [map_smul]

theorem signCircuit_clean_state (r : ℕ) (a : GateFilterTree.Word (r + 1) → ℝ)
    (v : GatePrefixCircuit.SlotState (r + 1)) :
    run (GateFilterTree.signCircuit r a) (cleanState v) =
      cleanState (GateFilterTree.signMap a v) := by
  rw [cleanState, run_coordinates]
  exact congrArg coordinates
    (congrArg (fun L : GatePrefixCircuit.SlotState (r + 1) →ₗ[ℂ]
        GateFilterTree.State (r + 1) => L v)
      (GateFilterTree.signCircuit_intertwines r a))

/-- Signs multiply arbitrary table amplitudes coherently; `v` need not
be a prepared probability table or a normalised state. -/
theorem signCircuit_clean_sum (r : ℕ) (a : GateFilterTree.Word (r + 1) → ℝ)
    (v : GateFilterTree.Word (r + 1) → ℂ) :
    run (GateFilterTree.signCircuit r a)
        (cleanState (∑ x, Finsupp.single x (v x))) =
      cleanState (∑ x, Finsupp.single x
        (CoherentLCU.coefficientPhase (a x) * v x)) := by
  classical
  rw [signCircuit_clean_state]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [GateFilterTree.signMap_single]
  simp only [Finsupp.smul_single, smul_eq_mul]

/-- The desired signed square-root amplitudes in a clean physical register. -/
def signedTableState (r : ℕ) (a p : GateFilterTree.Word (r + 1) → ℝ) :
    Physical (r + 1) :=
  cleanState (∑ x, Finsupp.single x
    (CoherentLCU.coefficientPhase (a x) * (Real.sqrt (p x) : ℂ)))

theorem signedTableState_apply (r : ℕ) (a p : GateFilterTree.Word (r + 1) → ℝ)
    (z : Configuration (r + 1)) :
    signedTableState r a p z = if z.flags = (fun _ => false)
      then CoherentLCU.coefficientPhase (a z.slot) * (Real.sqrt (p z.slot) : ℂ)
      else 0 := by
  classical
  rw [signedTableState, cleanState_apply]
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- Prepare absolute amplitudes, then load their known signs by the actual
bounded-arity list. Neither operation is an assumed table loader. -/
def signedTableCircuit (r : ℕ) (a p : GateFilterTree.Word (r + 1) → ℝ)
    (hp : ∀ x, 0 ≤ p x) : List (GateFilterTree.Gate (r + 1)) :=
  tableCircuit p hp ++ GateFilterTree.signCircuit r a

theorem signedTableCircuit_valid (r : ℕ) (a p : GateFilterTree.Word (r + 1) → ℝ)
    (hp : ∀ x, 0 ≤ p x) :
    GateFilterTree.GatesValid (signedTableCircuit r a p hp) :=
  (GateFilterTree.gatesValid_append _ _).mpr
    ⟨tableCircuit_valid p hp, GateFilterTree.signCircuit_valid r a⟩

theorem signedTableCircuit_unitary (r : ℕ) (a p : GateFilterTree.Word (r + 1) → ℝ)
    (hp : ∀ x, 0 ≤ p x) : IsUnitary (run (signedTableCircuit r a p hp)) :=
  run_unitary _ (signedTableCircuit_valid r a p hp)

/-- Full physical signed-state preparation with all temporary path flags
returned to zero. -/
theorem signedTableCircuit_prepares (r : ℕ) (a p : GateFilterTree.Word (r + 1) → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hmass : ∑ x, p x = 1) :
    run (signedTableCircuit r a p hp) (tableInput (r + 1)) =
      signedTableState r a p := by
  rw [signedTableCircuit, run_append]
  change run (GateFilterTree.signCircuit r a)
    (run (tableCircuit p hp) (tableInput (r + 1))) = _
  rw [tableCircuit_prepares p hp hmass]
  exact signCircuit_clean_sum r a (fun x => (Real.sqrt (p x) : ℂ))

theorem signedTableState_norm (r : ℕ) (a p : GateFilterTree.Word (r + 1) → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hmass : ∑ x, p x = 1) :
    ‖signedTableState r a p‖ = 1 := by
  rw [← signedTableCircuit_prepares r a p hp hmass]
  have hi : ((run (signedTableCircuit r a p hp))†).comp
      (run (signedTableCircuit r a p hp)) = 1 :=
    (signedTableCircuit_unitary r a p hp).1
  rw [(norm_map_iff_adjoint_comp_self _).mpr hi, tableInput_norm]

/-- The inverse is the literal reversed list, with the same elementary
gate count, and equals the Hilbert-space adjoint on every input. -/
theorem signedTableCircuit_unprepares (r : ℕ) (a p : GateFilterTree.Word (r + 1) → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hmass : ∑ x, p x = 1) :
    run (GateFilterTree.inverse (signedTableCircuit r a p hp))
        (signedTableState r a p) = tableInput (r + 1) := by
  rw [run_inverse, ← signedTableCircuit_prepares r a p hp hmass]
  exact congrArg (fun U : Physical (r + 1) →L[ℂ] Physical (r + 1) =>
    U (tableInput (r + 1))) (signedTableCircuit_unitary r a p hp).1

theorem signedTableCircuit_lengths (r : ℕ) (a p : GateFilterTree.Word (r + 1) → ℝ)
    (hp : ∀ x, 0 ≤ p x) :
    (signedTableCircuit r a p hp).length = 6 * (2 ^ (r + 1) - 1) ∧
    (GateFilterTree.inverse (signedTableCircuit r a p hp)).length =
      6 * (2 ^ (r + 1) - 1) := by
  have hf : (signedTableCircuit r a p hp).length = 6 * (2 ^ (r + 1) - 1) := by
    rw [signedTableCircuit, List.length_append, tableCircuit_length,
      GateFilterTree.signCircuit_length]
    omega
  exact ⟨hf, by rw [GateFilterTree.inverse_length, hf]⟩

/-- Reference amplitudes are unchanged, with no dependence of the gate
count on the reference dimension. -/
theorem reference_signedTableCircuit_prepares {R : Type*} [Fintype R]
    (r : ℕ) (a p : GateFilterTree.Word (r + 1) → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hmass : ∑ x, p x = 1) (v : R → ℂ) :
    referenceRun (signedTableCircuit r a p hp)
        (WithLp.toLp 2 (fun q => v q • tableInput (r + 1))) =
      WithLp.toLp 2 (fun q => v q • signedTableState r a p) := by
  apply PiLp.ext
  intro q
  rw [referenceRun_apply]
  change run (signedTableCircuit r a p hp) (v q • tableInput (r + 1)) =
    v q • signedTableState r a p
  rw [map_smul, signedTableCircuit_prepares r a p hp hmass]

end
end SparseHamiltonian.GateFilterHilbert


/-! ### The actual signed smoothing-filter output preparation -/

namespace SparseHamiltonian.GateFilterHilbert
noncomputable section

/-- The physical sign-loader interface on any nonempty branch register. -/
theorem signCircuitOfPos_clean_state (w : ℕ) (hw : 0 < w)
    (a : GateFilterTree.Word w → ℝ) (v : GatePrefixCircuit.SlotState w) :
    run (GateFilterTree.signCircuitOfPos w hw a) (cleanState v) =
      cleanState (GateFilterTree.signMap a v) := by
  cases w with
  | zero => omega
  | succ r => exact signCircuit_clean_state r a v

end
end SparseHamiltonian.GateFilterHilbert

namespace SparseHamiltonian.GateReuseFilterPhysical
noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped BigOperators InnerProduct

/-- The original signed coefficients on their explicit physical labels. -/
def actualCoefficient (L k : ℕ) : GateFilterTable.Word (width L k) → ℝ :=
  GateFilterTable.coefficient (AveragingPolynomial.filter L k).coeff
    (degree L k) (width L k) (GateFilterTable.branchBits_fits (degree L k))

/-- The full output list first prepares absolute amplitudes and then loads
the known signs with bounded-arity instructions on the same register. -/
def outputCircuit (L k : ℕ) : List (GateFilterTree.Gate (width L k)) :=
  GateFilterTable.circuit L k ++
    GateFilterTree.signCircuitOfPos (width L k)
      (GateFilterTable.branchBits_pos (degree L k)) (actualCoefficient L k)

/-- Exact signed target, including the clean prefix workspace. -/
def signedState (L k : ℕ) : GateFilterHilbert.Physical (width L k) :=
  GateFilterHilbert.cleanState (∑ x, Finsupp.single x
    (CoherentLCU.coefficientPhase (actualCoefficient L k x) *
      (Real.sqrt (probability L k x) : ℂ)))

theorem outputCircuit_valid (L k : ℕ) :
    GateFilterTree.GatesValid (outputCircuit L k) :=
  (GateFilterTree.gatesValid_append _ _).mpr
    ⟨GateFilterTable.circuit_valid L k,
      GateFilterTree.signCircuitOfPos_valid _ _ _⟩

theorem outputCircuit_unitary (L k : ℕ) :
    IsUnitary (GateFilterHilbert.run (outputCircuit L k)) :=
  GateFilterHilbert.run_unitary _ (outputCircuit_valid L k)

/-- There is no remaining sign-loader or preparation-correctness premise:
both parts are the explicitly compiled elementary gate lists. -/
theorem outputCircuit_prepares (L k : ℕ) (hL : 1 ≤ L)
    (hd : 0 < degree L k) :
    GateFilterHilbert.run (outputCircuit L k)
      (GateFilterHilbert.tableInput (width L k)) = signedState L k := by
  rw [outputCircuit, GateFilterHilbert.run_append]
  change GateFilterHilbert.run
    (GateFilterTree.signCircuitOfPos (width L k)
      (GateFilterTable.branchBits_pos (degree L k)) (actualCoefficient L k))
    (GateFilterHilbert.run (GateFilterTable.circuit L k)
      (GateFilterHilbert.tableInput (width L k))) = _
  rw [prepares L k hL hd, state, GateFilterHilbert.tableState,
    GateFilterHilbert.signCircuitOfPos_clean_state]
  exact congrArg GateFilterHilbert.cleanState
    (GateFilterTree.signMap_sqrtTable (actualCoefficient L k) (probability L k))

/-- Literal reversal includes both the sign traversal and the probability
traversal; no extra inverse-preparation interface is supplied. -/
theorem outputCircuit_unprepares (L k : ℕ) (hL : 1 ≤ L)
    (hd : 0 < degree L k) :
    GateFilterHilbert.run (GateFilterTree.inverse (outputCircuit L k))
      (signedState L k) = GateFilterHilbert.tableInput (width L k) := by
  rw [GateFilterHilbert.run_inverse, ← outputCircuit_prepares L k hL hd]
  exact congrArg
    (fun U : GateFilterHilbert.Physical (width L k) →L[ℂ]
        GateFilterHilbert.Physical (width L k) =>
      U (GateFilterHilbert.tableInput (width L k)))
    (outputCircuit_unitary L k).1

theorem outputCircuit_adjoint_unprepares (L k : ℕ) (hL : 1 ≤ L)
    (hd : 0 < degree L k) :
    ((GateFilterHilbert.run (outputCircuit L k))†) (signedState L k) =
      GateFilterHilbert.tableInput (width L k) := by
  rw [← GateFilterHilbert.run_inverse]
  exact outputCircuit_unprepares L k hL hd

theorem signedState_norm (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < degree L k) :
    ‖signedState L k‖ = 1 := by
  rw [← outputCircuit_prepares L k hL hd]
  have hi : ((GateFilterHilbert.run (outputCircuit L k))†).comp
      (GateFilterHilbert.run (outputCircuit L k)) = 1 :=
    (outputCircuit_unitary L k).1
  rw [(norm_map_iff_adjoint_comp_self _).mpr hi, GateFilterHilbert.tableInput_norm]

theorem signedState_apply (L k : ℕ)
    (z : GateFilterHilbert.Configuration (width L k)) :
    signedState L k z = if z.flags = (fun _ => false)
      then CoherentLCU.coefficientPhase (actualCoefficient L k z.slot) *
        (Real.sqrt (probability L k z.slot) : ℂ) else 0 := by
  classical
  rw [signedState, GateFilterHilbert.cleanState_apply]
  simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem output_original_amplitude (L k : ℕ) (hL : 1 ≤ L)
    (hd : 0 < degree L k) (i : ReuseWeights.Index (degree L k)) :
    GateFilterHilbert.run (outputCircuit L k)
        (GateFilterHilbert.tableInput (width L k))
        (⟨GateFilterTable.indexEmbedding (degree L k) (width L k)
          (GateFilterTable.branchBits_fits (degree L k)) i, fun _ => false⟩ :
            GateFilterHilbert.Configuration (width L k)) =
      CoherentLCU.coefficientPhase
        (ReuseWeights.weight (AveragingPolynomial.filter L k).coeff (degree L k) i) *
      (Real.sqrt (|ReuseWeights.weight (AveragingPolynomial.filter L k).coeff
        (degree L k) i| / 2) : ℂ) := by
  rw [outputCircuit_prepares L k hL hd, signedState_apply]
  simp only [↓reduceIte, actualCoefficient, probability,
    CoherentLCU.coefficientProbability, GateFilterTable.coefficient_at]

theorem output_clean_flags (L k : ℕ) (hL : 1 ≤ L)
    (hd : 0 < degree L k) (z : GateFilterHilbert.Configuration (width L k))
    (hz : z.flags ≠ (fun _ => false)) :
    GateFilterHilbert.run (outputCircuit L k)
      (GateFilterHilbert.tableInput (width L k)) z = 0 := by
  rw [outputCircuit_prepares L k hL hd, signedState_apply, if_neg hz]

theorem output_zero_padding (L k : ℕ) (hL : 1 ≤ L)
    (hd : 0 < degree L k) (z : GateFilterHilbert.Configuration (width L k))
    (hz : 2 * (degree L k + 1) ≤
      (GatePointerEncoding.wordEquivFin (width L k) z.slot).val) :
    GateFilterHilbert.run (outputCircuit L k)
      (GateFilterHilbert.tableInput (width L k)) z = 0 := by
  rw [outputCircuit_prepares L k hL hd, signedState_apply]
  have hzero : probability L k z.slot = 0 := by
    unfold probability CoherentLCU.coefficientProbability
    rw [GateFilterTable.coefficient_zero_padding _ _ _ _ _ hz]
    norm_num
  rw [hzero]
  simp

theorem reference_output_prepares {R : Type*} [Fintype R]
    (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < degree L k) (v : R → ℂ) :
    GateFilterHilbert.referenceRun (outputCircuit L k)
        (WithLp.toLp 2 (fun r => v r • GateFilterHilbert.tableInput (width L k))) =
      WithLp.toLp 2 (fun r => v r • signedState L k) := by
  apply PiLp.ext
  intro r
  rw [GateFilterHilbert.referenceRun_apply]
  change GateFilterHilbert.run (outputCircuit L k)
    (v r • GateFilterHilbert.tableInput (width L k)) = v r • signedState L k
  rw [map_smul, outputCircuit_prepares L k hL hd]

theorem outputCircuit_length (L k : ℕ) :
    (outputCircuit L k).length = 6 * (2 ^ width L k - 1) := by
  rw [outputCircuit, List.length_append, GateFilterTable.circuit_length,
    GateFilterTree.signCircuitOfPos_length]
  change 3 * (2 ^ width L k - 1) + 3 * (2 ^ width L k - 1) =
    6 * (2 ^ width L k - 1)
  omega

theorem outputCircuit_length_lt (L k : ℕ) :
    (outputCircuit L k).length < 24 * (degree L k + 1) := by
  rw [outputCircuit_length]
  have := GateFilterTable.branchBits_small (degree L k)
  change 6 * (2 ^ GateFilterTable.branchBits (degree L k) - 1) <
    24 * (degree L k + 1)
  omega

theorem outputCircuit_inverse_length_lt (L k : ℕ) :
    (GateFilterTree.inverse (outputCircuit L k)).length <
      24 * (degree L k + 1) := by
  rw [GateFilterTree.inverse_length]
  exact outputCircuit_length_lt L k

/-- Paired concrete coefficient preparations use the same 2r-bit physical
register. All signed output costs include the explicit sign-loader list. -/
theorem paired_preparation (L k : ℕ) (hL : 1 ≤ L) (hd : 0 < degree L k) :
    GateFilterHilbert.run (GateFilterTable.circuit L k)
      (GateFilterHilbert.tableInput (width L k)) = state L k ∧
    GateFilterHilbert.run (outputCircuit L k)
      (GateFilterHilbert.tableInput (width L k)) = signedState L k ∧
    GateFilterHilbert.run (GateFilterTree.inverse (outputCircuit L k))
      (signedState L k) = GateFilterHilbert.tableInput (width L k) ∧
    (GateFilterTable.circuit L k).length < 12 * (degree L k + 1) ∧
    (outputCircuit L k).length < 24 * (degree L k + 1) ∧
    (∀ g ∈ outputCircuit L k, g.arity ≤ 3) ∧
    Fintype.card (GateFilterHilbert.Configuration (width L k)) =
      2 ^ (2 * width L k) := by
  refine ⟨prepares L k hL hd, outputCircuit_prepares L k hL hd,
    outputCircuit_unprepares L k hL hd, GateFilterTable.circuit_length_lt L k,
    outputCircuit_length_lt L k, ?_, workspace_card L k⟩
  intro g hg
  exact GateFilterTree.Gate.arity_le_three g

end
end SparseHamiltonian.GateReuseFilterPhysical



/-! ### A clean extra control for a known Toffoli

This is one reusable local component of a future coherent range-control
compiler, not an implementation of an entire controlled range preparation.
The five wires have fixed physical roles. Each literal instruction touches
only its displayed two controls and one target.
-/

namespace SparseHamiltonian.GateKnownControl
noncomputable section
open ContinuousLinearMap OracleCircuit

inductive Wire
  | enable | first | second | target | scratch
  deriving DecidableEq, Fintype

abbrev Register := Wire → Bool
abbrev Physical := EuclideanSpace ℂ Register

inductive Gate
  | compute | applyTarget
  deriving DecidableEq

def Gate.controls : Gate → Wire × Wire
  | .compute => (.enable, .first)
  | .applyTarget => (.scratch, .second)

def Gate.target : Gate → Wire
  | .compute => .scratch
  | .applyTarget => .target

/-- A literal positive-control Toffoli, not a general register operation. -/
def Gate.eval (g : Gate) (z : Register) : Register :=
  Function.update z g.target
    (if z g.controls.1 && z g.controls.2 then !(z g.target) else z g.target)

def Gate.arity (_g : Gate) : ℕ := 3

theorem Gate.arity_eq_three (g : Gate) : g.arity = 3 := rfl

theorem Gate.controls_distinct (g : Gate) :
    g.controls.1 ≠ g.controls.2 ∧
      g.controls.1 ≠ g.target ∧ g.controls.2 ≠ g.target := by
  cases g <;> simp [Gate.controls, Gate.target]

theorem Gate.eval_target (g : Gate) (z : Register) :
    g.eval z g.target =
      if z g.controls.1 && z g.controls.2 then !(z g.target) else z g.target := by
  simp only [Gate.eval, Function.update_self]

theorem Gate.eval_other (g : Gate) (z : Register) (w : Wire) (hw : w ≠ g.target) :
    g.eval z w = z w := by
  simp only [Gate.eval, Function.update_of_ne hw]

/-- The controls cannot be overwritten by the local Toffoli. -/
theorem Gate.eval_controls (g : Gate) (z : Register) :
    g.eval z g.controls.1 = z g.controls.1 ∧
      g.eval z g.controls.2 = z g.controls.2 :=
  ⟨g.eval_other z _ g.controls_distinct.2.1,
    g.eval_other z _ g.controls_distinct.2.2⟩

theorem Gate.eval_involutive (g : Gate) : Function.Involutive g.eval := by
  intro z
  funext w
  by_cases hw : w = g.target
  · subst w
    simp only [Gate.eval_target, (g.eval_controls z).1, (g.eval_controls z).2]
    cases h : z g.controls.1 && z g.controls.2 <;> simp
  · rw [g.eval_other _ _ hw, g.eval_other _ _ hw]

def exec : List Gate → Register → Register
  | [], z => z
  | g :: gs, z => exec gs (g.eval z)

/-- Compute enable-and-first, use it as a control with second, uncompute. -/
def circuit : List Gate := [.compute, .applyTarget, .compute]

theorem circuit_length : circuit.length = 3 := rfl

theorem circuit_reverse : circuit.reverse = circuit := rfl

/-- Clean scratch is restored; all three logical controls are retained,
and only the intended target receives the three-control conjunction. -/
theorem circuit_clean (z : Register) (hz : z .scratch = false) :
    exec circuit z = Function.update z .target
      (if z .enable && z .first && z .second then !(z .target) else z .target) := by
  cases he : z .enable <;> cases ha : z .first <;> cases hb : z .second <;>
    funext w <;> cases w <;>
    simp [circuit, exec, Gate.eval, Gate.controls, Gate.target, he, ha, hb, hz]

theorem circuit_scratch_clean (z : Register) (hz : z .scratch = false) :
    exec circuit z .scratch = false := by
  rw [circuit_clean z hz]
  simpa using hz

theorem circuit_inputs (z : Register) (hz : z .scratch = false) :
    exec circuit z .enable = z .enable ∧
    exec circuit z .first = z .first ∧ exec circuit z .second = z .second := by
  rw [circuit_clean z hz]
  simp

/-- The same literal palindrome is a true inverse on the entire register,
including dirty scratch. Clean scratch is needed only for the advertised
three-controlled action, not for reversibility. -/
theorem circuit_involutive : Function.Involutive (exec circuit) := by
  intro z
  change Gate.eval .compute (Gate.eval .applyTarget (Gate.eval .compute
    (Gate.eval .compute (Gate.eval .applyTarget (Gate.eval .compute z))))) = z
  rw [Gate.eval_involutive .compute, Gate.eval_involutive .applyTarget,
    Gate.eval_involutive .compute]

def Gate.equiv (g : Gate) : Register ≃ Register where
  toFun := g.eval
  invFun := g.eval
  left_inv := g.eval_involutive
  right_inv := g.eval_involutive

def circuitEquiv : Register ≃ Register where
  toFun := exec circuit
  invFun := exec circuit
  left_inv := circuit_involutive
  right_inv := circuit_involutive

def Gate.operator (g : Gate) : Physical →L[ℂ] Physical :=
  (LookupOracle.permutationUnitary g.equiv).toLinearIsometry.toContinuousLinearMap

def run : List Gate → Physical →L[ℂ] Physical
  | [] => 1
  | g :: gs => run gs ∘L g.operator

theorem Gate.operator_single (g : Gate) (z : Register) (c : ℂ) :
    g.operator (EuclideanSpace.single z c) = EuclideanSpace.single (g.eval z) c :=
  LookupOracle.permutationUnitary_single g.equiv z c

theorem run_single (gs : List Gate) (z : Register) (c : ℂ) :
    run gs (EuclideanSpace.single z c) = EuclideanSpace.single (exec gs z) c := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih =>
      simp only [run, ContinuousLinearMap.comp_apply, Gate.operator_single,
        ih, exec]

/-- The physical operator is the product of exactly the three elementary
Toffolis above. Its permutation interpretation is proved afterwards. -/
theorem run_circuit_eq : run circuit =
    (LookupOracle.permutationUnitary circuitEquiv).toLinearIsometry.toContinuousLinearMap := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun Register ℂ).toBasis.ext
  intro z
  change run circuit (EuclideanSpace.basisFun Register ℂ z) =
    LookupOracle.permutationUnitary circuitEquiv (EuclideanSpace.basisFun Register ℂ z)
  rw [EuclideanSpace.basisFun_apply, run_single, LookupOracle.permutationUnitary_single]
  rfl

theorem run_circuit_unitary : IsUnitary (run circuit) := by
  rw [run_circuit_eq]
  exact LookupOracle.permutationUnitary_unitary circuitEquiv

theorem run_circuit_clean (z : Register) (hz : z .scratch = false) (c : ℂ) :
    run circuit (EuclideanSpace.single z c) =
      EuclideanSpace.single (Function.update z .target
        (if z .enable && z .first && z .second then !(z .target) else z .target)) c := by
  rw [run_single, circuit_clean z hz]

/-- Literal reversal, on the actual physical space, is the inverse on all
amplitudes. In particular it also reverses coherent superpositions. -/
theorem run_circuit_inverse : (run circuit) ∘L (run circuit) = 1 := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun Register ℂ).toBasis.ext
  intro z
  change run circuit (run circuit (EuclideanSpace.basisFun Register ℂ z)) =
    EuclideanSpace.basisFun Register ℂ z
  rw [EuclideanSpace.basisFun_apply, run_single, run_single, circuit_involutive]

end
end SparseHamiltonian.GateKnownControl



/-! ### Addressing the control primitive inside a larger qubit register -/

namespace SparseHamiltonian.GateKnownControl
noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- The five selected wires are actual qubit addresses; this restriction
does not implement a register permutation or hide any additional gate. -/
def restrict (e : Wire ↪ ι) (z : ι → Bool) : Register := fun w => z (e w)

/-- The same elementary Toffoli at its three chosen physical addresses. -/
def Gate.evalAt (g : Gate) (e : Wire ↪ ι) (z : ι → Bool) : ι → Bool :=
  Function.update z (e g.target)
    (if z (e g.controls.1) && z (e g.controls.2)
      then !(z (e g.target)) else z (e g.target))

theorem Gate.evalAt_restrict (g : Gate) (e : Wire ↪ ι) (z : ι → Bool) :
    restrict e (g.evalAt e z) = g.eval (restrict e z) := by
  funext w
  by_cases hw : w = g.target
  · subst w
    simp [restrict, Gate.evalAt, Gate.eval]
  · have he : e w ≠ e g.target := fun h => hw (e.injective h)
    simp [restrict, Gate.evalAt, Gate.eval, hw, he]

/-- Every instruction fixes every unaddressed wire. -/
theorem Gate.evalAt_other (g : Gate) (e : Wire ↪ ι) (z : ι → Bool)
    (i : ι) (hi : i ≠ e g.target) : g.evalAt e z i = z i := by
  simp only [Gate.evalAt, Function.update_of_ne hi]

def execAt (e : Wire ↪ ι) : List Gate → (ι → Bool) → (ι → Bool)
  | [], z => z
  | g :: gs, z => execAt e gs (g.evalAt e z)

theorem execAt_restrict (e : Wire ↪ ι) (gs : List Gate) (z : ι → Bool) :
    restrict e (execAt e gs z) = exec gs (restrict e z) := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih =>
      change restrict e (execAt e gs (g.evalAt e z)) =
        exec gs (g.eval (restrict e z))
      rw [ih, Gate.evalAt_restrict]

theorem execAt_outside (e : Wire ↪ ι) (gs : List Gate) (z : ι → Bool)
    (i : ι) (hi : ∀ w, e w ≠ i) : execAt e gs z i = z i := by
  induction gs generalizing z with
  | nil => rfl
  | cons g gs ih =>
      change execAt e gs (g.evalAt e z) i = z i
      rw [ih]
      exact g.evalAt_other e z i (Ne.symm (hi g.target))

/-- The three actual gates implement the extra control in any larger
register. All other data wires and the clean scratch are retained exactly. -/
theorem circuitAt_clean (e : Wire ↪ ι) (z : ι → Bool)
    (hz : z (e .scratch) = false) :
    execAt e circuit z = Function.update z (e .target)
      (if z (e .enable) && z (e .first) && z (e .second)
        then !(z (e .target)) else z (e .target)) := by
  classical
  funext i
  by_cases hi : ∃ w, e w = i
  · obtain ⟨w, rfl⟩ := hi
    have h := congrFun (execAt_restrict e circuit z) w
    rw [circuit_clean (restrict e z) hz] at h
    change execAt e circuit z (e w) = _ at h
    by_cases hw : w = .target
    · subst w
      simpa [restrict] using h
    · have he : e w ≠ e .target := fun hh => hw (e.injective hh)
      simpa [restrict, hw, he] using h
  · have hout : ∀ w, e w ≠ i := by
      intro w hw
      exact hi ⟨w, hw⟩
    rw [execAt_outside e circuit z i hout]
    simp only [Function.update_of_ne (Ne.symm (hout .target))]

/-- Reversibility also holds in the ambient register and on dirty scratch;
cleanliness is required for the advertised extra-control action only. -/
theorem circuitAt_involutive (e : Wire ↪ ι) :
    Function.Involutive (execAt e circuit) := by
  classical
  intro z
  funext i
  by_cases hi : ∃ w, e w = i
  · obtain ⟨w, rfl⟩ := hi
    have h : restrict e (execAt e circuit (execAt e circuit z)) = restrict e z := by
      calc
        _ = exec circuit (restrict e (execAt e circuit z)) :=
          execAt_restrict e circuit (execAt e circuit z)
        _ = exec circuit (exec circuit (restrict e z)) :=
          congrArg (exec circuit) (execAt_restrict e circuit z)
        _ = restrict e z := circuit_involutive (restrict e z)
    exact congrFun h w
  · have hout : ∀ w, e w ≠ i := by
      intro w hw
      exact hi ⟨w, hw⟩
    rw [execAt_outside e circuit _ i hout, execAt_outside e circuit z i hout]

end
end SparseHamiltonian.GateKnownControl
