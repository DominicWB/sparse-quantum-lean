import GateEfficientHamiltonian.GateUniformRange
/-!
# The two dyadic frames on one physical sector workspace

The previous component lemmas used an `m`-bit private register for each
frame and an `(m+1)`-bit register for the central rotation.  This section
puts the public/private sector bit and the `m` clock bits on one common
workspace.  Prefix computation is shared by both sectors.  Each nontrivial
frame rotation is additionally controlled by the known sector bit, so it is
a bounded-arity gate rather than an uncontrolled whole-register operator.

Only the two frames are composed here.  The next construction adds the
locally controlled central rotation between them on this same workspace.
-/

namespace SparseHamiltonian.GatePhysicalBoundary

noncomputable section

open GatePrefixCircuit

/-- One sector qubit tensored with the already explicit slot-and-prefix
workspace.  Writing the tensor/direct sum as a Boolean-indexed family keeps
the two sector components visible in the correctness proof. -/
abbrev State (m : ℕ) := Bool → GatePrefixCircuit.State m

/-- Block-diagonal action on the sector register. -/
def diagonal {m : ℕ}
    (A : Bool → GatePrefixCircuit.State m →ₗ[ℂ] GatePrefixCircuit.State m) :
    State m →ₗ[ℂ] State m where
  toFun v b := A b (v b)
  map_add' v w := by
    funext b
    exact map_add (A b) (v b) (w b)
  map_smul' z v := by
    funext b
    exact map_smul (A b) z (v b)

/-- The final locally available zero-prefix flag.  At positive width it
reads only the last computed prefix flag and the last slot bit. -/
def endControl : {m : ℕ} → GatePrefixCircuit.Configuration m → Bool
  | 0, _ => true
  | m + 1, z => z.flags (Fin.last m) && !(z.slot (Fin.last m))

theorem endControl_encoded {m : ℕ} (x : GatePrefixCircuit.Word m) :
    endControl (GatePrefixCircuit.encoded m x) =
      GatePrefixCircuit.prefixBit x m := by
  cases m with
  | zero => rfl
  | succ m =>
      simp [endControl, GatePrefixCircuit.encoded, GatePrefixCircuit.prefixBit,
        GatePrefixCircuit.bit]; rfl

/-- A sector rotation conditioned on the locally stored all-zero flag.  Its
coordinate definition makes clear that it couples only the sector qubit and
leaves the complete lower workspace configuration unchanged. -/
def centralAction {m : ℕ} (a : Coefficients) : State m →ₗ[ℂ] State m where
  toFun v b := Finsupp.equivFunOnFinite.symm (fun z =>
    if endControl z then ∑ t : Bool, a b t * v t z else v b z)
  map_add' v w := by
    funext b
    apply Finsupp.ext
    intro z
    by_cases h : endControl z
    · simp [h, mul_add, Finset.sum_add_distrib]
    · simp [h]
  map_smul' q v := by
    funext b
    apply Finsupp.ext
    intro z
    by_cases h : endControl z
    · simp [h]
      ring
    · simp [h]

@[simp] theorem centralAction_apply {m : ℕ} (a : Coefficients) (v : State m)
    (b : Bool) (z : GatePrefixCircuit.Configuration m) :
    centralAction a v b z =
      if endControl z then ∑ t : Bool, a b t * v t z else v b z := rfl

/-- Actual bounded-arity gates used by the common boundary circuit.  A prefix
gate reads at most two Boolean wires.  A private rotation reads the sector
bit, one clean prefix flag, and one target bit.  A central rotation reads the
sector target and the final two-bit zero-prefix control. -/
inductive Gate (m : ℕ)
  | prefixBit (j : Fin m)
  | privateRotate (j : Fin m) (a : Coefficients)
  | central (a : Coefficients)

/-- Exact linear semantics of the physical gates.  No opaque controlled
oracle occurs: the only additional control is the known sector bit. -/
def Gate.eval {m : ℕ} : Gate m → State m →ₗ[ℂ] State m
  | .prefixBit j => diagonal (fun _ => GatePrefixCircuit.Gate.eval (.prefixBit j))
  | .privateRotate j a => diagonal (fun b =>
      if b then GatePrefixCircuit.Gate.eval (.rotate j a) else LinearMap.id)
  | .central a => centralAction a

/-- Compile one gate from the clean prefix circuit into the common physical
workspace. -/
def liftGate {m : ℕ} : GatePrefixCircuit.Gate m → Gate m
  | .prefixBit j => .prefixBit j
  | .rotate j a => .privateRotate j a

/-- On the public sector, every private rotation is the identity.  This
shadow list is used only in the proof; the executed list is `liftCircuit`. -/
def publicShadow {m : ℕ} : GatePrefixCircuit.Gate m → GatePrefixCircuit.Gate m
  | .prefixBit j => .prefixBit j
  | .rotate j _ => .rotate j GateZeroControls.identityCoefficients

/-- Compile a complete prefix-gate list without introducing a
whole-register primitive. -/
def liftCircuit {m : ℕ} (gs : List (GatePrefixCircuit.Gate m)) : List (Gate m) :=
  gs.map liftGate

/-- Execute physical gates from left to right. -/
def run {m : ℕ} : List (Gate m) → State m →ₗ[ℂ] State m
  | [] => LinearMap.id
  | g :: gs => (run gs).comp g.eval

@[simp] theorem run_nil {m : ℕ} : run ([] : List (Gate m)) = LinearMap.id := rfl

@[simp] theorem run_append {m : ℕ} (gs hs : List (Gate m)) :
    run (gs ++ hs) = (run hs).comp (run gs) := by
  induction gs with
  | nil => simp [run]
  | cons g gs ih => simp [run, ih, LinearMap.comp_assoc]

@[simp] theorem eval_lift_true {m : ℕ} (g : GatePrefixCircuit.Gate m)
    (v : State m) :
    (liftGate g).eval v true = g.eval (v true) := by
  cases g <;> rfl

theorem eval_lift_false {m : ℕ} (g : GatePrefixCircuit.Gate m)
    (v : State m) :
    (liftGate g).eval v false = (publicShadow g).eval (v false) := by
  cases g with
  | prefixBit j => rfl
  | rotate j a =>
      change (LinearMap.id : GatePrefixCircuit.State m →ₗ[ℂ]
        GatePrefixCircuit.State m) (v false) =
          GatePrefixCircuit.Gate.eval
            (.rotate j GateZeroControls.identityCoefficients) (v false)
      have hi : GateZeroControls.identityCoefficients =
          (1 : Matrix Bool Bool ℂ) := rfl
      rw [hi, GatePrefixCircuit.rotate_identity]

/-- The private component of every compiled list is exactly the original
prefix circuit. -/
theorem run_lift_true {m : ℕ} (gs : List (GatePrefixCircuit.Gate m))
    (v : State m) :
    run (liftCircuit gs) v true = GatePrefixCircuit.run gs (v true) := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
      change run (liftCircuit gs) ((liftGate g).eval v) true =
        GatePrefixCircuit.run gs (g.eval (v true))
      rw [ih, eval_lift_true]

/-- The public component sees the same Boolean prefix computation, but all
frame rotations are replaced by identity rotations. -/
theorem run_lift_false {m : ℕ} (gs : List (GatePrefixCircuit.Gate m))
    (v : State m) :
    run (liftCircuit gs) v false =
      GatePrefixCircuit.run (gs.map publicShadow) (v false) := by
  induction gs generalizing v with
  | nil => rfl
  | cons g gs ih =>
      change run (liftCircuit gs) ((liftGate g).eval v) false =
        GatePrefixCircuit.run (gs.map publicShadow) ((publicShadow g).eval (v false))
      rw [ih, eval_lift_false]

theorem shadow_compute {m : ℕ} (n : ℕ) (h : n ≤ m) :
    (GatePrefixCircuit.compute n h).map publicShadow =
      GatePrefixCircuit.compute n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [GatePrefixCircuit.compute, List.map_append, publicShadow, ih]

theorem shadow_descend {m : ℕ} (a : Fin m → Coefficients)
    (n : ℕ) (h : n ≤ m) :
    (GatePrefixCircuit.descend a n h).map publicShadow =
      GatePrefixCircuit.descend
        (fun _ : Fin m => GateZeroControls.identityCoefficients) n h := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [GatePrefixCircuit.descend, publicShadow, ih]

/-- The public-sector shadow of either frame is the canonical clean identity
circuit, independently of its rotation angles. -/
theorem shadow_frame_circuit {m : ℕ} (a : Fin m → Coefficients) :
    (GatePrefixCircuit.circuit a).map publicShadow =
      GatePrefixCircuit.circuit
        (fun _ : Fin m => GateZeroControls.identityCoefficients) := by
  simp [GatePrefixCircuit.circuit, List.map_append, shadow_compute, shadow_descend]

theorem shadow_inverse_gate {m : ℕ} (g : GatePrefixCircuit.Gate m) :
    publicShadow g.inverse = (publicShadow g).inverse := by
  cases g with
  | prefixBit j => rfl
  | rotate j a =>
      have hi : GateZeroControls.identityCoefficients =
          (1 : Matrix Bool Bool ℂ) := rfl
      simp [publicShadow, GatePrefixCircuit.Gate.inverse, hi]

theorem shadow_inverse {m : ℕ} (gs : List (GatePrefixCircuit.Gate m)) :
    (GatePrefixInverse.inverse gs).map publicShadow =
      GatePrefixInverse.inverse (gs.map publicShadow) := by
  simp [GatePrefixInverse.inverse, List.map_reverse, List.map_map,
    Function.comp_def, shadow_inverse_gate]

theorem shadow_inverse_frame_circuit {m : ℕ} (a : Fin m → Coefficients) :
    (GatePrefixInverse.circuit a).map publicShadow =
      GatePrefixInverse.circuit
        (fun _ : Fin m => GateZeroControls.identityCoefficients) := by
  rw [GatePrefixInverse.circuit, shadow_inverse, shadow_frame_circuit]
  rfl

/-- The clean identity frame really is the identity on every slot
superposition and returns all prefix flags to zero. -/
theorem identity_frame_clean {m : ℕ} (f : GatePrefixCircuit.SlotState m) :
    GatePrefixCircuit.run (GatePrefixCircuit.circuit
      (fun _ : Fin m => GateZeroControls.identityCoefficients))
      (GatePrefixCircuit.embed 0 f) = GatePrefixCircuit.embed 0 f := by
  have h := LinearMap.congr_fun (GatePrefixCircuit.circuit_correct
    (fun _ : Fin m => GateZeroControls.identityCoefficients)) f
  simp only [LinearMap.comp_apply] at h
  have hi : GatePrefixCircuit.ideal
      (fun _ : Fin m => GateZeroControls.identityCoefficients) m le_rfl =
        LinearMap.id := by
    apply GateZeroControls.ideal_identity
    intro j hj
    rfl
  rw [hi] at h
  simpa using h

/-- Its explicitly reversed list is also clean identity; this is derived
from the gate-by-gate inverse construction. -/
theorem identity_inverse_frame_clean {m : ℕ}
    (f : GatePrefixCircuit.SlotState m) :
    GatePrefixCircuit.run (GatePrefixInverse.circuit
      (fun _ : Fin m => GateZeroControls.identityCoefficients))
      (GatePrefixCircuit.embed 0 f) = GatePrefixCircuit.embed 0 f := by
  have h := LinearMap.congr_fun (GatePrefixInverse.circuit_inverse_clean
    (fun _ : Fin m => GateZeroControls.identityCoefficients)
    (fun _ => GateZeroControls.identityCoefficients_unitary)) f
  simp only [LinearMap.comp_apply] at h
  have hi : GatePrefixCircuit.ideal
      (fun _ : Fin m => GateZeroControls.identityCoefficients) m le_rfl =
        LinearMap.id := by
    apply GateZeroControls.ideal_identity
    intro j hj
    rfl
  rw [hi] at h
  simpa using h

/-- The public sector contains only its distinguished root word. -/
def publicSlots {m : ℕ} (p : ℂ) : GatePrefixCircuit.SlotState m :=
  Finsupp.single (fun _ => false) p

/-- Clean physical encoding of one public amplitude and all private clock
amplitudes on the common sector workspace. -/
def cleanState (m : ℕ) (p : ℂ) (u : GateDyadicBoundary.Private m) : State m :=
  fun b => if b then
    GatePrefixCircuit.embed 0 (GateDyadicPrefixBridge.amplitudes m u)
  else GatePrefixCircuit.embed 0 (publicSlots p)

/-- The actual private-sector input-inverse frame list. -/
def inputInverseCircuit (c : ℝ) (m : ℕ) : List (Gate m) :=
  liftCircuit (GatePrefixInverse.circuit (fun j : Fin m =>
    GateDyadicPrefixBridge.inputCoefficients
      (GateDyadicBoundary.centralCosine c j.val)))

/-- The actual private-sector output frame list. -/
def outputCircuit (c : ℝ) (m : ℕ) : List (Gate m) :=
  liftCircuit (GatePrefixCircuit.circuit (fun j : Fin m =>
    GateDyadicPrefixBridge.outputCoefficients
      (GateDyadicBoundary.centralCosine c j.val)))

/-- Exact action of the compiled input-inverse frame on the shared physical
workspace.  The public root is untouched and every prefix flag is clean. -/
theorem inputInverseCircuit_correct (c : ℝ) (m : ℕ) (p : ℂ)
    (u : GateDyadicBoundary.Private m) :
    run (inputInverseCircuit c m) (cleanState m p u) =
      cleanState m p (GateDyadicBoundary.inputFrameInverse c m u) := by
  funext b
  cases b with
  | false =>
      rw [inputInverseCircuit, run_lift_false, shadow_inverse_frame_circuit]
      simpa [cleanState] using identity_inverse_frame_clean (publicSlots (m := m) p)
  | true =>
      rw [inputInverseCircuit, run_lift_true]
      simpa [cleanState] using GateDyadicUnitary.input_inverse_circuit_correct c m u

/-- Exact action of the compiled output frame on the same workspace. -/
theorem outputCircuit_correct (c : ℝ) (m : ℕ) (p : ℂ)
    (u : GateDyadicBoundary.Private m) :
    run (outputCircuit c m) (cleanState m p u) =
      cleanState m p (GateDyadicBoundary.outputFrame c m u) := by
  funext b
  cases b with
  | false =>
      rw [outputCircuit, run_lift_false, shadow_frame_circuit]
      simpa [cleanState] using identity_frame_clean (publicSlots (m := m) p)
  | true =>
      rw [outputCircuit, run_lift_true]
      simpa [cleanState] using GateDyadicPrefixBridge.output_circuit_correct c m u

@[simp] theorem liftCircuit_length {m : ℕ} (gs : List (GatePrefixCircuit.Gate m)) :
    (liftCircuit gs).length = gs.length := by
  simp [liftCircuit]

theorem inputInverseCircuit_length (c : ℝ) (m : ℕ) :
    (inputInverseCircuit c m).length = 3 * m := by
  simp [inputInverseCircuit, GatePrefixInverse.circuit_length]

theorem outputCircuit_length (c : ℝ) (m : ℕ) :
    (outputCircuit c m).length = 3 * m := by
  simp [outputCircuit, GatePrefixCircuit.circuit_length]

/-- Coordinate formula for the clean prefix embedding.  A malformed flag
configuration has zero amplitude; on the unique encoded configuration the
amplitude is the corresponding slot amplitude. -/
theorem embed_apply {m : ℕ} (n : ℕ) (f : GatePrefixCircuit.SlotState m)
    (z : GatePrefixCircuit.Configuration m) :
    GatePrefixCircuit.embed n f z =
      if GatePrefixCircuit.encoded n z.slot = z then f z.slot else 0 := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
      rw [map_add]
      simp only [Finsupp.add_apply, hf, hg]
      split <;> simp
  | single x q =>
      simp only [GatePrefixCircuit.embed, Finsupp.linearCombination_single,
        Finsupp.smul_apply, smul_eq_mul]
      by_cases hx : x = z.slot
      · subst x
        by_cases hz : GatePrefixCircuit.encoded n z.slot = z <;>
          simp [hz]
      · have hz : GatePrefixCircuit.encoded n x ≠ z := by
          intro h
          apply hx
          simpa [GatePrefixCircuit.encoded] using
            congrArg GatePrefixCircuit.Configuration.slot h
        simp [hx, hz]

theorem prefix_full_true_iff {m : ℕ} (x : GatePrefixCircuit.Word m) :
    GatePrefixCircuit.prefixBit x m = true ↔ x = (fun _ => false) := by
  rw [GatePrefixCircuit.prefix_true_iff x m le_rfl]
  constructor
  · intro h
    funext j
    exact h j j.isLt
  · intro h j hj
    simp [h]

/-- Embed both sector slot vectors with the same prefix depth. -/
def slotEmbed {m : ℕ} (n : ℕ) (f : Bool → GatePrefixCircuit.SlotState m) :
    State m := fun b => GatePrefixCircuit.embed n (f b)

/-- Slot-level meaning of the locally controlled sector rotation. -/
def slotCentral {m : ℕ} (a : Coefficients)
    (f : Bool → GatePrefixCircuit.SlotState m) :
    Bool → GatePrefixCircuit.SlotState m := fun b =>
  Finsupp.equivFunOnFinite.symm (fun x =>
    if x = (fun _ => false) then ∑ t : Bool, a b t * f t x else f b x)

@[simp] theorem slotCentral_apply {m : ℕ} (a : Coefficients)
    (f : Bool → GatePrefixCircuit.SlotState m) (b : Bool)
    (x : GatePrefixCircuit.Word m) :
    slotCentral a f b x =
      if x = (fun _ => false) then ∑ t : Bool, a b t * f t x else f b x := rfl

/-- The physical central gate intertwines exactly with its slot-level action
on the fully computed clean-prefix subspace. -/
theorem central_intertwines {m : ℕ} (a : Coefficients)
    (f : Bool → GatePrefixCircuit.SlotState m) :
    Gate.eval (.central a) (slotEmbed m f) =
      slotEmbed m (slotCentral a f) := by
  funext b
  apply Finsupp.ext
  intro z
  change centralAction a (slotEmbed m f) b z =
    slotEmbed m (slotCentral a f) b z
  rw [centralAction_apply]
  by_cases hz : GatePrefixCircuit.encoded m z.slot = z
  · have hc : endControl z = GatePrefixCircuit.prefixBit z.slot m :=
      (congrArg (@endControl m) hz).symm.trans (endControl_encoded z.slot)
    simp only [slotEmbed, embed_apply, if_pos hz, slotCentral_apply,
      hc, prefix_full_true_iff]
  · by_cases hc : endControl z <;>
      simp [hc, slotEmbed, slotCentral, embed_apply, hz]

/-- The two clean sector slot vectors associated with a public amplitude and
a recursive private clock register. -/
def slotPair {m : ℕ} (p : ℂ) (u : GateDyadicBoundary.Private m) :
    Bool → GatePrefixCircuit.SlotState m := fun b =>
  if b then GateDyadicPrefixBridge.amplitudes m u else publicSlots p

theorem cleanState_eq_slotEmbed (m : ℕ) (p : ℂ)
    (u : GateDyadicBoundary.Private m) :
    cleanState m p u = slotEmbed 0 (slotPair p u) := by
  funext b
  cases b <;> rfl

theorem publicSlots_apply {m : ℕ} (p : ℂ) (x : GatePrefixCircuit.Word m) :
    publicSlots p x = if x = (fun _ => false) then p else 0 := by
  classical
  by_cases hx : x = (fun _ => false)
  · subst x
    simp [publicSlots]
  · simp [publicSlots, hx]

theorem amplitudes_replace_root_apply {m : ℕ}
    (u : GateDyadicBoundary.Private m) (q : ℂ)
    (x : GatePrefixCircuit.Word m) :
    GateDyadicPrefixBridge.amplitudes m (q, u.2) x =
      if x = (fun _ => false) then q
      else GateDyadicPrefixBridge.amplitudes m u x := by
  exact GateDyadicBoundary.readPrivate_replace_root m u q x

/-- The slot-level central gate mixes exactly the public and private roots
and leaves every non-root private clock amplitude unchanged. -/
theorem slotCentral_slotPair (c σ : ℝ) (m : ℕ) (p : ℂ)
    (u : GateDyadicBoundary.Private m) :
    let q := GateDyadicBoundary.rotation
      (GateDyadicBoundary.centralCosine c m)
      (GateDyadicBoundary.centralSine c σ m) p u.1
    slotCentral (GateCentralBoundary.coefficients c σ m) (slotPair p u) =
      slotPair q.1 (q.2, u.2) := by
  dsimp only
  funext b
  cases b <;> apply Finsupp.ext <;> intro x <;>
    by_cases hx : x = (fun _ => false)
  · subst x
    simp [slotCentral, slotPair, publicSlots_apply,
      GateDyadicPrefixBridge.amplitudes_apply,
      GateDyadicBoundary.readPrivate_zero, 
      GateCentralBoundary.coefficients, GateDyadicUnitary.rotationCoefficients,
      GateDyadicBoundary.rotation]; ring
  · simp [slotCentral, slotPair, publicSlots_apply, hx,
      ]
  · subst x
    simp [slotCentral, slotPair, publicSlots_apply,
      GateDyadicPrefixBridge.amplitudes_apply,
      GateDyadicBoundary.readPrivate_zero, 
      GateCentralBoundary.coefficients, GateDyadicUnitary.rotationCoefficients,
      GateDyadicBoundary.rotation]; ring
  · simp only [slotCentral_apply, slotPair, if_true, if_neg hx]
    simpa only [if_neg hx] using
      (amplitudes_replace_root_apply u
        (GateDyadicBoundary.rotation
          (GateDyadicBoundary.centralCosine c m)
          (GateDyadicBoundary.centralSine c σ m) p u.1).2 x).symm

/-- Prefix computation used by the central gate. -/
def computeCircuit (m : ℕ) : List (Gate m) :=
  liftCircuit (GatePrefixCircuit.compute m le_rfl)

/-- Exact reverse prefix computation. -/
def uncomputeCircuit (m : ℕ) : List (Gate m) :=
  liftCircuit (GatePrefixInverse.inverse (GatePrefixCircuit.compute m le_rfl))

theorem computeCircuit_correct (m : ℕ) (p : ℂ)
    (u : GateDyadicBoundary.Private m) :
    run (computeCircuit m) (cleanState m p u) =
      slotEmbed m (slotPair p u) := by
  funext b
  cases b with
  | false =>
      rw [computeCircuit, run_lift_false, shadow_compute]
      have h := LinearMap.congr_fun
        (GatePrefixCircuit.compute_correct m le_rfl) (publicSlots (m := m) p)
      simpa [cleanState, slotEmbed, slotPair] using h
  | true =>
      rw [computeCircuit, run_lift_true]
      have h := LinearMap.congr_fun
        (GatePrefixCircuit.compute_correct m le_rfl)
        (GateDyadicPrefixBridge.amplitudes m u)
      simpa [cleanState, slotEmbed, slotPair] using h

theorem compute_valid {m : ℕ} (n : ℕ) (h : n ≤ m) :
    ∀ g ∈ GatePrefixCircuit.compute n h, g.Valid := by
  induction n with
  | zero => simp [GatePrefixCircuit.compute]
  | succ n ih =>
      intro g hg
      simp only [GatePrefixCircuit.compute, List.mem_append,
        List.mem_singleton] at hg
      rcases hg with hg | rfl
      · exact ih (by omega) g hg
      · trivial

theorem prefix_uncompute_correct {m : ℕ}
    (f : GatePrefixCircuit.SlotState m) :
    GatePrefixCircuit.run
      (GatePrefixInverse.inverse (GatePrefixCircuit.compute m le_rfl))
      (GatePrefixCircuit.embed m f) = GatePrefixCircuit.embed 0 f := by
  have hc := LinearMap.congr_fun
    (GatePrefixCircuit.compute_correct m le_rfl) f
  have hi := LinearMap.congr_fun
    (GatePrefixInverse.run_inverse_comp (GatePrefixCircuit.compute m le_rfl)
      (compute_valid m le_rfl)) (GatePrefixCircuit.embed 0 f)
  simp only [LinearMap.comp_apply] at hc
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hi
  rw [hc] at hi
  exact hi

theorem uncomputeCircuit_correct {m : ℕ}
    (f : Bool → GatePrefixCircuit.SlotState m) :
    run (uncomputeCircuit m) (slotEmbed m f) = slotEmbed 0 f := by
  funext b
  cases b with
  | false =>
      rw [uncomputeCircuit, run_lift_false, shadow_inverse, shadow_compute]
      exact prefix_uncompute_correct (f false)
  | true =>
      rw [uncomputeCircuit, run_lift_true]
      exact prefix_uncompute_correct (f true)

/-- Compute the local zero-prefix flag, rotate the sector qubit, and erase
the flag. -/
def centralCircuit (c σ : ℝ) (m : ℕ) : List (Gate m) :=
  computeCircuit m ++ [.central (GateCentralBoundary.coefficients c σ m)] ++
    uncomputeCircuit m

theorem centralCircuit_correct (c σ : ℝ) (m : ℕ) (p : ℂ)
    (u : GateDyadicBoundary.Private m) :
    run (centralCircuit c σ m) (cleanState m p u) =
      let q := GateDyadicBoundary.rotation
        (GateDyadicBoundary.centralCosine c m)
        (GateDyadicBoundary.centralSine c σ m) p u.1
      cleanState m q.1 (q.2, u.2) := by
  rw [centralCircuit, run_append, run_append]
  simp only [run, LinearMap.comp_apply, LinearMap.id_apply]
  rw [computeCircuit_correct, central_intertwines, slotCentral_slotPair,
    uncomputeCircuit_correct]
  exact (cleanState_eq_slotEmbed m _ _).symm

theorem centralCircuit_eq_central (c σ : ℝ) (m : ℕ)
    (x : GateDyadicBoundary.State m) :
    run (centralCircuit c σ m) (cleanState m x.1 x.2) =
      cleanState m (GateDyadicBoundary.central c σ m x).1
        (GateDyadicBoundary.central c σ m x).2 := by
  rcases x with ⟨p, u⟩
  simpa [GateDyadicBoundary.central] using centralCircuit_correct c σ m p u

theorem centralCircuit_length (c σ : ℝ) (m : ℕ) :
    (centralCircuit c σ m).length = 2 * m + 1 := by
  simp [centralCircuit, computeCircuit, uncomputeCircuit,
    GatePrefixCircuit.compute_length, GatePrefixInverse.inverse_length]; omega

/-- The complete physical boundary circuit on one sector/clock/prefix
workspace. -/
def boundaryCircuit (c σ : ℝ) (m : ℕ) : List (Gate m) :=
  inputInverseCircuit c m ++ centralCircuit c σ m ++ outputCircuit c m

theorem boundaryCircuit_correct (c σ : ℝ)
    (hunit : c ^ 2 + σ ^ 2 = 1) (m : ℕ)
    (x : GateDyadicBoundary.State m) :
    run (boundaryCircuit c σ m) (cleanState m x.1 x.2) =
      cleanState m (GateDyadicBoundary.chronological c σ m x).1
        (GateDyadicBoundary.chronological c σ m x).2 := by
  rcases x with ⟨p, u⟩
  rw [boundaryCircuit, run_append, run_append]
  simp only [LinearMap.comp_apply]
  rw [inputInverseCircuit_correct, centralCircuit_correct]
  dsimp only
  rw [outputCircuit_correct,
    GateDyadicBoundary.chronological_eq_compressed c σ hunit m (p, u)]
  rfl

/-- Exact linear gate count for the entire compressed boundary network. -/
theorem boundaryCircuit_length (c σ : ℝ) (m : ℕ) :
    (boundaryCircuit c σ m).length = 8 * m + 1 := by
  rw [boundaryCircuit]
  simp [inputInverseCircuit_length, centralCircuit_length,
    outputCircuit_length]
  omega

/-- Physical validity checks only the concrete two-by-two matrix on each
known sector-controlled rotation. -/
def Gate.Valid {m : ℕ} : Gate m → Prop
  | .prefixBit _ => True
  | .privateRotate _ a => a.IsUnitary
  | .central a => a.IsUnitary

theorem inputInverseCircuit_valid (c : ℝ) (m : ℕ) :
    ∀ g ∈ inputInverseCircuit c m, g.Valid := by
  intro g hg
  change g ∈ liftCircuit (GatePrefixInverse.circuit (fun j : Fin m =>
    GateDyadicPrefixBridge.inputCoefficients
      (GateDyadicBoundary.centralCosine c j.val))) at hg
  unfold liftCircuit at hg
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
  have hv := GatePrefixInverse.circuit_valid
    (fun j : Fin m => GateDyadicPrefixBridge.inputCoefficients
      (GateDyadicBoundary.centralCosine c j.val))
    (fun j => GateDyadicUnitary.inputCoefficients_unitary _) h hh
  cases h <;> exact hv

theorem outputCircuit_valid (c : ℝ) (m : ℕ) :
    ∀ g ∈ outputCircuit c m, g.Valid := by
  intro g hg
  change g ∈ liftCircuit (GatePrefixCircuit.circuit (fun j : Fin m =>
    GateDyadicPrefixBridge.outputCoefficients
      (GateDyadicBoundary.centralCosine c j.val))) at hg
  unfold liftCircuit at hg
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
  have hv := GatePrefixCircuit.circuit_valid
    (fun j : Fin m => GateDyadicPrefixBridge.outputCoefficients
      (GateDyadicBoundary.centralCosine c j.val))
    (fun j => GateDyadicUnitary.outputCoefficients_unitary _) h hh
  cases h <;> exact hv

theorem liftGate_valid {m : ℕ} (g : GatePrefixCircuit.Gate m)
    (hg : g.Valid) : (liftGate g).Valid := by
  cases g <;> exact hg

theorem liftCircuit_valid {m : ℕ} (gs : List (GatePrefixCircuit.Gate m))
    (hgs : ∀ g ∈ gs, g.Valid) : ∀ g ∈ liftCircuit gs, g.Valid := by
  intro g hg
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
  exact liftGate_valid h (hgs h hh)

theorem centralCircuit_valid (c σ : ℝ)
    (hunit : c ^ 2 + σ ^ 2 = 1) (m : ℕ) :
    ∀ g ∈ centralCircuit c σ m, g.Valid := by
  have hc := compute_valid m le_rfl
  have hci : ∀ g ∈ computeCircuit m, g.Valid :=
    liftCircuit_valid _ hc
  have hui : ∀ g ∈ uncomputeCircuit m, g.Valid := by
    apply liftCircuit_valid
    exact GatePrefixInverse.inverse_valid _ hc
  intro g hg
  simp only [centralCircuit, List.mem_append, List.mem_singleton] at hg
  rcases hg with (hg | rfl) | hg
  · exact hci g hg
  · exact GateDyadicUnitary.centralCoefficients_unitary c σ hunit m
  · exact hui g hg

theorem boundaryCircuit_valid (c σ : ℝ)
    (hunit : c ^ 2 + σ ^ 2 = 1) (m : ℕ) :
    ∀ g ∈ boundaryCircuit c σ m, g.Valid := by
  intro g hg
  simp only [boundaryCircuit, List.mem_append] at hg
  rcases hg with (hg | hg) | hg
  · exact inputInverseCircuit_valid c m g hg
  · exact centralCircuit_valid c σ hunit m g hg
  · exact outputCircuit_valid c m g hg

end
end SparseHamiltonian.GatePhysicalBoundary
