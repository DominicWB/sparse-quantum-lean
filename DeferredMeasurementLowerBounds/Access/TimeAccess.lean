import DeferredMeasurementLowerBounds.Access.Control
import DeferredMeasurementLowerBounds.Access.Transport
import DeferredMeasurementLowerBounds.Helpers.OdeAccess.Calls
import AdaptiveODELowerBound.Access.Calls
import AdaptiveHamiltonianLowerBound.Access.HardData
import SparseLowerBounds.ODE.Model
import SparseHamiltonian.MultiOracleTransport

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
set_option synthInstance.maxSize 8192

/-!
# Record-selected calls of the sampled-time ODE access

Manuscript Section `odel:sec:main`, lines 3669-3673 (a reversible value oracle and in-place
locators, "their inverses and controls, with a coherent time address"). The adaptive ODE lower
bounds (`AdaptiveODELowerBound.Model.TreeForces`) quantify over protocols over the sampled-time
access `F.access ι` (any branch register `ι`) and over its call forms
`callFamily (F.access ι)` (plain, inverse, controlled, controlled-inverse calls).

* `accessEquiv ι`: `F.access ι` is the spectator lift `1_ι ⊗ F.access Unit` of the
  one-branch access (`access_eq_conj`).
* `valueConj`: the value call is an additive lookup `|α, z⟩ ↦ |α, z + table α⟩`, so its inverse
  is the value call conjugated by the known negation `z ↦ -z` of the value register
  (`star_access_value`). Branch-dependent value directions in one aligned slot therefore cost
  one controlled value call: **no constant is lost** for this access.
* A record-selected call of `F.access ι` (plain shape) or of `callFamily (F.access ι)` (call
  shape) on the records `R` is a pattern of `F.access Unit` on the spectator register `R × ι`,
  respectively `(R × Bool) × ι` (`patOp_plain`, `patOp_call`: the call forms become masks on the
  control bit).
* The circuits of the deferred selection labels over the call forms of the sampled-time access
  (`plainCircuit`, `callCircuit`) are in `Access.TimeCircuits`.
-/

namespace DeferredMeasurementLowerBounds.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.ODE ContinuousLinearMap OracleCircuit
open NativeSparseBlockEncoding
open DeferredMeasurementLowerBounds.Model DeferredMeasurementLowerBounds.Deferral
open AdaptiveODELowerBound.Access (CallForm callFamily formOp ctrlOp activeEmbed)
open AdaptiveHamiltonianLowerBound.Access (valueWeight)
open scoped InnerProduct

variable {X N Z : Type*} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] {Kt s : ℕ}
  (F : Family X N Z Kt s)

/-- The workspace of the sampled-time access as branch register ⊗ one-branch workspace. -/
def accessEquiv (ι : Type*) [Fintype ι] :
    Workspace ι N Z Kt ≃ₗᵢ[ℂ] Joint ι (Workspace Unit N Z Kt) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ (SparseFlagEmbedding.Space (N × N) Z)
    ((Equiv.prodCongr (Equiv.refl ι) (Equiv.uniqueProd (Fin Kt) Unit).symm).trans
      (Equiv.sigmaEquivProd ι (Unit × Fin Kt)).symm)).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : ι) (_ : Unit × Fin Kt) =>
      SparseFlagEmbedding.Space (N × N) Z))

/-- **The sampled-time access is the spectator lift of the one-branch access.** -/
theorem access_eq_conj (ι : Type*) [Fintype ι] (q : Query) (x : X) :
    F.access ι q x = (accessEquiv ι).symm.conjStarAlgEquiv
      (Joint.fiber fun _ : ι => F.access Unit q x) := by
  ext Ψ b
  rfl

/-- Coordinates of a call of the sampled-time access in the one-branch blocks. -/
theorem access_apply (ι : Type*) [Fintype ι] (q : Query) (x : X) (w : Workspace ι N Z Kt)
    (i : ι) : accessEquiv ι (F.access ι q x w) i = F.access Unit q x (accessEquiv ι w i) := by
  rw [access_eq_conj, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_symm]
  rfl

/-- Coordinates of an inverse call of the sampled-time access in the one-branch blocks. -/
theorem star_access_apply (ι : Type*) [Fintype ι] (q : Query) (x : X) (w : Workspace ι N Z Kt)
    (i : ι) :
    accessEquiv ι (star (F.access ι q x) w) i = star (F.access Unit q x) (accessEquiv ι w i) := by
  rw [access_eq_conj, ← map_star, Joint.star_fiber,
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_symm]
  rfl

/-- Coordinates of an optional call of the sampled-time access in the one-branch blocks. -/
theorem callOpt_access_apply (ι : Type*) [Fintype ι] (c : Option (Query × Bool)) (x : X)
    (w : Workspace ι N Z Kt) (i : ι) :
    accessEquiv ι (callOpt (F.access ι) c x w) i =
      callOpt (F.access Unit) c x (accessEquiv ι w i) := by
  rcases c with _ | ⟨q, _ | _⟩
  · rfl
  · exact access_apply F ι q x w i
  · exact star_access_apply F ι q x w i

/-- The negation `z ↦ -z` of the value register in every block of the one-branch workspace. -/
def negValue : Workspace Unit N Z Kt →L[ℂ] Workspace Unit N Z Kt :=
  Joint.fiber fun _ =>
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ SparseFlagEmbedding.Qutrit
      (Equiv.prodCongr (Equiv.refl (N × N))
        (Equiv.neg Z))).toContinuousLinearEquiv.toContinuousLinearMap

omit [DecidableEq N] in
/-- The negation is unitary. -/
theorem negValue_unitary : IsUnitary (negValue (N := N) (Z := Z) (Kt := Kt)) := by
  have hs := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ SparseFlagEmbedding.Qutrit
    (Equiv.prodCongr (Equiv.refl (N × N)) (Equiv.neg Z))).star_eq_symm
  constructor
  · rw [negValue, Joint.star_fiber, Joint.fiber_mul]
    erw [hs]
    rw [← Joint.fiber_one]
    congr 1
    funext b
    ext v ⟨a, z⟩
    simp
  · rw [negValue, Joint.star_fiber, Joint.fiber_mul]
    erw [hs]
    rw [← Joint.fiber_one]
    congr 1
    funext b
    ext v ⟨a, z⟩
    simp

/-- **The inverse value call is the value call conjugated by the negation.** -/
theorem star_access_value (x : X) :
    star (F.access Unit .value x) = negValue * F.access Unit .value x * star negValue := by
  have hs := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ SparseFlagEmbedding.Qutrit
    (Equiv.prodCongr (Equiv.refl (N × N)) (Equiv.neg Z))).star_eq_symm
  rw [negValue, Joint.star_fiber]
  erw [hs]
  ext Ψ b ⟨a, z⟩ k
  rw [ContinuousLinearMap.star_eq_adjoint]
  change (ContinuousLinearMap.adjoint (F.access Unit .value x) Ψ) b (a, z) k = _
  rw [Family.access, TimeDependentODE.labelOracle, WeightedClock.diagonal_adjoint,
    WeightedClock.diagonal_apply]
  change (ContinuousLinearMap.adjoint
    (LookupControlledGate.oracle (K := SparseFlagEmbedding.Qutrit) F.data.table _)
    (Ψ b)) (a, z) k = _
  rw [LookupControlledGate.oracle_adjoint_apply]
  simp
  change _ = ((LookupControlledGate.oracle (K := SparseFlagEmbedding.Qutrit) F.data.table
    (TimeDependentODE.sample x b)) _ (a, -z)) k
  rw [LookupControlledGate.oracle_apply]
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, add_comm]

/-- The conjugation data of the value label; the locators have none. -/
def valueConj : (q : Query) → Option (InverseConj (F.access Unit) q)
  | .value => some ⟨negValue, negValue_unitary, star_access_value F⟩
  | _ => none

/-! ### Record-selected calls as patterns of the one-branch access -/

variable {R : Type} [Fintype R] {ι : Type} [Fintype ι]

/-- The records-and-branches register of the plain shape, flattened. -/
def plainEquiv (R ι : Type) [Fintype R] [Fintype ι] :
    Joint R (Workspace ι N Z Kt) ≃ₗᵢ[ℂ] Joint (R × ι) (Workspace Unit N Z Kt) :=
  (LinearIsometryEquiv.piLpCongrRight 2 fun _ : R => accessEquiv ι).trans
    (ODELowerBoundExtensions.Release.jointFlatten R ι _).symm

omit [DecidableEq N] [AddCommGroup Z] in
/-- Coordinates of the flattened plain register. -/
theorem plainEquiv_apply (Φ : Joint R (Workspace ι N Z Kt)) (r : R) (i : ι) :
    plainEquiv R ι Φ (r, i) = accessEquiv ι (Φ r) i := rfl

/-- **A record-selected call of the plain shape is a pattern on `R × ι`.** -/
theorem patOp_plain (π : Pat Query R) (x : X) :
    (plainEquiv R ι).conjStarAlgEquiv (patOp (F.access ι) π x) =
      patOp (F.access Unit) (fun ri => π ri.1) x := by
  refine ContinuousLinearMap.ext fun Ψ => PiLp.ext fun ri => ?_
  obtain ⟨r, i⟩ := ri
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, plainEquiv_apply]
  change accessEquiv ι (callOpt (F.access ι) (π r) x ((plainEquiv R ι).symm Ψ r)) i =
    callOpt (F.access Unit) (π r) x (Ψ (r, i))
  rw [callOpt_access_apply, ← plainEquiv_apply, LinearIsometryEquiv.apply_symm_apply]

/-- A call form with a direction, as a mask and direction on the control bit. -/
def formSel : Option ((Query × CallForm) × Bool) → Bool → Option (Query × Bool)
  | none, _ => none
  | some ((q, .plain), b), _ => some (q, b)
  | some ((q, .inverse), b), _ => some (q, !b)
  | some ((q, .controlled), b), d => if d then some (q, b) else none
  | some ((q, .controlledInverse), b), d => if d then some (q, !b) else none

/-- Optional calls of the call forms of a family, coordinatewise on the control bit. -/
theorem callOpt_callFamily_apply {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] (O : Query → X → W →L[ℂ] W) (c : Option ((Query × CallForm) × Bool))
    (x : X) (v : Joint Bool W) (d : Bool) :
    callOpt (callFamily O) c x v d = callOpt O (formSel c d) x (v d) := by
  rcases c with _ | ⟨⟨q, f⟩, b⟩
  · rfl
  have hc : ∀ U : W →L[ℂ] W, star (MaskedProgram.masked (fun c : Bool => c) U) =
      MaskedProgram.masked (fun c : Bool => c) (star U) := fun U => by
    rw [ContinuousLinearMap.star_eq_adjoint, MaskedProgram.masked_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint]
  cases f <;> cases b <;> cases d <;>
    simp [callOpt, queryOp, formSel, callFamily, formOp, Joint.star_fiber, hc, ctrlOp]

/-- The records-control-branches register of the call shape, flattened. -/
def callEquiv (R ι : Type) [Fintype R] [Fintype ι] :
    Joint R (Joint Bool (Workspace ι N Z Kt)) ≃ₗᵢ[ℂ]
      Joint ((R × Bool) × ι) (Workspace Unit N Z Kt) :=
  (LinearIsometryEquiv.piLpCongrRight 2 fun _ : R =>
    (LinearIsometryEquiv.piLpCongrRight 2 fun _ : Bool => accessEquiv ι).trans
      (ODELowerBoundExtensions.Release.jointFlatten Bool ι _).symm).trans
    (ODELowerBoundExtensions.Release.jointFlatten R (Bool × ι) _).symm |>.trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ _ (Equiv.prodAssoc R Bool ι).symm)

omit [DecidableEq N] [AddCommGroup Z] in
/-- Coordinates of the flattened call register. -/
theorem callEquiv_apply (Φ : Joint R (Joint Bool (Workspace ι N Z Kt))) (r : R) (d : Bool)
    (i : ι) : callEquiv R ι Φ ((r, d), i) = accessEquiv ι (Φ r d) i := rfl

/-- **A record-selected call of the call shape is a pattern on `(R × Bool) × ι`.** -/
theorem patOp_call (π : Pat (Query × CallForm) R) (x : X) :
    (callEquiv R ι).conjStarAlgEquiv (patOp (callFamily (F.access ι)) π x) =
      patOp (F.access Unit) (fun rdi => formSel (π rdi.1.1) rdi.1.2) x := by
  refine ContinuousLinearMap.ext fun Ψ => PiLp.ext fun rdi => ?_
  obtain ⟨⟨r, d⟩, i⟩ := rdi
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, callEquiv_apply]
  change accessEquiv ι (callOpt (callFamily (F.access ι)) (π r) x
      ((callEquiv R ι).symm Ψ r) d) i = callOpt (F.access Unit) (formSel (π r) d) x (Ψ ((r, d), i))
  rw [callOpt_callFamily_apply, callOpt_access_apply, ← callEquiv_apply,
    LinearIsometryEquiv.apply_symm_apply]

end

end DeferredMeasurementLowerBounds.Access
