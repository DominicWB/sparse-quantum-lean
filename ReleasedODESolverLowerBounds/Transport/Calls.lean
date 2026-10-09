import DeferredMeasurementLowerBounds.Access.Control
import DeferredMeasurementLowerBounds.Access.TimeAccess
import ODELowerBoundExtensions.Release.Registers

set_option autoImplicit false

/-!
# Record-selected calls of the call forms of any oracle family

Manuscript Section `odel:sec:main`, lines 3669-3673 ("their inverses and controls"). The call
forms `AdaptiveODELowerBound.Access.callFamily O` of a labelled family `O` act on
control ⊗ workspace; plain and inverse forms act on both control sectors, controlled forms on the
control sector `1` only. After flattening the records and the control bit into one register
(`callFlat`), a record-selected call of the call forms is a record-selected call of `O` itself
(`patOp_callFlat`), with the mask and direction of `formSelOf`. These are the label-generic forms
of `DeferredMeasurementLowerBounds.Access.formSel` and `callOpt_callFamily_apply`, which are
stated for the matrix labels `Query`: `formSel_eq_formSelOf` and
`callOpt_callFamily_apply_query` recover them as the instance `L₀ = Query`.
-/

namespace ReleasedODESolverLowerBounds.Transport

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Deferral (Pat patOp callOpt)
open AdaptiveODELowerBound.Access (CallForm callFamily)
open NativeSparseBlockEncoding (Query)
open scoped InnerProduct

variable {X L₀ : Type*} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- A call form with a direction, as a mask and a direction on the control bit. -/
def formSelOf : Option ((L₀ × CallForm) × Bool) → Bool → Option (L₀ × Bool)
  | none, _ => none
  | some ((q, .plain), b), _ => some (q, b)
  | some ((q, .inverse), b), _ => some (q, !b)
  | some ((q, .controlled), b), d => if d then some (q, b) else none
  | some ((q, .controlledInverse), b), d => if d then some (q, !b) else none

/-- The package's `DeferredMeasurementLowerBounds.Access.formSel` is `formSelOf` at the matrix
labels `Query`. -/
theorem formSel_eq_formSelOf :
    DeferredMeasurementLowerBounds.Access.formSel = formSelOf (L₀ := Query) := by
  funext c d
  rcases c with _ | ⟨⟨q, f⟩, b⟩
  · rfl
  · cases f <;> rfl

/-- Optional calls of the call forms of a family, coordinatewise on the control bit. -/
theorem callOpt_callFamily_apply_formSelOf (O : L₀ → X → W →L[ℂ] W)
    (c : Option ((L₀ × CallForm) × Bool)) (x : X) (v : Joint Bool W) (d : Bool) :
    callOpt (callFamily O) c x v d = callOpt O (formSelOf c d) x (v d) := by
  rcases c with _ | ⟨⟨q, f⟩, b⟩
  · rfl
  have hc : ∀ U : W →L[ℂ] W, star (MaskedProgram.masked (fun c : Bool => c) U) =
      MaskedProgram.masked (fun c : Bool => c) (star U) := fun U => by
    rw [ContinuousLinearMap.star_eq_adjoint, MaskedProgram.masked_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint]
  cases f <;> cases b <;> cases d <;>
    simp [callOpt, DeferredMeasurementLowerBounds.Model.queryOp, formSelOf, callFamily,
      AdaptiveODELowerBound.Access.formOp, Joint.star_fiber, hc,
      AdaptiveODELowerBound.Access.ctrlOp]

/-- **Containment**: the package's `DeferredMeasurementLowerBounds.Access.callOpt_callFamily_apply`
is `callOpt_callFamily_apply_formSelOf` at the matrix labels `Query` (via
`formSel_eq_formSelOf`). -/
theorem callOpt_callFamily_apply_query (O : Query → X → W →L[ℂ] W)
    (c : Option ((Query × CallForm) × Bool)) (x : X) (v : Joint Bool W)
    (d : Bool) :
    callOpt (callFamily O) c x v d =
      callOpt O (DeferredMeasurementLowerBounds.Access.formSel c d) x (v d) := by
  rw [formSel_eq_formSelOf]
  exact callOpt_callFamily_apply_formSelOf O c x v d

/-- A call of `formSelOf` names the label of its call form. -/
theorem formSelOf_eq_some {c : Option ((L₀ × CallForm) × Bool)} {d : Bool} {q : L₀} {b : Bool}
    (h : formSelOf c d = some (q, b)) : ∃ f b', c = some ((q, f), b') := by
  rcases c with _ | ⟨⟨q', f⟩, b'⟩
  · simp [formSelOf] at h
  · refine ⟨f, b', ?_⟩
    have hq : q' = q := by
      cases f <;> cases d <;> simp [formSelOf] at h <;> exact h.1
    rw [hq]

/-- The records and the control bit of the call shape, flattened into one register. -/
def callFlat (R : Type) [Fintype R] (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] :
    Joint R (Joint Bool W) ≃ₗᵢ[ℂ] Joint (R × Bool) W :=
  (ODELowerBoundExtensions.Release.jointFlatten R Bool W).symm

omit [CompleteSpace W] in
/-- Coordinates of the flattened call register. -/
theorem callFlat_apply {R : Type} [Fintype R] (Φ : Joint R (Joint Bool W)) (r : R) (d : Bool) :
    callFlat R W Φ (r, d) = Φ r d := by
  rfl

/-- **A record-selected call of the call forms is a record-selected call of the family** on the
records and the control bit. -/
theorem patOp_callFlat {R : Type} [Fintype R] (O : L₀ → X → W →L[ℂ] W)
    (π : Pat (L₀ × CallForm) R) (x : X) :
    (callFlat R W).conjStarAlgEquiv (patOp (callFamily O) π x) =
      patOp O (fun rd => formSelOf (π rd.1) rd.2) x := by
  refine ContinuousLinearMap.ext fun Ψ => PiLp.ext fun rd => ?_
  obtain ⟨r, d⟩ := rd
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, callFlat_apply]
  change callOpt (callFamily O) (π r) x ((callFlat R W).symm Ψ r) d =
    callOpt O (formSelOf (π r) d) x (Ψ (r, d))
  rw [callOpt_callFamily_apply_formSelOf, ← callFlat_apply, LinearIsometryEquiv.apply_symm_apply]

end

end ReleasedODESolverLowerBounds.Transport
