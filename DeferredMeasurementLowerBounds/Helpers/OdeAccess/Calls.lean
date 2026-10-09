import DeferredMeasurementLowerBounds.Access.Control

set_option autoImplicit false

/-!
# Generic calls and isometries for the sampled-time access

Coordinate rules used to identify record-selected calls of the sampled-time ODE access with
patterns of its one-branch access:

* `callOpt_fiber_apply`: an optional call of a homogeneous spectator family `1_J ⊗ O` acts on
  every block as the optional call of `O`;
* `patOp_subtype`: a call pattern over a set of labels is the call pattern of the underlying
  labels;
* `isoEquiv_isometry`, `comp_three_isometry`: the map of a linear isometry equivalence is an
  isometry, and so is a composition of three isometries.
-/

namespace DeferredMeasurementLowerBounds.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap OracleCircuit
open DeferredMeasurementLowerBounds.Model DeferredMeasurementLowerBounds.Deferral
open scoped InnerProduct

variable {X : Type*}

/-- Optional calls of a homogeneous spectator family, coordinatewise. -/
theorem callOpt_fiber_apply {W J' : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] [Fintype J'] {L : Type*} (O : L → X → W →L[ℂ] W) (c : Option (L × Bool))
    (x : X) (w : Joint J' W) (j : J') :
    callOpt (fun l x => Joint.fiber fun _ : J' => O l x) c x w j = callOpt O c x (w j) := by
  rcases c with _ | ⟨q, _ | _⟩
  · rfl
  · rfl
  · change star (Joint.fiber fun _ : J' => O q x) w j = star (O q x) (w j)
    rw [Joint.star_fiber]
    rfl

/-- The map of a linear isometry equivalence is an isometry. -/
theorem isoEquiv_isometry {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁]
    [CompleteSpace E₁] [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂] [CompleteSpace E₂]
    (e : E₁ ≃ₗᵢ[ℂ] E₂) :
    (e.toContinuousLinearEquiv.toContinuousLinearMap)† ∘L
      e.toContinuousLinearEquiv.toContinuousLinearMap = 1 := by
  have h : (e.toContinuousLinearEquiv.toContinuousLinearMap)† =
      e.symm.toContinuousLinearEquiv.toContinuousLinearMap := e.adjoint_eq_symm
  rw [h]
  refine ContinuousLinearMap.ext fun v => ?_
  simp

/-- A composition of three isometries is an isometry. -/
theorem comp_three_isometry {E₁ E₂ E₃ E₄ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂] [CompleteSpace E₂]
    [NormedAddCommGroup E₃] [InnerProductSpace ℂ E₃] [CompleteSpace E₃]
    [NormedAddCommGroup E₄] [InnerProductSpace ℂ E₄] [CompleteSpace E₄]
    (A : E₃ →L[ℂ] E₄) (B : E₂ →L[ℂ] E₃) (C : E₁ →L[ℂ] E₂) (hA : A† ∘L A = 1) (hB : B† ∘L B = 1)
    (hC : C† ∘L C = 1) : (A ∘L B ∘L C)† ∘L (A ∘L B ∘L C) = 1 := by
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [adjoint_comp, comp_apply]
  rw [← comp_apply (A†) A, hA, one_apply_eq_self, ← comp_apply (B†) B, hB,
    one_apply_eq_self, ← comp_apply (C†) C, hC]

/-- A call pattern of a set of labels is a call pattern of the labels. -/
theorem patOp_subtype {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [CompleteSpace W] {L R' : Type*} [Fintype R'] (O : L → X → W →L[ℂ] W) (p : L → Prop)
    (π : Pat {l // p l} R') (x : X) :
    patOp (fun l : {l // p l} => O l.1) π x =
      patOp O (fun r => (π r).map fun lb => (lb.1.1, lb.2)) x := by
  unfold patOp
  congr 1
  funext r
  dsimp only
  rcases π r with _ | ⟨l, b⟩ <;> rfl

end

end DeferredMeasurementLowerBounds.Access
