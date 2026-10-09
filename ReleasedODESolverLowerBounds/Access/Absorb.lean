import ODELowerBoundExtensions.Release.Registers
import DeferredMeasurementLowerBounds.Access.Control

set_option autoImplicit false

/-!
# Spectator forms and spectator absorption

Manuscript Section `odel:sec:main`, lines 3669-3673 (access "through a reversible value oracle
and in-place row/column locators, their inverses and controls") and line 2364 (purification and
deferred measurement).

The matrix labels of the released solvers' physical oracles are, after one fixed isometric
identification of the workspace with `ℂ^S ⊗ V`, the spectator lifts `1_S ⊗ P_l(x)` of one
primitive family `P` that does not depend on the branch register (`SpectatorForm`; the instances
are `Access/MeshForm` and `Access/ConstForm`). Two spectator forms of the same primitive family
are related by an isometry as soon as the target is large enough:

* `restrictMap e`, `padMap e`: restriction of a register along an embedding `e : S ↪ S'` and
  its adjoint, the extension by zero; `padMap` is an isometry (`padMap_isometry`) and commutes
  with every spectator lift (`fiber_comp_padMap`).
* `exists_absorb`: if `O = U⁻¹ (1_S ⊗ P) U`, `O' = U'⁻¹ (1_{S'} ⊗ P) U'` on finite-dimensional
  workspaces and `|J| · dim W ≤ dim W'`, there is an isometry `ℂ^J ⊗ W → W'` that intertwines
  `1_J ⊗ O_l(x)` with `O'_l(x)` for every label and input. This is the spectator identity that
  absorbs the record register of a deferred measured algorithm into the branch register of a
  larger physical oracle.
* `SpectatorForm.nonempty_inverseConj`: an inverse by a known conjugation of a primitive label
  gives one of the spectator-form label.
-/

namespace ReleasedODESolverLowerBounds.Access

noncomputable section
open SparseHamiltonian SparseLowerBounds ContinuousLinearMap
open DeferredMeasurementLowerBounds.Access (InverseConj)
open scoped InnerProduct

variable {X L : Type*} {W W' V : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [CompleteSpace W] [NormedAddCommGroup W'] [InnerProductSpace ℂ W'] [CompleteSpace W']
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- **Spectator form** of a labelled family `O` over a primitive family `P`: after one fixed
isometric identification `U : W ≃ ℂ^S ⊗ V` with a finite register `S`, every label is the
spectator lift `1_S ⊗ P_l(x)`. -/
def SpectatorForm (O : L → X → W →L[ℂ] W) (P : L → X → V →L[ℂ] V) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (U : W ≃ₗᵢ[ℂ] Joint S V),
    ∀ l x, O l x = U.symm.conjStarAlgEquiv (Joint.fiber fun _ : S => P l x)

section Pad

variable {S S' : Type} [Fintype S] [Fintype S']

/-- The restriction `Φ ↦ (s ↦ Φ (e s))` of a register along an embedding. -/
def restrictMap (e : S ↪ S') (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] : Joint S' V →L[ℂ] Joint S V :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : S => V)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun s => Joint.proj (e s)

/-- **Extension by zero** along an embedding of registers: the adjoint of the restriction. -/
def padMap (e : S ↪ S') (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] : Joint S V →L[ℂ] Joint S' V :=
  ContinuousLinearMap.adjoint (restrictMap e V)

omit [Fintype S] [Fintype S'] in
/-- Coordinates of the restriction. -/
@[simp] theorem restrictMap_apply (e : S ↪ S') (Φ : Joint S' V) (s : S) :
    restrictMap e V Φ s = Φ (e s) := rfl

/-- The explicit extension by zero, `Φ s' = Ψ s` if `s' = e s` and `0` otherwise. -/
def padOf (e : S ↪ S') (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] : Joint S V →L[ℂ] Joint S' V :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : S' => V)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun s' =>
      haveI := Classical.propDecidable (∃ s, e s = s')
      if h : ∃ s, e s = s' then Joint.proj h.choose else 0

/-- The extension by zero is the explicit padding. -/
theorem padMap_eq_padOf (e : S ↪ S') : padMap e V = padOf e V := by
  rw [padMap, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro Ψ Φ
  simp only [PiLp.inner_apply, restrictMap_apply]
  symm
  refine Fintype.sum_of_injective e e.injective _ _ ?_ ?_
  · intro s' hs'
    have h : ¬∃ s, e s = s' := fun ⟨s, hs⟩ => hs' ⟨s, hs⟩
    simp [padOf, h]
  · intro s
    simp [padOf]

/-- Coordinates of the extension by zero. -/
theorem padMap_apply (e : S ↪ S') (Ψ : Joint S V) (s' : S') :
    padMap e V Ψ s' =
      haveI := Classical.propDecidable (∃ s, e s = s')
      if h : ∃ s, e s = s' then Ψ h.choose else 0 := by
  rw [padMap_eq_padOf]
  change (haveI := Classical.propDecidable (∃ s, e s = s')
    if h : ∃ s, e s = s' then Joint.proj h.choose else 0 : Joint S V →L[ℂ] V) Ψ = _
  split_ifs <;> rfl

/-- The extension by zero on the image of the embedding. -/
@[simp] theorem padMap_apply_emb (e : S ↪ S') (Ψ : Joint S V) (s : S) :
    padMap e V Ψ (e s) = Ψ s := by
  have h : ∃ t, e t = e s := ⟨s, rfl⟩
  rw [padMap_apply, dif_pos h, e.injective h.choose_spec]

/-- The extension by zero off the image of the embedding. -/
theorem padMap_apply_of_not (e : S ↪ S') (Ψ : Joint S V) {s' : S'} (h : ¬∃ s, e s = s') :
    padMap e V Ψ s' = 0 := by
  rw [padMap_apply, dif_neg h]

/-- The extension by zero is an isometry. -/
theorem padMap_isometry (e : S ↪ S') : (padMap e V)† ∘L padMap e V = 1 := by
  rw [padMap, ContinuousLinearMap.adjoint_adjoint, ← padMap]
  ext Ψ s
  simp only [ContinuousLinearMap.comp_apply, restrictMap_apply, padMap_apply_emb]
  rfl

/-- The extension by zero commutes with every spectator lift. -/
theorem fiber_comp_padMap (e : S ↪ S') (A : V →L[ℂ] V) :
    Joint.fiber (fun _ : S' => A) ∘L padMap e V = padMap e V ∘L Joint.fiber (fun _ : S => A) := by
  ext Ψ s'
  simp only [ContinuousLinearMap.comp_apply, Joint.fiber_apply]
  by_cases h : ∃ s, e s = s'
  · obtain ⟨s, rfl⟩ := h
    simp only [padMap_apply_emb, Joint.fiber_apply]
  · rw [padMap_apply_of_not e _ h, padMap_apply_of_not e _ h, map_zero]

end Pad

omit [CompleteSpace V] in
/-- `dim (ℂ^S ⊗ V) = |S| · dim V`. -/
theorem finrank_joint (S : Type) [Fintype S] [FiniteDimensional ℂ V] :
    Module.finrank ℂ (Joint S V) = Fintype.card S * Module.finrank ℂ V := by
  show Module.finrank ℂ (PiLp 2 fun _ : S => V) = _
  rw [(WithLp.linearEquiv 2 ℂ _).finrank_eq, Module.finrank_pi_fintype]
  simp

/-- **Spectator absorption.** Two spectator forms of the same primitive family on
finite-dimensional workspaces with `|J| · dim W ≤ dim W'` are intertwined by an isometry
`ℂ^J ⊗ W → W'`: `O'_l(x) ∘ V = V ∘ (1_J ⊗ O_l(x))` for every label and input. -/
theorem exists_absorb {J : Type} [Fintype J] {O : L → X → W →L[ℂ] W}
    {O' : L → X → W' →L[ℂ] W'} {P : L → X → V →L[ℂ] V} [FiniteDimensional ℂ V]
    (hO : SpectatorForm O P) (hO' : SpectatorForm O' P)
    (hdim : Fintype.card J * Module.finrank ℂ W ≤ Module.finrank ℂ W') :
    ∃ Vm : Joint J W →L[ℂ] W', Vm† ∘L Vm = 1 ∧
      ∀ l x, O' l x ∘L Vm = Vm ∘L Joint.fiber (fun _ : J => O l x) := by
  obtain ⟨S, _, U, hU⟩ := hO
  obtain ⟨S', _, U', hU'⟩ := hO'
  have hW : Module.finrank ℂ W = Fintype.card S * Module.finrank ℂ V := by
    rw [U.toLinearEquiv.finrank_eq, finrank_joint]
  have hW' : Module.finrank ℂ W' = Fintype.card S' * Module.finrank ℂ V := by
    rw [U'.toLinearEquiv.finrank_eq, finrank_joint]
  rcases Nat.eq_zero_or_pos (Module.finrank ℂ V) with hV | hV
  · have hV0 : ∀ v : V, v = 0 := fun v => (Module.finrank_zero_iff.mp hV).elim v 0
    have hW0 : ∀ w : W, w = 0 := fun w =>
      U.injective (by rw [map_zero]; exact PiLp.ext fun s => hV0 _)
    have hJ0 : ∀ Ψ : Joint J W, Ψ = 0 := fun Ψ => PiLp.ext fun j => hW0 _
    refine ⟨0, ?_, fun l x => ?_⟩
    · ext Ψ
      rw [hJ0 Ψ, map_zero, map_zero]
    · ext Ψ
      rw [hJ0 Ψ, map_zero, map_zero]
  · rw [hW, hW', ← mul_assoc] at hdim
    have hcard : Fintype.card (J × S) ≤ Fintype.card S' := by
      rw [Fintype.card_prod]
      exact Nat.le_of_mul_le_mul_right hdim hV
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
    have hUiso : (U.toLinearIsometry.toContinuousLinearMap)† ∘L
        U.toLinearIsometry.toContinuousLinearMap = 1 :=
      (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp fun x => U.norm_map x
    refine ⟨U'.symm.toLinearIsometry.toContinuousLinearMap ∘L padMap e V ∘L
      (ODELowerBoundExtensions.Release.jointFlatten J S V).symm.toLinearIsometry.toContinuousLinearMap
        ∘L Adaptive.Access.jointMap J U.toLinearIsometry.toContinuousLinearMap, ?_, fun l x => ?_⟩
    · refine (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp fun Ψ => ?_
      have hpad := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr (padMap_isometry (V := V) e)
      have hjm := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr
        (Adaptive.Access.jointMap_isometry J _ hUiso)
      simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.norm_map, hpad, hjm]
    · rw [hU', hU]
      ext Ψ
      have hfl : ∀ (Y : Joint J (Joint S V)) (j : J) (s : S),
          (ODELowerBoundExtensions.Release.jointFlatten J S V).symm Y (j, s) = Y j s :=
        fun Y j s => by
          rw [← ODELowerBoundExtensions.Release.jointFlatten_apply,
            LinearIsometryEquiv.apply_symm_apply]
      simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
        LinearIsometryEquiv.symm_symm, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometryEquiv.coe_toLinearIsometry, LinearIsometryEquiv.apply_symm_apply]
      congr 1
      rw [← ContinuousLinearMap.comp_apply (Joint.fiber fun _ : S' => P l x), fiber_comp_padMap,
        ContinuousLinearMap.comp_apply]
      congr 1
      ext ⟨j, s⟩
      simp only [Joint.fiber_apply, hfl, Adaptive.Access.jointMap_apply,
        LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry,
        LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.symm_symm,
        LinearIsometryEquiv.apply_symm_apply]

set_option synthInstance.maxHeartbeats 400000 in
/-- **An inverse by conjugation passes to the spectator form**: if `P_l† = N P_l N†` for a known
unitary `N`, then `O_l† = N' O_l N'†` with `N' = U⁻¹ (1_S ⊗ N) U`. -/
theorem SpectatorForm.nonempty_inverseConj {O : L → X → W →L[ℂ] W} {P : L → X → V →L[ℂ] V}
    (hO : SpectatorForm O P) {l : L} (N : InverseConj P l) : Nonempty (InverseConj O l) := by
  obtain ⟨S, _, U, hU⟩ := hO
  refine ⟨⟨U.symm.conjStarAlgEquiv (Joint.fiber fun _ : S => N.conj),
    (PhaseCircuit.isUnitary_fiber _ fun _ => N.unitary).transport U.symm, fun x => ?_⟩⟩
  have hF : star (Joint.fiber fun _ : S => P l x) =
      Joint.fiber (fun _ : S => N.conj) * Joint.fiber (fun _ : S => P l x) *
        star (Joint.fiber fun _ : S => N.conj) := by
    rw [Joint.star_fiber, Joint.star_fiber, Joint.fiber_mul, Joint.fiber_mul]
    exact congrArg Joint.fiber (funext fun _ => N.star_eq x)
  rw [hU]
  simpa only [map_mul, map_star] using congrArg U.symm.conjStarAlgEquiv hF

end

end ReleasedODESolverLowerBounds.Access
