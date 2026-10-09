import SparseLowerBounds.Helpers.Adaptive.Access.Wrappers

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Fixed register relabellings and homogeneous spectators

Generic register lemmas for `Release/Normal` (manuscript lines 3669-3673: every matrix label of
the released ODE solver is one call of the sampled-time native query, with untouched spectator
registers and fixed register relabellings).

* `diagonal_conj`: a block diagonal of conjugated blocks is the conjugate of the block
  diagonal by the fixed blockwise relabelling;
* `diagonal_fiber`: a block diagonal of homogeneous spectators is a homogeneous spectator of
  the block diagonal, up to the fixed register swap `jointSwap`;
* `fiber_conj`: a homogeneous spectator of a conjugate is a conjugate of the spectator;
* `fiber_fiber`: two nested homogeneous spectators are one spectator on the product register,
  up to the fixed flattening `jointFlatten`.

`IsWrap W` says that `W` consists of untouched spectators and fixed relabellings only: there is
one fixed isometric identification `U` with `W A = U⁻¹ (1_Ω ⊗ A) U` for every `A`. Wrappers are
closed under spectators (`IsWrap.fiber`, `IsWrap.masked`, `IsWrap.diagonalConst`,
`IsWrap.spectator`), fixed conjugations (`IsWrap.conj`, `IsWrap.precomp`) and composition
(`IsWrap.comp`), and the block diagonal of a wrapper is a wrapper of the block diagonal
(`IsWrap.diagonal`).
-/

namespace ODELowerBoundExtensions.Release

noncomputable section
open SparseHamiltonian SparseLowerBounds Helpers.Adaptive.Access
open scoped InnerProduct

section Equivalences

variable (Ω₁ Ω₂ : Type) [Fintype Ω₁] [Fintype Ω₂]
  (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The fixed flattening `ℂ^{Ω₁ × Ω₂} ⊗ K ≃ ℂ^{Ω₁} ⊗ (ℂ^{Ω₂} ⊗ K)` of nested registers. -/
def jointFlatten : Joint (Ω₁ × Ω₂) K ≃ₗᵢ[ℂ] Joint Ω₁ (Joint Ω₂ K) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ K (Equiv.sigmaEquivProd Ω₁ Ω₂).symm).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : Ω₁) (_ : Ω₂) => K))

/-- The fixed swap `ℂ^{Ω₁} ⊗ (ℂ^{Ω₂} ⊗ K) ≃ ℂ^{Ω₂} ⊗ (ℂ^{Ω₁} ⊗ K)` of two registers. -/
def jointSwap : Joint Ω₁ (Joint Ω₂ K) ≃ₗᵢ[ℂ] Joint Ω₂ (Joint Ω₁ K) :=
  (jointFlatten Ω₁ Ω₂ K).symm.trans
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ K (Equiv.prodComm Ω₁ Ω₂)).trans
      (jointFlatten Ω₂ Ω₁ K))

/-- Coordinates of the flattening. -/
@[simp] theorem jointFlatten_apply (Ψ : Joint (Ω₁ × Ω₂) K) (a : Ω₁) (b : Ω₂) :
    jointFlatten Ω₁ Ω₂ K Ψ a b = Ψ (a, b) := rfl

end Equivalences

section Generic

variable {K E F : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A block diagonal of conjugated blocks is the conjugate of the block diagonal by the
fixed blockwise relabelling `1 ⊗ V`. -/
theorem diagonal_conj {κ : Type*} [Fintype κ] (V : K ≃ₗᵢ[ℂ] E) (A : κ → K →L[ℂ] K) :
    WeightedClock.diagonal (fun b => V.conjStarAlgEquiv (A b)) =
      (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : κ => V)).conjStarAlgEquiv
        (WeightedClock.diagonal A) := by
  ext Ψ b
  rfl

/-- A block diagonal of homogeneous spectators is the homogeneous spectator of the
block diagonal, up to the fixed register swap. -/
theorem diagonal_fiber {κ Ω : Type} [Fintype κ] [Fintype Ω] (A : κ → K →L[ℂ] K) :
    WeightedClock.diagonal (fun b => Joint.fiber (fun _ : Ω => A b)) =
      (jointSwap Ω κ K).conjStarAlgEquiv
        (Joint.fiber (fun _ : Ω => WeightedClock.diagonal A)) := by
  ext Ψ b ω
  rfl

/-- A homogeneous spectator of a conjugate is the conjugate of the spectator by the
fixed relabelling `1_Ω ⊗ V`. -/
theorem fiber_conj {Ω : Type} [Fintype Ω] (V : K ≃ₗᵢ[ℂ] E) (A : K →L[ℂ] K) :
    Joint.fiber (fun _ : Ω => V.conjStarAlgEquiv A) =
      (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Ω => V)).conjStarAlgEquiv
        (Joint.fiber (fun _ : Ω => A)) := by
  ext Ψ ω
  rfl

/-- Two nested homogeneous spectators are one homogeneous spectator on the product
register, up to the fixed flattening. -/
theorem fiber_fiber {Ω₁ Ω₂ : Type} [Fintype Ω₁] [Fintype Ω₂] (A : K →L[ℂ] K) :
    Joint.fiber (fun _ : Ω₁ => Joint.fiber (fun _ : Ω₂ => A)) =
      (jointFlatten Ω₁ Ω₂ K).conjStarAlgEquiv (Joint.fiber (fun _ : Ω₁ × Ω₂ => A)) := by
  ext Ψ a b
  rfl

/-- **Spectator wrappers**: `W` consists of untouched spectators and fixed relabellings, i.e.
there are a finite spectator register `Ω` and one fixed isometric identification `U` of `E` with
`ℂ^Ω ⊗ K` such that `W A = U⁻¹ (1_Ω ⊗ A) U` for every operator `A` on `K`. -/
def IsWrap (W : (K →L[ℂ] K) → (E →L[ℂ] E)) : Prop :=
  ∃ (Ω : Type) (_ : Fintype Ω) (U : E ≃ₗᵢ[ℂ] Joint Ω K),
    ∀ A, W A = U.symm.conjStarAlgEquiv (Joint.fiber (fun _ : Ω => A))

/-- The homogeneous spectator itself is a wrapper. -/
theorem isWrap_fiber (Ω : Type) [Fintype Ω] :
    IsWrap (fun A : K →L[ℂ] K => Joint.fiber (fun _ : Ω => A)) :=
  ⟨Ω, inferInstance, LinearIsometryEquiv.refl ℂ _, fun _ => rfl⟩

namespace IsWrap

/-- Post-composition with a fixed relabelling. -/
theorem conj {W : (K →L[ℂ] K) → (E →L[ℂ] E)} (hW : IsWrap W) (V : E ≃ₗᵢ[ℂ] F) :
    IsWrap (fun A => V.conjStarAlgEquiv (W A)) := by
  obtain ⟨Ω, _, U, hU⟩ := hW
  exact ⟨Ω, inferInstance, V.symm.trans U, fun A => by beta_reduce; rw [hU A]; rfl⟩

/-- Pre-composition with a fixed relabelling. -/
theorem precomp {W : (E →L[ℂ] E) → (F →L[ℂ] F)} (hW : IsWrap W) (V : K ≃ₗᵢ[ℂ] E) :
    IsWrap (fun A : K →L[ℂ] K => W (V.conjStarAlgEquiv A)) := by
  obtain ⟨Ω, _, U, hU⟩ := hW
  refine ⟨Ω, inferInstance,
    U.trans (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Ω => V.symm)), fun A => ?_⟩
  beta_reduce
  rw [hU, fiber_conj]
  rfl

/-- A homogeneous spectator of a wrapper is a wrapper. -/
theorem fiber {W : (K →L[ℂ] K) → (E →L[ℂ] E)} (hW : IsWrap W) (Ω' : Type) [Fintype Ω'] :
    IsWrap (fun A => Joint.fiber (fun _ : Ω' => W A)) := by
  obtain ⟨Ω, _, U, hU⟩ := hW
  refine ⟨Ω' × Ω, inferInstance,
    (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Ω' => U)).trans
      (jointFlatten Ω' Ω K).symm, fun A => ?_⟩
  simp only [hU]
  rw [fiber_conj, fiber_fiber]
  rfl

/-- Composition of wrappers. -/
theorem comp {W : (K →L[ℂ] K) → (E →L[ℂ] E)} {W' : (E →L[ℂ] E) → (F →L[ℂ] F)}
    (hW : IsWrap W) (hW' : IsWrap W') : IsWrap (fun A => W' (W A)) := by
  obtain ⟨Ω', _, U', hU'⟩ := hW'
  obtain ⟨Ω, _, U, hU⟩ := (hW.fiber Ω').conj U'.symm
  exact ⟨Ω, inferInstance, U, fun A => by beta_reduce at hU ⊢; rw [hU' (W A)]; exact hU A⟩

/-- The all-active branch mask of a wrapper is a wrapper. -/
theorem masked {W : (K →L[ℂ] K) → (E →L[ℂ] E)} (hW : IsWrap W) (ι : Type) [Fintype ι] :
    IsWrap (fun A => MaskedProgram.masked (fun _ : ι => true) (W A)) := by
  simpa only [masked_true_eq_fiber] using hW.fiber ι

/-- The constant block diagonal of a wrapper is a wrapper. -/
theorem diagonalConst {W : (K →L[ℂ] K) → (E →L[ℂ] E)} (hW : IsWrap W) (ι : Type) [Fintype ι] :
    IsWrap (fun A => WeightedClock.diagonal (fun _ : ι => W A)) := by
  simpa only [diagonal_const_eq_fiber] using hW.fiber ι

/-- A flattened spectator register (`LookupFromBasisOracle.spectator`) of a wrapper is a
wrapper. -/
theorem spectator {S B : Type} [Fintype S] [Fintype B]
    {W : (K →L[ℂ] K) → (EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B)} (hW : IsWrap W) :
    IsWrap (fun A => LookupFromBasisOracle.spectator (S := S) (W A)) := by
  simpa only [spectator_eq_conj_fiber] using
    (hW.fiber S).conj (RegisterEquivalences.productFlatten S B)

/-- **The block diagonal of a wrapper is a wrapper of the block diagonal**: for every finite
`κ` there is one fixed identification `U` with
`diag_b W (A b) = U⁻¹ (1_Ω ⊗ diag_b A b) U` for every family `A`. -/
theorem diagonal {W : (K →L[ℂ] K) → (E →L[ℂ] E)} (hW : IsWrap W) (κ : Type) [Fintype κ] :
    ∃ (Ω : Type) (_ : Fintype Ω) (U : PiLp 2 (fun _ : κ => E) ≃ₗᵢ[ℂ] Joint Ω (Joint κ K)),
      ∀ A : κ → K →L[ℂ] K, WeightedClock.diagonal (fun b => W (A b)) =
        U.symm.conjStarAlgEquiv (Joint.fiber (fun _ : Ω => WeightedClock.diagonal A)) := by
  obtain ⟨Ω, _, U, hU⟩ := hW
  refine ⟨Ω, inferInstance,
    (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : κ => U)).trans (jointSwap Ω κ K).symm,
    fun A => ?_⟩
  simp only [hU]
  rw [diagonal_conj, diagonal_fiber, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.conjStarAlgEquiv_trans,
    LinearIsometryEquiv.piLpCongrRight_symm, StarAlgEquiv.trans_apply]

end IsWrap

/-- A flattened spectator register (`LookupFromBasisOracle.spectator`) is a wrapper. -/
theorem isWrap_spectator (S B : Type) [Fintype S] [Fintype B] :
    IsWrap (fun A : EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B =>
      LookupFromBasisOracle.spectator (S := S) A) := by
  simpa only [spectator_eq_conj_fiber] using
    (isWrap_fiber (K := EuclideanSpace ℂ B) S).conj (RegisterEquivalences.productFlatten S B)

end Generic

end

end ODELowerBoundExtensions.Release
