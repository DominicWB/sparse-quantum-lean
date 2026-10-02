import SparseHamiltonian.ActiveClockAlgebra

/-!
# A fixed register layout for active clock queries

The chronological, reuse, and clock labels are flattened into one direct-sum
label. This equivalence is independent of the step number, the oracle input,
and every operator acting on the payload. Public reuse slots are retained as
separate labels, so their bypass action is an explicit identity block.
-/

namespace SparseHamiltonian.ActiveRegisterLayout

noncomputable section
open ContinuousLinearMap ChronologicalResolvent
open scoped BigOperators InnerProduct

/-- Private clock coordinates and public reuse coordinates in a common register. -/
abbrev Label (C : Type*) (T d : ℕ) :=
  ((ReuseWeights.Index d × Fin T) × C) ⊕
    (Σ i : ReuseWeights.Index d, Fin (ReuseWeights.length d i))

/-- The exact space on which the active chronological clock acts. -/
abbrev Space (K C : Type*) (T d : ℕ) :=
  PiLp 2 (SmoothingLCU.BranchSpace (P := K)
    (V := BlockOperator.H T (PiLp 2 (fun _ : C => K))) d)

variable (K C : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [Fintype C]

/-- Fixed flattening of all branch, time, clock, and public-slot labels. -/
def layout (T d : ℕ) : Space K C T d ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Label C T d => K) where
  toLinearEquiv :=
    { toFun := fun x => WithLp.toLp 2 (fun l => match l with
        | .inl ((i, t), c) => (x i).fst t c
        | .inr ⟨i, j⟩ => (x i).snd j)
      invFun := fun x => WithLp.toLp 2 (fun i => WithLp.toLp 2
        (WithLp.toLp 2 (fun t => WithLp.toLp 2 (fun c => x (.inl ((i, t), c)))),
          WithLp.toLp 2 (fun j => x (.inr ⟨i, j⟩))))
      left_inv := by
        intro x
        apply PiLp.ext
        intro i
        apply WithLp.ofLp_injective 2
        apply Prod.ext
        · apply PiLp.ext
          intro t
          apply PiLp.ext
          intro c
          rfl
        · apply PiLp.ext
          intro j
          rfl
      right_inv := by
        intro x
        apply PiLp.ext
        intro l
        cases l with
        | inl v => rcases v with ⟨⟨i, t⟩, c⟩; rfl
        | inr v => rcases v with ⟨i, j⟩; rfl
      map_add' := by
        intro x y
        apply PiLp.ext
        intro l
        cases l with
        | inl v => rcases v with ⟨⟨i, t⟩, c⟩; rfl
        | inr v => rcases v with ⟨i, j⟩; rfl
      map_smul' := by
        intro z x
        apply PiLp.ext
        intro l
        cases l with
        | inl v => rcases v with ⟨⟨i, t⟩, c⟩; rfl
        | inr v => rcases v with ⟨i, j⟩; rfl }
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2,
      Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sigma,
      Finset.sum_add_distrib]
    rfl

@[simp] theorem layout_private (T d : ℕ) (x : Space K C T d)
    (i : ReuseWeights.Index d) (t : Fin T) (c : C) :
    layout K C T d x (.inl ((i, t), c)) = (x i).fst t c := rfl

@[simp] theorem layout_public (T d : ℕ) (x : Space K C T d)
    (i : ReuseWeights.Index d) (j : Fin (ReuseWeights.length d i)) :
    layout K C T d x (.inr ⟨i, j⟩) = (x i).snd j := rfl

@[simp] theorem layout_symm_private (T d : ℕ)
    (x : PiLp 2 (fun _ : Label C T d => K))
    (i : ReuseWeights.Index d) (t : Fin T) (c : C) :
    (((layout K C T d).symm x) i).fst t c = x (.inl ((i, t), c)) := rfl

@[simp] theorem layout_symm_public (T d : ℕ)
    (x : PiLp 2 (fun _ : Label C T d => K))
    (i : ReuseWeights.Index d) (j : Fin (ReuseWeights.length d i)) :
    (((layout K C T d).symm x) i).snd j = x (.inr ⟨i, j⟩) := rfl

variable {K C}

/-- Payload operators are disabled on finished branches and all public slots. -/
def mask (U : C → K →L[ℂ] K) {T : ℕ} (d r : ℕ) : Label C T d → K →L[ℂ] K
  | .inl ((i, _), c) => if r < ReuseWeights.length d i then U c else 1
  | .inr _ => 1

omit [Fintype C] in
@[simp] theorem mask_private (U : C → K →L[ℂ] K) (T d r : ℕ)
    (i : ReuseWeights.Index d) (t : Fin T) (c : C) :
    mask U (T := T) d r (.inl ((i, t), c)) =
      if r < ReuseWeights.length d i then U c else 1 := rfl

omit [Fintype C] in
@[simp] theorem mask_public (U : C → K →L[ℂ] K) (T d r : ℕ)
    (i : ReuseWeights.Index d) (j : Fin (ReuseWeights.length d i)) :
    mask U (T := T) d r (.inr ⟨i, j⟩) = 1 := rfl

variable [CompleteSpace K]

/-- Fixed register flattening exposes the active clock as independent payload
blocks. The layer index appears only in the mask, not in the encoding. -/
theorem layout_activeClock (U : C → K →L[ℂ] K) (T d r : ℕ) :
    (layout K C T d).conjStarAlgEquiv
      (ReuseLayerFactorization.activeClock (P := K) (WeightedClock.diagonal U) T d r) =
      WeightedClock.diagonal (mask U (T := T) d r) := by
  ext x l
  cases l with
  | inl v =>
      rcases v with ⟨⟨i, t⟩, c⟩
      by_cases h : r < ReuseWeights.length d i
      · simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
          ReuseLayerFactorization.activeClock, ReuseLayerFactorization.activeQuery,
          ReuseLayerFactorization.activeBranch, mask, h]
      · simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
          ReuseLayerFactorization.activeClock, ReuseLayerFactorization.activeQuery,
          ReuseLayerFactorization.activeBranch, mask, h]
  | inr v =>
      rcases v with ⟨i, j⟩
      by_cases h : r < ReuseWeights.length d i
      · simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
          ReuseLayerFactorization.activeClock, ReuseLayerFactorization.activeQuery,
          ReuseLayerFactorization.activeBranch, mask, h]
      · simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
          ReuseLayerFactorization.activeClock, ReuseLayerFactorization.activeQuery,
          ReuseLayerFactorization.activeBranch, mask, h]

end
end SparseHamiltonian.ActiveRegisterLayout
