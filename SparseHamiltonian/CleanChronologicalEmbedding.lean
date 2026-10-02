import SparseHamiltonian.NativeSparseWholeProgram

namespace SparseHamiltonian.CleanChronologicalEmbedding

noncomputable section
open ContinuousLinearMap ReuseLayerFactorization
open scoped InnerProduct

variable {P Q V W : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P]
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- Embed every private chronological cell and every public reuse cell. Both
maps are fixed, and no data-dependent circuit is hidden in this preparation. -/
def embedding (eP : P →ₗᵢ[ℂ] Q) (eV : V →ₗᵢ[ℂ] W) (T d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := ChronologicalResolvent.BlockOperator.H T V) d) →ₗᵢ[ℂ]
      PiLp 2 (SmoothingLCU.BranchSpace (P := Q) (V := ChronologicalResolvent.BlockOperator.H T W) d) where
  toLinearMap :=
    { toFun := fun x => WithLp.toLp 2 (fun i => WithLp.toLp 2
        (WithLp.toLp 2 (fun t => eV ((x i).fst t)),
          WithLp.toLp 2 (fun j => eP ((x i).snd j))))
      map_add' := by
        intro x y
        apply PiLp.ext
        intro i
        apply WithLp.ofLp_injective 2
        apply Prod.ext
        · apply PiLp.ext
          intro t
          exact eV.map_add _ _
        · apply PiLp.ext
          intro j
          exact eP.map_add _ _
      map_smul' := by
        intro z x
        apply PiLp.ext
        intro i
        apply WithLp.ofLp_injective 2
        apply Prod.ext
        · apply PiLp.ext
          intro t
          exact eV.map_smul z _
        · apply PiLp.ext
          intro j
          exact eP.map_smul z _ }
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    change (∑ i, ((∑ t, ‖eV ((x i).fst t)‖ ^ 2) +
        ∑ j, ‖eP ((x i).snd j)‖ ^ 2)) =
      ∑ i, ((∑ t, ‖(x i).fst t‖ ^ 2) + ∑ j, ‖(x i).snd j‖ ^ 2)
    simp only [LinearIsometry.norm_map]

variable [CompleteSpace P] [CompleteSpace Q] [CompleteSpace V] [CompleteSpace W]

omit [CompleteSpace P] [CompleteSpace Q] [CompleteSpace V] [CompleteSpace W] in
/-- A clean implementation on one cell extends to all chronological copies,
including inactive branches and every public bypass. -/
theorem active_intertwines (eP : P →ₗᵢ[ℂ] Q) (eV : V →ₗᵢ[ℂ] W)
    (U : W →L[ℂ] W) (D : V →L[ℂ] V)
    (h : U ∘L eV.toContinuousLinearMap = eV.toContinuousLinearMap ∘L D)
    (T d r : ℕ) :
    activeClock (P := Q) U T d r ∘L (embedding eP eV T d).toContinuousLinearMap =
      (embedding eP eV T d).toContinuousLinearMap ∘L activeClock (P := P) D T d r := by
  have hv (v : V) : U (eV v) = eV (D v) :=
    congrArg (fun A : V →L[ℂ] W => A v) h
  ext x i
  by_cases hr : r < ReuseWeights.length d i
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply PiLp.ext
      intro t
      simp [activeClock, activeQuery, activeBranch, hr, embedding, hv]
    · apply PiLp.ext
      intro j
      simp [activeClock, activeQuery, activeBranch, hr, embedding]
  · simp [activeClock, activeQuery, activeBranch, hr, embedding]

end
end SparseHamiltonian.CleanChronologicalEmbedding
