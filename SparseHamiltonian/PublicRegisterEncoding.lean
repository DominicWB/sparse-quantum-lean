import SparseHamiltonian.FlattenedLookupClockBounds

/-!
# Embedding public registers without changing private clocks

A fixed isometric encoding of the public system is applied to every public
reuse slot. All shared private registers remain untouched. Active private clock
operations therefore intertwine this encoding exactly, allowing their full
physical implementations to serve a smaller logical public system. No cost for
preparing the encoding is asserted.
-/

namespace SparseHamiltonian.PublicRegisterEncoding

noncomputable section
open ContinuousLinearMap ChronologicalResolvent ReuseLayerFactorization OracleCircuit
open scoped InnerProduct

variable {P K V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Apply the fixed public encoding to each reuse slot, preserving private data. -/
def workspaceEmbedding (e : P →ₗᵢ[ℂ] K) (d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) d) →ₗᵢ[ℂ]
      PiLp 2 (SmoothingLCU.BranchSpace (P := K) (V := V) d) where
  toLinearMap :=
    { toFun := fun x => WithLp.toLp 2 (fun i => WithLp.toLp 2
        ((x i).fst, WithLp.toLp 2 (fun j => e ((x i).snd j))))
      map_add' := by
        intro x y
        apply PiLp.ext
        intro i
        apply WithLp.ofLp_injective 2
        apply Prod.ext
        · rfl
        · apply PiLp.ext
          intro j
          exact e.map_add _ _
      map_smul' := by
        intro z x
        apply PiLp.ext
        intro i
        apply WithLp.ofLp_injective 2
        apply Prod.ext
        · rfl
        · apply PiLp.ext
          intro j
          exact e.map_smul z _ }
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    change (∑ i, (‖(x i).fst‖ ^ 2 + ∑ j, ‖e ((x i).snd j)‖ ^ 2)) =
      ∑ i, (‖(x i).fst‖ ^ 2 + ∑ j, ‖(x i).snd j‖ ^ 2)
    simp only [LinearIsometry.norm_map]

@[simp] theorem workspaceEmbedding_private (e : P →ₗᵢ[ℂ] K) (d : ℕ)
    (x : PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) d))
    (i : ReuseWeights.Index d) :
    ((workspaceEmbedding e d) x i).fst = (x i).fst := rfl

@[simp] theorem workspaceEmbedding_public (e : P →ₗᵢ[ℂ] K) (d : ℕ)
    (x : PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) d))
    (i : ReuseWeights.Index d) (j : Fin (ReuseWeights.length d i)) :
    ((workspaceEmbedding e d) x i).snd j = e ((x i).snd j) := rfl

/-- The bounded operator associated with the fixed isometric workspace encoding. -/
abbrev embedding (e : P →ₗᵢ[ℂ] K) (d : ℕ) :
    PiLp 2 (SmoothingLCU.BranchSpace (P := P) (V := V) d) →L[ℂ]
      PiLp 2 (SmoothingLCU.BranchSpace (P := K) (V := V) d) :=
  (workspaceEmbedding e d).toContinuousLinearMap

variable [CompleteSpace P] [CompleteSpace K] [CompleteSpace V]

/-- The complete encoding is isometric on every public and private register. -/
theorem embedding_adjoint_comp (e : P →ₗᵢ[ℂ] K) (d : ℕ) :
    (embedding (V := V) e d)† ∘L embedding e d = 1 :=
  LinearIsometry.adjoint_comp_self _

omit [CompleteSpace P] [CompleteSpace K] [CompleteSpace V] in
/-- Changing the public register commutes with every active private operation. -/
theorem activeQuery_intertwines (e : P →ₗᵢ[ℂ] K) (D : V →L[ℂ] V) (d r : ℕ) :
    activeQuery (P := K) D d r ∘L embedding e d =
      embedding e d ∘L activeQuery (P := P) D d r := by
  ext x i
  by_cases h : r < ReuseWeights.length d i
  · apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simp [activeQuery, activeBranch, h, embedding, workspaceEmbedding]
    · apply PiLp.ext
      intro j
      simp [activeQuery, activeBranch, h, embedding, workspaceEmbedding]
  · simp [activeQuery, activeBranch, h, embedding, workspaceEmbedding]

omit [CompleteSpace P] [CompleteSpace K] [CompleteSpace V] in
/-- Parallel chronological clock operations preserve the same fixed encoding. -/
theorem activeClock_intertwines (e : P →ₗᵢ[ℂ] K) (D : V →L[ℂ] V) (T d r : ℕ) :
    activeClock (P := K) D T d r ∘L embedding e d =
      embedding e d ∘L activeClock (P := P) D T d r :=
  activeQuery_intertwines e (WeightedClock.diagonal (fun _ : Fin T => D)) d r

omit [CompleteSpace P] in
/-- A full physical active clock implementation supplies the corresponding
logical encoded implementation at the same query cost. -/
theorem activeClock_implementsOn {X : Type*}
    (e : P →ₗᵢ[ℂ] K) (D : X → V →L[ℂ] V) (T d r q : ℕ)
    (O : X → PiLp 2 (SmoothingLCU.BranchSpace (P := K) (V := BlockOperator.H T V) d) →L[ℂ]
      PiLp 2 (SmoothingLCU.BranchSpace (P := K) (V := BlockOperator.H T V) d))
    (h : Implements O (fun x => activeClock (P := K) (D x) T d r) q) :
    EncodedOracle.ImplementsOn O (fun x => activeClock (P := P) (D x) T d r)
      (embedding e d) q :=
  EncodedOracle.ImplementsOn.of_full h (fun x => activeClock_intertwines e (D x) T d r)

end
end SparseHamiltonian.PublicRegisterEncoding
