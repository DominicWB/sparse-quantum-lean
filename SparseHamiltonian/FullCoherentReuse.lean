import SparseHamiltonian.CoherentReuse

/-!
# Full coherent reuse with its private output retained

The successful block derived in `CoherentReuse` is the compression of a
norm-preserving map on the full Hilbert space, with a genuinely isometric
initialization into the zero-private, uniform-public subspace.
-/

namespace SparseHamiltonian.CoherentReuse

noncomputable section

open ContinuousLinearMap
open ChronologicalResolvent FiniteChronologicalInverse ChronologicalCatalyst
open GlobalColligation
open scoped BigOperators InnerProduct

variable {P V : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- The full chronological reuse map retains both the common private register
and the public time slots. -/
def fullReuse (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (n : ℕ) :
    WithLp 2 (V × BlockOperator.H n P) →L[ℂ] WithLp 2 (V × BlockOperator.H n P) :=
  blockMap (D ^ n) (publicExit D C n) (stackedResponse B D n) (publicReuse A B C D n)

omit [CompleteSpace P] [CompleteSpace V] in
/-- Local energy conservation proves norm preservation of the complete circuit. -/
theorem fullReuse_norm (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (n : ℕ) (x : WithLp 2 (V × BlockOperator.H n P)) :
    ‖fullReuse A B C D n x‖ = ‖x‖ :=
  chronological_blockMap_norm A B D C hStep n x

/-- The complete reuse map has isometric columns. -/
theorem fullReuse_adjoint_comp (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (n : ℕ) : (fullReuse A B C D n)† ∘L fullReuse A B C D n = 1 := by
  have hi := (LinearMap.norm_map_iff_inner_map_map (fullReuse A B C D n)).mp
    (fullReuse_norm A B C D hStep n)
  ext x
  apply ext_inner_right ℂ
  intro y
  simpa only [comp_apply, adjoint_inner_left, one_def, id_apply] using hi x y

/-- In finite dimensions the complete reuse map is a genuine two-sided unitary. -/
theorem fullReuse_unitary [FiniteDimensional ℂ P] [FiniteDimensional ℂ V]
    (A : P →L[ℂ] P) (B : V →L[ℂ] P) (C : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hStep : ∀ p v, ‖A p + B v‖ ^ 2 + ‖D v + C p‖ ^ 2 = ‖p‖ ^ 2 + ‖v‖ ^ 2)
    (n : ℕ) : (fullReuse A B C D n)† ∘L fullReuse A B C D n = 1 ∧
      fullReuse A B C D n ∘L (fullReuse A B C D n)† = 1 :=
  chronological_blockMap_unitary A B D C hStep n

/-- Initialize the common private register to zero and the public slots uniformly. -/
def initialEmbedding (n : ℕ) : P →L[ℂ] WithLp 2 (V × BlockOperator.H n P) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ V (BlockOperator.H n P)).symm.toContinuousLinearMap ∘L
    (0 : P →L[ℂ] V).prod (uniformEmbedding n)

omit [CompleteSpace P] [CompleteSpace V] in
@[simp] theorem initialEmbedding_apply (n : ℕ) (p : P) :
    (initialEmbedding n : P →L[ℂ] WithLp 2 (V × BlockOperator.H n P)) p =
      WithLp.toLp 2 (0, uniformEmbedding n p) := rfl

omit [CompleteSpace P] [CompleteSpace V] in
/-- The initialization is an isometry for nonzero reuse length. -/
theorem initialEmbedding_norm (n : ℕ) (hn : n ≠ 0) (p : P) :
    ‖(initialEmbedding n : P →L[ℂ] WithLp 2 (V × BlockOperator.H n P)) p‖ = ‖p‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [initialEmbedding_apply, WithLp.prod_norm_sq_eq_of_L2, WithLp.fst,
    WithLp.snd, norm_zero, zero_pow (by omega : 2 ≠ 0), zero_add, uniformEmbedding_norm n hn]

/-- Successful postselection discards the private coordinate and averages the
public slots with the adjoint uniform preparation. -/
theorem initialEmbedding_adjoint_apply (n : ℕ) (x : WithLp 2 (V × BlockOperator.H n P)) :
    ((initialEmbedding n : P →L[ℂ] WithLp 2 (V × BlockOperator.H n P))†) x =
      ((uniformEmbedding n)†) x.snd := by
  apply ext_inner_right ℂ
  intro p
  simp only [adjoint_inner_left, initialEmbedding_apply, WithLp.prod_inner_apply,
    WithLp.snd, inner_zero_right, zero_add]

/-- The concrete preparation and its adjoint meet the LCU isometry interface. -/
theorem initialEmbedding_adjoint_comp (n : ℕ) (hn : n ≠ 0) :
    (initialEmbedding n : P →L[ℂ] WithLp 2 (V × BlockOperator.H n P))† ∘L
      initialEmbedding n = 1 := by
  ext p
  simp only [comp_apply, initialEmbedding_adjoint_apply, initialEmbedding_apply,
    WithLp.snd]
  exact congrArg (fun L : P →L[ℂ] P => L p) (uniformEmbedding_adjoint_comp n hn)

/-- Uniform compression of the full map equals the previously derived public
successful block, with no condition on the private output. -/
theorem fullReuse_compression (A : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C : P →L[ℂ] V) (D : V →L[ℂ] V) (n : ℕ) :
    (initialEmbedding n)† ∘L fullReuse A B C D n ∘L initialEmbedding n =
      successfulBlock A B C D n := by
  ext p
  simp only [comp_apply, initialEmbedding_apply, initialEmbedding_adjoint_apply,
    fullReuse, blockMap_apply, WithLp.fst, WithLp.snd, map_zero, zero_add,
    successfulBlock]

/-- The full norm-preserving reuse construction has the claimed successful
block under the two catalyst transduction equations. -/
theorem fullReuse_compression_eq (A U : P →L[ℂ] P) (B : V →L[ℂ] P)
    (C Γ : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hPublic : A + B ∘L Γ = U) (hPrivate : C + D ∘L Γ = Γ)
    (n : ℕ) (hn : n ≠ 0) :
    (initialEmbedding n)† ∘L fullReuse A B C D n ∘L initialEmbedding n =
      U - B ∘L averagedGeometricFilter D n ∘L Γ := by
  rw [fullReuse_compression, successfulBlock_eq A U B C Γ D hPublic hPrivate n hn]

omit [CompleteSpace P] [CompleteSpace V] in
/-- The final private register is the geometric boundary response, derived by
comparing the finite convolution with the solved constant-input recurrence. -/
theorem finalPrivate_uniform (C Γ : P →L[ℂ] V) (D : V →L[ℂ] V)
    (hPrivate : C + D ∘L Γ = Γ) (n : ℕ) (p : P) :
    publicExit D C n (uniformEmbedding n p) =
      (uniformAmplitude n : ℂ) • (Γ p - (D ^ n) (Γ p)) := by
  have h := sharedPrivate_constant C Γ D hPrivate p (uniformAmplitude n : ℂ) n
  rw [forcedPublicState_eq_sum, ← Fin.sum_univ_eq_sum_range] at h
  rw [publicExit_apply, forcedPublicState_eq_sum, ← Fin.sum_univ_eq_sum_range]
  simpa only [extendSequence_apply, uniformEmbedding_apply] using h

end

end SparseHamiltonian.CoherentReuse
