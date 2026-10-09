import LinearSystemLowerBound.Weight.TreeBound

/-!
# Discarding a garbage register: the partial trace

A solver may leave its output register `I` entangled with a garbage register `G`; its output
state is then the partial trace over `G` of the heralded state on `I × G`.  Matrix entries are
`entry A a b = ⟨e_a, A e_b⟩` (`entry_eq_inner`), and

* `ptrace A` is the partial trace, `(Tr_G A)_{i i'} = ∑_g A_{(i,g),(i',g)}`;
* `ampl B` is `B ⊗ I_G`, the operator `B` on the output register acting trivially on `G`.

The partial trace is characterised by `tr(B Tr_G A) = tr((B ⊗ I_G) A)` for every operator `B`
on the output register (`trace_comp_ptrace`, and uniqueness `ptrace_unique`); hence
`corr B (Tr_G A) = corr (B ⊗ I_G) A` (`corr_ptrace`).  `B ⊗ I_G` is a contraction when `B` is (`norm_ampl_le`), and the partial
trace of a product `|v ⊗ u⟩⟨v ⊗ u|` with a unit garbage vector `u` is `|v⟩⟨v|`
(`ptrace_pure_tmul`).

A general output space `E` is identified with `I × G` by a fixed isometry `V`; correlations
are invariant under this identification (`corr_conjStarAlgEquiv`).  A clean output is the case
of a one-point garbage register (`unitGarbage`, `ptrace_unitGarbage`).
-/

namespace LinearSystemLowerBound

noncomputable section
open scoped BigOperators InnerProductSpace InnerProduct
open SparseHamiltonian

section Entries

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Matrix entries of an operator on a coordinate space. -/
def entry (A : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J) (a b : J) : ℂ :=
  A (EuclideanSpace.single b 1) a

theorem entry_eq_inner (A : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J) (a b : J) :
    entry A a b = ⟪EuclideanSpace.single a (1 : ℂ), A (EuclideanSpace.single b 1)⟫_ℂ := by
  rw [EuclideanSpace.inner_single_left]
  simp [entry]

/-- Every operator acts by its matrix entries. -/
theorem apply_eq_sum_entry (A : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J)
    (v : EuclideanSpace ℂ J) (a : J) : A v a = ∑ b, entry A a b * v b := by
  have hv : v = ∑ b, v b • EuclideanSpace.single b (1 : ℂ) := by
    have h := (EuclideanSpace.basisFun J ℂ).sum_repr v
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at h
    exact h.symm
  conv_lhs => rw [hv]
  rw [map_sum, piLp_sum_apply]
  simp only [map_smul, PiLp.smul_apply, smul_eq_mul, entry]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem entry_matrixOperator (M : Matrix J J ℂ) (a b : J) :
    entry (SparseStateOverlap.matrixOperator M) a b = M a b := by
  simp [entry, SparseStateOverlap.matrixOperator_apply, PiLp.single_apply]

theorem entry_comp (B A : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J) (a c : J) :
    entry (B ∘L A) a c = ∑ b, entry B a b * entry A b c := by
  rw [entry, ContinuousLinearMap.comp_apply, apply_eq_sum_entry]
  rfl

/-- The trace is the sum of the diagonal entries. -/
theorem trace_eq_sum_entry (A : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J) :
    LinearMap.trace ℂ (EuclideanSpace ℂ J) (A : EuclideanSpace ℂ J →ₗ[ℂ] EuclideanSpace ℂ J) =
      ∑ a, entry A a a := by
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun J ℂ)]
  apply Finset.sum_congr rfl
  intro a _
  rw [entry_eq_inner, EuclideanSpace.basisFun_apply]
  rfl

/-- Operators with the same matrix entries are equal. -/
theorem ext_entry {A B : EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ J}
    (h : ∀ a b, entry A a b = entry B a b) : A = B := by
  ext v a
  rw [apply_eq_sum_entry, apply_eq_sum_entry]
  exact Finset.sum_congr rfl fun b _ => by rw [h]

theorem entry_pure (y : EuclideanSpace ℂ J) (a b : J) :
    entry (ODEMixedOutput.pureOperator y) a b = y a * (starRingEnd ℂ) (y b) := by
  rw [entry, ODEMixedOutput.pureOperator, InnerProductSpace.rankOne_apply, PiLp.smul_apply,
    smul_eq_mul, EuclideanSpace.inner_single_right, one_mul, mul_comm]

end Entries

variable {I G : Type*} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]

/-- **The partial trace** over the garbage register: `(Tr_G A)_{i i'} = ∑_g A_{(i,g),(i',g)}`. -/
def ptrace (A : EuclideanSpace ℂ (I × G) →L[ℂ] EuclideanSpace ℂ (I × G)) :
    EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I :=
  SparseStateOverlap.matrixOperator (Matrix.of fun i i' => ∑ g, entry A (i, g) (i', g))

/-- `B ⊗ I_G`: an operator on the output register acting trivially on the garbage. -/
def ampl (B : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    EuclideanSpace ℂ (I × G) →L[ℂ] EuclideanSpace ℂ (I × G) :=
  SparseStateOverlap.matrixOperator (Matrix.of fun a b => if a.2 = b.2 then entry B a.1 b.1 else 0)

theorem entry_ptrace (A : EuclideanSpace ℂ (I × G) →L[ℂ] EuclideanSpace ℂ (I × G)) (i i' : I) :
    entry (ptrace A) i i' = ∑ g, entry A (i, g) (i', g) := by
  rw [ptrace, entry_matrixOperator]
  rfl

/-- **Characterisation of the partial trace**: `tr(B Tr_G A) = tr((B ⊗ I_G) A)`. -/
theorem trace_comp_ptrace (B : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (A : EuclideanSpace ℂ (I × G) →L[ℂ] EuclideanSpace ℂ (I × G)) :
    LinearMap.trace ℂ (EuclideanSpace ℂ I)
        ((B ∘L ptrace A : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
          EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) =
      LinearMap.trace ℂ (EuclideanSpace ℂ (I × G))
        ((ampl (G := G) B ∘L A : EuclideanSpace ℂ (I × G) →L[ℂ] EuclideanSpace ℂ (I × G)) :
          EuclideanSpace ℂ (I × G) →ₗ[ℂ] EuclideanSpace ℂ (I × G)) := by
  rw [trace_eq_sum_entry, trace_eq_sum_entry]
  simp only [entry_comp, entry_ptrace, ampl, entry_matrixOperator, Matrix.of_apply,
    Fintype.sum_prod_type, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- **Uniqueness**: an operator `X` with `tr(B X) = tr((B ⊗ I_G) A)` for every `B` is the
partial trace of `A`. -/
theorem ptrace_unique (A : EuclideanSpace ℂ (I × G) →L[ℂ] EuclideanSpace ℂ (I × G))
    (X : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (h : ∀ B : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I,
      LinearMap.trace ℂ (EuclideanSpace ℂ I)
          ((B ∘L X : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
            EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) =
        LinearMap.trace ℂ (EuclideanSpace ℂ (I × G))
          ((ampl (G := G) B ∘L A : EuclideanSpace ℂ (I × G) →L[ℂ] EuclideanSpace ℂ (I × G)) :
            EuclideanSpace ℂ (I × G) →ₗ[ℂ] EuclideanSpace ℂ (I × G))) :
    X = ptrace A := by
  apply ext_entry
  intro a b
  set U : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I :=
    SparseStateOverlap.matrixOperator (Matrix.of fun c d => if d = a then
      (if c = b then (1 : ℂ) else 0) else 0)
  have key : ∀ Y : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I,
      LinearMap.trace ℂ (EuclideanSpace ℂ I)
          ((U ∘L Y : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
            EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ I) = entry Y a b := by
    intro Y
    rw [trace_eq_sum_entry]
    simp only [U, entry_comp, entry_matrixOperator, Matrix.of_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← key X, ← key (ptrace A), h U, trace_comp_ptrace]

/-- The decoder correlation of the reduced state. -/
theorem corr_ptrace (B : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (A : EuclideanSpace ℂ (I × G) →L[ℂ] EuclideanSpace ℂ (I × G)) :
    corr B (ptrace A) = corr (ampl (G := G) B) A := by
  rw [corr, corr, trace_comp_ptrace]

/-- `B ⊗ I_G` acts slice by slice. -/
theorem ampl_apply (B : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (v : EuclideanSpace ℂ (I × G)) (i : I) (g : G) :
    ampl (G := G) B v (i, g) = B (WithLp.toLp 2 fun i' => v (i', g)) i := by
  rw [ampl, SparseStateOverlap.matrixOperator_apply, apply_eq_sum_entry, Fintype.sum_prod_type]
  simp only [Matrix.of_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- `B ⊗ I_G` is a contraction when `B` is. -/
theorem norm_ampl_le (B : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I)
    (hB : ∀ u, ‖B u‖ ≤ ‖u‖) (v : EuclideanSpace ℂ (I × G)) : ‖ampl (G := G) B v‖ ≤ ‖v‖ := by
  have hslice : ∀ w : EuclideanSpace ℂ (I × G), ‖w‖ ^ 2 =
      ∑ g, ‖(WithLp.toLp 2 fun i => w (i, g) : EuclideanSpace ℂ I)‖ ^ 2 := by
    intro w
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g _
    rw [EuclideanSpace.norm_sq_eq]
  have h : ‖ampl (G := G) B v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
    rw [hslice, hslice v]
    apply Finset.sum_le_sum
    intro g _
    have hs : (WithLp.toLp 2 fun i => ampl (G := G) B v (i, g) : EuclideanSpace ℂ I) =
        B (WithLp.toLp 2 fun i' => v (i', g)) := by
      ext i
      exact ampl_apply B v i g
    rw [hs]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB _) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- The product vector `v ⊗ u`. -/
def tmulVec (v : EuclideanSpace ℂ I) (u : EuclideanSpace ℂ G) : EuclideanSpace ℂ (I × G) :=
  WithLp.toLp 2 fun a => v a.1 * u a.2

/-- **Sanity check**: discarding a garbage register in a product state with a unit vector `u`
leaves the clean output, `Tr_G |v ⊗ u⟩⟨v ⊗ u| = |v⟩⟨v|`. -/
theorem ptrace_pure_tmul (v : EuclideanSpace ℂ I) (u : EuclideanSpace ℂ G) (hu : ‖u‖ = 1) :
    ptrace (ODEMixedOutput.pureOperator (tmulVec v u)) = ODEMixedOutput.pureOperator v := by
  have hu2 : ∑ g, u g * (starRingEnd ℂ) (u g) = 1 := by
    have h := EuclideanSpace.norm_sq_eq u
    rw [hu, one_pow] at h
    have : ∑ g, u g * (starRingEnd ℂ) (u g) = ((∑ g, ‖u g‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      apply Finset.sum_congr rfl
      intro g _
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [this, ← h]
    simp
  ext w i
  rw [apply_eq_sum_entry, apply_eq_sum_entry]
  apply Finset.sum_congr rfl
  intro i' _
  congr 1
  rw [entry_ptrace, entry_pure]
  simp only [entry_pure, tmulVec, map_mul]
  calc ∑ g, v i * u g * ((starRingEnd ℂ) (v i') * (starRingEnd ℂ) (u g))
      = v i * (starRingEnd ℂ) (v i') * ∑ g, u g * (starRingEnd ℂ) (u g) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _
        ring
    _ = v i * (starRingEnd ℂ) (v i') := by rw [hu2, mul_one]

/-! ### Identifying the output space with output and garbage registers -/

/-- Correlations are invariant under an isometric identification of output spaces. -/
theorem corr_conjStarAlgEquiv {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [FiniteDimensional ℂ E] [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
    [CompleteSpace E'] [FiniteDimensional ℂ E'] (V : E ≃ₗᵢ[ℂ] E') (B : E' →L[ℂ] E')
    (A : E →L[ℂ] E) :
    corr B (V.conjStarAlgEquiv A) = corr (V.conjStarAlgEquiv.symm B) A := by
  unfold corr
  congr 1
  have h : ((B ∘L V.conjStarAlgEquiv A : E' →L[ℂ] E') : E' →ₗ[ℂ] E') =
      V.toLinearEquiv.conj ((V.conjStarAlgEquiv.symm B ∘L A : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
    ext y
    simp [LinearEquiv.conj_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  rw [h, LinearMap.trace_conj']

/-- The decoder `B ⊗ I_G`, transported to the output space, is a contraction. -/
theorem norm_conj_ampl_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (V : E ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × G))
    (B : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) (hB : ∀ u, ‖B u‖ ≤ ‖u‖) (v : E) :
    ‖V.conjStarAlgEquiv.symm (ampl (G := G) B) v‖ ≤ ‖v‖ := by
  rw [LinearIsometryEquiv.symm_conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.norm_map]
  calc ‖ampl (G := G) B (V v)‖ ≤ ‖V v‖ := norm_ampl_le B hB _
    _ = ‖v‖ := V.norm_map v

/-- A clean output space: the output register with a one-point garbage register. -/
def unitGarbage : EuclideanSpace ℂ I ≃ₗᵢ[ℂ] EuclideanSpace ℂ (I × Unit) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.prodPUnit I).symm

omit [DecidableEq I] in
theorem unitGarbage_apply (v : EuclideanSpace ℂ I) (a : I × Unit) :
    unitGarbage v a = v a.1 := by
  simp [unitGarbage, Equiv.piCongrLeft'_apply]

omit [DecidableEq I] in
theorem unitGarbage_symm_apply (w : EuclideanSpace ℂ (I × Unit)) (i : I) :
    unitGarbage.symm w i = w (i, ()) := by
  simp [unitGarbage, Equiv.piCongrLeft'_apply]

/-- With a one-point garbage register the reduced output state is the output itself. -/
theorem ptrace_unitGarbage (A : EuclideanSpace ℂ I →L[ℂ] EuclideanSpace ℂ I) :
    ptrace (unitGarbage.conjStarAlgEquiv A) = A := by
  apply ext_entry
  intro i i'
  rw [entry_ptrace, Fintype.sum_unique]
  have hs : unitGarbage.symm (EuclideanSpace.single (i', default) (1 : ℂ)) =
      EuclideanSpace.single i' (1 : ℂ) := by
    ext j
    rw [unitGarbage_symm_apply]
    simp [PiLp.single_apply]
  simp only [entry, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, unitGarbage_apply, hs]

end

end LinearSystemLowerBound
