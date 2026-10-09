import SparseLowerBounds.Hamiltonian.Chains

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Block-diagonal matrices: norm and Schrödinger evolution

Helpers for `SparseLowerBounds.Hamiltonian.Instance`:

* the Euclidean norm on `α ⊕ β` splits as a sum of squares;
* `‖fromBlocks A 0 0 B‖ = max ‖A‖ ‖B‖` for the `L²` operator norm;
* `e^{-iτ(A ⊕ B)}` acts blockwise (ODE uniqueness,
  `evolve_apply_eq_of_hasDerivAt`);
* a zero-energy vector is fixed by the evolution.
-/

namespace SparseLowerBounds.Hamiltonian.HsInstance

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

open SparseHamiltonian.SparseStateOverlap (matrixOperator matrixOperator_apply)

/-- `‖A w‖ ≤ ‖A‖ ‖w‖` for plain vectors. -/
theorem norm_toLp_mulVec_le {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℂ) (w : κ → ℂ) :
    ‖WithLp.toLp 2 (A *ᵥ w)‖ ≤ ‖A‖ * ‖WithLp.toLp 2 w‖ :=
  (Matrix.toEuclideanCLM (n := κ) (𝕜 := ℂ) A).le_opNorm (WithLp.toLp 2 w)

/-- A matrix whose action on plain vectors is bounded by `c` has norm at most `c`. -/
theorem norm_le_of_mulVec {κ : Type*} [Fintype κ] [DecidableEq κ]
    {A : Matrix κ κ ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ w : κ → ℂ, ‖WithLp.toLp 2 (A *ᵥ w)‖ ≤ c * ‖WithLp.toLp 2 w‖) : ‖A‖ ≤ c := by
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun v => ?_
  have := h (WithLp.ofLp v)
  rw [WithLp.toLp_ofLp] at this
  exact this

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The squared Euclidean norm on `α ⊕ β` is the sum of the block norms. -/
theorem norm_toLp_sum_sq (f : α ⊕ β → ℂ) :
    ‖(WithLp.toLp 2 f : EuclideanSpace ℂ (α ⊕ β))‖ ^ 2 =
      ‖(WithLp.toLp 2 (f ∘ Sum.inl) : EuclideanSpace ℂ α)‖ ^ 2 +
        ‖(WithLp.toLp 2 (f ∘ Sum.inr) : EuclideanSpace ℂ β)‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
  rfl

theorem norm_toLp_sumElim_zero (f : α → ℂ) :
    ‖(WithLp.toLp 2 (Sum.elim f 0) : EuclideanSpace ℂ (α ⊕ β))‖ =
      ‖(WithLp.toLp 2 f : EuclideanSpace ℂ α)‖ := by
  have h := norm_toLp_sum_sq (α := α) (β := β) (Sum.elim f 0)
  rw [Sum.elim_comp_inl, Sum.elim_comp_inr] at h
  have h0 : ‖(WithLp.toLp 2 (0 : β → ℂ) : EuclideanSpace ℂ β)‖ = 0 := by
    rw [norm_eq_zero]; rfl
  rw [h0] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by simpa using h)

theorem norm_toLp_zero_sumElim (g : β → ℂ) :
    ‖(WithLp.toLp 2 (Sum.elim 0 g) : EuclideanSpace ℂ (α ⊕ β))‖ =
      ‖(WithLp.toLp 2 g : EuclideanSpace ℂ β)‖ := by
  have h := norm_toLp_sum_sq (α := α) (β := β) (Sum.elim 0 g)
  rw [Sum.elim_comp_inl, Sum.elim_comp_inr] at h
  have h0 : ‖(WithLp.toLp 2 (0 : α → ℂ) : EuclideanSpace ℂ α)‖ = 0 := by
    rw [norm_eq_zero]; rfl
  rw [h0] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (by simpa using h)

variable [DecidableEq α] [DecidableEq β]

/-- The `L²` norm of a block-diagonal matrix is the larger block norm. -/
theorem norm_fromBlocks_zero (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    ‖Matrix.fromBlocks A 0 0 B‖ = max ‖A‖ ‖B‖ := by
  apply le_antisymm
  · apply norm_le_of_mulVec (le_max_of_le_left (norm_nonneg _))
    intro w
    set c := max ‖A‖ ‖B‖
    have hc : 0 ≤ c := le_max_of_le_left (norm_nonneg _)
    rw [Matrix.fromBlocks_mulVec]
    simp only [Matrix.zero_mulVec, add_zero, zero_add]
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow,
      norm_toLp_sum_sq, norm_toLp_sum_sq (w), Sum.elim_comp_inl, Sum.elim_comp_inr]
    have h1 := norm_toLp_mulVec_le A (w ∘ Sum.inl)
    have h2 := norm_toLp_mulVec_le B (w ∘ Sum.inr)
    have h1' : ‖(WithLp.toLp 2 (A *ᵥ (w ∘ Sum.inl)) : EuclideanSpace ℂ α)‖ ≤
        c * ‖(WithLp.toLp 2 (w ∘ Sum.inl) : EuclideanSpace ℂ α)‖ :=
      h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have h2' : ‖(WithLp.toLp 2 (B *ᵥ (w ∘ Sum.inr)) : EuclideanSpace ℂ β)‖ ≤
        c * ‖(WithLp.toLp 2 (w ∘ Sum.inr) : EuclideanSpace ℂ β)‖ :=
      h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    have e1 := pow_le_pow_left₀ (norm_nonneg _) h1' 2
    have e2 := pow_le_pow_left₀ (norm_nonneg _) h2' 2
    rw [mul_pow] at e1 e2
    linarith
  · apply max_le
    · apply norm_le_of_mulVec (norm_nonneg _)
      intro w
      have h := norm_toLp_mulVec_le (Matrix.fromBlocks A 0 0 B)
        (Sum.elim w (0 : β → ℂ))
      rw [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr] at h
      simp only [Matrix.zero_mulVec, Matrix.mulVec_zero, add_zero] at h
      rw [norm_toLp_sumElim_zero, norm_toLp_sumElim_zero] at h
      exact h
    · apply norm_le_of_mulVec (norm_nonneg _)
      intro w
      have h := norm_toLp_mulVec_le (Matrix.fromBlocks A 0 0 B)
        (Sum.elim (0 : α → ℂ) w)
      rw [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr] at h
      simp only [Matrix.zero_mulVec, Matrix.mulVec_zero, zero_add] at h
      rw [norm_toLp_zero_sumElim, norm_toLp_zero_sumElim] at h
      exact h

/-- The evolution commutes with its generator. -/
theorem evolve_matrixOperator_apply {S : Type*} [Fintype S] [DecidableEq S] (H : Matrix S S ℂ)
    (t : ℝ) (w : EuclideanSpace ℂ S) :
    evolve H t (matrixOperator H w) = matrixOperator H (evolve H t w) := by
  have hc : Commute (matrixOperator H)
      (NormedSpace.exp ((-Complex.I * (t : ℂ)) • matrixOperator H)) :=
    Commute.exp_right (by
      show matrixOperator H * _ = _ * matrixOperator H
      ext1 v
      simp [mul_apply_eq_comp, map_smul])
  have := congrArg (fun T => T w) hc.eq
  simp only [mul_apply_eq_comp] at this
  exact this.symm

/-- The derivative of `t ↦ e^{-itH} w` in the Schrödinger form `-iH (e^{-itH} w)`. -/
theorem hasDerivAt_evolve_apply {S : Type*} [Fintype S] [DecidableEq S] (H : Matrix S S ℂ)
    (w : EuclideanSpace ℂ S) (t : ℝ) :
    HasDerivAt (fun u : ℝ => evolve H u w)
      ((-Complex.I) • matrixOperator H (evolve H t w)) t := by
  have h := ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ S) w).restrictScalars ℝ).hasFDerivAt
    |>.comp_hasDerivAt t (hasDerivAt_evolve H t)
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.apply_apply, mul_apply_eq_comp, FunLike.coe_smul,
    Pi.smul_apply, map_smul] at h
  rw [← evolve_matrixOperator_apply]
  exact h

/-- The coordinate embedding `ℂ^α → ℂ^{α ⊕ β}`. -/
def inlOp (α β : Type*) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] :
    EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ (α ⊕ β) :=
  matrixOperator (Matrix.of fun (i : α ⊕ β) (a : α) => if i = Sum.inl a then (1 : ℂ) else 0)

/-- The coordinate embedding `ℂ^β → ℂ^{α ⊕ β}`. -/
def inrOp (α β : Type*) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] :
    EuclideanSpace ℂ β →L[ℂ] EuclideanSpace ℂ (α ⊕ β) :=
  matrixOperator (Matrix.of fun (i : α ⊕ β) (b : β) => if i = Sum.inr b then (1 : ℂ) else 0)

@[simp] theorem inlOp_apply_inl (x : EuclideanSpace ℂ α) (a : α) :
    inlOp α β x (Sum.inl a) = x a := by
  simp [inlOp, matrixOperator_apply]

@[simp] theorem inlOp_apply_inr (x : EuclideanSpace ℂ α) (b : β) :
    inlOp α β x (Sum.inr b) = 0 := by
  simp [inlOp, matrixOperator_apply]

@[simp] theorem inrOp_apply_inl (x : EuclideanSpace ℂ β) (a : α) :
    inrOp α β x (Sum.inl a) = 0 := by
  simp [inrOp, matrixOperator_apply]

@[simp] theorem inrOp_apply_inr (x : EuclideanSpace ℂ β) (b : β) :
    inrOp α β x (Sum.inr b) = x b := by
  simp [inrOp, matrixOperator_apply]

/-- **Block-diagonal exponential**: `e^{-iτ(A ⊕ B)}` acts blockwise. -/
theorem evolve_fromBlocks_zero (A : Matrix α α ℂ) (B : Matrix β β ℂ) (τ : ℝ)
    (v : EuclideanSpace ℂ (α ⊕ β)) :
    evolve (Matrix.fromBlocks A 0 0 B) τ v =
      WithLp.toLp 2 fun i => Sum.elim
        (fun a => evolve A τ (WithLp.toLp 2 fun a' => v (Sum.inl a')) a)
        (fun b => evolve B τ (WithLp.toLp 2 fun b' => v (Sum.inr b')) b) i := by
  set v₁ : EuclideanSpace ℂ α := WithLp.toLp 2 fun a' => v (Sum.inl a') with hv₁
  set v₂ : EuclideanSpace ℂ β := WithLp.toLp 2 fun b' => v (Sum.inr b') with hv₂
  let f : ℝ → EuclideanSpace ℂ (α ⊕ β) := fun t =>
    inlOp α β (evolve A t v₁) + inrOp α β (evolve B t v₂)
  have hf0 : f 0 = v := by
    ext i
    cases i <;> simp [f, evolve_zero, v₁, v₂]
  have hfτ : f τ = WithLp.toLp 2 fun i => Sum.elim (fun a => evolve A τ v₁ a)
      (fun b => evolve B τ v₂ b) i := by
    ext i
    cases i <;> simp [f]
  have hderiv : ∀ t, HasDerivAt f
      ((-Complex.I) • matrixOperator (Matrix.fromBlocks A 0 0 B) (f t)) t := by
    intro t
    have h1 := ((inlOp α β).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_evolve_apply A v₁ t)
    have h2 := ((inrOp α β).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_evolve_apply B v₂ t)
    simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars'] at h1 h2
    refine (h1.add h2).congr_deriv ?_
    ext i
    cases i with
    | inl a =>
      simp [f, matrixOperator_apply, Fintype.sum_sum_type]
    | inr b =>
      simp [f, matrixOperator_apply, Fintype.sum_sum_type]
  have key := evolve_apply_eq_of_hasDerivAt (Matrix.fromBlocks A 0 0 B) hderiv τ
  rw [hf0, hfτ] at key
  exact key

/-- A zero-energy vector is fixed by the evolution. -/
theorem evolve_apply_of_matrixOperator_eq_zero {S : Type*} [Fintype S] [DecidableEq S]
    (H : Matrix S S ℂ) (w : EuclideanSpace ℂ S) (hw : matrixOperator H w = 0) (τ : ℝ) :
    evolve H τ w = w := by
  have hderiv : ∀ t, HasDerivAt (fun _ : ℝ => w) ((-Complex.I) • matrixOperator H w) t := by
    intro t
    rw [hw, smul_zero]
    exact hasDerivAt_const t w
  exact evolve_apply_eq_of_hasDerivAt H hderiv τ

end

end SparseLowerBounds.Hamiltonian.HsInstance
end
