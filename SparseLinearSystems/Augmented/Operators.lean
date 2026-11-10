import SparseLinearSystems.WalkGap
import SparseLinearSystems.Spectral.UnitaryFilter

/-!
# The augmented Hamiltonian as a sum of three branches

On the public space `Pub = (upper, (lower, e))`, with `Sys = reg ⊗ dil ⊗ V₀`,
the regularized augmented Hamiltonian of equation `qls:eq:augmented` is

`H_{σ,r} = a H₀ + σ T₁ + r⁻¹ T₂`,  `a = √(1 - σ²)`,

where `H₀` is the off-diagonal lift of `Z ⊗ B`, `T₁` the lift of `X ⊗ I`, and
`T₂ = -|upper, β⟩⟨e| - |e⟩⟨upper, β|` (`hamiltonian_decomp`).  This file
also records self-adjointness and norm bounds of the three branches and the
explicit public vectors used later: the seed coordinate `e`, the right-hand
side `β = |0⟩|0⟩|b⟩` and the solution coordinates `|lower⟩|0⟩|1⟩`.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace SparseLinearSystems.Augmented

noncomputable section
open ContinuousLinearMap HilbertBlocks HilbertRegularization HilbertAugmentation
open scoped InnerProduct ComplexConjugate

variable {V₀ : Type*} [NormedAddCommGroup V₀] [InnerProductSpace ℂ V₀] [CompleteSpace V₀]

/-- `reg ⊗ dil ⊗ V₀`. -/
abbrev Sys (V₀ : Type*) := Double (Double V₀)

/-- The public space `(upper, (lower, e))`. -/
abbrev Pub (V₀ : Type*) := FullSpace (Sys V₀)

/-- A public vector from its three sectors. -/
abbrev mk (u l : Sys V₀) (e : ℂ) : Pub V₀ := WithLp.toLp 2 (u, WithLp.toLp 2 (l, e))

omit [NormedAddCommGroup V₀] [InnerProductSpace ℂ V₀] [CompleteSpace V₀] in
theorem eta (x : Pub V₀) : mk x.fst x.snd.fst x.snd.snd = x := rfl

omit [NormedAddCommGroup V₀] [InnerProductSpace ℂ V₀] [CompleteSpace V₀] in
@[simp] theorem mk_fst (u l : Sys V₀) (e : ℂ) : (mk u l e).fst = u := rfl
omit [NormedAddCommGroup V₀] [InnerProductSpace ℂ V₀] [CompleteSpace V₀] in
@[simp] theorem mk_snd_fst (u l : Sys V₀) (e : ℂ) : (mk u l e).snd.fst = l := rfl
omit [NormedAddCommGroup V₀] [InnerProductSpace ℂ V₀] [CompleteSpace V₀] in
@[simp] theorem mk_snd_snd (u l : Sys V₀) (e : ℂ) : (mk u l e).snd.snd = e := rfl

omit [CompleteSpace V₀] in
/-- Inner product on the right-hand sector `(lower, e)`. -/
theorem inner_right (w z : RightSpace (Sys V₀)) :
    inner ℂ w z = inner ℂ w.fst z.fst + conj w.snd * z.snd := by
  rw [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_fst, WithLp.ofLp_snd,
    WithLp.ofLp_snd, RCLike.inner_apply, mul_comm]

omit [CompleteSpace V₀] in
theorem inner_pub (x y : Pub V₀) :
    inner ℂ x y = inner ℂ x.fst y.fst + inner ℂ x.snd.fst y.snd.fst +
      conj x.snd.snd * y.snd.snd := by
  rw [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_fst, WithLp.ofLp_snd,
    WithLp.ofLp_snd, inner_right, add_assoc]

omit [InnerProductSpace ℂ V₀] [CompleteSpace V₀] in
theorem norm_sq_pub (x : Pub V₀) :
    ‖x‖ ^ 2 = ‖x.fst‖ ^ 2 + ‖x.snd.fst‖ ^ 2 + ‖x.snd.snd‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2 x, WithLp.prod_norm_sq_eq_of_L2 x.snd, add_assoc]

/-! ### Off-diagonal lifts -/

/-- `y ↦ (y, 0)` into the right-hand sector. -/
abbrev inl : Sys V₀ →L[ℂ] RightSpace (Sys V₀) :=
  HilbertAugmentationGap.firstEmbedding.toContinuousLinearMap

/-- Off-diagonal lift `(x_u, (x_l, x_e)) ↦ (T x_l, (T x_u, 0))`. -/
def lift (T : Sys V₀ →L[ℂ] Sys V₀) : Pub V₀ →L[ℂ] Pub V₀ :=
  blockMap 0 (T ∘L WithLp.fstL 2 ℂ (Sys V₀) ℂ) (inl ∘L T) 0

omit [CompleteSpace V₀] in
theorem lift_apply (T : Sys V₀ →L[ℂ] Sys V₀) (x : Pub V₀) :
    lift T x = mk (T x.snd.fst) (T x.fst) 0 := by
  simp only [lift, blockMap_apply, zero_apply, zero_add, add_zero, comp_apply]
  rfl

theorem lift_selfAdjoint (T : Sys V₀ →L[ℂ] Sys V₀) (hT : (T†) = T) : ((lift T)†) = lift T := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_pub, inner_pub, lift_apply, lift_apply]
  simp only [mk_fst, mk_snd_fst, mk_snd_snd, mul_zero, map_zero, zero_mul, add_zero]
  have h1 : inner ℂ (T x.snd.fst) y.fst = inner ℂ x.snd.fst (T y.fst) := by
    rw [← adjoint_inner_right, hT]
  have h2 : inner ℂ (T x.fst) y.snd.fst = inner ℂ x.fst (T y.snd.fst) := by
    rw [← adjoint_inner_right, hT]
  rw [h1, h2, add_comm]

omit [CompleteSpace V₀] in
theorem lift_norm_sq (T : Sys V₀ →L[ℂ] Sys V₀) (x : Pub V₀) :
    ‖lift T x‖ ^ 2 = ‖T x.snd.fst‖ ^ 2 + ‖T x.fst‖ ^ 2 := by
  rw [lift_apply, norm_sq_pub]
  simp

omit [CompleteSpace V₀] in
theorem lift_norm_le (T : Sys V₀ →L[ℂ] Sys V₀) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ y, ‖T y‖ ≤ C * ‖y‖) (x : Pub V₀) : ‖lift T x‖ ≤ C * ‖x‖ := by
  apply le_of_pow_le_pow_left₀ two_ne_zero (by positivity)
  rw [lift_norm_sq, mul_pow, norm_sq_pub]
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (hT x.snd.fst) 2
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (hT x.fst) 2
  rw [mul_pow] at h1 h2
  nlinarith [sq_nonneg C, sq_nonneg ‖x.snd.snd‖]

/-! ### The three branches -/

/-- `Z ⊗ B`, with `B` the Hermitian dilation of `A`. -/
def zb (A : V₀ →L[ℂ] V₀) : Sys V₀ →L[ℂ] Sys V₀ := signedDiagonal (dilation A)

theorem zb_apply (A : V₀ →L[ℂ] V₀) (y : Sys V₀) :
    zb A y = WithLp.toLp 2 (dilation A y.fst, -dilation A y.snd) := by
  simp only [zb, signedDiagonal, blockMap_apply, zero_apply, add_zero, zero_add, neg_apply]

theorem zb_selfAdjoint (A : V₀ →L[ℂ] V₀) : ((zb A)†) = zb A := by
  rw [← star_eq_adjoint, zb]
  exact signedDiagonal_selfAdjoint _ (dilation_selfAdjoint A)

omit [CompleteSpace V₀] in
theorem exchange_apply' (y : Sys V₀) :
    (exchange : Sys V₀ →L[ℂ] Sys V₀) y = WithLp.toLp 2 (y.snd, y.fst) := by
  simp only [exchange, blockMap_apply, zero_apply, zero_add, add_zero, one_apply_eq_self]

theorem exchange_selfAdjoint' : ((exchange : Sys V₀ →L[ℂ] Sys V₀)†) = exchange := by
  rw [← star_eq_adjoint]; exact exchange_selfAdjoint

omit [CompleteSpace V₀] in
theorem norm_exchange (y : Sys V₀) : ‖(exchange : Sys V₀ →L[ℂ] Sys V₀) y‖ = ‖y‖ := by
  rw [exchange_apply']
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (y.snd, y.fst)), WithLp.prod_norm_sq_eq_of_L2 y]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  ring

/-- `H₀`: the lift of `Z ⊗ B`. -/
def H0 (A : V₀ →L[ℂ] V₀) : Pub V₀ →L[ℂ] Pub V₀ := lift (zb A)

/-- `T₁`: the lift of `X ⊗ I`. -/
def T1 : Pub V₀ →L[ℂ] Pub V₀ := lift exchange

/-- `z ↦ (0, z)` into the right-hand sector. -/
def sndEmb : ℂ →L[ℂ] RightSpace (Sys V₀) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (Sys V₀) ℂ).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℂ (Sys V₀) ℂ

omit [CompleteSpace V₀] in
theorem sndEmb_apply (z : ℂ) : (sndEmb (V₀ := V₀)) z = WithLp.toLp 2 (0, z) := rfl

/-- `T₂ = -|upper, β⟩⟨e| - |e⟩⟨upper, β|`. -/
def T2 (β : Sys V₀) : Pub V₀ →L[ℂ] Pub V₀ :=
  blockMap 0 (-(ray β ∘L WithLp.sndL 2 ℂ (Sys V₀) ℂ)) (-((sndEmb (V₀ := V₀)) ∘L innerSL ℂ β)) 0

omit [CompleteSpace V₀] in
theorem T2_apply (β : Sys V₀) (x : Pub V₀) :
    T2 β x = mk (-(x.snd.snd • β)) 0 (-(inner ℂ β x.fst)) := by
  apply prodExt
  · simp [T2, blockMap_apply]
  · apply prodExt
    · simp [T2, blockMap_apply, sndEmb_apply]
    · simp [T2, blockMap_apply, sndEmb_apply]

theorem T2_selfAdjoint (β : Sys V₀) : ((T2 β)†) = T2 β := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_pub, inner_pub, T2_apply, T2_apply]
  simp only [mk_fst, mk_snd_fst, mk_snd_snd, inner_zero_left, inner_zero_right, add_zero,
    inner_neg_left, inner_neg_right, inner_smul_left, inner_smul_right, map_neg,
    inner_conj_symm]
  ring

omit [CompleteSpace V₀] in
theorem T2_norm_le (β : Sys V₀) (hβ : ‖β‖ ≤ 1) (x : Pub V₀) : ‖T2 β x‖ ≤ ‖x‖ := by
  apply le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _)
  rw [T2_apply, norm_sq_pub, norm_sq_pub]
  simp only [mk_fst, mk_snd_fst, mk_snd_snd, norm_neg, norm_zero, norm_smul]
  have h1 : ‖inner ℂ β x.fst‖ ≤ ‖x.fst‖ :=
    (norm_inner_le_norm β x.fst).trans (by nlinarith [norm_nonneg x.fst, norm_nonneg β])
  have h2 : ‖x.snd.snd‖ * ‖β‖ ≤ ‖x.snd.snd‖ := by
    nlinarith [norm_nonneg x.snd.snd, norm_nonneg β]
  have h1' := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2' := pow_le_pow_left₀ (by positivity) h2 2
  nlinarith [sq_nonneg ‖x.snd.fst‖]

theorem T1_selfAdjoint : ((T1 : Pub V₀ →L[ℂ] Pub V₀)†) = T1 :=
  lift_selfAdjoint _ exchange_selfAdjoint'

omit [CompleteSpace V₀] in
theorem T1_norm_le (x : Pub V₀) : ‖(T1 : Pub V₀ →L[ℂ] Pub V₀) x‖ ≤ ‖x‖ := by
  have := lift_norm_le (exchange : Sys V₀ →L[ℂ] Sys V₀) 1 zero_le_one
    (fun y => by rw [norm_exchange, one_mul]) x
  simpa [T1] using this

theorem H0_selfAdjoint (A : V₀ →L[ℂ] V₀) : ((H0 A)†) = H0 A :=
  lift_selfAdjoint _ (zb_selfAdjoint A)

/-! ### The decomposition -/

omit [CompleteSpace V₀] in
theorem regularized_eq (B : Double V₀ →L[ℂ] Double V₀) (σ : ℝ) :
    regularized B σ = ((Real.sqrt (1 - σ ^ 2) : ℝ) : ℂ) • signedDiagonal B +
      (σ : ℂ) • (exchange : Double (Double V₀) →L[ℂ] Double (Double V₀)) := by
  ext y : 1
  apply prodExt
  · simp [regularized, weighted_apply, signedDiagonal, exchange, blockMap_apply]
  · simp [regularized, weighted_apply, signedDiagonal, exchange, blockMap_apply]
    module

theorem column_adjoint_apply (M : Sys V₀ ≃L[ℂ] Sys V₀)
    (hM : ((M : Sys V₀ →L[ℂ] Sys V₀)†) = M) (β : Sys V₀) (c : ℝ) (y : Sys V₀) :
    ((column M β (c : ℂ))†) y = WithLp.toLp 2 (M y, -((c : ℂ) * inner ℂ β y)) := by
  apply ext_inner_left ℂ
  intro w
  rw [adjoint_inner_right, column_apply, inner_right w]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [inner_sub_left, inner_smul_left, inner_smul_left, Complex.conj_ofReal]
  have hMy : inner ℂ ((M : Sys V₀ →L[ℂ] Sys V₀) w.fst) y =
      inner ℂ w.fst ((M : Sys V₀ →L[ℂ] Sys V₀) y) := by
    rw [← adjoint_inner_right, hM]
  rw [show inner ℂ (M w.fst) y = inner ℂ ((M : Sys V₀ →L[ℂ] Sys V₀) w.fst) y from rfl, hMy]
  change _ = inner ℂ w.fst ((M : Sys V₀ →L[ℂ] Sys V₀) y) + _
  ring

/-- **The three-branch decomposition** `H_{σ,r} = a H₀ + σ T₁ + r⁻¹ T₂`. -/
theorem hamiltonian_decomp (M : Sys V₀ ≃L[ℂ] Sys V₀) (A : V₀ →L[ℂ] V₀) (σ : ℝ)
    (hMdef : (M : Sys V₀ →L[ℂ] Sys V₀) = regularized (dilation A) σ)
    (β : Sys V₀) (c : ℝ) :
    hamiltonian M β (c : ℂ) =
      ((Real.sqrt (1 - σ ^ 2) : ℝ) : ℂ) • H0 A + (σ : ℂ) • T1 + (c : ℂ) • T2 β := by
  have hMsa : ((M : Sys V₀ →L[ℂ] Sys V₀)†) = M := by
    rw [hMdef, ← star_eq_adjoint]
    exact regularized_selfAdjoint _ (dilation_selfAdjoint A) σ
  have hMx : ∀ y : Sys V₀, M y = ((Real.sqrt (1 - σ ^ 2) : ℝ) : ℂ) • zb A y +
      (σ : ℂ) • (exchange : Sys V₀ →L[ℂ] Sys V₀) y := by
    intro y
    have := DFunLike.congr_fun hMdef y
    rw [show M y = (M : Sys V₀ →L[ℂ] Sys V₀) y from rfl, this, regularized_eq]
    rfl
  ext1 x
  rw [hamiltonian_apply, column_adjoint_apply M hMsa β c x.fst]
  apply prodExt
  · simp only [WithLp.toLp_fst, column_apply, add_apply,
      smul_apply, H0, T1, lift_apply, T2_apply, WithLp.add_fst, WithLp.smul_fst, hMx]
    module
  · apply prodExt
    · simp only [WithLp.toLp_snd, WithLp.toLp_fst, add_apply, smul_apply, H0, T1, lift_apply,
        T2_apply, WithLp.add_snd, WithLp.smul_snd, WithLp.add_fst, WithLp.smul_fst, 
        hMx, smul_zero, add_zero]
    · simp only [WithLp.toLp_snd, add_apply, smul_apply, H0, T1, lift_apply, T2_apply,
        WithLp.add_snd, WithLp.smul_snd, smul_eq_mul]
      ring

/-! ### Public vectors -/

/-- The appended coordinate `e`. -/
def eVec : Pub V₀ := mk 0 0 1

/-- `β = |0⟩_reg |0⟩_dil |b⟩`. -/
def betaOf (b : V₀) : Sys V₀ := WithLp.toLp 2 (WithLp.toLp 2 (b, 0), 0)

omit [InnerProductSpace ℂ V₀] [CompleteSpace V₀] in
theorem norm_betaOf (b : V₀) : ‖betaOf b‖ = ‖b‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [betaOf]

/-- The solution coordinates `|lower⟩|0⟩_reg|1⟩_dil ⊗ V₀`. -/
def solEmb : V₀ →L[ℂ] Pub V₀ :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ (Sys V₀) (RightSpace (Sys V₀))).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℂ (Sys V₀) (RightSpace (Sys V₀)) ∘L
    inl ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℂ (Double V₀) (Double V₀)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inl ℂ (Double V₀) (Double V₀) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℂ V₀ V₀).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.inr ℂ V₀ V₀

omit [CompleteSpace V₀] in
theorem solEmb_apply (v : V₀) :
    solEmb v = mk 0 (WithLp.toLp 2 (WithLp.toLp 2 (0, v), 0)) 0 := rfl

theorem solEmb_isometry : ((solEmb : V₀ →L[ℂ] Pub V₀)†) ∘L solEmb = 1 := by
  apply (solEmb : V₀ →L[ℂ] Pub V₀).norm_map_iff_adjoint_comp_self.mp
  intro v
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [solEmb_apply, norm_sq_pub]
  simp

theorem solEmb_adjoint_apply (x : Pub V₀) :
    ((solEmb : V₀ →L[ℂ] Pub V₀)†) x = x.snd.fst.fst.snd := by
  apply ext_inner_left ℂ
  intro v
  rw [adjoint_inner_right, solEmb_apply, inner_pub]
  simp [WithLp.prod_inner_apply]

end

end SparseLinearSystems.Augmented
