import OptimalLowerBounds.Access

set_option synthInstance.maxHeartbeats 400000

/-!
# The uniform ancilla: embedding, evolution and discarding

The proof of Proposition `hsl:prop:two-norm` (Section `twonorml:sec:lower`) enlarges a hard family
by a factor `m`: `H_X = μ H_X⁽⁰⁾ ⊗ 𝟙_m 𝟙_mᵀ = μ m H_X⁽⁰⁾ ⊗ |u_m⟩⟨u_m|` with `u_m = m^{-1/2} Σ_a |a⟩`
(eq. `twonorml:eq:enlargement`). For the known isometry `V ψ := ψ ⊗ u_m`,
`H_X V = V (μ m H_X⁽⁰⁾)` and `e^{-itH_X} V = V e^{-iθ H_X⁽⁰⁾}` (eq.
`twonorml:eq:embedded-evolution`), and after the added register is discarded, "Trace distance
contracts under this operation, so an `ε`-accurate enlarged output yields an `ε`-accurate old
output, even when the simulation output is mixed". This module proves these three facts for any
finite index type, with a real coefficient `c` in place of `μ` (so that `c < 0` treats negative
times).

* `regroup A B K`: the fixed relabelling `ℂ^{A × B} ⊗ K ≃ ℂ^A ⊗ (ℂ^B ⊗ K)`;
* `embedU m ψ = ψ ⊗ u_m` (`embedU_apply`), an isometry for `m ≥ 1` (`inner_embedU`,
  `embedU_isometry`);
* `enlargeMatrix H m c = c H ⊗ 𝟙𝟙ᵀ` and the intertwining
  `matrixOperator (enlargeMatrix H m c) ∘ V = V ∘ (c m) matrixOperator H`
  (`matrixOperator_enlarge_comp`);
* `exp_comp_eq_comp_exp`: an intertwining `A V = V B` passes to `e^A V = V e^B` (exponential
  series); hence `evolve_enlarge`: `e^{-itH_X} V ψ = V e^{-i(cmt) H⁽⁰⁾} ψ`;
* **`accurate_of_embedU`**: if the output read through `e` (system `ℂ^{N × Fin m}`) is
  `ε`-accurate for `V φ`, then the same output read through `regroup ∘ e` (system `ℂ^N`, the
  ancilla moved to the garbage) is `ε`-accurate for `φ`. The observable `M` on `ℂ^N` is tested as
  `M ⊗ 1_m` (`liftU M`, self-adjoint with norm at most `‖M‖`; `outObs_regroup`), whose
  expectation in `V φ` is that of `M` in `φ` (`inner_embedU_liftU`).
-/

namespace OptimalLowerBounds

noncomputable section
set_option autoImplicit false
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Hamiltonian Readout
open ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

/-! ### Registers -/

section Registers

variable (A B : Type) [Fintype A] [Fintype B] (K : Type*) [NormedAddCommGroup K]
  [InnerProductSpace ℂ K]

/-- The fixed relabelling `ℂ^{A × B} ⊗ K ≃ ℂ^A ⊗ (ℂ^B ⊗ K)`. -/
def regroup : Joint (A × B) K ≃ₗᵢ[ℂ] Joint A (Joint B K) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ K (Equiv.sigmaEquivProd A B).symm).trans
    (LinearIsometryEquiv.piLpCurry ℂ 2 (fun (_ : A) (_ : B) => K))

@[simp] theorem regroup_apply (Ψ : Joint (A × B) K) (a : A) (b : B) :
    regroup A B K Ψ a b = Ψ (a, b) := rfl

@[simp] theorem regroup_symm_apply (Φ : Joint A (Joint B K)) (a : A) (b : B) :
    (regroup A B K).symm Φ (a, b) = Φ a b := rfl

end Registers

/-! ### The exponential of an intertwined operator -/

/-- **Intertwining passes to the exponential**: if `A ∘ V = V ∘ B` then `e^A ∘ V = V ∘ e^B`
(termwise on the exponential series, `A^n ∘ V = V ∘ B^n`). -/
theorem exp_comp_eq_comp_exp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] E) (B : F →L[ℂ] F) (V : F →L[ℂ] E) (h : A ∘L V = V ∘L B) :
    NormedSpace.exp A ∘L V = V ∘L NormedSpace.exp B := by
  have hpow : ∀ n : ℕ, (A ^ n) ∘L V = V ∘L (B ^ n) := by
    intro n
    induction n with
    | zero => ext x; simp
    | succ n ih =>
      rw [pow_succ, pow_succ, mul_def, mul_def, comp_assoc, h, ← comp_assoc, ih, comp_assoc]
  have h1 : HasSum (fun n : ℕ => ((n.factorial⁻¹ : ℂ) • A ^ n) ∘L V)
      (NormedSpace.exp A ∘L V) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) A).mapL
      ((ContinuousLinearMap.compL ℂ F E E).flip V)
  have h2 : HasSum (fun n : ℕ => V ∘L ((n.factorial⁻¹ : ℂ) • B ^ n))
      (V ∘L NormedSpace.exp B) :=
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) B).mapL
      (ContinuousLinearMap.compL ℂ F F E V)
  have hf : (fun n : ℕ => ((n.factorial⁻¹ : ℂ) • A ^ n) ∘L V) =
      fun n => V ∘L ((n.factorial⁻¹ : ℂ) • B ^ n) := by
    funext n
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hpow]
  rw [hf] at h1
  exact h1.unique h2

/-! ### The uniform embedding -/

section Embed

variable {N : Type} [Fintype N]

/-- **The embedding `V ψ = ψ ⊗ u_m`**, `u_m = m^{-1/2} Σ_a |a⟩`: `(V ψ)(i, a) = ψ i / √m`. -/
def embedU (m : ℕ) : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ (N × Fin m) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ψ => WithLp.toLp 2 fun ia => ψ ia.1 * ((Real.sqrt m : ℝ) : ℂ)⁻¹
      map_add' := fun ψ φ => by ext ia; simp [add_mul]
      map_smul' := fun c ψ => by ext ia; simp [mul_assoc] }

@[simp] theorem embedU_apply (m : ℕ) (ψ : EuclideanSpace ℂ N) (ia : N × Fin m) :
    embedU m ψ ia = ψ ia.1 * ((Real.sqrt m : ℝ) : ℂ)⁻¹ := rfl

/-- `(√m)⁻² · m = 1` for `m ≥ 1`, in `ℂ`. -/
theorem sqrt_inv_sq_mul (m : ℕ) (hm : 0 < m) :
    ((Real.sqrt m : ℝ) : ℂ)⁻¹ * ((Real.sqrt m : ℝ) : ℂ)⁻¹ * (m : ℂ) = 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm'.le
  have : ((Real.sqrt m : ℝ) : ℂ)⁻¹ * ((Real.sqrt m : ℝ) : ℂ)⁻¹ * (m : ℂ) =
      (((Real.sqrt m * Real.sqrt m)⁻¹ * m : ℝ) : ℂ) := by push_cast; ring
  rw [this, hs, inv_mul_cancel₀ hm'.ne']
  simp

/-- The embedding preserves inner products for `m ≥ 1`. -/
theorem inner_embedU (m : ℕ) (hm : 0 < m) (ψ φ : EuclideanSpace ℂ N) :
    ⟪embedU m ψ, embedU m φ⟫_ℂ = ⟪ψ, φ⟫_ℂ := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [embedU_apply, RCLike.inner_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, map_mul, map_inv₀, Complex.conj_ofReal]
  linear_combination (φ i * (starRingEnd ℂ) (ψ i)) * sqrt_inv_sq_mul m hm

/-- The embedding is an isometry for `m ≥ 1`. -/
theorem embedU_isometry (m : ℕ) (hm : 0 < m) :
    (embedU (N := N) m)† ∘L embedU m = 1 :=
  ContinuousLinearMap.ext fun ψ => ext_inner_left ℂ fun φ => by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      inner_embedU m hm, one_apply_eq_self]

/-- The embedding preserves norms for `m ≥ 1`. -/
theorem norm_embedU (m : ℕ) (hm : 0 < m) (ψ : EuclideanSpace ℂ N) :
    ‖embedU m ψ‖ = ‖ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_embedU m hm]

/-! ### The enlarged matrix -/

omit [Fintype N] in
/-- **The enlarged matrix** `c H ⊗ 𝟙𝟙ᵀ`: entry `((i, a), (j, b)) ↦ c H i j`
(eq. `twonorml:eq:enlargement` with `c = μ`). -/
def enlargeMatrix (H : Matrix N N ℂ) (m : ℕ) (c : ℝ) : Matrix (N × Fin m) (N × Fin m) ℂ :=
  Matrix.of fun A B => (c : ℂ) * H A.1 B.1

omit [Fintype N] in
@[simp] theorem enlargeMatrix_apply (H : Matrix N N ℂ) (m : ℕ) (c : ℝ) (A B : N × Fin m) :
    enlargeMatrix H m c A B = (c : ℂ) * H A.1 B.1 := rfl

/-- **`H_X V = V (c m H_X⁽⁰⁾)`** (eq. `twonorml:eq:embedded-evolution`, first identity). -/
theorem matrixOperator_enlarge_comp (H : Matrix N N ℂ) (m : ℕ) (c : ℝ) :
    SparseStateOverlap.matrixOperator (enlargeMatrix H m c) ∘L embedU m =
      embedU m ∘L (((c * m : ℝ) : ℂ) • SparseStateOverlap.matrixOperator H) := by
  ext ψ ia
  simp only [ContinuousLinearMap.comp_apply, SparseStateOverlap.matrixOperator_apply,
    enlargeMatrix_apply, embedU_apply, smul_apply,
    PiLp.smul_apply, smul_eq_mul, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  push_cast
  ring

/-- **`e^{-itH_X} V = V e^{-i(cmt) H_X⁽⁰⁾}`** (eq. `twonorml:eq:embedded-evolution`, second
identity, with `θ = c m t`). -/
theorem evolve_enlarge [DecidableEq N] (H : Matrix N N ℂ) (m : ℕ) (c t : ℝ)
    (ψ : EuclideanSpace ℂ N) :
    evolve (enlargeMatrix H m c) t (embedU m ψ) = embedU m (evolve H (c * m * t) ψ) := by
  have h := exp_comp_eq_comp_exp
    ((-Complex.I * (t : ℂ)) • SparseStateOverlap.matrixOperator (enlargeMatrix H m c))
    ((-Complex.I * ((c * m * t : ℝ) : ℂ)) • SparseStateOverlap.matrixOperator H) (embedU m) (by
      rw [ContinuousLinearMap.smul_comp, matrixOperator_enlarge_comp,
        ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_smul, smul_smul]
      congr 1
      push_cast
      ring)
  exact congrArg (fun L => L ψ) h

/-- **The enlarged matrix has operator norm at least `|c| m ‖H‖`**: `H' V = V (c m H)` and `V` is an
isometry (remark after `hsl:prop:two-norm`: "The enlarged operator norm is exactly `μ m`, which can
exceed `η = μ√m`"). -/
theorem norm_enlarge_ge [DecidableEq N] (H : Matrix N N ℂ) (m : ℕ) (hm : 0 < m) (c : ℝ) :
    |c| * m * ‖SparseStateOverlap.matrixOperator H‖ ≤
      ‖SparseStateOverlap.matrixOperator (enlargeMatrix H m c)‖ := by
  have key : ‖((c * m : ℝ) : ℂ) • SparseStateOverlap.matrixOperator H‖ ≤
      ‖SparseStateOverlap.matrixOperator (enlargeMatrix H m c)‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun ψ => ?_
    have h := congrArg (fun L => L ψ) (matrixOperator_enlarge_comp H m c)
    simp only [ContinuousLinearMap.comp_apply] at h
    rw [← norm_embedU m hm, ← h, ← norm_embedU m hm ψ]
    exact ContinuousLinearMap.le_opNorm _ _
  rwa [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_mul, Nat.abs_cast] at key

/-! ### Discarding the ancilla -/

variable [DecidableEq N]

/-- The observable `M ⊗ 1_m` on `ℂ^{N × Fin m}`. -/
def liftU (m : ℕ) (M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) :
    EuclideanSpace ℂ (N × Fin m) →L[ℂ] EuclideanSpace ℂ (N × Fin m) :=
  (regroup N (Fin m) ℂ).symm.conjStarAlgEquiv (liftObs (G := EuclideanSpace ℂ (Fin m)) M)

theorem liftU_apply (m : ℕ) (M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N)
    (v : EuclideanSpace ℂ (N × Fin m)) (i : N) (a : Fin m) :
    liftU m M v (i, a) = ∑ i', M (EuclideanSpace.single i' 1) i * v (i', a) := by
  rw [liftU, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, regroup_symm_apply,
    LinearIsometryEquiv.symm_symm, liftObs_apply]
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, regroup_apply, smul_eq_mul]

theorem isSelfAdjoint_liftU (m : ℕ) {M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N}
    (hM : IsSelfAdjoint M) : IsSelfAdjoint (liftU m M) :=
  (isSelfAdjoint_liftObs hM).map _

theorem norm_liftU_le (m : ℕ) (M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) :
    ‖liftU m M‖ ≤ ‖M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rw [liftU, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.norm_map]
  calc ‖liftObs (G := EuclideanSpace ℂ (Fin m)) M ((regroup N (Fin m) ℂ).symm.symm v)‖
      ≤ ‖liftObs (G := EuclideanSpace ℂ (Fin m)) M‖ * ‖(regroup N (Fin m) ℂ).symm.symm v‖ :=
        le_opNorm _ _
    _ ≤ ‖M‖ * ‖v‖ := by
        rw [LinearIsometryEquiv.norm_map]
        exact mul_le_mul_of_nonneg_right (norm_liftObs_le M) (norm_nonneg _)

variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- Measuring `M` after moving the ancilla to the garbage is measuring `M ⊗ 1_m` before:
`regroup⁻¹ (M ⊗ 1_{ℂ^m ⊗ G}) regroup = (M ⊗ 1_m) ⊗ 1_G`. -/
theorem liftObs_regroup (m : ℕ) (M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) :
    (regroup N (Fin m) G).symm.conjStarAlgEquiv (liftObs (G := Joint (Fin m) G) M) =
      liftObs (G := G) (liftU m M) := by
  ext Ψ ia
  obtain ⟨i, a⟩ := ia
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, regroup_symm_apply,
    LinearIsometryEquiv.symm_symm]
  rw [liftObs_apply, liftObs_apply, Fintype.sum_prod_type]
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply, WithLp.ofLp_smul, Pi.smul_apply, regroup_apply]
  refine Finset.sum_congr rfl fun i' _ => ?_
  have hsingle : ∀ a' : Fin m, liftU m M (EuclideanSpace.single (i', a') 1) (i, a) =
      M (EuclideanSpace.single i' 1) i * (if a' = a then 1 else 0) := by
    intro a'
    rw [liftU_apply]
    simp only [PiLp.single_apply, Prod.mk.injEq]
    rw [Finset.sum_eq_single i']
    · by_cases ha : a' = a
      · subst ha; simp
      · simp [Ne.symm ha, ha]
    · intro b _ hb; simp [hb]
    · simp
  simp only [hsingle, ite_smul, zero_smul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ a]
  simp

/-- `(M ⊗ 1_m) V = V M`. -/
theorem liftU_comp_embedU (m : ℕ) (M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) :
    liftU m M ∘L embedU m = embedU m ∘L M := by
  ext φ ia
  obtain ⟨i, a⟩ := ia
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, liftU_apply, embedU_apply]
  have hMφ : (M φ) i = ∑ i', M (EuclideanSpace.single i' 1) i * φ i' := by
    conv_lhs => rw [← (EuclideanSpace.basisFun N ℂ).sum_repr φ]
    simp [map_sum, map_smul, EuclideanSpace.basisFun_apply, mul_comm]
  rw [hMφ, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [embedU_apply]
  ring

/-- The expectation of `M ⊗ 1_m` in `V φ` is that of `M` in `φ`. -/
theorem inner_embedU_liftU (m : ℕ) (hm : 0 < m) (M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N)
    (φ : EuclideanSpace ℂ N) :
    ⟪embedU m φ, liftU m M (embedU m φ)⟫_ℂ = ⟪φ, M φ⟫_ℂ := by
  rw [← ContinuousLinearMap.comp_apply (liftU m M) (embedU m), liftU_comp_embedU,
    ContinuousLinearMap.comp_apply, inner_embedU m hm]

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Measuring `M` through `regroup ∘ e` is measuring `M ⊗ 1_m` through `e`. -/
theorem outObs_regroup (m : ℕ) (e : K →L[ℂ] SysGarb (N × Fin m) G)
    (M : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) :
    outObs (((regroup N (Fin m) G) :
      SysGarb (N × Fin m) G →L[ℂ] SysGarb N (Joint (Fin m) G)) ∘L e) M =
        outObs e (liftU m M) := by
  rw [outObs, outObs, ← liftObs_regroup m M, LinearIsometryEquiv.conjStarAlgEquiv_apply,
    LinearIsometryEquiv.symm_symm, ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm]
  simp only [ContinuousLinearMap.comp_assoc]

/-- **Discarding the ancilla preserves accuracy** (proof of `hsl:prop:two-norm`, on discarding the
added register: "Trace distance contracts under this operation"). If the output `Φ` read through
`e` into `ℂ^{N × Fin m} ⊗ G` is `ε`-accurate for `V φ = φ ⊗ u_m`, then `Φ` read through
`regroup ∘ e` into `ℂ^N ⊗ (ℂ^m ⊗ G)` is `ε`-accurate for `φ`. -/
theorem accurate_of_embedU (m : ℕ) (hm : 0 < m) (e : K →L[ℂ] SysGarb (N × Fin m) G) (Φ : K)
    (φ : EuclideanSpace ℂ N) (ε : ℝ) (hacc : Accurate e Φ (embedU m φ) ε) :
    Accurate (((regroup N (Fin m) G) :
      SysGarb (N × Fin m) G →L[ℂ] SysGarb N (Joint (Fin m) G)) ∘L e) Φ φ ε := by
  intro M hM hM1
  have h := hacc (liftU m M) (isSelfAdjoint_liftU m hM) ((norm_liftU_le m M).trans hM1)
  rw [outObs_regroup, ← inner_embedU_liftU m hm M φ]
  exact h

omit [DecidableEq N] in
/-- `regroup ∘ e` is an isometry when `e` is. -/
theorem regroup_comp_isometry (m : ℕ) (e : K →L[ℂ] SysGarb (N × Fin m) G) (he : e† ∘L e = 1) :
    (((regroup N (Fin m) G) :
      SysGarb (N × Fin m) G →L[ℂ] SysGarb N (Joint (Fin m) G)) ∘L e)† ∘L
      (((regroup N (Fin m) G) :
        SysGarb (N × Fin m) G →L[ℂ] SysGarb N (Joint (Fin m) G)) ∘L e) = 1 := by
  rw [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm,
    ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc _ _ e]
  have : (((regroup N (Fin m) G).symm : SysGarb N (Joint (Fin m) G) →L[ℂ] SysGarb (N × Fin m) G)
      ∘L ((regroup N (Fin m) G) : SysGarb (N × Fin m) G →L[ℂ] SysGarb N (Joint (Fin m) G))) =
        1 := by
    ext Ψ ia
    simp
  rw [this, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, he]

end Embed

end

end OptimalLowerBounds
