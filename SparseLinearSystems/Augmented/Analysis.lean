import SparseLinearSystems.Augmented.NormLadder
import SparseLinearSystems.Foundations.HilbertAugmentationGap
import SparseLinearSystems.Spectral.CayleyAlgebra

/-!
# Spectral facts used by the protocol

Everything here is stated either for an abstract walk satisfying the
hypotheses of Lemma `qls:lem:walk` (`WalkGap.Hyp`), or for the augmented
Hamiltonian on the public space.  The concrete walk is treated in
`SparseLinearSystems.Circuit.Facts`.

* `Hyp.seed_facts`: if the kernel of `H` is the line through `u₀` and
  `⟪u₀, e⟫ = 1`, then there is `0 ≤ a ≤ μ ‖u₀‖²` with
  `‖P J e‖² = 1/(‖u₀‖² + a)` and `J† P J e = (‖u₀‖² + a)⁻¹ u₀`;
* `branchHam_*`: the kernel, normalization, gap and solution coordinates of
  `H_{σ,r} = a H₀ + σ T₁ + r⁻¹ T₂` (equations `qls:eq:u`, `qls:eq:augmented`);
* `filter_bounds`: equation `qls:eq:filterprobability` for the averaging filter.

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace SparseLinearSystems.Augmented

noncomputable section
open ContinuousLinearMap HilbertBlocks HilbertRegularization HilbertAugmentation
  FourBranchCompression
open scoped InnerProduct ComplexConjugate

/-! ### Abstract walk -/

section Abstract

variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
variable {J : P →L[ℂ] V} {K : V →L[ℂ] V} {H : P →L[ℂ] P} {α μ k₀ : ℝ}

/-- **Seed probability and extracted amplitude**, with the explicit kernel
defect `a = ‖K J u₀‖²`. -/
theorem _root_.SparseLinearSystems.WalkGap.Hyp.seed_facts (h : WalkGap.Hyp J K H α μ k₀)
    (u₀ e : P) (hu₀ : H u₀ = 0) (hker : ∀ u, H u = 0 → ∃ c : ℂ, u = c • u₀) (hne : u₀ ≠ 0)
    (hie : inner ℂ u₀ e = 1) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ μ * ‖u₀‖ ^ 2 ∧
      ‖UnitaryFilter.fixedProj (WalkGap.walk J h.cayley) (J e)‖ ^ 2 = 1 / (‖u₀‖ ^ 2 + a) ∧
      (J†) (UnitaryFilter.fixedProj (WalkGap.walk J h.cayley) (J e)) =
        (((1 / (‖u₀‖ ^ 2 + a) : ℝ) : ℂ)) • u₀ := by
  have hp := h.seed_probability u₀ hu₀ hker hne e
  have hx := h.extracted_amplitude u₀ hu₀ hker hne e
  rw [hie] at hp hx
  refine ⟨‖K (J u₀)‖ ^ 2, sq_nonneg _, h.moment u₀, ?_, ?_⟩
  · rw [hp, norm_one, one_pow]
  · rw [hx]
    congr 1
    push_cast
    ring

/-- `‖P J e‖²` lies between `1/((1 + μ) ‖u₀‖²)` and `1/‖u₀‖²`. -/
theorem _root_.SparseLinearSystems.WalkGap.Hyp.seed_bounds (h : WalkGap.Hyp J K H α μ k₀)
    (u₀ e : P) (hu₀ : H u₀ = 0) (hker : ∀ u, H u = 0 → ∃ c : ℂ, u = c • u₀) (hne : u₀ ≠ 0)
    (hie : inner ℂ u₀ e = 1) :
    1 / ((1 + μ) * ‖u₀‖ ^ 2) ≤ ‖UnitaryFilter.fixedProj (WalkGap.walk J h.cayley) (J e)‖ ^ 2 ∧
      ‖UnitaryFilter.fixedProj (WalkGap.walk J h.cayley) (J e)‖ ^ 2 ≤ 1 / ‖u₀‖ ^ 2 := by
  obtain ⟨a, ha0, ha1, hp, -⟩ := h.seed_facts u₀ e hu₀ hker hne hie
  have hu : 0 < ‖u₀‖ ^ 2 := by have := norm_pos_iff.mpr hne; positivity
  rw [hp]
  constructor
  · apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  · apply one_div_le_one_div_of_le hu
    linarith

end Abstract

/-! ### Transport along a linear isometric equivalence -/

section Transport

variable {V V' P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [CompleteSpace V'] [FiniteDimensional ℂ V']
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] in
theorem conj_apply (e : V ≃ₗᵢ[ℂ] V') (T : V →L[ℂ] V) (v : V') :
    e.conjStarAlgEquiv T v = e (T (e.symm v)) := rfl

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] in
/-- If `J' = e ∘ J` pointwise, then `J'† ∘ e = J†`. -/
theorem adjoint_transport (e : V ≃ₗᵢ[ℂ] V') (J : P →L[ℂ] V) (J' : P →L[ℂ] V')
    (hJ' : ∀ u, J' u = e (J u)) (w : V) : (J'†) (e w) = (J†) w := by
  apply ext_inner_left ℂ
  intro y
  rw [adjoint_inner_right, adjoint_inner_right, hJ', LinearIsometryEquiv.inner_map_map]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] in
/-- **Transport of the walk-lemma hypotheses** along a linear isometric equivalence. -/
theorem _root_.SparseLinearSystems.WalkGap.Hyp.transport {J : P →L[ℂ] V} {K : V →L[ℂ] V}
    {H : P →L[ℂ] P} {α μ k₀ : ℝ} (h : WalkGap.Hyp J K H α μ k₀) (e : V ≃ₗᵢ[ℂ] V')
    (J' : P →L[ℂ] V') (hJ' : ∀ u, J' u = e (J u)) (hiso : (J'†) ∘L J' = 1) :
    WalkGap.Hyp J' (e.conjStarAlgEquiv K) H α μ k₀ where
  isometry := hiso
  selfAdjoint := by
    rw [← star_eq_adjoint, ← map_star, star_eq_adjoint, h.selfAdjoint]
  alpha_pos := h.alpha_pos
  compression := by
    ext u
    have hc := congrArg (fun T : P →L[ℂ] P => T u) h.compression
    simp only [comp_apply] at hc ⊢
    rw [hJ', conj_apply, LinearIsometryEquiv.symm_apply_apply, adjoint_transport e J J' hJ']
    exact hc
  moment := by
    intro u
    rw [hJ', conj_apply, LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.norm_map]
    exact h.moment u
  mu_nonneg := h.mu_nonneg
  bound := by
    intro v
    rw [conj_apply, LinearIsometryEquiv.norm_map]
    calc ‖K (e.symm v)‖ ≤ k₀ * ‖e.symm v‖ := h.bound _
      _ = k₀ * ‖v‖ := by rw [LinearIsometryEquiv.norm_map]
  k0_nonneg := h.k0_nonneg

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ V'] in
theorem conj_reflection (e : V ≃ₗᵢ[ℂ] V') (J : P →L[ℂ] V) (J' : P →L[ℂ] V')
    (hJ' : ∀ u, J' u = e (J u)) :
    e.conjStarAlgEquiv (WalkGap.reflection J) = WalkGap.reflection J' := by
  ext v
  simp only [WalkGap.reflection, conj_apply, sub_apply, one_apply_eq_self, smul_apply,
    comp_apply, map_sub, map_smul, LinearIsometryEquiv.apply_symm_apply]
  rw [← adjoint_transport e J J' hJ' (e.symm v), LinearIsometryEquiv.apply_symm_apply, hJ']

theorem conj_cayley (e : V ≃ₗᵢ[ℂ] V') (K : V →L[ℂ] V) (hK : (K†) = K)
    (hK' : ((e.conjStarAlgEquiv K)†) = e.conjStarAlgEquiv K) :
    e.conjStarAlgEquiv (HilbertCayley.cayley K hK) =
      HilbertCayley.cayley (e.conjStarAlgEquiv K) hK' := by
  set S := HilbertCayley.denominatorInverse K hK
  have hS : (K - Complex.I • (1 : V →L[ℂ] V)) * S = 1 := CayleyAlgebra.cayley_mul_denominator K hK
  have hS' : (e.conjStarAlgEquiv K - Complex.I • (1 : V' →L[ℂ] V')) *
      e.conjStarAlgEquiv S = 1 := by
    rw [← map_one e.conjStarAlgEquiv, ← map_smul, ← map_sub, ← map_mul, hS]
  rw [CayleyAlgebra.cayley_eq_of_right_inverse _ hK' _ hS',
    CayleyAlgebra.cayley_eq_of_right_inverse _ hK _ hS, map_mul, map_add, map_smul, map_one]

/-- **Transport of the walk.** -/
theorem conj_walk (e : V ≃ₗᵢ[ℂ] V') (J : P →L[ℂ] V) (J' : P →L[ℂ] V')
    (hJ' : ∀ u, J' u = e (J u)) (K : V →L[ℂ] V) (hK : (K†) = K)
    (hK' : ((e.conjStarAlgEquiv K)†) = e.conjStarAlgEquiv K) :
    e.conjStarAlgEquiv (WalkGap.walk J (HilbertCayley.cayley K hK)) =
      WalkGap.walk J' (HilbertCayley.cayley (e.conjStarAlgEquiv K) hK') := by
  rw [WalkGap.walk, WalkGap.walk, map_mul, conj_reflection e J J' hJ', conj_cayley]

end Transport

/-! ### The augmented Hamiltonian -/

section Hamiltonian

variable {V₀ : Type*} [NormedAddCommGroup V₀] [InnerProductSpace ℂ V₀] [FiniteDimensional ℂ V₀]
  [CompleteSpace V₀]
variable (A : V₀ ≃L[ℂ] V₀) (κ : ℝ) (hκ : 1 ≤ κ) (hInv : ‖A.symm.toContinuousLinearMap‖ ≤ κ)

/-- The branch form `H_{σ,r} = √(1-σ²) H₀ + σ T₁ + r⁻¹ T₂`. -/
abbrev branchHam (σ r : ℝ) (b : V₀) : Pub V₀ →L[ℂ] Pub V₀ :=
  ((Real.sqrt (1 - σ ^ 2) : ℝ) : ℂ) • H0 A.toContinuousLinearMap + (σ : ℂ) • T1 +
    ((1 / r : ℝ) : ℂ) • T2 (betaOf b)

/-- The kernel generator `u₀ = (0; M_σ⁻¹ β / r, 1)`. -/
abbrev kerVec (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (r : ℝ) (b : V₀) : Pub V₀ :=
  generator (Mσ A κ σ hκ hInv hσ₀ hσ₁) (betaOf b) ((1 / r : ℝ) : ℂ)

theorem branchHam_eq (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (r : ℝ) (b : V₀) :
    hamiltonian (Mσ A κ σ hκ hInv hσ₀ hσ₁) (betaOf b) ((1 / r : ℝ) : ℂ) = branchHam A σ r b :=
  hamiltonian_eq_branches A κ σ hκ hInv hσ₀ hσ₁ (betaOf b) (1 / r)

theorem branchHam_kerVec (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (r : ℝ) (b : V₀) :
    branchHam A σ r b (kerVec A κ hκ hInv σ hσ₀ hσ₁ r b) = 0 := by
  rw [← branchHam_eq A κ hκ hInv σ hσ₀ hσ₁ r b]
  exact hamiltonian_generator _ _ _

theorem branchHam_kernel (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (r : ℝ) (b : V₀) (u : Pub V₀)
    (hu : branchHam A σ r b u = 0) : ∃ c : ℂ, u = c • kerVec A κ hκ hInv σ hσ₀ hσ₁ r b := by
  rw [← branchHam_eq A κ hκ hInv σ hσ₀ hσ₁ r b] at hu
  exact hamiltonian_kernel _ _ _ u hu

theorem kerVec_ne_zero (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (r : ℝ) (b : V₀) :
    kerVec A κ hκ hInv σ hσ₀ hσ₁ r b ≠ 0 :=
  generator_ne_zero _ _ _

theorem kerVec_inner_eVec (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (r : ℝ) (b : V₀) :
    inner ℂ (kerVec A κ hκ hInv σ hσ₀ hσ₁ r b) (eVec : Pub V₀) = 1 :=
  inner_generator_eVec _ _ _

/-- `‖u₀‖² = 1 + q²`, `q = r_σ / r`. -/
theorem kerVec_norm_sq (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (r : ℝ) (b : V₀) :
    ‖kerVec A κ hκ hInv σ hσ₀ hσ₁ r b‖ ^ 2 =
      1 + (rSigma A κ σ hκ hInv hσ₀ hσ₁ (betaOf b) / r) ^ 2 := by
  rw [kerVec, generator_norm_sq_real, rSigma]
  ring

include hκ hInv in
/-- **The nonzero eigenvalue gap of `H_{σ,r}`.** -/
theorem branchHam_gap (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (r : ℝ) (b : V₀) (x : Pub V₀)
    (c : ℂ) (hx : x ≠ 0) (hHx : branchHam A σ r b x = c • x) (hc : c ≠ 0) :
    RegularizationGap.gap κ σ ≤ ‖c‖ := by
  rw [← branchHam_eq A κ hκ hInv σ hσ₀ hσ₁ r b] at hHx
  exact HilbertAugmentationGap.regularizedAugmentedHamiltonian_nonzero_eigenvalue_gap
    A κ σ hκ hInv hσ₀ hσ₁ (betaOf b) _ x c hx hc hHx

/-- The solution coordinates of `u₀` at `σ = 0` are `A⁻¹ b / r`. -/
theorem solEmb_kerVec (h₀ : (0 : ℝ) ≤ 0) (h₁ : (0 : ℝ) ≤ 1) (r : ℝ) (b : V₀) :
    (solEmb†) (kerVec A κ hκ hInv 0 h₀ h₁ r b) = ((1 / r : ℝ) : ℂ) • A.symm b := by
  rw [solEmb_adjoint_apply]
  simp only [kerVec, generator, WithLp.toLp_snd, WithLp.toLp_fst]
  rw [M0_symm_beta A κ hκ hInv b]
  simp only [WithLp.smul_fst, WithLp.smul_snd, WithLp.toLp_fst, WithLp.toLp_snd]

end Hamiltonian

/-! ### Filtered probabilities -/

section Filter

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [CompleteSpace V]

/-- **Equation `qls:eq:filterprobability`** for the averaging filter. -/
theorem filter_bounds {W : V →L[ℂ] V} (hW : UnitaryFilter.Unitary W) (b : ℝ) (hb : 0 < b)
    (hgap : ∀ (z : ℂ) (v : V), v ≠ 0 → W v = z • v → z ≠ 1 → 2 * b ≤ ‖z - 1‖)
    (N : ℕ) (hN : 0 < N) (k : ℕ) (x : V) :
    ‖UnitaryFilter.fixedProj W x‖ ^ 2 ≤ ‖UnitaryFilter.filter W N k x‖ ^ 2 ∧
      ‖UnitaryFilter.filter W N k x‖ ^ 2 ≤
        ‖UnitaryFilter.fixedProj W x‖ ^ 2 + ((1 / (N * b)) ^ k * ‖x‖) ^ 2 := by
  have h1 := UnitaryFilter.filter_norm_sq hW b hb hgap N hN k x
  have h2 := UnitaryFilter.filter_sub_proj_le hW b hb hgap N hN k x
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  constructor <;>
    nlinarith [sq_nonneg ‖UnitaryFilter.filter W N k x - UnitaryFilter.fixedProj W x‖]

end Filter

end

end SparseLinearSystems.Augmented
