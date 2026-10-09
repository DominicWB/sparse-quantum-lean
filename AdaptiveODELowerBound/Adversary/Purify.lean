import AdaptiveODELowerBound.Adversary.Kernel
import ODELowerBoundExtensions.Release.Purify

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

/-!
# Lossless purification of an adaptive protocol

Manuscript lines 2672-2673 ("Randomised or adaptive algorithms are covered by purification and
deferred measurement") and lines 4226-4234 (the bounded-error step of Lemma `odel:lem:outer`).

For an adaptive protocol `T` of unitary runs on a finite-dimensional workspace, there are unit
vectors `Ψ_x` in a Hilbert space with Gram matrix `treeKernel T` and a contraction `R` whose
expectation on `Ψ_x` is the heralded correlation `corr B (T.successDensity x)` of any contraction
`B` on the output space (`exists_tree_purification`). At a final leaf this is the released
`Release.exists_purification`. At a test run (`tree_purification_step`) the deferred measurement
gives `Ψ'_x = (Π φ_x ⊗ Ψ^s_x, (1 - Π) φ_x ⊗ Ψ^f_x)` in the `L²` product of the two branch spaces
(`Release.tens`, the coordinates of the workspace) and `R' = (1 ⊗ R_s) ⊕ (1 ⊗ R_f)`; the
expectation is `p_x corr_s + (1 - p_x) corr_f`, `p_x = ‖F† φ_x‖²`, the success density of the
tree.
-/

namespace AdaptiveODELowerBound.Adversary

noncomputable section
open SparseHamiltonian SparseLowerBounds OracleCircuit SparseLinearSystems.Protocol
open LinearSystemLowerBound (corr corr_add corr_smul_real)
open ODELowerBoundExtensions.Release (tens inner_tens fiber_tens)
open scoped InnerProduct InnerProductSpace

variable {E W Fl X L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Fl] [InnerProductSpace ℂ Fl] [CompleteSpace Fl]
  {O : L → X → W →L[ℂ] W}

section Pair

variable {A C : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup C]
  [InnerProductSpace ℂ C]

/-- The block-diagonal operator `R₁ ⊕ R₂` on the `L²` product `A ⊕ C`. -/
def pairOp (R₁ : A →L[ℂ] A) (R₂ : C →L[ℂ] C) : WithLp 2 (A × C) →L[ℂ] WithLp 2 (A × C) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ A C).symm.toContinuousLinearMap ∘L (R₁.prodMap R₂) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℂ A C).toContinuousLinearMap

/-- `(R₁ ⊕ R₂)(u, v) = (R₁ u, R₂ v)`. -/
theorem pairOp_toLp (R₁ : A →L[ℂ] A) (R₂ : C →L[ℂ] C) (u : A) (v : C) :
    pairOp R₁ R₂ (WithLp.toLp 2 (u, v)) = WithLp.toLp 2 (R₁ u, R₂ v) := rfl

/-- `⟪(u, v), (u', v')⟫ = ⟪u, u'⟫ + ⟪v, v'⟫` in the `L²` product. -/
theorem inner_pair (u u' : A) (v v' : C) :
    ⟪(WithLp.toLp 2 (u, v) : WithLp 2 (A × C)), WithLp.toLp 2 (u', v')⟫_ℂ =
      ⟪u, u'⟫_ℂ + ⟪v, v'⟫_ℂ := rfl

/-- The direct sum of two contractions is a contraction. -/
theorem norm_pairOp_le (R₁ : A →L[ℂ] A) (R₂ : C →L[ℂ] C) (h₁ : ‖R₁‖ ≤ 1) (h₂ : ‖R₂‖ ≤ 1) :
    ‖pairOp R₁ R₂‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  rw [one_mul]
  have e₁ : ‖R₁ (WithLp.ofLp z).1‖ ≤ ‖(WithLp.ofLp z).1‖ :=
    (R₁.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) h₁)
  have e₂ : ‖R₂ (WithLp.ofLp z).2‖ ≤ ‖(WithLp.ofLp z).2‖ :=
    (R₂.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) h₂)
  have hsq : ‖pairOp R₁ R₂ z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2]
    exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) e₁ 2)
      (pow_le_pow_left₀ (norm_nonneg _) e₂ 2)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq

end Pair

/-- **One step of the purification**: purifications of the success and failure subtrees (unit
vectors with the subtree kernels as Gram matrices and contractions reading the heralded
correlations of `B`) give a purification of the test node `Tree.test t s f`. -/
theorem tree_purification_step [FiniteDimensional ℂ W] (hO : ∀ l x, IsUnitary (O l x))
    (t : TestRun O Fl) (s f : Tree O Fl E) (B : E →L[ℂ] E)
    {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (Ψ₁ : X → H₁) (R₁ : H₁ →L[ℂ] H₁) (hΨ₁ : ∀ x, ‖Ψ₁ x‖ = 1) (hR₁ : ‖R₁‖ ≤ 1)
    (hG₁ : ∀ x x', ⟪Ψ₁ x, Ψ₁ x'⟫_ℂ = treeKernel s x x')
    (hC₁ : ∀ x, (⟪Ψ₁ x, R₁ (Ψ₁ x)⟫_ℂ).re = corr B (s.successDensity x))
    (Ψ₂ : X → H₂) (R₂ : H₂ →L[ℂ] H₂) (hΨ₂ : ∀ x, ‖Ψ₂ x‖ = 1) (hR₂ : ‖R₂‖ ≤ 1)
    (hG₂ : ∀ x x', ⟪Ψ₂ x, Ψ₂ x'⟫_ℂ = treeKernel f x x')
    (hC₂ : ∀ x, (⟪Ψ₂ x, R₂ (Ψ₂ x)⟫_ℂ).re = corr B (f.successDensity x)) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (Ψ : X → H)
      (R : H →L[ℂ] H),
      (∀ x, ‖Ψ x‖ = 1) ∧ ‖R‖ ≤ 1 ∧
        (∀ x x', ⟪Ψ x, Ψ x'⟫_ℂ = treeKernel (.test t s f) x x') ∧
        ∀ x, (⟪Ψ x, R (Ψ x)⟫_ℂ).re = corr B ((Tree.test t s f).successDensity x) := by
  classical
  set F := t.flag with hFdef
  have hF : F† ∘L F = 1 := t.flag_isometry
  have hFF : ∀ v, (F†) (F v) = v := fun v => by
    simpa using congrArg (fun A : Fl →L[ℂ] Fl => A v) hF
  set φ : X → W := fun x => t.circuit.eval x t.seed with hφ
  have hφn : ∀ x, ⟪φ x, φ x⟫_ℂ = 1 := fun x => by
    rw [inner_self_eq_norm_sq_to_K, hφ, (t.circuit.eval x).norm_map_iff_adjoint_comp_self.mpr
      (t.circuit.eval_unitary hO x).1, t.seed_unit]
    simp
  -- The success branch `Π φ_x` and the failure branch `(1 - Π) φ_x`.
  set a : X → W := fun x => F ((F†) (φ x)) with ha_def
  set b : X → W := fun x => φ x - a x with hb_def
  have ha : ∀ x x', ⟪a x, a x'⟫_ℂ = ⟪(F†) (φ x), (F†) (φ x')⟫_ℂ := fun x x' => by
    rw [ha_def, ← ContinuousLinearMap.adjoint_inner_left, hFF]
  have hφa : ∀ x x', ⟪φ x, a x'⟫_ℂ = ⟪(F†) (φ x), (F†) (φ x')⟫_ℂ := fun x x' =>
    (ContinuousLinearMap.adjoint_inner_left F _ _).symm
  have haφ : ∀ x x', ⟪a x, φ x'⟫_ℂ = ⟪(F†) (φ x), (F†) (φ x')⟫_ℂ := fun x x' =>
    (ContinuousLinearMap.adjoint_inner_right F _ _).symm
  have hb : ∀ x x', ⟪b x, b x'⟫_ℂ = ⟪φ x, φ x'⟫_ℂ - ⟪(F†) (φ x), (F†) (φ x')⟫_ℂ :=
    fun x x' => by
      simp only [hb_def, inner_sub_left, inner_sub_right, ha, hφa, haφ]
      ring
  have hconst : ∀ u v : W, ⟪(Joint.const u : Joint (Fin 1) W), Joint.const v⟫_ℂ = ⟪u, v⟫_ℂ :=
    fun u v => by simp [PiLp.inner_apply]
  -- The two branch spaces and their `L²` product.
  let Ψ : X → WithLp 2 (Joint (Fin 1 × Fin (Module.finrank ℂ W)) H₁ ×
      Joint (Fin 1 × Fin (Module.finrank ℂ W)) H₂) := fun x =>
    WithLp.toLp 2 (tens (Joint.const (a x) : Joint (Fin 1) W) (Ψ₁ x),
      tens (Joint.const (b x) : Joint (Fin 1) W) (Ψ₂ x))
  let R := pairOp (Joint.fiber (J := Fin 1 × Fin (Module.finrank ℂ W)) fun _ => R₁)
    (Joint.fiber (J := Fin 1 × Fin (Module.finrank ℂ W)) fun _ => R₂)
  have hgram : ∀ x x', ⟪Ψ x, Ψ x'⟫_ℂ =
      ⟪a x, a x'⟫_ℂ * ⟪Ψ₁ x, Ψ₁ x'⟫_ℂ + ⟪b x, b x'⟫_ℂ * ⟪Ψ₂ x, Ψ₂ x'⟫_ℂ := fun x x' => by
    rw [inner_pair, inner_tens, inner_tens, hconst, hconst]
  have hgram' : ∀ x x', ⟪Ψ x, Ψ x'⟫_ℂ = treeKernel (.test t s f) x x' := fun x x' => by
    rw [hgram, ha, hb, hG₁, hG₂]
    rfl
  have hu₁ : ∀ x, ⟪Ψ₁ x, Ψ₁ x⟫_ℂ = 1 := fun x => by rw [inner_self_eq_norm_sq_to_K, hΨ₁]; simp
  have hu₂ : ∀ x, ⟪Ψ₂ x, Ψ₂ x⟫_ℂ = 1 := fun x => by rw [inner_self_eq_norm_sq_to_K, hΨ₂]; simp
  have hp : ∀ x, ⟪(F†) (φ x), (F†) (φ x)⟫_ℂ = ((t.probability x : ℝ) : ℂ) := fun x => by
    rw [inner_self_eq_norm_sq_to_K, TestRun.probability]
    push_cast
    rfl
  refine ⟨_, inferInstance, inferInstance, Ψ, R, fun x => ?_, ?_, hgram', fun x => ?_⟩
  · have h3 : ⟪Ψ x, Ψ x⟫_ℂ = 1 := by
      rw [hgram, ha, hb, hu₁, hu₂, hφn]
      ring
    have h' : ‖Ψ x‖ ^ 2 = 1 ^ 2 := by
      rw [one_pow, @norm_sq_eq_re_inner ℂ, h3, RCLike.one_re]
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 h'
  · exact norm_pairOp_le _ _
      (Joint.norm_fiber_le (fun _ => R₁) zero_le_one fun _ => hR₁)
      (Joint.norm_fiber_le (fun _ => R₂) zero_le_one fun _ => hR₂)
  · have hexp : ⟪Ψ x, R (Ψ x)⟫_ℂ =
        ⟪a x, a x⟫_ℂ * ⟪Ψ₁ x, R₁ (Ψ₁ x)⟫_ℂ + ⟪b x, b x⟫_ℂ * ⟪Ψ₂ x, R₂ (Ψ₂ x)⟫_ℂ := by
      rw [pairOp_toLp, fiber_tens, fiber_tens, inner_pair, inner_tens, inner_tens, hconst,
        hconst]
    have hbb : ⟪b x, b x⟫_ℂ = ((1 - t.probability x : ℝ) : ℂ) := by
      rw [hb, hφn, hp]; push_cast; ring
    have hsd : (Tree.test t s f).successDensity x =
        ((t.probability x : ℝ) : ℂ) • s.successDensity x +
          ((1 - t.probability x : ℝ) : ℂ) • f.successDensity x := rfl
    rw [hexp, ha, hp, hbb, hsd, corr_add, corr_smul_real, corr_smul_real, ← hC₁, ← hC₂,
      Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]

/-- **Lossless purification of an adaptive protocol**: unit vectors `Ψ_x` with Gram matrix the
tree kernel, and a contraction `R` whose expectation on `Ψ_x` is the heralded correlation
`corr B (T.successDensity x)` of any contraction `B`. -/
theorem exists_tree_purification [FiniteDimensional ℂ W] [FiniteDimensional ℂ E]
    (hO : ∀ l x, IsUnitary (O l x)) (T : Tree O Fl E) (B : E →L[ℂ] E) (hB : ‖B‖ ≤ 1) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (Ψ : X → H)
      (R : H →L[ℂ] H),
      (∀ x, ‖Ψ x‖ = 1) ∧ ‖R‖ ≤ 1 ∧ (∀ x x', ⟪Ψ x, Ψ x'⟫_ℂ = treeKernel T x x') ∧
        ∀ x, (⟪Ψ x, R (Ψ x)⟫_ℂ).re = corr B (T.successDensity x) := by
  induction T with
  | final p =>
    obtain ⟨H, i₁, i₂, Ψ, R, hΨ, hR, hG, hC⟩ :=
      ODELowerBoundExtensions.Release.exists_purification hO p B hB
    exact ⟨H, i₁, i₂, Ψ, R, hΨ, hR, hG, hC⟩
  | test t s f ihs ihf =>
    obtain ⟨H₁, _, _, Ψ₁, R₁, hΨ₁, hR₁, hG₁, hC₁⟩ := ihs
    obtain ⟨H₂, _, _, Ψ₂, R₂, hΨ₂, hR₂, hG₂, hC₂⟩ := ihf
    exact tree_purification_step hO t s f B Ψ₁ R₁ hΨ₁ hR₁ hG₁ hC₁ Ψ₂ R₂ hΨ₂ hR₂ hG₂ hC₂

end

end AdaptiveODELowerBound.Adversary
