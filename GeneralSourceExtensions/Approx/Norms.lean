import GeneralSourceExtensions.Approx.Recast

/-!
# Operator-norm bounds for the supplied source operations

The supplied weight preparation acts on the branch register as `P_w ⊗ 1` (`Weights.act`), the
loading oracle as the label-controlled block diagonal `∑_a |a⟩⟨a| ⊗ U_load(a)`
(`Weights.loader`), and every supplied call is enabled on the inactive matrix sector
(`ODESectorTensor.sourcePhysical`). Errors of the supplied operations do not grow under these
embeddings:

* `norm_act_le`: `‖P ⊗ 1‖ ≤ ‖P‖`, by Parseval's identity in an orthonormal basis of the data
  space;
* `norm_loader_sub_le`: `‖loader J - loader J'‖ ≤ δ` if `‖J a - J' a‖ ≤ δ` for every label;
* `norm_sourcePhysical_sub_le`: `‖sourcePhysical S - sourcePhysical S'‖ ≤ ‖S - S'‖`;
* `norm_conj_le`: conjugation by a linear isometry equivalence is norm contractive.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSourceExtensions

noncomputable section
open ContinuousLinearMap
open scoped InnerProduct BigOperators

section Act

variable {σ ι P : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

omit [CompleteSpace P] in
theorem act_add (Q R : GeneralSourceODE.Weights.LabelOp σ) :
    GeneralSourceODE.Weights.act (ι := ι) (P := P) (Q + R) =
      GeneralSourceODE.Weights.act Q + GeneralSourceODE.Weights.act R := by
  ext f b
  change GeneralSourceODE.Weights.act (Q + R) f b =
    GeneralSourceODE.Weights.act Q f b + GeneralSourceODE.Weights.act R f b
  simp only [GeneralSourceODE.Weights.act_apply, GeneralSourceODE.Weights.amp,
    add_apply, PiLp.add_apply, add_smul, Finset.sum_add_distrib]

omit [CompleteSpace P] in
theorem act_smul (c : ℂ) (Q : GeneralSourceODE.Weights.LabelOp σ) :
    GeneralSourceODE.Weights.act (ι := ι) (P := P) (c • Q) =
      c • GeneralSourceODE.Weights.act Q := by
  ext f b
  change GeneralSourceODE.Weights.act (c • Q) f b = c • GeneralSourceODE.Weights.act Q f b
  simp only [GeneralSourceODE.Weights.act_apply, GeneralSourceODE.Weights.amp,
    smul_apply, PiLp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

omit [CompleteSpace P] in
theorem act_sub (Q R : GeneralSourceODE.Weights.LabelOp σ) :
    GeneralSourceODE.Weights.act (ι := ι) (P := P) (Q - R) =
      GeneralSourceODE.Weights.act Q - GeneralSourceODE.Weights.act R := by
  ext f b
  change GeneralSourceODE.Weights.act (Q - R) f b =
    GeneralSourceODE.Weights.act Q f b - GeneralSourceODE.Weights.act R f b
  simp only [GeneralSourceODE.Weights.act_apply, GeneralSourceODE.Weights.amp,
    sub_apply, PiLp.sub_apply, sub_smul, Finset.sum_sub_distrib]

omit [CompleteSpace P] in
/-- `‖(Q ⊗ 1) f‖ ≤ ‖Q‖ ‖f‖`: in an orthonormal basis of the data space every coordinate of `f`
is a label vector, on which `Q` acts. -/
theorem norm_act_apply_le [FiniteDimensional ℂ P] (Q : GeneralSourceODE.Weights.LabelOp σ)
    (f : GeneralSourceODE.Weights.Space σ ι P) :
    ‖GeneralSourceODE.Weights.act (ι := ι) Q f‖ ≤ ‖Q‖ * ‖f‖ := by
  let e := stdOrthonormalBasis ℂ P
  let c : ι → Fin (Module.finrank ℂ P) → EuclideanSpace ℂ σ := fun k i =>
    WithLp.toLp 2 (fun a : σ => inner ℂ (e i) (f (a, k)))
  have hcoord : ∀ (b : σ) (k : ι) (i : Fin (Module.finrank ℂ P)),
      inner ℂ (e i) (GeneralSourceODE.Weights.act Q f (b, k)) = Q (c k i) b := by
    intro b k i
    rw [GeneralSourceODE.Weights.act_apply, inner_sum, GeneralSourceODE.Weights.apply_eq_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [inner_smul_right]
  have hc : ∀ k i, ‖c k i‖ ^ 2 = ∑ a : σ, ‖inner ℂ (e i) (f (a, k))‖ ^ 2 := by
    intro k i
    rw [EuclideanSpace.norm_sq_eq]
  have hsq : ‖GeneralSourceODE.Weights.act (ι := ι) Q f‖ ^ 2 ≤ (‖Q‖ * ‖f‖) ^ 2 := by
    calc ‖GeneralSourceODE.Weights.act (ι := ι) Q f‖ ^ 2
        = ∑ p : σ × ι, ‖GeneralSourceODE.Weights.act Q f p‖ ^ 2 := PiLp.norm_sq_eq_of_L2 _ _
      _ = ∑ p : σ × ι, ∑ i, ‖inner ℂ (e i) (GeneralSourceODE.Weights.act Q f p)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro p _
          rw [OrthonormalBasis.sum_sq_norm_inner_right]
      _ = ∑ k : ι, ∑ i, ∑ b : σ, ‖Q (c k i) b‖ ^ 2 := by
          rw [Fintype.sum_prod_type]
          simp only [hcoord]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_comm]
      _ = ∑ k : ι, ∑ i, ‖Q (c k i)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro i _
          rw [EuclideanSpace.norm_sq_eq]
      _ ≤ ∑ k : ι, ∑ i, ‖Q‖ ^ 2 * ‖c k i‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro k _
          apply Finset.sum_le_sum
          intro i _
          rw [← mul_pow]
          exact pow_le_pow_left₀ (norm_nonneg _) (Q.le_opNorm _) 2
      _ = ‖Q‖ ^ 2 * ∑ k : ι, ∑ a : σ, ∑ i, ‖inner ℂ (e i) (f (a, k))‖ ^ 2 := by
          simp only [hc, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          exact Finset.sum_comm
      _ = (‖Q‖ * ‖f‖) ^ 2 := by
          rw [mul_pow, PiLp.norm_sq_eq_of_L2 _ f, Fintype.sum_prod_type, Finset.sum_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro a _
          exact OrthonormalBasis.sum_sq_norm_inner_right e _
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hsq

omit [CompleteSpace P] in
/-- `‖Q ⊗ 1‖ ≤ ‖Q‖`. -/
theorem norm_act_le [FiniteDimensional ℂ P] (Q : GeneralSourceODE.Weights.LabelOp σ) :
    ‖GeneralSourceODE.Weights.act (ι := ι) (P := P) Q‖ ≤ ‖Q‖ :=
  opNorm_le_bound _ (norm_nonneg _) (norm_act_apply_le Q)

omit [CompleteSpace P] in
/-- `‖Q ⊗ 1 - Q' ⊗ 1‖ ≤ ‖Q - Q'‖`. -/
theorem norm_act_sub_le [FiniteDimensional ℂ P] (Q Q' : GeneralSourceODE.Weights.LabelOp σ) :
    ‖GeneralSourceODE.Weights.act (ι := ι) (P := P) Q - GeneralSourceODE.Weights.act Q'‖ ≤
      ‖Q - Q'‖ := by
  rw [← act_sub]
  exact norm_act_le _

omit [DecidableEq σ] [CompleteSpace P] in
/-- The label-controlled loaders move by at most the largest error of the loaded operations. -/
theorem norm_loader_sub_le (J J' : σ → P →L[ℂ] P) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ a, ‖J a - J' a‖ ≤ δ) :
    ‖GeneralSourceODE.Weights.loader (ι := ι) J - GeneralSourceODE.Weights.loader J'‖ ≤ δ := by
  have e : GeneralSourceODE.Weights.loader (ι := ι) J - GeneralSourceODE.Weights.loader J' =
      WeightedClock.diagonal (fun b : σ × ι => J b.1 - J' b.1) := by
    ext f b
    rfl
  rw [e]
  exact WeightedClock.norm_diagonal_le _ δ hδ (fun b => h b.1)

end Act

section Conj

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Conjugation by a linear isometry equivalence is norm contractive. -/
theorem norm_conj_le (e : E ≃ₗᵢ[ℂ] F) (A : E →L[ℂ] E) : ‖e.conjStarAlgEquiv A‖ ≤ ‖A‖ := by
  apply opNorm_le_bound _ (norm_nonneg _)
  intro v
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, LinearIsometryEquiv.norm_map]
  refine (A.le_opNorm _).trans ?_
  rw [LinearIsometryEquiv.norm_map]

theorem norm_conj_sub_le (e : E ≃ₗᵢ[ℂ] F) (A B : E →L[ℂ] E) :
    ‖e.conjStarAlgEquiv A - e.conjStarAlgEquiv B‖ ≤ ‖A - B‖ := by
  rw [← map_sub]
  exact norm_conj_le e _

end Conj

section Sector

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [DecidableEq A] [DecidableEq B] in
/-- An enabled supplied call moves by at most the error of the supplied operation. -/
theorem norm_sourcePhysical_sub_le (S S' : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) :
    ‖ODESectorTensor.sourcePhysical (B := B) S - ODESectorTensor.sourcePhysical (B := B) S'‖ ≤
      ‖S - S'‖ := by
  unfold ODESectorTensor.sourcePhysical
  refine (norm_conj_sub_le _ _ _).trans ?_
  have e : WeightedClock.diagonal (fun w : NativeControlledOracle.Workspace B =>
        if w.1.1.1 then (1 : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) else S) -
      WeightedClock.diagonal (fun w : NativeControlledOracle.Workspace B =>
        if w.1.1.1 then (1 : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) else S') =
      WeightedClock.diagonal (fun w : NativeControlledOracle.Workspace B =>
        (if w.1.1.1 then (1 : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) else S) -
          (if w.1.1.1 then (1 : EuclideanSpace ℂ A →L[ℂ] EuclideanSpace ℂ A) else S')) := by
    ext f w
    rfl
  rw [e]
  apply WeightedClock.norm_diagonal_le _ _ (norm_nonneg _)
  intro w
  split_ifs
  · rw [sub_self, norm_zero]
    exact norm_nonneg _
  · exact le_rfl

end Sector

end

end SparseHamiltonian.GeneralSourceExtensions
