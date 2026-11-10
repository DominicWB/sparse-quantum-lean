import LargeSparsityCore.Clusters
import LargeSparsityCore.ProductFilter
import SparseHamiltonian.OperatorFilter

set_option autoImplicit false

/-!
# The product-filter bound from resolvent bounds on three circles

Let `T` be a contraction on a finite-dimensional complex normed space. Suppose that `z - T` is
invertible on the closed disk `|z - 1| ≤ ρ` outside two open disks `|z - μᵢ| < ζ` (the *gap
region*), that the two closed isolated disks lie in the disk around one and are disjoint, and that
the resolvent is bounded by `M` on the isolated circles and by `M_b` on the circle `|z - 1| = ρ`.
Then the product filter `f = g_B^m g_p^k` satisfies (`filter_norm_le`)

`‖f(T)‖ ≤ 2 ζ F M + (2/(Bρ))^m ρ M_b (1 + 2 ζ M)`,

where `F` bounds `|f|` on the isolated circles.

This replaces the contour of the manuscript (`opt:eq:bulk-contour`), which uses an outer arc of
`|z| = 1 + 1/B₀` and an inner arc of `|z - 1| = ρ₀`, by full circles: the two isolated clusters are
split off by Riesz projections (`LargeSparsityCore.Riesz`, `LargeSparsityCore.Clusters`), and on
the remaining bulk projection `P_b` the average is `g_B(T) P_b = B⁻¹ (1 - T^B) S` with
`(1 - T) S = P_b`; contractivity bounds `1 - T^B`, and a Cauchy estimate on the full circle
`|z - 1| = ρ` bounds `S^m` (`inverse_power_norm_le_sphere`). As in the manuscript, there is no
factor proportional to the inverse spectral gap `B ~ q/β` in the bulk term beyond `(2/(Bρ))^m`.
-/

namespace LargeSparsityCore.FilterBound

noncomputable section

open Complex Metric Polynomial SparseHamiltonian
open scoped Real

/-- Cauchy's estimate for powers, with the bound required only on the sphere. -/
theorem inverse_power_norm_le_sphere {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (R : A) (r M : ℝ) (hr : 0 < r)
    (hu : ∀ z : ℂ, ‖z‖ ≤ r → IsUnit (1 - z • R))
    (hb : ∀ z : ℂ, ‖z‖ = r → ‖Ring.inverse (1 - z • R) * R‖ ≤ M) (n : ℕ) :
    ‖R ^ (n + 1)‖ ≤ M / r ^ n := by
  let f : ℂ → A := fun z => Ring.inverse (1 - z • R) * R
  have hd : DifferentiableOn ℂ f (Metric.closedBall 0 r) := by
    intro z hz
    have hunit := hu z (by simpa using hz)
    have hinner : DifferentiableAt ℂ (fun w : ℂ => 1 - w • R) z :=
      (differentiableAt_id.smul_const R).const_sub 1
    exact ((differentiableAt_inverse hunit).comp z hinner).mul_const R
      |>.differentiableWithinAt
  have hbound := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    (hd.diffContOnCl_ball (fun _ hz => hz))
    (fun z hz => hb z (by simpa using hz))
  rw [OperatorFilter.inverse_generating_derivative] at hbound
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul] at hbound
  apply (mul_le_mul_iff_right₀ hn).mp
  simpa [mul_div_assoc] using hbound

section Bulk

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

omit [NormedAlgebra ℂ A] [CompleteSpace A] in
/-- Elements commuting with `x` commute with `Ring.inverse x`. -/
theorem commute_ring_inverse {a x : A} (h : Commute a x) : Commute a (Ring.inverse x) := by
  by_cases hu : IsUnit x
  · obtain ⟨u, rfl⟩ := hu
    rw [Ring.inverse_unit]
    exact h.units_inv_right
  · rw [Ring.inverse_non_unit _ hu]
    exact Commute.zero_right a

omit [CompleteSpace A] in
theorem commute_T_outer (T P : A) (hTP : T * P = P * T) (z : ℂ) :
    Commute T (Riesz.outer T P z) := by
  have h1 : Commute T (z • (1 : A) - T) :=
    ((Commute.one_right T).smul_right z).sub_right (Commute.refl T)
  have h2 : Commute T P := hTP
  exact (h1.mul_right h2).add_right ((Commute.one_right T).sub_right h2)

omit [CompleteSpace A] in
/-- Where both `z - T` and the exterior operator are units, `X⁻¹ P = (z - T)⁻¹ P`. -/
theorem inverse_outer_mul_proj (T P : A) (hP : P * P = P) (hTP : T * P = P * T) (z : ℂ)
    (hz : IsUnit (z • (1 : A) - T)) (hout : IsUnit (Riesz.outer T P z)) :
    Ring.inverse (Riesz.outer T P z) * P = Riesz.resolvent T z * P := by
  have hc : Commute (z • (1 : A) - T) (Ring.inverse (Riesz.outer T P z)) :=
    commute_ring_inverse (Riesz.commute_sub_outer T P hTP z)
  have h1 : Ring.inverse (Riesz.outer T P z) * ((z • (1 : A) - T) * P) = P := by
    rw [← Riesz.outer_mul_proj T P hP z, ← mul_assoc, Ring.inverse_mul_cancel _ hout, one_mul]
  unfold Riesz.resolvent
  calc Ring.inverse (Riesz.outer T P z) * P =
        Ring.inverse (z • (1 : A) - T) * ((z • (1 : A) - T) *
          (Ring.inverse (Riesz.outer T P z) * P)) := by
          rw [← mul_assoc, Ring.inverse_mul_cancel _ hz, one_mul]
    _ = Ring.inverse (z • (1 : A) - T) * (Ring.inverse (Riesz.outer T P z) *
          ((z • (1 : A) - T) * P)) := by
          rw [← mul_assoc (z • (1 : A) - T), hc.eq, mul_assoc]
    _ = Ring.inverse (z • (1 : A) - T) * P := by rw [h1]

/-- The inverse of `1 - T` on the range of the idempotent `P`. -/
def bulkInverse (T P : A) : A := Ring.inverse (Riesz.outer T P 1) * P

omit [CompleteSpace A] in
theorem outer_sub_eq (T P : A) (w : ℂ) :
    Riesz.outer T P (1 - w) = Riesz.outer T P 1 - w • P := by
  simp only [Riesz.outer, sub_smul, one_smul, sub_mul, smul_mul_assoc, one_mul]
  abel

omit [CompleteSpace A] in
theorem one_sub_smul_bulkInverse (T P : A) (w : ℂ) (h1 : IsUnit (Riesz.outer T P 1)) :
    1 - w • bulkInverse T P = Ring.inverse (Riesz.outer T P 1) * Riesz.outer T P (1 - w) := by
  rw [outer_sub_eq, mul_sub, Ring.inverse_mul_cancel _ h1, mul_smul_comm, bulkInverse]

omit [CompleteSpace A] in
theorem bulkInverse_mul_one_sub (T P : A) (hP : P * P = P) (hTP : T * P = P * T)
    (h1 : IsUnit (Riesz.outer T P 1)) : bulkInverse T P * (1 - T) = P := by
  have hX := Riesz.outer_mul_proj T P hP 1
  rw [one_smul] at hX
  have hPT : P * (1 - T) = (1 - T) * P := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hTP]
  rw [bulkInverse, mul_assoc, hPT, ← hX, ← mul_assoc, Ring.inverse_mul_cancel _ h1, one_mul]

/-- **Cauchy estimate on the bulk.** If the exterior operator of `P` is invertible on the closed
disk `|z - 1| ≤ ρ` and `‖X(z)⁻¹ P‖ ≤ M` on its boundary, then `‖S^{n+1}‖ ≤ M/ρⁿ` for the inverse
`S` of `1 - T` on the range of `P`. -/
theorem bulkInverse_pow_norm_le (T P : A) {ρ M : ℝ} (hρ : 0 < ρ)
    (hout : ∀ z : ℂ, ‖z - 1‖ ≤ ρ → IsUnit (Riesz.outer T P z))
    (hM : ∀ z : ℂ, ‖z - 1‖ = ρ → ‖Ring.inverse (Riesz.outer T P z) * P‖ ≤ M) (n : ℕ) :
    ‖bulkInverse T P ^ (n + 1)‖ ≤ M / ρ ^ n := by
  have h1 : IsUnit (Riesz.outer T P 1) := hout 1 (by simp [hρ.le])
  have hw : ∀ w : ℂ, ‖(1 - w) - 1‖ = ‖w‖ := fun w => by
    rw [sub_sub_cancel_left, norm_neg]
  apply inverse_power_norm_le_sphere (bulkInverse T P) ρ M hρ
  · intro w hwρ
    rw [one_sub_smul_bulkInverse T P w h1]
    exact h1.ringInverse.mul (hout (1 - w) (by rw [hw]; exact hwρ))
  · intro w hwρ
    have hu := hout (1 - w) (by rw [hw]; exact hwρ.le)
    rw [one_sub_smul_bulkInverse T P w h1, Ring.inverse_mul (Or.inl h1.ringInverse),
      Ring.inverse_inverse h1, bulkInverse, mul_assoc, ← mul_assoc (Riesz.outer T P 1),
      Ring.mul_inverse_cancel _ h1, one_mul]
    exact hM (1 - w) (by rw [hw, hwρ])

/-- **Bulk filter bound.** `‖g_B(T)^m P‖ ≤ (2/(Bρ))^m ρ M` for a contraction `T`. -/
theorem average_pow_mul_proj_norm_le (T P : A) (hP : P * P = P) (hTP : T * P = P * T)
    (hT : ‖T‖ ≤ 1) (hone : ‖(1 : A)‖ ≤ 1) {ρ M : ℝ} (hρ : 0 < ρ)
    (hout : ∀ z : ℂ, ‖z - 1‖ ≤ ρ → IsUnit (Riesz.outer T P z))
    (hM : ∀ z : ℂ, ‖z - 1‖ = ρ → ‖Ring.inverse (Riesz.outer T P z) * P‖ ≤ M)
    (B m : ℕ) (hB : 1 ≤ B) (hm : 1 ≤ m) :
    ‖FilterCoefficients.operatorGeometricAverage (K := ℂ) B T ^ m * P‖ ≤
      (2 / ((B : ℝ) * ρ)) ^ m * ρ * M := by
  have h1 : IsUnit (Riesz.outer T P 1) := hout 1 (by simp [hρ.le])
  set S := bulkInverse T P with hSdef
  set G := FilterCoefficients.operatorGeometricAverage (K := ℂ) B T
  set C := (1 : A) - T ^ B
  have hPT : Commute P T := hTP.symm
  have hPG : Commute P G := by
    unfold G FilterCoefficients.operatorGeometricAverage FilterCoefficients.geometricSum
    exact (Commute.sum_right _ _ _ fun j _ => hPT.pow_right j).smul_right _
  have hST : Commute S T := by
    rw [hSdef, bulkInverse]
    exact ((commute_ring_inverse (commute_T_outer T P hTP 1)).symm).mul_left hPT
  have hSC : Commute S C := ((Commute.one_right S).sub_right (hST.pow_right B))
  -- `P g_B(T) = B⁻¹ S (1 - T^B)`.
  have hPG' : P * G = (B : ℂ)⁻¹ • (S * C) := by
    have hgeom : (1 - T) * FilterCoefficients.geometricSum B T = C := mul_neg_geom_sum T B
    rw [← bulkInverse_mul_one_sub T P hP hTP h1, ← hSdef]
    unfold G FilterCoefficients.operatorGeometricAverage
    rw [mul_smul_comm, mul_assoc, hgeom]
  -- `g_B(T)^m P = (P g_B(T))^m`.
  have hPpow : ∀ n : ℕ, P ^ (n + 1) = P := fun n => by
    induction n with
    | zero => rw [zero_add, pow_one]
    | succ n ih => rw [pow_succ, ih, hP]
  have hpow : ∀ n : ℕ, G ^ (n + 1) * P = (P * G) ^ (n + 1) := fun n => by
    rw [hPG.mul_pow, hPpow]
    exact ((hPG.pow_right (n + 1)).eq).symm
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hC : ‖C‖ ≤ 2 := by
    calc ‖C‖ ≤ ‖(1 : A)‖ + ‖T ^ B‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add hone ((norm_pow_le' T (by omega)).trans
          (pow_le_one₀ (norm_nonneg _) hT))
      _ = 2 := by norm_num
  have hS := bulkInverse_pow_norm_le T P hρ hout hM n
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  rw [hpow, hPG', smul_pow, hSC.mul_pow, norm_smul, norm_pow, norm_inv, Complex.norm_natCast]
  calc ((B : ℝ)⁻¹) ^ (n + 1) * ‖S ^ (n + 1) * C ^ (n + 1)‖ ≤
        ((B : ℝ)⁻¹) ^ (n + 1) * ((M / ρ ^ n) * 2 ^ (n + 1)) := by
        gcongr
        calc ‖S ^ (n + 1) * C ^ (n + 1)‖ ≤ ‖S ^ (n + 1)‖ * ‖C ^ (n + 1)‖ := norm_mul_le _ _
          _ ≤ (M / ρ ^ n) * 2 ^ (n + 1) := by
            apply mul_le_mul hS ((norm_pow_le' C (by omega)).trans
              (pow_le_pow_left₀ (norm_nonneg _) hC _)) (norm_nonneg _)
            exact (norm_nonneg _).trans hS
    _ = (2 / ((B : ℝ) * ρ)) ^ (n + 1) * ρ * M := by
        have hρ0 : ρ ≠ 0 := hρ.ne'
        have hB0 : (B : ℝ) ≠ 0 := hBpos.ne'
        rw [div_pow, mul_pow, pow_succ ρ n, inv_pow]
        field_simp

end Bulk

section Assembly

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Product-filter bound.** Resolvent bounds on two isolated circles `|z - μᵢ| = ζ` and on the
circle `|z - 1| = ρ`, invertibility on the gap region, and a bound `F` for the scalar filter on
the isolated circles bound the operator filter `g_B(T)^m g_p(T)^k`. -/
theorem filter_norm_le (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) (μ₁ μ₂ : ℂ) {ζ ρ M Mb F : ℝ}
    (hζ : 0 < ζ) (hρ : 0 < ρ)
    (hsep : 2 * ζ ≤ ‖μ₁ - μ₂‖) (hμ₁ : ‖μ₁ - 1‖ + ζ ≤ ρ) (hμ₂ : ‖μ₂ - 1‖ + ζ ≤ ρ)
    (hgap : ∀ z : ℂ, ‖z - 1‖ ≤ ρ → ζ ≤ ‖z - μ₁‖ → ζ ≤ ‖z - μ₂‖ →
      IsUnit (z • (1 : E →L[ℂ] E) - T))
    (hM₁ : ∀ z : ℂ, ‖z - μ₁‖ = ζ → ‖Riesz.resolvent T z‖ ≤ M)
    (hM₂ : ∀ z : ℂ, ‖z - μ₂‖ = ζ → ‖Riesz.resolvent T z‖ ≤ M)
    (hMb : ∀ z : ℂ, ‖z - 1‖ = ρ → ‖Riesz.resolvent T z‖ ≤ Mb)
    (B m p k : ℕ) (hB : 1 ≤ B) (hp : 1 ≤ p) (hm : 1 ≤ m)
    (hF₁ : ∀ z : ℂ, ‖z - μ₁‖ = ζ → ‖FilterCoefficients.geometricAverage B z ^ m *
      FilterCoefficients.geometricAverage p z ^ k‖ ≤ F)
    (hF₂ : ∀ z : ℂ, ‖z - μ₂‖ = ζ → ‖FilterCoefficients.geometricAverage B z ^ m *
      FilterCoefficients.geometricAverage p z ^ k‖ ≤ F) :
    ‖averagedGeometricFilter T B ^ m * averagedGeometricFilter T p ^ k‖ ≤
      2 * (ζ * (F * M)) + (2 / ((B : ℝ) * ρ)) ^ m * ρ * (Mb * (1 + 2 * (ζ * M))) := by
  set f := averagedGeometricFilter T B ^ m * averagedGeometricFilter T p ^ k
  have hdist : ∀ a b : ℂ, ‖a - b‖ = dist a b := fun a b => (dist_eq_norm a b).symm
  obtain ⟨P₁, P₂, hP₁, hP₂, h12, h21, hTP₁, hTP₂, hout₁, hin₁, hout₂, hin₂, houtb⟩ :=
    Clusters.exists_clusters T (ball μ₁ ζ) (ball μ₂ ζ) (closedBall 1 ρ)ᶜ (by
      intro z hz1 hz2 hzB
      rw [mem_ball, not_lt, ← hdist] at hz1 hz2
      rw [Set.mem_compl_iff, not_not, mem_closedBall, ← hdist] at hzB
      exact hgap z hzB hz1 hz2)
  -- Geometry of the isolated disks.
  have hfar₁ : ∀ z : ℂ, ‖z - μ₁‖ ≤ ζ → ζ ≤ ‖z - μ₂‖ ∧ ‖z - 1‖ ≤ ρ := by
    intro z hz
    constructor
    · have h := norm_sub_le_norm_sub_add_norm_sub μ₁ z μ₂
      rw [norm_sub_rev μ₁ z] at h
      linarith
    · have h := norm_sub_le_norm_sub_add_norm_sub z μ₁ 1
      linarith
  have hfar₂ : ∀ z : ℂ, ‖z - μ₂‖ ≤ ζ → ζ ≤ ‖z - μ₁‖ ∧ ‖z - 1‖ ≤ ρ := by
    intro z hz
    constructor
    · have h := norm_sub_le_norm_sub_add_norm_sub μ₂ z μ₁
      rw [norm_sub_rev μ₂ z, norm_sub_rev μ₂ μ₁] at h
      linarith
    · have h := norm_sub_le_norm_sub_add_norm_sub z μ₂ 1
      linarith
  have hRout₁ : ∀ z : ℂ, ζ ≤ ‖z - μ₁‖ → IsUnit (Riesz.outer T P₁ z) := fun z hz =>
    hout₁ z (by rw [mem_ball, not_lt, ← hdist]; exact hz)
  have hRin₁ : ∀ z : ℂ, ‖z - μ₁‖ ≤ ζ → IsUnit (Riesz.inner T P₁ z) := fun z hz =>
    hin₁ z (by rw [mem_ball, not_lt, ← hdist]; exact (hfar₁ z hz).1)
      (by rw [Set.mem_compl_iff, not_not, mem_closedBall, ← hdist]; exact (hfar₁ z hz).2)
  have hRout₂ : ∀ z : ℂ, ζ ≤ ‖z - μ₂‖ → IsUnit (Riesz.outer T P₂ z) := fun z hz =>
    hout₂ z (by rw [mem_ball, not_lt, ← hdist]; exact hz)
  have hRin₂ : ∀ z : ℂ, ‖z - μ₂‖ ≤ ζ → IsUnit (Riesz.inner T P₂ z) := fun z hz =>
    hin₂ z (by rw [mem_ball, not_lt, ← hdist]; exact (hfar₂ z hz).1)
      (by rw [Set.mem_compl_iff, not_not, mem_closedBall, ← hdist]; exact (hfar₂ z hz).2)
  have hsph : ∀ (c : ℂ) (z : ℂ), z ∈ sphere c ζ → ‖z - c‖ = ζ := fun c z hz => by
    rwa [mem_sphere, dist_eq_norm] at hz
  -- Isolated parts.
  have hfP₁ : ‖f * P₁‖ ≤ ζ * (F * M) := by
    have h := Riesz.norm_aeval_mul_le T P₁ hP₁ hTP₁ μ₁ hζ hRout₁ hRin₁
      (ProductFilter.cpoly B m p k)
      (fun z hz => by rw [ProductFilter.eval_cpoly]; exact hF₁ z (hsph μ₁ z hz))
      (fun z hz => hM₁ z (hsph μ₁ z hz))
    rwa [ProductFilter.aeval_cpoly] at h
  have hfP₂ : ‖f * P₂‖ ≤ ζ * (F * M) := by
    have h := Riesz.norm_aeval_mul_le T P₂ hP₂ hTP₂ μ₂ hζ hRout₂ hRin₂
      (ProductFilter.cpoly B m p k)
      (fun z hz => by rw [ProductFilter.eval_cpoly]; exact hF₂ z (hsph μ₂ z hz))
      (fun z hz => hM₂ z (hsph μ₂ z hz))
    rwa [ProductFilter.aeval_cpoly] at h
  have hnP₁ : ‖P₁‖ ≤ ζ * M :=
    Riesz.norm_proj_le T P₁ hP₁ hTP₁ μ₁ hζ hRout₁ hRin₁ (fun z hz => hM₁ z (hsph μ₁ z hz))
  have hnP₂ : ‖P₂‖ ≤ ζ * M :=
    Riesz.norm_proj_le T P₂ hP₂ hTP₂ μ₂ hζ hRout₂ hRin₂ (fun z hz => hM₂ z (hsph μ₂ z hz))
  -- The bulk projection.
  set Pb := 1 - P₁ - P₂ with hPbdef
  have hPb : Pb * Pb = Pb := by
    rw [← sub_eq_zero]
    have h : ((1 : E →L[ℂ] E) - P₁ - P₂) * (1 - P₁ - P₂) - (1 - P₁ - P₂) =
        (P₁ * P₁ - P₁) + (P₂ * P₂ - P₂) + P₁ * P₂ + P₂ * P₁ := by noncomm_ring
    rw [hPbdef, h, hP₁, hP₂, h12, h21, sub_self, sub_self, add_zero, add_zero, add_zero]
  have hTPb : T * Pb = Pb * T := by
    rw [hPbdef, mul_sub, mul_sub, sub_mul, sub_mul, mul_one, one_mul, hTP₁, hTP₂]
  have hnPb : ‖Pb‖ ≤ 1 + 2 * (ζ * M) := by
    calc ‖Pb‖ ≤ ‖(1 : E →L[ℂ] E) - P₁‖ + ‖P₂‖ := norm_sub_le _ _
      _ ≤ ‖(1 : E →L[ℂ] E)‖ + ‖P₁‖ + ‖P₂‖ := by gcongr; exact norm_sub_le _ _
      _ ≤ 1 + ζ * M + ζ * M := by gcongr; exact ContinuousLinearMap.norm_id_le
      _ = 1 + 2 * (ζ * M) := by ring
  have hRoutb : ∀ z : ℂ, ‖z - 1‖ ≤ ρ → IsUnit (Riesz.outer T Pb z) := fun z hz =>
    houtb z (by rw [Set.mem_compl_iff, not_not, mem_closedBall, ← hdist]; exact hz)
  have hMb' : ∀ z : ℂ, ‖z - 1‖ = ρ →
      ‖Ring.inverse (Riesz.outer T Pb z) * Pb‖ ≤ Mb * (1 + 2 * (ζ * M)) := by
    intro z hz
    have hz1 : ζ ≤ ‖z - μ₁‖ := by
      have h := norm_sub_le_norm_sub_add_norm_sub z μ₁ 1
      rw [norm_sub_rev μ₁ 1] at hμ₁
      linarith [norm_sub_rev (1 : ℂ) μ₁]
    have hz2 : ζ ≤ ‖z - μ₂‖ := by
      have h := norm_sub_le_norm_sub_add_norm_sub z μ₂ 1
      linarith [norm_sub_rev (1 : ℂ) μ₂]
    rw [inverse_outer_mul_proj T Pb hPb hTPb z (hgap z hz.le hz1 hz2) (hRoutb z hz.le)]
    calc ‖Riesz.resolvent T z * Pb‖ ≤ ‖Riesz.resolvent T z‖ * ‖Pb‖ := norm_mul_le _ _
      _ ≤ Mb * (1 + 2 * (ζ * M)) := by
          apply mul_le_mul (hMb z hz) hnPb (norm_nonneg _)
          exact (norm_nonneg _).trans (hMb z hz)
  have hbulkB := average_pow_mul_proj_norm_le T Pb hPb hTPb hT ContinuousLinearMap.norm_id_le hρ
    hRoutb hMb' B m hB hm
  rw [OperatorPolynomial.complex_average_eq] at hbulkB
  -- Commutation of the two filters and assembly.
  have hGG : Commute (averagedGeometricFilter T B ^ m) (averagedGeometricFilter T p ^ k) := by
    have hc : Commute (averagedGeometricFilter T B) (averagedGeometricFilter T p) := by
      unfold averagedGeometricFilter
      exact ((Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ =>
        (Commute.refl T).pow_pow i j).smul_left _).smul_right _
    exact hc.pow_pow m k
  have hfPb : ‖f * Pb‖ ≤ (2 / ((B : ℝ) * ρ)) ^ m * ρ * (Mb * (1 + 2 * (ζ * M))) := by
    have hsplit : f * Pb = averagedGeometricFilter T p ^ k *
        (averagedGeometricFilter T B ^ m * Pb) := by
      rw [← mul_assoc, ← hGG.eq]
    rw [hsplit]
    calc _ ≤ ‖averagedGeometricFilter T p ^ k‖ *
          ‖averagedGeometricFilter T B ^ m * Pb‖ := norm_mul_le _ _
      _ ≤ 1 * ((2 / ((B : ℝ) * ρ)) ^ m * ρ * (Mb * (1 + 2 * (ζ * M)))) :=
          mul_le_mul (averagedGeometricFilter_pow_norm_le T hT hp k) hbulkB (norm_nonneg _)
            zero_le_one
      _ = _ := one_mul _
  have hdecomp : f = f * P₁ + f * P₂ + f * Pb := by
    rw [← mul_add, ← mul_add, hPbdef]
    noncomm_ring
  rw [hdecomp]
  calc ‖f * P₁ + f * P₂ + f * Pb‖ ≤ ‖f * P₁‖ + ‖f * P₂‖ + ‖f * Pb‖ := norm_add₃_le
    _ ≤ ζ * (F * M) + ζ * (F * M) + (2 / ((B : ℝ) * ρ)) ^ m * ρ * (Mb * (1 + 2 * (ζ * M))) := by
        gcongr
    _ = _ := by ring

end Assembly

end

end LargeSparsityCore.FilterBound
