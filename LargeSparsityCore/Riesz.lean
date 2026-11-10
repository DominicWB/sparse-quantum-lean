import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false

/-!
# Riesz projections and the Dunford formula on circles

Let `T` be an element of a complete normed complex algebra and let `P` be an idempotent commuting
with `T`. Suppose that `(z - T) P + (1 - P)` is invertible for every `z` outside the open disk of
radius `r` about `c`, and that `(z - T)(1 - P) + P` is invertible for every `z` in the closed disk.
Then the resolvent integral over the circle is the projection:

`(2πi)⁻¹ ∮_{|z - c| = r} (z - T)⁻¹ dz = P` (`riesz`),

and for every polynomial `f`, `(2πi)⁻¹ ∮ f(z) (z - T)⁻¹ dz = f(T) P` (`dunford`). Consequently
`‖P‖ ≤ r M` and `‖f(T) P‖ ≤ r F M` when `‖(z - T)⁻¹‖ ≤ M` and `|f(z)| ≤ F` on the circle
(`norm_proj_le`, `norm_aeval_mul_le`).

The exterior part `(z - T)⁻¹ P` is analytic outside the disk; its integral does not depend on the
radius (Cauchy's theorem on annuli) and tends to `2πi P` as the radius grows. The interior part
`(z - T)⁻¹ (1 - P)` is analytic on the closed disk, so its integral vanishes. No spectral theorem
and no normality is used.
-/

namespace LargeSparsityCore.Riesz

noncomputable section

open Complex Metric Polynomial
open scoped Real

section RingIdentities

variable {R : Type*} [Ring R] (A P : R)

/-! Polynomial identities in two noncommuting variables, written with the defects
`P * P - P` and `P * A - A * P` so that they can be applied to commuting idempotents. -/

theorem outer_proj_identity :
    (A * P + (1 - P)) * P - A * P = (A - 1) * (P * P - P) := by noncomm_ring

theorem outer_compl_identity :
    (A * P + (1 - P)) * (1 - P) - (1 - P) = (1 - A) * (P * P - P) := by noncomm_ring

theorem inner_proj_identity :
    (A * (1 - P) + P) * P - P = (1 - A) * (P * P - P) := by noncomm_ring

theorem inner_compl_identity :
    (A * (1 - P) + P) * (1 - P) - A * (1 - P) = (A - 1) * (P * P - P) := by noncomm_ring

theorem proj_outer_identity :
    P * (A * P + (1 - P)) - (A * P + (1 - P)) * P = (P * A - A * P) * P := by noncomm_ring

theorem proj_inner_identity :
    P * (A * (1 - P) + P) - (A * (1 - P) + P) * P = (P * A - A * P) * (1 - P) := by noncomm_ring

theorem sub_outer_identity :
    A * (A * P + (1 - P)) - (A * P + (1 - P)) * A = (1 - A) * (P * A - A * P) := by noncomm_ring

theorem sub_inner_identity :
    A * (A * (1 - P) + P) - (A * (1 - P) + P) * A = (A - 1) * (P * A - A * P) := by noncomm_ring

theorem outer_inner_identity :
    (A * P + (1 - P)) * (A * (1 - P) + P) - A =
      -((A - 1) * (A - 1) * (P * P - P)) + (A - 1) * (P * A - A * P) * (1 - P) := by
  noncomm_ring

end RingIdentities

section Definitions

variable {𝒜 : Type*} [Ring 𝒜] [Algebra ℂ 𝒜]

/-- The resolvent `(z - T)⁻¹` (with the junk value of `Ring.inverse` on the spectrum). -/
def resolvent (T : 𝒜) (z : ℂ) : 𝒜 := Ring.inverse (z • (1 : 𝒜) - T)

/-- The operator `(z - T) P + (1 - P)`: `z - T` on the range of `P`, the identity on its
complement. -/
def outer (T P : 𝒜) (z : ℂ) : 𝒜 := (z • (1 : 𝒜) - T) * P + (1 - P)

/-- The operator `(z - T)(1 - P) + P`: `z - T` on the range of `1 - P`, the identity on the range
of `P`. -/
def inner (T P : 𝒜) (z : ℂ) : 𝒜 := (z • (1 : 𝒜) - T) * (1 - P) + P

variable (T P : 𝒜)

theorem commute_sub (hTP : T * P = P * T) (z : ℂ) :
    P * (z • (1 : 𝒜) - T) - (z • (1 : 𝒜) - T) * P = 0 := by
  rw [sub_mul, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one, hTP,
    sub_sub_sub_cancel_left, sub_self]

theorem outer_mul_proj (hP : P * P = P) (z : ℂ) : outer T P z * P = (z • (1 : 𝒜) - T) * P := by
  rw [← sub_eq_zero, outer, outer_proj_identity, hP, sub_self, mul_zero]

theorem outer_mul_compl (hP : P * P = P) (z : ℂ) : outer T P z * (1 - P) = 1 - P := by
  rw [← sub_eq_zero, outer, outer_compl_identity, hP, sub_self, mul_zero]

theorem inner_mul_proj (hP : P * P = P) (z : ℂ) : inner T P z * P = P := by
  rw [← sub_eq_zero, inner, inner_proj_identity, hP, sub_self, mul_zero]

theorem inner_mul_compl (hP : P * P = P) (z : ℂ) :
    inner T P z * (1 - P) = (z • (1 : 𝒜) - T) * (1 - P) := by
  rw [← sub_eq_zero, inner, inner_compl_identity, hP, sub_self, mul_zero]

theorem commute_outer (hTP : T * P = P * T) (z : ℂ) : Commute P (outer T P z) := by
  unfold Commute SemiconjBy
  rw [← sub_eq_zero, outer, proj_outer_identity, commute_sub T P hTP z, zero_mul]

theorem commute_inner (hTP : T * P = P * T) (z : ℂ) : Commute P (inner T P z) := by
  unfold Commute SemiconjBy
  rw [← sub_eq_zero, inner, proj_inner_identity, commute_sub T P hTP z, zero_mul]

theorem commute_sub_outer (hTP : T * P = P * T) (z : ℂ) :
    Commute (z • (1 : 𝒜) - T) (outer T P z) := by
  unfold Commute SemiconjBy
  rw [← sub_eq_zero, outer, sub_outer_identity, commute_sub T P hTP z, mul_zero]

theorem commute_sub_inner (hTP : T * P = P * T) (z : ℂ) :
    Commute (z • (1 : 𝒜) - T) (inner T P z) := by
  unfold Commute SemiconjBy
  rw [← sub_eq_zero, inner, sub_inner_identity, commute_sub T P hTP z, mul_zero]

theorem outer_mul_inner (hP : P * P = P) (hTP : T * P = P * T) (z : ℂ) :
    outer T P z * inner T P z = z • (1 : 𝒜) - T := by
  rw [← sub_eq_zero, outer, inner, outer_inner_identity, hP, sub_self, mul_zero,
    commute_sub T P hTP z, mul_zero, zero_mul, neg_zero, add_zero]

/-- The resolvent denominator is a unit where both the exterior and the interior operators
are units. -/
theorem isUnit_sub (hP : P * P = P) (hTP : T * P = P * T) (z : ℂ)
    (hout : IsUnit (outer T P z)) (hin : IsUnit (inner T P z)) :
    IsUnit (z • (1 : 𝒜) - T) := by
  rw [← outer_mul_inner T P hP hTP z]
  exact hout.mul hin

/-- On the common unit set, the resolvent splits into the exterior and interior parts. -/
theorem resolvent_eq_split (hP : P * P = P) (hTP : T * P = P * T) (z : ℂ)
    (hout : IsUnit (outer T P z)) (hin : IsUnit (inner T P z)) :
    resolvent T z = Ring.inverse (outer T P z) * P + Ring.inverse (inner T P z) * (1 - P) := by
  set A := z • (1 : 𝒜) - T with hAdef
  have hXA : Commute A (Ring.inverse (outer T P z)) := by
    obtain ⟨u, hu⟩ := hout
    have h := commute_sub_outer T P hTP z
    rw [← hu] at h
    rw [← hu, Ring.inverse_unit]
    exact h.units_inv_right
  have hYA : Commute A (Ring.inverse (inner T P z)) := by
    obtain ⟨u, hu⟩ := hin
    have h := commute_sub_inner T P hTP z
    rw [← hu] at h
    rw [← hu, Ring.inverse_unit]
    exact h.units_inv_right
  have hRight : A * (Ring.inverse (outer T P z) * P + Ring.inverse (inner T P z) * (1 - P)) =
      1 := by
    rw [mul_add, ← mul_assoc, ← mul_assoc, hXA.eq, hYA.eq, mul_assoc, mul_assoc,
      ← outer_mul_proj T P hP z, ← inner_mul_compl T P hP z, ← mul_assoc, ← mul_assoc,
      Ring.inverse_mul_cancel _ hout, Ring.inverse_mul_cancel _ hin, one_mul, one_mul,
      add_sub_cancel]
  have h := (Ring.inverse_mul_eq_iff_eq_mul A 1 _ (isUnit_sub T P hP hTP z hout hin)).mpr
    hRight.symm
  rw [mul_one] at h
  exact h

/-- The resolvent commutes with every element commuting with `T`. -/
theorem commute_resolvent (z : ℂ) (a : 𝒜) (ha : Commute a T) : Commute a (resolvent T z) := by
  unfold resolvent
  by_cases hu : IsUnit (z • (1 : 𝒜) - T)
  · obtain ⟨u, hu⟩ := hu
    have h : Commute a (u : 𝒜) := by
      rw [hu]
      exact ((Commute.one_right a).smul_right z).sub_right ha
    rw [← hu, Ring.inverse_unit]
    exact h.units_inv_right
  · rw [Ring.inverse_non_unit _ hu]
    exact Commute.zero_right a

/-- Elements commuting with `T` commute with every polynomial in `T`. -/
theorem commute_aeval (a : 𝒜) (ha : Commute a T) (f : ℂ[X]) : Commute a (aeval T f) := by
  rw [aeval_eq_sum_range]
  exact Commute.sum_right _ _ _ fun n _ => (ha.pow_right n).smul_right _

end Definitions

section Analysis

variable {𝒜 : Type*} [NormedRing 𝒜] [NormedAlgebra ℂ 𝒜] [CompleteSpace 𝒜]

omit [CompleteSpace 𝒜] in
theorem differentiable_outer (T P : 𝒜) : Differentiable ℂ (outer T P) := by
  unfold outer
  exact (((differentiable_id.smul_const (1 : 𝒜)).sub_const T).mul_const P).add_const _

omit [CompleteSpace 𝒜] in
theorem differentiable_inner (T P : 𝒜) : Differentiable ℂ (inner T P) := by
  unfold inner
  exact (((differentiable_id.smul_const (1 : 𝒜)).sub_const T).mul_const (1 - P)).add_const _

theorem differentiableAt_outer_part (T P C : 𝒜) (z : ℂ) (hz : IsUnit (outer T P z)) :
    DifferentiableAt ℂ (fun w => Ring.inverse (outer T P w) * C) z :=
  ((differentiableAt_inverse hz).comp z (differentiable_outer T P z)).mul_const C

theorem differentiableAt_inner_part (T P C : 𝒜) (z : ℂ) (hz : IsUnit (inner T P z)) :
    DifferentiableAt ℂ (fun w => Ring.inverse (inner T P w) * C) z :=
  ((differentiableAt_inverse hz).comp z (differentiable_inner T P z)).mul_const C

theorem differentiableAt_resolvent (T : 𝒜) (z : ℂ) (hz : IsUnit (z • (1 : 𝒜) - T)) :
    DifferentiableAt ℂ (resolvent T) z :=
  (differentiableAt_inverse hz).comp z ((differentiable_id.smul_const (1 : 𝒜)).sub_const T z)

omit [CompleteSpace 𝒜] in
/-- The exterior part satisfies `(z - c) Ψ = P + Ψ N` with `N = (T - c) P`. -/
theorem exterior_identity (T P : 𝒜) (hP : P * P = P) (hTP : T * P = P * T) (c z : ℂ)
    (hz : IsUnit (outer T P z)) :
    (z - c) • (Ring.inverse (outer T P z) * P) =
      P + Ring.inverse (outer T P z) * P * ((T - c • (1 : 𝒜)) * P) := by
  have hsplit : (z • (1 : 𝒜) - T) * P = (z - c) • P - (T - c • (1 : 𝒜)) * P := by
    rw [sub_mul, sub_mul, smul_mul_assoc, one_mul, smul_mul_assoc, one_mul, sub_smul]
    abel
  have hkey : Ring.inverse (outer T P z) * P * ((z • (1 : 𝒜) - T) * P) = P := by
    rw [← outer_mul_proj T P hP z, ← mul_assoc, mul_assoc (Ring.inverse (outer T P z)) P,
      (commute_outer T P hTP z).eq, ← mul_assoc, Ring.inverse_mul_cancel _ hz, one_mul, hP]
  have hΨP : Ring.inverse (outer T P z) * P * P = Ring.inverse (outer T P z) * P := by
    rw [mul_assoc, hP]
  rw [hsplit, mul_sub, mul_smul_comm, hΨP] at hkey
  exact sub_eq_iff_eq_add.mp hkey

omit [CompleteSpace 𝒜] in
/-- Exterior estimate: `‖Ψ(z) - (z - c)⁻¹ P‖ ≤ 2 ‖P‖ ‖N‖ / |z - c|²` once `|z - c| ≥ 2 ‖N‖`. -/
theorem norm_exterior_sub_le (T P : 𝒜) (hP : P * P = P) (hTP : T * P = P * T) (c z : ℂ)
    (hz : IsUnit (outer T P z)) (hzc : 0 < ‖z - c‖)
    (hlarge : 2 * ‖(T - c • (1 : 𝒜)) * P‖ ≤ ‖z - c‖) :
    ‖Ring.inverse (outer T P z) * P - (z - c)⁻¹ • P‖ ≤
      2 * ‖P‖ * ‖(T - c • (1 : 𝒜)) * P‖ / ‖z - c‖ ^ 2 := by
  set Ψ := Ring.inverse (outer T P z) * P
  set N := (T - c • (1 : 𝒜)) * P
  have hid := exterior_identity T P hP hTP c z hz
  have hzc' : z - c ≠ 0 := norm_pos_iff.mp hzc
  have hΨ : ‖Ψ‖ ≤ 2 * ‖P‖ / ‖z - c‖ := by
    have h1 : ‖z - c‖ * ‖Ψ‖ ≤ ‖P‖ + ‖Ψ‖ * ‖N‖ := by
      rw [← norm_smul, hid]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_mul_le _ _))
    rw [le_div_iff₀ hzc]
    nlinarith [norm_nonneg Ψ, norm_nonneg N, norm_nonneg P]
  have hdiff : Ψ - (z - c)⁻¹ • P = (z - c)⁻¹ • (Ψ * N) := by
    have h2 : Ψ = (z - c)⁻¹ • ((z - c) • Ψ) := by rw [smul_smul, inv_mul_cancel₀ hzc', one_smul]
    conv_lhs => rw [h2, hid, smul_add]
    abel
  rw [hdiff, norm_smul, norm_inv]
  calc ‖z - c‖⁻¹ * ‖Ψ * N‖ ≤ ‖z - c‖⁻¹ * (2 * ‖P‖ / ‖z - c‖ * ‖N‖) := by
        gcongr
        exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hΨ (norm_nonneg _))
    _ = 2 * ‖P‖ * ‖N‖ / ‖z - c‖ ^ 2 := by
        field_simp

/-- **Exterior integral.** If the exterior operator is invertible outside the open disk, the
exterior part of the resolvent has circle integral `2πi P`. -/
theorem integral_exterior (T P : 𝒜) (hP : P * P = P) (hTP : T * P = P * T) (c : ℂ) {r : ℝ}
    (hr : 0 < r) (hout : ∀ z : ℂ, r ≤ ‖z - c‖ → IsUnit (outer T P z)) :
    (∮ z in C(c, r), Ring.inverse (outer T P z) * P) = (2 * π * I : ℂ) • P := by
  set Ψ : ℂ → 𝒜 := fun z => Ring.inverse (outer T P z) * P with hΨdef
  set N := (T - c • (1 : 𝒜)) * P
  have hΨd : ∀ z : ℂ, r ≤ ‖z - c‖ → DifferentiableAt ℂ Ψ z := fun z hz =>
    differentiableAt_outer_part T P P z (hout z hz)
  have hrad : ∀ R : ℝ, r ≤ R → (∮ z in C(c, R), Ψ z) = ∮ z in C(c, r), Ψ z := by
    intro R hR
    apply Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hr hR
      Set.countable_empty
    · intro z hz
      have hz' : r ≤ ‖z - c‖ := by
        have := hz.2
        rw [Metric.mem_ball, dist_eq_norm, not_lt] at this
        exact this
      exact (hΨd z hz').continuousAt.continuousWithinAt
    · intro z hz
      have hz' : r ≤ ‖z - c‖ := by
        have := hz.1.2
        rw [Metric.mem_closedBall, dist_eq_norm, not_le] at this
        exact this.le
      exact hΨd z hz'
  set I0 := ∮ z in C(c, r), Ψ z
  set K := 4 * π * (‖P‖ * ‖N‖)
  have hbound : ∀ R : ℝ, r ≤ R → 2 * ‖N‖ ≤ R → ‖I0 - (2 * π * I : ℂ) • P‖ * R ≤ K := by
    intro R hrR hNR
    have hR : 0 < R := hr.trans_le hrR
    have hsphere : ∀ z ∈ sphere c R, r ≤ ‖z - c‖ ∧ ‖z - c‖ = R := by
      intro z hz
      rw [mem_sphere, dist_eq_norm] at hz
      exact ⟨hz ▸ hrR, hz⟩
    have hcont1 : ContinuousOn Ψ (sphere c R) := fun z hz =>
      (hΨd z (hsphere z hz).1).continuousAt.continuousWithinAt
    have hcont2 : ContinuousOn (fun z : ℂ => (z - c)⁻¹ • P) (sphere c R) := by
      intro z hz
      have hne : z - c ≠ 0 := by
        rw [← norm_pos_iff, (hsphere z hz).2]
        exact hR
      exact ((continuousAt_id.sub continuousAt_const).inv₀ hne).smul continuousAt_const
        |>.continuousWithinAt
    have hsplit : I0 = (∮ z in C(c, R), (Ψ z - (z - c)⁻¹ • P)) + (2 * π * I : ℂ) • P := by
      rw [← hrad R hrR, circleIntegral.integral_sub (hcont1.circleIntegrable hR.le)
        (hcont2.circleIntegrable hR.le), circleIntegral.integral_smul_const,
        circleIntegral.integral_sub_center_inv c hR.ne', sub_add_cancel]
    have herr : ‖∮ z in C(c, R), (Ψ z - (z - c)⁻¹ • P)‖ ≤
        2 * π * R * (2 * ‖P‖ * ‖N‖ / R ^ 2) := by
      apply circleIntegral.norm_integral_le_of_norm_le_const hR.le
      intro z hz
      obtain ⟨hrz, hzR⟩ := hsphere z hz
      have h := norm_exterior_sub_le T P hP hTP c z (hout z hrz) (hzR ▸ hR) (hzR ▸ hNR)
      rw [hzR] at h
      exact h
    rw [hsplit, add_sub_cancel_right]
    calc ‖∮ z in C(c, R), (Ψ z - (z - c)⁻¹ • P)‖ * R ≤
          2 * π * R * (2 * ‖P‖ * ‖N‖ / R ^ 2) * R := mul_le_mul_of_nonneg_right herr hR.le
      _ = K := by
          simp only [K]
          field_simp
          ring
  by_contra hne
  have hδ : 0 < ‖I0 - (2 * π * I : ℂ) • P‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set δ := ‖I0 - (2 * π * I : ℂ) • P‖
  set R0 := r + 2 * ‖N‖ + (K + 1) / δ
  have hK : 0 ≤ K := by positivity
  have h := hbound R0 (by have : 0 ≤ 2 * ‖N‖ + (K + 1) / δ := by positivity
                          linarith)
    (by have : 0 ≤ r + (K + 1) / δ := by positivity
        linarith)
  have : δ * R0 = δ * (r + 2 * ‖N‖) + (K + 1) := by
    simp only [R0]
    field_simp
  nlinarith [mul_nonneg hδ.le (show 0 ≤ r + 2 * ‖N‖ by positivity)]

/-- **Interior integral.** If the interior operator is invertible on the closed disk, the
interior part of the resolvent has circle integral zero. -/
theorem integral_interior (T P : 𝒜) (c : ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hin : ∀ z : ℂ, ‖z - c‖ ≤ r → IsUnit (inner T P z)) :
    (∮ z in C(c, r), Ring.inverse (inner T P z) * (1 - P)) = 0 := by
  have hmem : ∀ z ∈ closedBall c r, IsUnit (inner T P z) := fun z hz =>
    hin z (by rwa [Metric.mem_closedBall, dist_eq_norm] at hz)
  apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr Set.countable_empty
  · intro z hz
    exact (differentiableAt_inner_part T P (1 - P) z (hmem z hz)).continuousAt.continuousWithinAt
  · intro z hz
    exact differentiableAt_inner_part T P (1 - P) z (hmem z (Metric.ball_subset_closedBall hz.1))

/-- **Riesz projection.** The resolvent integral over the circle is the idempotent `P`. -/
theorem riesz (T P : 𝒜) (hP : P * P = P) (hTP : T * P = P * T) (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hout : ∀ z : ℂ, r ≤ ‖z - c‖ → IsUnit (outer T P z))
    (hin : ∀ z : ℂ, ‖z - c‖ ≤ r → IsUnit (inner T P z)) :
    (2 * π * I : ℂ)⁻¹ • (∮ z in C(c, r), resolvent T z) = P := by
  have hsphere : ∀ z ∈ sphere c r, ‖z - c‖ = r := fun z hz => by
    rwa [mem_sphere, dist_eq_norm] at hz
  have hEq : Set.EqOn (resolvent T)
      (fun z => Ring.inverse (outer T P z) * P + Ring.inverse (inner T P z) * (1 - P))
      (sphere c r) := fun z hz =>
    resolvent_eq_split T P hP hTP z (hout z (hsphere z hz).ge) (hin z (hsphere z hz).le)
  have hc1 : ContinuousOn (fun z => Ring.inverse (outer T P z) * P) (sphere c r) := fun z hz =>
    (differentiableAt_outer_part T P P z (hout z (hsphere z hz).ge)).continuousAt.continuousWithinAt
  have hc2 : ContinuousOn (fun z => Ring.inverse (inner T P z) * (1 - P)) (sphere c r) :=
    fun z hz => (differentiableAt_inner_part T P (1 - P) z
      (hin z (hsphere z hz).le)).continuousAt.continuousWithinAt
  rw [circleIntegral.integral_congr hr.le hEq, circleIntegral.integral_add
    (hc1.circleIntegrable hr.le) (hc2.circleIntegrable hr.le),
    integral_exterior T P hP hTP c hr hout, integral_interior T P c hr.le hin, add_zero, smul_smul,
    inv_mul_cancel₀ (by simp [Real.pi_ne_zero, I_ne_zero]), one_smul]

/-- Continuous linear maps commute with circle integrals of circle-integrable functions. -/
theorem circleIntegral_comp_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {R : ℝ} (hf : CircleIntegrable f c R) :
    (∮ z in C(c, R), L (f z)) = L (∮ z in C(c, R), f z) := by
  simp only [circleIntegral, ← L.map_smul]
  exact L.intervalIntegral_comp_comm hf.out

/-- The polynomial part `G(z) = ∑ₙ aₙ ∑_{i<n} zⁱ Tⁿ⁻¹⁻ⁱ` of `f(z) - f(T) = (z - T) G(z)`. -/
def quotient (T : 𝒜) (f : ℂ[X]) (z : ℂ) : 𝒜 :=
  ∑ n ∈ Finset.range (f.natDegree + 1),
    f.coeff n • ∑ i ∈ Finset.range n, z ^ i • T ^ (n - 1 - i)

omit [CompleteSpace 𝒜] in
theorem differentiable_quotient (T : 𝒜) (f : ℂ[X]) : Differentiable ℂ (quotient T f) := by
  unfold quotient
  fun_prop

omit [CompleteSpace 𝒜] in
theorem sub_mul_quotient (T : 𝒜) (f : ℂ[X]) (z : ℂ) :
    (z • (1 : 𝒜) - T) * quotient T f z = f.eval z • (1 : 𝒜) - aeval T f := by
  have hc : Commute (z • (1 : 𝒜)) T := (Commute.one_left T).smul_left z
  have hpow (i : ℕ) : (z • (1 : 𝒜)) ^ i = z ^ i • (1 : 𝒜) := by
    rw [smul_pow, one_pow]
  unfold quotient
  rw [Finset.mul_sum, eval_eq_sum_range, aeval_eq_sum_range, Finset.sum_smul,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [mul_smul_comm, mul_smul, ← smul_sub]
  congr 1
  have h := hc.mul_geom_sum₂ n
  simp only [hpow, smul_mul_assoc, one_mul] at h
  rw [h]

/-- **Dunford formula** for polynomials: `(2πi)⁻¹ ∮ f(z) (z - T)⁻¹ dz = f(T) P`. -/
theorem dunford (T P : 𝒜) (hP : P * P = P) (hTP : T * P = P * T) (c : ℂ) {r : ℝ} (hr : 0 < r)
    (hout : ∀ z : ℂ, r ≤ ‖z - c‖ → IsUnit (outer T P z))
    (hin : ∀ z : ℂ, ‖z - c‖ ≤ r → IsUnit (inner T P z)) (f : ℂ[X]) :
    (2 * π * I : ℂ)⁻¹ • (∮ z in C(c, r), f.eval z • resolvent T z) = aeval T f * P := by
  have hsphere : ∀ z ∈ sphere c r, ‖z - c‖ = r := fun z hz => by
    rwa [mem_sphere, dist_eq_norm] at hz
  have hunit : ∀ z ∈ sphere c r, IsUnit (z • (1 : 𝒜) - T) := fun z hz =>
    isUnit_sub T P hP hTP z (hout z (hsphere z hz).ge) (hin z (hsphere z hz).le)
  have hEq : Set.EqOn (fun z => f.eval z • resolvent T z)
      (fun z => aeval T f * resolvent T z + quotient T f z) (sphere c r) := by
    intro z hz
    have hcomm : Commute (aeval T f) (resolvent T z) :=
      (commute_resolvent T z (aeval T f) (commute_aeval T T (Commute.refl T) f).symm)
    have hRA : resolvent T z * (z • (1 : 𝒜) - T) = 1 :=
      Ring.inverse_mul_cancel _ (hunit z hz)
    have h := congrArg (fun x => resolvent T z * x) (sub_mul_quotient T f z)
    simp only [← mul_assoc, hRA, one_mul] at h
    rw [mul_sub, mul_smul_comm, mul_one, ← hcomm.eq] at h
    simp only
    rw [h]
    abel
  have hcR : ContinuousOn (resolvent T) (sphere c r) := fun z hz =>
    (differentiableAt_resolvent T z (hunit z hz)).continuousAt.continuousWithinAt
  have hint1 : CircleIntegrable (fun z => aeval T f * resolvent T z) c r :=
    (continuousOn_const.mul hcR).circleIntegrable hr.le
  have hint2 : CircleIntegrable (quotient T f) c r :=
    (differentiable_quotient T f).continuous.continuousOn.circleIntegrable hr.le
  have hzero : (∮ z in C(c, r), quotient T f z) = 0 :=
    ((differentiable_quotient T f).diffContOnCl).circleIntegral_eq_zero hr.le
  have hmul : (∮ z in C(c, r), aeval T f * resolvent T z) =
      aeval T f * ∮ z in C(c, r), resolvent T z :=
    circleIntegral_comp_clm (ContinuousLinearMap.mul ℂ 𝒜 (aeval T f))
      (hcR.circleIntegrable hr.le)
  rw [circleIntegral.integral_congr hr.le hEq, circleIntegral.integral_add hint1 hint2, hzero,
    add_zero, hmul, ← mul_smul_comm, riesz T P hP hTP c hr hout hin]

/-- The Riesz projection is bounded by the radius times the resolvent bound on the circle. -/
theorem norm_proj_le (T P : 𝒜) (hP : P * P = P) (hTP : T * P = P * T) (c : ℂ) {r M : ℝ}
    (hr : 0 < r) (hout : ∀ z : ℂ, r ≤ ‖z - c‖ → IsUnit (outer T P z))
    (hin : ∀ z : ℂ, ‖z - c‖ ≤ r → IsUnit (inner T P z))
    (hM : ∀ z ∈ sphere c r, ‖resolvent T z‖ ≤ M) : ‖P‖ ≤ r * M := by
  rw [← riesz T P hP hTP c hr hout hin]
  exact circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le hM

/-- **Isolated filter bound.** `‖f(T) P‖ ≤ r F M` when `|f| ≤ F` and `‖(z - T)⁻¹‖ ≤ M` on the
circle. -/
theorem norm_aeval_mul_le (T P : 𝒜) (hP : P * P = P) (hTP : T * P = P * T) (c : ℂ) {r M F : ℝ}
    (hr : 0 < r) (hout : ∀ z : ℂ, r ≤ ‖z - c‖ → IsUnit (outer T P z))
    (hin : ∀ z : ℂ, ‖z - c‖ ≤ r → IsUnit (inner T P z)) (f : ℂ[X])
    (hF : ∀ z ∈ sphere c r, ‖f.eval z‖ ≤ F)
    (hM : ∀ z ∈ sphere c r, ‖resolvent T z‖ ≤ M) : ‖aeval T f * P‖ ≤ r * (F * M) := by
  rw [← dunford T P hP hTP c hr hout hin f]
  apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le
  intro z hz
  rw [norm_smul]
  exact mul_le_mul (hF z hz) (hM z hz) (norm_nonneg _) ((norm_nonneg _).trans (hF z hz))

end Analysis

end

end LargeSparsityCore.Riesz
