import GateEfficientQuadrature.Paper

/-!
# The constants of the left-endpoint quadrature are attained

For the zero generator (accretive, `Λ = 0`) and the ramp `b(t) = t w` (Lipschitz constant
`‖w‖`, `ramp_lipschitz`), with the exact samples `b(q T / n)` and the constant homogeneous
solutions (`const_homog`), every hypothesis of `cert_left` and `mass_left` holds with `Λ = 0`,
`L = ‖w‖` and `δ = 0`, and both bounds are attained: the certificate error of the left-endpoint
quadrature with `n` nodes is exactly `‖w‖ T² / (2n)` (`sharp_cert`) and
`|B_n - B| = ‖w‖ T² / (2n)` (`sharp_mass`). So the bound `T² L_b / (2m)` of the proof of Theorem
`ode:thm:gates` cannot be improved, and neither can `T² C_b / (2m)` for a zero generator
(`Λ = 0`); whether the coefficient of `Λ b_*` is sharp is not addressed here.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateQuad

noncomputable section
open Set
open TimeDependentODE (SolvesODE Accretive)
open scoped InnerProduct BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem sum_range_cast (n : ℕ) : ∑ q ∈ Finset.range n, (q : ℝ) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- The ramp `b(t) = t w`. -/
def ramp (w : V) (t : ℝ) : V := ((t : ℝ) : ℂ) • w

/-- The solution `x(t) = x₀ + (t² / 2) w` of `x' = t w` (zero generator). -/
def rampSol (x0 w : V) (t : ℝ) : V := x0 + ((t ^ 2 / 2 : ℝ) : ℂ) • w

theorem rampSol_solves (x0 w : V) (T : ℝ) :
    SolvesODE (fun _ => 0) (ramp w) (rampSol x0 w) 0 T := by
  intro u _
  have h1 : HasDerivAt (fun t : ℝ => ((t ^ 2 / 2 : ℝ) : ℂ)) ((u : ℝ) : ℂ) u :=
    (((hasDerivAt_pow 2 u).div_const 2).ofReal_comp).congr_deriv (by norm_num)
  have h2 := ((h1.smul_const w).const_add x0).hasDerivWithinAt (s := Icc 0 T)
  refine h2.congr_deriv ?_
  simp [ramp]

theorem ramp_lipschitz (w : V) (u u' : ℝ) : ‖ramp w u - ramp w u'‖ = ‖w‖ * |u - u'| := by
  unfold ramp
  rw [← sub_smul, ← Complex.ofReal_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_comm]

/-- Constants solve the homogeneous equation of the zero generator. -/
theorem const_homog (z : V) (a c : ℝ) :
    SolvesODE (fun _ => (0 : V →L[ℂ] V)) (fun _ => 0) (fun _ => z) a c := by
  intro u _
  exact (hasDerivWithinAt_const _ _ _).congr_deriv (by simp)

/-- **The certificate bound is attained.** For the zero generator, the ramp `b(t) = t w`, the
exact samples and the constant homogeneous solutions, the certificate error of the
left-endpoint quadrature with `n` nodes is `‖w‖ T² / (2n)`, the bound of `cert_left` for
`Λ = 0`, `L = ‖w‖`, `δ = 0`. -/
theorem sharp_cert (T : ℝ) {n : ℕ} (hn : 0 < n) (x0 w : V) :
    ‖rampSol x0 w T - x0 - ∑ q ∈ Finset.range n, ((T / n : ℝ) : ℂ) • ramp w (q * T / n)‖ =
      ‖w‖ * T ^ 2 / (2 * n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcoef : ∑ q ∈ Finset.range n, T / n * ((q : ℝ) * T / n) = T ^ 2 * (n - 1) / (2 * n) := by
    have h1 : ∑ q ∈ Finset.range n, T / n * ((q : ℝ) * T / n) =
        (T / n) ^ 2 * ∑ q ∈ Finset.range n, (q : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    rw [h1, sum_range_cast]
    field_simp
  have hsum : ∑ q ∈ Finset.range n, ((T / n : ℝ) : ℂ) • ramp w (q * T / n) =
      ((T ^ 2 * (n - 1) / (2 * n) : ℝ) : ℂ) • w := by
    unfold ramp
    simp_rw [smul_smul, ← Complex.ofReal_mul]
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, hcoef]
  rw [hsum]
  unfold rampSol
  have e : x0 + ((T ^ 2 / 2 : ℝ) : ℂ) • w - x0 - ((T ^ 2 * (n - 1) / (2 * n) : ℝ) : ℂ) • w =
      ((T ^ 2 / (2 * n) : ℝ) : ℂ) • w := by
    rw [add_sub_cancel_left, ← sub_smul, ← Complex.ofReal_sub]
    congr 2
    field_simp
    ring
  rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  ring

/-- **The mass bound is attained.** For the ramp `b(t) = t w` and the exact samples,
`|B_n - B| = ‖w‖ T² / (2n)`, the bound of `mass_left` for `L = ‖w‖`, `δ = 0`. -/
theorem sharp_mass {T : ℝ} {n : ℕ} (hT : 0 ≤ T) (hn : 0 < n) (x0 w : V) :
    |quadMass x0 (fun q => ramp w (q * T / n)) T n - contMass x0 (ramp w) T| =
      ‖w‖ * T ^ 2 / (2 * n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold quadMass contMass
  have hint : ∫ u in (0 : ℝ)..T, ‖ramp w u‖ = ‖w‖ * T ^ 2 / 2 := by
    have hEq : EqOn (fun u => ‖ramp w u‖) (fun u => u * ‖w‖) (uIcc 0 T) := by
      intro u hu
      rw [uIcc_of_le hT] at hu
      simp only [ramp, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
    rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_mul_const, integral_id]
    ring
  have hq : ∑ q ∈ Finset.range n, T / n * ‖ramp w (q * T / n)‖ =
      ‖w‖ * T ^ 2 * (n - 1) / (2 * n) := by
    have h1 : ∀ q ∈ Finset.range n, T / n * ‖ramp w (q * T / n)‖ =
        (T / n) ^ 2 * ‖w‖ * q := by
      intro q _
      have hq0 : (0 : ℝ) ≤ q * T / n := by positivity
      simp only [ramp, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, sum_range_cast]
    field_simp
  rw [hint, hq]
  have e : ‖x0‖ + ‖w‖ * T ^ 2 * (n - 1) / (2 * n) - (‖x0‖ + ‖w‖ * T ^ 2 / 2) =
      -(‖w‖ * T ^ 2 / (2 * n)) := by
    field_simp
    ring
  rw [e, abs_neg, abs_of_nonneg (by positivity)]

end

end SparseHamiltonian.GateQuad
