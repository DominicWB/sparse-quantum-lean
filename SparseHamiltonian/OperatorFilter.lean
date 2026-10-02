import SparseHamiltonian.GlobalResolventContinuation2

/-!
# Inverse-power bounds from the resolvent disk

A Cauchy estimate on the small spectrum-free disk bounds powers of the inverse
at one. Combining these estimates with the finite geometric identity will give
exponential decay of the averaging filter without an indented contour.
All norms here are Banach-algebra norms; in the application they are genuine
operator norms on the private Hilbert space.
-/

namespace SparseHamiltonian.OperatorFilter

open scoped Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The inverse generating function has the expected operator-valued Taylor
coefficients, with no commutativity assumption on the ambient algebra. -/
theorem inverse_generating_derivative (R : A) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => Ring.inverse (1 - z • R) * R) 0 =
      n.factorial • R ^ (n + 1) := by
  let g : A →L[ℂ] A := (ContinuousLinearMap.mul ℂ A).flip R
  have h := g.comp_hasFPowerSeriesOnBall
    (spectrum.hasFPowerSeriesOnBall_inverse_one_sub_smul ℂ R)
  have hd := h.factorial_smul (1 : ℂ) n
  simpa [iteratedDeriv_eq_iteratedFDeriv, g,
    ContinuousLinearMap.compFormalMultilinearSeries_apply,
    ContinuousMultilinearMap.mkPiRing_apply, Function.comp_def, pow_succ] using hd.symm

/-- Cauchy's derivative bound controls powers of the inverse through the
bounded generating function on a disk. -/
theorem inverse_power_norm_le (R : A) (r M : ℝ) (hr : 0 < r)
    (hu : ∀ z : ℂ, ‖z‖ ≤ r → IsUnit (1 - z • R))
    (hb : ∀ z : ℂ, ‖z‖ ≤ r → ‖Ring.inverse (1 - z • R) * R‖ ≤ M)
    (n : ℕ) : ‖R ^ (n + 1)‖ ≤ M / r ^ n := by
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
    (fun z hz => hb z (by simpa using (Metric.sphere_subset_closedBall hz)))
  rw [inverse_generating_derivative] at hbound
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  rw [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul] at hbound
  apply (mul_le_mul_iff_right₀ hn).mp
  simpa [mul_div_assoc] using hbound

omit [CompleteSpace A] in
/-- The usual resolvent disk gives the hypotheses for the inverse generating
function after replacing the spectral parameter by `1-z`. -/
theorem shifted_inverse_identification (D R S : A) (z : ℂ)
    (hleft : (1 - D) * R = 1) (hright : R * (1 - D) = 1)
    (hSleft : (((1 - z) • (1 : A)) - D) * S = 1)
    (hSright : S * (((1 - z) • (1 : A)) - D) = 1) :
    IsUnit (1 - z • R) ∧ Ring.inverse (1 - z • R) * R = S := by
  let Az : A := (1 - z) • (1 : A) - D
  have huAz : IsUnit Az := ⟨⟨Az, S, hSleft, hSright⟩, rfl⟩
  have huR : IsUnit R := ⟨⟨R, 1 - D, hright, hleft⟩, rfl⟩
  have hfactor : Az * R = 1 - z • R := by
    calc
      Az * R = (1 - D) * R - z • R := by
        simp only [Az, sub_smul, one_smul, sub_mul, smul_mul_assoc, one_mul]
        abel
      _ = 1 - z • R := by rw [hleft]
  have hfactor' : R * Az = 1 - z • R := by
    calc
      R * Az = R * (1 - D) - z • R := by
        simp only [Az, sub_smul, one_smul, mul_sub, mul_smul_comm, mul_one]
        abel
      _ = 1 - z • R := by rw [hright]
  have hu : IsUnit (1 - z • R) := hfactor ▸ huAz.mul huR
  refine ⟨hu, (Ring.inverse_mul_eq_iff_eq_mul _ _ _ hu).mpr ?_⟩
  rw [← hfactor', mul_assoc]
  exact (mul_one R).symm.trans (congrArg (R * ·) hSleft).symm

/-- A uniform bound for the actual resolvent on a disk around one bounds every
positive power of its central inverse. No normality assumption is needed. -/
theorem inverse_power_norm_le_of_resolvent_disk (D R : A) (r M : ℝ) (hr : 0 < r)
    (hleft : (1 - D) * R = 1) (hright : R * (1 - D) = 1)
    (hdisk : ∀ z : ℂ, ‖z - 1‖ ≤ r → ∃ S : A,
      (z • (1 : A) - D) * S = 1 ∧ S * (z • (1 : A) - D) = 1 ∧ ‖S‖ ≤ M)
    (n : ℕ) : ‖R ^ (n + 1)‖ ≤ M / r ^ n := by
  have hgen (z : ℂ) (hz : ‖z‖ ≤ r) :
      IsUnit (1 - z • R) ∧ ‖Ring.inverse (1 - z • R) * R‖ ≤ M := by
    have hz' : ‖(1 - z) - 1‖ ≤ r := by simpa [sub_sub_cancel_left] using hz
    obtain ⟨S, hSleft, hSright, hSnorm⟩ := hdisk (1 - z) hz'
    obtain ⟨hu, heq⟩ := shifted_inverse_identification D R S z hleft hright hSleft hSright
    exact ⟨hu, heq ▸ hSnorm⟩
  exact inverse_power_norm_le R r M hr (fun z hz => (hgen z hz).1)
    (fun z hz => (hgen z hz).2) n

end SparseHamiltonian.OperatorFilter
