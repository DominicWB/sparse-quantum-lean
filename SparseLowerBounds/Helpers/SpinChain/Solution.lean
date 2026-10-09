import SparseLowerBounds.Helpers.SpinChain.PathSum

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Derivative of a trigonometric monomial

Helper module of group spin-chain (`SparseLowerBounds.Hamiltonian.SpinChain`):
the components `C cos(θ)^p (-i sin θ)^q` of the explicit spin-chain solution,
differentiated along a real curve `θ(t)`.
-/

namespace SparseLowerBounds.Helpers.SpinChain

/-- `d/dt [C cos(θ)^p (-i sin θ)^q] = C θ' (-i) [p cos^{p-1} (-i sin)^{q+1} + q cos^{p+1} (-i sin)^{q-1}]`. -/
theorem hasDerivAt_trigMonomial {θ : ℝ → ℝ} {θ' t : ℝ} (hθ : HasDerivAt θ θ' t) (C : ℝ)
    (p q : ℕ) :
    HasDerivAt (fun u : ℝ => (C : ℂ) * ((Real.cos (θ u) : ℝ) : ℂ) ^ p *
        (-Complex.I * ((Real.sin (θ u) : ℝ) : ℂ)) ^ q)
      ((C : ℂ) * (θ' : ℂ) * (-Complex.I) *
        ((p : ℂ) * ((Real.cos (θ t) : ℝ) : ℂ) ^ (p - 1) *
            (-Complex.I * ((Real.sin (θ t) : ℝ) : ℂ)) ^ (q + 1) +
          (q : ℂ) * ((Real.cos (θ t) : ℝ) : ℂ) ^ (p + 1) *
            (-Complex.I * ((Real.sin (θ t) : ℝ) : ℂ)) ^ (q - 1))) t := by
  have hc : HasDerivAt (fun u => ((Real.cos (θ u) : ℝ) : ℂ)) ((-Real.sin (θ t) * θ' : ℝ) : ℂ) t :=
    ((Real.hasDerivAt_cos (θ t)).comp t hθ).ofReal_comp
  have hs : HasDerivAt (fun u => ((Real.sin (θ u) : ℝ) : ℂ)) ((Real.cos (θ t) * θ' : ℝ) : ℂ) t :=
    ((Real.hasDerivAt_sin (θ t)).comp t hθ).ofReal_comp
  have h := ((hc.fun_pow p).const_mul (C : ℂ)).mul ((hs.const_mul (-Complex.I)).fun_pow q)
  refine h.congr_deriv ?_
  simp only [Complex.ofReal_mul, Complex.ofReal_neg]
  set c : ℂ := ((Real.cos (θ t) : ℝ) : ℂ)
  set s : ℂ := ((Real.sin (θ t) : ℝ) : ℂ)
  rw [pow_succ _ q, pow_succ _ p]
  rcases q with _ | q
  · simp only [pow_zero, Nat.cast_zero, zero_mul, add_zero, mul_zero, one_mul, mul_one]
    linear_combination (-(↑C * ↑θ' * ↑p * c ^ (p - 1) * s)) * Complex.I_sq
  · rw [Nat.add_sub_cancel, pow_succ _ q]
    push_cast
    linear_combination
      (-(↑C * ↑θ' * ↑p * c ^ (p - 1) * (-Complex.I * s) ^ q * (-Complex.I * s) * s)) * Complex.I_sq

end SparseLowerBounds.Helpers.SpinChain
end
