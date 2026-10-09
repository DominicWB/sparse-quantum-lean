import SparseLowerBounds.Query.Joint

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Pythagoras for a resolution of the identity by star projections

Helper for `SparseLowerBounds.Query.Adversary`. If `R` and `P i` are star
projections with `R + Σ_i P i = 1`, then `‖x‖² = ‖R x‖² + Σ_i ‖P i x‖²`. If in
addition they are pairwise orthogonal, then
`‖R a + Σ_i P i (b i)‖² = ‖R a‖² + Σ_i ‖P i (b i)‖²`.
-/

namespace SparseLowerBounds.Helpers.Adversary

noncomputable section
open scoped InnerProductSpace

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- For a star projection `Q`, `re ⟪x, Q x⟫ = ‖Q x‖²`. -/
theorem re_inner_apply_self_of_isStarProjection {Q : K →L[ℂ] K} (hQ : IsStarProjection Q)
    (x : K) : RCLike.re ⟪x, Q x⟫_ℂ = ‖Q x‖ ^ 2 := by
  have hidem : Q (Q x) = Q x := by
    have h := hQ.isIdempotentElem
    exact congrArg (fun T : K →L[ℂ] K => T x) h
  have hadj : ContinuousLinearMap.adjoint Q = Q := by
    rw [← ContinuousLinearMap.star_eq_adjoint]; exact hQ.isSelfAdjoint
  have h1 : ⟪x, Q x⟫_ℂ = ⟪Q x, Q x⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hadj, hidem]
  rw [h1, inner_self_eq_norm_sq]

/-- A resolution of the identity by star projections splits the squared norm. -/
theorem norm_sq_eq_add_sum {I : Type*} [Fintype I] (R : K →L[ℂ] K) (P : I → K →L[ℂ] K)
    (hR : IsStarProjection R) (hP : ∀ i, IsStarProjection (P i))
    (hsum : R + ∑ i, P i = 1) (x : K) :
    ‖x‖ ^ 2 = ‖R x‖ ^ 2 + ∑ i, ‖P i x‖ ^ 2 := by
  have hx : x = R x + ∑ i, P i x := by
    have h := congrArg (fun T : K →L[ℂ] K => T x) hsum
    simp only [add_apply, sum_apply,
      one_apply_eq_self] at h
    exact h.symm
  have hs : ∑ i, ‖P i x‖ ^ 2 = RCLike.re ⟪x, ∑ i, P i x⟫_ℂ := by
    rw [inner_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => (re_inner_apply_self_of_isStarProjection (hP i) x).symm
  rw [hs, ← re_inner_apply_self_of_isStarProjection hR x, ← map_add, ← inner_add_right, ← hx,
    inner_self_eq_norm_sq]

/-- For pairwise orthogonal star projections resolving the identity, the squared
norm of `R a + Σ_i P i (b i)` is the sum of the squared norms of its pieces. -/
theorem norm_sq_add_sum_apply {I : Type*} [Fintype I] [DecidableEq I] (R : K →L[ℂ] K)
    (P : I → K →L[ℂ] K) (hR : IsStarProjection R) (hP : ∀ i, IsStarProjection (P i))
    (hsum : R + ∑ i, P i = 1) (hRP : ∀ i, R * P i = 0) (hPR : ∀ i, P i * R = 0)
    (hPP : ∀ i i', i ≠ i' → P i * P i' = 0) (a : K) (b : I → K) :
    ‖R a + ∑ i, P i (b i)‖ ^ 2 = ‖R a‖ ^ 2 + ∑ i, ‖P i (b i)‖ ^ 2 := by
  have app : ∀ (S T : K →L[ℂ] K) (v : K), S (T v) = (S * T) v := fun _ _ _ => rfl
  have hRx : R (R a + ∑ i, P i (b i)) = R a := by
    rw [map_add, map_sum, app, hR.isIdempotentElem.eq]
    simp [app, hRP]
  have hPx : ∀ i, P i (R a + ∑ i', P i' (b i')) = P i (b i) := by
    intro i
    rw [map_add, map_sum, app, hPR, zero_apply, zero_add,
      Finset.sum_eq_single i]
    · rw [app, (hP i).isIdempotentElem.eq]
    · intro i' _ hne
      rw [app, hPP i i' (Ne.symm hne), zero_apply]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [norm_sq_eq_add_sum R P hR hP hsum, hRx]
  simp_rw [hPx]

end

end SparseLowerBounds.Helpers.Adversary
end
