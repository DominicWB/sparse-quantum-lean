import ODELowerBoundExtensions.Homogeneous.Defs

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false
-- The flag-extended joint index exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-!
# Proposition `odel:rem:homogeneous`: the final state, its norm and `g`

Manuscript: the proof of Proposition `odel:rem:homogeneous`. After the hidden stages the flag-one
coefficient of candidate `a` is `(-i)^n σ_a` (`exp_candPhase_final`); the merged pulse multiplies it
by `e^{i((n+2) mod 4)π/2} = -i^n`, giving `-σ_a`; the `Y` rotation by `π/4` sends `(1, -σ_a)/√(2M)`
to `((1+σ_a), (1-σ_a))/(2√M)`, so even candidates (`σ_a = 1`) end with flag zero and the odd
candidate `a_*` with flag one (Proposition `odel:rem:homogeneous`); the dissipation multiplies flag
zero by `e^{-d} = 1/(4√M)`. Hence (`homSol_of_busy_le`)
`x(T) = M^{-1/2} (e^{-d} Σ_{a ≠ a_*} |0, a, ω⟩ + |1, a_*, ω⟩)` (`homEnd`), and

* `‖x(T)‖² = (1 + (M-1)e^{-2d})/M` (`norm_sq_homEnd`, Proposition `odel:rem:homogeneous`);
* with `B = ‖x₀‖ = 1` (`norm_homInit`), `(4/√17)√M ≤ g ≤ √M` (`homEnd_g_bounds`, Proposition
  `odel:rem:homogeneous`);
* the normalised solution has probability at least `16/17` on `a_*` (`homEnd_prob_ge`,
  Proposition `odel:rem:homogeneous`);
* the half indicator has ideal signed correlation at least `2·(16/17) - 1 = 15/17` with
  `halfSign(a_*)` (`homEnd_ideal_corr` in `ODELowerBoundExtensions.Homogeneous.Readout`;
  equivalently decision success `(2/3)(16/17 - ε) + 1/6`).

The computations go through `flagComb`, the combination `Σ_a (p_a |0,a,ω⟩ + q_a |1,a,ω⟩)`
of the orthonormal candidate states; the final state is the combination with the real
coefficients `endP`, `endQ`.
-/

namespace ODELowerBoundExtensions.Homogeneous

noncomputable section
open SparseLowerBounds SparseLowerBounds.ODE SparseHamiltonian
open scoped InnerProductSpace

variable {M n μ s : ℕ}

/-! ### Candidate states and their combinations -/

/-- The inner product of two candidate states reduces to the joint candidate states. -/
theorem inner_flagCand_eq (f f' : Bool) (a a' : Fin M) :
    ⟪flagCand M μ s f a, flagCand M μ s f' a'⟫_ℂ =
      if f = f' then ⟪candState M μ s a, candState M μ s a'⟫_ℂ else 0 := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, Fintype.sum_bool]
  cases f <;> cases f' <;> simp [flagCand_apply, PiLp.inner_apply]

/-- The candidate states are orthonormal. -/
theorem inner_flagCand (f f' : Bool) (a a' : Fin M) :
    ⟪flagCand M μ s f a, flagCand M μ s f' a'⟫_ℂ = if f = f' ∧ a = a' then 1 else 0 := by
  rw [inner_flagCand_eq, inner_candState]
  by_cases hf : f = f' <;> by_cases ha : a = a' <;> simp [hf, ha]

/-- `‖|f, a, ω⟩‖ = 1`. -/
theorem norm_flagCand (f : Bool) (a : Fin M) : ‖flagCand M μ s f a‖ = 1 := by
  have h : ‖flagCand M μ s f a‖ ^ 2 = 1 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_flagCand]; simp
  rw [← Real.sqrt_sq (norm_nonneg _), h, Real.sqrt_one]

/-- A combination `Σ_a (p_a |0, a, ω⟩ + q_a |1, a, ω⟩)` of the candidate states. -/
def flagComb (M μ s : ℕ) (p q : Fin M → ℂ) : EuclideanSpace ℂ (HomIndex M μ s) :=
  ∑ a, (p a • flagCand M μ s false a + q a • flagCand M μ s true a)

/-- The coefficients of a combination: `⟨f, b, ω | Σ_a (p_a |0,a,ω⟩ + q_a |1,a,ω⟩)⟩`. -/
theorem inner_flagCand_flagComb (f : Bool) (b : Fin M) (p q : Fin M → ℂ) :
    ⟪flagCand M μ s f b, flagComb M μ s p q⟫_ℂ = if f then q b else p b := by
  simp only [flagComb, inner_sum, inner_add_right, inner_smul_right, inner_flagCand]
  cases f <;> simp

/-- Inner product of two combinations of candidate states. -/
theorem inner_flagComb (p q p' q' : Fin M → ℂ) :
    ⟪flagComb M μ s p q, flagComb M μ s p' q'⟫_ℂ =
      ∑ a, (starRingEnd ℂ (p a) * p' a + starRingEnd ℂ (q a) * q' a) := by
  conv_lhs => rw [flagComb]
  simp only [sum_inner, inner_add_left, inner_smul_left, inner_flagCand_flagComb]
  simp

/-- Inner product of two combinations with real coefficients. -/
theorem inner_flagComb_ofReal (p q p' q' : Fin M → ℝ) :
    ⟪flagComb M μ s (fun a => (p a : ℂ)) (fun a => (q a : ℂ)),
      flagComb M μ s (fun a => (p' a : ℂ)) (fun a => (q' a : ℂ))⟫_ℂ =
      ((∑ a, (p a * p' a + q a * q' a) : ℝ) : ℂ) := by
  rw [inner_flagComb]; push_cast; simp [Complex.conj_ofReal]

/-- A real multiple of a combination with real coefficients. -/
theorem smul_flagComb_ofReal (c : ℝ) (p q : Fin M → ℝ) :
    (c : ℂ) • flagComb M μ s (fun a => (p a : ℂ)) (fun a => (q a : ℂ)) =
      flagComb M μ s (fun a => ((c * p a : ℝ) : ℂ)) (fun a => ((c * q a : ℝ) : ℂ)) := by
  simp only [flagComb, Finset.smul_sum, smul_add, smul_smul, Complex.ofReal_mul]

/-- A complex multiple of a combination. -/
theorem smul_flagComb (c : ℂ) (p q : Fin M → ℂ) :
    c • flagComb M μ s p q = flagComb M μ s (fun a => c * p a) (fun a => c * q a) := by
  simp only [flagComb, Finset.smul_sum, smul_add, smul_smul]

/-! ### The final state as a combination -/

/-- The flag-zero coefficients of `x(T)`: `0` at `b`, `M^{-1/2} e^{-d}` elsewhere. -/
def endP (M : ℕ) (b a : Fin M) : ℝ :=
  if a = b then 0 else (Real.sqrt M)⁻¹ * (4 * Real.sqrt M)⁻¹

/-- The flag-one coefficients of `x(T)`: `M^{-1/2}` at `b`, `0` elsewhere. -/
def endQ (M : ℕ) (b a : Fin M) : ℝ :=
  if a = b then (Real.sqrt M)⁻¹ else 0

/-- `homEnd` as a combination with the real coefficients `endP`, `endQ`. -/
theorem homEnd_eq_flagComb (b : Fin M) :
    homEnd M μ s b =
      flagComb M μ s (fun a => (endP M b a : ℂ)) (fun a => (endQ M b a : ℂ)) := by
  have h1 : ∑ a, (endP M b a : ℂ) • flagCand M μ s false a =
      (((Real.sqrt M : ℂ))⁻¹ * (((4 * Real.sqrt M)⁻¹ : ℝ) : ℂ)) •
        ∑ a ∈ Finset.univ.erase b, flagCand M μ s false a := by
    rw [Finset.smul_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ b)]
    rw [show endP M b b = 0 from if_pos rfl, Complex.ofReal_zero, zero_smul, add_zero]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [endP, if_neg (Finset.ne_of_mem_erase ha)]
    push_cast; rfl
  have h2 : ∑ a, (endQ M b a : ℂ) • flagCand M μ s true a =
      ((Real.sqrt M : ℂ))⁻¹ • flagCand M μ s true b := by
    simp [endQ, apply_ite (fun r : ℝ => (r : ℂ)), ite_smul]
  rw [homEnd, flagComb, Finset.sum_add_distrib, h1, h2, smul_add, smul_smul]

/-- `Σ_a endP² = (M - 1) (M^{-1/2} (4√M)^{-1})²`. -/
theorem sum_endP_sq (hM : 1 ≤ M) (b : Fin M) :
    ∑ a, endP M b a ^ 2 = ((M : ℝ) - 1) * ((Real.sqrt M)⁻¹ * (4 * Real.sqrt M)⁻¹) ^ 2 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b)]
  have h : ∀ a ∈ Finset.univ.erase b, endP M b a ^ 2 =
      ((Real.sqrt M)⁻¹ * (4 * Real.sqrt M)⁻¹) ^ 2 := fun a ha => by
    rw [endP, if_neg (Finset.ne_of_mem_erase ha)]
  rw [Finset.sum_congr rfl h, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ b),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hM]
  simp [endP]

/-- `Σ_a endQ² = M^{-1}`. -/
theorem sum_endQ_sq (b : Fin M) : ∑ a, endQ M b a ^ 2 = ((Real.sqrt M)⁻¹) ^ 2 := by
  simp [endQ, ite_pow]

/-- `‖x(T)‖² = Σ_a endP² + Σ_a endQ²`. -/
theorem norm_sq_homEnd_eq (b : Fin M) :
    ‖homEnd M μ s b‖ ^ 2 = ∑ a, endP M b a ^ 2 + ∑ a, endQ M b a ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), homEnd_eq_flagComb, inner_flagComb_ofReal,
    RCLike.re_to_complex, Complex.ofReal_re, ← Finset.sum_add_distrib]
  simp only [sq]

/-- The numbers behind every endpoint bound: with `P = Σ endP²`, `Q = Σ endQ²`,
`Q M = 1`, `0 ≤ P` and `16 P ≤ Q`. -/
theorem endPQ_facts (hM : 1 ≤ M) (b : Fin M) :
    (∑ a, endQ M b a ^ 2) * M = 1 ∧ 0 ≤ ∑ a, endP M b a ^ 2 ∧
      16 * ∑ a, endP M b a ^ 2 ≤ ∑ a, endQ M b a ^ 2 := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hr2 : Real.sqrt M ^ 2 = M := Real.sq_sqrt (by linarith)
  refine ⟨?_, Finset.sum_nonneg fun a _ => sq_nonneg _, ?_⟩
  · rw [sum_endQ_sq, inv_pow, hr2]; field_simp
  · rw [sum_endP_sq hM, sum_endQ_sq, mul_pow, inv_pow, inv_pow, mul_pow, hr2]
    rw [show (16 : ℝ) * (((M : ℝ) - 1) * ((M : ℝ)⁻¹ * (4 ^ 2 * (M : ℝ))⁻¹)) =
      ((M : ℝ) - 1) / M * (M : ℝ)⁻¹ by field_simp; ring]
    have h1 : ((M : ℝ) - 1) / M ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have h2 : 0 ≤ (M : ℝ)⁻¹ := by positivity
    nlinarith

/-- `‖x₀‖ = 1` (Proposition `odel:rem:homogeneous`), hence `B = 1`. -/
theorem norm_homInit (hM : 1 ≤ M) : ‖homInit M μ s‖ = 1 := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hx : homInit M μ s = (((Real.sqrt (2 * (M : ℝ)))⁻¹ : ℝ) : ℂ) •
      flagComb M μ s (fun _ => ((1 : ℝ) : ℂ)) (fun _ => ((1 : ℝ) : ℂ)) := by
    simp [homInit, flagComb]
  have h2 : ‖homInit M μ s‖ ^ 2 = 1 := by
    rw [hx, smul_flagComb_ofReal, norm_sq_eq_re_inner (𝕜 := ℂ), inner_flagComb_ofReal,
      RCLike.re_to_complex, Complex.ofReal_re]
    simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hs : Real.sqrt (2 * (M : ℝ)) ^ 2 = 2 * M := Real.sq_sqrt (by positivity)
    have hc : (Real.sqrt (2 * (M : ℝ)))⁻¹ * (Real.sqrt (2 * (M : ℝ)))⁻¹ = (2 * (M : ℝ))⁻¹ := by
      rw [← mul_inv, ← sq, hs]
    have hM0 : (M : ℝ) ≠ 0 := by positivity
    rw [hc]
    field_simp
    ring
  rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_one]

/-! ### The solution after the busy time -/

/-- The merged pulse phase times the hidden phase: `(-i)^n e^{i((n+2) mod 4)π/2} = -1`. -/
theorem negI_pow_mul_exp_pulse (n : ℕ) :
    (-Complex.I) ^ n * Complex.exp (Complex.I * ((pulseLen n : ℝ) : ℂ)) = -1 := by
  have hexp : Complex.exp (Complex.I * ((pulseLen n : ℝ) : ℂ)) = Complex.I ^ ((n + 2) % 4) := by
    have h : Complex.I * ((((((n + 2) % 4 : ℕ) : ℝ) * (Real.pi / 2) : ℝ)) : ℂ) =
        (((n + 2) % 4 : ℕ) : ℂ) * ((Real.pi : ℂ) / 2 * Complex.I) := by push_cast; ring
    rw [pulseLen, h, Complex.exp_nat_mul, Complex.exp_pi_div_two_mul_I]
  have hI : Complex.I ^ ((n + 2) % 4) = Complex.I ^ (n + 2) := by
    conv_rhs => rw [← Nat.mod_add_div (n + 2) 4, pow_add, pow_mul, Complex.I_pow_four, one_pow,
      mul_one]
  rw [hexp, hI, pow_add, ← mul_assoc, ← mul_pow]
  simp

/-- The flag-zero and flag-one coefficients after the busy time. -/
theorem homAlpha_homBeta_of_busy_le (j : Positions M n (2 ^ μ)) (a : Fin M)
    {t : ℝ} (ht : homBusy M n ≤ t) :
    homAlpha j a t =
        ((Real.exp (-homD M) * (Real.sqrt 2 / 2) * (1 + parity (j a)) : ℝ) : ℂ) ∧
      homBeta j a t = ((Real.sqrt 2 / 2 * (1 - parity (j a)) : ℝ) : ℂ) := by
  have hp := pulseLen_nonneg n
  have hd := homD_nonneg M
  have hπ := Real.pi_pos
  unfold homBusy at ht
  have hn : (0 : ℝ) ≤ n * (Real.pi / 2) := by positivity
  have hdamp : dampTime M n t = homD M := by
    unfold dampTime; rw [max_eq_left (by linarith), min_eq_right (by linarith)]
  have hy : yAngle n t = Real.pi / 4 := by
    unfold yAngle; rw [max_eq_left (by linarith), min_eq_right (by linarith)]
  have hph : phaseCoeff j a t = -(parity (j a) : ℂ) := by
    unfold phaseCoeff
    rw [candPhase_of_ge j a (by linarith), exp_candPhase_final,
      max_eq_left (by linarith), min_eq_right (by linarith)]
    have h := negI_pow_mul_exp_pulse n
    linear_combination (parity (j a) : ℂ) * h
  unfold homAlpha homBeta
  rw [hdamp, hy, hph, Real.cos_pi_div_four, Real.sin_pi_div_four]
  constructor <;> push_cast <;> ring

/-- **The final state** (Proposition `odel:rem:homogeneous`): after the busy time the solution is
`homEnd` at the odd candidate. -/
theorem homSol_of_busy_le (hM : 1 ≤ M) (x : Promised M n (2 ^ μ)) {t : ℝ}
    (ht : homBusy M n ≤ t) : homSol M n μ s x t = homEnd M μ s (oddCand x) := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hr : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by linarith)
  have h2 : 0 < Real.sqrt 2 := by positivity
  have h22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsq : Real.sqrt (2 * (M : ℝ)) = Real.sqrt 2 * Real.sqrt M :=
    Real.sqrt_mul (by norm_num) _
  have hsol : homSol M n μ s x t = (((Real.sqrt (2 * (M : ℝ)))⁻¹ : ℝ) : ℂ) •
      flagComb M μ s (fun a => homAlpha x.1 a t) (fun a => homBeta x.1 a t) := by
    rw [homSol, flagComb, Complex.ofReal_inv]
  rw [hsol, smul_flagComb, homEnd_eq_flagComb]
  congr 1 <;> funext a
  · rw [(homAlpha_homBeta_of_busy_le x.1 a ht).1, ← Complex.ofReal_mul]
    congr 1
    rw [endP, exp_neg_homD hM, hsq]
    by_cases ha : a = oddCand x
    · subst ha; rw [if_pos rfl, parity_oddCand]; ring
    · rw [if_neg ha, parity_eq_one_of_ne x ha]
      field_simp
      ring
  · rw [(homAlpha_homBeta_of_busy_le x.1 a ht).2, ← Complex.ofReal_mul]
    congr 1
    rw [endQ, hsq]
    by_cases ha : a = oddCand x
    · subst ha; rw [if_pos rfl, parity_oddCand]
      field_simp
      ring
    · rw [if_neg ha, parity_eq_one_of_ne x ha]; ring

/-! ### Norm, normalisation and the readout -/

/-- **The final norm** `‖x(T)‖² = (1 + (M-1)e^{-2d})/M` (Proposition `odel:rem:homogeneous`). -/
theorem norm_sq_homEnd (hM : 1 ≤ M) (b : Fin M) :
    ‖homEnd M μ s b‖ ^ 2 = (1 + ((M : ℝ) - 1) * Real.exp (-2 * homD M)) / M := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hr : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by linarith)
  have hr2 : Real.sqrt M ^ 2 = M := Real.sq_sqrt (by linarith)
  rw [norm_sq_homEnd_eq, sum_endP_sq hM, sum_endQ_sq,
    show -2 * homD M = -homD M + -homD M by ring, Real.exp_add, exp_neg_homD hM]
  field_simp
  rw [hr2]
  ring

/-- The final state is nonzero. -/
theorem homEnd_ne_zero (hM : 1 ≤ M) (b : Fin M) : homEnd M μ s b ≠ 0 := by
  intro h
  have h0 := norm_sq_homEnd_eq (μ := μ) (s := s) b
  obtain ⟨hQ, hP, -⟩ := endPQ_facts hM b
  rw [h, norm_zero] at h0
  have hq : ∑ a, endQ M b a ^ 2 = 0 := by
    have : 0 ≤ ∑ a, endQ M b a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
    linarith
  rw [hq, zero_mul] at hQ
  exact zero_ne_one hQ

/-- **The normalisation parameter** (Proposition `odel:rem:homogeneous`): with `B = 1`,
`(4/√17)√M ≤ g = 1/‖x(T)‖ ≤ √M`. -/
theorem homEnd_g_bounds (hM : 1 ≤ M) (b : Fin M) :
    4 / Real.sqrt 17 * Real.sqrt M ≤ 1 / ‖homEnd M μ s b‖ ∧
      1 / ‖homEnd M μ s b‖ ≤ Real.sqrt M := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hr2 : Real.sqrt M ^ 2 = M := Real.sq_sqrt (by linarith)
  have hN : 0 < ‖homEnd M μ s b‖ := norm_pos_iff.mpr (homEnd_ne_zero hM b)
  have hN2 := norm_sq_homEnd_eq (μ := μ) (s := s) b
  obtain ⟨hQ, hP, h16⟩ := endPQ_facts hM b
  have h17 : (0 : ℝ) < Real.sqrt 17 := by positivity
  have hrN : 0 ≤ Real.sqrt M * ‖homEnd M μ s b‖ := by positivity
  have hsq : (Real.sqrt M * ‖homEnd M μ s b‖) ^ 2 =
      M * (∑ a, endP M b a ^ 2 + ∑ a, endQ M b a ^ 2) := by
    rw [mul_pow, hr2, hN2]
  constructor
  · rw [le_div_iff₀ hN, show 4 / Real.sqrt 17 * Real.sqrt M * ‖homEnd M μ s b‖ =
      4 * (Real.sqrt M * ‖homEnd M μ s b‖) / Real.sqrt 17 by ring, div_le_one h17]
    have : |4 * (Real.sqrt M * ‖homEnd M μ s b‖)| ≤ Real.sqrt 17 := by
      refine Real.abs_le_sqrt ?_
      rw [mul_pow, hsq]; nlinarith
    exact (le_abs_self _).trans this
  · rw [div_le_iff₀ hN]
    nlinarith

/-- `unitDirection x(T)` as a combination with real coefficients. -/
theorem unitDirection_homEnd (b : Fin M) :
    ODEStateNormalization.unitDirection (homEnd M μ s b) =
      flagComb M μ s (fun a => ((‖homEnd M μ s b‖⁻¹ * endP M b a : ℝ) : ℂ))
        (fun a => ((‖homEnd M μ s b‖⁻¹ * endQ M b a : ℝ) : ℂ)) := by
  rw [ODEStateNormalization.unitDirection, ← Complex.coe_smul]
  conv_lhs => arg 2; rw [homEnd_eq_flagComb]
  rw [smul_flagComb_ofReal]

/-- **Probability at least `16/17` on the odd candidate** (Proposition `odel:rem:homogeneous`): the
normalised final state has squared overlap at least `16/17` with `|1, a_*, ω⟩`, its whole component
on `a_*`. -/
theorem homEnd_prob_ge (hM : 1 ≤ M) (b : Fin M) :
    16 / 17 ≤ ‖⟪flagCand M μ s true b,
      ODEStateNormalization.unitDirection (homEnd M μ s b)⟫_ℂ‖ ^ 2 := by
  rw [unitDirection_homEnd, inner_flagCand_flagComb, if_pos rfl, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, mul_pow, inv_pow, norm_sq_homEnd_eq]
  obtain ⟨hQ, hP, h16⟩ := endPQ_facts hM b
  have hqb : endQ M b b ^ 2 = ∑ a, endQ M b a ^ 2 := by
    rw [sum_endQ_sq, endQ, if_pos rfl]
  have hQ0 : 0 < ∑ a, endQ M b a ^ 2 := by
    by_contra h; have h' := not_lt.mp h; nlinarith
  rw [hqb, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
  nlinarith

end

end ODELowerBoundExtensions.Homogeneous
