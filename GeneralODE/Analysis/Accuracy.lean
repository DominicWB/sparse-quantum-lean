import GeneralODE.Analysis.Implemented

/-!
# Accuracy of the implemented history solution

With `m ≥ α T`, `m ≥ 8 Λ T` and a common budget `ϑ` for the three error
sources,

* `m K ε₀ ≤ ϑ` (the identity block `B₀`),
* `m δ_U ≤ ϑ` (the matrix block `B_U ≈ A/α`),
* `m (Λh)^{K+1}/(K+1)! ≤ ϑ` (Taylor truncation),

the final copy `ŷ_m` of the implemented history solution satisfies
`‖ŷ_m - x(T)‖ ≤ 210 C̄ g ϑ ‖x(T)‖`, the whole history has norm at most
`8 √m g ‖x(T)‖`, and the implemented step has powers bounded by `2 C̄`.
Here `C̄` bounds `‖e^{tA}‖` and `g` the path ratio `‖x(t)‖/‖x(T)‖` on `[0,T]`.
-/

namespace SparseHamiltonian.GeneralODE.Implemented

noncomputable section
open NormedSpace ContinuousLinearMap History ExpBounds ODEConstantForcing
open scoped BigOperators Nat

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [Nontrivial V]

local notation "Op" => V →L[ℂ] V

set_option maxHeartbeats 4000000 in
/-- The common accuracy budget of the history construction. -/
theorem history_accuracy (A BU B0 : Op) (x0 b : V) (Λ T Cbar g α δU ε0 ϑ : ℝ) (m K : ℕ)
    (hm : 1 ≤ m) (hT : 0 < T) (hα : 0 < α) (hαT : α * T ≤ m) (hΛT : 8 * Λ * T ≤ m)
    (hA : ‖A‖ ≤ Λ) (hU : ‖BU‖ ≤ 1) (h0 : ‖B0‖ ≤ 1)
    (hUerr : ‖BU - ((α⁻¹ : ℝ) : ℂ) • A‖ ≤ δU) (h0err : ‖B0 - 1‖ ≤ ε0)
    (hC1 : 1 ≤ Cbar) (hC : ∀ t, 0 ≤ t → t ≤ T → ‖exp (t • A)‖ ≤ Cbar)
    (hg1 : 1 ≤ g)
    (hg : ∀ t, 0 ≤ t → t ≤ T → ‖solution A x0 b t‖ ≤ g * ‖solution A x0 b T‖)
    (hϑ0 : 0 ≤ ϑ) (hϑ : 210 * Cbar * g * ϑ ≤ 1)
    (hR1 : m * (K * ε0) ≤ ϑ) (hR2 : m * δU ≤ ϑ)
    (hR3 : m * ((Λ * (T / m)) ^ (K + 1) / ((K + 1) ! : ℝ)) ≤ ϑ) :
    ∃ Q0 : Op, Q0 * powers BU B0 K 0 = 1 ∧ powers BU B0 K 0 * Q0 = 1 ∧ ‖Q0‖ ≤ 2 ∧
      ‖poly (phiCoef (α * (T / m))) (powers BU B0 K)‖ ≤ Real.exp 1 ∧
      (∀ k, k ≤ m → ‖(Q0 * poly (taylorCoef (α * (T / m))) (powers BU B0 K)) ^ k‖ ≤ 2 * Cbar) ∧
      ‖solSeq m (poly (taylorCoef (α * (T / m))) (powers BU B0 K))
          (poly (phiCoef (α * (T / m))) (powers BU B0 K)) Q0 (T / Real.sqrt m) x0 b m -
        solution A x0 b T‖ ≤ 210 * Cbar * g * ϑ * ‖solution A x0 b T‖ ∧
      ‖History.solution m (poly (taylorCoef (α * (T / m))) (powers BU B0 K))
          (poly (phiCoef (α * (T / m))) (powers BU B0 K)) Q0 (T / Real.sqrt m) x0 b‖ ≤
        8 * Real.sqrt m * (g * ‖solution A x0 b T‖) := by
  set h := T / m with hh
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hh0 : 0 ≤ h := div_nonneg hT.le hm0.le
  have hΛ0 : 0 ≤ Λ := (norm_nonneg _).trans hA
  have hτ : α * h ≤ 1 := by
    rw [hh, ← mul_div_assoc, div_le_one hm0]; exact hαT
  have hΛh : Λ * (T / m) ≤ 1 / 8 := by
    rw [← mul_div_assoc, div_le_iff₀ hm0]; linarith
  have hmh : (m : ℝ) * h = T := by rw [hh]; field_simp
  have hε00 : 0 ≤ ε0 := (norm_nonneg _).trans h0err
  have hδ0 : 0 ≤ δU := (norm_nonneg _).trans hUerr
  have hKε0 : 0 ≤ (K : ℝ) * ε0 := by positivity
  have hKε : (K : ℝ) * ε0 ≤ ϑ / m := by rw [le_div_iff₀ hm0]; linarith
  have hδ : δU ≤ ϑ / m := by rw [le_div_iff₀ hm0]; linarith
  have hTay0 : 0 ≤ (Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ) := by positivity
  have hTay : (Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ) ≤ ϑ / m := by
    rw [le_div_iff₀ hm0]; linarith
  have hCg : (1 : ℝ) ≤ Cbar * g := by nlinarith only [hC1, hg1]
  have hϑ1 : ϑ ≤ 1 / 210 := by
    have h1 : ϑ ≤ Cbar * g * ϑ := by nlinarith only [hCg, hϑ0]
    linarith
  have hK : (K : ℝ) * ε0 ≤ 1 / 2 :=
    hKε.trans ((div_le_self hϑ0 hmR).trans (by linarith))
  obtain ⟨Q0, hQP, hPQ, hQ1, hQ2, hΦn, hstep, hsrc⟩ :=
    implemented_bounds A BU B0 Λ α δU ε0 h K hU h0 hα hUerr h0err hK hh0 hτ hA
      (hΛh.trans (by norm_num))
  set V := poly (taylorCoef (α * h)) (powers BU B0 K) with hV
  set Φ := poly (phiCoef (α * h)) (powers BU B0 K) with hΦ
  set e := Real.exp 1 with he
  have he3 : e ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have he0 : 0 ≤ e := (Real.exp_pos 1).le
  -- the error parameters
  set η0 := 2 * ((K : ℝ) * ε0) with hη0
  set ηE := 3 * e * ((K : ℝ) * ε0) + e * (h * α * δU) +
    3 * ((Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ)) with hηE
  set ρS := 7 * e * ((K : ℝ) * ε0) + e * (h * α * δU) +
    3 * ((Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ)) with hρS
  have hhα0 : 0 ≤ h * α * δU := by positivity
  have hhα : h * α * δU ≤ ϑ / m := by
    have : h * α ≤ 1 := by linarith [mul_comm α h]
    calc h * α * δU ≤ 1 * δU := mul_le_mul_of_nonneg_right this hδ0
      _ ≤ ϑ / m := by linarith
  have hmηE : (m : ℝ) * ηE ≤ 15 * ϑ := by
    have h1 : (m : ℝ) * ((K : ℝ) * ε0) ≤ ϑ := hR1
    have h2 : (m : ℝ) * (h * α * δU) ≤ ϑ := by
      have := mul_le_mul_of_nonneg_left hhα hm0.le
      rwa [mul_div_cancel₀ _ hm0.ne'] at this
    have h3 : (m : ℝ) * ((Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ)) ≤ ϑ := hR3
    have hid : (m : ℝ) * ηE = 3 * e * ((m : ℝ) * ((K : ℝ) * ε0)) +
        e * ((m : ℝ) * (h * α * δU)) + 3 * ((m : ℝ) * ((Λ * h) ^ (K + 1) / ((K + 1) ! : ℝ))) := by
      rw [hηE]; ring
    rw [hid]
    have hm1 : 0 ≤ (m : ℝ) * ((K : ℝ) * ε0) := by positivity
    have hm2 : 0 ≤ (m : ℝ) * (h * α * δU) := by positivity
    nlinarith only [mul_le_mul he3 h1 hm1 (by norm_num : (0 : ℝ) ≤ 3),
      mul_le_mul he3 h2 hm2 (by norm_num : (0 : ℝ) ≤ 3), h3]
  have hρS0 : 0 ≤ ρS := by rw [hρS]; positivity
  have hρSb : ρS ≤ 27 * (ϑ / m) := by
    have h1 : e * ((K : ℝ) * ε0) ≤ 3 * (ϑ / m) :=
      (mul_le_mul_of_nonneg_right he3 hKε0).trans (mul_le_mul_of_nonneg_left hKε (by norm_num))
    have h2 : e * (h * α * δU) ≤ 3 * (ϑ / m) :=
      (mul_le_mul_of_nonneg_right he3 hhα0).trans (mul_le_mul_of_nonneg_left hhα (by norm_num))
    rw [hρS]
    linarith
  have hρS3 : ρS * (3 + 2 * Λ * T) ≤ 88 * ϑ := by
    have h1 : 3 + 2 * Λ * T ≤ (13 / 4) * m := by linarith
    have h2 : ρS * (3 + 2 * Λ * T) ≤ 27 * (ϑ / m) * ((13 / 4) * m) :=
      mul_le_mul hρSb h1 (by nlinarith only [mul_nonneg hΛ0 hT.le]) (by positivity)
    have h3 : 27 * (ϑ / m) * ((13 / 4) * m) = 87.75 * ϑ := by field_simp; ring
    linarith
  have hη0b : η0 ≤ 2 * ϑ := by
    rw [hη0]
    have : (K : ℝ) * ε0 ≤ ϑ := hKε.trans (div_le_self hϑ0 hmR)
    linarith
  set X := ‖solution A x0 b T‖ with hX
  have hX0 : 0 ≤ X := norm_nonneg _
  set G := g * X with hG
  have hG0 : 0 ≤ G := by positivity
  -- hypotheses of the trajectory accuracy theorem
  have hCk : ∀ k, k ≤ m → ‖exp (((k : ℝ) * (T / m)) • A)‖ ≤ Cbar := by
    intro k hk
    apply hC
    · positivity
    · have hk' : (k : ℝ) ≤ m := by exact_mod_cast hk
      calc (k : ℝ) * (T / m) ≤ m * (T / m) := mul_le_mul_of_nonneg_right hk' hh0
        _ = T := hmh
  have hGk : ∀ j, j ≤ m → ‖samples A x0 b (T / m) j‖ ≤ G := by
    intro j hj
    unfold samples
    apply hg
    · positivity
    · have hj' : (j : ℝ) ≤ m := by exact_mod_cast hj
      calc (j : ℝ) * (T / m) ≤ m * (T / m) := mul_le_mul_of_nonneg_right hj' hh0
        _ = T := hmh
  have hsmall : Cbar * m * ηE ≤ 1 / 2 := by
    have hC0 : 0 ≤ Cbar := by linarith
    have h1 : Cbar * ((m : ℝ) * ηE) ≤ Cbar * (15 * ϑ) := mul_le_mul_of_nonneg_left hmηE hC0
    have h2 : Cbar * ϑ ≤ 1 / 210 := by
      have : Cbar * ϑ ≤ Cbar * g * ϑ := by nlinarith only [mul_nonneg hC0 hϑ0, hg1]
      linarith
    nlinarith only [h1, h2]
  have hsrc' : ‖stepSource m Φ Q0 (T / Real.sqrt m) b - response A b (T / m)‖ ≤
      ρS * (T / m) * ‖b‖ := by
    rw [stepSource_eq m hm Φ Q0 T b]
    exact hsrc b
  have htraj := trajectory_accuracy A V Φ Q0 x0 b Λ T Cbar G η0 ηE ρS m hm hA hT.le hΛh hCk hGk
    hQ1 hstep hsmall hρS0 hsrc'
  -- the trajectory error budget
  have herr : 2 * Cbar * ((η0 + m * ηE) * G + ρS * (3 + 2 * Λ * T) * G) ≤
      210 * Cbar * g * ϑ * X := by
    have hC0 : 0 ≤ Cbar := by linarith
    have hsum : (η0 + m * ηE) * G + ρS * (3 + 2 * Λ * T) * G ≤ 105 * ϑ * G := by
      have : η0 + m * ηE + ρS * (3 + 2 * Λ * T) ≤ 105 * ϑ := by linarith
      nlinarith only [this, hG0]
    calc 2 * Cbar * ((η0 + m * ηE) * G + ρS * (3 + 2 * Λ * T) * G)
        ≤ 2 * Cbar * (105 * ϑ * G) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 210 * Cbar * g * ϑ * X := by rw [hG]; ring
  have hsampleT : samples A x0 b (T / m) m = solution A x0 b T := by
    unfold samples; rw [hmh]
  refine ⟨Q0, hQP, hPQ, hQ2, hΦn, ?_, ?_, ?_⟩
  · exact step_pow_le A (Q0 * V) T Cbar ηE m hCk hstep hsmall
  · have := htraj m le_rfl
    rw [hsampleT] at this
    exact this.trans herr
  · -- the norm of the history solution
    have hζ : 210 * Cbar * g * ϑ * X ≤ X := by nlinarith only [hϑ, hX0]
    have hseq : ∀ j, j ≤ m → ‖solSeq m V Φ Q0 (T / Real.sqrt m) x0 b j‖ ≤ 2 * G := by
      intro j hj
      have h1 := (htraj j hj).trans herr
      have h2 := hGk j hj
      have h3 : X ≤ G := by rw [hG]; nlinarith only [hg1, hX0]
      calc ‖solSeq m V Φ Q0 (T / Real.sqrt m) x0 b j‖
          = ‖(solSeq m V Φ Q0 (T / Real.sqrt m) x0 b j - samples A x0 b (T / m) j) +
              samples A x0 b (T / m) j‖ := by rw [sub_add_cancel]
        _ ≤ ‖solSeq m V Φ Q0 (T / Real.sqrt m) x0 b j - samples A x0 b (T / m) j‖ +
              ‖samples A x0 b (T / m) j‖ := norm_add_le _ _
        _ ≤ X + G := add_le_add (h1.trans hζ) h2
        _ ≤ 2 * G := by linarith
    have hforce := forcing_le A x0 b Λ T m hm hA hT.le hΛh G hGk
    have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
    have hsq : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
    have hμb : ‖Q0 (((T / Real.sqrt m : ℝ) : ℂ) • b)‖ ≤ 6.5 * Real.sqrt m * G := by
      have h1 : ‖Q0 (((T / Real.sqrt m : ℝ) : ℂ) • b)‖ ≤ 2 * ((T / Real.sqrt m) * ‖b‖) := by
        refine (Q0.le_opNorm _).trans (mul_le_mul hQ2 ?_ (norm_nonneg _) (by norm_num))
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h2 : T * ‖b‖ ≤ (13 / 4) * m * G := by
        have : (3 + 2 * Λ * T) * G ≤ (13 / 4) * m * G :=
          mul_le_mul_of_nonneg_right (by linarith) hG0
        linarith
      have h3 : (T / Real.sqrt m) * ‖b‖ ≤ (13 / 4) * Real.sqrt m * G := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hsm]
        calc T * ‖b‖ ≤ (13 / 4) * m * G := h2
          _ = (13 / 4) * Real.sqrt m * G * Real.sqrt m := by
              linear_combination (-(13 / 4) * G) * hsq
      linarith
    have hnorm := norm_sq_solution m V Φ Q0 (T / Real.sqrt m) x0 b
    have hsum : ∑ j ∈ Finset.range (2 * m + 1),
        ‖solSeq m V Φ Q0 (T / Real.sqrt m) x0 b (min j m)‖ ^ 2 ≤ (2 * m + 1) * (2 * G) ^ 2 := by
      have hterm : ∀ j ∈ Finset.range (2 * m + 1),
          ‖solSeq m V Φ Q0 (T / Real.sqrt m) x0 b (min j m)‖ ^ 2 ≤ (2 * G) ^ 2 := by
        intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (hseq _ (min_le_right j m)) 2
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      exact le_rfl
    have hfinal : ‖History.solution m V Φ Q0 (T / Real.sqrt m) x0 b‖ ^ 2 ≤
        (8 * Real.sqrt m * G) ^ 2 := by
      rw [hnorm]
      have h1 : ‖Q0 (((T / Real.sqrt m : ℝ) : ℂ) • b)‖ ^ 2 ≤ (6.5 * Real.sqrt m * G) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hμb 2
      have h2 : (6.5 * Real.sqrt m * G) ^ 2 = 42.25 * m * G ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hm0.le]; ring
      have h3 : (8 * Real.sqrt m * G) ^ 2 = 64 * m * G ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hm0.le]; ring
      rw [h3]
      rw [h2] at h1
      have h4 : (2 * (m : ℝ) + 1) * (2 * G) ^ 2 ≤ 12 * m * G ^ 2 := by
        nlinarith only [sq_nonneg G, hmR]
      have h5 : 0 ≤ (m : ℝ) * G ^ 2 := by positivity
      linarith
    have h0' : 0 ≤ 8 * Real.sqrt m * G := by positivity
    calc ‖History.solution m V Φ Q0 (T / Real.sqrt m) x0 b‖
        ≤ 8 * Real.sqrt m * G := (pow_le_pow_iff_left₀ (norm_nonneg _) h0' two_ne_zero).mp hfinal
      _ = 8 * Real.sqrt m * (g * X) := by rw [hG]

end

end SparseHamiltonian.GeneralODE.Implemented
