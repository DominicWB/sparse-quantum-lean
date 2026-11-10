import OptimalPrecision.Weights.Poisson

/-!
# The `L²` bound for `χ = tφ + tφ' + φ`

With `φ = e^{-t} P(t)`, `P` the delayed exponential polynomial with Taylor data
`d` at the delay `a` (`ExpPoly.shifted`), this file proves

  `∫_0^∞ χ² ≤ a ((a+1) ω)² + 2 ω σ ((a + D + 1)² + D + 2)`

whenever `|d_j| ≤ w_j ≤ ω`, `∑_j w_j ≤ σ`, and `d` vanishes up to an index
`k₀ ≥ 11a`. With `ω = 2/ℓ²`, `σ = 2/ℓ`, `ℓ ≥ a` and `D ≤ 26a` both terms are
`O(1/a)`, which is the bound `‖𝔏ψ‖₂ = O(a^{-1/2})` of `opt:thm:weights`.
-/

namespace OptimalPrecision.ExpPoly

noncomputable section

open MeasureTheory Set Polynomial Finset Nat
open scoped Polynomial

/-- `χ = e^{-t}(t P' + P)` in Poisson coordinates. -/
theorem exp_mul_eval_chi (a : ℝ) (d : ℕ → ℝ) (D : ℕ) (hdD : d (D + 1) = 0) (t : ℝ) :
    Real.exp (-t) * (X * derivative (shifted a (Real.exp a) d D) +
        shifted a (Real.exp a) d D).eval t =
      t * Phi D (fun m => d (m + 1)) (t - a) + Phi D d (t - a) := by
  rw [eval_add, eval_mul, eval_X, mul_add, derivative_shifted a _ d D hdD,
    ← exp_mul_eval_shifted, ← exp_mul_eval_shifted]
  ring

/-- `∑_{j ≤ D} w_{j+1} ≤ ∑_{j ≤ D} w_j` when `w_{D+1} = 0` and `w_0 ≥ 0`. -/
theorem sum_shift_le {D : ℕ} {w : ℕ → ℝ} (hw0 : 0 ≤ w 0) (hwD : w (D + 1) = 0) :
    ∑ j ∈ range (D + 1), w (j + 1) ≤ ∑ j ∈ range (D + 1), w j := by
  have h := Finset.sum_range_succ' w (D + 1)
  rw [Finset.sum_range_succ w (D + 1), hwD, add_zero] at h
  linarith

/-- **The `L²` bound for `χ`.** -/
theorem J_chi_le {a : ℝ} (ha : 1 ≤ a) {D k0 : ℕ} {d w : ℕ → ℝ} {ω σ : ℝ}
    (hdw : ∀ j, |d j| ≤ w j) (hwω : ∀ j, w j ≤ ω) (hω : 0 ≤ ω) (hw0 : ∀ j, 0 ≤ w j)
    (hwσ : ∑ j ∈ range (D + 1), w j ≤ σ) (hdD : d (D + 1) = 0) (hwD : w (D + 1) = 0)
    (hvan : ∀ j, j ≤ k0 → d j = 0) (hk0 : 11 * a ≤ k0) :
    J ((X * derivative (shifted a (Real.exp a) d D) + shifted a (Real.exp a) d D) *
        (X * derivative (shifted a (Real.exp a) d D) + shifted a (Real.exp a) d D)) ≤
      a * ((a + 1) * ω) ^ 2 + 2 * ω * σ * ((a + D + 1) ^ 2 + D + 2) := by
  set χπ := X * derivative (shifted a (Real.exp a) d D) + shifted a (Real.exp a) d D
  set d₁ : ℕ → ℝ := fun m => d (m + 1) with hd₁
  set w₁ : ℕ → ℝ := fun m => w (m + 1) with hw₁
  have hχ : ∀ t, Real.exp (-t) * χπ.eval t = t * Phi D d₁ (t - a) + Phi D d (t - a) :=
    exp_mul_eval_chi a d D hdD
  have ha0 : 0 < a := by linarith
  have hσ : 0 ≤ σ := (Finset.sum_nonneg fun j _ => hw0 j).trans hwσ
  rw [← integral_sq_eq_J]
  have hint := integrableOn_sq χπ
  rw [← Ioc_union_Ioi_eq_Ioi ha0.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi ha0.le))]
  -- below the delay: `0 < t ≤ a`
  have hpart1 : ∫ t in Ioc 0 a, (Real.exp (-t) * χπ.eval t) ^ 2 ≤ a * ((a + 1) * ω) ^ 2 := by
    have hb : ∀ t ∈ Ioc (0 : ℝ) a, (Real.exp (-t) * χπ.eval t) ^ 2 ≤ ((a + 1) * ω) ^ 2 := by
      intro t ht
      rw [hχ]
      have hu1 : -a ≤ t - a := by linarith [ht.1]
      have hu2 : t - a ≤ 0 := by linarith [ht.2]
      have hdω : ∀ j, |d j| ≤ ω := fun j => (hdw j).trans (hwω j)
      have h1 : |Phi D d₁ (t - a)| ≤ ω :=
        abs_Phi_le_of_nonpos ha hk0 hω (fun j => hdω (j + 1)) (fun j hj => hvan (j + 1) (by omega))
          hu1 hu2
      have h2 : |Phi D d (t - a)| ≤ ω :=
        abs_Phi_le_of_nonpos ha hk0 hω hdω (fun j hj => hvan j hj.le) hu1 hu2
      have h3 : |t * Phi D d₁ (t - a) + Phi D d (t - a)| ≤ (a + 1) * ω := by
        calc |t * Phi D d₁ (t - a) + Phi D d (t - a)| ≤
            |t| * |Phi D d₁ (t - a)| + |Phi D d (t - a)| := by
              rw [← abs_mul]; exact abs_add_le _ _
          _ ≤ a * ω + ω := by
              rw [abs_of_pos ht.1]
              exact add_le_add (mul_le_mul ht.2 h1 (abs_nonneg _) ha0.le) h2
          _ = (a + 1) * ω := by ring
      calc (t * Phi D d₁ (t - a) + Phi D d (t - a)) ^ 2 =
          |t * Phi D d₁ (t - a) + Phi D d (t - a)| ^ 2 := (sq_abs _).symm
        _ ≤ ((a + 1) * ω) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
    calc ∫ t in Ioc 0 a, (Real.exp (-t) * χπ.eval t) ^ 2 ≤
          ∫ _t in Ioc (0 : ℝ) a, ((a + 1) * ω) ^ 2 :=
          setIntegral_mono_on (hint.mono_set Ioc_subset_Ioi_self)
            (integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top))
            measurableSet_Ioc hb
      _ = a * ((a + 1) * ω) ^ 2 := by
          rw [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero,
            ENNReal.toReal_ofReal ha0.le, smul_eq_mul]
  -- beyond the delay: `t > a`
  have hpart2 : ∫ t in Ioi a, (Real.exp (-t) * χπ.eval t) ^ 2 ≤
      2 * ω * σ * ((a + D + 1) ^ 2 + D + 2) := by
    rw [setIntegral_Ioi_shift]
    simp only [hχ, add_sub_cancel_right]
    -- integrability of the integrand: it is `e^{-2a}(e^{-u} π₂(u))²` with `π₂ = χπ(· + a)`
    have hF : IntegrableOn (fun u => ((u + a) * Phi D d₁ u + Phi D d u) ^ 2) (Ioi 0) := by
      have h : IntegrableOn (fun u : ℝ => Real.exp (-(2 * a)) *
          (Real.exp (-u) * (χπ.comp (X + C a)).eval u) ^ 2) (Ioi 0) :=
        (integrableOn_sq (χπ.comp (X + C a))).const_mul (Real.exp (-(2 * a)))
      refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
      have e := hχ (u + a)
      rw [add_sub_cancel_right] at e
      dsimp only
      have hXa : (X + C a : ℝ[X]).eval u = u + a := by simp
      rw [← e, eval_comp, hXa, show -(u + a) = -u + -a by ring, Real.exp_add,
        show Real.exp (-(2 * a)) = Real.exp (-a) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf]
      ring
    have hG1 : IntegrableOn (fun u => 2 * ω * ((u + a) ^ 2 * Phi D w₁ u)) (Ioi 0) :=
      (integrableOn_sq_mul_Phi a D w₁).const_mul _
    have hG2 : IntegrableOn (fun u => 2 * ω * Phi D w u) (Ioi 0) :=
      (integrableOn_Phi D w).const_mul _
    have hG : IntegrableOn (fun u => 2 * ω * ((u + a) ^ 2 * Phi D w₁ u) + 2 * ω * Phi D w u)
        (Ioi 0) := hG1.add hG2
    have hpt : ∀ u ∈ Ioi (0 : ℝ), ((u + a) * Phi D d₁ u + Phi D d u) ^ 2 ≤
        2 * ω * ((u + a) ^ 2 * Phi D w₁ u) + 2 * ω * Phi D w u := by
      intro u hu
      have hu0 : (0 : ℝ) ≤ u := le_of_lt hu
      have e1 : ((u + a) * Phi D d₁ u + Phi D d u) ^ 2 ≤
          2 * ((u + a) ^ 2 * Phi D d₁ u ^ 2) + 2 * Phi D d u ^ 2 := by
        nlinarith [sq_nonneg ((u + a) * Phi D d₁ u - Phi D d u)]
      have e2 : Phi D d₁ u ^ 2 ≤ ω * Phi D w₁ u :=
        Phi_sq_le (fun j => hdw (j + 1)) (fun j => hwω (j + 1)) hω hu0
      have e3 : Phi D d u ^ 2 ≤ ω * Phi D w u := Phi_sq_le hdw hwω hω hu0
      have hua : 0 ≤ (u + a) ^ 2 := sq_nonneg _
      calc ((u + a) * Phi D d₁ u + Phi D d u) ^ 2 ≤
          2 * ((u + a) ^ 2 * Phi D d₁ u ^ 2) + 2 * Phi D d u ^ 2 := e1
        _ ≤ 2 * ((u + a) ^ 2 * (ω * Phi D w₁ u)) + 2 * (ω * Phi D w u) := by gcongr
        _ = 2 * ω * ((u + a) ^ 2 * Phi D w₁ u) + 2 * ω * Phi D w u := by ring
    have hsum1 : ∑ j ∈ range (D + 1), w₁ j * ((a + j + 1) ^ 2 + (j + 1)) ≤
        ((a + D + 1) ^ 2 + (D + 1)) * σ := by
      calc ∑ j ∈ range (D + 1), w₁ j * ((a + j + 1) ^ 2 + (j + 1)) ≤
          ∑ j ∈ range (D + 1), w₁ j * ((a + D + 1) ^ 2 + (D + 1)) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hjD : (j : ℝ) ≤ D := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
            have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
            apply mul_le_mul_of_nonneg_left _ (hw0 (j + 1))
            have : a + j + 1 ≤ a + D + 1 := by linarith
            have h0 : 0 ≤ a + j + 1 := by linarith
            nlinarith
        _ = ((a + D + 1) ^ 2 + (D + 1)) * ∑ j ∈ range (D + 1), w₁ j := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
        _ ≤ ((a + D + 1) ^ 2 + (D + 1)) * σ := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact (sum_shift_le (hw0 0) hwD).trans hwσ
    calc ∫ u in Ioi 0, ((u + a) * Phi D d₁ u + Phi D d u) ^ 2 ≤
        ∫ u in Ioi 0, (2 * ω * ((u + a) ^ 2 * Phi D w₁ u) + 2 * ω * Phi D w u) :=
          setIntegral_mono_on hF hG measurableSet_Ioi hpt
      _ = 2 * ω * ∑ j ∈ range (D + 1), w₁ j * ((a + j + 1) ^ 2 + (j + 1)) +
            2 * ω * ∑ j ∈ range (D + 1), w j := by
          rw [integral_add hG1 hG2, integral_const_mul, integral_const_mul, integral_sq_mul_Phi,
            integral_Phi]
      _ ≤ 2 * ω * (((a + D + 1) ^ 2 + (D + 1)) * σ) + 2 * ω * σ := by
          gcongr
      _ = 2 * ω * σ * ((a + D + 1) ^ 2 + D + 2) := by ring
  linarith

end

end OptimalPrecision.ExpPoly
