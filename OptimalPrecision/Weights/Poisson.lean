import OptimalPrecision.Weights.Integral
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The extraction function in Poisson coordinates, and its `L²` bound

Write `p_j(u) = e^{-u} u^j / j!` (the gamma densities of `opt:eq:gamma-degree`)
and `Φ_d(u) = ∑_{j ≤ D} d_j p_j(u)`. For the polynomial `P` with Taylor data
`d` at the delay `a` (`ExpPoly.shifted`), `e^{-t} P(t) = Φ_d(t - a)` and
`e^{-t} P'(t) = Φ_{d(·+1)}(t - a)`.

The main result `J_chi_le` bounds `∫_0^∞ χ²` for `χ = tφ + tφ' + φ`
(`= e^{-t}(tP' + P)`), where `φ = e^{-t}P`:

* on `t > a`, the Poisson probabilities give `|Φ_d| ≤ Φ_w ≤ ω` for `|d_j| ≤ w_j ≤ ω`,
  hence `Φ_d² ≤ ω Φ_w`, and the first two gamma moments finish
  (`opt:eq:gamma-norms`);
* on `0 < t ≤ a`, the coefficients vanish below `k₀ ≥ 11a` and the Poisson tail
  `e^a ∑_{j ≥ k₀} a^j/j! ≤ 1` bounds the extension below the delay.
-/

namespace OptimalPrecision.ExpPoly

noncomputable section

open MeasureTheory Set Polynomial Finset Nat
open scoped Polynomial

/-! ### Poisson coordinates -/

/-- The gamma density `p_j(u) = e^{-u} u^j / j!`. -/
def pk (j : ℕ) (u : ℝ) : ℝ := Real.exp (-u) * u ^ j / (j ! : ℝ)

/-- `Φ_d(u) = ∑_{j ≤ D} d_j p_j(u)`. -/
def Phi (D : ℕ) (d : ℕ → ℝ) (u : ℝ) : ℝ := ∑ j ∈ range (D + 1), d j * pk j u

theorem eval_shifted (a E : ℝ) (d : ℕ → ℝ) (D : ℕ) (t : ℝ) :
    (shifted a E d D).eval t = E * ∑ m ∈ range (D + 1), d m / (m ! : ℝ) * (t - a) ^ m := by
  rw [shifted, taylor_eval, eval_smul, eval_finsetSum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X, sub_eq_add_neg]

theorem exp_mul_eval_shifted (a : ℝ) (d : ℕ → ℝ) (D : ℕ) (t : ℝ) :
    Real.exp (-t) * (shifted a (Real.exp a) d D).eval t = Phi D d (t - a) := by
  rw [eval_shifted, Phi, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [pk, show -(t - a) = -t + a by ring, Real.exp_add]
  ring

theorem derivative_taylor (r : ℝ) (f : ℝ[X]) :
    derivative (taylor r f) = taylor r (derivative f) := by
  rw [taylor_apply, taylor_apply, derivative_comp, derivative_add, derivative_X, derivative_C,
    add_zero, one_mul]

theorem coeff_sum_C_mul_X_pow (D : ℕ) (c : ℕ → ℝ) (j : ℕ) :
    (∑ m ∈ range (D + 1), C (c m) * X ^ m : ℝ[X]).coeff j = if j < D + 1 then c j else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

/-- The derivative of the delayed exponential polynomial shifts the Taylor data. -/
theorem derivative_shifted (a E : ℝ) (d : ℕ → ℝ) (D : ℕ) (hD : d (D + 1) = 0) :
    derivative (shifted a E d D) = shifted a E (fun m => d (m + 1)) D := by
  rw [shifted, shifted, derivative_taylor]
  congr 1
  ext j
  rw [coeff_derivative, coeff_smul, coeff_smul, coeff_sum_C_mul_X_pow, coeff_sum_C_mul_X_pow,
    smul_eq_mul, smul_eq_mul]
  have hj : ((j + 1 : ℕ) ! : ℝ) = ((j : ℝ) + 1) * (j ! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hj0 : (j ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have hj1 : (j : ℝ) + 1 ≠ 0 := by positivity
  by_cases h1 : j + 1 < D + 1
  · rw [if_pos h1, if_pos (by omega), hj]
    field_simp
  · rw [if_neg h1]
    by_cases h2 : j < D + 1
    · have : j = D := by omega
      subst this
      rw [if_pos h2, hD]; simp
    · rw [if_neg h2]; simp

/-! ### Pointwise bounds -/

theorem pk_nonneg (j : ℕ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ pk j u := by
  unfold pk; positivity

theorem sum_pk_le_one (D : ℕ) {u : ℝ} (hu : 0 ≤ u) : ∑ j ∈ range (D + 1), pk j u ≤ 1 := by
  have h := Real.sum_le_exp_of_nonneg hu (D + 1)
  have e : ∑ j ∈ range (D + 1), pk j u = Real.exp (-u) * ∑ j ∈ range (D + 1), u ^ j / j ! := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by unfold pk; ring
  rw [e]
  calc Real.exp (-u) * ∑ j ∈ range (D + 1), u ^ j / j ! ≤ Real.exp (-u) * Real.exp u :=
        mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

theorem abs_pk_le {a u : ℝ} (j : ℕ) (hu1 : -a ≤ u) (hu2 : u ≤ 0) :
    |pk j u| ≤ Real.exp a * a ^ j / j ! := by
  unfold pk
  have ha : 0 ≤ a := by linarith
  rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos _), abs_pow, Nat.abs_cast]
  have h1 : Real.exp (-u) ≤ Real.exp a := Real.exp_le_exp.mpr (by linarith)
  have h2 : |u| ^ j ≤ a ^ j :=
    pow_le_pow_left₀ (abs_nonneg u) (by rw [abs_of_nonpos hu2]; linarith) j
  exact div_le_div_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le)
    (by positivity)

theorem abs_Phi_le {D : ℕ} {d w : ℕ → ℝ} (hdw : ∀ j, |d j| ≤ w j) {u : ℝ} (hu : 0 ≤ u) :
    |Phi D d u| ≤ Phi D w u := by
  unfold Phi
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul, abs_of_nonneg (pk_nonneg j hu)]
  exact mul_le_mul_of_nonneg_right (hdw j) (pk_nonneg j hu)

theorem Phi_le {D : ℕ} {w : ℕ → ℝ} {ω : ℝ} (hwω : ∀ j, w j ≤ ω) (hω : 0 ≤ ω) {u : ℝ}
    (hu : 0 ≤ u) : Phi D w u ≤ ω := by
  unfold Phi
  calc ∑ j ∈ range (D + 1), w j * pk j u ≤ ∑ j ∈ range (D + 1), ω * pk j u :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hwω j) (pk_nonneg j hu)
    _ = ω * ∑ j ∈ range (D + 1), pk j u := by rw [Finset.mul_sum]
    _ ≤ ω * 1 := mul_le_mul_of_nonneg_left (sum_pk_le_one D hu) hω
    _ = ω := mul_one ω

theorem Phi_sq_le {D : ℕ} {d w : ℕ → ℝ} {ω : ℝ} (hdw : ∀ j, |d j| ≤ w j) (hwω : ∀ j, w j ≤ ω)
    (hω : 0 ≤ ω) {u : ℝ} (hu : 0 ≤ u) : Phi D d u ^ 2 ≤ ω * Phi D w u := by
  have h1 := abs_Phi_le (D := D) hdw hu
  have h2 := Phi_le (D := D) hwω hω hu
  have h3 : 0 ≤ Phi D w u := (abs_nonneg _).trans h1
  calc Phi D d u ^ 2 = |Phi D d u| * |Phi D d u| := by rw [sq, abs_mul_abs_self]
    _ ≤ Phi D w u * ω := mul_le_mul h1 (h1.trans h2) (abs_nonneg _) h3
    _ = ω * Phi D w u := mul_comm _ _

/-- The Poisson tail beyond `k₀ ≥ 11a`: `e^a ∑_{j ≥ k₀} a^j/j! ≤ 1`. -/
theorem tail_le_one {a : ℝ} (ha : 1 ≤ a) {k0 : ℕ} (hk0 : 11 * a ≤ k0) (D : ℕ) :
    Real.exp a * ∑ j ∈ Ico k0 (D + 1), a ^ j / (j ! : ℝ) ≤ 1 := by
  have ha0 : 0 ≤ a := by linarith
  -- `a^j/j! ≤ e^{4a} 4^{-j}`
  have hterm : ∀ j : ℕ, a ^ j / (j ! : ℝ) ≤ Real.exp (4 * a) * (1 / 4 : ℝ) ^ j := by
    intro j
    have h := Real.pow_div_factorial_le_exp (4 * a) (by linarith) j
    rw [mul_pow] at h
    have h4 : (0 : ℝ) < 4 ^ j := by positivity
    rw [one_div_pow, mul_one_div, le_div_iff₀ h4]
    calc a ^ j / (j ! : ℝ) * 4 ^ j = 4 ^ j * a ^ j / j ! := by ring
      _ ≤ Real.exp (4 * a) := h
  have hgeom : ∑ j ∈ Ico k0 (D + 1), (1 / 4 : ℝ) ^ j ≤ (1 / 4 : ℝ) ^ k0 / (1 - 1 / 4) :=
    geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
  have hsum : ∑ j ∈ Ico k0 (D + 1), a ^ j / (j ! : ℝ) ≤
      Real.exp (4 * a) * ((1 / 4 : ℝ) ^ k0 / (1 - 1 / 4)) := by
    calc ∑ j ∈ Ico k0 (D + 1), a ^ j / (j ! : ℝ) ≤
        ∑ j ∈ Ico k0 (D + 1), Real.exp (4 * a) * (1 / 4 : ℝ) ^ j :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = Real.exp (4 * a) * ∑ j ∈ Ico k0 (D + 1), (1 / 4 : ℝ) ^ j := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hgeom (Real.exp_pos _).le
  -- `4^{-k₀} ≤ e^{-k₀} ≤ e^{-11a}`
  have he : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hpow : (1 / 4 : ℝ) ^ k0 ≤ Real.exp (-(11 * a)) := by
    calc (1 / 4 : ℝ) ^ k0 ≤ Real.exp (-1) ^ k0 := pow_le_pow_left₀ (by norm_num) he k0
      _ = Real.exp (-(k0 : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
      _ ≤ Real.exp (-(11 * a)) := Real.exp_le_exp.mpr (by linarith)
  calc Real.exp a * ∑ j ∈ Ico k0 (D + 1), a ^ j / (j ! : ℝ) ≤
      Real.exp a * (Real.exp (4 * a) * ((1 / 4 : ℝ) ^ k0 / (1 - 1 / 4))) :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = (4 / 3) * (Real.exp a * Real.exp (4 * a) * (1 / 4 : ℝ) ^ k0) := by ring
    _ ≤ (4 / 3) * (Real.exp a * Real.exp (4 * a) * Real.exp (-(11 * a))) := by gcongr
    _ = (4 / 3) * Real.exp (-(6 * a)) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    _ ≤ (4 / 3) * Real.exp (-6) := by gcongr; linarith
    _ ≤ 1 := by
        have : Real.exp (-6) ≤ 3 / 4 := by
          rw [Real.exp_neg]
          have h7 : (7 : ℝ) ≤ Real.exp 6 := by linarith [Real.add_one_le_exp (6 : ℝ)]
          rw [inv_le_comm₀ (Real.exp_pos 6) (by norm_num)]
          linarith
        linarith

/-- Below the delay: `|Φ_d(u)| ≤ ω` for `-a ≤ u ≤ 0` when `d` vanishes up to `k₀ ≥ 11a`. -/
theorem abs_Phi_le_of_nonpos {a : ℝ} (ha : 1 ≤ a) {D k0 : ℕ} (hk0 : 11 * a ≤ k0) {d : ℕ → ℝ}
    {ω : ℝ} (hω : 0 ≤ ω) (hdω : ∀ j, |d j| ≤ ω) (hvan : ∀ j < k0, d j = 0) {u : ℝ}
    (hu1 : -a ≤ u) (hu2 : u ≤ 0) : |Phi D d u| ≤ ω := by
  unfold Phi
  have hsplit : ∑ j ∈ range (D + 1), d j * pk j u = ∑ j ∈ Ico k0 (D + 1), d j * pk j u := by
    rw [Finset.range_eq_Ico]
    by_cases hk : k0 ≤ D + 1
    · rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le k0) hk, Finset.sum_eq_zero, zero_add]
      intro j hj
      rw [hvan j (Finset.mem_Ico.mp hj).2, zero_mul]
    · rw [Finset.Ico_eq_empty_of_le (by omega : D + 1 ≤ k0), Finset.sum_empty, Finset.sum_eq_zero]
      intro j hj
      rw [hvan j (by have := (Finset.mem_Ico.mp hj).2; omega), zero_mul]
  rw [hsplit]
  calc |∑ j ∈ Ico k0 (D + 1), d j * pk j u| ≤ ∑ j ∈ Ico k0 (D + 1), |d j * pk j u| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Ico k0 (D + 1), ω * (Real.exp a * a ^ j / j !) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (hdω j) (abs_pk_le j hu1 hu2) (abs_nonneg _) hω
    _ = ω * (Real.exp a * ∑ j ∈ Ico k0 (D + 1), a ^ j / (j ! : ℝ)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ω * 1 := mul_le_mul_of_nonneg_left (tail_le_one ha hk0 D) hω
    _ = ω := mul_one ω

/-! ### Gamma moments -/

theorem pk_eq (j : ℕ) (u : ℝ) : pk j u = (j ! : ℝ)⁻¹ * (u ^ j * Real.exp (-(1 * u))) := by
  unfold pk; rw [one_mul]; ring

theorem integrableOn_pk (j : ℕ) : IntegrableOn (pk j) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => (j ! : ℝ)⁻¹ * (u ^ j * Real.exp (-(1 * u)))) (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg j one_pos).const_mul ((j ! : ℝ)⁻¹)
  exact h.congr_fun (fun u _ => (pk_eq j u).symm) measurableSet_Ioi

theorem integral_pk (j : ℕ) : ∫ u in Ioi 0, pk j u = 1 := by
  have hj : (j ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  simp_rw [pk_eq]
  rw [integral_const_mul, integral_pow_mul_exp_neg j one_pos, one_pow, div_one,
    inv_mul_cancel₀ hj]

theorem sq_mul_pk_eq (a : ℝ) (j : ℕ) (u : ℝ) : (u + a) ^ 2 * pk j u =
    (j ! : ℝ)⁻¹ * (u ^ (j + 2) * Real.exp (-(1 * u))) +
      (2 * a * (j ! : ℝ)⁻¹) * (u ^ (j + 1) * Real.exp (-(1 * u))) +
        (a ^ 2 * (j ! : ℝ)⁻¹) * (u ^ j * Real.exp (-(1 * u))) := by
  unfold pk; rw [one_mul]; ring

theorem integrableOn_sq_mul_pk (a : ℝ) (j : ℕ) :
    IntegrableOn (fun u => (u + a) ^ 2 * pk j u) (Ioi 0) := by
  have i1 : IntegrableOn (fun u : ℝ => (j ! : ℝ)⁻¹ * (u ^ (j + 2) * Real.exp (-(1 * u)))) (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg (j + 2) one_pos).const_mul _
  have i2 : IntegrableOn
      (fun u : ℝ => (2 * a * (j ! : ℝ)⁻¹) * (u ^ (j + 1) * Real.exp (-(1 * u)))) (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg (j + 1) one_pos).const_mul _
  have i3 : IntegrableOn
      (fun u : ℝ => (a ^ 2 * (j ! : ℝ)⁻¹) * (u ^ j * Real.exp (-(1 * u)))) (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg j one_pos).const_mul _
  have i123 : IntegrableOn (fun u : ℝ => (j ! : ℝ)⁻¹ * (u ^ (j + 2) * Real.exp (-(1 * u))) +
      (2 * a * (j ! : ℝ)⁻¹) * (u ^ (j + 1) * Real.exp (-(1 * u))) +
        (a ^ 2 * (j ! : ℝ)⁻¹) * (u ^ j * Real.exp (-(1 * u)))) (Ioi 0) := (i1.add i2).add i3
  exact i123.congr_fun (fun u _ => (sq_mul_pk_eq a j u).symm) measurableSet_Ioi

/-- `∫_0^∞ (u + a)² p_j(u) du = (a + j + 1)² + (j + 1)`. -/
theorem integral_sq_mul_pk (a : ℝ) (j : ℕ) :
    ∫ u in Ioi 0, (u + a) ^ 2 * pk j u = (a + j + 1) ^ 2 + (j + 1) := by
  have i1 : IntegrableOn (fun u : ℝ => (j ! : ℝ)⁻¹ * (u ^ (j + 2) * Real.exp (-(1 * u)))) (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg (j + 2) one_pos).const_mul _
  have i2 : IntegrableOn
      (fun u : ℝ => (2 * a * (j ! : ℝ)⁻¹) * (u ^ (j + 1) * Real.exp (-(1 * u)))) (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg (j + 1) one_pos).const_mul _
  have i3 : IntegrableOn
      (fun u : ℝ => (a ^ 2 * (j ! : ℝ)⁻¹) * (u ^ j * Real.exp (-(1 * u)))) (Ioi 0) :=
    (integrableOn_pow_mul_exp_neg j one_pos).const_mul _
  have i12 : IntegrableOn (fun u : ℝ => (j ! : ℝ)⁻¹ * (u ^ (j + 2) * Real.exp (-(1 * u))) +
      (2 * a * (j ! : ℝ)⁻¹) * (u ^ (j + 1) * Real.exp (-(1 * u)))) (Ioi 0) := i1.add i2
  simp_rw [sq_mul_pk_eq a j]
  rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_pow_mul_exp_neg _ one_pos, integral_pow_mul_exp_neg _ one_pos,
    integral_pow_mul_exp_neg _ one_pos]
  have hj : (j ! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  rw [Nat.factorial_succ (j + 1), Nat.factorial_succ j]
  push_cast
  field_simp
  ring

theorem integrableOn_Phi (D : ℕ) (w : ℕ → ℝ) : IntegrableOn (Phi D w) (Ioi 0) := by
  unfold Phi
  exact integrable_finsetSum _ fun j _ => (integrableOn_pk j).const_mul _

theorem integral_Phi (D : ℕ) (w : ℕ → ℝ) : ∫ u in Ioi 0, Phi D w u = ∑ j ∈ range (D + 1), w j := by
  unfold Phi
  rw [integral_finsetSum _ fun j _ => (integrableOn_pk j).const_mul _]
  exact Finset.sum_congr rfl fun j _ => by rw [integral_const_mul, integral_pk, mul_one]

theorem integrableOn_sq_mul_Phi (a : ℝ) (D : ℕ) (w : ℕ → ℝ) :
    IntegrableOn (fun u => (u + a) ^ 2 * Phi D w u) (Ioi 0) := by
  have h : IntegrableOn (fun u => ∑ j ∈ range (D + 1), w j * ((u + a) ^ 2 * pk j u)) (Ioi 0) :=
    integrable_finsetSum _ fun j _ => (integrableOn_sq_mul_pk a j).const_mul (w j)
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [Phi, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem integral_sq_mul_Phi (a : ℝ) (D : ℕ) (w : ℕ → ℝ) :
    ∫ u in Ioi 0, (u + a) ^ 2 * Phi D w u =
      ∑ j ∈ range (D + 1), w j * ((a + j + 1) ^ 2 + (j + 1)) := by
  have e : (fun u => (u + a) ^ 2 * Phi D w u) =
      fun u => ∑ j ∈ range (D + 1), w j * ((u + a) ^ 2 * pk j u) := by
    funext u
    simp only [Phi, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, integral_finsetSum _ fun j _ => (integrableOn_sq_mul_pk a j).const_mul (w j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_sq_mul_pk]

end

end OptimalPrecision.ExpPoly
