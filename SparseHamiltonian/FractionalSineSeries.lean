import SparseHamiltonian.FractionalAngleSeriesDifferentiation

/-!
# Analytic target and uniqueness for fractional-angle series

The explicit target solves the fractional Chebyshev differential equation with
initial values zero and one. A conserved-energy argument proves uniqueness
on the open unit interval. Power-series convergence and termwise differentiation
remain separate obligations, rather than assumptions identifying the target.
-/
namespace SparseHamiltonian.FractionalSineSeries
noncomputable section

/-- Fractional-angle target, normalized to have slope one at zero. -/
def target (a y : ℝ) : ℝ := Real.sin (a * Real.arcsin y) / a

/-- Explicit first derivative on the open unit interval. -/
def slope (a y : ℝ) : ℝ := Real.cos (a * Real.arcsin y) / Real.sqrt (1 - y ^ 2)

/-- Explicit second derivative on the open unit interval. -/
def curvature (a y : ℝ) : ℝ :=
  y * Real.cos (a * Real.arcsin y) / Real.sqrt (1 - y ^ 2) ^ 3 -
    a * Real.sin (a * Real.arcsin y) / (1 - y ^ 2)

@[simp] theorem target_zero (a : ℝ) : target a 0 = 0 := by simp [target]

@[simp] theorem slope_zero (a : ℝ) : slope a 0 = 1 := by simp [slope]

theorem target_odd (a : ℝ) : Function.Odd (target a) := by
  intro y
  simp [target, Real.arcsin_neg, Real.sin_neg, neg_div]

theorem radicand_pos (y : ℝ) (hy : |y| < 1) : 0 < 1 - y ^ 2 := by
  have h := abs_lt.mp hy
  nlinarith

theorem hasDerivAt_target (a y : ℝ) (ha : a ≠ 0) (hy : |y| < 1) :
    HasDerivAt (target a) (slope a y) y := by
  have hm : y ≠ -1 := by have h := abs_lt.mp hy; linarith
  have hp : y ≠ 1 := by have h := abs_lt.mp hy; linarith
  have h := (((Real.hasDerivAt_arcsin hm hp).const_mul a).sin).div_const a
  convert h using 1 <;> try rfl
  simp only [slope]
  field_simp

theorem hasDerivAt_slope (a y : ℝ) (hy : |y| < 1) :
    HasDerivAt (slope a) (curvature a y) y := by
  have hm : y ≠ -1 := by have h := abs_lt.mp hy; linarith
  have hp : y ≠ 1 := by have h := abs_lt.mp hy; linarith
  have hd : 0 < 1 - y ^ 2 := radicand_pos y hy
  have hs : Real.sqrt (1 - y ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have hden : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-2 * y) y := by
    convert ((hasDerivAt_id y).pow 2).const_sub (1 : ℝ) using 1 <;> first | rfl | norm_num
  have hroot := hden.sqrt hd.ne'
  have hcos := ((Real.hasDerivAt_arcsin hm hp).const_mul a).cos
  have h := hcos.div hroot hs
  convert h using 1 <;> try rfl
  simp only [curvature]
  have hs2 := Real.sq_sqrt hd.le
  field_simp
  rw [pow_succ _ 2, hs2]
  ring

/-- The target satisfies the differential equation that generates the coefficient recurrence. -/
theorem target_ode (a y : ℝ) (hy : |y| < 1) :
    (1 - y ^ 2) * curvature a y - y * slope a y + a ^ 2 * target a y = 0 := by
  have hd : 0 < 1 - y ^ 2 := radicand_pos y hy
  have hs : Real.sqrt (1 - y ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  have hs2 := Real.sq_sqrt hd.le
  unfold curvature slope target
  field_simp
  rw [hs2]
  ring

/-- Conserved energy of a solution to the homogeneous fractional Chebyshev equation. -/
def energy (a : ℝ) (f g : ℝ → ℝ) (y : ℝ) : ℝ :=
  (1 - y ^ 2) * (g y) ^ 2 + a ^ 2 * (f y) ^ 2

/-- The energy derivative vanishes by exactly the displayed differential equation. -/
theorem hasDerivAt_energy (a y : ℝ) (f g h : ℝ → ℝ)
    (hf : HasDerivAt f (g y) y) (hg : HasDerivAt g (h y) y)
    (hode : (1 - y ^ 2) * h y - y * g y + a ^ 2 * f y = 0) :
    HasDerivAt (energy a f g) 0 y := by
  have hden : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-2 * y) y := by
    convert ((hasDerivAt_id y).pow 2).const_sub (1 : ℝ) using 1 <;> first | rfl | norm_num
  have he := (hden.mul (hg.pow 2)).add ((hf.pow 2).const_mul (a ^ 2))
  convert he using 1 <;> try rfl
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  calc
    0 = 2 * g y * ((1 - y ^ 2) * h y - y * g y + a ^ 2 * f y) := by rw [hode]; ring
    _ = _ := by ring

/-- Zero initial data force the only homogeneous solution to vanish on `(-1,1)`.
No general ODE uniqueness theorem or numerical error estimate is assumed. -/
theorem homogeneous_unique (a : ℝ) (ha : a ≠ 0) (f g h : ℝ → ℝ)
    (hf : ∀ y, |y| < 1 → HasDerivAt f (g y) y)
    (hg : ∀ y, |y| < 1 → HasDerivAt g (h y) y)
    (hode : ∀ y, |y| < 1 → (1 - y ^ 2) * h y - y * g y + a ^ 2 * f y = 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (y : ℝ) (hy : |y| < 1) : f y = 0 := by
  have he (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) : HasDerivAt (energy a f g) 0 t :=
    hasDerivAt_energy a t f g h (hf t (abs_lt.mpr ht)) (hg t (abs_lt.mpr ht))
      (hode t (abs_lt.mpr ht))
  have heq := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun t ht => (he t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (he t ht).deriv) (abs_lt.mp hy) (by norm_num : (0 : ℝ) ∈ Set.Ioo (-1) 1)
  have hz : energy a f g y = 0 := by simpa [energy, hf0, hg0] using heq
  have hn := mul_nonneg (radicand_pos y hy).le (sq_nonneg (g y))
  have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
  unfold energy at hz
  have hfy : (f y) ^ 2 = 0 := by nlinarith [sq_nonneg (f y)]
  exact sq_eq_zero_iff.mp hfy

/-- Any twice differentiable solution with the recurrence's initial data is the
explicit fractional-angle target. The remaining series bridge only needs
termwise derivatives and its coefficient recurrence. -/
theorem eq_target_of_ode (a : ℝ) (ha : a ≠ 0) (f g h : ℝ → ℝ)
    (hf : ∀ y, |y| < 1 → HasDerivAt f (g y) y)
    (hg : ∀ y, |y| < 1 → HasDerivAt g (h y) y)
    (hode : ∀ y, |y| < 1 → (1 - y ^ 2) * h y - y * g y + a ^ 2 * f y = 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 1) (y : ℝ) (hy : |y| < 1) :
    f y = target a y := by
  apply sub_eq_zero.mp
  apply homogeneous_unique a ha (fun t => f t - target a t)
    (fun t => g t - slope a t) (fun t => h t - curvature a t)
  · intro t ht
    exact (hf t ht).sub (hasDerivAt_target a t ha ht)
  · intro t ht
    exact (hg t ht).sub (hasDerivAt_slope a t ht)
  · intro t ht
    have h1 := hode t ht
    have h2 := target_ode a t ht
    nlinarith
  · simpa using hf0
  · simp [hg0]
  · exact hy

end
end SparseHamiltonian.FractionalSineSeries
