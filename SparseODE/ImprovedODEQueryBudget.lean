import SparseODE.ODESourceQuadrature

/-!
# Improved ODE query-budget arithmetic

This fragment converts an explicitly supplied selected-Hamiltonian query
certificate to the improved ODE bound. It does not construct the Gaussian
quadrature, the common coherent schedule, or amplitude amplification.
The convenient radius below dominates the exact Gaussian cutoff.

-/

namespace SparseHamiltonian.ImprovedODEQueryBudget

noncomputable section

/-- Accuracy allocated to each approximation in the improved ODE construction. -/
def precision (g ε : ℝ) : ℝ := ε / (10000 * g)

/-- The sole logarithmic envelope; it has no sparsity or duration dependence. -/
def logBudget (g ε : ℝ) : ℝ := Real.log (10000 * g / ε)

/-- A public cutoff dominating the Gaussian LCHS radius. -/
def radius (g ε : ℝ) : ℝ := 4 * Real.log (20000 * g / ε)

/-- Logarithm entering the improved Hamiltonian simulation theorem. -/
def simulationLog (g ε : ℝ) : ℝ := Real.log (2 / precision g ε)

/-- Dissipative and skew-Hermitian contributions to the ODE time budget. -/
def theta (τH τD g ε : ℝ) : ℝ := τH + τD * logBudget g ε

/-- Largest selected Hamiltonian duration at the convenient cutoff. -/
def effectiveTime (τH τD g ε : ℝ) : ℝ := τH + radius g ε * τD

/-- The three terms of the improved Hamiltonian query bound. -/
def queryShape (s u L : ℝ) : ℝ :=
  Real.sqrt s * u + Real.sqrt (s * u * L) + L

theorem precision_pos (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) :
    0 < precision g ε := by
  have hg0 : 0 < g := by linarith
  unfold precision
  positivity

theorem precision_le_one_ten_thousandth (g ε : ℝ)
    (hg : 1 ≤ g) (hε1 : ε ≤ 1) :
    precision g ε ≤ 1 / 10000 := by
  have hg0 : 0 < g := by linarith
  unfold precision
  apply (div_le_iff₀ (by positivity : 0 < 10000 * g)).2
  nlinarith

/-- The selected errors lie inside all three quoted LCHS validity ranges. -/
theorem precision_validity (g ε : ℝ) (hg : 1 ≤ g)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < precision g ε ∧ precision g ε ≤ 0.9027 ∧
      precision g ε ≤ 4 / 15 ∧ precision g ε ≤ 4 / 5 := by
  have h := precision_le_one_ten_thousandth g ε hg hε1
  exact ⟨precision_pos g ε hg hε, by linarith, by linarith, by linarith⟩

theorem logArgument_ge (g ε : ℝ) (hg : 1 ≤ g)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    10000 ≤ 10000 * g / ε := by
  apply (le_div_iff₀ hε).2
  linarith

theorem logBudget_ge_one (g ε : ℝ) (hg : 1 ≤ g)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ logBudget g ε := by
  have harg := logArgument_ge g ε hg hε hε1
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
    (show 4 ≤ 10000 * g / ε by linarith)
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using
      Real.log_pow (2 : ℝ) 2
  rw [hfour] at hlog
  unfold logBudget
  linarith [ODEQueryBudget.log_two_ge_half]

theorem simulationLog_eq (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) :
    simulationLog g ε = Real.log 2 + logBudget g ε := by
  have hg0 : 0 < g := by linarith
  have harg : 0 < 10000 * g / ε := by positivity
  have heq : 2 / precision g ε = 2 * (10000 * g / ε) := by
    unfold precision
    field_simp [hg0.ne', hε.ne']
  unfold simulationLog logBudget
  rw [heq, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) harg.ne']

theorem simulationLog_le (g ε : ℝ) (hg : 1 ≤ g)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    simulationLog g ε ≤ 2 * logBudget g ε := by
  rw [simulationLog_eq g ε hg hε]
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith [logBudget_ge_one g ε hg hε hε1]

theorem simulationLog_nonneg (g ε : ℝ) (hg : 1 ≤ g)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ simulationLog g ε := by
  rw [simulationLog_eq g ε hg hε]
  linarith [logBudget_ge_one g ε hg hε hε1, ODEQueryBudget.log_two_ge_half]

theorem radius_eq (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) :
    radius g ε = 4 * simulationLog g ε := by
  have hg0 : 0 < g := by linarith
  have heq : 20000 * g / ε = 2 / precision g ε := by
    unfold precision
    field_simp [hg0.ne', hε.ne']
    ring
  unfold radius simulationLog
  rw [heq]

theorem radius_nonneg (g ε : ℝ) (hg : 1 ≤ g)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ radius g ε := by
  rw [radius_eq g ε hg hε]
  have h := simulationLog_nonneg g ε hg hε hε1
  positivity

theorem radius_le (g ε : ℝ) (hg : 1 ≤ g)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    radius g ε ≤ 8 * logBudget g ε := by
  rw [radius_eq g ε hg hε]
  linarith [simulationLog_le g ε hg hε hε1]

/-- The chosen public radius contains the exact Gaussian cutoff used in the
manuscript. The additional constant factor does not change its complexity. -/
theorem gaussian_radius_le (g ε : ℝ) (hg : 1 ≤ g)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    2 * (1 + Real.log ((1 + 1 / (2 * Real.pi)) / precision g ε)) ≤
      radius g ε := by
  have hν := precision_pos g ε hg hε
  have hpi : 0 < 2 * Real.pi := by positivity
  have hinv : 1 / (2 * Real.pi) ≤ 1 :=
    (div_le_one hpi).2 (by linarith [Real.two_le_pi])
  have harg : (1 + 1 / (2 * Real.pi)) / precision g ε ≤ 2 / precision g ε :=
    div_le_div_of_nonneg_right (by linarith) hν.le
  have hl := Real.log_le_log (by positivity :
    (0 : ℝ) < (1 + 1 / (2 * Real.pi)) / precision g ε) harg
  have hL : 1 ≤ simulationLog g ε := by
    rw [simulationLog_eq g ε hg hε]
    linarith [logBudget_ge_one g ε hg hε hε1, ODEQueryBudget.log_two_ge_half]
  rw [radius_eq g ε hg hε]
  change Real.log ((1 + 1 / (2 * Real.pi)) / precision g ε) ≤
    simulationLog g ε at hl
  linarith

theorem theta_nonneg (τH τD g ε : ℝ) (hH : 0 ≤ τH) (hD : 0 ≤ τD)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ theta τH τD g ε := by
  have hL : 0 ≤ logBudget g ε := by linarith [logBudget_ge_one g ε hg hε hε1]
  unfold theta
  positivity

theorem effectiveTime_nonneg (τH τD g ε : ℝ)
    (hH : 0 ≤ τH) (hD : 0 ≤ τD)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ effectiveTime τH τD g ε := by
  have hR := radius_nonneg g ε hg hε hε1
  unfold effectiveTime
  positivity

theorem effectiveTime_le (τH τD g ε : ℝ)
    (hH : 0 ≤ τH) (hD : 0 ≤ τD)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    effectiveTime τH τD g ε ≤ 8 * theta τH τD g ε := by
  have hR := mul_le_mul_of_nonneg_right (radius_le g ε hg hε hε1) hD
  unfold effectiveTime theta
  nlinarith

/-- All retained nodes and all shorter nonnegative durations satisfy the same
public effective-time bound. This is not a coherent-schedule construction. -/
theorem branch_effectiveTime_le (T u ηH ηD k g ε : ℝ)
    (hu : 0 ≤ u) (huT : u ≤ T) (hH : 0 ≤ ηH) (hD : 0 ≤ ηD)
    (hk : |k| ≤ radius g ε) :
    u * (ηH + |k| * ηD) ≤ effectiveTime (T * ηH) (T * ηD) g ε := by
  have hT : 0 ≤ T := hu.trans huT
  have hR : 0 ≤ radius g ε := (abs_nonneg k).trans hk
  calc
    _ ≤ T * (ηH + |k| * ηD) :=
      mul_le_mul_of_nonneg_right huT (by positivity)
    _ ≤ T * (ηH + radius g ε * ηD) := by gcongr
    _ = _ := by unfold effectiveTime; ring

theorem queryShape_nonneg (s u L : ℝ) (hu : 0 ≤ u) (hL : 0 ≤ L) :
    0 ≤ queryShape s u L := by
  unfold queryShape
  positivity

/-- A scalar conversion lemma retaining the square-root mixed term rather
than replacing it by a higher power of the precision logarithm. -/
theorem tagged_shape_le (s u L Θ ℓ : ℝ)
    (hs : 0 ≤ s) (hu : 0 ≤ u) (hL : 0 ≤ L)
    (hΘ : 0 ≤ Θ) (hℓ : 0 ≤ ℓ)
    (huΘ : u ≤ 8 * Θ) (hLℓ : L ≤ 2 * ℓ) :
    queryShape (2 * s) u L ≤ 16 * queryShape s Θ ℓ := by
  have hsqrt : Real.sqrt (2 * s) ≤ 2 * Real.sqrt s := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [Real.sq_sqrt hs]
  have hfirst : Real.sqrt (2 * s) * u ≤ 16 * (Real.sqrt s * Θ) := by
    calc
      _ ≤ (2 * Real.sqrt s) * (8 * Θ) := by gcongr
      _ = _ := by ring
  have hrad : (2 * s) * u * L ≤ 32 * (s * Θ * ℓ) := by
    calc
      _ ≤ (2 * s) * (8 * Θ) * (2 * ℓ) := by gcongr
      _ = _ := by ring
  have hroot : Real.sqrt (32 * (s * Θ * ℓ)) ≤ 8 * Real.sqrt (s * Θ * ℓ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hz : 0 ≤ s * Θ * ℓ := by positivity
      nlinarith [Real.sq_sqrt hz]
  have hmiddle : Real.sqrt ((2 * s) * u * L) ≤ 8 * Real.sqrt (s * Θ * ℓ) :=
    (Real.sqrt_le_sqrt hrad).trans hroot
  have hn1 : 0 ≤ Real.sqrt s * Θ := by positivity
  have hn2 : 0 ≤ Real.sqrt (s * Θ * ℓ) := Real.sqrt_nonneg _
  unfold queryShape
  linarith

/-- The improved selected-Hamiltonian resource expression has one common
logarithmic envelope, independent of sparsity and duration. -/
theorem selected_shape_le (s τH τD g ε : ℝ)
    (hs : 0 ≤ s) (hH : 0 ≤ τH) (hD : 0 ≤ τD)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    queryShape (2 * s) (effectiveTime τH τD g ε) (simulationLog g ε) ≤
      16 * queryShape s (theta τH τD g ε) (logBudget g ε) := by
  exact tagged_shape_le s _ _ _ _ hs
    (effectiveTime_nonneg τH τD g ε hH hD hg hε hε1)
    (simulationLog_nonneg g ε hg hε hε1)
    (theta_nonneg τH τD g ε hH hD hg hε hε1)
    (by linarith [logBudget_ge_one g ε hg hε hε1])
    (effectiveTime_le τH τD g ε hH hD hg hε hε1)
    (simulationLog_le g ε hg hε hε1)

/-- Conditional query accounting: a separate program theorem must supply
`hq`, including the coherent schedule and original-oracle compilation. -/
theorem selected_query_bound (C q s τH τD g ε : ℝ)
    (hC : 0 ≤ C) (hs : 0 ≤ s) (hH : 0 ≤ τH) (hD : 0 ≤ τD)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hq : q ≤ C * queryShape (2 * s) (effectiveTime τH τD g ε)
      (simulationLog g ε)) :
    q ≤ 16 * C * queryShape s (theta τH τD g ε) (logBudget g ε) := by
  have h := mul_le_mul_of_nonneg_left
    (selected_shape_le s τH τD g ε hs hH hD hg hε hε1) hC
  calc
    q ≤ C * queryShape (2 * s) (effectiveTime τH τD g ε) (simulationLog g ε) := hq
    _ ≤ C * (16 * queryShape s (theta τH τD g ε) (logBudget g ε)) := h
    _ = _ := by ring

/-- Conditional accounting for an explicitly certified `M*g` repetition cost.
This lemma makes no amplitude-amplification implementation claim. -/
theorem amplified_query_bound (M C q s τH τD g ε : ℝ)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hs : 0 ≤ s) (hH : 0 ≤ τH) (hD : 0 ≤ τD)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hq : q ≤ C * queryShape (2 * s) (effectiveTime τH τD g ε)
      (simulationLog g ε)) :
    M * g * q ≤ 16 * M * C * g *
      queryShape s (theta τH τD g ε) (logBudget g ε) := by
  have hg0 : 0 ≤ g := by linarith
  have h := mul_le_mul_of_nonneg_left
    (selected_query_bound C q s τH τD g ε hC hs hH hD hg hε hε1 hq)
    (show 0 ≤ M * g by positivity)
  calc
    _ ≤ M * g * (16 * C * queryShape s (theta τH τD g ε) (logBudget g ε)) := h
    _ = _ := by ring

/-- When one common row/column energy bound is used for both components,
the logarithmic envelope factors out with only a constant loss. -/
theorem common_shape_le (s τ g ε : ℝ) (hs : 0 ≤ s) (hτ : 0 ≤ τ)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    queryShape s (theta τ τ g ε) (logBudget g ε) ≤
      2 * (Real.sqrt s * (τ + Real.sqrt τ) + 1) * logBudget g ε := by
  have hℓ := logBudget_ge_one g ε hg hε hε1
  have hℓ0 : 0 ≤ logBudget g ε := by linarith
  have hΘ : theta τ τ g ε ≤ 2 * τ * logBudget g ε := by
    have hm := mul_le_mul_of_nonneg_left hℓ hτ
    unfold theta
    nlinarith
  have hfirst : Real.sqrt s * theta τ τ g ε ≤
      2 * Real.sqrt s * τ * logBudget g ε := by
    calc
      _ ≤ Real.sqrt s * (2 * τ * logBudget g ε) :=
        mul_le_mul_of_nonneg_left hΘ (Real.sqrt_nonneg s)
      _ = _ := by ring
  have hmiddle : Real.sqrt (s * theta τ τ g ε * logBudget g ε) ≤
      2 * Real.sqrt s * Real.sqrt τ * logBudget g ε := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · have hrad : s * theta τ τ g ε * logBudget g ε ≤
          s * (2 * τ * logBudget g ε) * logBudget g ε := by gcongr
      have hsq : (2 * Real.sqrt s * Real.sqrt τ * logBudget g ε) ^ 2 =
          4 * s * τ * (logBudget g ε) ^ 2 := by
        simp only [mul_pow, Real.sq_sqrt hs, Real.sq_sqrt hτ]
        ring
      rw [hsq]
      have hz : 0 ≤ s * τ * (logBudget g ε) ^ 2 := by positivity
      nlinarith
  unfold queryShape
  nlinarith

/-- The explicit Hamiltonian theorem constant may be substituted without
changing the conditional status of the selected-program premise. -/
theorem native_selected_query_bound (q s τH τD g ε : ℝ)
    (hs : 0 ≤ s) (hH : 0 ≤ τH) (hD : 0 ≤ τD)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hq : q ≤ 497664 * queryShape (2 * s) (effectiveTime τH τD g ε)
      (simulationLog g ε)) :
    q ≤ 7962624 * queryShape s (theta τH τD g ε) (logBudget g ε) := by
  convert selected_query_bound 497664 q s τH τD g ε (by norm_num)
    hs hH hD hg hε hε1 hq using 1; norm_num

/-- With no dissipative component, the time budget retains the improved
Hamiltonian form exactly. -/
theorem theta_zero_dissipation (τH g ε : ℝ) :
    theta τH 0 g ε = τH := by
  simp [theta]

end
end SparseHamiltonian.ImprovedODEQueryBudget
