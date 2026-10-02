import SparseHamiltonian.ODECoherentLCU

/-!
# Scalar precision and query budgets for the ODE solver

This module proves arithmetic estimates used by the proposed LCHS reduction.
It does not assert an LCHS representation, coherent Hamiltonian implementation,
or amplitude-amplification algorithm. Those constructions must supply the
hypotheses of the final conditional resource inequality.

The accumulated time parameter `a` can be instantiated by `T * η`. Constants
are deliberately generous. All logarithms in the public envelope are natural.
-/
namespace SparseHamiltonian.ODEQueryBudget

noncomputable section

/-- Accuracy allocated to each linear-combination approximation. -/
def precision (g ε : ℝ) : ℝ := ε / (1000 * g)

/-- A convenient radius that dominates the Gaussian LCHS cutoff. -/
def radius (g ε : ℝ) : ℝ := 4 * Real.log (2000 * g / ε)

/-- Common logarithmic envelope for the cutoff and Hamiltonian precision. -/
def logArgument (s a g ε : ℝ) : ℝ := 1000000 * (s + 1) * (1 + a) * g / ε

def logBudget (s a g ε : ℝ) : ℝ := Real.log (logArgument s a g ε) + 1

/-- Largest effective simulation duration after the LCHS Hermitian dilation. -/
def effectiveTime (a g ε : ℝ) : ℝ := 1 + a * Real.sqrt (1 + radius g ε ^ 2)

/-- The logarithmic factor appearing in the verified Hamiltonian query bound. -/
def simulationLog (s a g ε : ℝ) : ℝ :=
  Real.log (120 * effectiveTime a g ε * (s + 1) / precision g ε) / Real.log 2 + 1

theorem precision_pos (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) :
    0 < precision g ε := by
  have hg0 : 0 < g := by linarith
  unfold precision
  positivity

theorem precision_le_one_thousandth (g ε : ℝ) (hg : 1 ≤ g) (hε1 : ε ≤ 1) :
    precision g ε ≤ 1 / 1000 := by
  have hg0 : 0 < g := by linarith
  unfold precision
  apply (div_le_iff₀ (by positivity : 0 < 1000 * g)).2
  nlinarith

/-- The standard LCHS, quadrature, and block-encoding validity ranges all
contain this chosen precision. -/
theorem precision_validity (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < precision g ε ∧ precision g ε ≤ 0.9027 ∧
      precision g ε ≤ 4 / 15 ∧ precision g ε ≤ 4 / 5 := by
  have h := precision_le_one_thousandth g ε hg hε1
  exact ⟨precision_pos g ε hg hε, by linarith, by linarith, by linarith⟩

theorem log_two_ge_half : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  norm_num at h ⊢
  exact h

theorem cutoff_argument_ge (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    2000 ≤ 2000 * g / ε := by
  apply (le_div_iff₀ hε).2
  linarith

theorem cutoff_log_ge_one (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ Real.log (2000 * g / ε) := by
  have harg := cutoff_argument_ge g ε hg hε hε1
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 4)
    (show 4 ≤ 2000 * g / ε by linarith)
  have hfour : Real.log 4 = 2 * Real.log 2 := by
    simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using
      Real.log_pow (2 : ℝ) 2
  rw [hfour] at hlog
  linarith [log_two_ge_half]

theorem radius_nonneg (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ radius g ε := by
  unfold radius
  linarith [cutoff_log_ge_one g ε hg hε hε1]

/-- The convenient cutoff dominates the exact radius at the chosen precision
in the `c = 1` Gaussian LCHS parameter selection. -/
theorem gaussian_radius_le (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    2 * (1 + Real.log ((1 + 1 / (2 * Real.pi)) / precision g ε)) ≤ radius g ε := by
  have hν := precision_pos g ε hg hε
  have hg0 : 0 < g := by linarith
  have hpi : 0 < 2 * Real.pi := by positivity
  have hinv : 1 / (2 * Real.pi) ≤ 1 :=
    (div_le_one hpi).2 (by linarith [Real.two_le_pi])
  have harg : (1 + 1 / (2 * Real.pi)) / precision g ε ≤ 2000 * g / ε := by
    calc
      _ ≤ 2 / precision g ε := div_le_div_of_nonneg_right (by linarith) hν.le
      _ = _ := by unfold precision; field_simp [hg0.ne', hε.ne']; ring
  have hl := Real.log_le_log (by positivity :
    (0 : ℝ) < (1 + 1 / (2 * Real.pi)) / precision g ε) harg
  have hlog := cutoff_log_ge_one g ε hg hε hε1
  unfold radius
  linarith

theorem logArgument_ge_cutoff (s a g ε : ℝ) (hs : 1 ≤ s) (ha : 0 ≤ a)
    (hg : 1 ≤ g) (hε : 0 < ε) :
    2000 * g / ε ≤ logArgument s a g ε := by
  have hg0 : 0 ≤ g := by linarith
  have hsa : 2 ≤ (s + 1) * (1 + a) := by
    nlinarith [mul_nonneg (show 0 ≤ s + 1 by linarith) ha]
  unfold logArgument
  apply div_le_div_of_nonneg_right _ hε.le
  have h := mul_le_mul_of_nonneg_right hsa hg0
  nlinarith

theorem logArgument_pos (s a g ε : ℝ) (hs : 1 ≤ s) (ha : 0 ≤ a)
    (hg : 1 ≤ g) (hε : 0 < ε) :
    0 < logArgument s a g ε := by
  have hg0 : 0 < g := by linarith
  have hs0 : 0 < s + 1 := by linarith
  unfold logArgument
  positivity

theorem logBudget_ge_one (s a g ε : ℝ) (hs : 1 ≤ s) (ha : 0 ≤ a)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ logBudget s a g ε := by
  have harg := (cutoff_argument_ge g ε hg hε hε1).trans
    (logArgument_ge_cutoff s a g ε hs ha hg hε)
  have hl := Real.log_nonneg (show 1 ≤ logArgument s a g ε by linarith)
  unfold logBudget
  linarith

theorem radius_le_logBudget (s a g ε : ℝ) (hs : 1 ≤ s) (ha : 0 ≤ a)
    (hg : 1 ≤ g) (hε : 0 < ε) :
    radius g ε ≤ 4 * logBudget s a g ε := by
  have hg0 : 0 < g := by linarith
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 2000 * g / ε)
    (logArgument_ge_cutoff s a g ε hs ha hg hε)
  unfold radius logBudget
  linarith

theorem effectiveTime_ge_one (a g ε : ℝ) (ha : 0 ≤ a) :
    1 ≤ effectiveTime a g ε := by
  unfold effectiveTime
  have h := mul_nonneg ha (Real.sqrt_nonneg (1 + radius g ε ^ 2))
  linarith

/-- One public effective-time bound covers all retained LCHS nodes and all
shorter durations. This is arithmetic only; coherent use requires a common
query schedule. -/
theorem branch_effectiveTime_le (a τ k g ε : ℝ) (hτ : 0 ≤ τ) (hτa : τ ≤ a)
    (hk : |k| ≤ radius g ε) :
    1 + τ * Real.sqrt (1 + k ^ 2) ≤ effectiveTime a g ε := by
  have ha : 0 ≤ a := hτ.trans hτa
  have hR : 0 ≤ radius g ε := (abs_nonneg k).trans hk
  have hsq : k ^ 2 ≤ radius g ε ^ 2 := by
    calc
      k ^ 2 = |k| ^ 2 := (sq_abs k).symm
      _ ≤ radius g ε ^ 2 := pow_le_pow_left₀ (abs_nonneg k) hk 2
  have hsqrt := Real.sqrt_le_sqrt (show 1 + k ^ 2 ≤ 1 + radius g ε ^ 2 by linarith)
  unfold effectiveTime
  gcongr

/-- Radius growth costs only one further logarithmic factor in the effective time. -/
theorem effectiveTime_le (s a g ε : ℝ) (hs : 1 ≤ s) (ha : 0 ≤ a)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    effectiveTime a g ε ≤ 6 * (1 + a) * logBudget s a g ε := by
  have hR := radius_nonneg g ε hg hε hε1
  have hRle := radius_le_logBudget s a g ε hs ha hg hε
  have hB := logBudget_ge_one s a g ε hs ha hg hε hε1
  have hsqrt : Real.sqrt (1 + radius g ε ^ 2) ≤ 1 + radius g ε := by
    apply (Real.sqrt_le_iff).2
    constructor
    · linarith
    · nlinarith
  unfold effectiveTime
  have ht := mul_le_mul_of_nonneg_left hsqrt ha
  have hRmul := mul_le_mul_of_nonneg_left hRle ha
  have hBa : a ≤ a * logBudget s a g ε := by nlinarith
  nlinarith

/-- The logarithm inside the Hamiltonian bound is absorbed by the same envelope. -/
theorem simulationLog_le (s a g ε : ℝ) (hs : 1 ≤ s) (ha : 0 ≤ a)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    simulationLog s a g ε ≤ 4 * logBudget s a g ε := by
  have hν := precision_pos g ε hg hε
  have hE := effectiveTime_ge_one a g ε ha
  have hB := logBudget_ge_one s a g ε hs ha hg hε hε1
  have hA := logArgument_pos s a g ε hs ha hg hε
  have hEup := effectiveTime_le s a g ε hs ha hg hε hε1
  have hs0 : 0 < s + 1 := by linarith
  have hg0 : 0 < g := by linarith
  have harg : 120 * effectiveTime a g ε * (s + 1) / precision g ε ≤
      logArgument s a g ε * logBudget s a g ε := by
    have hcoefficient : 120000 * effectiveTime a g ε ≤
        1000000 * (1 + a) * logBudget s a g ε := by
      have hnonneg : 0 ≤ (1 + a) * logBudget s a g ε := by positivity
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_right hcoefficient
      (show 0 ≤ (s + 1) * g / ε by positivity)
    calc
      _ = (120000 * effectiveTime a g ε) * ((s + 1) * g / ε) := by
        unfold precision
        field_simp [hg0.ne', hε.ne']; ring
      _ ≤ (1000000 * (1 + a) * logBudget s a g ε) * ((s + 1) * g / ε) := hscaled
      _ = _ := by unfold logArgument; ring
  have hl := Real.log_le_log (by positivity :
    (0 : ℝ) < 120 * effectiveTime a g ε * (s + 1) / precision g ε) harg
  rw [Real.log_mul hA.ne' (by linarith : logBudget s a g ε ≠ 0)] at hl
  have hlB := Real.log_le_sub_one_of_pos (show 0 < logBudget s a g ε by linarith)
  have hlA : Real.log (logArgument s a g ε) = logBudget s a g ε - 1 := by
    unfold logBudget
    ring
  rw [hlA] at hl
  have hlog : Real.log (120 * effectiveTime a g ε * (s + 1) / precision g ε) ≤
      2 * logBudget s a g ε - 2 := by linarith
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold simulationLog
  have hdiv : Real.log (120 * effectiveTime a g ε * (s + 1) / precision g ε) /
      Real.log 2 ≤ 4 * logBudget s a g ε - 1 := by
    apply (div_le_iff₀ hd).2
    have hmul := mul_le_mul_of_nonneg_left log_two_ge_half
      (show 0 ≤ 4 * logBudget s a g ε - 1 by linarith)
    nlinarith
  linarith

/-- The logarithmic factor is nonnegative, as needed when squaring its bound. -/
theorem simulationLog_nonneg (s a g ε : ℝ) (hs : 1 ≤ s) (ha : 0 ≤ a)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ simulationLog s a g ε := by
  have hν := precision_pos g ε hg hε
  have hν1 := precision_le_one_thousandth g ε hg hε1
  have hE := effectiveTime_ge_one a g ε ha
  have harg : 1 ≤ 120 * effectiveTime a g ε * (s + 1) / precision g ε := by
    apply (le_div_iff₀ hν).2
    have hprod : 2 ≤ effectiveTime a g ε * (s + 1) := by nlinarith
    nlinarith
  have hl := Real.log_nonneg harg
  have hd : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold simulationLog
  positivity

/-- Scalar conversion of a selected-Hamiltonian query certificate to the ODE
log-cubed budget. `C` can be the explicit Hamiltonian simulation constant.
This theorem makes no assertion that a coherent SELECT circuit has yet been
constructed. -/
theorem selected_query_bound (C s a g ε : ℝ) (hC : 0 ≤ C)
    (hs : 1 ≤ s) (ha : 0 ≤ a) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    C * effectiveTime a g ε * Real.sqrt s * simulationLog s a g ε ^ 2 ≤
      96 * C * (1 + a) * Real.sqrt s * logBudget s a g ε ^ 3 := by
  have hE := effectiveTime_le s a g ε hs ha hg hε hε1
  have hL := simulationLog_le s a g ε hs ha hg hε hε1
  have hL0 := simulationLog_nonneg s a g ε hs ha hg hε hε1
  have hB := logBudget_ge_one s a g ε hs ha hg hε hε1
  have hsqrt := Real.sqrt_nonneg s
  have hLsq : simulationLog s a g ε ^ 2 ≤ 16 * logBudget s a g ε ^ 2 := by
    nlinarith
  calc
    _ ≤ C * (6 * (1 + a) * logBudget s a g ε) * Real.sqrt s *
        simulationLog s a g ε ^ 2 := by gcongr
    _ ≤ C * (6 * (1 + a) * logBudget s a g ε) * Real.sqrt s *
        (16 * logBudget s a g ε ^ 2) := by gcongr
    _ = _ := by ring

/-- Instantiation with the explicit constant from the verified native sparse
Hamiltonian simulation theorem. -/
theorem native_selected_query_bound (s a g ε : ℝ)
    (hs : 1 ≤ s) (ha : 0 ≤ a) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    2235174912 * effectiveTime a g ε * Real.sqrt s * simulationLog s a g ε ^ 2 ≤
      214576791552 * (1 + a) * Real.sqrt s * logBudget s a g ε ^ 3 := by
  convert selected_query_bound 2235174912 s a g ε (by norm_num)
    hs ha hg hε hε1 using 1; norm_num

/-- Conditional scalar accounting for `M * g` uses of a selected Hamiltonian
implementation. A separate algorithmic theorem must certify that use count. -/
theorem amplified_query_bound (M C q s a g ε : ℝ) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hs : 1 ≤ s) (ha : 0 ≤ a) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hq : q ≤ C * effectiveTime a g ε * Real.sqrt s * simulationLog s a g ε ^ 2) :
    M * g * q ≤ 96 * M * C * g * (1 + a) * Real.sqrt s * logBudget s a g ε ^ 3 := by
  have h := hq.trans (selected_query_bound C s a g ε hC hs ha hg hε hε1)
  have hmul := mul_le_mul_of_nonneg_left h (show 0 ≤ M * g by positivity)
  calc
    _ ≤ M * g * (96 * C * (1 + a) * Real.sqrt s * logBudget s a g ε ^ 3) := hmul
    _ = _ := by ring

end
end SparseHamiltonian.ODEQueryBudget
