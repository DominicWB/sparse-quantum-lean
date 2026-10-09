import GeneralODE.Analysis.History
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

/-!
# Public parameters of the general ODE solver

All parameters are explicit functions of the public data `Λ, T, C̄, g, ε` and
of the solver's success bound `q₀`:

* `α = 8√2 Λ`, the normalisation of the native block encoding of `A`;
* `m = ⌈α T⌉` history steps of length `h = T/m`, so `α h ≤ 1` and `Λ h ≤ 1/8`;
* the common error budget `ϑ = ε / (1680 C̄ g)`;
* the Taylor degree `K = ⌈log₂ ⌈m/ϑ⌉⌉`, so `m 2^{-K} ≤ ϑ`;
* the arcsine degree `K + 1` and the simulation precision `ϑ / (4 m (K+1))`
  of the native block encoding;
* the condition-number bound `κ = 7 κ_H(m, 2, e, 2C̄) = O(C̄ m)` and the solver
  accuracy `δ = ε / (40 g)`;
* the amplification gain `5 g / √q₀`.

The lemmas below are the numerical facts used in the assembly.
-/

namespace SparseHamiltonian.GeneralODE.Plan

noncomputable section
open History
open scoped Nat

/-- Normalisation of the native block encoding of `A`. -/
def alpha (Λ : ℝ) : ℝ := 8 * Real.sqrt 2 * Λ

/-- Number of history steps. -/
def steps (Λ T : ℝ) : ℕ := ⌈alpha Λ * T⌉₊

/-- Common error budget. -/
def budget (Cbar g ε : ℝ) : ℝ := ε / (1680 * Cbar * g)

/-- Taylor degree. -/
def degree (Λ T Cbar g ε : ℝ) : ℕ := Nat.clog 2 ⌈(steps Λ T : ℝ) / budget Cbar g ε⌉₊

/-- Arcsine degree of the native block encoding. -/
def arcDegree (Λ T Cbar g ε : ℝ) : ℕ := degree Λ T Cbar g ε + 1

/-- Simulation precision of the native block encoding. -/
def nativeError (Λ T Cbar g ε : ℝ) : ℝ :=
  budget Cbar g ε / (4 * steps Λ T * (degree Λ T Cbar g ε + 1))

/-- Condition-number bound supplied to the solver. -/
def kappa (Λ T Cbar : ℝ) : ℝ := 7 * kappaH (steps Λ T) 2 (Real.exp 1) (2 * Cbar)

/-- Accuracy requested from the solver. -/
def delta (g ε : ℝ) : ℝ := ε / (40 * g)

/-- Extraction ratio after decoding. -/
def theta (g ε : ℝ) : ℝ := (1 - ε / 8) / (8 * g)

/-- Amplification gain. -/
def gain (g q₀ : ℝ) : ℝ := 5 * g / Real.sqrt q₀

section Facts

variable {Λ T Cbar g ε q₀ : ℝ}

theorem one_le_sqrt_two : 1 ≤ Real.sqrt 2 := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_le_sqrt (by norm_num)

theorem alpha_pos (hΛ : 0 < Λ) : 0 < alpha Λ := by
  have := one_le_sqrt_two
  unfold alpha
  positivity

theorem steps_pos (hΛ : 0 < Λ) (hT : 0 < T) : 1 ≤ steps Λ T := by
  unfold steps
  have h : 0 < alpha Λ * T := mul_pos (alpha_pos hΛ) hT
  exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr h).ne'

theorem alpha_mul_le (Λ T : ℝ) : alpha Λ * T ≤ steps Λ T := Nat.le_ceil _

theorem eight_mul_le (hΛ : 0 < Λ) (hT : 0 < T) : 8 * Λ * T ≤ steps Λ T := by
  refine le_trans ?_ (alpha_mul_le Λ T)
  unfold alpha
  have h := one_le_sqrt_two
  have h0 : 0 ≤ Λ * T := by positivity
  nlinarith

theorem budget_pos (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) : 0 < budget Cbar g ε := by
  unfold budget
  have : 0 < Cbar := by linarith
  have : 0 < g := by linarith
  positivity

theorem budget_mul (hC : 1 ≤ Cbar) (hg : 1 ≤ g) : 210 * Cbar * g * budget Cbar g ε = ε / 8 := by
  unfold budget
  have : Cbar ≠ 0 := by positivity
  have : g ≠ 0 := by positivity
  field_simp
  ring

theorem budget_le (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    budget Cbar g ε ≤ 1 := by
  unfold budget
  have h1 : 1 ≤ Cbar * g := by nlinarith
  rw [div_le_one (by positivity)]
  nlinarith

theorem steps_half_pow_le (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) :
    (steps Λ T : ℝ) * (1 / 2) ^ degree Λ T Cbar g ε ≤ budget Cbar g ε := by
  have hb := budget_pos hC hg hε
  set D := degree Λ T Cbar g ε with hD
  have h1 : (steps Λ T : ℝ) / budget Cbar g ε ≤ (⌈(steps Λ T : ℝ) / budget Cbar g ε⌉₊ : ℝ) :=
    Nat.le_ceil _
  have h2 : ⌈(steps Λ T : ℝ) / budget Cbar g ε⌉₊ ≤ 2 ^ D := Nat.le_pow_clog (by norm_num) _
  have h2' : (⌈(steps Λ T : ℝ) / budget Cbar g ε⌉₊ : ℝ) ≤ (2 : ℝ) ^ D := by exact_mod_cast h2
  have h3 : (steps Λ T : ℝ) ≤ budget Cbar g ε * 2 ^ D := by
    have h := h1.trans h2'
    rwa [div_le_iff₀ hb, mul_comm] at h
  have h4 : (1 / 2 : ℝ) ^ D * 2 ^ D = 1 := by rw [← mul_pow]; norm_num
  calc (steps Λ T : ℝ) * (1 / 2) ^ D ≤ budget Cbar g ε * 2 ^ D * (1 / 2) ^ D :=
        mul_le_mul_of_nonneg_right h3 (by positivity)
    _ = budget Cbar g ε := by rw [mul_assoc, mul_comm ((2 : ℝ) ^ D), h4, mul_one]

theorem nativeError_pos (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) :
    0 < nativeError Λ T Cbar g ε := by
  unfold nativeError
  have := budget_pos hC hg hε
  have : (1 : ℝ) ≤ steps Λ T := by exact_mod_cast steps_pos hΛ hT
  positivity

theorem nativeError_le (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 2) : nativeError Λ T Cbar g ε ≤ 1 := by
  unfold nativeError
  have hb := budget_pos hC hg hε
  have hb1 := budget_le hC hg hε hε1
  have hs : (1 : ℝ) ≤ steps Λ T := by exact_mod_cast steps_pos hΛ hT
  have hd : (0 : ℝ) ≤ degree Λ T Cbar g ε := Nat.cast_nonneg _
  rw [div_le_one (by positivity)]
  nlinarith

/-- `m K ε₀ ≤ ϑ` with `ε₀ = 2 ε_native`. -/
theorem budget_identity (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) :
    (steps Λ T : ℝ) * ((degree Λ T Cbar g ε : ℝ) * (2 * nativeError Λ T Cbar g ε)) ≤
      budget Cbar g ε := by
  have hb := budget_pos hC hg hε
  have hs : (0 : ℝ) < steps Λ T := by exact_mod_cast steps_pos hΛ hT
  set D : ℝ := (degree Λ T Cbar g ε : ℝ) with hD
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  have heq : (steps Λ T : ℝ) * (D * (2 * nativeError Λ T Cbar g ε)) =
      budget Cbar g ε * (D / (2 * (D + 1))) := by
    unfold nativeError
    rw [← hD]
    field_simp
    ring
  rw [heq]
  have h : D / (2 * (D + 1)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  nlinarith

/-- `m δ_U ≤ ϑ` with `δ_U = 2 ε_native + 4^{-(K+1)}/2`. -/
theorem budget_matrix (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) :
    (steps Λ T : ℝ) * (2 * nativeError Λ T Cbar g ε + (1 / 4) ^ arcDegree Λ T Cbar g ε / 2) ≤
      budget Cbar g ε := by
  have hb := budget_pos hC hg hε
  have hs : (0 : ℝ) < steps Λ T := by exact_mod_cast steps_pos hΛ hT
  have hhalf := steps_half_pow_le (Λ := Λ) (T := T) hC hg hε
  set D : ℝ := (degree Λ T Cbar g ε : ℝ) with hD
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  have h1 : (steps Λ T : ℝ) * (2 * nativeError Λ T Cbar g ε) = budget Cbar g ε / (2 * (D + 1)) := by
    unfold nativeError
    rw [← hD]
    field_simp
    ring
  have h1' : budget Cbar g ε / (2 * (D + 1)) ≤ budget Cbar g ε / 2 := by
    apply div_le_div_of_nonneg_left hb.le (by norm_num)
    linarith
  have h2 : (1 / 4 : ℝ) ^ arcDegree Λ T Cbar g ε ≤ (1 / 2) ^ degree Λ T Cbar g ε := by
    unfold arcDegree
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, ← pow_mul]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have h3 : (steps Λ T : ℝ) * ((1 / 4) ^ arcDegree Λ T Cbar g ε / 2) ≤ budget Cbar g ε / 2 := by
    have := mul_le_mul_of_nonneg_left h2 hs.le
    rw [mul_div_assoc']
    linarith
  rw [mul_add]
  linarith

/-- `m (Λh)^{K+1}/(K+1)! ≤ ϑ`. -/
theorem budget_taylor (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) :
    (steps Λ T : ℝ) * ((Λ * (T / steps Λ T)) ^ (degree Λ T Cbar g ε + 1) /
      ((degree Λ T Cbar g ε + 1) ! : ℝ)) ≤ budget Cbar g ε := by
  have hs : (0 : ℝ) < steps Λ T := by exact_mod_cast steps_pos hΛ hT
  have hhalf := steps_half_pow_le (Λ := Λ) (T := T) hC hg hε
  set D := degree Λ T Cbar g ε with hD
  set u := Λ * (T / steps Λ T) with hu
  have hu0 : 0 ≤ u := by positivity
  have hu8 : u ≤ 1 / 8 := by
    rw [hu, ← mul_div_assoc, div_le_iff₀ hs]
    have := eight_mul_le hΛ hT
    linarith
  have hpow : u ^ (D + 1) ≤ (1 / 2) ^ D := by
    calc u ^ (D + 1) ≤ (1 / 8) ^ (D + 1) := pow_le_pow_left₀ hu0 hu8 _
      _ ≤ (1 / 8) ^ D := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ ≤ (1 / 2) ^ D := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hfac : (1 : ℝ) ≤ ((D + 1) ! : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hdiv : u ^ (D + 1) / ((D + 1) ! : ℝ) ≤ (1 / 2) ^ D :=
    (div_le_self (by positivity) hfac).trans hpow
  calc (steps Λ T : ℝ) * (u ^ (D + 1) / ((D + 1) ! : ℝ)) ≤ (steps Λ T : ℝ) * (1 / 2) ^ D :=
        mul_le_mul_of_nonneg_left hdiv hs.le
    _ ≤ budget Cbar g ε := hhalf

theorem one_le_kappa (hC : 1 ≤ Cbar) : 1 ≤ kappa Λ T Cbar := by
  unfold kappa kappaH
  have he : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hm : (0 : ℝ) ≤ steps Λ T := Nat.cast_nonneg _
  have h1 : 0 ≤ 2 * Cbar * (2 * (steps Λ T : ℝ) + 1) * (2 + 2 ^ 2 * Real.exp 1) := by positivity
  linarith

theorem delta_pos (hg : 1 ≤ g) (hε : 0 < ε) : 0 < delta g ε := by
  unfold delta
  have : 0 < g := by linarith
  positivity

theorem delta_le (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) : delta g ε ≤ 1 / 2 := by
  unfold delta
  rw [div_le_iff₀ (by linarith)]
  nlinarith

theorem theta_pos (hg : 1 ≤ g) (hε1 : ε ≤ 1 / 2) : 0 < theta g ε := by
  unfold theta
  have : 0 < g := by linarith
  have : 0 < 1 - ε / 8 := by linarith
  positivity

theorem delta_lt_theta (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) : delta g ε < theta g ε := by
  unfold delta theta
  have hg0 : 0 < g := by linarith
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

theorem one_le_gain (hg : 1 ≤ g) (hq₀ : 0 < q₀) (hq₀1 : q₀ ≤ 1) : 1 ≤ gain g q₀ := by
  unfold gain
  have hs : 0 < Real.sqrt q₀ := Real.sqrt_pos.mpr hq₀
  have hs1 : Real.sqrt q₀ ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hq₀1
  rw [le_div_iff₀ hs]
  linarith

/-- The decoded amplitude suffices for amplification with gain `5 g / √q₀`. -/
theorem amplitude_bound (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) (hq₀ : 0 < q₀) :
    1 / (2 * gain g q₀) ≤ Real.sqrt q₀ * (theta g ε - delta g ε) := by
  unfold gain theta delta
  have hg0 : 0 < g := by linarith
  have hs : 0 < Real.sqrt q₀ := Real.sqrt_pos.mpr hq₀
  have hdiff : 1 / (10 * g) ≤ (1 - ε / 8) / (8 * g) - ε / (40 * g) := by
    rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
      (by positivity)]
    have h : 0 ≤ (80 - 130 * ε) * (g * g) := mul_nonneg (by linarith) (by positivity)
    nlinarith [h]
  have hlhs : 1 / (2 * (5 * g / Real.sqrt q₀)) = Real.sqrt q₀ * (1 / (10 * g)) := by
    field_simp
    ring
  rw [hlhs]
  exact mul_le_mul_of_nonneg_left hdiff hs.le

/-- Total direction error: decoding plus discretisation. -/
theorem direction_bound (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    2 * delta g ε / theta g ε + 2 * (ε / 8) ≤ ε := by
  unfold delta theta
  have hg0 : 0 < g := by linarith
  have hθ : 0 < 1 - ε / 8 := by linarith
  have heq : 2 * (ε / (40 * g)) / ((1 - ε / 8) / (8 * g)) = 2 * ε / (5 * (1 - ε / 8)) := by
    field_simp
    ring
  rw [heq]
  have h : 2 * ε / (5 * (1 - ε / 8)) ≤ 3 * ε / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

end Facts

end

end SparseHamiltonian.GeneralODE.Plan
