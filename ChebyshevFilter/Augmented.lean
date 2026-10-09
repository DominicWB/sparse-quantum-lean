import ChebyshevFilter.Circuit
import SparseLinearSystems.Circuit.Facts
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false

/-!
# The filter for the augmented walk (equation `qls:eq:filtercost`)

For the augmented walk of the linear-system algorithm the released files prove, for every
public `0 < g ≤ g_σ`, the gap `|z - 1| ≥ 2 b` for every eigenvalue `z ≠ 1`, where
`b = χ / √(1 + χ²)` and `χ = 4 g / (165 √s)` (`Facts.gapO`, the chord form of equation
`qls:eq:augsine`; `b_σ`, `χ_σ` at `g = g_σ`). Here:

* `artanh_bLow`: `artanh b_σ = arsinh χ_σ` (second half of `qls:eq:augsine`);
* `augDegree s g δ = ⌈arcosh(1/δ) / (2 arsinh(4g/(165√s)))⌉`, equal to the degree
  `chebDegree b_σ δ` of Proposition `qls:prop:chebyshev` (`augDegree_eq`);
* `augDegree_le`: `d_σ(δ) ≤ 23 √s log(2/δ) / g` for `s ≥ 1`, `0 < g ≤ 1`, `0 < δ < 1`, an
  explicit form of `d_σ(δ) = O((√s / g) log(2/δ))`. The proof uses `artanh b ≥ b`
  (`le_artanh`) and `arcosh y ≤ log(2y)` (`arcosh_le_log`);
* `augmented_filter`: for the walk `WwO` of the released circuit layer, under the hypotheses
  of `Facts.gapO`, the filter of degree `d_σ(δ)` is within `δ` of the eigenvalue-one projector
  in operator norm, the LCU circuit with `d_σ(δ)` signed steps has exactly this success block,
  and the degree obeys the bound above.
-/

namespace ChebyshevFilter

noncomputable section
open SparseHamiltonian SparseLinearSystems SparseLinearSystems.Augmented
  SparseLinearSystems.UnitaryFilter SparseLinearSystems.LogicalWalk ContinuousLinearMap
open scoped InnerProduct

/-! ### Elementary inequalities -/

/-- `artanh b ≥ b` on `[0, 1)`, from `log((1+b)/(1-b)) = ∑_k 2 b^{2k+1}/(2k+1)`. -/
theorem le_artanh {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b < 1) : b ≤ Real.artanh b := by
  have hs := Real.hasSum_log_sub_log_of_abs_lt_one
    (show |b| < 1 by rw [abs_of_nonneg hb0]; exact hb1)
  have h := sum_le_hasSum {0} (fun i _ => by positivity) hs
  simp only [Finset.sum_singleton, CharP.cast_eq_zero, mul_zero, zero_add, div_one, mul_one,
    pow_one] at h
  rw [Real.artanh_eq_half_log ⟨by linarith, hb1.le⟩,
    Real.log_div (by linarith) (by linarith)]
  linarith

theorem two_thirds_le_log_two : (2 : ℝ) / 3 ≤ Real.log 2 := by
  have h := le_artanh (show (0 : ℝ) ≤ 1 / 3 by norm_num) (by norm_num)
  rw [Real.artanh_eq_half_log ⟨by norm_num, by norm_num⟩] at h
  norm_num at h
  linarith

/-- `arcosh y ≤ log(2y)` for `y ≥ 1`. -/
theorem arcosh_le_log {y : ℝ} (hy : 1 ≤ y) : Real.arcosh y ≤ Real.log (2 * y) := by
  have hsq : Real.sqrt (y ^ 2 - 1) ≤ y := by
    calc Real.sqrt (y ^ 2 - 1) ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = y := Real.sqrt_sq (by linarith)
  unfold Real.arcosh
  exact Real.log_le_log (by positivity) (by linarith)

/-! ### The augmented gap -/

/-- `artanh b_σ = arsinh χ_σ`. -/
theorem artanh_bLow (s g : ℝ) : Real.artanh (bLow s g) = Real.arsinh (chi s g) := by
  rw [bLow, ← Real.tanh_arsinh, Real.artanh_tanh]

theorem bLow_nonneg (s : ℝ) {g : ℝ} (hg : 0 ≤ g) : 0 ≤ bLow s g := by
  unfold bLow chi
  positivity

theorem bLow_lt_one (s g : ℝ) : bLow s g < 1 := by
  rw [bLow, div_lt_one (Real.sqrt_pos.mpr (by positivity))]
  calc chi s g ≤ |chi s g| := le_abs_self _
    _ = Real.sqrt (chi s g ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ < Real.sqrt (1 + chi s g ^ 2) := Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)

/-- **The augmented-walk degree** `d_σ(δ) = ⌈arcosh(1/δ) / (2 arsinh(4g/(165√s)))⌉`
(equation `qls:eq:filtercost`). -/
def augDegree (s g δ : ℝ) : ℕ := ⌈Real.arcosh (1 / δ) / (2 * Real.arsinh (chi s g))⌉₊

/-- `d_σ(δ)` is the degree of Proposition `qls:prop:chebyshev` at `b = b_σ`. -/
theorem augDegree_eq (s g δ : ℝ) : augDegree s g δ = chebDegree (bLow s g) δ := by
  rw [augDegree, chebDegree, artanh_bLow]

/-- **The degree bound** `d_σ(δ) ≤ 23 √s log(2/δ) / g`, an explicit
`d_σ(δ) = O((√s / g) log(2/δ))`. -/
theorem augDegree_le {s g δ : ℝ} (hs : 1 ≤ s) (hg0 : 0 < g) (hg1 : g ≤ 1) (hδ0 : 0 < δ)
    (hδ1 : δ < 1) : (augDegree s g δ : ℝ) ≤ 23 * Real.sqrt s * Real.log (2 / δ) / g := by
  have hsq : 1 ≤ Real.sqrt s := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hs
  have hχ0 : 0 < chi s g := by unfold chi; positivity
  have hχ1 : chi s g ≤ 4 / 165 := by
    unfold chi
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- `arsinh χ ≥ χ / √(1 + χ²) ≥ 1000 χ / 1001`
  have hroot : Real.sqrt (1 + chi s g ^ 2) ≤ 1001 / 1000 := by
    calc Real.sqrt (1 + chi s g ^ 2) ≤ Real.sqrt ((1001 / 1000) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith)
      _ = 1001 / 1000 := Real.sqrt_sq (by norm_num)
  have hb := le_artanh (bLow_nonneg s hg0.le) (bLow_lt_one s g)
  rw [artanh_bLow] at hb
  have ha : 1000 * chi s g / 1001 ≤ Real.arsinh (chi s g) := by
    refine le_trans ?_ hb
    rw [bLow, div_le_div_iff₀ (by norm_num) (Real.sqrt_pos.mpr (by positivity))]
    nlinarith
  have hapos : 0 < Real.arsinh (chi s g) := lt_of_lt_of_le (by positivity) ha
  -- `arcosh(1/δ) ≤ log(2/δ)` and `log(2/δ) ≥ 2/3`
  have h1δ : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith
  have hAL : Real.arcosh (1 / δ) ≤ Real.log (2 / δ) := by
    have h := arcosh_le_log h1δ
    rwa [show 2 * (1 / δ) = 2 / δ by ring] at h
  have hL : 2 / 3 ≤ Real.log (2 / δ) := by
    refine two_thirds_le_log_two.trans (Real.log_le_log (by norm_num) ?_)
    rw [le_div_iff₀ hδ0]
    linarith
  set Q := Real.sqrt s * Real.log (2 / δ) / g with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact div_nonneg (by nlinarith) hg0.le
  have hceil : (augDegree s g δ : ℝ) < Real.arcosh (1 / δ) / (2 * Real.arsinh (chi s g)) + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (Real.arcosh_nonneg h1δ) (by positivity))
  have hq : Real.arcosh (1 / δ) / (2 * Real.arsinh (chi s g)) ≤ 1001 * 165 / 8000 * Q := by
    rw [div_le_iff₀ (by positivity)]
    have e : 1001 * 165 / 8000 * Q * (2 * (1000 * chi s g / 1001)) = Real.log (2 / δ) := by
      rw [hQ]
      unfold chi
      field_simp
      ring
    calc Real.arcosh (1 / δ) ≤ Real.log (2 / δ) := hAL
      _ = 1001 * 165 / 8000 * Q * (2 * (1000 * chi s g / 1001)) := e.symm
      _ ≤ 1001 * 165 / 8000 * Q * (2 * Real.arsinh (chi s g)) := by gcongr
  have h1 : 1 ≤ 3 / 2 * Q := by
    have hLQ : Real.log (2 / δ) ≤ Q := by
      rw [hQ, le_div_iff₀ hg0]
      nlinarith
    linarith
  have hfin : (augDegree s g δ : ℝ) ≤ 23 * Q := by linarith
  rw [hQ] at hfin
  calc (augDegree s g δ : ℝ) ≤ 23 * (Real.sqrt s * Real.log (2 / δ) / g) := hfin
    _ = 23 * Real.sqrt s * Real.log (2 / δ) / g := by ring

/-! ### The augmented walk -/

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s : ℕ}

local notation "V0" => EuclideanSpace ℂ n

/-- **The Chebyshev filter for the augmented walk.** Under the hypotheses of the released gap
theorem `Facts.gapO` (with `0 < g ≤ g_σ`): the filter of degree `d_σ(δ)` is within `δ` of
the eigenvalue-one projector `P_{σ,r}` of `W_{σ,r}`; it is the success block of the
normalisation-one LCU circuit with `d_σ(δ)` signed walk steps; and
`d_σ(δ) ≤ 23 √s log(2/δ) / g`. -/
theorem augmented_filter (D : NativeSparseBlockEncoding.Data X n Z s) (x : X)
    (hA1 : ‖Facts.Aop D x‖ ≤ 1) (κ : ℝ) (hκ : 1 ≤ κ) (hlow : ∀ v, ‖v‖ ≤ κ * ‖Facts.Aop D x v‖)
    (Ub : X → V0 →L[ℂ] V0) (sv : V0) (hb : ‖Ub x sv‖ ≤ 1) (σ : ℝ) (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1)
    (r : ℝ) (hr : 1 / 8 ≤ r) (g : ℝ) (hg0 : 0 < g) (hg : g ≤ RegularizationGap.gap κ σ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ‖filterOp (WwO D Ub sv σ r x) (bLow s g) (augDegree s g δ) -
        fixedProj (WwO D Ub sv σ r x)‖ ≤ δ ∧
      ((seed (V := PrivO n) (bLow s g) (augDegree s g δ))†) ∘L
          (signedSteps (WwO D Ub sv σ r x) (augDegree s g δ) (augDegree s g δ) ∘L
            seed (bLow s g) (augDegree s g δ)) =
        filterOp (WwO D Ub sv σ r x) (bLow s g) (augDegree s g δ) ∧
      (augDegree s g δ : ℝ) ≤ 23 * Real.sqrt s * Real.log (2 / δ) / g := by
  have hs : (0 : ℝ) < s := by exact_mod_cast D.slots_pos
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast D.slots_pos
  have hbpos := Facts.bLow_pos (s : ℝ) g hs hg0
  have hbmem : bLow (s : ℝ) g ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith, bLow_lt_one _ _⟩
  have hgap := Facts.gapO D x hA1 κ hκ hlow Ub sv hb σ hσ₀ hσ₁ r hr g hg0 hg
  have hg1 : g ≤ 1 := hg.trans (RegularizationGap.gap_le_one κ σ hκ hσ₀ hσ₁)
  refine ⟨?_, lcu_compression _ hbmem _, augDegree_le hs1 hg0 hg1 hδ0 hδ1⟩
  rw [augDegree_eq]
  exact norm_filterOp_sub_fixedProj_le (Facts.WwO_unitaryF D Ub sv σ r x) hbpos
    (bLow_lt_one _ _) hgap hδ0 hδ1.le

end

end ChebyshevFilter
