import SparseHamiltonian.SharpClockQuery

/-!
# Scalar optimization of the improved sparse Hamiltonian query budget

This file proves only the scalar rescaling optimization. It neither assumes nor
asserts an implementation of the improved simulation circuit. In particular,
`exists_rescaling` must be combined with a separately proved oracle query bound.
The precision parameter `ell` is any strictly positive real; it can later be
instantiated with the certified filter schedule's logarithmic precision budget.
-/

namespace SparseHamiltonian.ImprovedSimulationBudget

noncomputable section

/-- The width-coordinate cost, where `a = sqrt s` and `x = gamma * a`. -/
def widthCost (a tau ell x : ℝ) : ℝ :=
  tau / 2 * (x + a ^ 2 / x) + (⌈x⌉₊ : ℝ) * ell

/-- The scalar catalyst-plus-filter budget in the manuscript. -/
def rescaledCost (s tau ell gamma : ℝ) : ℝ :=
  tau * Real.sqrt s / 2 * (gamma + gamma⁻¹) +
    (⌈max 1 (gamma * Real.sqrt s)⌉₊ : ℝ) * ell

/-- The three terms of the improved asymptotic query bound. -/
def targetBudget (s tau ell : ℝ) : ℝ :=
  Real.sqrt s * tau + Real.sqrt (s * tau * ell) + ell

/-- Above unit width, rounding the width up costs at most a factor of two. -/
theorem ceil_le_twice {x : ℝ} (hx : 1 ≤ x) : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
  linarith

/-- At full width, a time budget at least as large as the precision budget
absorbs the filter cost. -/
theorem widthCost_full {a tau ell : ℝ} (ha : 1 ≤ a)
    (_ht : 0 ≤ tau) (hell : 0 ≤ ell) (hlarge : ell ≤ tau) :
    widthCost a tau ell a ≤ 3 * a * tau := by
  have hap : 0 < a := by linarith
  have hdiv : a ^ 2 / a = a := by
    field_simp [hap.ne']
  have hceil := ceil_le_twice ha
  have hfilter := mul_le_mul_of_nonneg_right hceil hell
  have htime := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ 2 * a by positivity)
  unfold widthCost
  rw [hdiv]
  nlinarith

/-- At unit width, a sufficiently small time budget contributes at most `ell`;
the integer filter width is exactly one. -/
theorem widthCost_unit {a tau ell : ℝ} (ha : 1 ≤ a)
    (ht : 0 ≤ tau) (hsmall : tau * a ^ 2 ≤ ell) :
    widthCost a tau ell 1 ≤ 2 * ell := by
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  have htime := mul_le_mul_of_nonneg_left ha2 ht
  norm_num [widthCost]
  nlinarith

/-- A balanced width makes the inverse-width part of the catalyst cost equal
to `x * ell`; rounding the filter width preserves the threefold bound. -/
theorem widthCost_balanced {a tau ell x : ℝ} (hx : 1 ≤ x)
    (hell : 0 ≤ ell) (hsmall : tau ≤ ell)
    (hbalance : tau * a ^ 2 = x ^ 2 * ell) :
    widthCost a tau ell x ≤ 3 * x * ell := by
  have hxp : 0 < x := by linarith
  have hcancel : tau * (a ^ 2 / x) = x * ell := by
    calc
      tau * (a ^ 2 / x) = (tau * a ^ 2) / x := by ring
      _ = (x ^ 2 * ell) / x := by rw [hbalance]
      _ = x * ell := by field_simp [hxp.ne']
  have hcost : widthCost a tau ell x =
      (tau * x + x * ell) / 2 + (⌈x⌉₊ : ℝ) * ell := by
    unfold widthCost
    calc
      _ = (tau * x + tau * (a ^ 2 / x)) / 2 +
          (⌈x⌉₊ : ℝ) * ell := by ring
      _ = _ := by rw [hcancel]
  have htime := mul_le_mul_of_nonneg_right hsmall hxp.le
  have hfilter := mul_le_mul_of_nonneg_right (ceil_le_twice hx) hell
  rw [hcost]
  nlinarith

/-- Constructive three-regime optimization. The witness is respectively `a`,
`1`, or `r / ell`. Writing the result with a supplied nonnegative square root
keeps the argument independent of square-root normalization conventions. -/
theorem exists_width {a tau ell r : ℝ} (ha : 1 ≤ a)
    (ht : 0 ≤ tau) (hell : 0 < ell) (hr : 0 ≤ r)
    (hrsq : r ^ 2 = a ^ 2 * tau * ell) :
    ∃ x : ℝ, 1 ≤ x ∧ x ≤ a ∧
      widthCost a tau ell x ≤ 3 * (a * tau + r + ell) := by
  have hap : 0 < a := by linarith
  have hat : 0 ≤ a * tau := mul_nonneg hap.le ht
  by_cases hlarge : ell ≤ tau
  · refine ⟨a, ha, le_rfl, ?_⟩
    have h := widthCost_full ha ht hell.le hlarge
    nlinarith
  · have htell : tau ≤ ell := le_of_lt (lt_of_not_ge hlarge)
    by_cases hsmall : tau * a ^ 2 ≤ ell
    · refine ⟨1, le_rfl, ha, ?_⟩
      have h := widthCost_unit ha ht hsmall
      nlinarith
    · have hmiddle : ell ≤ tau * a ^ 2 := le_of_lt (lt_of_not_ge hsmall)
      let x : ℝ := r / ell
      have hx : 1 ≤ x := by
        apply (le_div_iff₀ hell).2
        have hmul := mul_le_mul_of_nonneg_right hmiddle hell.le
        have hsq : ell ^ 2 ≤ r ^ 2 := by nlinarith [hrsq]
        simpa only [one_mul] using (sq_le_sq₀ hell.le hr).mp hsq
      have hxa : x ≤ a := by
        apply (div_le_iff₀ hell).2
        have hmul := mul_le_mul_of_nonneg_left htell
          (mul_nonneg (sq_nonneg a) hell.le)
        have hsq : r ^ 2 ≤ (a * ell) ^ 2 := by nlinarith [hrsq]
        exact (sq_le_sq₀ hr (mul_nonneg hap.le hell.le)).mp hsq
      have hbalance : tau * a ^ 2 = x ^ 2 * ell := by
        dsimp [x]
        calc
          tau * a ^ 2 = r ^ 2 / ell := by
            apply (eq_div_iff hell.ne').2
            nlinarith [hrsq]
          _ = (r / ell) ^ 2 * ell := by
            field_simp [hell.ne']
      have hxe : x * ell = r := by
        dsimp [x]
        exact div_mul_cancel₀ r hell.ne'
      refine ⟨x, hx, hxa, ?_⟩
      have h := widthCost_balanced hx hell.le htell hbalance
      rw [mul_assoc, hxe] at h
      nlinarith

/-- Change of variables between the manuscript's rescaling and the width
coordinate. No approximation or asymptotic notation is involved. -/
theorem rescaledCost_eq_widthCost {s tau ell x : ℝ}
    (hs : 0 < s) (hx : 1 ≤ x) :
    rescaledCost s tau ell (x / Real.sqrt s) =
      widthCost (Real.sqrt s) tau ell x := by
  have ha : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have hxp : 0 < x := by linarith
  have hwidth : x / Real.sqrt s * Real.sqrt s = x :=
    div_mul_cancel₀ x ha.ne'
  unfold rescaledCost widthCost
  rw [hwidth, max_eq_right hx]
  congr 1
  field_simp [ha.ne', hxp.ne']

/-- There is an admissible rescaling whose exact catalyst-plus-filter scalar
budget is at most three times the desired three-term query expression.
This includes `tau = 0`; an end-to-end simulation may instead use the identity
circuit in that case. -/
theorem exists_rescaling {s tau ell : ℝ} (hs : 1 ≤ s)
    (ht : 0 ≤ tau) (hell : 0 < ell) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma ≤ 1 ∧
      1 ≤ gamma * Real.sqrt s ∧
      rescaledCost s tau ell gamma ≤ 3 * targetBudget s tau ell := by
  have hsp : 0 < s := by linarith
  have ha : 1 ≤ Real.sqrt s := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hs
  have hap : 0 < Real.sqrt s := Real.sqrt_pos.2 hsp
  have ha2 : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hsp.le
  have hr : 0 ≤ Real.sqrt (s * tau * ell) := Real.sqrt_nonneg _
  have hr2 : (Real.sqrt (s * tau * ell)) ^ 2 =
      (Real.sqrt s) ^ 2 * tau * ell := by
    rw [ha2]
    exact Real.sq_sqrt (mul_nonneg (mul_nonneg hsp.le ht) hell.le)
  obtain ⟨x, hx, hxa, hcost⟩ := exists_width ha ht hell hr hr2
  have hxp : 0 < x := by linarith
  refine ⟨x / Real.sqrt s, div_pos hxp hap, ?_, ?_, ?_⟩
  · exact (div_le_one hap).2 hxa
  · simpa only [div_mul_cancel₀ x hap.ne'] using hx
  · rw [rescaledCost_eq_widthCost hsp hx]
    exact hcost

/-- The equivalent `(1 + gamma^2)/gamma` form used in the resolvent moments. -/
theorem rescaledCost_eq_moments {s tau ell gamma : ℝ} (hg : 0 < gamma) :
    rescaledCost s tau ell gamma =
      tau * Real.sqrt s / gamma * ((1 + gamma ^ 2) / 2) +
        (⌈max 1 (gamma * Real.sqrt s)⌉₊ : ℝ) * ell := by
  unfold rescaledCost
  congr 1
  field_simp [hg.ne']; ring

/-- Optimization in the exact moment-budget notation. This is a scalar result,
not a theorem asserting a simulation circuit or a sparse-oracle implementation. -/
theorem exists_rescaling_moment_budget {s tau ell : ℝ} (hs : 1 ≤ s)
    (ht : 0 ≤ tau) (hell : 0 < ell) :
    ∃ gamma : ℝ, 0 < gamma ∧ gamma ≤ 1 ∧
      1 ≤ gamma * Real.sqrt s ∧
      tau * Real.sqrt s / gamma * ((1 + gamma ^ 2) / 2) +
        (⌈max 1 (gamma * Real.sqrt s)⌉₊ : ℝ) * ell ≤
          3 * targetBudget s tau ell := by
  obtain ⟨gamma, hg, hg1, hwidth, hcost⟩ := exists_rescaling hs ht hell
  refine ⟨gamma, hg, hg1, hwidth, ?_⟩
  rw [rescaledCost_eq_moments hg] at hcost
  exact hcost

end

end SparseHamiltonian.ImprovedSimulationBudget
