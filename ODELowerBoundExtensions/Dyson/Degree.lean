import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import GeneralODE.Analysis.ExpBounds

set_option autoImplicit false

/-!
# The truncation degree of the Dyson series (`odel:lem:dyson`, eq. `odel:eq:degree`)

Manuscript, proof of Lemma `odel:lem:dyson`
(lines 4216-4228): truncating the Dyson series at degree `K` leaves the factorial tail
`∑_{k>K} z^k/k!`, and for `K + 2 ≥ 2z`

  `∑_{k>K} z^k/k! ≤ 2 z^{K+1}/(K+1)! ≤ 2 (e z/(K+1))^{K+1}`.

Choosing `K` so that this is at most a small constant times `ε/ḡ` gives eq. `odel:eq:degree`,
`K = O(1 + z + L_g / log(e + L_g/z))`.

* `expTail y K = exp y - ∑_{k ≤ K} y^k/k!` is the tail in finite form;
* `expTail_le`: the displayed tail bound (lines 4218-4222);
* `dysonLog g ε = log (4000 g / ε)` is the precision logarithm `L_g = log(C ḡ/ε)` with
  `C = 4000`;
* `truncDegree z g ε = ⌈e² z + 4 L_g / log(e + L_g/z)⌉₊` is the explicit public degree;
* `expTail_truncDegree_le`: at this degree the tail is at most `ε/(2000 g)`;
* `truncDegree_le`: eq. `odel:eq:degree` with explicit constants;
* `dysonBound z g ε = 16000 g e^z (1 + z + L_g/log(e + L_g/z))`, the explicit form of
  eq. `odel:eq:dyson`, and `cost_le_dysonBound`.
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open scoped Nat BigOperators

/-- The exponential tail `∑_{k > K} y^k/k!`, written in the finite form
`exp y - ∑_{k ≤ K} y^k/k!` (proof of `odel:lem:dyson`, line 4217). -/
def expTail (y : ℝ) (K : ℕ) : ℝ :=
  Real.exp y - ∑ k ∈ Finset.range (K + 1), y ^ k / (k ! : ℝ)

/-- `expTail y K` is the series tail `∑_{n ≥ 0} y^{n+K+1}/(n+K+1)!` (line 4217). -/
theorem hasSum_expTail (y : ℝ) (K : ℕ) :
    HasSum (fun n : ℕ => y ^ (n + (K + 1)) / ((n + (K + 1))! : ℝ)) (expTail y K) := by
  rw [expTail]
  exact (hasSum_nat_add_iff' (K + 1)).mpr
    (SparseHamiltonian.GeneralODE.ExpBounds.real_exp_hasSum y)

/-- The tail of a nonnegative argument is nonnegative. -/
theorem expTail_nonneg (y : ℝ) (hy : 0 ≤ y) (K : ℕ) : 0 ≤ expTail y K := by
  exact (hasSum_expTail y K).nonneg (fun n => by positivity)

/-- The tail is monotone in a nonnegative argument. -/
theorem expTail_mono (K : ℕ) {y y' : ℝ} (hy : 0 ≤ y) (hyy : y ≤ y') :
    expTail y K ≤ expTail y' K := by
  refine hasSum_le (fun n => ?_) (hasSum_expTail y K) (hasSum_expTail y' K)
  gcongr

/-- **The factorial tail bound** (lines 4216-4222): for `0 ≤ y` and `K + 2 ≥ 2 y`,
`∑_{k>K} y^k/k! ≤ 2 y^{K+1}/(K+1)! ≤ 2 (e y/(K+1))^{K+1}` (both displayed inequalities). -/
theorem expTail_le (y : ℝ) (K : ℕ) (hy : 0 ≤ y) (hK : 2 * y ≤ (K : ℝ) + 2) :
    expTail y K ≤ 2 * y ^ (K + 1) / ((K + 1)! : ℝ) ∧
      2 * y ^ (K + 1) / ((K + 1)! : ℝ) ≤ 2 * (Real.exp 1 * y / ((K : ℝ) + 1)) ^ (K + 1) := by
  constructor
  · have hstep : ∀ n : ℕ, y ^ (n + 1 + (K + 1)) / ((n + 1 + (K + 1))! : ℝ) =
        y ^ (n + (K + 1)) / ((n + (K + 1))! : ℝ) * (y / (((n + (K + 1) : ℕ) : ℝ) + 1)) := by
      intro n
      rw [show n + 1 + (K + 1) = (n + (K + 1)) + 1 by ring, pow_succ, Nat.factorial_succ]
      push_cast
      field_simp
    have hratio : ∀ n : ℕ, y / (((n + (K + 1) : ℕ) : ℝ) + 1) ≤ 1 / 2 := by
      intro n
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [div_le_iff₀ (by positivity)]
      push_cast
      linarith
    have hterm : ∀ n : ℕ, y ^ (n + (K + 1)) / ((n + (K + 1))! : ℝ) ≤
        y ^ (K + 1) / ((K + 1)! : ℝ) * (1 / 2) ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [hstep n, pow_succ ((1 : ℝ) / 2) n, ← mul_assoc]
        exact mul_le_mul ih (hratio n) (by positivity) (by positivity)
    have h := hasSum_le hterm (hasSum_expTail y K)
      (hasSum_geometric_two.mul_left (y ^ (K + 1) / ((K + 1)! : ℝ)))
    calc expTail y K ≤ y ^ (K + 1) / ((K + 1)! : ℝ) * 2 := h
      _ = 2 * y ^ (K + 1) / ((K + 1)! : ℝ) := by ring
  · have hF : (0 : ℝ) < ((K + 1)! : ℝ) := by positivity
    have ha : (0 : ℝ) < ((K : ℝ) + 1) ^ (K + 1) := by positivity
    have hfac : ((K : ℝ) + 1) ^ (K + 1) ≤ Real.exp 1 ^ (K + 1) * ((K + 1)! : ℝ) := by
      have h := Real.pow_div_factorial_le_exp (x := (K : ℝ) + 1) (by positivity) (K + 1)
      rw [div_le_iff₀ hF] at h
      have he : Real.exp ((K : ℝ) + 1) = Real.exp 1 ^ (K + 1) := by
        rw [← Real.exp_nat_mul]; push_cast; ring_nf
      rwa [he] at h
    have hrhs : 2 * (Real.exp 1 * y / ((K : ℝ) + 1)) ^ (K + 1) =
        2 * (y ^ (K + 1) * Real.exp 1 ^ (K + 1)) / ((K : ℝ) + 1) ^ (K + 1) := by
      rw [div_pow, mul_pow]; ring
    rw [hrhs, div_le_div_iff₀ hF ha]
    have hy' : 0 ≤ 2 * y ^ (K + 1) := by positivity
    have := mul_le_mul_of_nonneg_left hfac hy'
    linarith

/-- The precision logarithm `L_g = log(C ḡ/ε)` of `odel:lem:dyson` with `C = 4000`. -/
def dysonLog (g ε : ℝ) : ℝ := Real.log (4000 * g / ε)

/-- `L_g > 0` in the range `g ≥ 1`, `0 < ε ≤ 1`. -/
theorem dysonLog_pos (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < dysonLog g ε := by
  unfold dysonLog
  apply Real.log_pos
  rw [one_lt_div hε]
  linarith

/-- `log(e + a) ≥ 1` for `a ≥ 0`. -/
theorem one_le_log_exp_one_add (a : ℝ) (ha : 0 ≤ a) : 1 ≤ Real.log (Real.exp 1 + a) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  linarith

/-- The degree inequality behind eq. `odel:eq:degree` (lines 4223-4227): for `z, L > 0` and
`m > e² z + 4L/log(e + L/z)`, `L ≤ m log(m/(e z))`. -/
theorem le_mul_log_of_gt (z L m : ℝ) (hz : 0 < z) (hL : 0 < L)
    (hm : Real.exp 2 * z + 4 * L / Real.log (Real.exp 1 + L / z) < m) :
    L ≤ m * Real.log (m / (Real.exp 1 * z)) := by
  have hE2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hE : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  have hu0 : 0 < L / z := div_pos hL hz
  have hs1 : 1 ≤ Real.log (Real.exp 1 + L / z) := one_le_log_exp_one_add _ hu0.le
  have hexps : Real.exp (Real.log (Real.exp 1 + L / z)) = Real.exp 1 + L / z :=
    Real.exp_log (by positivity)
  have hLz : L = L / z * z := by field_simp
  set E := Real.exp 1 with hEdef
  set u := L / z with hu
  set s := Real.log (E + u) with hs
  have hs0 : 0 < s := by linarith
  have hEz : 0 < E * z := by positivity
  have hq : 0 ≤ 4 * L / s := by positivity
  have hm0 : 0 < m := by
    have : 0 < Real.exp 2 * z := by positivity
    linarith
  have hr : 0 < m / (E * z) := div_pos hm0 hEz
  rw [hE2] at hm
  by_cases hcase : u ≤ E * E
  · -- `L ≤ e² z < m` and `m/(e z) > e`
    have hLE : L ≤ E * E * z := by
      rw [hLz]; exact mul_le_mul_of_nonneg_right hcase hz.le
    have h1 : L ≤ m := by linarith
    have h2 : 1 ≤ Real.log (m / (E * z)) := by
      rw [Real.le_log_iff_exp_le hr, le_div_iff₀ hEz]
      nlinarith
    nlinarith
  · replace hcase := not_le.mp hcase
    have huE : E ≤ u := by nlinarith
    have hkey : E * s ≤ 2 * Real.exp (3 * s / 4) := by
      have h := Real.add_one_le_exp (3 * s / 4 - 1)
      have he : Real.exp (3 * s / 4) = E * Real.exp (3 * s / 4 - 1) := by
        rw [hEdef, ← Real.exp_add]; ring_nf
      rw [he]
      nlinarith
    have hsplit : Real.exp s = Real.exp (s / 4) * Real.exp (3 * s / 4) := by
      rw [← Real.exp_add]; ring_nf
    have hp4 : 0 < Real.exp (s / 4) := Real.exp_pos _
    have hb : Real.exp (s / 4) * (E * s) ≤ 4 * u := by
      have := mul_le_mul_of_nonneg_left hkey hp4.le
      nlinarith
    have hms : 4 * L < m * s := by
      have h4 : 4 * L / s < m := by
        have : 0 ≤ E * E * z := by positivity
        linarith
      rwa [div_lt_iff₀ hs0] at h4
    have h3 : s / 4 ≤ Real.log (m / (E * z)) := by
      rw [Real.le_log_iff_exp_le hr, le_div_iff₀ hEz]
      have hz' := mul_le_mul_of_nonneg_right hb hz.le
      have : Real.exp (s / 4) * (E * z) * s ≤ m * s := by nlinarith
      exact le_of_mul_le_mul_right this hs0
    have hm' : 4 * L / s ≤ m := by
      rw [div_le_iff₀ hs0]; exact hms.le
    calc L = (4 * L / s) * (s / 4) := by field_simp
      _ ≤ m * (s / 4) := by gcongr
      _ ≤ m * Real.log (m / (E * z)) := by gcongr

/-- **The public truncation degree** `K = ⌈e² z + 4 L_g / log(e + L_g/z)⌉₊`
(eq. `odel:eq:degree`, lines 4225-4227). -/
def truncDegree (z g ε : ℝ) : ℕ :=
  ⌈Real.exp 2 * z + 4 * dysonLog g ε / Real.log (Real.exp 1 + dysonLog g ε / z)⌉₊

/-- At the public degree the truncation error is at most `ε/(2000 g)`, a sufficiently small
constant times `ε/ḡ` (lines 4223-4224). -/
theorem expTail_truncDegree_le (z g ε : ℝ) (hz : 0 < z) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    expTail z (truncDegree z g ε) ≤ ε / (2000 * g) := by
  have hL := dysonLog_pos g ε hg hε hε1
  have hlog1 : 1 ≤ Real.log (Real.exp 1 + dysonLog g ε / z) :=
    one_le_log_exp_one_add _ (by positivity)
  have hKge : Real.exp 2 * z + 4 * dysonLog g ε / Real.log (Real.exp 1 + dysonLog g ε / z) ≤
      (truncDegree z g ε : ℝ) := Nat.le_ceil _
  have hq : 0 ≤ 4 * dysonLog g ε / Real.log (Real.exp 1 + dysonLog g ε / z) := by positivity
  have hm : Real.exp 2 * z + 4 * dysonLog g ε / Real.log (Real.exp 1 + dysonLog g ε / z) <
      (truncDegree z g ε : ℝ) + 1 := by linarith
  have hE2 : 2 ≤ Real.exp 2 := by have := Real.add_one_le_exp 2; linarith
  have h2z : 2 * z ≤ (truncDegree z g ε : ℝ) + 2 := by nlinarith
  have hb := expTail_le z (truncDegree z g ε) hz.le h2z
  refine hb.1.trans (hb.2.trans ?_)
  have hkey := le_mul_log_of_gt z (dysonLog g ε) _ hz hL hm
  have hexpL : Real.exp (dysonLog g ε) = 4000 * g / ε := Real.exp_log (by positivity)
  set K := truncDegree z g ε
  set L := dysonLog g ε
  have hr : 0 < ((K : ℝ) + 1) / (Real.exp 1 * z) := by positivity
  have hrpow : Real.exp L ≤ (((K : ℝ) + 1) / (Real.exp 1 * z)) ^ (K + 1) := by
    rw [← Real.exp_log hr, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  have hinv : Real.exp 1 * z / ((K : ℝ) + 1) = (((K : ℝ) + 1) / (Real.exp 1 * z))⁻¹ := by
    rw [inv_div]
  rw [hinv, inv_pow]
  have h := inv_anti₀ (Real.exp_pos L) hrpow
  rw [hexpL, inv_div] at h
  calc 2 * ((((K : ℝ) + 1) / (Real.exp 1 * z)) ^ (K + 1))⁻¹ ≤ 2 * (ε / (4000 * g)) := by
        linarith
    _ = ε / (2000 * g) := by
        have : (0 : ℝ) < g := by linarith
        field_simp
        ring

/-- **Eq. `odel:eq:degree`** with explicit constants:
`K ≤ e² z + 4 L_g / log(e + L_g/z) + 1`. -/
theorem truncDegree_le (z g ε : ℝ) (hz : 0 < z) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (truncDegree z g ε : ℝ) ≤
      Real.exp 2 * z + 4 * dysonLog g ε / Real.log (Real.exp 1 + dysonLog g ε / z) + 1 := by
  have hL := dysonLog_pos g ε hg hε hε1
  have hlog1 : 1 ≤ Real.log (Real.exp 1 + dysonLog g ε / z) :=
    one_le_log_exp_one_add _ (by positivity)
  exact (Nat.ceil_lt_add_one (by positivity)).le

/-- **The paper-form query bound** of eq. `odel:eq:dyson` with explicit constants:
`16000 ḡ e^z (1 + z + L_g / log(e + L_g/z))`, `L_g = log(4000 ḡ/ε)`. -/
def dysonBound (z g ε : ℝ) : ℝ :=
  16000 * g * Real.exp z *
    (1 + z + dysonLog g ε / Real.log (Real.exp 1 + dysonLog g ε / z))

/-- The four-trial count `2160 (g m) K` at the public degree is at most `dysonBound` whenever
the coefficient-mass ratio satisfies `m ≤ e^z` (`2160 e² < 16000`; for `m < 0` the left side is
nonpositive and `dysonBound` is positive). -/
theorem cost_le_dysonBound (z g ε m : ℝ) (hz : 0 < z) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : m ≤ Real.exp z) :
    2160 * (g * m) * (truncDegree z g ε : ℝ) ≤ dysonBound z g ε := by
  have hL := dysonLog_pos g ε hg hε hε1
  have hlog1 : 1 ≤ Real.log (Real.exp 1 + dysonLog g ε / z) :=
    one_le_log_exp_one_add _ (by positivity)
  have hKle := truncDegree_le z g ε hz hg hε hε1
  have hK0 : (0 : ℝ) ≤ truncDegree z g ε := Nat.cast_nonneg _
  have hE2 : Real.exp 2 < 7.4 := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have := Real.exp_one_lt_d9
    have := Real.exp_pos 1
    rw [h2]; nlinarith
  have hg0 : 0 < g := by linarith
  have hez : 0 < Real.exp z := Real.exp_pos z
  unfold dysonBound
  set K : ℝ := (truncDegree z g ε : ℝ)
  set s := Real.log (Real.exp 1 + dysonLog g ε / z)
  set L := dysonLog g ε
  have hL' : 0 ≤ L / s := by positivity
  have h4 : 4 * L / s = 4 * (L / s) := mul_div_assoc _ _ _
  rw [h4] at hKle
  set L' := L / s
  have hpos : 0 < 16000 * g * Real.exp z * (1 + z + L') := by positivity
  rcases lt_or_ge m 0 with hneg | hnn
  · have : g * m ≤ 0 := by nlinarith
    nlinarith
  · have hgm : g * m ≤ g * Real.exp z := mul_le_mul_of_nonneg_left hm hg0.le
    have h1 : 2160 * (g * m) * K ≤ 2160 * (g * Real.exp z) * (Real.exp 2 * z + 4 * L' + 1) := by
      apply mul_le_mul (by linarith) hKle hK0 (by positivity)
    have hz2 : Real.exp 2 * z ≤ 7.4 * z := by nlinarith
    have h2 : 2160 * (Real.exp 2 * z + 4 * L' + 1) ≤ 16000 * (1 + z + L') := by linarith
    have hG : 0 < g * Real.exp z := by positivity
    have h3 := mul_le_mul_of_nonneg_left h2 hG.le
    nlinarith

end

end ODELowerBoundExtensions.Dyson
