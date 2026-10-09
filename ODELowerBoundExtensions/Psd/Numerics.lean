import ODELowerBoundExtensions.Psd.Params

/-!
# Numerics of Theorem `odel:thm:psd` at the main parameters

Manuscript lines 4032-4037 (eq. `odel:eq:nrange`), 4055-4061 (eq. `odel:eq:alower`),
4097-4108 (eqs. `odel:eq:smallbias`, `odel:eq:psdmixedlocal`), 4111-4132 (choice of `m`, the
cases `s ≥ 512n/τ` and `s < 512n/τ`, the assembly). Real analysis only; no quantum objects.
Main parameters: `n = ⌊r/4⌋` (`Hamiltonian.precN`), `u = τ/2`, `a = psdAmp n u`, `β₀ = a/4`,
`m = 2^{psdMu s}`.

* eq. `odel:eq:nrange` is the released `Hamiltonian.precN_range h.toHSRange h.hL` (`n ≥ 2`,
  `r/8 ≤ n ≤ r/4`, `τ ≤ r/8`); the only new fact is `half_tau_le_precN` (`u ≤ n`);
* `exp_neg_quarter_le_psdAmp`, `eight_eps_le_psdAmp`: `a ≥ (u/(en))^n ≥ e^{-L/4} ≥ 8ε`
  (route: `en/u ≤ e z/(2h) ≤ e + z` for `z = L/τ ≥ 64`, since `h = log(e + z) ≥ 2 > e/2`
  (`psd_two_le_hsH`, `psd_en_div_le`), and `n log(en/u) ≤ n h ≤ L/4`);
* `psd_hyp`, `psd_root`: `4 β₀^{-1/n} ≤ 8en/u ≤ 64n/τ` (`4^{1/n} ≤ 2` for `n ≥ 2`) and
  `β₀^{1/(2n)} ≥ ¼ √(u/n)` (`2^{-1/n} ≥ 1/2`, `e^{-1/2} ≥ 1/2`);
* `psd_m_cond`, `psd_gadget_arith`, `psd_scalar_sqrt`: the choice of `m` and the two cases;
* `psdGadgetConst = log 2/(1536√2)`, `psdConst = log 2/(3072√2)` and `psd_assembly`
  (`psdConst ≤ psdGadgetConst/2`, `psdConst ≤ 1/512`).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Psd

noncomputable section
open SparseLowerBounds SparseLowerBounds.Hamiltonian

variable {τ ε : ℝ} {s : ℕ}

/-! ### Numerics at the main parameters `n = ⌊r/4⌋`, `u = τ/2` -/

/-- **Eq. `odel:eq:nrange`, the new part** (lines 4035-4036): `n ≥ r/8 ≥ τ ≥ u = τ/2`. The
rest of eq. `odel:eq:nrange` is `Hamiltonian.precN_range h.toHSRange h.hL`. -/
theorem half_tau_le_precN (h : PsdRange τ s ε) : τ / 2 ≤ precN τ ε := by
  obtain ⟨-, hrn, hτr, -⟩ := precN_range h.toHSRange h.hL
  have hτ := h.toHSRange.tau_pos
  linarith

/-- `h = log(e + L/τ) ≥ 2` when `L ≥ 64τ` (`e² < 9 ≤ e + 64`; line 4059 uses `h > e/2`). -/
theorem psd_two_le_hsH (h : PsdRange τ s ε) : 2 ≤ hsH τ ε := by
  have hτ := h.toHSRange.tau_pos
  have hz : 64 ≤ hsL ε / τ := by rw [le_div_iff₀ hτ]; exact h.hL
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  unfold hsH
  rw [Real.le_log_iff_exp_le (by positivity)]
  have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [e2]
  nlinarith

/-- `en/u ≤ e + L/τ` at `u = τ/2` (lines 4057-4059: `en/u ≤ e z/(2h) ≤ e + z`). -/
theorem psd_en_div_le (h : PsdRange τ s ε) :
    Real.exp 1 * precN τ ε / (τ / 2) ≤ Real.exp 1 + hsL ε / τ := by
  have H := h.toHSRange
  have hτ := H.tau_pos
  have hh2 := psd_two_le_hsH h
  have hnr := H.precN_le_quarter
  have hrh := H.hsR_mul_hsH
  have hr0 := H.hsR_pos
  have hL0 := H.hsL_pos
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hn0 : (0 : ℝ) ≤ precN τ ε := Nat.cast_nonneg _
  -- `2n ≤ nh ≤ rh/4 = L/4`, so `n ≤ L/8`
  have hn8 : (precN τ ε : ℝ) * 8 ≤ hsL ε := by nlinarith
  have hen : Real.exp 1 * precN τ ε ≤ 3 * hsL ε / 8 := by nlinarith
  have h1 : Real.exp 1 * precN τ ε / (τ / 2) ≤ hsL ε / τ := by
    rw [div_le_div_iff₀ (by positivity) hτ]
    nlinarith
  have : 0 < hsL ε / τ := by positivity
  linarith

/-- **Eq. `odel:eq:alower`** (lines 4055-4061): `a ≥ (u/(en))^n ≥ e^{-L/4}` at `u = τ/2`. -/
theorem exp_neg_quarter_le_psdAmp (h : PsdRange τ s ε) :
    Real.exp (-(hsL ε / 4)) ≤ psdAmp (precN τ ε) (τ / 2) := by
  have H := h.toHSRange
  have hτ := H.tau_pos
  obtain ⟨hn2, -, -, -⟩ := precN_range H h.hL
  have hn1 : 1 ≤ precN τ ε := by omega
  have hn : (0 : ℝ) < precN τ ε := by exact_mod_cast (show 0 < precN τ ε by omega)
  have hge := psdAmp_ge hn1 (by linarith : (0 : ℝ) < τ / 2) (half_tau_le_precN h)
  refine le_trans ?_ hge
  have hx : 0 < τ / 2 / (Real.exp 1 * precN τ ε) := by positivity
  have e : Real.log (τ / 2 / (Real.exp 1 * precN τ ε)) =
      -Real.log (Real.exp 1 * precN τ ε / (τ / 2)) := by
    rw [← Real.log_inv, inv_div]
  have hlog : Real.log (Real.exp 1 * precN τ ε / (τ / 2)) ≤ hsH τ ε := by
    unfold hsH
    exact Real.log_le_log (by positivity) (psd_en_div_le h)
  have hb := (precision_exp_bound H).2
  rw [← Real.exp_log (pow_pos hx _), Real.log_pow, e]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hlog hn.le]

/-- `a ≥ 8ε` (line 4061). -/
theorem eight_eps_le_psdAmp (h : PsdRange τ s ε) : 8 * ε ≤ psdAmp (precN τ ε) (τ / 2) := by
  have H := h.toHSRange
  have h1 := exp_neg_quarter_ge H.four_le_hsL
  rw [exp_neg_hsL h.eps_pos] at h1
  have := exp_neg_quarter_le_psdAmp h
  linarith [h.eps_pos]

/-- `(x^n/4)^{-1/n} = 4^{1/n}/x` for `x > 0`, `n ≥ 1` (line 4102). -/
theorem psd_pow_div_four_rpow_neg_inv {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    (x ^ n / 4) ^ (-(1 : ℝ) / n) = (4 : ℝ) ^ (1 / (n : ℝ)) / x := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_natCast x n,
    ← Real.rpow_mul hx.le]
  have e : (n : ℝ) * (-(1 : ℝ) / n) = -1 := by field_simp
  rw [e, Real.rpow_neg_one, neg_div, Real.rpow_neg (by norm_num), div_inv_eq_mul,
    inv_mul_eq_div]

/-- `4^{1/n} ≤ 2` for `n ≥ 2` (line 4103). -/
theorem psd_four_rpow_inv_le_two {n : ℕ} (hn : 2 ≤ n) : (4 : ℝ) ^ (1 / (n : ℝ)) ≤ 2 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hn'
  have h2 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
    rw [← Real.sqrt_eq_rpow, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc (4 : ℝ) ^ (1 / (n : ℝ)) ≤ 4 ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    _ = 2 := h2

/-- **Side condition of eq. `odel:eq:smallbias`** at `β₀ = a/4` (lines 4101-4104):
`4 β₀^{-1/n} ≤ 8en/u < 32n/u = 64n/τ`. -/
theorem psd_hyp (h : PsdRange τ s ε) :
    4 * (psdAmp (precN τ ε) (τ / 2) / 4) ^ (-(1 : ℝ) / precN τ ε) ≤ 64 * precN τ ε / τ := by
  have H := h.toHSRange
  have hτ := H.tau_pos
  obtain ⟨hn2, -, -, -⟩ := precN_range H h.hL
  have hn1 : 1 ≤ precN τ ε := by omega
  have hn : (0 : ℝ) < precN τ ε := by exact_mod_cast (show 0 < precN τ ε by omega)
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hx : 0 < τ / 2 / (Real.exp 1 * precN τ ε) := by positivity
  have hge := psdAmp_ge hn1 (by linarith : (0 : ℝ) < τ / 2) (half_tau_le_precN h)
  have hxn : 0 < (τ / 2 / (Real.exp 1 * precN τ ε)) ^ precN τ ε / 4 := by positivity
  have hexp : -(1 : ℝ) / precN τ ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hn.le
  have h1 := Real.rpow_le_rpow_of_nonpos hxn
    (div_le_div_of_nonneg_right hge (by norm_num : (0 : ℝ) ≤ 4)) hexp
  rw [psd_pow_div_four_rpow_neg_inv hn1 hx] at h1
  have h4 := psd_four_rpow_inv_le_two hn2
  have h2 : 4 * ((4 : ℝ) ^ (1 / (precN τ ε : ℝ)) / (τ / 2 / (Real.exp 1 * precN τ ε))) ≤
      8 / (τ / 2 / (Real.exp 1 * precN τ ε)) := by
    rw [mul_div_assoc', div_le_div_iff_of_pos_right hx]; linarith
  have e3 : 8 / (τ / 2 / (Real.exp 1 * precN τ ε)) = 16 * Real.exp 1 * precN τ ε / τ := by
    field_simp; ring
  have h3 : 16 * Real.exp 1 * precN τ ε / τ ≤ 64 * precN τ ε / τ := by
    apply div_le_div_of_nonneg_right _ hτ.le
    nlinarith
  linarith

/-- **Root bound** (line 4105): `β₀^{1/(2n)} ≥ ¼ √(u/n)` at `β₀ = a/4`. -/
theorem psd_root (h : PsdRange τ s ε) :
    1 / 4 * Real.sqrt (τ / 2 / precN τ ε) ≤
      (psdAmp (precN τ ε) (τ / 2) / 4) ^ (1 / (2 * (precN τ ε : ℝ))) := by
  have H := h.toHSRange
  have hτ := H.tau_pos
  obtain ⟨hn2, -, -, -⟩ := precN_range H h.hL
  have hn1 : 1 ≤ precN τ ε := by omega
  have hn : (0 : ℝ) < precN τ ε := by exact_mod_cast (show 0 < precN τ ε by omega)
  have hn0 : (precN τ ε : ℝ) ≠ 0 := hn.ne'
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have hx : 0 < τ / 2 / (Real.exp 1 * precN τ ε) := by positivity
  have hge := psdAmp_ge hn1 (by linarith : (0 : ℝ) < τ / 2) (half_tau_le_precN h)
  have h1 : ((τ / 2 / (Real.exp 1 * precN τ ε)) ^ precN τ ε / 4) ^ (1 / (2 * (precN τ ε : ℝ))) ≤
      (psdAmp (precN τ ε) (τ / 2) / 4) ^ (1 / (2 * (precN τ ε : ℝ))) :=
    Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hge (by norm_num))
      (by positivity)
  have e1 : ((τ / 2 / (Real.exp 1 * precN τ ε)) ^ precN τ ε / 4) ^ (1 / (2 * (precN τ ε : ℝ))) =
      Real.sqrt (τ / 2 / (Real.exp 1 * precN τ ε)) * (2 : ℝ) ^ (-(1 : ℝ) / precN τ ε) := by
    rw [div_eq_mul_one_div _ (4 : ℝ), Real.mul_rpow (by positivity) (by norm_num),
      quarter_rpow_root, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    have e : (precN τ ε : ℝ) * (1 / (2 * (precN τ ε : ℝ))) = 1 / 2 := by field_simp
    rw [e, ← Real.sqrt_eq_rpow]
  rw [e1] at h1
  refine le_trans ?_ h1
  have h2 := half_le_two_rpow_neg_inv (precN τ ε)
  have e2 : Real.sqrt (τ / 2 / precN τ ε) =
      Real.sqrt (Real.exp 1) * Real.sqrt (τ / 2 / (Real.exp 1 * precN τ ε)) := by
    rw [← Real.sqrt_mul he0.le]
    congr 1
    field_simp
  have hse : Real.sqrt (Real.exp 1) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsx := Real.sqrt_nonneg (τ / 2 / (Real.exp 1 * precN τ ε))
  rw [e2]
  nlinarith [mul_le_mul_of_nonneg_left h2 hsx, mul_le_mul_of_nonneg_right hse hsx]

/-- **The choice of `m`** (lines 4111-4113): for `s ≥ 512n/τ`, `m > s/8 ≥ 64n/τ = 32n/u`. -/
theorem psd_m_cond (h : PsdRange τ s ε) (hs : 512 * (precN τ ε : ℝ) / τ ≤ s) :
    64 * (precN τ ε : ℝ) / τ ≤ (2 : ℝ) ^ psdMu s := by
  have hm := psdM_gt h.s_ge
  have e : 64 * (precN τ ε : ℝ) / τ = (512 * (precN τ ε : ℝ) / τ) / 8 := by ring
  rw [e]
  linarith

/-- The constant of the gadget family, `log 2/(1536√2)` (line 4116). -/
def psdGadgetConst : ℝ := Real.log 2 / (1536 * Real.sqrt 2)

/-- **The explicit constant of eq. `odel:eq:psd`**, `log 2/(3072√2) = psdGadgetConst/2`. -/
def psdConst : ℝ := Real.log 2 / (3072 * Real.sqrt 2)

/-- `psdConst > 0`. -/
theorem psdConst_pos : 0 < psdConst := by
  unfold psdConst
  have := Real.log_pos one_lt_two
  positivity

/-- **From eq. `odel:eq:psdmixedlocal` to the gadget bound** (lines 4112-4117):
`(log 2/192) √(m n u) ≥ (log 2/(1536√2)) √(sτr)` since `m > s/8`, `n ≥ r/8`, `u = τ/2`. -/
theorem psd_gadget_arith (h : PsdRange τ s ε) :
    psdGadgetConst * Real.sqrt (s * τ * hsR τ ε) ≤
      Real.log 2 / 192 * Real.sqrt ((2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2)) := by
  have H := h.toHSRange
  have hτ := H.tau_pos
  have hr0 := H.hsR_pos
  obtain ⟨-, hrn, -, -⟩ := precN_range H h.hL
  have hm := psdM_gt h.s_ge
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hle : (s : ℝ) * τ * hsR τ ε ≤ 128 * ((2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2)) := by
    have hs8 : (s : ℝ) ≤ 8 * (2 : ℝ) ^ psdMu s := by linarith
    have hr8 : hsR τ ε ≤ 8 * precN τ ε := by linarith
    calc (s : ℝ) * τ * hsR τ ε ≤ (8 * (2 : ℝ) ^ psdMu s) * τ * hsR τ ε :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hs8 hτ.le) hr0.le
      _ ≤ (8 * (2 : ℝ) ^ psdMu s) * τ * (8 * precN τ ε) :=
          mul_le_mul_of_nonneg_left hr8 (by positivity)
      _ = 128 * ((2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2)) := by ring
  have h1 : Real.sqrt (s * τ * hsR τ ε) ≤
      Real.sqrt 128 * Real.sqrt ((2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2)) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 128)]
    exact Real.sqrt_le_sqrt hle
  have h128 : Real.sqrt 128 = 8 * Real.sqrt 2 := by
    rw [show (128 : ℝ) = 8 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8 ^ 2),
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8)]
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs2' : Real.sqrt 2 ≠ 0 := hs2.ne'
  rw [h128] at h1
  unfold psdGadgetConst
  calc Real.log 2 / (1536 * Real.sqrt 2) * Real.sqrt (s * τ * hsR τ ε)
      ≤ Real.log 2 / (1536 * Real.sqrt 2) *
          (8 * Real.sqrt 2 * Real.sqrt ((2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2))) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg hl.le (by positivity))
    _ = Real.log 2 / 192 * Real.sqrt ((2 : ℝ) ^ psdMu s * precN τ ε * (τ / 2)) := by
        field_simp; ring

/-- **Small sparsity** (lines 4129-4131): if `s < 512n/τ` then `r ≤ 8n` gives
`√(sτr) < 64n`, so `n/4 > √(sτr)/256`. -/
theorem psd_scalar_sqrt (h : PsdRange τ s ε) (hs : (s : ℝ) < 512 * precN τ ε / τ) :
    Real.sqrt (s * τ * hsR τ ε) / 256 ≤ (precN τ ε : ℝ) / 4 := by
  have H := h.toHSRange
  have hτ := H.tau_pos
  have hr0 := H.hsR_pos
  have hr := hsR_le_eight_precN H h.hL
  have hsτ : (s : ℝ) * τ < 512 * precN τ ε := by rwa [lt_div_iff₀ hτ] at hs
  have hn0 : (0 : ℝ) ≤ precN τ ε := Nat.cast_nonneg _
  have hlt : (s : ℝ) * τ * hsR τ ε ≤ (64 * (precN τ ε : ℝ)) ^ 2 := by
    calc (s : ℝ) * τ * hsR τ ε ≤ 512 * precN τ ε * hsR τ ε :=
          mul_le_mul_of_nonneg_right hsτ.le hr0.le
      _ ≤ 512 * precN τ ε * (8 * precN τ ε) := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = (64 * (precN τ ε : ℝ)) ^ 2 := by ring
  have h1 : Real.sqrt (s * τ * hsR τ ε) ≤ 64 * precN τ ε := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 64 * precN τ ε)]
    exact Real.sqrt_le_sqrt hlt
  linarith

/-- **Assembly of eq. `odel:eq:psd`** (lines 4131-4132): from the gadget bound (for
`s ≥ 512n/τ`) and the scalar bounds `r/32` and (for `s < 512n/τ`) `√(sτr)/256`, the larger of
the two query counts is at least `psdConst (√(sτr) + r)`. -/
theorem psd_assembly (h : PsdRange τ s ε) {QG QS : ℝ} (hS : hsR τ ε / 32 ≤ QS)
    (hS' : (s : ℝ) < 512 * precN τ ε / τ → Real.sqrt (s * τ * hsR τ ε) / 256 ≤ QS)
    (hG : 512 * (precN τ ε : ℝ) / τ ≤ s → psdGadgetConst * Real.sqrt (s * τ * hsR τ ε) ≤ QG) :
    psdConst * (Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤ max QG QS := by
  have H := h.toHSRange
  have hr0 := H.hsR_pos
  have hsq := Real.sqrt_nonneg (s * τ * hsR τ ε)
  have hl1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hs2 : 1 ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hc : psdConst = psdGadgetConst / 2 := by
    unfold psdConst psdGadgetConst; field_simp; ring
  have hc0 : 0 ≤ psdConst := psdConst_pos.le
  have hc1 : psdConst ≤ 1 / 512 := by
    unfold psdConst
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hQS := le_max_right QG QS
  have hQG := le_max_left QG QS
  rcases le_or_gt (512 * (precN τ ε : ℝ) / τ) s with hs | hs
  · have hG' := hG hs
    have h1 : psdConst * hsR τ ε ≤ hsR τ ε / 64 := by nlinarith
    have h2 : psdConst * Real.sqrt (s * τ * hsR τ ε) =
        psdGadgetConst * Real.sqrt (s * τ * hsR τ ε) / 2 := by rw [hc]; ring
    nlinarith
  · have hS'' := hS' hs
    have h1 : psdConst * hsR τ ε ≤ hsR τ ε / 512 := by nlinarith
    have h2 : psdConst * Real.sqrt (s * τ * hsR τ ε) ≤ Real.sqrt (s * τ * hsR τ ε) / 512 := by
      nlinarith
    nlinarith

end

end ODELowerBoundExtensions.Psd
