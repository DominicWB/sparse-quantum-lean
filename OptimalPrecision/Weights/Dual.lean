import OptimalPrecision.Weights.Resolvent
import OptimalPrecision.Weights.Gamma
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The dual functional of the gamma mixtures

The extraction rule of Theorem `opt:thm:weights` pairs a power series `s` in
`x = -∂` with the Taylor data of the extraction function `φ` at the delay:

  `L(s) = ∑_{i ≤ N} s_i D_i`,  `D(z) = ∑_i D_i z^i = (C₂(z) - C₁(z))/ℓ`.

Every inverse power of `x - y⁻¹ + 1` is, up to a power of `y`, the rescaled
negative binomial series, and its pairing with `D` is a derivative of
`z^k D(z)` at `z = y` (`pair_geom`). This file verifies the hypotheses of
`Resolvent.Hyp` for `L` and `c = i/q`:

* `L(x^{-1}) = D(1) = 0` and `L(x^{-2}) = (zD)'(1) = 1` (equal masses, means
  separated by `ℓ`: `opt:eq:gamma-means`);
* `L(x^j) = 0` for `j < d₀` (vanishing below the shape index `d₀`);
* `L((x ∓ c)^{-b}) = 0` for `1 ≤ b ≤ M`, because `(1 ∓ c)^{-1} ∈ {α, ᾱ}` are
  zeros of `D` of multiplicity `M` (`opt:eq:oscillators`).
-/

namespace OptimalPrecision.Dual

noncomputable section

open Polynomial Finset Nat
open scoped Polynomial
open Resolvent

/-! ### The pairing -/

/-- The pairing `s ↦ ∑_{i ≤ N} s_i D_i`. -/
def pair (N : ℕ) (Dp : ℂ[X]) : PowerSeries ℂ →ₗ[ℂ] ℂ :=
  ∑ i ∈ range (N + 1), Dp.coeff i • PowerSeries.coeff i

theorem pair_apply (N : ℕ) (Dp : ℂ[X]) (s : PowerSeries ℂ) :
    pair N Dp s = ∑ i ∈ range (N + 1), PowerSeries.coeff i s * Dp.coeff i := by
  simp only [pair, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- `y^{k+1} (1 - yX)^{-(k+1)}`. -/
def geom (y : ℂ) (k : ℕ) : PowerSeries ℂ :=
  PowerSeries.C (y ^ (k + 1)) *
    PowerSeries.rescale y (PowerSeries.mk fun n => ((k + n).choose k : ℂ))

theorem coeff_geom (y : ℂ) (k i : ℕ) :
    PowerSeries.coeff i (geom y k) = y ^ (k + 1) * (y ^ i * ((k + i).choose k : ℂ)) := by
  rw [geom, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, PowerSeries.coeff_mk]

/-- **The pairing with a negative binomial series** is a derivative at `y`. -/
theorem pair_geom {N : ℕ} {Dp : ℂ[X]} (hD : Dp.natDegree ≤ N) (y : ℂ) (k : ℕ) :
    pair N Dp (geom y k) =
      y ^ (k + 1) / (k ! : ℂ) * (derivative^[k] (X ^ k * Dp)).eval y := by
  have hdeg : (derivative^[k] (X ^ k * Dp)).natDegree < N + 1 := by
    refine lt_of_le_of_lt (natDegree_iterate_derivative _ k) ?_
    have := natDegree_mul_le (p := (X ^ k : ℂ[X])) (q := Dp)
    rw [natDegree_X_pow] at this
    omega
  rw [pair_apply, eval_eq_sum_range' hdeg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_geom, coeff_iterate_derivative, coeff_X_pow_mul, nsmul_eq_mul,
    Nat.descFactorial_eq_factorial_mul_choose, add_comm i k]
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  push_cast
  field_simp

/-! ### Inverse powers as negative binomial series -/

theorem v_zero : v 0 = u := by simp [v]

theorem v_neg (c : ℂ) : v (-c) = v' c := by simp [v, v']

/-- `(x - c)^{-1} = y Σ (yX)^n` with `y = (1 - c)^{-1}`. -/
theorem v_inv {c : ℂ} (hc : 1 - c ≠ 0) :
    (v c)⁻¹ = PowerSeries.C (1 - c)⁻¹ * PowerSeries.rescale (1 - c)⁻¹ (PowerSeries.mk 1) := by
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one (by rw [constantCoeff_v]; exact hc)]
  set y := (1 - c)⁻¹ with hy_def
  have hy : y * (1 - c) = 1 := inv_mul_cancel₀ hc
  have h1 := congrArg (PowerSeries.rescale y) (PowerSeries.mk_one_mul_one_sub_eq_one ℂ)
  simp only [map_mul, map_sub, map_one, PowerSeries.rescale_X] at h1
  have hv : v c = PowerSeries.C (1 - c) * (1 - PowerSeries.C y * PowerSeries.X) := by
    have hcy : PowerSeries.C (1 - c) * PowerSeries.C y = (1 : PowerSeries ℂ) := by
      rw [← map_mul, mul_comm, hy, map_one]
    calc v c = PowerSeries.C (1 - c) -
          (PowerSeries.C (1 - c) * PowerSeries.C y) * PowerSeries.X := by
          rw [hcy, one_mul, map_sub, map_one]; simp [v, u, ExpPoly.xs]; ring
      _ = _ := by ring
  rw [hv]
  calc PowerSeries.C y * PowerSeries.rescale y (PowerSeries.mk 1) *
        (PowerSeries.C (1 - c) * (1 - PowerSeries.C y * PowerSeries.X)) =
      (PowerSeries.C y * PowerSeries.C (1 - c)) *
        (PowerSeries.rescale y (PowerSeries.mk 1) * (1 - PowerSeries.C y * PowerSeries.X)) := by
        ring
    _ = 1 := by rw [h1, ← map_mul, hy, map_one, one_mul]

/-- `(x - c)^{-(k+1)}` is the negative binomial series at `y = (1 - c)^{-1}`. -/
theorem v_inv_pow {c : ℂ} (hc : 1 - c ≠ 0) (k : ℕ) :
    (v c)⁻¹ ^ (k + 1) = geom (1 - c)⁻¹ k := by
  rw [v_inv hc, mul_pow, ← map_pow, ← map_pow, PowerSeries.mk_one_pow_eq_mk_choose_add, geom]

theorem u_inv_pow (k : ℕ) : u⁻¹ ^ (k + 1) = geom 1 k := by
  have := v_inv_pow (c := 0) (by norm_num) k
  rwa [v_zero, sub_zero, inv_one] at this

theorem v'_inv_pow {c : ℂ} (hc : 1 + c ≠ 0) (k : ℕ) :
    (v' c)⁻¹ ^ (k + 1) = geom (1 + c)⁻¹ k := by
  have := v_inv_pow (c := -c) (by rwa [sub_neg_eq_add]) k
  rwa [v_neg, sub_neg_eq_add] at this

/-- Coefficients of `x^j = (1 - X)^j` vanish beyond `j`. -/
theorem coeff_u_pow_of_lt {i j : ℕ} (h : j < i) : PowerSeries.coeff i (u ^ j) = 0 := by
  have hpoly : (u ^ j : PowerSeries ℂ) = (((1 - X) ^ j : ℂ[X]) : PowerSeries ℂ) := by
    simp [u, ExpPoly.xs]
  rw [hpoly, Polynomial.coeff_coe]
  apply coeff_eq_zero_of_natDegree_lt
  refine lt_of_le_of_lt (natDegree_pow_le) ?_
  have : (1 - X : ℂ[X]).natDegree ≤ 1 :=
    (natDegree_sub_le _ _).trans (by simp)
  calc j * (1 - X : ℂ[X]).natDegree ≤ j * 1 := Nat.mul_le_mul_left _ this
    _ < i := by omega

/-! ### Verification of the dual hypotheses -/

/-- A divisibility `(X - y)^M ∣ D` kills the pairing with `(1 - yX)^{-b}`, `b ≤ M`. -/
theorem pair_geom_of_dvd {N M : ℕ} {Dp : ℂ[X]} (hD : Dp.natDegree ≤ N) {y : ℂ}
    (hdvd : (X - C y) ^ M ∣ Dp) {k : ℕ} (hk : k < M) : pair N Dp (geom y k) = 0 := by
  rw [pair_geom hD]
  have h1 : (X - C y) ^ M ∣ X ^ k * Dp := Dvd.dvd.mul_left hdvd _
  have h2 := pow_sub_dvd_iterate_derivative_of_pow_dvd k h1
  have h3 : X - C y ∣ derivative^[k] (X ^ k * Dp) :=
    (dvd_pow_self _ (by omega : M - k ≠ 0)).trans h2
  rw [dvd_iff_isRoot.mp h3, mul_zero]

/-- **The dual hypotheses** for a difference polynomial `D` with the moment,
vanishing and root properties of `opt:eq:oscillators`–`opt:eq:gamma-means`. -/
theorem hyp_of {N M d₀ : ℕ} {Dp : ℂ[X]} {c : ℂ} (hD : Dp.natDegree ≤ N)
    (hc0 : c ≠ 0) (hc1 : 1 - c ≠ 0) (hc2 : 1 + c ≠ 0)
    (hvan : ∀ i < d₀, Dp.coeff i = 0) (hD1 : Dp.eval 1 = 0)
    (hDd : (derivative (X * Dp)).eval 1 = 1)
    (hα : (X - C (1 - c)⁻¹) ^ M ∣ Dp) (hβ : (X - C (1 + c)⁻¹) ^ M ∣ Dp) :
    Hyp (pair N Dp) c M d₀ where
  c_ne := hc0
  one_sub_ne := hc1
  one_add_ne := hc2
  ui_sq := by
    rw [u_inv_pow 1, pair_geom hD]
    simp only [Function.iterate_one, pow_one, one_pow, Nat.factorial_one, Nat.cast_one, div_one,
      one_mul, hDd]
  ui := by
    have := u_inv_pow 0
    rw [pow_one] at this
    rw [this, pair_geom hD]
    simp [hD1]
  u_pow := by
    intro j hj
    rw [pair_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases Nat.lt_or_ge i d₀ with h | h
    · rw [hvan i h, mul_zero]
    · rw [coeff_u_pow_of_lt (by omega), zero_mul]
  vi_pow := by
    intro b hb1 hbM
    obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
    rw [v_inv_pow hc1, pair_geom_of_dvd hD hα (by omega)]
  wi_pow := by
    intro e he1 heM
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    rw [v'_inv_pow hc2, pair_geom_of_dvd hD hβ (by omega)]

/-! ### The gamma mixtures -/

section Mixture

open Gamma

variable (q : ℝ) (M : ℕ)

/-- `D = (C₂ - C₁)/ℓ` over `ℝ`. -/
def diffR : ℝ[X] := C ((ell (q * M) : ℝ)⁻¹) * (C2 q M - C1 q M)

/-- `D` over `ℂ`. -/
def diffC : ℂ[X] := (diffR q M).map Complex.ofRealHom

/-- The pole `c = i/q`. -/
def cq : ℂ := Complex.I / q

variable {q M}

theorem diffC_eq : diffC q M =
    C (((ell (q * M) : ℝ)⁻¹ : ℝ) : ℂ) *
      ((X ^ ell (q * M) - 1) * (C1 q M).map Complex.ofRealHom) := by
  simp [diffC, diffR, C2_sub_C1, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow]

theorem natDegree_diffC_le (hq : 1 ≤ q) (hM : 1 ≤ M) : (diffC q M).natDegree ≤ Dstar q M := by
  refine (natDegree_map_le).trans ((natDegree_C_mul_le _ _).trans ?_)
  exact (natDegree_sub_le _ _).trans (max_le (natDegree_C2_le hq hM) (natDegree_C1_le_Dstar hq hM))

theorem coeff_diffC_of_lt {i : ℕ} (hi : i < d0 (q * M)) : (diffC q M).coeff i = 0 := by
  rw [diffC, coeff_map, diffR, coeff_C_mul, coeff_sub, coeff_C1_of_lt hi, coeff_C2_of_lt hi]
  simp

theorem eval_one_diffC (hq : 1 ≤ q) (hM : 1 ≤ M) : (diffC q M).eval 1 = 0 := by
  rw [diffC, eval_one_map, diffR, eval_mul, eval_sub, eval_one_C1 hq hM, eval_one_C2 hq hM]
  simp

theorem eval_one_derivative_X_mul_diffC (hq : 1 ≤ q) (hM : 1 ≤ M) :
    (derivative (X * diffC q M)).eval 1 = 1 := by
  have ha : 0 < q * M := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hl : (ell (q * M) : ℂ) ≠ 0 := by exact_mod_cast (ell_pos ha).ne'
  have h1 : ((C1 q M).map Complex.ofRealHom).eval 1 = 1 := by
    rw [eval_one_map, eval_one_C1 hq hM, map_one]
  rw [diffC_eq]
  simp only [derivative_mul, derivative_X, derivative_C, derivative_sub, derivative_X_pow,
    derivative_one, eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_one, eval_pow, one_pow,
    h1, zero_mul, zero_add, one_mul, mul_one, sub_self, mul_zero, add_zero, sub_zero]
  push_cast
  field_simp

theorem cq_ne_zero (hq : 0 < q) : cq q ≠ 0 := by
  have : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  simp [cq, Complex.I_ne_zero, this]

theorem one_sub_cq_ne_zero : 1 - cq q ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [cq, Complex.div_re] at this

theorem one_add_cq_ne_zero : 1 + cq q ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp [cq, Complex.div_re] at this

theorem inv_one_sub_cq : (1 - cq q)⁻¹ = alpha q := rfl

theorem inv_one_add_cq : (1 + cq q)⁻¹ = (starRingEnd ℂ) (alpha q) := by
  rw [alpha, map_inv₀, map_sub, map_one, map_div₀, Complex.conj_I, Complex.conj_ofReal, cq]
  ring_nf

theorem dvd_diffC_alpha : (X - C (1 - cq q)⁻¹) ^ M ∣ diffC q M := by
  rw [inv_one_sub_cq, diffC_eq]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left dvd_C1_alpha _) _

theorem dvd_diffC_conj_alpha : (X - C (1 + cq q)⁻¹) ^ M ∣ diffC q M := by
  rw [inv_one_add_cq, diffC_eq]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left dvd_C1_conj_alpha _) _

/-- **The dual hypotheses hold for the gamma mixtures.** -/
theorem hyp_mixture (hq : 1 ≤ q) (hM : 1 ≤ M) :
    Hyp (pair (Dstar q M) (diffC q M)) (cq q) M (d0 (q * M)) :=
  hyp_of (natDegree_diffC_le hq hM) (cq_ne_zero (by linarith)) one_sub_cq_ne_zero
    one_add_cq_ne_zero (fun _ hi => coeff_diffC_of_lt hi) (eval_one_diffC hq hM)
    (eval_one_derivative_X_mul_diffC hq hM) dvd_diffC_alpha dvd_diffC_conj_alpha

end Mixture

end

end OptimalPrecision.Dual
