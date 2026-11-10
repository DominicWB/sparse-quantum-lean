import SparseLowerBounds.Hamiltonian.Theorem

/-!
# Parameters and rounding of Theorem `odel:thm:psd`

Manuscript: Theorem `odel:thm:psd` and, in its proof, eq. `odel:eq:imaginaryamp`, the rounding
precision and the choice of `m`.
Real analysis only; no quantum objects.

* `PsdRange τ s ε`: `s ≥ 32`, `τ ≥ 1`, `ε > 0`, `L = log(1/ε) ≥ 64τ` (the paper assumes
  `τ ≥ 2`; no step uses it, `PsdRange.of_paper`). It is exactly `Hamiltonian.HSRange` (which
  already has `1 ≤ τ`) together with `64τ ≤ L`, where `ε ≤ 1/64` is derived
  (`PsdRange.toHSRange`, `PsdRange.of_HSRange`). As in the Hamiltonian lower bound,
  `h = log(e + L/τ)`, `r = L/h` (`Hamiltonian.hsR`) and `n = ⌊r/4⌋` (`Hamiltonian.precN`);
  `u = τ/2`.
* `psdMu s = hsMu (s - 1)`: `m = 2^{psdMu s}` is the largest power of two at most `(s-1)/2`,
  so `2m + 1 ≤ s` and `m > s/8` (proof of Theorem `odel:thm:psd`).
* `psdAmp n u = e^{-u} sinh(u/n)^n` (eq. `odel:eq:imaginaryamp`, the amplitude `a`), the
  rounding precision `psdDelta n u = min{1/(2√n), a/(16u)}` (`1/(2√n) ≤ ½ min_k b_k`)
  and the rounded dyadic weights `psdWeight n u k = N_k/2^F` of `b_k` (`Hamiltonian.roundNum`,
  `Hamiltonian.roundBits`, as `Hamiltonian.chainWeight`).
* The numerics at the main parameters are in `Psd/Numerics`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

namespace ODELowerBoundExtensions.Psd

noncomputable section
open SparseLowerBounds SparseLowerBounds.Hamiltonian
open scoped Matrix.Norms.L2Operator

/-! ### The parameter range -/

/-- **The parameter range of Theorem `odel:thm:psd`** (Theorem `odel:thm:psd`): `s ≥ 32`, `τ ≥ 1`,
`ε > 0` and `L = log(1/ε) ≥ 64τ`. The paper states `τ ≥ 2`; the proof never uses more than
`τ ≥ 1`, so this range contains the paper's (`PsdRange.of_paper`). -/
structure PsdRange (τ : ℝ) (s : ℕ) (ε : ℝ) : Prop where
  s_ge : 32 ≤ s
  one_le_tau : 1 ≤ τ
  eps_pos : 0 < ε
  hL : 64 * τ ≤ hsL ε

variable {τ ε : ℝ} {s : ℕ}

/-- The paper's range `s ≥ 32`, `τ ≥ 2`, `L ≥ 64τ` (Theorem `odel:thm:psd`) is inside `PsdRange`. -/
theorem PsdRange.of_paper (hs : 32 ≤ s) (hτ : 2 ≤ τ) (hε : 0 < ε) (hL : 64 * τ ≤ hsL ε) :
    PsdRange τ s ε :=
  ⟨hs, by linarith, hε, hL⟩

/-- `PsdRange` is inside the range of Theorem `hsl:thm:main` (`ε ≤ 1/64` from `L ≥ 64`). -/
theorem PsdRange.toHSRange (h : PsdRange τ s ε) : HSRange τ s ε := by
  refine ⟨h.one_le_tau, h.s_ge, h.eps_pos, ?_⟩
  have hL : 64 ≤ hsL ε := by linarith [h.hL, h.one_le_tau]
  have h1 : Real.exp (-hsL ε) ≤ Real.exp (-64) := Real.exp_le_exp.mpr (by linarith)
  have h2 : (65 : ℝ) ≤ Real.exp 64 := by linarith [Real.add_one_le_exp (64 : ℝ)]
  rw [Real.exp_neg 64, exp_neg_hsL h.eps_pos] at h1
  calc ε ≤ (Real.exp 64)⁻¹ := h1
    _ ≤ 1 / 64 := by rw [one_div]; exact inv_anti₀ (by norm_num) (by linarith)

/-- The released precision range `HSRange τ s ε` with `64τ ≤ L` (the hypotheses `(h, hL)` of
`ODE.mixed_forces`, `ODE.precision_forces`) is `PsdRange`. -/
theorem PsdRange.of_HSRange (h : HSRange τ s ε) (hL : 64 * τ ≤ hsL ε) : PsdRange τ s ε :=
  ⟨h.s_ge, h.one_le_tau, h.eps_pos, hL⟩

/-! ### The register size `m` (proof of Theorem `odel:thm:psd`) -/

/-- `log₂ m` for the largest power of two `m ≤ (s-1)/2` (proof of Theorem `odel:thm:psd`). -/
def psdMu (s : ℕ) : ℕ := hsMu (s - 1)

/-- `μ ≥ 1` (indeed `m ≥ 8`) for `s ≥ 32`. -/
theorem one_le_psdMu (hs : 32 ≤ s) : 1 ≤ psdMu s := by
  have h4 : 4 ≤ Nat.log 2 (s - 1) := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  unfold psdMu hsMu
  omega

/-- `2m + 1 ≤ s`: a path row (two register blocks and the diagonal) fits in `s` slots. -/
theorem two_mul_psdM_add_one_le (hs : 32 ≤ s) : 2 * 2 ^ psdMu s + 1 ≤ s := by
  have h := two_pow_hsMu_succ_le (s := s - 1) (by omega)
  rw [pow_succ] at h
  unfold psdMu
  generalize 2 ^ hsMu (s - 1) = m at h ⊢
  omega

/-- `m > s/8` (proof of Theorem `odel:thm:psd`). -/
theorem psdM_gt (hs : 32 ≤ s) : (s : ℝ) / 8 < (2 : ℝ) ^ psdMu s := by
  have h1 := lt_two_pow_hsMu_add_two (s := s - 1) (by omega)
  rw [pow_add] at h1
  have h2 : s ≤ 2 ^ psdMu s * 4 := by
    unfold psdMu
    norm_num at h1
    generalize 2 ^ hsMu (s - 1) = m at h1 ⊢
    omega
  have h3 : (s : ℝ) ≤ (2 : ℝ) ^ psdMu s * 4 := by exact_mod_cast h2
  have h4 : (0 : ℝ) < (2 : ℝ) ^ psdMu s := by positivity
  linarith

/-! ### The amplitude and the rounded weights (eq. `odel:eq:imaginaryamp` and proof of Theorem `odel:thm:psd`) -/

/-- **The imaginary-time amplitude** `a = e^{-u} sinh(u/n)^n` (eq. `odel:eq:imaginaryamp`). -/
def psdAmp (n : ℕ) (u : ℝ) : ℝ := Real.exp (-u) * Real.sinh (u / n) ^ n

/-- The rounding precision `δ = min{1/(2√n), a/(16u)}` (proof of Theorem `odel:thm:psd`;
`1/(2√n) ≤ ½ min_k b_k` since `b_k ≥ 1/√n`, `Hamiltonian.inv_sqrt_le_spinWeight`). -/
def psdDelta (n : ℕ) (u : ℝ) : ℝ := min (1 / (2 * Real.sqrt n)) (psdAmp n u / (16 * u))

/-- The fractional bits `F` of the rounded weights, `2^{-F} ≤ δ`. -/
def psdBits (n : ℕ) (u : ℝ) : ℕ := roundBits (psdDelta n u)

/-- The integer numerator `N_k` of the rounded weight `b'_k = N_k/2^F` of `b_k`. -/
def psdNum (n : ℕ) (u : ℝ) (k : ℕ) : ℕ := roundNum (psdBits n u) (spinWeight n k)

/-- **The rounded dyadic weight** `b'_k = N_k/2^F` (proof of Theorem `odel:thm:psd`: `b_k` rounded
down). -/
def psdWeight (n : ℕ) (u : ℝ) (k : ℕ) : ℝ := (psdNum n u k : ℝ) / 2 ^ psdBits n u

variable {n : ℕ} {u : ℝ}

/-- `a > 0` for `n ≥ 1`, `u > 0`. -/
theorem psdAmp_pos (hn : 1 ≤ n) (hu : 0 < u) : 0 < psdAmp n u := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  exact mul_pos (Real.exp_pos _) (pow_pos (Real.sinh_pos_iff.mpr (div_pos hu hn')) _)

/-- **Eq. `odel:eq:alower`, first step** (proof of Theorem `odel:thm:psd`): `a ≥ (u/(en))^n` for
`0 < u ≤ n` (`sinh z ≥ z`, `e^{-u} ≥ e^{-n}`). -/
theorem psdAmp_ge (hn : 1 ≤ n) (hu : 0 < u) (hun : u ≤ n) :
    (u / (Real.exp 1 * n)) ^ n ≤ psdAmp n u := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hz : 0 ≤ u / n := (div_pos hu hn').le
  have hs : (u / n) ^ n ≤ Real.sinh (u / n) ^ n :=
    pow_le_pow_left₀ hz (Real.self_le_sinh_iff.mpr hz) n
  have he : Real.exp (-(n : ℝ)) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
  have he' : Real.exp (-(n : ℝ)) = (Real.exp 1 ^ n)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul, mul_one]
  have hl : (u / (Real.exp 1 * n)) ^ n = Real.exp (-(n : ℝ)) * (u / n) ^ n := by
    rw [he', mul_comm (Real.exp 1), ← div_div, div_pow, div_eq_inv_mul]
  unfold psdAmp
  rw [hl]
  exact mul_le_mul he hs (by positivity) (Real.exp_pos _).le

/-- `δ > 0`. -/
theorem psdDelta_pos (hn : 1 ≤ n) (hu : 0 < u) : 0 < psdDelta n u := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  exact lt_min (by positivity) (div_pos (psdAmp_pos hn hu) (by positivity))

/-- The numerator is strictly below `2^F`. -/
theorem psdNum_lt (n : ℕ) (u : ℝ) (k : ℕ) : psdNum n u k < 2 ^ psdBits n u := by
  exact (roundNum_le _ _).trans_lt (Nat.sub_lt (Nat.two_pow_pos _) one_pos)

/-- Rounding down: `0 ≤ b'_k ≤ b_k`. -/
theorem psdWeight_le (n : ℕ) (u : ℝ) (k : ℕ) :
    0 ≤ psdWeight n u k ∧ psdWeight n u k ≤ spinWeight n k := by
  unfold psdWeight psdNum
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  exact roundNum_le_mul (spinWeight_nonneg n k) _

/-- Every edge stays nonzero and within `δ` of `b_k` (proof of Theorem `odel:thm:psd`). -/
theorem psdWeight_pos (hn : 1 ≤ n) (hu : 0 < u) {k : ℕ} (hk : k < n) :
    spinWeight n k - psdWeight n u k ≤ psdDelta n u ∧ 0 < psdWeight n u k := by
  have h1 : spinWeight n k - psdWeight n u k ≤ psdDelta n u :=
    (sub_roundNum_le (spinWeight_nonneg n k) (spinWeight_le_one n k) (psdBits n u)).trans
      (two_pow_roundBits_inv_le (psdDelta_pos hn hu))
  refine ⟨h1, ?_⟩
  have h2 : psdDelta n u ≤ 1 / (2 * Real.sqrt n) := min_le_left _ _
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have h3 : 1 / (2 * Real.sqrt n) ≤ 1 / 2 * spinWeight n k := by
    have he : 1 / (2 * Real.sqrt n) = 1 / 2 * (Real.sqrt n)⁻¹ := by
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left (inv_sqrt_le_spinWeight hk) (by positivity)
  have h4 := spinWeight_pos hk
  linarith

/-- The rounded path has norm at most one (proof of Theorem `odel:thm:psd`, entrywise comparison
with `B_n`). -/
theorem norm_pathMatrix_psdWeight_le (n : ℕ) (u : ℝ) : ‖pathMatrix n (psdWeight n u)‖ ≤ 1 := by
  exact norm_pathMatrix_le (fun k => (psdWeight_le n u k).1) (fun k _ => (psdWeight_le n u k).2)

/-- `‖B_n - B'_n‖ ≤ 2δ` (proof of Theorem `odel:thm:psd`, `Hamiltonian.norm_pathMatrix_sub_le`). -/
theorem norm_pathMatrix_sub_psdWeight_le (hn : 1 ≤ n) (hu : 0 < u) :
    ‖pathMatrix n (spinWeight n) - pathMatrix n (psdWeight n u)‖ ≤ 2 * psdDelta n u := by
  refine norm_pathMatrix_sub_le (psdDelta_pos hn hu).le fun k hk => ?_
  rw [abs_of_nonneg (sub_nonneg.mpr (psdWeight_le n u k).2)]
  exact (psdWeight_pos hn hu hk).1

end

end ODELowerBoundExtensions.Psd
