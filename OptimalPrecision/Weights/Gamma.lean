import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Positive gamma mixtures with prescribed zeros

The two mixing polynomials of Appendix A.2 (`opt:sec:weights`):

  `A(z) = (z^{2m₀} - 2 Re(α^{m₀}) z^{m₀} + |α|^{2m₀}) / N`,
  `C₁(z) = z^{d₀} A(z)^M B_ℓ(z)`,  `C₂(z) = z^ℓ C₁(z)`,

with `α = (1 - i/q)^{-1}`, `m₀ = ⌈π/(2θ)⌉`, `θ = arctan(1/q)`, `d₀ = ⌈12a⌉`,
`ℓ = ⌈a⌉`, `a = qM`, and `B_ℓ` the uniform average of `1, z, …, z^{ℓ-1}`.
The middle coefficient is written as `-2 Re(α^{m₀})`; the polar form
`α^{m₀} = ρ^{m₀} e^{i m₀ θ}` shows it is `-2ρ^{m₀} cos(m₀θ) ≥ 0`.

Proved here: nonnegative coefficients (`coeff_C1_nonneg`, `coeff_C2_nonneg`), each
at most `1/ℓ` (`coeff_C1_le`, `coeff_C2_le`) and summing to one (`eval_one_C1`,
`sum_coeff_C1` and the same for `C₂`); `C₂ - C₁ = (z^ℓ - 1) C₁` (`C2_sub_C1`,
which gives the mean difference `ℓ` in `Weights.Dual`); vanishing below `d₀`
(`coeff_C1_of_lt`, `coeff_C2_of_lt`); the degree bound `D_*`
(`natDegree_C2_le`); zeros of multiplicity `M` at `α` and `ᾱ` (`dvd_C1_alpha`,
`dvd_C1_conj_alpha`); and the clock length `n = D_* + 1 ≤ 27a`
(`Dstar_add_one_le`, `opt:eq:degree27`), from `θ ≥ 1/(2q)`.
-/

namespace OptimalPrecision.Gamma

noncomputable section

open Polynomial Finset Real
open scoped Polynomial

variable (q : ℝ) (M : ℕ)

/-- `α = (1 - i/q)^{-1}`. -/
def alpha : ℂ := (1 - Complex.I / q)⁻¹

/-- `θ = arctan(1/q) = arg α`. -/
def theta : ℝ := Real.arctan (1 / q)

/-- `ρ = |α| = q / √(q² + 1)`. -/
def rho : ℝ := q / Real.sqrt (q ^ 2 + 1)

/-- `m₀ = ⌈π/(2θ)⌉`. -/
def m0 : ℕ := ⌈π / (2 * theta q)⌉₊

/-- `ℓ = ⌈a⌉`. -/
def ell (a : ℝ) : ℕ := ⌈a⌉₊

/-- `d₀ = ⌈12 a⌉`. -/
def d0 (a : ℝ) : ℕ := ⌈12 * a⌉₊

/-- The middle coefficient `-2 Re(α^{m₀})`. -/
def mid : ℝ := -2 * (alpha q ^ m0 q).re

/-- The constant coefficient `|α|^{2m₀}`. -/
def cst : ℝ := ‖alpha q‖ ^ (2 * m0 q)

/-- The unnormalized quadratic in `z^{m₀}`. -/
def Araw : ℝ[X] := X ^ (2 * m0 q) + C (mid q) * X ^ m0 q + C (cst q)

/-- The normalizer `A_raw(1)`. -/
def norm0 : ℝ := (Araw q).eval 1

/-- `A(z)`, with `A(1) = 1`. -/
def Apoly : ℝ[X] := C (norm0 q)⁻¹ * Araw q

/-- The uniform average `B_ℓ(z) = (1/ℓ) ∑_{j<ℓ} z^j`. -/
def Bpoly (l : ℕ) : ℝ[X] := C (l : ℝ)⁻¹ * ∑ j ∈ range l, X ^ j

/-- `C₁(z) = z^{d₀} A(z)^M B_ℓ(z)`. -/
def C1 : ℝ[X] := X ^ d0 (q * M) * Apoly q ^ M * Bpoly (ell (q * M))

/-- `C₂(z) = z^ℓ C₁(z)`. -/
def C2 : ℝ[X] := X ^ ell (q * M) * C1 q M

/-- The top degree `D_* = d₀ + 2m₀M + 2ℓ - 1`. -/
def Dstar : ℕ := d0 (q * M) + 2 * m0 q * M + 2 * ell (q * M) - 1

/-! ### The angle -/

variable {q}

theorem theta_pos (hq : 0 < q) : 0 < theta q := by
  rw [theta]; exact Real.arctan_pos.mpr (by positivity)

theorem theta_le (hq : 1 ≤ q) : theta q ≤ π / 4 := by
  rw [theta, ← Real.arctan_one]
  apply Real.arctan_mono
  rw [div_le_one (by linarith)]; exact hq

theorem sin_theta (hq : 0 < q) : Real.sin (theta q) = 1 / Real.sqrt (q ^ 2 + 1) := by
  rw [theta, Real.sin_arctan]
  have : 1 + (1 / q) ^ 2 = (q ^ 2 + 1) / q ^ 2 := by field_simp
  rw [this, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hq.le]
  field_simp

/-- `θ ≥ 1/(2q)`, from `θ ≥ sin θ = (q² + 1)^{-1/2}`. -/
theorem theta_ge (hq : 1 ≤ q) : 1 / (2 * q) ≤ theta q := by
  have hq0 : 0 < q := by linarith
  have h1 := Real.sin_le (theta_pos hq0).le
  rw [sin_theta hq0] at h1
  have hs : Real.sqrt (q ^ 2 + 1) ≤ 2 * q := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  calc 1 / (2 * q) ≤ 1 / Real.sqrt (q ^ 2 + 1) :=
        one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by positivity)) hs
    _ ≤ theta q := h1

/-- Polar form `α = ρ e^{iθ}`. -/
theorem alpha_polar (hq : 0 < q) :
    alpha q = (rho q : ℂ) * Complex.exp (theta q * Complex.I) := by
  have hs : 0 < Real.sqrt (q ^ 2 + 1) := Real.sqrt_pos.mpr (by positivity)
  have hcos : Real.cos (theta q) = q / Real.sqrt (q ^ 2 + 1) := by
    rw [theta, Real.cos_arctan]
    have : 1 + (1 / q) ^ 2 = (q ^ 2 + 1) / q ^ 2 := by field_simp
    rw [this, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hq.le]
    field_simp
  have hsin : Real.sin (theta q) = 1 / Real.sqrt (q ^ 2 + 1) := by
    rw [theta, Real.sin_arctan]
    have : 1 + (1 / q) ^ 2 = (q ^ 2 + 1) / q ^ 2 := by field_simp
    rw [this, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hq.le]
    field_simp
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hcos, hsin, alpha, rho]
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hs' : (Real.sqrt (q ^ 2 + 1) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hsq : (Real.sqrt (q ^ 2 + 1) : ℂ) ^ 2 = (q : ℂ) ^ 2 + 1 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hden : (1 - Complex.I / q) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    exact hq.ne' (by simpa using this)
  rw [inv_eq_one_div, div_eq_iff hden]
  push_cast
  field_simp
  linear_combination hsq + Complex.I_sq

theorem norm_alpha (hq : 0 < q) : ‖alpha q‖ = rho q := by
  rw [alpha_polar hq, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by unfold rho; positivity)]

theorem rho_pos (hq : 0 < q) : 0 < rho q := by
  unfold rho; positivity

theorem alpha_pow_polar (hq : 0 < q) (m : ℕ) :
    alpha q ^ m = ((rho q ^ m : ℝ) : ℂ) * Complex.exp ((m * theta q : ℝ) * Complex.I) := by
  rw [alpha_polar hq, mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

theorem m0_theta_ge (hq : 0 < q) : π / 2 ≤ m0 q * theta q := by
  have ht := theta_pos hq
  have := Nat.le_ceil (π / (2 * theta q))
  rw [m0]
  calc π / 2 = π / (2 * theta q) * theta q := by field_simp
    _ ≤ (⌈π / (2 * theta q)⌉₊ : ℝ) * theta q := by gcongr

theorem m0_theta_lt (hq : 0 < q) : m0 q * theta q < π / 2 + theta q := by
  have ht := theta_pos hq
  have h := Nat.ceil_lt_add_one (show 0 ≤ π / (2 * theta q) by positivity)
  rw [m0]
  calc (⌈π / (2 * theta q)⌉₊ : ℝ) * theta q < (π / (2 * theta q) + 1) * theta q := by gcongr
    _ = π / 2 + theta q := by field_simp

/-- The middle coefficient is nonnegative. -/
theorem mid_nonneg (hq : 1 ≤ q) : 0 ≤ mid q := by
  have hq0 : 0 < q := by linarith
  have hre : (alpha q ^ m0 q).re = rho q ^ m0 q * Real.cos (m0 q * theta q) := by
    rw [alpha_pow_polar hq0, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have hcos : Real.cos (m0 q * theta q) ≤ 0 := by
    apply Real.cos_nonpos_of_pi_div_two_le_of_le (m0_theta_ge hq0)
    have := m0_theta_lt hq0
    have := theta_le hq
    linarith [Real.pi_pos]
  rw [mid, hre]
  have : 0 ≤ rho q ^ m0 q := pow_nonneg (rho_pos hq0).le _
  nlinarith

/-! ### Coefficients of `A` -/

theorem cst_nonneg : 0 ≤ cst q := by unfold cst; positivity

theorem m0_pos (hq : 0 < q) : 0 < m0 q := by
  rw [m0, Nat.ceil_pos]
  have := theta_pos hq
  positivity

theorem norm0_pos (hq : 1 ≤ q) : 0 < norm0 q := by
  have hm := m0_pos (show 0 < q by linarith)
  simp only [norm0, Araw, eval_add, eval_pow, eval_X, one_pow, eval_mul, eval_C, mul_one]
  linarith [mid_nonneg hq, cst_nonneg (q := q)]

theorem coeff_Araw_nonneg (hq : 1 ≤ q) (n : ℕ) : 0 ≤ (Araw q).coeff n := by
  simp only [Araw, coeff_add, coeff_X_pow, coeff_C_mul, coeff_C]
  have := mid_nonneg hq
  have := cst_nonneg (q := q)
  split_ifs <;> positivity

theorem coeff_Apoly_nonneg (hq : 1 ≤ q) (n : ℕ) : 0 ≤ (Apoly q).coeff n := by
  rw [Apoly, coeff_C_mul]
  exact mul_nonneg (inv_nonneg.mpr (norm0_pos hq).le) (coeff_Araw_nonneg hq n)

theorem eval_one_Apoly (hq : 1 ≤ q) : (Apoly q).eval 1 = 1 := by
  rw [Apoly, eval_mul, eval_C, ← norm0, inv_mul_cancel₀ (norm0_pos hq).ne']

/-- `α` is a root of `A`. -/
theorem eval_alpha_Araw : ((Araw q).map Complex.ofRealHom).eval (alpha q) = 0 := by
  set y := alpha q ^ m0 q
  have hy : y * (starRingEnd ℂ) y = (cst q : ℂ) := by
    rw [Complex.mul_conj, cst, Complex.normSq_eq_norm_sq, norm_pow]
    push_cast; ring
  have hre : ((mid q : ℝ) : ℂ) = -(y + (starRingEnd ℂ) y) := by
    rw [mid, Complex.add_conj]; push_cast; ring
  simp only [Araw, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C,
    eval_add, eval_mul, eval_pow, eval_X, eval_C, Complex.ofRealHom_eq_coe]
  rw [pow_mul', ← hy, hre]
  change y ^ 2 + -(y + (starRingEnd ℂ) y) * y + y * (starRingEnd ℂ) y = 0
  ring

/-- `ᾱ` is a root of `A`. -/
theorem eval_conj_alpha_Araw :
    ((Araw q).map Complex.ofRealHom).eval ((starRingEnd ℂ) (alpha q)) = 0 := by
  have h := eval_alpha_Araw (q := q)
  rw [Polynomial.eval_map] at h ⊢
  have hcomp : (starRingEnd ℂ).comp Complex.ofRealHom = Complex.ofRealHom := by
    ext x; simp
  have key := Polynomial.hom_eval₂ (Araw q) Complex.ofRealHom (starRingEnd ℂ) (alpha q)
  rw [hcomp, h, map_zero] at key
  exact key.symm

/-! ### The mixtures `C₁`, `C₂` -/

variable {M}

theorem ell_pos {a : ℝ} (ha : 0 < a) : 0 < ell a := Nat.ceil_pos.mpr ha

theorem eval_one_Bpoly {l : ℕ} (hl : 0 < l) : (Bpoly l).eval 1 = 1 := by
  have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  simp [Bpoly, eval_finsetSum, hl']

theorem eval_one_C1 (hq : 1 ≤ q) (hM : 1 ≤ M) : (C1 q M).eval 1 = 1 := by
  have ha : 0 < q * M := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  simp only [C1, eval_mul, eval_pow, eval_X, one_pow, one_mul, eval_one_Apoly hq,
    eval_one_Bpoly (ell_pos ha)]

theorem eval_one_C2 (hq : 1 ≤ q) (hM : 1 ≤ M) : (C2 q M).eval 1 = 1 := by
  rw [C2, eval_mul, eval_pow, eval_X, one_pow, one_mul, eval_one_C1 hq hM]

theorem C2_sub_C1 : C2 q M - C1 q M = (X ^ ell (q * M) - 1) * C1 q M := by
  rw [C2]; ring

/-- The mixtures vanish below `d₀`. -/
theorem coeff_C1_of_lt {j : ℕ} (hj : j < d0 (q * M)) : (C1 q M).coeff j = 0 := by
  rw [C1, mul_assoc, coeff_X_pow_mul', if_neg (by omega)]

theorem coeff_C2_of_lt {j : ℕ} (hj : j < d0 (q * M)) : (C2 q M).coeff j = 0 := by
  rw [C2, coeff_X_pow_mul']
  split_ifs with h
  · exact coeff_C1_of_lt (by omega)
  · rfl

theorem natDegree_Araw_le (hq : 0 < q) : (Araw q).natDegree ≤ 2 * m0 q := by
  have hm := m0_pos hq
  unfold Araw
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
  · rw [natDegree_X_pow]
  · exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X_pow]; omega)
  · rw [natDegree_C]; omega

theorem natDegree_Apoly_le (hq : 0 < q) : (Apoly q).natDegree ≤ 2 * m0 q :=
  (natDegree_C_mul_le _ _).trans (natDegree_Araw_le hq)

theorem natDegree_Bpoly_le (l : ℕ) : (Bpoly l).natDegree ≤ l - 1 := by
  refine (natDegree_C_mul_le _ _).trans ?_
  apply natDegree_sum_le_of_forall_le
  intro j hj
  rw [natDegree_X_pow]
  have := Finset.mem_range.mp hj
  omega

theorem natDegree_C1_le (hq : 0 < q) :
    (C1 q M).natDegree ≤ d0 (q * M) + 2 * m0 q * M + (ell (q * M) - 1) := by
  unfold C1
  refine (natDegree_mul_le).trans (add_le_add ((natDegree_mul_le).trans
    (add_le_add (natDegree_X_pow_le _) ((natDegree_pow_le).trans ?_))) (natDegree_Bpoly_le _))
  calc M * (Apoly q).natDegree ≤ M * (2 * m0 q) := Nat.mul_le_mul_left _ (natDegree_Apoly_le hq)
    _ = 2 * m0 q * M := by ring

theorem natDegree_C2_le (hq : 1 ≤ q) (hM : 1 ≤ M) : (C2 q M).natDegree ≤ Dstar q M := by
  have ha : 0 < q * M := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hl := ell_pos ha
  unfold C2 Dstar
  refine (natDegree_mul_le).trans ?_
  have := natDegree_C1_le (M := M) (show 0 < q by linarith)
  have := natDegree_X_pow_le (R := ℝ) (ell (q * M))
  omega

theorem natDegree_C1_le_Dstar (hq : 1 ≤ q) (hM : 1 ≤ M) : (C1 q M).natDegree ≤ Dstar q M := by
  have ha : 0 < q * M := by
    have : (1 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hl := ell_pos ha
  have := natDegree_C1_le (M := M) (show 0 < q by linarith)
  unfold Dstar
  omega

/-- `(X - α)^M` divides `C₁` over `ℂ`. -/
theorem dvd_C1_alpha : (X - C (alpha q)) ^ M ∣ (C1 q M).map Complex.ofRealHom := by
  have hroot : X - C (alpha q) ∣ (Araw q).map Complex.ofRealHom :=
    dvd_iff_isRoot.mpr (eval_alpha_Araw (q := q))
  have hA : X - C (alpha q) ∣ (Apoly q).map Complex.ofRealHom := by
    rw [Apoly, Polynomial.map_mul]; exact Dvd.dvd.mul_left hroot _
  simp only [C1, Polynomial.map_mul, Polynomial.map_pow]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hA M) _) _

/-- `(X - ᾱ)^M` divides `C₁` over `ℂ`. -/
theorem dvd_C1_conj_alpha :
    (X - C ((starRingEnd ℂ) (alpha q))) ^ M ∣ (C1 q M).map Complex.ofRealHom := by
  have hroot : X - C ((starRingEnd ℂ) (alpha q)) ∣ (Araw q).map Complex.ofRealHom :=
    dvd_iff_isRoot.mpr (eval_conj_alpha_Araw (q := q))
  have hA : X - C ((starRingEnd ℂ) (alpha q)) ∣ (Apoly q).map Complex.ofRealHom := by
    rw [Apoly, Polynomial.map_mul]; exact Dvd.dvd.mul_left hroot _
  simp only [C1, Polynomial.map_mul, Polynomial.map_pow]
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hA M) _) _

/-! ### Coefficient bounds and the degree -/

theorem coeff_mul_nonneg {p r : ℝ[X]} (hp : ∀ n, 0 ≤ p.coeff n) (hr : ∀ n, 0 ≤ r.coeff n)
    (n : ℕ) : 0 ≤ (p * r).coeff n := by
  rw [coeff_mul]; exact Finset.sum_nonneg fun x _ => mul_nonneg (hp _) (hr _)

theorem coeff_pow_nonneg {p : ℝ[X]} (hp : ∀ n, 0 ≤ p.coeff n) (m n : ℕ) :
    0 ≤ (p ^ m).coeff n := by
  induction m generalizing n with
  | zero => rw [pow_zero, coeff_one]; split_ifs <;> norm_num
  | succ m ih => rw [pow_succ]; exact coeff_mul_nonneg ih hp n

theorem coeff_X_pow_nonneg (k n : ℕ) : 0 ≤ (X ^ k : ℝ[X]).coeff n := by
  rw [coeff_X_pow]; split_ifs <;> norm_num

theorem coeff_geomPoly (l k : ℕ) :
    (∑ j ∈ range l, (X : ℝ[X]) ^ j).coeff k = if k < l then 1 else 0 := by
  rw [finsetSum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem coeff_Bpoly (l k : ℕ) : (Bpoly l).coeff k = if k < l then (l : ℝ)⁻¹ else 0 := by
  rw [Bpoly, coeff_C_mul, coeff_geomPoly]
  split_ifs <;> simp

theorem coeff_Bpoly_nonneg (l k : ℕ) : 0 ≤ (Bpoly l).coeff k := by
  rw [coeff_Bpoly]; split_ifs <;> positivity

/-- Coefficients of `p ∑_{k<ℓ} X^k` are at most `p(1)` when `p ≥ 0`. -/
theorem coeff_mul_geomPoly_le {p : ℝ[X]} (hp : ∀ n, 0 ≤ p.coeff n) (l j : ℕ) :
    (p * ∑ k ∈ range l, (X : ℝ[X]) ^ k).coeff j ≤ p.eval 1 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc ∑ i ∈ range j.succ, p.coeff (i, j - i).1 * (∑ k ∈ range l, (X : ℝ[X]) ^ k).coeff (i, j - i).2
      ≤ ∑ i ∈ range j.succ, p.coeff i := by
        refine Finset.sum_le_sum fun i _ => ?_
        dsimp only
        rw [coeff_geomPoly]
        split_ifs
        · rw [mul_one]
        · rw [mul_zero]; exact hp i
    _ ≤ ∑ i ∈ range (max j p.natDegree + 1), p.coeff i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
        · intro i _ _; exact hp i
    _ = p.eval 1 := by
        rw [eval_eq_sum_range' (n := max j p.natDegree + 1) (by omega)]
        simp

theorem coeff_C1_nonneg (hq : 1 ≤ q) (j : ℕ) : 0 ≤ (C1 q M).coeff j :=
  coeff_mul_nonneg (coeff_mul_nonneg (coeff_X_pow_nonneg _)
    (coeff_pow_nonneg (coeff_Apoly_nonneg hq) M)) (coeff_Bpoly_nonneg _) j

theorem coeff_C2_nonneg (hq : 1 ≤ q) (j : ℕ) : 0 ≤ (C2 q M).coeff j :=
  coeff_mul_nonneg (coeff_X_pow_nonneg _) (coeff_C1_nonneg hq) j

/-- Each mixture coefficient is at most `1/ℓ` (the averaging factor `B_ℓ`). -/
theorem coeff_C1_le (hq : 1 ≤ q) (j : ℕ) : (C1 q M).coeff j ≤ (ell (q * M) : ℝ)⁻¹ := by
  set p : ℝ[X] := X ^ d0 (q * M) * Apoly q ^ M
  have hp : ∀ n, 0 ≤ p.coeff n :=
    coeff_mul_nonneg (coeff_X_pow_nonneg _) (coeff_pow_nonneg (coeff_Apoly_nonneg hq) M)
  have hp1 : p.eval 1 = 1 := by simp [p, eval_one_Apoly hq]
  have hC1 : C1 q M = C ((ell (q * M) : ℝ)⁻¹) * (p * ∑ k ∈ range (ell (q * M)), X ^ k) := by
    simp only [C1, Bpoly, p]; ring
  rw [hC1, coeff_C_mul]
  have hl : (0 : ℝ) ≤ (ell (q * M) : ℝ)⁻¹ := by positivity
  calc (ell (q * M) : ℝ)⁻¹ * (p * ∑ k ∈ range (ell (q * M)), X ^ k).coeff j ≤
      (ell (q * M) : ℝ)⁻¹ * p.eval 1 := mul_le_mul_of_nonneg_left (coeff_mul_geomPoly_le hp _ j) hl
    _ = (ell (q * M) : ℝ)⁻¹ := by rw [hp1, mul_one]

theorem coeff_C2_le (hq : 1 ≤ q) (j : ℕ) : (C2 q M).coeff j ≤ (ell (q * M) : ℝ)⁻¹ := by
  rw [C2, coeff_X_pow_mul']
  split_ifs
  · exact coeff_C1_le hq _
  · positivity

theorem sum_coeff_C1 (hq : 1 ≤ q) (hM : 1 ≤ M) :
    ∑ j ∈ range (Dstar q M + 1), (C1 q M).coeff j = 1 := by
  rw [← eval_one_C1 hq hM,
    eval_eq_sum_range' (n := Dstar q M + 1) (by have := natDegree_C1_le_Dstar hq hM; omega)]
  simp

theorem sum_coeff_C2 (hq : 1 ≤ q) (hM : 1 ≤ M) :
    ∑ j ∈ range (Dstar q M + 1), (C2 q M).coeff j = 1 := by
  rw [← eval_one_C2 hq hM,
    eval_eq_sum_range' (n := Dstar q M + 1) (by have := natDegree_C2_le hq hM; omega)]
  simp

theorem m0_le (hq : 1 ≤ q) : (m0 q : ℝ) ≤ π * q + 1 := by
  have hq0 : 0 < q := by linarith
  have hθ := theta_ge hq
  have hθ0 := theta_pos hq0
  have h := Nat.ceil_lt_add_one (show 0 ≤ π / (2 * theta q) by positivity)
  have h2 : π / (2 * theta q) ≤ π * q := by
    rw [div_le_iff₀ (by positivity)]
    have h3 : 1 ≤ 2 * q * theta q := by
      have := mul_le_mul_of_nonneg_left hθ (show (0 : ℝ) ≤ 2 * q by positivity)
      rwa [mul_one_div_cancel (by positivity)] at this
    nlinarith [Real.pi_pos]
  rw [m0]; linarith

/-- **The clock length**: `n = D_* + 1 ≤ 27a` (`opt:eq:degree27`). -/
theorem Dstar_add_one_le (hq : 1 ≤ q) (hM : 1 ≤ M) :
    ((Dstar q M + 1 : ℕ) : ℝ) ≤ 27 * (q * M) := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have ha : 1 ≤ q * M := by nlinarith
  have hl := ell_pos (show 0 < q * M by linarith)
  have hD : Dstar q M + 1 = d0 (q * M) + 2 * m0 q * M + 2 * ell (q * M) := by
    unfold Dstar; omega
  rw [hD]
  push_cast
  have h1 : (d0 (q * M) : ℝ) < 12 * (q * M) + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2 : (ell (q * M) : ℝ) < q * M + 1 := Nat.ceil_lt_add_one (by positivity)
  have h3 := m0_le hq
  have h4 : (m0 q : ℝ) * M ≤ (π * q + 1) * M := mul_le_mul_of_nonneg_right h3 (by positivity)
  have hpi := Real.pi_le_four
  have h5 : (π * q + 1) * M ≤ 5 * (q * M) := by nlinarith
  nlinarith

end

end OptimalPrecision.Gamma
