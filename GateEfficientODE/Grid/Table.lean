import GateEfficientODE.Grid.Trapezoid
import TimeDependentODE.LCHS.GaussianFull

/-!
# The analytic LCHS grid

The Gaussian LCHS integrand `k ↦ kernel w k • F k` continues holomorphically
to the strip `|Im k| ≤ 1/2`, where the complex kernel is bounded by
`exp (1 + Im k) / (π (1/4 + (Re k)²))` and the family grows at most like
`exp (D Im k)` above the real axis.  The trapezoidal rule therefore converges
exponentially in `1/h` (`StripQuadrature.trapezoid_error_op`), and a step

  `h ≤ stepBound D g ε = π / (D/2 + log (512/ν))`

suffices.  The public grid has `2K + 1` nodes `n h`, `|n| ≤ K`,
`K = ⌈R / stepBound⌉`, `h = R / K`, and coefficients `h · kernel w (n h)`:

* `gridSize_le`: `2K + 1 ≤ R (D + 2 log (512/ν)) / π + 3` nodes, so the grid
  size is `O(R (D + log (1/ν)))` rather than polynomial in `1/ν`;
* `nodes_abs_le`: every node lies in `[-R, R]`;
* `mass_le`: the coefficient mass is at most `3`;
* `table_error`: for every entire family `F` that is contractive on the closed
  lower half-plane and grows at most like `exp (D Im z)` on the upper one,
  `‖∑ c_i F (k_i) - F (-I)‖ ≤ 2ν`.

The error splits into the discrete Gaussian tail beyond `R` (bounded through
the trapezoidal sums of the Cauchy density), the trapezoidal error, and the
full-line LCHS error `exp (1 - w)` (`TimeDependentODE.GaussianLCHS.full_line_error`).
`evolution_norm_le_exp` supplies the growth bound for the complex-frequency
evolutions `exp (-i u (H + z L))` with `‖L‖ ≤ λ`, with `D = u λ`.
-/

namespace SparseHamiltonian.GateODE.AnalyticLCHS

noncomputable section
open Complex MeasureTheory Filter Set StripQuadrature ContinuousLinearMap
open scoped Interval Topology Real BigOperators InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ### Growth of the complex-frequency evolution above the real axis -/

/-- `‖exp (-i u (H + z L))‖ ≤ exp (u λ Im z)` for `Im z ≥ 0` and `‖L‖ ≤ λ`. -/
theorem evolution_norm_le_exp (D H : V →L[ℂ] V) (hD : star D = D) (hH : star H = H)
    (lam : ℝ) (hDn : ‖D‖ ≤ lam) (u : ℝ) (hu : 0 ≤ u) (z : ℂ) (hz : 0 ≤ z.im) :
    ‖ODEComplexFrequency.evolution D H u z‖ ≤ Real.exp (u * (lam * z.im)) := by
  letI : NormedAlgebra ℚ (V →L[ℂ] V) := .restrictScalars ℚ ℂ _
  set c : ℝ := lam * z.im with hcdef
  set A : V →L[ℂ] V := ODEComplexFrequency.generator D H z - (c : ℂ) • (1 : V →L[ℂ] V)
    with hAdef
  have hA : SparseHamiltonian.ODEDissipative.Dissipative A := by
    intro v
    have h1 := ODEComplexFrequency.generator_real_inner D H hD hH z v
    have h2 : (inner ℂ v (D v)).re ≤ lam * ‖v‖ ^ 2 := by
      calc (inner ℂ v (D v)).re ≤ ‖inner ℂ v (D v)‖ := Complex.re_le_norm _
        _ ≤ ‖v‖ * ‖D v‖ := norm_inner_le_norm _ _
        _ ≤ ‖v‖ * (‖D‖ * ‖v‖) := mul_le_mul_of_nonneg_left (D.le_opNorm v) (norm_nonneg _)
        _ ≤ ‖v‖ * (lam * ‖v‖) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            exact mul_le_mul_of_nonneg_right hDn (norm_nonneg _)
        _ = lam * ‖v‖ ^ 2 := by ring
    have h3 : (inner ℂ v (((c : ℂ) • (1 : V →L[ℂ] V)) v)).re = c * ‖v‖ ^ 2 := by
      rw [smul_apply, one_apply_eq_self, inner_smul_right, inner_self_eq_norm_sq_to_K]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      norm_cast
    rw [hAdef, sub_apply, inner_sub_right, Complex.sub_re, h1, h3, hcdef]
    have h4 := mul_le_mul_of_nonneg_left h2 hz
    nlinarith
  have hsplit : u • ODEComplexFrequency.generator D H z =
      u • A + u • ((c : ℂ) • (1 : V →L[ℂ] V)) := by
    rw [hAdef, smul_sub]
    abel
  have hcomm : Commute (u • A) (u • ((c : ℂ) • (1 : V →L[ℂ] V))) :=
    ((((Commute.one_right A).smul_right (c : ℂ))).smul_right u).smul_left u
  have hscalar : u • ((c : ℂ) • (1 : V →L[ℂ] V)) =
      algebraMap ℂ (V →L[ℂ] V) ((u * c : ℝ) : ℂ) := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, smul_smul]
    push_cast
    rfl
  unfold ODEComplexFrequency.evolution
  rw [hsplit, NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hcomm
    ((NormedSpace.expSeries_radius_eq_top ℂ (V →L[ℂ] V)).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℂ (V →L[ℂ] V)).symm ▸ edist_lt_top _ _),
    hscalar, ← NormedSpace.algebraMap_exp_comm]
  have hexpA := SparseHamiltonian.ODEDissipative.exp_norm_le_one A hA u hu
  have hsc : ‖algebraMap ℂ (V →L[ℂ] V) (NormedSpace.exp ((u * c : ℝ) : ℂ))‖ ≤
      Real.exp (u * c) := by
    rw [Algebra.algebraMap_eq_smul_one, ← Complex.exp_eq_exp_ℂ, norm_smul,
      ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc Real.exp (u * c) * ‖(1 : V →L[ℂ] V)‖ ≤ Real.exp (u * c) * 1 :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le) (Real.exp_pos _).le
      _ = Real.exp (u * c) := mul_one _
  calc ‖NormedSpace.exp (u • A) *
        algebraMap ℂ (V →L[ℂ] V) (NormedSpace.exp ((u * c : ℝ) : ℂ))‖
      ≤ ‖NormedSpace.exp (u • A)‖ *
          ‖algebraMap ℂ (V →L[ℂ] V) (NormedSpace.exp ((u * c : ℝ) : ℂ))‖ := norm_mul_le _ _
    _ ≤ 1 * Real.exp (u * c) := mul_le_mul hexpA hsc (norm_nonneg _) zero_le_one
    _ = Real.exp (u * c) := one_mul _

/-! ### The complex Gaussian kernel on the strip `|Im z| ≤ 1/2` -/

theorem kernel_denominator_ne (z : ℂ) (hz : |z.im| ≤ 1 / 2) :
    (Real.pi : ℂ) * (1 + z ^ 2) ≠ 0 := by
  intro h0
  have h1 := denominator_lower z hz
  rw [h0, norm_zero] at h1
  have : 0 < π * (1 / 4 + z.re ^ 2) := by have := Real.pi_pos; positivity
  linarith

theorem kernel_differentiableAt (w : ℝ) (z : ℂ) (hz : |z.im| ≤ 1 / 2) :
    DifferentiableAt ℂ (ODEGaussianComplex.kernel w) z := by
  have hnum : DifferentiableAt ℂ (ODEGaussianComplex.numerator w) z := by
    unfold ODEGaussianComplex.numerator ODEGaussianComplex.exponent
    fun_prop
  have hden : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) * (1 + z ^ 2)) z := by
    fun_prop
  exact hnum.div hden (kernel_denominator_ne z hz)

theorem kernel_norm_le (w : ℝ) (hw : 0 < w) (z : ℂ) (hz : |z.im| ≤ 1 / 2) :
    ‖ODEGaussianComplex.kernel w z‖ ≤ Real.exp (1 + z.im) / (π * (1 / 4 + z.re ^ 2)) := by
  have hden := denominator_lower z hz
  have hpos : 0 < π * (1 / 4 + z.re ^ 2) := by have := Real.pi_pos; positivity
  have hy : z.im ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hz
    nlinarith
  have hnum : ‖ODEGaussianComplex.numerator w z‖ ≤ Real.exp (1 + z.im) := by
    rw [ODEGaussianComplex.numerator, Complex.norm_exp]
    have h := ODEGaussianComplex.exponent_re w z.re z.im
    rw [Complex.re_add_im] at h
    rw [h]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ (z.re ^ 2 - z.im ^ 2 + 1) / (4 * w) :=
      div_nonneg (by nlinarith [sq_nonneg z.re]) (by positivity)
    linarith
  rw [ODEGaussianComplex.kernel, norm_div]
  calc ‖ODEGaussianComplex.numerator w z‖ / ‖(Real.pi : ℂ) * (1 + z ^ 2)‖
      ≤ Real.exp (1 + z.im) / ‖(Real.pi : ℂ) * (1 + z ^ 2)‖ :=
        div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ Real.exp (1 + z.im) / (π * (1 / 4 + z.re ^ 2)) :=
        div_le_div_of_nonneg_left (Real.exp_pos _).le hpos hden

/-! ### The public grid -/

/-- The step bound `π / (D/2 + log (512/ν))`. -/
def stepBound (D g ε : ℝ) : ℝ :=
  π / (D / 2 + Real.log (512 / ImprovedODEQueryBudget.precision g ε))

/-- Half the number of nodes, `K = ⌈R / stepBound⌉`. -/
def halfCount (D g ε : ℝ) : ℕ :=
  ⌈ImprovedODEQueryBudget.radius g ε / stepBound D g ε⌉₊

/-- The step `h = R / K`. -/
def step (D g ε : ℝ) : ℝ := ImprovedODEQueryBudget.radius g ε / halfCount D g ε

/-- The number of nodes, `2K + 1`. -/
def gridSize (D g ε : ℝ) : ℕ := 2 * halfCount D g ε + 1

/-- The nodes `(i - K) h`, `i < 2K + 1`. -/
def nodes (D g ε : ℝ) (i : Fin (gridSize D g ε)) : ℝ :=
  ((i : ℝ) - halfCount D g ε) * step D g ε

/-- The coefficients `h · kernel w (node)`. -/
def coefficients (D g ε : ℝ) (i : Fin (gridSize D g ε)) : ℂ :=
  (step D g ε : ℂ) * ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε) (nodes D g ε i)

section Facts

variable {D g ε : ℝ}

theorem log_arg_pos (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    0 < Real.log (512 / ImprovedODEQueryBudget.precision g ε) := by
  have hν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hν1 := ImprovedODEQueryBudget.precision_le_one_ten_thousandth g ε hg hεOne
  apply Real.log_pos
  rw [lt_div_iff₀ hν]
  linarith

theorem stepBound_pos (hD : 0 ≤ D) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    0 < stepBound D g ε := by
  have := log_arg_pos hg hε hεOne
  unfold stepBound
  apply div_pos Real.pi_pos
  linarith

theorem radius_pos (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    0 < ImprovedODEQueryBudget.radius g ε := by
  have h1 := ODEGaussianParameters.width_ge_two g ε hg hε hεOne
  have h2 := ODEGaussianParameters.cutoff_le_radius g ε hg hε hεOne
  linarith

theorem halfCount_pos (hD : 0 ≤ D) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    0 < halfCount D g ε := by
  unfold halfCount
  apply Nat.ceil_pos.mpr
  exact div_pos (radius_pos hg hε hεOne) (stepBound_pos hD hg hε hεOne)

theorem step_pos (hD : 0 ≤ D) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    0 < step D g ε := by
  unfold step
  have := halfCount_pos hD hg hε hεOne
  exact div_pos (radius_pos hg hε hεOne) (by exact_mod_cast this)

theorem radius_eq_mul (hD : 0 ≤ D) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ImprovedODEQueryBudget.radius g ε = (halfCount D g ε : ℝ) * step D g ε := by
  unfold step
  have := halfCount_pos hD hg hε hεOne
  have hK : (halfCount D g ε : ℝ) ≠ 0 := by exact_mod_cast this.ne'
  field_simp

theorem step_le (hD : 0 ≤ D) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    step D g ε ≤ stepBound D g ε := by
  have hB := stepBound_pos hD hg hε hεOne
  have hK := halfCount_pos hD hg hε hεOne
  have hR := radius_pos hg hε hεOne
  have hceil : ImprovedODEQueryBudget.radius g ε / stepBound D g ε ≤ halfCount D g ε :=
    Nat.le_ceil _
  unfold step
  rw [div_le_iff₀ (by exact_mod_cast hK)]
  rw [div_le_iff₀ hB] at hceil
  linarith

/-- The exponential gain of the step: `exp (π / h) ≥ exp (D/2) · 512 / ν`. -/
theorem exp_step_ge (hD : 0 ≤ D) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    Real.exp (D / 2) * (512 / ImprovedODEQueryBudget.precision g ε) ≤
      Real.exp (π / step D g ε) := by
  have hν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hh := step_pos hD hg hε hεOne
  have hhB := step_le hD hg hε hεOne
  have hlog := log_arg_pos hg hε hεOne
  have hden : 0 < D / 2 + Real.log (512 / ImprovedODEQueryBudget.precision g ε) := by
    linarith
  have h1 : D / 2 + Real.log (512 / ImprovedODEQueryBudget.precision g ε) ≤
      π / step D g ε := by
    rw [le_div_iff₀ hh]
    have h2 : stepBound D g ε * (D / 2 + Real.log (512 / ImprovedODEQueryBudget.precision g ε)) =
        π := by
      unfold stepBound
      field_simp
    nlinarith
  calc Real.exp (D / 2) * (512 / ImprovedODEQueryBudget.precision g ε)
      = Real.exp (D / 2 + Real.log (512 / ImprovedODEQueryBudget.precision g ε)) := by
        rw [Real.exp_add, Real.exp_log (by positivity)]
    _ ≤ Real.exp (π / step D g ε) := Real.exp_le_exp.mpr h1

theorem gridSize_pos : 0 < gridSize D g ε := by
  unfold gridSize
  omega

/-- **The grid size** is `O(R (D + log (1/ν)))`. -/
theorem gridSize_le (hD : 0 ≤ D) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    (gridSize D g ε : ℝ) ≤
      ImprovedODEQueryBudget.radius g ε *
        (D + 2 * Real.log (512 / ImprovedODEQueryBudget.precision g ε)) / π + 3 := by
  have hB := stepBound_pos hD hg hε hεOne
  have hR := radius_pos hg hε hεOne
  have hceil : (halfCount D g ε : ℝ) < ImprovedODEQueryBudget.radius g ε / stepBound D g ε + 1 :=
    Nat.ceil_lt_add_one (div_pos hR hB).le
  have e : ImprovedODEQueryBudget.radius g ε / stepBound D g ε =
      ImprovedODEQueryBudget.radius g ε *
        (D + 2 * Real.log (512 / ImprovedODEQueryBudget.precision g ε)) / π / 2 := by
    unfold stepBound
    have := Real.pi_pos
    field_simp
  unfold gridSize
  push_cast
  rw [e] at hceil
  linarith

/-- Every node lies in `[-R, R]`. -/
theorem nodes_abs_le (hD : 0 ≤ D) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (i : Fin (gridSize D g ε)) : |nodes D g ε i| ≤ ImprovedODEQueryBudget.radius g ε := by
  have hh := step_pos hD hg hε hεOne
  rw [radius_eq_mul hD hg hε hεOne, nodes, abs_mul, abs_of_pos hh]
  apply mul_le_mul_of_nonneg_right _ hh.le
  have hi := i.isLt
  unfold gridSize at hi
  rw [abs_le]
  constructor
  · have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
    linarith
  · have : ((i : ℕ) : ℝ) ≤ 2 * (halfCount D g ε : ℝ) := by exact_mod_cast (by omega : (i : ℕ) ≤ 2 * halfCount D g ε)
    linarith

end Facts

/-! ### Reindexing the grid by integers -/

theorem sum_fin_eq_sum_Icc {M : Type*} [AddCommMonoid M] (K : ℕ) (G : ℤ → M) :
    ∑ i : Fin (2 * K + 1), G ((i : ℤ) - K) = ∑ n ∈ Finset.Icc (-(K : ℤ)) K, G n := by
  rw [Fin.sum_univ_eq_sum_range (fun m => G ((m : ℤ) - K)) (2 * K + 1)]
  refine Finset.sum_nbij' (fun m : ℕ => (m : ℤ) - K) (fun n : ℤ => (n + K).toNat) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_range] at hm
    simp only [Finset.mem_Icc]
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  · intro m _
    simp
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    omega
  · intro m _
    rfl

theorem node_cast (D g ε : ℝ) (i : Fin (gridSize D g ε)) :
    ((nodes D g ε i : ℝ) : ℂ) = (((i : ℤ) - halfCount D g ε : ℤ) : ℂ) * (step D g ε : ℂ) := by
  unfold nodes
  push_cast
  rfl

/-! ### Mass and error -/

/-- **The coefficient mass is at most three.** -/
theorem mass_le {D g ε : ℝ} (hD : 0 ≤ D) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ODECoherentLCU.coefficientMass (coefficients D g ε) ≤ 3 := by
  set h := step D g ε with hhdef
  set K := halfCount D g ε with hKdef
  have hh : 0 < h := step_pos hD hg hε hεOne
  have hw : 0 < ODEGaussianParameters.width g ε :=
    ODEGaussianParameters.width_pos g ε hg hε hεOne
  have hν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hν1 := ImprovedODEQueryBudget.precision_le_one_ten_thousandth g ε hg hεOne
  obtain ⟨hsum, hC⟩ := cauchy_sum_le h hh
  have hterm : ∀ i : Fin (gridSize D g ε), ‖coefficients D g ε i‖ ≤
      Real.exp 1 * (h / (π * (1 + (((((i : ℤ) - K : ℤ)) : ℝ) * h) ^ 2))) := by
    intro i
    unfold coefficients
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← hhdef, abs_of_pos hh]
    have h1 := ODEGaussianKernel.norm_kernel_le_cauchy (ODEGaussianParameters.width g ε)
      (nodes D g ε i) hw
    have hnode : nodes D g ε i = (((i : ℤ) - K : ℤ) : ℝ) * h := by
      unfold nodes
      push_cast
      rfl
    rw [hnode] at h1
    calc h * ‖ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε) (nodes D g ε i)‖
        ≤ h * (Real.exp 1 / (π * (1 + ((((i : ℤ) - K : ℤ) : ℝ) * h) ^ 2))) := by
          rw [hnode]
          exact mul_le_mul_of_nonneg_left h1 hh.le
      _ = Real.exp 1 * (h / (π * (1 + ((((i : ℤ) - K : ℤ) : ℝ) * h) ^ 2))) := by ring
  have hfin : ∑ i : Fin (gridSize D g ε), h / (π * (1 + ((((i : ℤ) - K : ℤ) : ℝ) * h) ^ 2)) ≤
      ∑' n : ℤ, h / (π * (1 + ((n : ℝ) * h) ^ 2)) := by
    have e := sum_fin_eq_sum_Icc K (fun n : ℤ => h / (π * (1 + ((n : ℝ) * h) ^ 2)))
    have e' : ∑ i : Fin (gridSize D g ε), h / (π * (1 + ((((i : ℤ) - K : ℤ) : ℝ) * h) ^ 2)) =
        ∑ n ∈ Finset.Icc (-(K : ℤ)) K, h / (π * (1 + ((n : ℝ) * h) ^ 2)) := e
    rw [e']
    refine hsum.sum_le_tsum _ (fun n _ => ?_)
    have := Real.pi_pos
    positivity
  have hX := exp_step_ge hD hg hε hεOne
  have hX2 : 2 ≤ Real.exp (π / h) := by
    have h1 : 1 ≤ Real.exp (D / 2) := Real.one_le_exp (by linarith)
    have h2 : 2 ≤ 512 / ImprovedODEQueryBudget.precision g ε := by
      rw [le_div_iff₀ hν]; linarith
    nlinarith
  have hδ : 4 / (Real.exp (π / h) - 1) ≤ 1 / 64 := by
    rw [div_le_iff₀ (by linarith)]
    have h1 : 1 ≤ Real.exp (D / 2) := Real.one_le_exp (by linarith)
    have h2 : 512 ≤ 512 / ImprovedODEQueryBudget.precision g ε := by
      rw [le_div_iff₀ hν]; linarith
    nlinarith
  have he := Real.exp_one_lt_d9
  calc ODECoherentLCU.coefficientMass (coefficients D g ε)
      = ∑ i, ‖coefficients D g ε i‖ := rfl
    _ ≤ ∑ i : Fin (gridSize D g ε),
          Real.exp 1 * (h / (π * (1 + ((((i : ℤ) - K : ℤ) : ℝ) * h) ^ 2))) :=
        Finset.sum_le_sum (fun i _ => hterm i)
    _ = Real.exp 1 * ∑ i : Fin (gridSize D g ε),
          h / (π * (1 + ((((i : ℤ) - K : ℤ) : ℝ) * h) ^ 2)) := by rw [Finset.mul_sum]
    _ ≤ Real.exp 1 * (1 + 4 / (Real.exp (π / h) - 1)) :=
        mul_le_mul_of_nonneg_left (hfin.trans hC) (Real.exp_pos 1).le
    _ ≤ Real.exp 1 * (1 + 1 / 64) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos 1).le
    _ ≤ 3 := by linarith

/-! ### Numerical facts of the error budget -/

theorem exp_three_halves_le : Real.exp (3 / 2) ≤ 7.4 := by
  have h1 : Real.exp (3 / 2) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have h3 := Real.exp_one_lt_d9
  have h4 := Real.exp_pos 1
  have h5 : Real.exp 1 * Real.exp 1 ≤ 2.7182818286 * 2.7182818286 :=
    mul_le_mul h3.le h3.le h4.le (by norm_num)
  linarith

/-- The full-line residual `exp (1 - w)` is at most `7ν/8`. -/
theorem residual_le {g ε : ℝ} (hg : 1 ≤ g) (hε : 0 < ε) :
    Real.exp (1 - ODEGaussianParameters.width g ε) ≤
      7 / 8 * ImprovedODEQueryBudget.precision g ε := by
  rw [ODEGaussianParameters.residual_factor g ε hg hε]
  have hν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  have h7 : 1 / 7 ≤ 1 / (2 * π) := one_div_le_one_div_of_le (by positivity) (by linarith)
  have h8 : 8 / 7 ≤ 1 + 1 / (2 * π) := by linarith
  rw [div_le_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_left h8 (by positivity :
    (0 : ℝ) ≤ 7 / 8 * ImprovedODEQueryBudget.precision g ε)
  linarith

section Budget

variable {D g ε : ℝ}

theorem exp_step_large (hD : 0 ≤ D) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    512 ≤ 512 / ImprovedODEQueryBudget.precision g ε ∧
      512 / ImprovedODEQueryBudget.precision g ε ≤ Real.exp (π / step D g ε) := by
  have hν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hν1 := ImprovedODEQueryBudget.precision_le_one_ten_thousandth g ε hg hεOne
  have hX := exp_step_ge hD hg hε hεOne
  have hexpD : 1 ≤ Real.exp (D / 2) := Real.one_le_exp (by linarith)
  refine ⟨by rw [le_div_iff₀ hν]; linarith, ?_⟩
  exact (le_mul_of_one_le_left (by positivity) hexpD).trans hX

/-- The trapezoidal term is at most `ν / 8`. -/
theorem trapezoid_term_le (hD : 0 ≤ D) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    2 * (Real.exp (3 / 2 + D / 2) / π * π / (1 / 2)) /
        (Real.exp (2 * π * (1 / 2) / step D g ε) - 1) ≤
      ImprovedODEQueryBudget.precision g ε / 8 := by
  have hν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hX : Real.exp (D / 2) * (512 / ImprovedODEQueryBudget.precision g ε) ≤
      Real.exp (π / step D g ε) := exp_step_ge hD hg hε hεOne
  obtain ⟨h512, hbig⟩ := exp_step_large hD hg hε hεOne
  have hX2 : 2 ≤ Real.exp (π / step D g ε) := by linarith
  have hXpos : 0 < Real.exp (π / step D g ε) - 1 := by linarith
  have e1 : 2 * π * (1 / 2) / step D g ε = π / step D g ε := by ring
  have e2 : 2 * (Real.exp (3 / 2 + D / 2) / π * π / (1 / 2)) =
      4 * (Real.exp (3 / 2) * Real.exp (D / 2)) := by
    rw [Real.exp_add]
    have := Real.pi_pos
    field_simp
    ring
  rw [e1, e2, div_le_iff₀ hXpos]
  have hX' : Real.exp (D / 2) * 512 ≤
      Real.exp (π / step D g ε) * ImprovedODEQueryBudget.precision g ε := by
    have := mul_le_mul_of_nonneg_right hX hν.le
    rwa [mul_assoc, div_mul_cancel₀ _ hν.ne'] at this
  have h1 : Real.exp (3 / 2) * Real.exp (D / 2) ≤ 7.4 * Real.exp (D / 2) :=
    mul_le_mul_of_nonneg_right exp_three_halves_le (Real.exp_pos _).le
  have h2 : ImprovedODEQueryBudget.precision g ε * 2 ≤
      ImprovedODEQueryBudget.precision g ε * Real.exp (π / step D g ε) :=
    mul_le_mul_of_nonneg_left hX2 hν.le
  linarith

/-- The correction factor of the Cauchy trapezoidal sum is at most `1/64`. -/
theorem cauchy_factor_le (hD : 0 ≤ D) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    4 / (Real.exp (π / step D g ε) - 1) ≤ 1 / 64 := by
  obtain ⟨h512, hbig⟩ := exp_step_large hD hg hε hεOne
  have hXpos : 0 < Real.exp (π / step D g ε) - 1 := by linarith
  rw [div_le_iff₀ hXpos]
  linarith

end Budget

/-! ### The integrand on the strip -/

omit [CompleteSpace V] in
/-- The LCHS integrand of a contractive family with growth `exp (D Im z)` has a
Cauchy envelope on the strip `|Im z| ≤ 1/2`. -/
theorem strip_bound (F : ℂ → V →L[ℂ] V) (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1)
    {D : ℝ} (hD : 0 ≤ D) (hGrowth : ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ ≤ Real.exp (D * z.im))
    (w : ℝ) (hw : 0 < w) (z : ℂ) (hz : |z.im| ≤ 1 / 2) :
    ‖ODEGaussianComplex.kernel w z • F z‖ ≤
      (Real.exp (3 / 2 + D / 2) / π) / ((1 / 2) ^ 2 + z.re ^ 2) := by
  have hk := kernel_norm_le w hw z hz
  have hy := abs_le.mp hz
  have hFz : ‖F z‖ ≤ Real.exp (D / 2) := by
    rcases le_or_gt 0 z.im with hpos | hneg
    · refine (hGrowth z hpos).trans (Real.exp_le_exp.mpr ?_)
      have := mul_le_mul_of_nonneg_left hy.2 hD
      linarith
    · exact (hBound z hneg.le).trans (Real.one_le_exp (by linarith))
  have hpos : 0 < π * (1 / 4 + z.re ^ 2) := by have := Real.pi_pos; positivity
  rw [norm_smul]
  calc ‖ODEGaussianComplex.kernel w z‖ * ‖F z‖
      ≤ (Real.exp (1 + z.im) / (π * (1 / 4 + z.re ^ 2))) * Real.exp (D / 2) :=
        mul_le_mul hk hFz (norm_nonneg _) (by positivity)
    _ ≤ (Real.exp (3 / 2) / (π * (1 / 4 + z.re ^ 2))) * Real.exp (D / 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply div_le_div_of_nonneg_right _ hpos.le
        exact Real.exp_le_exp.mpr (by linarith)
    _ = (Real.exp (3 / 2 + D / 2) / π) / ((1 / 2) ^ 2 + z.re ^ 2) := by
        rw [Real.exp_add]
        have := Real.pi_pos
        field_simp
        ring

omit [CompleteSpace V] in
/-- The table sum as a trapezoidal sum over `|n| ≤ K`. -/
theorem finite_sum_eq (F : ℂ → V →L[ℂ] V) (D g ε : ℝ) :
    ∑ i, coefficients D g ε i • F (nodes D g ε i : ℂ) =
      (step D g ε : ℂ) • ∑ n ∈ Finset.Icc (-(halfCount D g ε : ℤ)) (halfCount D g ε),
        ODEGaussianComplex.kernel (ODEGaussianParameters.width g ε) ((n : ℂ) * step D g ε) •
          F ((n : ℂ) * step D g ε) := by
  have e1 : ∀ i : Fin (gridSize D g ε), coefficients D g ε i • F (nodes D g ε i : ℂ) =
      (step D g ε : ℂ) • (fun n : ℤ =>
        ODEGaussianComplex.kernel (ODEGaussianParameters.width g ε) ((n : ℂ) * step D g ε) •
          F ((n : ℂ) * step D g ε)) ((i : ℤ) - halfCount D g ε) := by
    intro i
    unfold coefficients
    simp only
    rw [← node_cast, mul_smul, ODEGaussianComplex.kernel_ofReal]
  simp only [e1]
  rw [← Finset.smul_sum]
  congr 1
  exact sum_fin_eq_sum_Icc (halfCount D g ε) (fun n : ℤ =>
    ODEGaussianComplex.kernel (ODEGaussianParameters.width g ε) ((n : ℂ) * step D g ε) •
      F ((n : ℂ) * step D g ε))

/-- The discrete Gaussian tail beyond the radius. -/
theorem tail_bound (F : ℂ → V →L[ℂ] V) (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1)
    {D g ε : ℝ} (hD : 0 ≤ D) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (henv : ∀ n : ℤ, ‖ODEGaussianComplex.kernel (ODEGaussianParameters.width g ε)
        ((n : ℂ) * step D g ε) • F ((n : ℂ) * step D g ε)‖ ≤
        (Real.exp (3 / 2 + D / 2) / π) / ((1 / 2) ^ 2 + ((n : ℝ) * step D g ε) ^ 2)) :
    ‖(step D g ε : ℂ) • (∑' n : ℤ,
        ODEGaussianComplex.kernel (ODEGaussianParameters.width g ε) ((n : ℂ) * step D g ε) •
          F ((n : ℂ) * step D g ε) -
      ∑ n ∈ Finset.Icc (-(halfCount D g ε : ℤ)) (halfCount D g ε),
        ODEGaussianComplex.kernel (ODEGaussianParameters.width g ε) ((n : ℂ) * step D g ε) •
          F ((n : ℂ) * step D g ε))‖ ≤
      Real.exp (1 - ODEGaussianParameters.width g ε) * (1 + 1 / 64) := by
  set w := ODEGaussianParameters.width g ε with hwdef
  set h := step D g ε with hhdef
  set K := halfCount D g ε with hKdef
  set Φ : ℤ → V →L[ℂ] V := fun n =>
    ODEGaussianComplex.kernel w ((n : ℂ) * h) • F ((n : ℂ) * h) with hΦdef
  have hh : 0 < h := step_pos hD hg hε hεOne
  have hw : 0 < w := ODEGaussianParameters.width_pos g ε hg hε hεOne
  have hRw : 2 * w ≤ ImprovedODEQueryBudget.radius g ε :=
    ODEGaussianParameters.cutoff_le_radius g ε hg hε hεOne
  have hRK : ImprovedODEQueryBudget.radius g ε = (K : ℝ) * h := radius_eq_mul hD hg hε hεOne
  set s : Finset ℤ := Finset.Icc (-(K : ℤ)) K with hsdef
  let t : ℤ → V →L[ℂ] V := fun n => if n ∈ s then 0 else Φ n
  have hsplit : ∑' n : ℤ, Φ n - ∑ n ∈ s, Φ n = ∑' n : ℤ, t n := by
    have h1 : Summable (fun n : ℤ => if n ∈ s then Φ n else 0) := by
      refine summable_of_ne_finset_zero (s := s) (fun n hn => ?_)
      simp [hn]
    have h2 : Summable t := by
      refine Summable.of_norm_bounded
        (envelope_summable (Real.exp (3 / 2 + D / 2) / π) (1 / 2) h hh) (fun n => ?_)
      simp only [t]
      split_ifs
      · rw [norm_zero]
        have := Real.pi_pos
        positivity
      · exact henv n
    have h3 : ∑' n : ℤ, (if n ∈ s then Φ n else 0) = ∑ n ∈ s, Φ n := by
      rw [tsum_eq_sum (s := s) (fun n hn => by simp [hn])]
      exact Finset.sum_congr rfl (fun n hn => by simp [hn])
    have h4 : ∑' n : ℤ, Φ n = ∑' n : ℤ, (if n ∈ s then Φ n else 0) + ∑' n : ℤ, t n := by
      rw [← h1.tsum_add h2]
      exact tsum_congr (fun n => by simp only [t]; split_ifs <;> simp)
    rw [h4, h3]
    abel
  obtain ⟨hsumC, hC⟩ := cauchy_sum_le h hh
  have hs1 : Summable (fun n : ℤ => 1 / (π * (1 + ((n : ℝ) * h) ^ 2))) := by
    have := hsumC.mul_left h⁻¹
    refine this.congr (fun n => ?_)
    field_simp
  have htail : ‖∑' n : ℤ, t n‖ ≤
      Real.exp (1 - w) * ∑' n : ℤ, 1 / (π * (1 + ((n : ℝ) * h) ^ 2)) := by
    refine tsum_of_norm_bounded (hs1.hasSum.mul_left (Real.exp (1 - w))) (fun n => ?_)
    simp only [t]
    split_ifs with hn
    · rw [norm_zero]
      have := Real.pi_pos
      positivity
    · have hn' : (K : ℤ) < |n| := by
        simp only [hsdef, Finset.mem_Icc, not_and_or, not_le] at hn
        rcases hn with hn | hn
        · rw [abs_of_neg (by omega)]
          omega
        · rw [abs_of_pos (by omega)]
          omega
      have hRle : ImprovedODEQueryBudget.radius g ε ≤ |(n : ℝ) * h| := by
        rw [abs_mul, abs_of_pos hh, hRK]
        apply mul_le_mul_of_nonneg_right _ hh.le
        have : ((K : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast hn'.le
        simpa [Int.cast_abs] using this
      have hk := ODEGaussianKernel.norm_kernel_le_width_tail w
        (ImprovedODEQueryBudget.radius g ε) ((n : ℝ) * h) hw hRw hRle
      have hcast : ((n : ℂ) * h) = (((n : ℝ) * h : ℝ) : ℂ) := by push_cast; rfl
      have hFn : ‖F (((n : ℝ) * h : ℝ) : ℂ)‖ ≤ 1 := hBound _ (by simp)
      simp only [Φ, hcast, ODEGaussianComplex.kernel_ofReal, norm_smul]
      calc ‖ODEGaussianKernel.kernel w ((n : ℝ) * h)‖ * ‖F (((n : ℝ) * h : ℝ) : ℂ)‖
          ≤ (Real.exp (1 - w) / (π * (1 + ((n : ℝ) * h) ^ 2))) * 1 :=
            mul_le_mul hk hFn (norm_nonneg _) (by have := Real.pi_pos; positivity)
        _ = Real.exp (1 - w) * (1 / (π * (1 + ((n : ℝ) * h) ^ 2))) := by ring
  have hCsum : h * ∑' n : ℤ, 1 / (π * (1 + ((n : ℝ) * h) ^ 2)) =
      ∑' n : ℤ, h / (π * (1 + ((n : ℝ) * h) ^ 2)) := by
    rw [← tsum_mul_left]
    exact tsum_congr (fun n => by field_simp)
  have hfac := cauchy_factor_le hD hg hε hεOne
  rw [hsplit, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hres0 : 0 ≤ Real.exp (1 - w) := (Real.exp_pos _).le
  calc h * ‖∑' n : ℤ, t n‖
      ≤ h * (Real.exp (1 - w) * ∑' n : ℤ, 1 / (π * (1 + ((n : ℝ) * h) ^ 2))) :=
        mul_le_mul_of_nonneg_left htail hh.le
    _ = Real.exp (1 - w) * ∑' n : ℤ, h / (π * (1 + ((n : ℝ) * h) ^ 2)) := by
        rw [← hCsum]
        ring
    _ ≤ Real.exp (1 - w) * (1 + 4 / (Real.exp (π / h) - 1)) :=
        mul_le_mul_of_nonneg_left hC hres0
    _ ≤ Real.exp (1 - w) * (1 + 1 / 64) :=
        mul_le_mul_of_nonneg_left (by linarith) hres0

/-- **The analytic table approximates the LCHS integral to `2ν`.** -/
theorem table_error (F : ℂ → V →L[ℂ] V) (hF : ∀ z, AnalyticAt ℂ F z)
    (hBound : ∀ z : ℂ, z.im ≤ 0 → ‖F z‖ ≤ 1) {D : ℝ} (hD : 0 ≤ D)
    (hGrowth : ∀ z : ℂ, 0 ≤ z.im → ‖F z‖ ≤ Real.exp (D * z.im))
    {g ε : ℝ} (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ‖(∑ i, coefficients D g ε i • F (nodes D g ε i : ℂ)) - F (-Complex.I)‖ ≤
      2 * ImprovedODEQueryBudget.precision g ε := by
  have hw : 0 < ODEGaussianParameters.width g ε :=
    ODEGaussianParameters.width_pos g ε hg hε hεOne
  have hw1 : 1 ≤ ODEGaussianParameters.width g ε :=
    ODEGaussianParameters.width_ge_one g ε hg hε hεOne
  have hh : 0 < step D g ε := step_pos hD hg hε hεOne
  have hbound : ∀ z : ℂ, |z.im| ≤ 1 / 2 →
      ‖ODEGaussianComplex.kernel (ODEGaussianParameters.width g ε) z • F z‖ ≤
        (Real.exp (3 / 2 + D / 2) / π) / ((1 / 2) ^ 2 + z.re ^ 2) :=
    fun z hz => strip_bound F hBound hD hGrowth _ hw z hz
  obtain ⟨-, -, htrap⟩ := trapezoid_error_op
    (fun z => ODEGaussianComplex.kernel (ODEGaussianParameters.width g ε) z • F z)
    (by norm_num : (0 : ℝ) < 1 / 2) hh (by norm_num : (0 : ℝ) < 1 / 2)
    (fun z hz => (kernel_differentiableAt _ z hz).smul (hF z).differentiableAt) hbound
  have htrap' := htrap.trans (trapezoid_term_le hD hg hε hεOne)
  have hfull := TimeDependentODE.GaussianLCHS.full_line_error F hF hBound _ hw1
  have hIeq : ∫ x : ℝ, ODEGaussianComplex.kernel (ODEGaussianParameters.width g ε) (x : ℂ) •
        F (x : ℂ) =
      ∫ k : ℝ, ODEGaussianKernel.kernel (ODEGaussianParameters.width g ε) k • F (k : ℂ) := by
    congr 1
    ext1 k
    rw [ODEGaussianComplex.kernel_ofReal]
  rw [← hIeq] at hfull
  have henv : ∀ n : ℤ, ‖ODEGaussianComplex.kernel (ODEGaussianParameters.width g ε)
      ((n : ℂ) * step D g ε) • F ((n : ℂ) * step D g ε)‖ ≤
      (Real.exp (3 / 2 + D / 2) / π) / ((1 / 2) ^ 2 + ((n : ℝ) * step D g ε) ^ 2) := by
    intro n
    have h1 := hbound ((n : ℂ) * step D g ε) (by simp)
    have hre : ((n : ℂ) * step D g ε).re = (n : ℝ) * step D g ε := by simp
    rwa [hre] at h1
  have htail := tail_bound F hBound hD hg hε hεOne henv
  have hres := residual_le hg hε
  rw [finite_sum_eq]
  set S := ∑ n ∈ Finset.Icc (-(halfCount D g ε : ℤ)) (halfCount D g ε),
    ODEGaussianComplex.kernel (ODEGaussianParameters.width g ε) ((n : ℂ) * step D g ε) •
      F ((n : ℂ) * step D g ε) with hSdef
  set S' := ∑' n : ℤ,
    ODEGaussianComplex.kernel (ODEGaussianParameters.width g ε) ((n : ℂ) * step D g ε) •
      F ((n : ℂ) * step D g ε) with hS'def
  set I := ∫ x : ℝ, ODEGaussianComplex.kernel (ODEGaussianParameters.width g ε) (x : ℂ) •
    F (x : ℂ) with hIdef
  have hdecomp : (step D g ε : ℂ) • S - F (-Complex.I) =
      -((step D g ε : ℂ) • (S' - S)) + ((step D g ε : ℂ) • S' - I) + (I - F (-Complex.I)) := by
    rw [smul_sub]
    abel
  rw [hdecomp]
  have hres0 : 0 ≤ Real.exp (1 - ODEGaussianParameters.width g ε) := (Real.exp_pos _).le
  calc ‖-((step D g ε : ℂ) • (S' - S)) + ((step D g ε : ℂ) • S' - I) + (I - F (-Complex.I))‖
      ≤ ‖(step D g ε : ℂ) • (S' - S)‖ + ‖(step D g ε : ℂ) • S' - I‖ + ‖I - F (-Complex.I)‖ := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ((norm_add_le _ _).trans ?_) le_rfl
        rw [norm_neg]
    _ ≤ Real.exp (1 - ODEGaussianParameters.width g ε) * (1 + 1 / 64) +
          ImprovedODEQueryBudget.precision g ε / 8 +
          Real.exp (1 - ODEGaussianParameters.width g ε) :=
        add_le_add (add_le_add htail htrap') hfull
    _ ≤ 2 * ImprovedODEQueryBudget.precision g ε := by linarith

/-- **The analytic table certificate**, uniform over a family of contractive
entire families with a common growth constant. -/
theorem table_certificate {Y : Type*} (F : Y → ℂ → V →L[ℂ] V)
    (hF : ∀ y z, AnalyticAt ℂ (F y) z) (hBound : ∀ y (z : ℂ), z.im ≤ 0 → ‖F y z‖ ≤ 1)
    (D : ℝ) (hD : 0 ≤ D) (hGrowth : ∀ y (z : ℂ), 0 ≤ z.im → ‖F y z‖ ≤ Real.exp (D * z.im))
    (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    0 < gridSize D g ε ∧
      (∀ i, |nodes D g ε i| ≤ ImprovedODEQueryBudget.radius g ε) ∧
      ODECoherentLCU.coefficientMass (coefficients D g ε) ≤ 3 ∧
      ∀ y, ‖(∑ i, coefficients D g ε i • F y (nodes D g ε i : ℂ)) - F y (-Complex.I)‖ ≤
        2 * ImprovedODEQueryBudget.precision g ε :=
  ⟨gridSize_pos, nodes_abs_le hD hg hε hεOne, mass_le hD hg hε hεOne,
    fun y => table_error (F y) (hF y) (hBound y) hD (hGrowth y) hg hε hεOne⟩

end

end SparseHamiltonian.GateODE.AnalyticLCHS
