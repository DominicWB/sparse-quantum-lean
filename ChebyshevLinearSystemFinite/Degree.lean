import ChebyshevLinearSystem.Algorithm

set_option autoImplicit false

/-!
# Finite degrees, residual amplitudes and error allowances (equation `qls:eq:finitedegree`)

For the augmented walk at the public gap `g` the Chebyshev filter of degree `D` has
`‖F_{b,D}(W) - P‖ ≤ 1/T_D(1 + 2λ) = sech(2 D arsinh χ)`, `χ = 4g/(165√s)`,
`b = χ/√(1 + χ²)` (`ChebyshevFilter.norm_filterOp_sub_le`); this residual amplitude is
`resid s g D`. Equation `qls:eq:finitedegree` uses one extra degree,

`d^fin_σ(δ) = d_σ(δ) + 1` (`finDegree`),   `δ₀ = sech(2 d^fin_σ(δ) artanh b_σ)` (`delta0`),

and here:

* `delta0_le`: `δ₀ ≤ δ / (1 + 2χ²) < δ`, since one extra degree multiplies
  `cosh(2 d artanh b) ≥ 1/δ` by at least `cosh(2 artanh b) = 1 + 2χ²` (`resid_succ_le`);
  `delta0_le_sharp`: `δ₀ ≤ δ / (1 + 2(1 - δ)χ)`, since `cosh x ≥ 1/δ` also gives
  `sinh x ≥ (1 - δ) cosh x` (`resid_succ_le_sharp`);
* `augDegree_resid`: `d_σ(sech(2 D arsinh χ)) = D`, so the released analysis at a target `δ`
  applies at every degree `D ≥ 1` with `δ = resid s g D`;
* the parameters of the finite-degree protocol: `dTestF s j = d_{σ_j}(1/100) + 1`,
  `dFinF s κ ε = d_0(ε/1000) + 1` (at the public gap `1/κ`), and the register
  `TcF = 2 (d^fin_fin + Σ_{j ≤ m} d^fin_j)`;
* the error allowances of the manuscript: `eTest s j = (δ² - δ₀²)/2` at `δ = 1/100` for the
  probability tests and `eFin s κ ε = δ - δ₀` at `δ = ε/1000` for the final attempts, with the
  explicit lower bounds `eTest s j ≥ 1/(9·10⁶ s 4^j)` and `eFin s κ ε ≥ ε/(9·10⁵ s κ²)`
  (`eTest_ge`, `eFin_ge`, from `delta0_le`) and the sharper `eTest s j ≥ 1/(825000 √s 2^j)`
  and `eFin s κ ε ≥ ε/(41250 √s κ)` (`eTest_ge_sharp`, `eFin_ge_sharp`, from
  `delta0_le_sharp`).

Notation: the regularization parameter is `σ` here and `ξ` in the manuscript, so a subscript `σ` (as
in `g_σ`, `r_σ`, `H_{σ,r}`) stands for the manuscript's subscript `ξ`.
-/

namespace ChebyshevLinearSystemFinite

noncomputable section
open SparseHamiltonian SparseLinearSystems Augmented ChebyshevFilter Endpoint
  ChebyshevLinearSystem

/-! ### Residual amplitudes -/

/-- **The residual amplitude** of the augmented-walk filter of degree `D` at the public gap `g`:
`1/T_D(1 + 2λ) = sech(2 D arsinh χ)`, `χ = 4g/(165√s)` (`resid_eq`). It bounds
`‖F_{b,D}(W) - P‖` for `b = b(g)` (`ChebyshevFilter.norm_filterOp_sub_le`). -/
def resid (s g : ℝ) (D : ℕ) : ℝ := (filterNorm (bLow s g) D)⁻¹

theorem resid_eq (s g : ℝ) (D : ℕ) :
    resid s g D = (Real.cosh (2 * D * Real.arsinh (chi s g)))⁻¹ := by
  rw [resid, filterNorm_eq_cosh (bLow_mem s g), artanh_bLow]

theorem resid_pos (s g : ℝ) (D : ℕ) : 0 < resid s g D :=
  inv_pos.mpr (filterNorm_pos (bLow_mem s g) D)

theorem chi_pos {s g : ℝ} (hs : 0 < s) (hg : 0 < g) : 0 < chi s g := by
  unfold chi
  have := Real.sqrt_pos.mpr hs
  positivity

theorem arsinh_chi_pos {s g : ℝ} (hs : 0 < s) (hg : 0 < g) : 0 < Real.arsinh (chi s g) :=
  Real.arsinh_pos_iff.mpr (chi_pos hs hg)

/-- For `D ≥ 1` the residual amplitude is below one. -/
theorem resid_lt_one {s g : ℝ} (hs : 0 < s) (hg : 0 < g) {D : ℕ} (hD : 0 < D) :
    resid s g D < 1 := by
  rw [resid_eq]
  have ha := arsinh_chi_pos hs hg
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have h1 : 1 < Real.cosh (2 * D * Real.arsinh (chi s g)) := by
    rw [Real.one_lt_cosh]
    exact (mul_pos (mul_pos two_pos hD') ha).ne'
  exact inv_lt_one_of_one_lt₀ h1

/-- **The degree of a residual amplitude**: `d_σ(sech(2 D arsinh χ)) = D`. -/
theorem augDegree_resid {s g : ℝ} (hs : 0 < s) (hg : 0 < g) (D : ℕ) :
    augDegree s g (resid s g D) = D := by
  have ha := arsinh_chi_pos hs hg
  rw [augDegree, resid_eq, one_div, inv_inv,
    Real.arcosh_cosh (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg D)) ha.le),
    show 2 * (D : ℝ) * Real.arsinh (chi s g) / (2 * Real.arsinh (chi s g)) = D by
      field_simp]
  exact Nat.ceil_natCast D

/-- `cosh(2 arsinh u) = 1 + 2u²`. -/
theorem cosh_two_arsinh (u : ℝ) : Real.cosh (2 * Real.arsinh u) = 1 + 2 * u ^ 2 := by
  rw [Real.cosh_two_mul, Real.cosh_arsinh, Real.sinh_arsinh, Real.sq_sqrt (by positivity)]
  ring

/-- **One extra degree** divides the residual amplitude by at least
`cosh(2 artanh b) = 1 + 2χ²`. -/
theorem resid_succ_le {s g : ℝ} (hs : 0 < s) (hg : 0 < g) (d : ℕ) :
    resid s g (d + 1) ≤ resid s g d / (1 + 2 * chi s g ^ 2) := by
  have ha := arsinh_chi_pos hs hg
  have hu : 0 < 1 + 2 * chi s g ^ 2 := by positivity
  rw [resid_eq, resid_eq, div_eq_mul_inv, ← mul_inv]
  apply inv_anti₀ (mul_pos (Real.cosh_pos _) hu)
  have he : 2 * ((d + 1 : ℕ) : ℝ) * Real.arsinh (chi s g) =
      2 * d * Real.arsinh (chi s g) + 2 * Real.arsinh (chi s g) := by
    push_cast
    ring
  rw [he, Real.cosh_add, cosh_two_arsinh]
  have : 0 ≤ Real.sinh (2 * d * Real.arsinh (chi s g)) * Real.sinh (2 * Real.arsinh (chi s g)) :=
    mul_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg d))
      ha.le)) (Real.sinh_nonneg_iff.mpr (mul_nonneg zero_le_two ha.le))
  linarith

/-- **One extra degree, sharper**: if `resid s g d ≤ δ ≤ 1`, one extra degree divides `δ` by at
least `1 + 2(1 - δ)χ`. With `x = 2 d arsinh χ`, `cosh x ≥ 1/δ` gives `sinh x ≥ (1 - δ) cosh x`,
and `sinh(2 arsinh χ) ≥ 2χ`, so `cosh(x + 2 arsinh χ) ≥ (1 + 2(1 - δ)χ) cosh x`. -/
theorem resid_succ_le_sharp {s g δ : ℝ} (hs : 0 < s) (hg : 0 < g) (d : ℕ)
    (hd : resid s g d ≤ δ) (hδ1 : δ ≤ 1) :
    resid s g (d + 1) ≤ δ / (1 + 2 * (1 - δ) * chi s g) := by
  have ha := arsinh_chi_pos hs hg
  have hχ := chi_pos hs hg
  set a := Real.arsinh (chi s g) with ha_def
  set x : ℝ := 2 * d * a with hx
  have hx0 : 0 ≤ x := by positivity
  have hcx : 0 < Real.cosh x := Real.cosh_pos x
  rw [resid_eq] at hd ⊢
  have hδ0 : 0 < δ := lt_of_lt_of_le (inv_pos.mpr hcx) hd
  -- `cosh x ≥ 1/δ`
  have hc : 1 ≤ δ * Real.cosh x := by
    rw [inv_le_iff_one_le_mul₀ hcx] at hd
    linarith
  -- `sinh x ≥ (1 - δ) cosh x`
  have hsx : (1 - δ) * Real.cosh x ≤ Real.sinh x := by
    have h1 : Real.cosh x - Real.sinh x = Real.exp (-x) := Real.cosh_sub_sinh x
    have h2 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith
  -- `sinh (2a) ≥ 2χ`, `cosh (2a) ≥ 1`
  have hsy : 2 * chi s g ≤ Real.sinh (2 * a) := by
    rw [Real.sinh_two_mul, Real.sinh_arsinh, Real.cosh_arsinh]
    have : 1 ≤ Real.sqrt (1 + chi s g ^ 2) := by
      rw [Real.one_le_sqrt]; nlinarith
    nlinarith
  have hcy : 1 ≤ Real.cosh (2 * a) := Real.one_le_cosh _
  have he : 2 * ((d + 1 : ℕ) : ℝ) * a = x + 2 * a := by push_cast; ring
  rw [he, Real.cosh_add]
  have hu : 0 < 1 + 2 * (1 - δ) * chi s g := by nlinarith
  have key : (1 + 2 * (1 - δ) * chi s g) / δ ≤
      Real.cosh x * Real.cosh (2 * a) + Real.sinh x * Real.sinh (2 * a) := by
    rw [div_le_iff₀ hδ0]
    have h1 : Real.cosh x ≤ Real.cosh x * Real.cosh (2 * a) := by nlinarith
    have h2 : (1 - δ) * Real.cosh x * (2 * chi s g) ≤ Real.sinh x * Real.sinh (2 * a) := by
      have h0 : 0 ≤ (1 - δ) * Real.cosh x := by nlinarith
      calc (1 - δ) * Real.cosh x * (2 * chi s g) ≤ Real.sinh x * (2 * chi s g) :=
            mul_le_mul_of_nonneg_right hsx (by positivity)
        _ ≤ Real.sinh x * Real.sinh (2 * a) :=
            mul_le_mul_of_nonneg_left hsy (le_trans h0 hsx)
    nlinarith
  have hpos : 0 < (1 + 2 * (1 - δ) * chi s g) / δ := by positivity
  calc (Real.cosh x * Real.cosh (2 * a) + Real.sinh x * Real.sinh (2 * a))⁻¹
      ≤ ((1 + 2 * (1 - δ) * chi s g) / δ)⁻¹ := inv_anti₀ hpos key
    _ = δ / (1 + 2 * (1 - δ) * chi s g) := by rw [inv_div]

/-- At the degree `d_σ(δ)` the residual amplitude is at most `δ` (Proposition
`qls:prop:chebyshev`). -/
theorem resid_augDegree_le {s g δ : ℝ} (hs : 0 < s) (hg : 0 < g) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1) : resid s g (augDegree s g δ) ≤ δ := by
  rw [resid, augDegree_eq]
  exact inv_filterNorm_chebDegree_le (Facts.bLow_pos s g hs hg) (bLow_lt_one s g) hδ0 hδ1

/-! ### The finite degree -/

/-- **The finite degree** `d^fin_σ(δ) = d_σ(δ) + 1` of equation `qls:eq:finitedegree`. -/
def finDegree (s g δ : ℝ) : ℕ := augDegree s g δ + 1

/-- **The residual amplitude at the finite degree**: `δ₀ = sech(2 d^fin_σ(δ) artanh b_σ)`
(equation `qls:eq:finitedegree`). -/
def delta0 (s g δ : ℝ) : ℝ := resid s g (finDegree s g δ)

theorem delta0_pos (s g δ : ℝ) : 0 < delta0 s g δ := resid_pos _ _ _

/-- **The finite-degree margin** (equation `qls:eq:finitedegree`): `δ₀ ≤ δ / (1 + 2χ²)`. -/
theorem delta0_le {s g δ : ℝ} (hs : 0 < s) (hg : 0 < g) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    delta0 s g δ ≤ δ / (1 + 2 * chi s g ^ 2) :=
  (resid_succ_le hs hg _).trans
    (div_le_div_of_nonneg_right (resid_augDegree_le hs hg hδ0 hδ1) (by positivity))

/-- `δ₀ < δ` (equation `qls:eq:finitedegree`). -/
theorem delta0_lt {s g δ : ℝ} (hs : 0 < s) (hg : 0 < g) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    delta0 s g δ < δ := by
  have hχ := chi_pos hs hg
  exact (delta0_le hs hg hδ0 hδ1).trans_lt (div_lt_self hδ0 (by nlinarith))

/-- **The sharper finite-degree margin**: `δ₀ ≤ δ / (1 + 2(1 - δ)χ)` (`resid_succ_le_sharp`). -/
theorem delta0_le_sharp {s g δ : ℝ} (hs : 0 < s) (hg : 0 < g) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    delta0 s g δ ≤ δ / (1 + 2 * (1 - δ) * chi s g) :=
  resid_succ_le_sharp hs hg _ (resid_augDegree_le hs hg hδ0 hδ1) hδ1

/-! ### The finite-degree protocol parameters -/

/-- **Finite test degree** `d^fin_j = d_{σ_j}(1/100) + 1` (equation `qls:eq:finitedegree`). -/
def dTestF (s j : ℕ) : ℕ := dTest s j + 1

theorem dTestF_eq (s j : ℕ) : dTestF s j = finDegree s (sig j) (1 / 100) := rfl

/-- **Finite final degree** `d^fin_0(ε/1000) = d_0(ε/1000) + 1` at the public gap `1/κ`. -/
def dFinF (s : ℕ) (κ ε : ℝ) : ℕ := dFin s κ ε + 1

theorem dFinF_eq (s : ℕ) (κ ε : ℝ) : dFinF s κ ε = finDegree s (1 / κ) (ε / 1000) := rfl

/-- The counter register size `T = 2 (d^fin_fin + Σ_{j ≤ m} d^fin_j)` of the finite-degree
protocol. -/
def TcF (s : ℕ) (κ ε : ℝ) : ℕ :=
  2 * (dFinF s κ ε + ∑ j ∈ Finset.range (stagesM κ + 1), dTestF s j)

theorem testF_fits (s : ℕ) (κ ε : ℝ) (j : ℕ) : 2 * dTestF s (stageOf κ j) ≤ TcF s κ ε := by
  have h := Finset.single_le_sum (f := fun j => dTestF s j) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (show stageOf κ j < stagesM κ + 1 by
      have := stageOf_le κ j
      omega))
  unfold TcF
  omega

theorem finalF_fits (s : ℕ) (κ ε : ℝ) : 2 * dFinF s κ ε ≤ TcF s κ ε := by
  unfold TcF
  omega

/-! ### Error allowances -/

/-- **The test allowance** `e_test = (δ² - δ₀²)/2` at `δ = 1/100` (before equation
`qls:eq:bernoulli`), with `δ₀ = δ₀(σ_j)` at the finite test degree. -/
def eTest (s j : ℕ) : ℝ := ((1 / 100) ^ 2 - delta0 s (sig j) (1 / 100) ^ 2) / 2

/-- **The final allowance** `e_fin = δ - δ₀` at `δ = ε/1000`, with `δ₀` at the finite final
degree and the public gap `1/κ`. -/
def eFin (s : ℕ) (κ ε : ℝ) : ℝ := ε / 1000 - delta0 s (1 / κ) (ε / 1000)

theorem chi_sq (s g : ℝ) (hs : 0 ≤ s) : chi s g ^ 2 = 16 * g ^ 2 / (27225 * s) := by
  unfold chi
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hs]
  norm_num

/-- The test allowance in terms of `χ_j = 4σ_j/(165√s)`:
`e_test ≥ 2 · 10⁻⁴ χ² / (1 + 2χ²)²`. -/
theorem eTest_ge_chi (s j : ℕ) (hs : 0 < s) :
    2 * (1 / 100) ^ 2 * chi s (sig j) ^ 2 / (1 + 2 * chi s (sig j) ^ 2) ^ 2 ≤ eTest s j := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hd := delta0_le hs' (sig_pos j) (by norm_num : (0 : ℝ) < 1 / 100) (by norm_num)
  have h0 := (delta0_pos (s : ℝ) (sig j) (1 / 100)).le
  unfold eTest
  generalize delta0 (s : ℝ) (sig j) (1 / 100) = d0 at hd h0 ⊢
  generalize chi (s : ℝ) (sig j) = c at hd ⊢
  have hu : 0 < 1 + 2 * c ^ 2 := by positivity
  rw [le_div_iff₀ hu] at hd
  have hsq : d0 ^ 2 * (1 + 2 * c ^ 2) ^ 2 ≤ (1 / 100) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hd 2
    rw [mul_pow] at this
    exact this
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg c, sq_nonneg (c ^ 2)]

/-- **Explicit test allowance**: `e_test ≥ 1/(9·10⁶ s 4^j)`. -/
theorem eTest_ge (s j : ℕ) (hs : 0 < s) : 1 / (9 * 10 ^ 6 * (s : ℝ) * 4 ^ j) ≤ eTest s j := by
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hsig : sig j ^ 2 * 4 ^ j = 1 := by
    unfold sig
    rw [← pow_mul, mul_comm j 2, pow_mul, ← mul_pow]
    norm_num
  have hc : chi (s : ℝ) (sig j) ^ 2 * ((s : ℝ) * 4 ^ j) = 16 / 27225 := by
    rw [chi_sq _ _ (by linarith)]
    have hs0 : (s : ℝ) ≠ 0 := by positivity
    calc 16 * sig j ^ 2 / (27225 * (s : ℝ)) * ((s : ℝ) * 4 ^ j)
        = 16 * (sig j ^ 2 * 4 ^ j) / 27225 := by field_simp
      _ = 16 / 27225 := by rw [hsig, mul_one]
  have hX : (1 : ℝ) ≤ s * 4 ^ j := by
    have : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
    nlinarith
  have h := eTest_ge_chi s j hs
  rw [show (9 * 10 ^ 6 * (s : ℝ) * 4 ^ j) = 9 * 10 ^ 6 * ((s : ℝ) * 4 ^ j) by ring]
  generalize chi (s : ℝ) (sig j) ^ 2 = c at hc h
  generalize (s : ℝ) * 4 ^ j = Y at hc hX ⊢
  have hc0 : 0 < c := by nlinarith
  have hcle : c ≤ 16 / 27225 := by nlinarith
  refine le_trans ?_ h
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left hcle hc0.le]

theorem eTest_pos (s j : ℕ) (hs : 0 < s) : 0 < eTest s j :=
  lt_of_lt_of_le (by positivity) (eTest_ge s j hs)

/-- **Sharper explicit test allowance**: `e_test ≥ χ_j 10⁻⁴/2 = 1/(825000 √s 2^j)`, from
`δ - δ₀ ≥ χ_j δ` (`delta0_le_sharp`). -/
theorem eTest_ge_sharp (s j : ℕ) (hs : 0 < s) :
    1 / (825000 * Real.sqrt s * 2 ^ j) ≤ eTest s j := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have h := delta0_le_sharp hs' (sig_pos j) (by norm_num : (0 : ℝ) < 1 / 100) (by norm_num)
  have hχ : chi (s : ℝ) (sig j) = 4 / (165 * Real.sqrt s * 2 ^ j) := by
    unfold chi sig
    rw [one_div_pow]
    field_simp
  have hsq : 1 ≤ Real.sqrt (s : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hs)
  have h2 : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  have hχle : chi (s : ℝ) (sig j) ≤ 4 / 165 := by
    rw [hχ, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul hsq h2 zero_le_one (by positivity)]
  have hr0 := delta0_pos (s : ℝ) (sig j) (1 / 100)
  unfold eTest
  generalize chi (s : ℝ) (sig j) = c at h hχ hχle
  generalize delta0 (s : ℝ) (sig j) (1 / 100) = r at h hr0 ⊢
  have hc0 : 0 < c := by rw [hχ]; positivity
  have hu : 0 < 1 + 2 * (1 - 1 / 100) * c := by nlinarith
  rw [le_div_iff₀ hu] at h
  have h4 : 0 ≤ 1 - 2 * (1 / 100 : ℝ) - 2 * (1 - 1 / 100) * c := by nlinarith
  have hk : 1 ≤ (1 - c) * (1 + 2 * (1 - 1 / 100) * c) := by nlinarith [mul_nonneg hc0.le h4]
  have hb : c * (1 / 100) ≤ 1 / 100 - r := by
    by_contra hcon
    push Not at hcon
    have h3 : 1 / 100 * (1 - c) * (1 + 2 * (1 - 1 / 100) * c) <
        r * (1 + 2 * (1 - 1 / 100) * c) := mul_lt_mul_of_pos_right (by linarith) hu
    nlinarith
  have hsq2 : c * (1 / 100) * (1 / 100) ≤ (1 / 100) ^ 2 - r ^ 2 := by nlinarith
  have e1 : 1 / (825000 * Real.sqrt s * 2 ^ j) = c * (1 / 100) * (1 / 100) / 2 := by
    rw [hχ]
    field_simp
    ring
  rw [e1]
  linarith

/-- The final allowance in terms of `χ = 4/(165 √s κ)`: `e_fin ≥ 2 (ε/1000) χ² / (1 + 2χ²)`. -/
theorem eFin_ge_chi (s : ℕ) (hs : 0 < s) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 10) :
    2 * (ε / 1000) * chi s (1 / κ) ^ 2 / (1 + 2 * chi s (1 / κ) ^ 2) ≤ eFin s κ ε := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hd := delta0_le hs' (by positivity : (0 : ℝ) < 1 / κ) (by positivity : 0 < ε / 1000)
    (by linarith)
  unfold eFin
  generalize delta0 (s : ℝ) (1 / κ) (ε / 1000) = d0 at hd ⊢
  generalize chi (s : ℝ) (1 / κ) = c at hd ⊢
  have hu : 0 < 1 + 2 * c ^ 2 := by positivity
  have e : ε / 1000 / (1 + 2 * c ^ 2) = ε / 1000 - 2 * (ε / 1000) * c ^ 2 / (1 + 2 * c ^ 2) := by
    field_simp
    ring
  linarith

/-- **Explicit final allowance**: `e_fin ≥ ε/(9·10⁵ s κ²)`. -/
theorem eFin_ge (s : ℕ) (hs : 0 < s) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    ε / (9 * 10 ^ 5 * (s : ℝ) * κ ^ 2) ≤ eFin s κ ε := by
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hκ0 : 0 < κ := by linarith
  have hc : chi (s : ℝ) (1 / κ) ^ 2 * ((s : ℝ) * κ ^ 2) = 16 / 27225 := by
    rw [chi_sq _ _ (by linarith)]
    field_simp
  have hX : (1 : ℝ) ≤ s * κ ^ 2 := by
    have : (1 : ℝ) ≤ κ ^ 2 := one_le_pow₀ hκ
    nlinarith
  have h := eFin_ge_chi s hs κ ε hκ hε hε1
  rw [show (9 * 10 ^ 5 * (s : ℝ) * κ ^ 2) = 9 * 10 ^ 5 * ((s : ℝ) * κ ^ 2) by ring]
  generalize chi (s : ℝ) (1 / κ) ^ 2 = c at hc h
  generalize (s : ℝ) * κ ^ 2 = Y at hc hX ⊢
  have hc0 : 0 < c := by nlinarith
  have hcle : c ≤ 16 / 27225 := by nlinarith
  refine le_trans ?_ h
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hεc : ε * (c * Y) = ε * (16 / 27225) := by rw [hc]
  nlinarith [mul_le_mul_of_nonneg_left hcle hε.le]

theorem eFin_pos (s : ℕ) (hs : 0 < s) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 10) :
    0 < eFin s κ ε := by
  have hκ0 : 0 < κ := by linarith
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  exact lt_of_lt_of_le (by positivity) (eFin_ge s hs κ ε hκ hε hε1)

/-- **Sharper explicit final allowance**: `e_fin ≥ χ ε/1000 = ε/(41250 √s κ)`, from
`δ - δ₀ ≥ χ δ` (`delta0_le_sharp`). -/
theorem eFin_ge_sharp (s : ℕ) (hs : 0 < s) (κ ε : ℝ) (hκ : 1 ≤ κ) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / 10) :
    ε / (41250 * Real.sqrt s * κ) ≤ eFin s κ ε := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hκ0 : 0 < κ := by linarith
  have h := delta0_le_sharp hs' (by positivity : (0 : ℝ) < 1 / κ) (by positivity : 0 < ε / 1000)
    (by linarith)
  have hχ : chi (s : ℝ) (1 / κ) = 4 / (165 * Real.sqrt s * κ) := by
    unfold chi
    field_simp
  have hsq : 1 ≤ Real.sqrt (s : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hs)
  have hχle : chi (s : ℝ) (1 / κ) ≤ 4 / 165 := by
    rw [hχ, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul hsq hκ zero_le_one (by positivity)]
  unfold eFin
  generalize chi (s : ℝ) (1 / κ) = c at h hχ hχle
  have hc0 : 0 < c := by rw [hχ]; positivity
  have hu : 0 < 1 + 2 * (1 - ε / 1000) * c := by nlinarith
  rw [le_div_iff₀ hu] at h
  generalize delta0 (s : ℝ) (1 / κ) (ε / 1000) = r at h ⊢
  have h4 : 0 ≤ 1 - 2 * (ε / 1000) - 2 * (1 - ε / 1000) * c := by nlinarith
  have hk : 1 ≤ (1 - c) * (1 + 2 * (1 - ε / 1000) * c) := by nlinarith [mul_nonneg hc0.le h4]
  have hb : c * (ε / 1000) ≤ ε / 1000 - r := by
    by_contra hcon
    push Not at hcon
    have h3 : ε / 1000 * (1 - c) * (1 + 2 * (1 - ε / 1000) * c) <
        r * (1 + 2 * (1 - ε / 1000) * c) := mul_lt_mul_of_pos_right (by linarith) hu
    nlinarith
  refine le_trans (le_of_eq ?_) hb
  rw [hχ]
  field_simp
  ring

end

end ChebyshevLinearSystemFinite
