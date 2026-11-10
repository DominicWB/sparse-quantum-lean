import ODELowerBoundExtensions.Dyson.Degree

set_option autoImplicit false

/-!
# Eq. `odel:eq:fixed` and its consequence (`odel:lem:dyson`)

"At fixed positive `s, τ, ḡ`, this gives `Q_A = O(log(1/ε)/log log(1/ε))` (`ε → 0`). Consequently a
uniform worst-case lower bound proportional to `ḡ √s τ log(ḡ/ε)` is false under these access
assumptions: fixing any admissible positive `s, τ, ḡ` makes this comparison upper bound sublinear in
`log(1/ε)`."

Here `z = s τ` (`τ = Λ T`, `Λ` the public entry bound), and the auxiliary upper bound is
`dysonBound z ḡ ε` (eq. `odel:eq:dyson`, `Degree.lean`), which bounds the worst-case matrix
queries of the Dyson solver (`Theorem.lean`, `Outcome`).

* `dyson_fixed`: eq. `odel:eq:fixed` — `dysonBound z ḡ ε ≤ C log(1/ε)/log log(1/ε)` for all small
  `ε`, with `C` and the threshold depending only on `z` and `ḡ`;
* `eventually_lt`: for every `c > 0`, `dysonBound (s τ) ḡ ε < c ḡ √s τ log(ḡ/ε)` for all small
  `ε`.

Eq. `odel:eq:fixed` for `Q_A` itself: `Corollaries.lean` (`certificate_queries_le`,
`queries_fixed`) combines `dyson_fixed` with `dyson` for the worst-case matrix queries of the
general Dyson solver; for the ODE lower-bound class, `Family/Retry.lean` (`retry_fixed`,
`no_uniform_lower_bound`, `no_retry_witnesses`) gives eq. `odel:eq:fixed` for `Q_A` and the
refutation of the uniform bound for release-style retry protocols.
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

/-- `L_g = log(4000 ḡ) + log(1/ε)`. -/
theorem dysonLog_eq (g ε : ℝ) (hg : 1 ≤ g) (hε : 0 < ε) :
    dysonLog g ε = Real.log (4000 * g) + Real.log (1 / ε) := by
  unfold dysonLog
  have hg0 : (0 : ℝ) < 4000 * g := by linarith
  rw [show 4000 * g / ε = (4000 * g) * (1 / ε) by ring,
    Real.log_mul hg0.ne' (one_div_pos.mpr hε).ne']

/-- For `ε ≤ exp(-N)`, `N ≤ log(1/ε)`. -/
theorem le_log_one_div (N ε : ℝ) (hε : 0 < ε) (hεN : ε ≤ Real.exp (-N)) :
    N ≤ Real.log (1 / ε) := by
  have h1 : Real.log ε ≤ Real.log (Real.exp (-N)) := Real.log_le_log hε hεN
  rw [Real.log_exp] at h1
  rw [one_div, Real.log_inv]
  linarith

/-- **Eq. `odel:eq:fixed`**: at fixed `z > 0` and `ḡ ≥ 1`, the Dyson bound is
`O(log(1/ε)/log log(1/ε))` as `ε → 0`. -/
theorem dyson_fixed (z g : ℝ) (hz : 0 < z) (hg : 1 ≤ g) :
    ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      dysonBound z g ε ≤ C * (Real.log (1 / ε) / Real.log (Real.log (1 / ε))) := by
  have hg0 : 0 < g := by linarith
  have ha : 0 < Real.log (4000 * g) := Real.log_pos (by linarith)
  have hN2 := le_max_right (max (Real.log (4000 * g)) (z ^ 2)) 2
  refine ⟨16000 * g * Real.exp z * (5 + z), Real.exp (-(max (max (Real.log (4000 * g)) (z ^ 2)) 2)),
    Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith), ?_⟩
  intro ε hε hεN
  have hNu := le_log_one_div _ ε hε hεN
  have hNa := le_max_left (Real.log (4000 * g)) (z ^ 2)
  have hNz := le_max_right (Real.log (4000 * g)) (z ^ 2)
  have hNm := le_max_left (max (Real.log (4000 * g)) (z ^ 2)) 2
  set u := Real.log (1 / ε) with hu_def
  have hu0 : 0 < u := by linarith
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hL : dysonLog g ε = Real.log (4000 * g) + u := dysonLog_eq g ε hg hε
  have hL2 : dysonLog g ε ≤ 2 * u := by rw [hL]; linarith
  have hden : Real.log u / 2 ≤ Real.log (Real.exp 1 + dysonLog g ε / z) := by
    have h1 : Real.log (u / z) ≤ Real.log (Real.exp 1 + dysonLog g ε / z) := by
      apply Real.log_le_log (div_pos hu0 hz)
      have : u / z ≤ dysonLog g ε / z :=
        div_le_div_of_nonneg_right (by rw [hL]; linarith) hz.le
      linarith [Real.exp_pos 1]
    have h2 : Real.log (u / z) = Real.log u - Real.log z := Real.log_div hu0.ne' hz.ne'
    have h3 : 2 * Real.log z ≤ Real.log u := by
      have : Real.log (z ^ 2) ≤ Real.log u := Real.log_le_log (pow_pos hz 2) (by linarith)
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    linarith
  have hdenpos : 0 < Real.log (Real.exp 1 + dysonLog g ε / z) := by linarith
  have hfrac : dysonLog g ε / Real.log (Real.exp 1 + dysonLog g ε / z) ≤
      4 * (u / Real.log u) := by
    rw [div_le_iff₀ hdenpos]
    have hlu : Real.log u ≠ 0 := hlogu.ne'
    have hq : 0 ≤ 4 * (u / Real.log u) := by positivity
    calc dysonLog g ε ≤ 2 * u := hL2
      _ = 4 * (u / Real.log u) * (Real.log u / 2) := by field_simp; ring
      _ ≤ 4 * (u / Real.log u) * Real.log (Real.exp 1 + dysonLog g ε / z) :=
          mul_le_mul_of_nonneg_left hden hq
  have hone : 1 ≤ u / Real.log u := by
    rw [le_div_iff₀ hlogu, one_mul]
    linarith [Real.log_le_sub_one_of_pos hu0]
  have hpre : 0 ≤ 16000 * g * Real.exp z :=
    mul_nonneg (mul_nonneg (by norm_num) hg0.le) (Real.exp_pos z).le
  unfold dysonBound
  calc 16000 * g * Real.exp z *
        (1 + z + dysonLog g ε / Real.log (Real.exp 1 + dysonLog g ε / z))
      ≤ 16000 * g * Real.exp z * ((1 + z) * (u / Real.log u) + 4 * (u / Real.log u)) := by
        apply mul_le_mul_of_nonneg_left _ hpre
        have : (1 + z) * 1 ≤ (1 + z) * (u / Real.log u) :=
          mul_le_mul_of_nonneg_left hone (by linarith)
        linarith
    _ = 16000 * g * Real.exp z * (5 + z) * (u / Real.log u) := by ring

/-- **The Dyson bound falls below `c ḡ √s τ log(ḡ/ε)`** (the text after eq. `odel:eq:fixed`): for
fixed `s, τ > 0`, `ḡ ≥ 1` and every `c > 0`, the Dyson bound is below
`c ḡ √s τ log(ḡ/ε)` for all small `ε`. -/
theorem eventually_lt (s τ g c : ℝ) (hs : 0 < s) (hτ : 0 < τ) (hg : 1 ≤ g) (hc : 0 < c) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε, 0 < ε → ε ≤ ε₀ →
      dysonBound (s * τ) g ε < c * g * Real.sqrt s * τ * Real.log (g / ε) := by
  obtain ⟨C, ε₁, hε₁, -, hC⟩ := dyson_fixed (s * τ) g (mul_pos hs hτ) hg
  have hg0 : 0 < g := by linarith
  have hk : 0 < c * g * Real.sqrt s * τ :=
    mul_pos (mul_pos (mul_pos hc hg0) (Real.sqrt_pos.mpr hs)) hτ
  refine ⟨min ε₁ (Real.exp (-(Real.exp (|C| / (c * g * Real.sqrt s * τ)) + 1))),
    lt_min hε₁ (Real.exp_pos _), ?_⟩
  intro ε hε hε0
  have hu := le_log_one_div _ ε hε (le_trans hε0 (min_le_right _ _))
  have hb := hC ε hε (le_trans hε0 (min_le_left _ _))
  set u := Real.log (1 / ε) with hu_def
  set k := c * g * Real.sqrt s * τ with hk_def
  have he := Real.exp_pos (|C| / k)
  have hu0 : 0 < u := by linarith
  have hlogu : |C| / k < Real.log u := (Real.lt_log_iff_exp_lt hu0).mpr (by linarith)
  have hlogpos : 0 < Real.log u :=
    lt_of_le_of_lt (div_nonneg (abs_nonneg C) hk.le) hlogu
  have hlog_ge : u ≤ Real.log (g / ε) := by
    rw [show g / ε = g * (1 / ε) by ring,
      Real.log_mul hg0.ne' (one_div_pos.mpr hε).ne']
    linarith [Real.log_nonneg hg]
  have hCk : C < k * Real.log u := by
    have := (div_lt_iff₀ hk).mp hlogu
    linarith [le_abs_self C]
  have key : C * (u / Real.log u) < k * u := by
    rw [mul_div_assoc', div_lt_iff₀ hlogpos]
    nlinarith [mul_lt_mul_of_pos_right hCk hu0]
  calc dysonBound (s * τ) g ε ≤ C * (u / Real.log u) := hb
    _ < k * u := key
    _ ≤ k * Real.log (g / ε) := mul_le_mul_of_nonneg_left hlog_ge hk.le

end

end ODELowerBoundExtensions.Dyson
