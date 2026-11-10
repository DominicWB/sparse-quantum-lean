import SparseLowerBounds.Hamiltonian.Accuracy
import UnitaryImplementationExtensions.Search

set_option autoImplicit false

/-!
# From operator-norm error to trace distance, sharply

Corollary `hs:cor:unitary` of the manuscript measures the error of a unitary
implementation in operator norm, `‖A_U - U‖ ≤ ε` (eq. `hs:eq:unitaryerror`),
for `0 < ε ≤ 1/2`. The package's lower bounds for adaptive and measured algorithms take
trace-distance accuracy of the output. For two unit vectors at distance `d = ‖a - b‖` the trace
distance of the pure states is `√(1 - |⟪a, b⟫|²) ≤ d √(1 - d²/4)`. The package's vector form of
that passage is `UnitaryImplementationExtensions.Search.norm_sub_proj_le` (the component of a
unit vector orthogonal to a unit vector within `ε ≤ 1` has norm at most `ε √(1 - ε²/4)`); this
module proves its observable form, for vectors of norm at most one and `ε² ≤ 2`:

* `abs_re_inner_sub_le_sharp`: for vectors `a`, `b` of norm at most one with `‖a - b‖ ≤ ε`
  (`ε² ≤ 2`) and every self-adjoint contraction `L`,
  `|Re⟪a, L a⟫ - Re⟪b, L b⟫| ≤ 2 ε √(1 - ε²/4)`. The proof writes the difference as
  `Re⟪a + b, L (a - b)⟫` and uses `‖a + b‖² ≤ 4 - ‖a - b‖²` (parallelogram law,
  `norm_add_sq_le`);
* `accurate_of_endpoint_sharp`: the analogue of
  `SparseLowerBounds.Hamiltonian.accurate_of_endpoint`, under the same hypotheses and
  `ε² ≤ 2`, with the sharp constant `ε √(1 - ε²/4)` in place of `ε`;
* the constants: `ε √(1 - ε²/4) ≤ ε`, and `ε √(1 - ε²/4) ≤ √15 / 8 < 1/2` on the range
  `0 ≤ ε ≤ 1/2`, which contains the manuscript's `0 < ε ≤ 1/2` (Corollary `hs:cor:unitary`)
  (`sharp_lt_half`, a corollary of the positivity
  `UnitaryImplementationExtensions.Search.near_factor_pos`), and the comparison
  `(N - 2)² ≤ 4 (N (1 - s) - 1)²` for `s ≤ 1/2` used for the `√N` forms.
-/

namespace MeasuredUnitaryLowerBound.OperatorNorm

noncomputable section
open SparseHamiltonian SparseLowerBounds SparseLowerBounds.Readout ContinuousLinearMap
open scoped InnerProduct InnerProductSpace

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For a self-adjoint `L`, `Re⟪a, L a⟫ - Re⟪b, L b⟫ = Re⟪a + b, L (a - b)⟫`. -/
theorem re_inner_sub_eq (L : H →L[ℂ] H) (hL : IsSelfAdjoint L) (a b : H) :
    (⟪a, L a⟫_ℂ).re - (⟪b, L b⟫_ℂ).re = (⟪a + b, L (a - b)⟫_ℂ).re := by
  have h1 : ⟪b, L a⟫_ℂ = (starRingEnd ℂ) ⟪a, L b⟫_ℂ := by
    rw [inner_conj_symm, ← ContinuousLinearMap.adjoint_inner_left, hL.adjoint_eq]
  rw [inner_add_left, map_sub, inner_sub_right, inner_sub_right, h1]
  simp only [Complex.sub_re, Complex.add_re, Complex.conj_re]
  ring

omit [CompleteSpace H] in
/-- For vectors of norm at most one, `‖a + b‖² ≤ 4 - ‖a - b‖²` (parallelogram law,
`‖a + b‖² + ‖a - b‖² = 2 ‖a‖² + 2 ‖b‖²`). -/
theorem norm_add_sq_le {a b : H} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    ‖a + b‖ ^ 2 ≤ 4 - ‖a - b‖ ^ 2 := by
  have h := parallelogram_law_with_norm ℂ a b
  have ha2 : ‖a‖ * ‖a‖ ≤ 1 := mul_le_one₀ ha (norm_nonneg a) ha
  have hb2 : ‖b‖ * ‖b‖ ≤ 1 := mul_le_one₀ hb (norm_nonneg b) hb
  nlinarith

/-- `d √(4 - d²)` is monotone on `0 ≤ d`, `d² ≤ 2`: for `0 ≤ d ≤ ε` and `ε² ≤ 2`,
`d √(4 - d²) ≤ 2 ε √(1 - ε²/4)`. -/
theorem mul_sqrt_four_sub_le {d ε : ℝ} (hd : 0 ≤ d) (hdε : d ≤ ε) (hε : ε ^ 2 ≤ 2) :
    d * Real.sqrt (4 - d ^ 2) ≤ 2 * (ε * Real.sqrt (1 - ε ^ 2 / 4)) := by
  have hε0 : 0 ≤ ε := hd.trans hdε
  have e1 : d ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hd hdε 2
  have hk := mul_nonneg (sub_nonneg.2 e1) (by linarith : 0 ≤ 4 - ε ^ 2 - d ^ 2)
  have s1 := Real.sq_sqrt (by linarith : 0 ≤ 4 - d ^ 2)
  have s2 := Real.sq_sqrt (by linarith : 0 ≤ 1 - ε ^ 2 / 4)
  have hx : 0 ≤ d * Real.sqrt (4 - d ^ 2) := mul_nonneg hd (Real.sqrt_nonneg _)
  have hy : 0 ≤ 2 * (ε * Real.sqrt (1 - ε ^ 2 / 4)) :=
    mul_nonneg zero_le_two (mul_nonneg hε0 (Real.sqrt_nonneg _))
  refine (sq_le_sq₀ hx hy).1 ?_
  have ex : (d * Real.sqrt (4 - d ^ 2)) ^ 2 = d ^ 2 * (4 - d ^ 2) := by rw [mul_pow, s1]
  have ey : (2 * (ε * Real.sqrt (1 - ε ^ 2 / 4))) ^ 2 = ε ^ 2 * (4 - ε ^ 2) := by
    rw [mul_pow, mul_pow, s2]; ring
  rw [ex, ey]
  nlinarith

/-- **Sharp comparison of two vectors.** For vectors `a`, `b` of norm at most one with
`‖a - b‖ ≤ ε` and `ε² ≤ 2`, and every self-adjoint contraction `L`,
`|Re⟪a, L a⟫ - Re⟪b, L b⟫| ≤ 2 ε √(1 - ε²/4)`: for unit vectors, the two pure states are within
trace distance `ε √(1 - ε²/4)`. This is the observable form of
`UnitaryImplementationExtensions.Search.norm_sub_proj_le` for subnormalised vectors. -/
theorem abs_re_inner_sub_le_sharp (L : H →L[ℂ] H) (hL : IsSelfAdjoint L) (hL1 : ‖L‖ ≤ 1)
    {a b : H} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) {ε : ℝ} (hab : ‖a - b‖ ≤ ε) (hε : ε ^ 2 ≤ 2) :
    |(⟪a, L a⟫_ℂ).re - (⟪b, L b⟫_ℂ).re| ≤ 2 * (ε * Real.sqrt (1 - ε ^ 2 / 4)) := by
  rw [re_inner_sub_eq L hL]
  have hd0 : 0 ≤ ‖a - b‖ := norm_nonneg _
  have hplus : ‖a + b‖ ≤ Real.sqrt (4 - ‖a - b‖ ^ 2) :=
    (le_abs_self _).trans (Real.abs_le_sqrt (norm_add_sq_le ha hb))
  have hLd : ‖L (a - b)‖ ≤ ‖a - b‖ :=
    (L.le_opNorm _).trans (by nlinarith [norm_nonneg L])
  calc |(⟪a + b, L (a - b)⟫_ℂ).re| ≤ ‖⟪a + b, L (a - b)⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖a + b‖ * ‖L (a - b)‖ := norm_inner_le_norm _ _
    _ ≤ Real.sqrt (4 - ‖a - b‖ ^ 2) * ‖a - b‖ :=
        mul_le_mul hplus hLd (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = ‖a - b‖ * Real.sqrt (4 - ‖a - b‖ ^ 2) := mul_comm _ _
    _ ≤ 2 * (ε * Real.sqrt (1 - ε ^ 2 / 4)) := mul_sqrt_four_sub_le hd0 hab hε

end Hilbert

/-- **Operator-norm error gives sharp trace-distance accuracy** (eq. `hs:eq:unitaryerror`). If
`‖V ∘ ι - ι ∘ U‖ ≤ ε` for a contraction `V` and an isometric encoding `ι`, with `ε² ≤ 2`, then for
every input `ψ` with `‖ψ‖ ≤ 1` and `‖U ψ‖ ≤ 1`, the output `V (ι ψ)` read through
`endpointReadout ι i₀` is `ε √(1 - ε²/4)`-accurate for `U ψ`. This is the analogue of
`SparseLowerBounds.Hamiltonian.accurate_of_endpoint`, under its hypotheses and `ε² ≤ 2`, with the
sharp constant `ε √(1 - ε²/4)` in place of `ε`. -/
theorem accurate_of_endpoint_sharp {S K : Type*} [Fintype S] [DecidableEq S]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (ι : EuclideanSpace ℂ S →L[ℂ] K) (hι : ι† ∘L ι = 1) (i₀ : S) (V : K →L[ℂ] K)
    (hV : ‖V‖ ≤ 1) (U : EuclideanSpace ℂ S →L[ℂ] EuclideanSpace ℂ S) {ψ : EuclideanSpace ℂ S}
    (hψ : ‖ψ‖ ≤ 1) (hUψ : ‖U ψ‖ ≤ 1) {ε : ℝ} (hε : ε ^ 2 ≤ 2)
    (hErr : ‖V ∘L ι - ι ∘L U‖ ≤ ε) :
    Accurate (Hamiltonian.endpointReadout ι i₀) (V (ι ψ)) (U ψ)
      (ε * Real.sqrt (1 - ε ^ 2 / 4)) := by
  intro M hM hM1
  rw [← Hamiltonian.inner_outObs_endpointReadout ι hι i₀ M (U ψ)]
  have hL : ‖outObs (Hamiltonian.endpointReadout ι i₀) M‖ ≤ 1 :=
    (norm_outObs_le _ (Hamiltonian.endpointReadout_isometry ι hι i₀) M).trans hM1
  have hLsa : IsSelfAdjoint (outObs (Hamiltonian.endpointReadout ι i₀) M) :=
    (isSelfAdjoint_liftObs hM).adjoint_conj _
  have hι1 := Hamiltonian.Accuracy.norm_iota_le hι
  have hιψ : ‖ι ψ‖ ≤ 1 :=
    (ι.le_opNorm ψ).trans (by nlinarith [norm_nonneg ι, norm_nonneg ψ])
  have ha : ‖V (ι ψ)‖ ≤ 1 :=
    (V.le_opNorm _).trans (by nlinarith [norm_nonneg V, norm_nonneg (ι ψ)])
  have hb : ‖ι (U ψ)‖ ≤ 1 :=
    (ι.le_opNorm _).trans (by nlinarith [norm_nonneg ι, norm_nonneg (U ψ)])
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hErr
  have hd : ‖V (ι ψ) - ι (U ψ)‖ ≤ ε := by
    have hsub : V (ι ψ) - ι (U ψ) = (V ∘L ι - ι ∘L U) ψ := by simp
    rw [hsub]
    calc ‖(V ∘L ι - ι ∘L U) ψ‖ ≤ ‖V ∘L ι - ι ∘L U‖ * ‖ψ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * 1 := mul_le_mul hErr hψ (norm_nonneg _) hε0
      _ = ε := mul_one _
  exact abs_re_inner_sub_le_sharp _ hLsa hL ha hb hd hε

/-! ### The constants -/

/-- The sharp error is nonnegative. -/
theorem sharp_nonneg {ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ ε * Real.sqrt (1 - ε ^ 2 / 4) := by
  exact mul_nonneg hε (Real.sqrt_nonneg _)

/-- The sharp error is at most the operator-norm error. -/
theorem sharp_le_self {ε : ℝ} (hε : 0 ≤ ε) : ε * Real.sqrt (1 - ε ^ 2 / 4) ≤ ε := by
  have h1 : Real.sqrt (1 - ε ^ 2 / 4) ≤ 1 :=
    (Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε] : 1 - ε ^ 2 / 4 ≤ 1)).trans_eq Real.sqrt_one
  exact mul_le_of_le_one_right hε h1

/-- On the range `0 ≤ ε ≤ 1/2`, which contains the manuscript's `0 < ε ≤ 1/2` (Corollary
`hs:cor:unitary`), the sharp error is at most `√15 / 8`, its value at `ε = 1/2`. -/
theorem sharp_le_of_le_half {ε : ℝ} (hε : 0 ≤ ε) (h : ε ≤ 1 / 2) :
    ε * Real.sqrt (1 - ε ^ 2 / 4) ≤ Real.sqrt 15 / 8 := by
  have e1 : ε ^ 2 ≤ 1 / 4 := by nlinarith
  have s2 := Real.sq_sqrt (by linarith : 0 ≤ 1 - ε ^ 2 / 4)
  have s15 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 15)
  have hx : 0 ≤ ε * Real.sqrt (1 - ε ^ 2 / 4) := mul_nonneg hε (Real.sqrt_nonneg _)
  have hy : 0 ≤ Real.sqrt 15 / 8 := by positivity
  refine (sq_le_sq₀ hx hy).1 ?_
  rw [mul_pow, s2, div_pow, s15]
  have hk := mul_nonneg (sub_nonneg.2 e1) (by linarith : (0 : ℝ) ≤ 15 / 4 - ε ^ 2)
  nlinarith

/-- The sharp error at `ε = 1/2` is `√15 / 8`. -/
theorem sharp_half : (1 / 2 : ℝ) * Real.sqrt (1 - (1 / 2 : ℝ) ^ 2 / 4) = Real.sqrt 15 / 8 := by
  have h : (1 : ℝ) - (1 / 2 : ℝ) ^ 2 / 4 = 15 / 4 ^ 2 := by norm_num
  rw [h, Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by norm_num)]
  ring

/-- `√15 / 8 < 1/2`. -/
theorem sqrt_fifteen_div_eight_lt_half : Real.sqrt 15 / 8 < 1 / 2 := by
  have h : Real.sqrt 15 < 4 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  linarith

/-- **The sharp error is below `1/2`**: for `0 ≤ ε ≤ 1/2`, a range that contains the
manuscript's `0 < ε ≤ 1/2` (Corollary `hs:cor:unitary`),
`ε √(1 - ε²/4) < 1/2`. A one-line corollary of
`UnitaryImplementationExtensions.Search.near_factor_pos`, `0 < 1 - 2 ε √(1 - ε²/4)`. -/
theorem sharp_lt_half {ε : ℝ} (hε : 0 ≤ ε) (h : ε ≤ 1 / 2) :
    ε * Real.sqrt (1 - ε ^ 2 / 4) < 1 / 2 := by
  linarith [UnitaryImplementationExtensions.Search.near_factor_pos hε h]

/-- For an error `s ≤ 1/2` and `N ≥ 2`, `(N - 2)² ≤ 4 (N (1 - s) - 1)²`. -/
theorem sub_two_sq_le {N : ℕ} (hN : 2 ≤ N) {s : ℝ} (hs : s ≤ 1 / 2) :
    ((N : ℝ) - 2) ^ 2 ≤ 4 * ((N : ℝ) * (1 - s) - 1) ^ 2 := by
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : 0 ≤ (N : ℝ) - 2 := by linarith
  have h1 : (N : ℝ) - 2 ≤ 2 * ((N : ℝ) * (1 - s) - 1) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ N) (by linarith : (0 : ℝ) ≤ 1 - 2 * s)]
  calc ((N : ℝ) - 2) ^ 2 ≤ (2 * ((N : ℝ) * (1 - s) - 1)) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = 4 * ((N : ℝ) * (1 - s) - 1) ^ 2 := by ring

end
end MeasuredUnitaryLowerBound.OperatorNorm
