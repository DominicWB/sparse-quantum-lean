import SparseLowerBounds.Hamiltonian.SpinChain

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Exact dyadic weights

Manuscript lines 2254-2279 (eqs. `hsl:eq:round`, `hsl:eq:roundevolution`).
Every positive public weight `a b_k` of a chain is rounded **down** to a dyadic
`b'_k = N_k/2^F` with `0 ≤ a b_k - b'_k ≤ 2^{-F} ≤ δ`, where (eq. `hsl:eq:round`)

  `δ = min{a/(2√n), A/(16τ)}`,  `A = sin(aτ/n)^n` (`chainAmp`),

and `a/(2√n) ≤ ½ min_k a b_k` because `b_k ≥ 1/√n`. The numerator is capped
at `2^F - 1` (`roundNum`), so every chain word is strictly inside the word
range of `Hamiltonian/DataBuilder`; the rounding error is still at most
`2^{-F}`.

* `chainNum_lt`: `N_k < 2^F`;
* `chainWeight_le`: `0 ≤ b'_k ≤ a b_k`, so the rounded path still has norm at
  most one (`norm_pathMatrix_le`);
* `chainWeight_pos`: all edges remain nonzero (line 2277);
* `norm_endAmp_chainWeight_sub_le`: Duhamel's inequality
  (`HamiltonianStability.evolution_error_le`) and row sums give
  `‖e^{-iτB} - e^{-iτB'}‖ ≤ 2τδ ≤ A/8` (eq. `hsl:eq:roundevolution`), applied to
  the endpoint matrix element.
-/

namespace SparseLowerBounds.Hamiltonian

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator

/-- The capped dyadic numerator `min ⌊x 2^F⌋ (2^F - 1)`. -/
def roundNum (F : ℕ) (x : ℝ) : ℕ := min ⌊x * 2 ^ F⌋₊ (2 ^ F - 1)

/-- The fractional bits `F = ⌈log₂ (1/δ)⌉`, so that `2^{-F} ≤ δ` for `δ > 0`. -/
def roundBits (δ : ℝ) : ℕ := ⌈Real.logb 2 δ⁻¹⌉₊

/-- The ideal endpoint amplitude `A = sin(aτ/n)^n` of the chain `a B_n`. -/
def chainAmp (n : ℕ) (a τ : ℝ) : ℝ := Real.sin (a * τ / n) ^ n

/-- The rounding precision `δ = min{a/(2√n), A/(16τ)}` (eq. `hsl:eq:round`). -/
def chainDelta (n : ℕ) (a τ : ℝ) : ℝ := min (a / (2 * Real.sqrt n)) (chainAmp n a τ / (16 * τ))

/-- The fractional bits of the rounded chain. -/
def chainBits (n : ℕ) (a τ : ℝ) : ℕ := roundBits (chainDelta n a τ)

/-- The integer numerator `N_k` of the rounded weight `b'_k = N_k/2^F` of `a b_k`. -/
def chainNum (n : ℕ) (a τ : ℝ) (k : ℕ) : ℕ := roundNum (chainBits n a τ) (a * spinWeight n k)

/-- The rounded dyadic weight `b'_k = N_k/2^F`. -/
def chainWeight (n : ℕ) (a τ : ℝ) (k : ℕ) : ℝ := (chainNum n a τ k : ℝ) / 2 ^ chainBits n a τ

/-! ### Dyadic rounding (eq. `hsl:eq:round`) -/

/-- The cap: `roundNum F x ≤ 2^F - 1`. -/
theorem roundNum_le (F : ℕ) (x : ℝ) : roundNum F x ≤ 2 ^ F - 1 := by
  exact min_le_right _ _

/-- Rounding down: `roundNum F x ≤ x 2^F` for `x ≥ 0`. -/
theorem roundNum_le_mul {x : ℝ} (hx : 0 ≤ x) (F : ℕ) : (roundNum F x : ℝ) ≤ x * 2 ^ F := by
  unfold roundNum
  calc ((min ⌊x * 2 ^ F⌋₊ (2 ^ F - 1) : ℕ) : ℝ) ≤ (⌊x * 2 ^ F⌋₊ : ℝ) := by
        exact_mod_cast min_le_left _ _
    _ ≤ x * 2 ^ F := Nat.floor_le (by positivity)

/-- The rounding error is at most `2^{-F}` on `[0, 1]` (at `x = 1` the cap
`2^F - 1` is attained and the error is exactly `2^{-F}`). -/
theorem sub_roundNum_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (F : ℕ) :
    x - (roundNum F x : ℝ) / 2 ^ F ≤ ((2 : ℝ) ^ F)⁻¹ := by
  have hpos : (0 : ℝ) < 2 ^ F := by positivity
  -- `hx0` is not needed: for `x < 0` the floor is `0` and the bound is trivial.
  have _ := hx0
  have key : x * 2 ^ F - (roundNum F x : ℝ) ≤ 1 := by
    unfold roundNum
    rcases le_or_gt ⌊x * 2 ^ F⌋₊ (2 ^ F - 1) with h | h
    · rw [min_eq_left h]
      have := Nat.lt_floor_add_one (x * 2 ^ F)
      linarith
    · rw [min_eq_right h.le]
      have h1 : (1 : ℕ) ≤ 2 ^ F := Nat.one_le_two_pow
      rw [Nat.cast_sub h1]
      push_cast
      have : x * 2 ^ F ≤ 2 ^ F := mul_le_of_le_one_left hpos.le hx1
      linarith
  have he : x - (roundNum F x : ℝ) / 2 ^ F = (x * 2 ^ F - (roundNum F x : ℝ)) / 2 ^ F := by
    field_simp
  rw [he, inv_eq_one_div]
  exact div_le_div_of_nonneg_right key hpos.le

/-- `2^{-⌈log₂(1/δ)⌉} ≤ δ` for `δ > 0` (for `δ ≥ 1` the exponent is `0`). -/
theorem two_pow_roundBits_inv_le {δ : ℝ} (hδ : 0 < δ) : ((2 : ℝ) ^ roundBits δ)⁻¹ ≤ δ := by
  have h1 : Real.logb 2 δ⁻¹ ≤ (roundBits δ : ℝ) := Nat.le_ceil _
  have h2 : (2 : ℝ) ^ Real.logb 2 δ⁻¹ ≤ (2 : ℝ) ^ (roundBits δ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two h1
  rw [Real.rpow_logb (by norm_num) (by norm_num) (inv_pos.mpr hδ), Real.rpow_natCast] at h2
  exact inv_le_of_inv_le₀ hδ h2

theorem chainDelta_le_left (n : ℕ) (a τ : ℝ) : chainDelta n a τ ≤ a / (2 * Real.sqrt n) :=
  min_le_left _ _

theorem chainDelta_le_amp (n : ℕ) (a τ : ℝ) : chainDelta n a τ ≤ chainAmp n a τ / (16 * τ) :=
  min_le_right _ _

variable {n : ℕ}

/-- The precision is positive when the ideal amplitude is. -/
theorem chainDelta_pos (hn : 1 ≤ n) {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hA : 0 < chainAmp n a τ) : 0 < chainDelta n a τ := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  exact lt_min (div_pos ha (by positivity)) (div_pos hA (by positivity))

/-- The numerator is strictly below `2^F`. -/
theorem chainNum_lt (n : ℕ) (a τ : ℝ) (k : ℕ) : chainNum n a τ k < 2 ^ chainBits n a τ := by
  exact (roundNum_le _ _).trans_lt (Nat.sub_lt (Nat.two_pow_pos _) one_pos)

/-- Rounding down: `0 ≤ b'_k ≤ a b_k` for `a ≥ 0`. -/
theorem chainWeight_le {a : ℝ} (ha : 0 ≤ a) (τ : ℝ) (k : ℕ) :
    0 ≤ chainWeight n a τ k ∧ chainWeight n a τ k ≤ a * spinWeight n k := by
  unfold chainWeight chainNum
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  exact roundNum_le_mul (mul_nonneg ha (spinWeight_nonneg n k)) _

/-- The rounded path has norm at most one for `0 ≤ a ≤ 1` (lines 2263-2270:
`0 ≤ b'_k ≤ a b_k ≤ b_k` and `norm_pathMatrix_le`). -/
theorem norm_pathMatrix_chainWeight_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (τ : ℝ) :
    ‖pathMatrix n (chainWeight n a τ)‖ ≤ 1 := by
  exact norm_pathMatrix_le (fun k => (chainWeight_le ha0 τ k).1)
    (fun k _ => (chainWeight_le ha0 τ k).2.trans
      (mul_le_of_le_one_left (spinWeight_nonneg n k) ha1))

/-- **Eq. `hsl:eq:round`**: `a b_k - b'_k ≤ δ` and `b'_k ≥ a b_k/2 > 0`, so all
edges remain nonzero (line 2277). -/
theorem chainWeight_pos (hn : 1 ≤ n) {a τ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hτ : 0 < τ)
    (hA : 0 < chainAmp n a τ) {k : ℕ} (hk : k < n) :
    a * spinWeight n k - chainWeight n a τ k ≤ chainDelta n a τ ∧ 0 < chainWeight n a τ k := by
  have h1 : a * spinWeight n k - chainWeight n a τ k ≤ chainDelta n a τ := by
    have hx0 : 0 ≤ a * spinWeight n k := mul_nonneg ha.le (spinWeight_nonneg n k)
    have hx1 : a * spinWeight n k ≤ 1 :=
      mul_le_one₀ ha1 (spinWeight_nonneg n k) (spinWeight_le_one n k)
    exact (sub_roundNum_le hx0 hx1 (chainBits n a τ)).trans
      (two_pow_roundBits_inv_le (chainDelta_pos hn ha hτ hA))
  refine ⟨h1, ?_⟩
  have h2 := chainDelta_le_left n a τ
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have h3 : a / (2 * Real.sqrt n) ≤ a / 2 * spinWeight n k := by
    have he : a / (2 * Real.sqrt n) = a / 2 * (Real.sqrt n)⁻¹ := by
      field_simp
    rw [he]
    exact mul_le_mul_of_nonneg_left (inv_sqrt_le_spinWeight hk) (by positivity)
  have h4 := mul_pos ha (spinWeight_pos hk)
  linarith

/-! ### Duhamel's inequality (eq. `hsl:eq:roundevolution`) -/

/-- Duhamel for matrices: `‖e^{-iτH} - e^{-iτG}‖ ≤ |τ| ‖H - G‖` for Hermitian
`H, G` (`HamiltonianStability.evolution_error_le` and `norm_matrixOperator`). -/
theorem norm_evolve_sub_le {S : Type*} [Fintype S] [DecidableEq S] {H G : Matrix S S ℂ}
    (hH : H.IsHermitian) (hG : G.IsHermitian) (τ : ℝ) :
    ‖evolve H τ - evolve G τ‖ ≤ |τ| * ‖H - G‖ := by
  unfold evolve
  have h := SparseHamiltonian.HamiltonianStability.evolution_error_le _ _ τ
    (star_matrixOperator_of_isHermitian hH) (star_matrixOperator_of_isHermitian hG)
  have he : SparseHamiltonian.SparseStateOverlap.matrixOperator H -
      SparseHamiltonian.SparseStateOverlap.matrixOperator G =
      SparseHamiltonian.SparseStateOverlap.matrixOperator (H - G) := by
    rw [matrixOperator_eq_toEuclideanCLM, matrixOperator_eq_toEuclideanCLM,
      matrixOperator_eq_toEuclideanCLM, map_sub]
  rw [he, norm_matrixOperator] at h
  exact h

/-- An endpoint matrix element moves by at most the operator distance of the
two evolutions (`‖|0⟩‖ = 1`). -/
theorem norm_endAmp_sub_le (n : ℕ) (c c' : ℕ → ℝ) (τ : ℝ) :
    ‖endAmp n c τ - endAmp n c' τ‖ ≤ ‖evolve (pathMatrix n c) τ - evolve (pathMatrix n c') τ‖ := by
  have he : endAmp n c τ - endAmp n c' τ =
      ((evolve (pathMatrix n c) τ - evolve (pathMatrix n c') τ)
        (EuclideanSpace.single 0 1)) (Fin.last n) := by
    rfl
  rw [he]
  refine (PiLp.norm_apply_le _ _).trans ((ContinuousLinearMap.le_opNorm _ _).trans_eq ?_)
  simp

/-- Row sums (line 2271) for the rounded chain: `‖a B_n - B'_n‖ ≤ 2δ`. -/
theorem norm_pathMatrix_sub_chainWeight_le (hn : 1 ≤ n) {a τ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hτ : 0 < τ) (hA : 0 < chainAmp n a τ) :
    ‖pathMatrix n (fun k => a * spinWeight n k) - pathMatrix n (chainWeight n a τ)‖ ≤
      2 * chainDelta n a τ := by
  refine norm_pathMatrix_sub_le (chainDelta_pos hn ha hτ hA).le (fun k hk => ?_)
  have hle := (chainWeight_le (n := n) ha.le τ k).2
  rw [abs_of_nonneg (by linarith)]
  exact (chainWeight_pos hn ha ha1 hτ hA hk).1

/-- **Eq. `hsl:eq:roundevolution`**: `‖e^{-iτ aB_n} - e^{-iτB'_n}‖ ≤ 2τδ ≤ A/8`. -/
theorem norm_evolve_sub_chainWeight_le (hn : 1 ≤ n) {a τ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hτ : 0 < τ) (hA : 0 < chainAmp n a τ) :
    ‖evolve (pathMatrix n fun k => a * spinWeight n k) τ - evolve (pathMatrix n (chainWeight n a τ)) τ‖ ≤
      chainAmp n a τ / 8 := by
  calc _ ≤ |τ| * ‖pathMatrix n (fun k => a * spinWeight n k) -
          pathMatrix n (chainWeight n a τ)‖ :=
        norm_evolve_sub_le (isHermitian_pathMatrix _ _) (isHermitian_pathMatrix _ _) τ
    _ ≤ τ * (2 * (chainAmp n a τ / (16 * τ))) := by
        rw [abs_of_pos hτ]
        refine mul_le_mul_of_nonneg_left ?_ hτ.le
        exact (norm_pathMatrix_sub_chainWeight_le hn ha ha1 hτ hA).trans
          (by linarith [chainDelta_le_amp n a τ])
    _ = chainAmp n a τ / 8 := by
        field_simp
        ring

/-- **Eq. `hsl:eq:roundevolution`** on the endpoint amplitude: the rounded
chain's amplitude is within `A/8` of the ideal `(-i)^n A`. -/
theorem norm_endAmp_chainWeight_sub_le (hn : 1 ≤ n) {a τ : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hτ : 0 < τ) (hA : 0 < chainAmp n a τ) :
    ‖endAmp n (chainWeight n a τ) τ - (-Complex.I) ^ n * (chainAmp n a τ : ℂ)‖ ≤
      chainAmp n a τ / 8 := by
  have h : endAmp n (fun k => a * spinWeight n k) τ =
      (-Complex.I) ^ n * (chainAmp n a τ : ℂ) :=
    endAmp_scaled hn a τ
  rw [← h, norm_sub_rev]
  exact (norm_endAmp_sub_le _ _ _ _).trans (norm_evolve_sub_chainWeight_le hn ha ha1 hτ hA)

end

end SparseLowerBounds.Hamiltonian
end
