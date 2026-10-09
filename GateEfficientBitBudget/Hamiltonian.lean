import GateEfficientBitBudget.Scale
import GateEfficientBinaryTime.Budget
import GateEfficientODEBudget.Words

/-!
# The per-call cost of the binary constructions in the bit lengths

Theorem `hs:thm:gates` of the accompanying paper concludes, for efficiently decoded binary or
fixed-point entries with bit lengths at most `b_data`, `q = √s τ + √(sτℓ) + ℓ` and private
arithmetic of polynomial cost, that `G_additional = q poly(b_data, log(N+1), log((q+1)/ε))`
(equation `hs:eq:gate-binary`). The released budgets bound the gates of the binary constructions
by `200 (4608 q + 1) (G_C + (σ+1) + (k+1) + m + r + 1)`, with the per-call cost
`G_C = 56 k + 2 |circ| + 2 bP + bT + 1` of the CORDIC arithmetic at the decoder scale
`κ = γ √s c₀`. This file bounds `G_C` in
`𝔟_H = bitH b_data (2^k) q ε = b_data + log₂(N+1) + log₂((q+1)/ε)` (`N = 2^k`), for stored bits
`b ≤ b_data`, a decoder scale `c₀` of bit length `b_data` (`HasBits`) and an arithmetic accuracy
`ζ ≥ ε/(442368 q)`:

* `cordicWords k b κ ζ = k + b + n + ⌈log₂ ⌈κ⌉⌉ + ⌈log₂ ⌈1/κ⌉⌉` (`n = nOf ζ` CORDIC steps);
  `cordic_words`: the per-call gates of the CORDIC arithmetic are at most
  `57000 (cordicWords + 1)³` (from the released counts `cordicArith_counts`, `params_fields` and
  `GateODEBudget.arith_poly`); `privGates_binary`, `privGates_binaryT`: the same for the private
  operations of the time-independent and the time-dependent constructions;
* `cordicWords_le`: `cordicWords ≤ 25 (𝔟_H + 1)` for `κ = γ √s c₀` with `γ ≤ 1 ≤ γ √s`;
* `hs_zeta_spec`: `ζ = ε/(442368 q)` is admissible (`0 < ζ ≤ 1`, the released budget
  `221184 q ζ ≤ ε` and the lower bound `ε ≤ 442368 q ζ`) for `q ≥ 1/2`;
  `hs_zeta_shape_spec`, `hs_zeta_shape_specT`: the same at the query shapes
  `q = √s τ + √(sτ log(1/ε)) + log(1/ε)` and `q = √s t + √(st log(2/ε)) + log(2/ε)` of the
  endpoints, which are at least `log 2 > 1/2`;
* `le_shape`, `hs_final_arith`: the arithmetic of the final bound.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBitBudget

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.OracleCircuit CayleyClockInterface
open SparseHamiltonian.GateCircuit.Sim (fDeg simM simR io)
open GateODEBudget (arith_poly wordOf_le)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-! ### The per-call cost of the CORDIC arithmetic -/

/-- **The words of the CORDIC arithmetic** of a binary private operation with `k` index bits, `b`
stored bits, decoder scale `κ` and accuracy `ζ`: `k + b + n + ⌈log₂ ⌈κ⌉⌉ + ⌈log₂ ⌈1/κ⌉⌉`, with
`n = nOf ζ` CORDIC steps per stage. -/
def cordicWords (k b : ℕ) (κ ζ : ℝ) : ℕ :=
  k + b + Cordic.nOf ζ + Nat.clog 2 ⌈κ⌉₊ + Nat.clog 2 ⌈1 / κ⌉₊

/-- **The per-call gates of the CORDIC arithmetic as a polynomial in its words**:
`2 (28 k) + 2 |circ| + 2 bP + bT + 1 ≤ 57000 (cordicWords + 1)³`, from the released counts. -/
theorem cordic_words {B : Type*} (k b : ℕ) (xw yw : Fin b → B) (κ ζ : ℝ) :
    2 * (28 * k) + 2 * (cordicArith b xw yw κ ζ).circ.length +
        (2 * (cordicArith b xw yw κ ζ).bP + (cordicArith b xw yw κ ζ).bT + 1) ≤
      57000 * (cordicWords k b κ ζ + 1) ^ 3 := by
  obtain ⟨hc, -, hT, hP⟩ := cordicArith_counts b xw yw κ ζ
  obtain ⟨hn, hbT, hbP, hw⟩ := params_fields b κ ζ
  have hu : cordicWords k b κ ζ = k + b + Cordic.nOf ζ + Nat.clog 2 ⌈κ⌉₊ +
      Nat.clog 2 ⌈1 / κ⌉₊ := rfl
  have hW := wordOf_le (Cordic.nOf ζ)
  have hg2 : Cordic.g2Of (Cordic.nOf ζ) κ = Nat.clog 2 ⌈κ⌉₊ + Cordic.nOf ζ + 5 := by
    unfold Cordic.g2Of
    rfl
  have hlk : Cordic.lkOf κ = Nat.clog 2 ⌈1 / κ⌉₊ := by
    unfold Cordic.lkOf
    rfl
  have hnu : Cordic.nOf ζ ≤ cordicWords k b κ ζ := by
    rw [hu]
    omega
  have hNN : Cordic.nOf ζ * Cordic.nOf ζ ≤ cordicWords k b κ ζ * cordicWords k b κ ζ :=
    Nat.mul_le_mul hnu hnu
  have hWc : (Cordic.params b κ ζ).w ≤
      37 * ((cordicWords k b κ ζ + 1) * (cordicWords k b κ ζ + 1)) := by
    rw [hw, hg2, hlk]
    have e : (cordicWords k b κ ζ + 1) * (cordicWords k b κ ζ + 1) =
        cordicWords k b κ ζ * cordicWords k b κ ζ + 2 * cordicWords k b κ ζ + 1 := by ring
    rw [e]
    have h1 : Nat.clog 2 ⌈κ⌉₊ + Nat.clog 2 ⌈1 / κ⌉₊ + b ≤ cordicWords k b κ ζ := by
      rw [hu]
      omega
    omega
  obtain ⟨h1, -⟩ := arith_poly 0 0 (Cordic.params b κ ζ).w (Cordic.params b κ ζ).n
    (Cordic.wordOf (Cordic.nOf ζ)) (cordicWords k b κ ζ) (by omega) (by omega) hWc
    (by rw [hn]; exact hnu) (by omega)
  rw [hbP, hbT] at hc
  have hlen : (cordicArith b xw yw κ ζ).circ.length ≤ 28355 * (cordicWords k b κ ζ + 1) ^ 3 := by
    omega
  have hk : k ≤ cordicWords k b κ ζ := by
    rw [hu]
    omega
  have hp1 : cordicWords k b κ ζ + 1 ≤ (cordicWords k b κ ζ + 1) ^ 3 :=
    le_self_pow₀ (by omega) (by norm_num)
  omega

/-- **The per-call cost of the binary private operation** (time-independent):
`G_C = privGates ≤ 57000 (cordicWords + 1)³`. -/
theorem privGates_binary (k b : ℕ) (κ ζ : ℝ) :
    privGates (sparseOp k b κ) (binArith k b κ ζ) ≤ 57000 * (cordicWords k b κ ζ + 1) ^ 3 := by
  have e : privGates (sparseOp k b κ) (binArith k b κ ζ) = 2 * (28 * k) +
      2 * (binArith k b κ ζ).circ.length +
        (2 * (binArith k b κ ζ).bP + (binArith k b κ ζ).bT + 1) := by
    rw [privGates, show (sparseOp k b κ).V = computeV k b from rfl, computeV_nGates]
  rw [e]
  exact cordic_words k b (valX k b) (valY k b) κ ζ

/-- **The per-call cost of the slot-selected binary private operation** (time-dependent):
`G_C = privGates ≤ 57000 (cordicWords + 1)³`. -/
theorem privGates_binaryT (k b m : ℕ) (κ ζ : ℝ) :
    privGates (sparseOpT k b m κ) (binArithT k b m κ ζ) ≤
      57000 * (cordicWords k b κ ζ + 1) ^ 3 := by
  have e : privGates (sparseOpT k b m κ) (binArithT k b m κ ζ) = 2 * (28 * k) +
      2 * (binArithT k b m κ ζ).circ.length +
        (2 * (binArithT k b m κ ζ).bP + (binArithT k b m κ ζ).bT + 1) := by
    rw [privGates, show (sparseOpT k b m κ).V = computeVT k b m from rfl, computeVT_nGates]
  rw [e]
  exact cordic_words k b (valXT k b m) (valYT k b m) κ ζ

/-! ### The words in the bit lengths -/

/-- **The arithmetic accuracy of `hs:eq:gate-binary`**: for `0 < ε ≤ 1` and `q ≥ 1/2`, the choice
`ζ = ε/(442368 q)` has `0 < ζ ≤ 1`, the released budget `221184 q ζ ≤ ε` and the lower bound
`ε ≤ 442368 q ζ` of `binary_simulation_bits`. -/
theorem hs_zeta_spec {ε Q : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hQ : 1 / 2 ≤ Q) :
    0 < ε / (442368 * Q) ∧ ε / (442368 * Q) ≤ 1 ∧ 221184 * Q * (ε / (442368 * Q)) ≤ ε ∧
      ε ≤ 442368 * Q * (ε / (442368 * Q)) := by
  have hQ0 : 0 < Q := by linarith
  have e : 442368 * Q * (ε / (442368 * Q)) = ε := by
    field_simp
  refine ⟨by positivity, ?_, ?_, le_of_eq e.symm⟩
  · rw [div_le_one (by positivity)]
    linarith
  · have e2 : 221184 * Q * (ε / (442368 * Q)) = ε / 2 := by
      field_simp
      ring
    rw [e2]
    linarith

/-- The query shape is at least its logarithm: `ℓ ≤ √s τ + √(s τ ℓ) + ℓ` for `τ ≥ 0`. -/
theorem le_shape (s τ ℓ : ℝ) (hτ : 0 ≤ τ) : ℓ ≤ ImprovedPrecisionBudget.shape s τ ℓ := by
  unfold ImprovedPrecisionBudget.shape
  have h1 := mul_nonneg (Real.sqrt_nonneg s) hτ
  have h2 := Real.sqrt_nonneg (s * τ * ℓ)
  linarith

/-- **The arithmetic accuracy of `hs:eq:gate-binary` at the query shape of the endpoints**: for
`τ ≥ 0`, `0 < ε ≤ 1/2` and `q = √s τ + √(s τ log(1/ε)) + log(1/ε)`, `ζ = ε/(442368 q)` meets the
accuracy hypotheses `0 < ζ ≤ 1`, `221184 q ζ ≤ ε` and `ε ≤ 442368 q ζ` of
`binary_simulation_bits` and `binary_simulation_budget_synth_bits` (`q ≥ log 2 > 1/2`). -/
theorem hs_zeta_shape_spec (s : ℕ) {τ ε : ℝ} (hτ : 0 ≤ τ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    0 < ε / (442368 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ∧
    ε / (442368 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ≤ 1 ∧
    221184 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) *
      (ε / (442368 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)))) ≤ ε ∧
    ε ≤ 442368 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) *
      (ε / (442368 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)))) := by
  apply hs_zeta_spec hε (by linarith)
  have h1 : Real.log 2 ≤ Real.log (1 / ε) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith)
  have h2 := Real.log_two_gt_d9
  norm_num at h2
  exact le_trans (by linarith) (le_shape _ _ _ hτ)

/-- **The same for the time-dependent endpoints**: for `t ≥ 0`, `0 < ε ≤ 1` and
`q = √s t + √(s t log(2/ε)) + log(2/ε)`, `ζ = ε/(442368 q)` meets the accuracy hypotheses of
`binary_time_simulation_bits` and `binary_time_simulation_budget_synth_bits`
(`q ≥ log(2/ε) ≥ 1/2`, `ImprovedPrecisionBudget.targetLog_ge_half`). -/
theorem hs_zeta_shape_specT (s : ℕ) {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < ε / (442368 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ∧
    ε / (442368 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ≤ 1 ∧
    221184 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) *
      (ε / (442368 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)))) ≤ ε ∧
    ε ≤ 442368 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) *
      (ε / (442368 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)))) :=
  hs_zeta_spec hε hε1
    ((ImprovedPrecisionBudget.targetLog_ge_half ε hε hε1).trans (le_shape _ _ _ ht))

/-- **The words of the CORDIC arithmetic in the bit lengths**: for `κ = γ √s c₀` with
`s = 2^σ`, `σ ≤ k`, `γ ≤ 1 ≤ γ √s`, stored bits `b ≤ b_data`, `c₀ > 0` of bit length `b_data` and
an accuracy `ζ ≥ ε/(442368 q)` (`q ≥ 0`, `0 < ε ≤ 1`),
`cordicWords k b κ ζ ≤ 25 (b_data + log₂(N+1) + log₂((q+1)/ε) + 1)`, `N = 2^k`. -/
theorem cordicWords_le (bd k b σ s : ℕ) {γ c0 ζ Q ε : ℝ} (hs : s = 2 ^ σ) (hσ : σ ≤ k)
    (hγ1 : γ ≤ 1) (hγs : 1 ≤ γ * Real.sqrt s) (hb : b ≤ bd) (hc0 : HasBits bd c0)
    (hc0p : 0 < c0) (hζ : 0 < ζ) (hQ : 0 ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hζlo : ε ≤ 442368 * Q * ζ) :
    (cordicWords k b (γ * Real.sqrt s * c0) ζ : ℝ) ≤ 25 * (bitH bd (2 ^ k) Q ε + 1) := by
  have hs1 : (1 : ℝ) ≤ s := by
    rw [hs]
    exact_mod_cast Nat.one_le_two_pow
  have hsk : (s : ℝ) ≤ 2 ^ k := by
    rw [hs]
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) hσ
  set Y := (Q + 1) / ε with hYdef
  have hY1 : 1 ≤ Y := by
    rw [hYdef, le_div_iff₀ hε]
    linarith
  have hQY : Q / ε ≤ Y := div_le_div_of_nonneg_right (by linarith) hε.le
  -- the decoder scale
  have hsq : Real.sqrt (s : ℝ) ≤ s := sqrt_le_self_of_one_le hs1
  have hc0' : c0 ≤ 2 ^ bd := hc0.lt.le
  have hκ : γ * Real.sqrt s * c0 ≤ 2 ^ (k + bd) := by
    have hγ0 : 0 ≤ γ * Real.sqrt s := by linarith
    have hγs' : γ * Real.sqrt s ≤ s := by
      have := mul_le_mul_of_nonneg_right hγ1 (Real.sqrt_nonneg (s : ℝ))
      linarith
    calc γ * Real.sqrt s * c0 ≤ (2 : ℝ) ^ k * 2 ^ bd :=
          mul_le_mul (hγs'.trans hsk) hc0' hc0p.le (by positivity)
      _ = 2 ^ (k + bd) := by ring
  have hκi : 1 / (γ * Real.sqrt s * c0) ≤ 2 ^ bd := by
    rw [div_le_iff₀ (by nlinarith)]
    have h1 := hc0.one_le_mul hc0p
    have h2 : c0 ≤ γ * Real.sqrt s * c0 := le_mul_of_one_le_left hc0p.le hγs
    have h3 : (2 : ℝ) ^ bd * c0 ≤ 2 ^ bd * (γ * Real.sqrt s * c0) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have wκ : (Nat.clog 2 ⌈γ * Real.sqrt s * c0⌉₊ : ℝ) ≤ k + bd := by
    have := clog_ceil_le_nat _ _ hκ
    exact_mod_cast this
  have wκi : (Nat.clog 2 ⌈1 / (γ * Real.sqrt s * c0)⌉₊ : ℝ) ≤ bd := by
    have := clog_ceil_le_nat _ _ hκi
    exact_mod_cast this
  -- the CORDIC steps
  have hz : 8 / ζ ≤ 2 ^ 22 * Y ^ 1 := by
    have h1 : ε / ζ ≤ 442368 * Q := by
      rw [div_le_iff₀ hζ]
      linarith
    have e : 8 / ζ = 8 * (ε / ζ) * (1 / ε) := by
      field_simp
    rw [e, pow_one]
    have h2 : 8 * (ε / ζ) * (1 / ε) ≤ 8 * (442368 * Q) * (1 / ε) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e2 : 8 * (442368 * Q) * (1 / ε) = 3538944 * (Q / ε) := by ring
    linarith
  have wn : (Cordic.nOf ζ : ℝ) ≤ 25 + Real.logb 2 Y := by
    have h := clog_le_mul_pow (8 / ζ) (2 ^ 22) Y 22 1 hY1 le_rfl hz
    unfold Cordic.nOf
    push_cast at h ⊢
    linarith
  have wk := nat_le_logb k
  have wb : (b : ℝ) ≤ bd := by exact_mod_cast hb
  have hL0 := Real.logb_nonneg one_lt_two hY1
  have hN0 := logb_succ_nonneg (2 ^ k)
  have hw : (cordicWords k b (γ * Real.sqrt s * c0) ζ : ℝ) = k + b + (Cordic.nOf ζ : ℝ) +
      (Nat.clog 2 ⌈γ * Real.sqrt s * c0⌉₊ : ℝ) +
      (Nat.clog 2 ⌈1 / (γ * Real.sqrt s * c0)⌉₊ : ℝ) := by
    unfold cordicWords
    push_cast
    ring
  have hB : bitH bd (2 ^ k) Q ε = bd + Real.logb 2 (((2 ^ k : ℕ) : ℝ) + 1) + Real.logb 2 Y := rfl
  rw [hw, hB]
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  linarith

/-! ### The final arithmetic -/

/-- The arithmetic of the final bound: `200 (4608 q + 1) T ≤ 10¹⁵ q B` for `q ≥ 1/2`,
`0 ≤ T ≤ 1001832023 B`. -/
theorem hs_final_arith {Q T Bc : ℝ} (hQ : 1 / 2 ≤ Q) (hT0 : 0 ≤ T) (hT : T ≤ 1001832023 * Bc)
    (hBc : 0 ≤ Bc) : 200 * (4608 * Q + 1) * T ≤ 10 ^ 15 * Q * Bc := by
  have hQ0 : 0 ≤ Q := by linarith
  have h1 : 200 * (4608 * Q + 1) * T ≤ 200 * (4610 * Q) * T :=
    mul_le_mul_of_nonneg_right (by linarith) hT0
  have h2 : 200 * (4610 * Q) * T ≤ 200 * (4610 * Q) * (1001832023 * Bc) :=
    mul_le_mul_of_nonneg_left hT (by positivity)
  have h3 : 0 ≤ Q * Bc := mul_nonneg hQ0 hBc
  nlinarith

end

end SparseHamiltonian.GateBitBudget
