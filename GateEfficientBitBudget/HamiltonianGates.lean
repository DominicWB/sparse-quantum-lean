import GateEfficientBitBudget.Hamiltonian

/-!
# The gate counts of the binary constructions in the bit lengths

For equation `hs:eq:gate-binary` of Theorem `hs:thm:gates`: the released budgets
`GateBinary.binary_simulation_budget` and `GateBinary.binary_time_simulation_budget` bound the
gates of the binary constructions by
`200 (4608 q + 1) (G_C + (σ+1) + (k+1) + m + r + 1)`, with the per-call cost `G_C`, the time
word `m` (the `2^m` slots of the time-dependent construction, respectively the released
simulator word for the rescaled time `τ' ≤ √s q`) and the reuse word `r` with
`2^r ≤ 4 (4608 q + 1)`. This file bounds these counts in
`𝔟_H = bitH b_data (2^k) q ε = b_data + log₂(N+1) + log₂((q+1)/ε)`:

* `simM_word`: `2^m < 2 (2 + 4τ' + √(6τ'³/ε))` with `τ' ≤ √s q`, `s ≤ 2^k` gives
  `m ≤ 5 + 2k + 2 log₂((q+1)/ε)`; `simR_word`: `r ≤ 15 + log₂((q+1)/ε)`;
* `hs_gates_le` (time-independent): `G_C ≤ 1001832000 (𝔟_H + 1)³` and
  `0 ≤ 200 (4608 q + 1) (G_C + (σ+1) + (k+1) + m + r + 1) ≤ 10¹⁵ q (𝔟_H + 1)³`;
* `hs_gatesT_le` (time-dependent, `M = 2^m` slots): the same with `𝔟_H + log₂(M+1)` in the total
  count.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateBitBudget

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.OracleCircuit CayleyClockInterface
open SparseHamiltonian.GateCircuit.Sim (fDeg simM simR io)
open NativeSparseBlockEncoding (Data Query)

/-! ### The simulator words -/

/-- **The time word of the released simulator in the bit lengths**: for `1 ≤ s ≤ 2^k`,
`0 ≤ τ' ≤ √s q`, `q ≥ 0` and `0 < ε ≤ 1`, `2^m < 2 (2 + 4τ' + √(6τ'³/ε))` gives
`m ≤ 5 + 2k + 2 log₂((q+1)/ε)`. -/
theorem simM_word (m k : ℕ) {s τ' Q ε : ℝ} (hs1 : 1 ≤ s) (hsk : s ≤ 2 ^ k) (hτ0 : 0 ≤ τ')
    (hτ : τ' ≤ Real.sqrt s * Q) (hQ : 0 ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : ((2 ^ m : ℕ) : ℝ) < 2 * (2 + 4 * τ' + Real.sqrt (6 * τ' ^ 3 / ε))) :
    (m : ℝ) ≤ 5 + 2 * k + 2 * Real.logb 2 ((Q + 1) / ε) := by
  have hY1 : 1 ≤ (Q + 1) / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hQY : Q ≤ (Q + 1) / ε := by
    rw [le_div_iff₀ hε]
    nlinarith
  have hεY : 1 / ε ≤ (Q + 1) / ε := div_le_div_of_nonneg_right (by linarith) hε.le
  have hsq : Real.sqrt s ≤ 2 ^ k := (sqrt_le_self_of_one_le hs1).trans hsk
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hA1 : 1 ≤ (2 : ℝ) ^ k * ((Q + 1) / ε) := one_le_mul_of_one_le_of_one_le h2k hY1
  have hτA : τ' ≤ (2 : ℝ) ^ k * ((Q + 1) / ε) :=
    hτ.trans (mul_le_mul hsq hQY hQ (by positivity))
  have hεA : 1 / ε ≤ (2 : ℝ) ^ k * ((Q + 1) / ε) :=
    hεY.trans (le_mul_of_one_le_left (by linarith) h2k)
  have hin : 6 * τ' ^ 3 / ε ≤ (3 * ((2 : ℝ) ^ k * ((Q + 1) / ε)) ^ 2) ^ 2 := by
    have e : 6 * τ' ^ 3 / ε = 6 * τ' ^ 3 * (1 / ε) := by ring
    rw [e]
    have h1 : τ' ^ 3 ≤ ((2 : ℝ) ^ k * ((Q + 1) / ε)) ^ 3 := pow_le_pow_left₀ hτ0 hτA 3
    have h2 : 6 * τ' ^ 3 * (1 / ε) ≤ 6 * ((2 : ℝ) ^ k * ((Q + 1) / ε)) ^ 3 *
        ((2 : ℝ) ^ k * ((Q + 1) / ε)) :=
      mul_le_mul (by linarith) hεA (by positivity) (by positivity)
    have hA4 : 0 ≤ ((2 : ℝ) ^ k * ((Q + 1) / ε)) ^ 4 := by positivity
    have e2 : 6 * ((2 : ℝ) ^ k * ((Q + 1) / ε)) ^ 3 * ((2 : ℝ) ^ k * ((Q + 1) / ε)) =
        6 * ((2 : ℝ) ^ k * ((Q + 1) / ε)) ^ 4 := by ring
    have e3 : (3 * ((2 : ℝ) ^ k * ((Q + 1) / ε)) ^ 2) ^ 2 =
        9 * ((2 : ℝ) ^ k * ((Q + 1) / ε)) ^ 4 := by ring
    linarith
  have hsq2 : Real.sqrt (6 * τ' ^ 3 / ε) ≤ 3 * ((2 : ℝ) ^ k * ((Q + 1) / ε)) ^ 2 := by
    have := Real.sqrt_le_sqrt hin
    rwa [Real.sqrt_sq (by positivity)] at this
  have hAA : (2 : ℝ) ^ k * ((Q + 1) / ε) ≤ ((2 : ℝ) ^ k * ((Q + 1) / ε)) ^ 2 := by nlinarith
  have hA2 : 1 ≤ ((2 : ℝ) ^ k * ((Q + 1) / ε)) ^ 2 := by nlinarith
  have h2 : 2 * (2 + 4 * τ' + Real.sqrt (6 * τ' ^ 3 / ε)) ≤
      (2 : ℝ) ^ (5 + 2 * k) * ((Q + 1) / ε) ^ 2 := by
    have e : (2 : ℝ) ^ (5 + 2 * k) * ((Q + 1) / ε) ^ 2 =
        32 * ((2 : ℝ) ^ k * ((Q + 1) / ε)) ^ 2 := by ring
    rw [e]
    linarith
  have h3 := nat_le_mul_pow m ((2 : ℝ) ^ (5 + 2 * k)) ((Q + 1) / ε) (5 + 2 * k) 2 hY1 le_rfl
    (h.le.trans h2)
  push_cast at h3
  linarith

/-- **The reuse word of the released simulator in the bit lengths**: for `q ≥ 0` and
`0 < ε ≤ 1`, `2^r ≤ 4 (4608 q + 1)` gives `r ≤ 15 + log₂((q+1)/ε)`. -/
theorem simR_word (r : ℕ) {Q ε : ℝ} (hQ : 0 ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (h : ((2 ^ r : ℕ) : ℝ) ≤ 4 * (4608 * Q + 1)) :
    (r : ℝ) ≤ 15 + Real.logb 2 ((Q + 1) / ε) := by
  have hY1 : 1 ≤ (Q + 1) / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hQY : Q ≤ (Q + 1) / ε := by
    rw [le_div_iff₀ hε]
    nlinarith
  have h1 : 4 * (4608 * Q + 1) ≤ (2 : ℝ) ^ 15 * ((Q + 1) / ε) ^ 1 := by
    rw [pow_one]
    linarith
  have h2 := nat_le_mul_pow r (2 ^ 15) ((Q + 1) / ε) 15 1 hY1 le_rfl (h.trans h1)
  push_cast at h2
  linarith

/-! ### The gate counts in the bit lengths -/

/-- **The gate count of the binary construction in the bit lengths** (time-independent): for a
rescaling `γ` with `γ ≤ 1 ≤ γ √s`, `τ' ≤ √s q` and the released bounds
`2^m < 2 (2 + 4τ' + √(6τ'³/ε))`, `2^r ≤ 4 (4608 q + 1)` on the simulator words, `s = 2^σ`,
`σ ≤ k`, `b ≤ b_data`, `c₀ > 0` of bit length `b_data` and `ζ ≥ ε/(442368 q)`
(`q = √s τ + √(sτ log(1/ε)) + log(1/ε)`, `0 < ε ≤ 1/2`): the private operation has at most
`1001832000 (𝔟_H + 1)³` gates, and `0 ≤ 200 (4608 q + 1) (G_C + (σ+1) + (k+1) + m + r + 1) ≤
10¹⁵ q (𝔟_H + 1)³`, `𝔟_H = bitH b_data (2^k) q ε`. -/
theorem hs_gates_le (s k b σ bd : ℕ) {γ c0 τ ε ζ : ℝ} (hs : s = 2 ^ σ) (hσ : σ ≤ k)
    (hbd : b ≤ bd) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hγs : 1 ≤ γ * Real.sqrt s) (hτ : 0 ≤ τ)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hbits : HasBits bd c0) (hc0 : 0 < c0) (hζ : 0 < ζ)
    (hζlo : ε ≤ 442368 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) * ζ)
    (hτq : time (s : ℝ) τ γ ≤
      Real.sqrt s * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)))
    (hm : ((2 ^ simM (time (s : ℝ) τ γ) (ε / 2) : ℕ) : ℝ) <
      2 * (2 + 4 * time (s : ℝ) τ γ + Real.sqrt (6 * time (s : ℝ) τ γ ^ 3 / ε)))
    (hr : ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℕ) : ℝ) ≤
      4 * (4608 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1)) :
    (privGates (sparseOp k b (γ * Real.sqrt s * c0))
        (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) ≤ 1001832000 *
      (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ε + 1) ^ 3 ∧
    0 ≤ 200 * (4608 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1) *
        ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
            (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
          simM (time (s : ℝ) τ γ) (ε / 2) +
          simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) ∧
    200 * (4608 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1) *
        ((privGates (sparseOp k b (γ * Real.sqrt s * c0))
            (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) +
          simM (time (s : ℝ) τ γ) (ε / 2) +
          simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 1) ≤
      10 ^ 15 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) *
        (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ε + 1) ^ 3 := by
  have hε1 : ε ≤ 1 := by linarith
  have hs1' : (1 : ℝ) ≤ s := by
    rw [hs]
    exact_mod_cast Nat.one_le_two_pow
  have hsk : (s : ℝ) ≤ 2 ^ k := by
    rw [hs]
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) hσ
  -- the query shape
  have hℓ : 1 / 2 ≤ Real.log (1 / ε) := by
    have h1 : Real.log 2 ≤ Real.log (1 / ε) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith)
    have h2 := Real.log_two_gt_d9
    norm_num at h2
    linarith
  have hQ : 1 / 2 ≤ ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) :=
    hℓ.trans (le_shape _ _ _ hτ)
  have hQ0 : 0 ≤ ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) := by linarith
  -- the per-call cost
  have hu := cordicWords_le bd k b σ s hs hσ hγ1 hγs hbd hbits hc0 hζ hQ0 hε hε1 hζlo
  have hB0 := bitH_nonneg bd (2 ^ k) hQ0 hε hε1
  have hcube := cube_le (Nat.cast_nonneg _) hB0 hu
  have hpriv : (privGates (sparseOp k b (γ * Real.sqrt s * c0))
      (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) ≤
      57000 * ((cordicWords k b (γ * Real.sqrt s * c0) ζ : ℝ) + 1) ^ 3 := by
    exact_mod_cast privGates_binary k b (γ * Real.sqrt s * c0) ζ
  have hpriv' : (privGates (sparseOp k b (γ * Real.sqrt s * c0))
      (binArith k b (γ * Real.sqrt s * c0) ζ) : ℝ) ≤ 1001832000 *
        (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ε + 1) ^ 3 := by
    have e : ((25 : ℝ) + 1) ^ 3 = 17576 := by norm_num
    rw [e] at hcube
    linarith
  have hY : 0 ≤ (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ε +
      1) ^ 3 := by positivity
  refine ⟨hpriv', ?_⟩
  -- the simulator words
  have htime0 : 0 ≤ time (s : ℝ) τ γ := by
    unfold CayleyClockInterface.time
    positivity
  have hsM := simM_word _ k hs1' hsk htime0 hτq hQ0 hε hε1 hm
  have hsR := simR_word _ hQ0 hε hε1 hr
  have hσk : (σ : ℝ) ≤ k := by exact_mod_cast hσ
  have hkN := nat_le_logb k
  have hL0 : 0 ≤ Real.logb 2
      ((ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1) / ε) := by
    apply Real.logb_nonneg one_lt_two
    rw [le_div_iff₀ hε]
    linarith
  have hB : bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ε =
      bd + Real.logb 2 (((2 ^ k : ℕ) : ℝ) + 1) +
        Real.logb 2 ((ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1) / ε) := rfl
  have hB1 : bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ε + 1 ≤
      (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ε + 1) ^ 3 :=
    le_self_pow₀ (by linarith) (by norm_num)
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  refine ⟨mul_nonneg (by positivity) ?_, hs_final_arith hQ ?_ ?_ hY⟩
  · exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (Nat.cast_nonneg _)
      (by positivity)) (by positivity)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) zero_le_one
  · exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (Nat.cast_nonneg _)
      (by positivity)) (by positivity)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) zero_le_one
  · rw [hB] at hB1 hpriv' ⊢
    linarith

/-- **The gate count of the time-dependent binary construction in the bit lengths**: for a
rescaling `γ` with `γ ≤ 1 ≤ γ √s`, the released bound `2^r ≤ 4 (4608 q + 1)`, `s = 2^σ`,
`σ ≤ k`, `b ≤ b_data`, `c₀ > 0` of bit length `b_data` and `ζ ≥ ε/(442368 q)`
(`q = √s t + √(st log(2/ε)) + log(2/ε)`, `0 < ε ≤ 1`): the slot-selected private operation has at
most `1001832000 (𝔟_H + 1)³` gates, and
`0 ≤ 200 (4608 q + 1) (G_C + (σ+1) + (k+1) + m + r + 1) ≤ 10¹⁵ q (𝔟_H + log₂(M+1) + 1)³`,
`M = 2^m`. -/
theorem hs_gatesT_le (s k b m σ bd : ℕ) {γ c0 t ε ζ : ℝ} (hs : s = 2 ^ σ) (hσ : σ ≤ k)
    (hbd : b ≤ bd) (hγ1 : γ ≤ 1) (hγs : 1 ≤ γ * Real.sqrt s) (ht : 0 ≤ t) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hbits : HasBits bd c0) (hc0 : 0 < c0) (hζ : 0 < ζ)
    (hζlo : ε ≤ 442368 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) * ζ)
    (hr : ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℕ) : ℝ) ≤
      4 * (4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1)) :
    (privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
        (binArithT k b m (γ * Real.sqrt s * c0) ζ) : ℝ) ≤ 1001832000 *
      (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ε + 1) ^ 3 ∧
    0 ≤ 200 * (4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) *
        ((privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
            (binArithT k b m (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) + m +
          simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) ∧
    200 * (4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) *
        ((privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
            (binArithT k b m (γ * Real.sqrt s * c0) ζ) : ℝ) + (σ + 1) + (k + 1) + m +
          simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 1) ≤
      10 ^ 15 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) *
        (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ε +
          Real.logb 2 (((2 ^ m : ℕ) : ℝ) + 1) + 1) ^ 3 := by
  -- the query shape
  have hℓ : 1 / 2 ≤ Real.log (2 / ε) := ImprovedPrecisionBudget.targetLog_ge_half ε hε hε1
  have hQ : 1 / 2 ≤ ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) :=
    hℓ.trans (le_shape _ _ _ ht)
  have hQ0 : 0 ≤ ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) := by linarith
  -- the per-call cost
  have hu := cordicWords_le bd k b σ s hs hσ hγ1 hγs hbd hbits hc0 hζ hQ0 hε hε1 hζlo
  have hB0 := bitH_nonneg bd (2 ^ k) hQ0 hε hε1
  have hcube := cube_le (Nat.cast_nonneg _) hB0 hu
  have hpriv : (privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
      (binArithT k b m (γ * Real.sqrt s * c0) ζ) : ℝ) ≤
      57000 * ((cordicWords k b (γ * Real.sqrt s * c0) ζ : ℝ) + 1) ^ 3 := by
    exact_mod_cast privGates_binaryT k b m (γ * Real.sqrt s * c0) ζ
  have hpriv' : (privGates (sparseOpT k b m (γ * Real.sqrt s * c0))
      (binArithT k b m (γ * Real.sqrt s * c0) ζ) : ℝ) ≤ 1001832000 *
        (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ε + 1) ^ 3 := by
    have e : ((25 : ℝ) + 1) ^ 3 = 17576 := by norm_num
    rw [e] at hcube
    linarith
  refine ⟨hpriv', ?_⟩
  -- the remaining words
  have hsR := simR_word _ hQ0 hε hε1 hr
  have hσk : (σ : ℝ) ≤ k := by exact_mod_cast hσ
  have hkN := nat_le_logb k
  have hmM := nat_le_logb m
  have hM0 := logb_succ_nonneg (2 ^ m)
  have hL0 : 0 ≤ Real.logb 2
      ((ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) / ε) := by
    apply Real.logb_nonneg one_lt_two
    rw [le_div_iff₀ hε]
    linarith
  have hB : bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ε =
      bd + Real.logb 2 (((2 ^ k : ℕ) : ℝ) + 1) +
        Real.logb 2 ((ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1) / ε) := rfl
  have hBB : (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ε + 1) ^ 3 ≤
      (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ε +
        Real.logb 2 (((2 ^ m : ℕ) : ℝ) + 1) + 1) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have hB1 : bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ε +
      Real.logb 2 (((2 ^ m : ℕ) : ℝ) + 1) + 1 ≤
      (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ε +
        Real.logb 2 (((2 ^ m : ℕ) : ℝ) + 1) + 1) ^ 3 :=
    le_self_pow₀ (by linarith) (by norm_num)
  have hbd0 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  refine ⟨mul_nonneg (by positivity) ?_, hs_final_arith hQ ?_ ?_ (by positivity)⟩
  · exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (Nat.cast_nonneg _)
      (by positivity)) (by positivity)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) zero_le_one
  · exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (Nat.cast_nonneg _)
      (by positivity)) (by positivity)) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) zero_le_one
  · rw [hB] at hB1 hBB hpriv' ⊢
    linarith

end

end SparseHamiltonian.GateBitBudget
