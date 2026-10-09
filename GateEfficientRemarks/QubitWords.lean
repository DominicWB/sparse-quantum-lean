import GateEfficientBitBudget.HamiltonianGates

/-!
# The registers of the binary constructions in the bit lengths

Theorem `hs:thm:gates` of the accompanying paper (equation `hs:eq:gate-total`) counts
`O(A_C(ξ) + a + m + r)` auxiliary qubits, where `A_C` counts the clean work qubits of the
private operation (entry decoding and rotation arithmetic). The released binary-data theorems
state the register sizes exactly:

* `GateBinary.binary_simulation`: `binarySim` has
  `k + (2(k+1) + 3m + 6r + 3) + (6k + 2b + bT + bP + A + 3)` qubits, with the `k` system qubits,
  the simulator wires (`a = k + 1`), the private scratch `6k + 2b` and the CORDIC fields `bT`,
  `bP`, `A` of `binArith`;
* `GateBinary.binary_time_simulation`: the same for `binaryTimeSim` with `m` slot qubits.

By `GateBinary.cordicArith_counts` and `GateBinary.params_fields`, `A = 1 + 2w + (6(n+1)+1) w`
and `bT = bP = wordOf n` for `n` CORDIC steps and the register width `w = 2n² + …`, so `A` is
cubic in the words of the arithmetic. This file bounds the registers in the bit-length
parameter `𝔟_H = bitH b_data (2^k) q ε = b_data + log₂(N+1) + log₂((q+1)/ε)` of the library
`GateEfficientBitBudget`:

* `card_binary_register`, `card_binary_registerT`: the register formulas hold for all
  parameters (from `GateNative.card_HW`, `GateCircuit.Sim.card_simWire`,
  `GateCircuit.Sim.card_wire`, `GateBinary.card_SZ`);
* `cordic_register_le`: `9k + 2b + bT + bP + A ≤ 13 u + 11 + 207 (u+1)³` for
  `u = cordicWords k b κ ζ`;
* `binary_register_le`: the register of `binarySim` has at most `4·10⁶ (𝔟_H + 1)³` qubits, under
  the hypotheses of the released gate bound `GateBitBudget.hs_gates_le`;
* `binary_registerT_le`: the register of `binaryTimeSim` on `M = 2^m` time slots has at most
  `4·10⁶ (𝔟_H + log₂(M+1) + 1)³` qubits, under those of `GateBitBudget.hs_gatesT_le`;
* `cordic_A_ge`, `nOf_ge`, `binArith_A_ge`: the converse, the CORDIC workspace has at least
  `12 n³` wires for `n ≥ log₂(8/ζ) + 2` steps, hence at least `12 (log₂(1/ε))³` in the accuracy
  window of the endpoints, so the cubic degree cannot be lowered for these circuits.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateRemarks

noncomputable section
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative SparseHamiltonian.GateBinary
open SparseHamiltonian.GateBitBudget CayleyClockInterface
open SparseHamiltonian.GateCircuit.Sim (fDeg simM simR SimWire Wire card_simWire card_wire)

/-! ### The register formulas -/

/-- **The register of `binarySim`** (`hs:eq:gate-total`, time-independent): the wires
`HW (SimWire (k+1) Q τ q̄ ε) (Fin k) Empty (SZ k b) bT bP A` number
`k + (2(k+1) + 3m + 6r + 3) + (6k + 2b + bT + bP + A + 3)` with `m = simM τ ε` and
`r = simR Q τ q̄ ε`, for all parameters; this is the formula stated by
`GateBinary.binary_simulation`. -/
theorem card_binary_register (k b bT bP A : ℕ) (Q τ qbar ε : ℝ) :
    Fintype.card (HW (SimWire (k + 1) Q τ qbar ε) (Fin k) Empty (SZ k b) bT bP A) =
      k + (2 * (k + 1) + 3 * simM τ ε + 6 * simR Q τ qbar ε + 3) +
        (6 * k + 2 * b + bT + bP + A + 3) := by
  rw [card_HW, card_simWire, card_SZ, Fintype.card_fin]
  simp only [Fintype.card_empty, add_zero]
  ring

/-- **The register of `binaryTimeSim`** (`hs:eq:gate-total`, time-dependent part): the wires
`HW (Wire (k+1) m r (k+1+m+2r)) (Fin k) Empty (SZ k b) bT bP A` number
`k + (2(k+1) + 3m + 6r + 3) + (6k + 2b + bT + bP + A + 3)`, for all parameters; this is the
formula stated by `GateBinary.binary_time_simulation`. -/
theorem card_binary_registerT (k b m r bT bP A : ℕ) :
    Fintype.card (HW (Wire (k + 1) m r (k + 1 + m + 2 * r)) (Fin k) Empty (SZ k b) bT bP A) =
      k + (2 * (k + 1) + 3 * m + 6 * r + 3) + (6 * k + 2 * b + bT + bP + A + 3) := by
  rw [card_HW, card_wire, card_SZ, Fintype.card_fin]
  simp only [Fintype.card_empty, add_zero]
  ring

/-! ### The registers in the bit lengths -/

/-- **The CORDIC registers in the words** (`hs:eq:gate-total`): for the CORDIC arithmetic of a
binary private operation with `k` index bits, `b` stored bits, decoder scale `κ` and accuracy
`ζ`, `9k + 2b + bT + bP + A ≤ 13 u + 11 + 207 (u+1)³`, `u = cordicWords k b κ ζ`
(`A = 1 + 2w + (6(n+1)+1) w`, `w ≤ 23 (u+1)²`, `bT = bP ≤ 2n + 5`, `n ≤ u`). -/
theorem cordic_register_le {B : Type*} (k b : ℕ) (xw yw : Fin b → B) (κ ζ : ℝ) :
    9 * k + 2 * b + (cordicArith b xw yw κ ζ).bT + (cordicArith b xw yw κ ζ).bP +
        (cordicArith b xw yw κ ζ).A ≤
      13 * cordicWords k b κ ζ + 11 + 207 * (cordicWords k b κ ζ + 1) ^ 3 := by
  obtain ⟨-, hA, hT, hP⟩ := cordicArith_counts b xw yw κ ζ
  obtain ⟨hn, hbT, hbP, hw⟩ := params_fields b κ ζ
  have hW := GateODEBudget.wordOf_le (Cordic.nOf ζ)
  have hg2 : Cordic.g2Of (Cordic.nOf ζ) κ = Nat.clog 2 ⌈κ⌉₊ + Cordic.nOf ζ + 5 := by
    unfold Cordic.g2Of
    rfl
  have hlk : Cordic.lkOf κ = Nat.clog 2 ⌈1 / κ⌉₊ := by
    unfold Cordic.lkOf
    rfl
  have hu : cordicWords k b κ ζ = k + b + Cordic.nOf ζ + Nat.clog 2 ⌈κ⌉₊ +
      Nat.clog 2 ⌈1 / κ⌉₊ := rfl
  rw [hA, hT, hP, hbT, hbP, hn]
  have hnu : Cordic.nOf ζ ≤ cordicWords k b κ ζ := by
    rw [hu]
    omega
  have hNN : Cordic.nOf ζ * Cordic.nOf ζ ≤ cordicWords k b κ ζ * cordicWords k b κ ζ :=
    Nat.mul_le_mul hnu hnu
  have hw' : (Cordic.params b κ ζ).w ≤
      23 * ((cordicWords k b κ ζ + 1) * (cordicWords k b κ ζ + 1)) := by
    rw [hw, hg2, hlk]
    have e : (cordicWords k b κ ζ + 1) * (cordicWords k b κ ζ + 1) =
        cordicWords k b κ ζ * cordicWords k b κ ζ + 2 * cordicWords k b κ ζ + 1 := by ring
    rw [e]
    have h1 : Nat.clog 2 ⌈κ⌉₊ + Nat.clog 2 ⌈1 / κ⌉₊ + b ≤ cordicWords k b κ ζ := by
      rw [hu]
      omega
    omega
  have h1 : (6 * (Cordic.nOf ζ + 1) + 1) * (Cordic.params b κ ζ).w ≤
      7 * (cordicWords k b κ ζ + 1) *
        (23 * ((cordicWords k b κ ζ + 1) * (cordicWords k b κ ζ + 1))) :=
    Nat.mul_le_mul (by omega) hw'
  have e3 : 7 * (cordicWords k b κ ζ + 1) *
      (23 * ((cordicWords k b κ ζ + 1) * (cordicWords k b κ ζ + 1))) =
      161 * (cordicWords k b κ ζ + 1) ^ 3 := by ring
  have hp2 : (cordicWords k b κ ζ + 1) * (cordicWords k b κ ζ + 1) ≤
      (cordicWords k b κ ζ + 1) ^ 3 := by
    have e : (cordicWords k b κ ζ + 1) ^ 3 =
        (cordicWords k b κ ζ + 1) * (cordicWords k b κ ζ + 1) * (cordicWords k b κ ζ + 1) := by
      ring
    rw [e]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hkb : k + b ≤ cordicWords k b κ ζ := by
    rw [hu]
    omega
  omega

/-- The query shape of the time-independent endpoints is at least `1/2`
(`hs:eq:gate-binary`). -/
theorem half_le_shape (s : ℕ) {τ ε : ℝ} (hτ : 0 ≤ τ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    1 / 2 ≤ ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) := by
  have h1 : Real.log 2 ≤ Real.log (1 / ε) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith)
  have h2 := Real.log_two_gt_d9
  norm_num at h2
  exact le_trans (by linarith) (le_shape _ _ _ hτ)

/-- **The register of the binary construction in the bit lengths** (`hs:eq:gate-total`,
time-independent): under the hypotheses of `GateBitBudget.hs_gates_le` (a rescaling with
`γ ≤ 1 ≤ γ √s`, `τ' ≤ √s q` and the bounds on `2^m`, `2^r` that the released budget states for
its rescaling;
`s = 2^σ`, `σ ≤ k`, `b ≤ b_data`, `c₀ > 0` of bit length `b_data`, `ζ ≥ ε/(442368 q)`), the
register of `binarySim`, `k + (2(k+1) + 3m + 6r + 3) + (6k + 2b + bT + bP + A + 3)` qubits, has
at most `4·10⁶ (𝔟_H + 1)³` qubits, `𝔟_H = bitH b_data (2^k) q ε`. -/
theorem binary_register_le (s k b σ bd : ℕ) {γ c0 τ ε ζ : ℝ} (hs : s = 2 ^ σ) (hσ : σ ≤ k)
    (hbd : b ≤ bd) (hγ1 : γ ≤ 1) (hγs : 1 ≤ γ * Real.sqrt s) (hτ : 0 ≤ τ)
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hbits : HasBits bd c0) (hc0 : 0 < c0) (hζ : 0 < ζ)
    (hζlo : ε ≤ 442368 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) * ζ)
    (hτq : time (s : ℝ) τ γ ≤
      Real.sqrt s * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)))
    (hm : ((2 ^ simM (time (s : ℝ) τ γ) (ε / 2) : ℕ) : ℝ) <
      2 * (2 + 4 * time (s : ℝ) τ γ + Real.sqrt (6 * time (s : ℝ) τ γ ^ 3 / ε)))
    (hr : ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℕ) : ℝ) ≤
      4 * (4608 * ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) + 1)) :
    ((k + (2 * (k + 1) + 3 * simM (time (s : ℝ) τ γ) (ε / 2) +
        6 * simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 3) +
      (6 * k + 2 * b + (binArith k b (γ * Real.sqrt s * c0) ζ).bT +
        (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
        (binArith k b (γ * Real.sqrt s * c0) ζ).A + 3) : ℕ) : ℝ) ≤
      4 * 10 ^ 6 *
        (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε))) ε + 1) ^ 3 := by
  have hε1 : ε ≤ 1 := by linarith
  have hs1' : (1 : ℝ) ≤ s := by
    rw [hs]
    exact_mod_cast Nat.one_le_two_pow
  have hsk : (s : ℝ) ≤ 2 ^ k := by
    rw [hs]
    exact_mod_cast Nat.pow_le_pow_right (by norm_num) hσ
  have hQ := half_le_shape s hτ hε hε2
  have hQ0 : 0 ≤ ImprovedPrecisionBudget.shape s τ (Real.log (1 / ε)) := by linarith
  have hu := cordicWords_le bd k b σ s hs hσ hγ1 hγs hbd hbits hc0 hζ hQ0 hε hε1 hζlo
  have hB0 := bitH_nonneg bd (2 ^ k) hQ0 hε hε1
  have hcube := cube_le (Nat.cast_nonneg _) hB0 hu
  have e26 : ((25 : ℝ) + 1) ^ 3 = 17576 := by norm_num
  rw [e26] at hcube
  have hreg := cordic_register_le k b (valX k b) (valY k b) (γ * Real.sqrt s * c0) ζ
  have hreg' : ((9 * k + 2 * b + (binArith k b (γ * Real.sqrt s * c0) ζ).bT +
      (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
      (binArith k b (γ * Real.sqrt s * c0) ζ).A : ℕ) : ℝ) ≤
      13 * (cordicWords k b (γ * Real.sqrt s * c0) ζ : ℝ) + 11 +
        207 * ((cordicWords k b (γ * Real.sqrt s * c0) ζ : ℝ) + 1) ^ 3 := by
    exact_mod_cast hreg
  have htime0 : 0 ≤ time (s : ℝ) τ γ := by
    unfold CayleyClockInterface.time
    have hγ0 : 0 < γ := by
      by_contra hneg
      have : γ * Real.sqrt s ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hneg) (Real.sqrt_nonneg _)
      linarith
    positivity
  have hsM := simM_word _ k hs1' hsk htime0 hτq hQ0 hε hε1 hm
  have hsR := simR_word _ hQ0 hε hε1 hr
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
  have hcast : ((k + (2 * (k + 1) + 3 * simM (time (s : ℝ) τ γ) (ε / 2) +
        6 * simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) + 3) +
      (6 * k + 2 * b + (binArith k b (γ * Real.sqrt s * c0) ζ).bT +
        (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
        (binArith k b (γ * Real.sqrt s * c0) ζ).A + 3) : ℕ) : ℝ) =
      ((9 * k + 2 * b + (binArith k b (γ * Real.sqrt s * c0) ζ).bT +
        (binArith k b (γ * Real.sqrt s * c0) ζ).bP +
        (binArith k b (γ * Real.sqrt s * c0) ζ).A : ℕ) : ℝ) +
        3 * (simM (time (s : ℝ) τ γ) (ε / 2) : ℝ) +
        6 * (simR (width (s : ℝ) γ) (time (s : ℝ) τ γ) (moment γ) (ε / 2) : ℝ) + 8 := by
    push_cast
    ring
  rw [hcast]
  rw [hB] at hB1 hcube hu ⊢
  have hu0 : (0 : ℝ) ≤ (cordicWords k b (γ * Real.sqrt s * c0) ζ : ℝ) := Nat.cast_nonneg _
  nlinarith

/-- **The register of the time-dependent binary construction in the bit lengths**
(`hs:eq:gate-total`, time-dependent part): under the hypotheses of `GateBitBudget.hs_gatesT_le`
(`γ ≤ 1 ≤ γ √s`, the released bound `2^r ≤ 4 (4608 q + 1)`, `s = 2^σ`, `σ ≤ k`, `b ≤ b_data`,
`c₀ > 0` of bit length `b_data`, `ζ ≥ ε/(442368 q)`, `q = √s t + √(st log(2/ε)) + log(2/ε)`,
`0 < ε ≤ 1`), the register of `binaryTimeSim` on `M = 2^m` time slots,
`k + (2(k+1) + 3m + 6r + 3) + (6k + 2b + bT + bP + A + 3)` qubits, has at most
`4·10⁶ (𝔟_H + log₂(M+1) + 1)³` qubits. -/
theorem binary_registerT_le (s k b m σ bd : ℕ) {γ c0 t ε ζ : ℝ} (hs : s = 2 ^ σ) (hσ : σ ≤ k)
    (hbd : b ≤ bd) (hγ1 : γ ≤ 1) (hγs : 1 ≤ γ * Real.sqrt s) (ht : 0 ≤ t) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hbits : HasBits bd c0) (hc0 : 0 < c0) (hζ : 0 < ζ)
    (hζlo : ε ≤ 442368 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) * ζ)
    (hr : ((2 ^ simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℕ) : ℝ) ≤
      4 * (4608 * ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) + 1)) :
    ((k + (2 * (k + 1) + 3 * m +
        6 * simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 3) +
      (6 * k + 2 * b + (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT +
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).A + 3) : ℕ) : ℝ) ≤
      4 * 10 ^ 6 *
        (bitH bd (2 ^ k) (ImprovedPrecisionBudget.shape s t (Real.log (2 / ε))) ε +
          Real.logb 2 (((2 ^ m : ℕ) : ℝ) + 1) + 1) ^ 3 := by
  have hℓ : 1 / 2 ≤ Real.log (2 / ε) := ImprovedPrecisionBudget.targetLog_ge_half ε hε hε1
  have hQ : 1 / 2 ≤ ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) :=
    hℓ.trans (le_shape _ _ _ ht)
  have hQ0 : 0 ≤ ImprovedPrecisionBudget.shape s t (Real.log (2 / ε)) := by linarith
  have hu := cordicWords_le bd k b σ s hs hσ hγ1 hγs hbd hbits hc0 hζ hQ0 hε hε1 hζlo
  have hB0 := bitH_nonneg bd (2 ^ k) hQ0 hε hε1
  have hM0 := logb_succ_nonneg (2 ^ m)
  have hcube := cube_le (Nat.cast_nonneg _) hB0 hu
  have e26 : ((25 : ℝ) + 1) ^ 3 = 17576 := by norm_num
  rw [e26] at hcube
  have hreg := cordic_register_le k b (valXT k b m) (valYT k b m) (γ * Real.sqrt s * c0) ζ
  have hreg' : ((9 * k + 2 * b + (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT +
      (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
      (binArithT k b m (γ * Real.sqrt s * c0) ζ).A : ℕ) : ℝ) ≤
      13 * (cordicWords k b (γ * Real.sqrt s * c0) ζ : ℝ) + 11 +
        207 * ((cordicWords k b (γ * Real.sqrt s * c0) ζ : ℝ) + 1) ^ 3 := by
    exact_mod_cast hreg
  have hsR := simR_word _ hQ0 hε hε1 hr
  have hkN := nat_le_logb k
  have hmM := nat_le_logb m
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
  have hcast : ((k + (2 * (k + 1) + 3 * m +
        6 * simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) + 3) +
      (6 * k + 2 * b + (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT +
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).A + 3) : ℕ) : ℝ) =
      ((9 * k + 2 * b + (binArithT k b m (γ * Real.sqrt s * c0) ζ).bT +
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).bP +
        (binArithT k b m (γ * Real.sqrt s * c0) ζ).A : ℕ) : ℝ) + 3 * (m : ℝ) +
        6 * (simR (width (s : ℝ) γ) (time (s : ℝ) t γ) (moment γ) (ε / 4) : ℝ) + 8 := by
    push_cast
    ring
  rw [hcast]
  rw [hB] at hB1 hBB hcube hu ⊢
  have hu0 : (0 : ℝ) ≤ (cordicWords k b (γ * Real.sqrt s * c0) ζ : ℝ) := Nat.cast_nonneg _
  nlinarith

/-! ### The cubic workspace of the released CORDIC arithmetic -/

/-- **The released CORDIC workspace is cubic in its steps** (`hs:eq:gate-total`): it has at
least `12 n³` work wires for `n = nOf ζ` steps (`A = 1 + 2w + (6(n+1)+1) w` with
`w ≥ 2 n²`). -/
theorem cordic_A_ge {B : Type*} (b : ℕ) (xw yw : Fin b → B) (κ ζ : ℝ) :
    12 * Cordic.nOf ζ ^ 3 ≤ (cordicArith b xw yw κ ζ).A := by
  obtain ⟨-, hA, -, -⟩ := cordicArith_counts b xw yw κ ζ
  obtain ⟨hn, -, -, hw⟩ := params_fields b κ ζ
  rw [hA, hn, hw]
  have h1 : 12 * Cordic.nOf ζ ^ 3 ≤
      (6 * (Cordic.nOf ζ + 1) + 1) * (2 * (Cordic.nOf ζ * Cordic.nOf ζ)) := by
    ring_nf
    nlinarith
  refine h1.trans (le_add_left (Nat.mul_le_mul_left _ ?_))
  omega

/-- The number of CORDIC steps is at least `log₂(8/ζ) + 2` (`hs:eq:gate-total`). -/
theorem nOf_ge {ζ : ℝ} (hζ : 0 < ζ) : Real.logb 2 (8 / ζ) + 2 ≤ (Cordic.nOf ζ : ℝ) := by
  have h1 : ((⌈8 / ζ⌉₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 ⌈8 / ζ⌉₊ := by
    exact_mod_cast Nat.le_pow_clog (by norm_num) _
  have h3 : Real.logb 2 (8 / ζ) ≤ Nat.clog 2 ⌈8 / ζ⌉₊ := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_natCast]
    exact (Nat.le_ceil _).trans h1
  have e : (Cordic.nOf ζ : ℝ) = Nat.clog 2 ⌈8 / ζ⌉₊ + 2 := by
    unfold Cordic.nOf
    push_cast
    ring
  linarith

/-- **No quadratic qubit bound for the released arithmetic** (`hs:eq:gate-total`,
`hs:eq:gate-binary`): in the accuracy window of the bit-length endpoints (`221184 q ζ ≤ ε`,
`q ≥ 1/2`, `0 < ε ≤ 1`) the CORDIC workspace of the binary construction has at least
`12 (log₂(1/ε))³` qubits. For fixed data `𝔟_H` grows like `log₂(1/ε)` as `ε → 0`, so no bound
`C (𝔟_H + 1)²` holds for the registers of these circuits. -/
theorem binArith_A_ge (k b : ℕ) (κ : ℝ) {q ε ζ : ℝ} (hζ : 0 < ζ) (hq : 1 / 2 ≤ q)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hw : 221184 * q * ζ ≤ ε) :
    12 * Real.logb 2 (1 / ε) ^ 3 ≤ ((binArith k b κ ζ).A : ℝ) := by
  have hA : ((12 * Cordic.nOf ζ ^ 3 : ℕ) : ℝ) ≤ ((binArith k b κ ζ).A : ℝ) := by
    exact_mod_cast cordic_A_ge b (valX k b) (valY k b) κ ζ
  have hle : 1 / ε ≤ 8 / ζ := by
    rw [div_le_div_iff₀ hε hζ]
    nlinarith
  have hl : Real.logb 2 (1 / ε) ≤ Real.logb 2 (8 / ζ) :=
    Real.logb_le_logb_of_le one_lt_two (by positivity) hle
  have h0 : 0 ≤ Real.logb 2 (1 / ε) :=
    Real.logb_nonneg one_lt_two (by rw [le_div_iff₀ hε]; linarith)
  have h3 : Real.logb 2 (1 / ε) ^ 3 ≤ (Cordic.nOf ζ : ℝ) ^ 3 :=
    pow_le_pow_left₀ h0 (by linarith [nOf_ge hζ]) 3
  push_cast at hA
  linarith

end

end SparseHamiltonian.GateRemarks
