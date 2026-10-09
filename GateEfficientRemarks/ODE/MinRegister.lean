import ZeroTimeGateODE.Synth
import GateEfficientBitBudget.Bits
import GateEfficientODEBudget.Shape

/-!
# The minimal register of the direct source assembly and the word budget `𝔟`

The remark of Theorem `ode:thm:gates` of the accompanying paper ("Zero time or a known zero
generator uses direct source assembly and needs no matrix calls") is formalised in the released
library `ZeroTimeGateODE` on every native ODE register `ZeroTimeGateODE.ZNW a m r K k l f S Zs Z
bT bP A`: the direct source assembly uses no simulator, LCHS, private-operation or arithmetic
wire. For the absolute-constant forms of equations `ode:eq:gate-main` and `ode:eq:gate-space` in
the word budget `𝔟` of `ode:eq:gate-word-budget` we use the register without these work wires:

* `MinW k k_x Zs = ZNW 0 0 0 0 k 0 0 (Fin k_x) Zs Empty 0 0 0`: the sector wire `sec`, the
  source-label wire `ini`, the `k`-bit source-label word (`k = 0` for constant coefficients, the `m`
  mesh bits of the weight preparation for time-dependent coefficients) and the flags `hf`, `lf`,
  `flg` of the released wire types with zero parameters (`card_AW_min`: `k + 5` wires), the three
  native flags (`card_XW_min`), the system qubits `Fin k_x`, the source scratch `Zs` and the
  released pool of the native zero tests: `2 k_x + 2 k + 2 |Zs| + 17` qubits (`card_MinW`),
  `k + k_x + |Zs| + 8` wires tested by the zero tests (`tested_min`);
* `MinSW k k_x Zs Xa`: its trial register for the synthesis of the preparation with the per-trial
  claim (`GateSynthTrials.SWO` with the synthesis ancillas `Xa`):
  `4 k_x + 4 k + 4 |Zs| + 2 |Xa| + 35` qubits (`card_MinSW`), `2 k + 2 k_x + 2 |Zs| + |Xa| + 17`
  tested wires (`tested_minS`).

The word budget in the zero case: the query shape `q* = qOf s T η_H η_D g ε` is at least `1` for
`T, η_H, η_D ≥ 0` (`one_le_qOf`) and equals `ℓ = log(10⁴ g/ε)` in the zero case (`qOf_zero`);
`k_x ≤ 𝔟` and `k_x + m ≤ 𝔟` for `N = 2^k_x` and `M = 2^m` (`kx_le_bitB`, `kx_add_le_bitB`); and
the logarithm of the synthesis accuracy is bounded by `𝔟` (`log_le_bitB`, `log_trial_le`,
`log_trialT_le`: `log((N+1)/(ν/3)) ≤ 64 (𝔟+1) + log(G_src + 1)`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open GateCircuit GateNative
open SparseHamiltonian.GateBitBudget (bitB)
open ImprovedODEQueryBudget (precision logBudget)

/-! ### The registers -/

/-- **The minimal register of the direct source assembly**: the native ODE register
`ZNW 0 0 0 0 k 0 0 (Fin k_x) Zs Empty 0 0 0` without simulator, LCHS, private-operation and
arithmetic wires; `k` source-label bits, system `Fin k_x`, source scratch `Zs`. -/
abbrev MinW (k kx : ℕ) (Zs : Type*) [Fintype Zs] : Type _ :=
  ZeroTimeGateODE.ZNW 0 0 0 0 k 0 0 (Fin kx) Zs Empty 0 0 0

/-- **The trial register of the minimal register** for the synthesis of the preparation with
the per-trial claim, with the synthesis ancillas `Xa`. -/
abbrev MinSW (k kx : ℕ) (Zs Xa : Type*) [Fintype Zs] [Fintype Xa] : Type _ :=
  GateSynthTrials.SWO 0 0 0 0 k 0 0 (Fin kx) Zs
    (ZeroTimeGateODE.zPool 0 0 0 0 k 0 0 (Fin kx) Zs Empty 0 0 0) Empty 0 0 0 Xa

/-- The released wire types with zero parameters and a `k`-bit source-label word have `k + 5`
wires. -/
theorem card_AW_min (k : ℕ) : Fintype.card (GateODE.AW 0 0 0 0 k 0 0) = k + 5 := by
  rw [Fintype.card_sum, GateCircuit.Sim.card_wire, GateODE.card_oWire]
  omega

/-- The native work wires without private scratch and arithmetic: the three native flags. -/
theorem card_XW_min : Fintype.card (XW Empty 0 0 0) = 3 := by
  simp [XW, AWr]

section Cards

variable (k kx : ℕ) (Zs Xa : Type*) [Fintype Zs] [Fintype Xa]

/-- **The qubits of the minimal register**: `2 k_x + 2 k + 2 |Zs| + 17`. -/
theorem card_MinW : Fintype.card (MinW k kx Zs) = 2 * kx + 2 * k + 2 * Fintype.card Zs + 17 := by
  rw [ZeroTimeGateODE.card_ZNW, card_AW_min, Fintype.card_fin, Fintype.card_empty]
  ring

/-- **The wires tested by the zero tests on the minimal register**: `k + k_x + |Zs| + 8`. -/
theorem tested_min :
    Fintype.card (GateODE.AW 0 0 0 0 k 0 0) + Fintype.card (XW Empty 0 0 0) + Fintype.card Zs +
      Fintype.card (Fin kx) = k + kx + Fintype.card Zs + 8 := by
  rw [card_AW_min, card_XW_min, Fintype.card_fin]
  ring

/-- **The qubits of the trial register of the minimal register**:
`4 k_x + 4 k + 4 |Zs| + 2 |Xa| + 35`. -/
theorem card_MinSW :
    Fintype.card (MinSW k kx Zs Xa) =
      4 * kx + 4 * k + 4 * Fintype.card Zs + 2 * Fintype.card Xa + 35 := by
  rw [GateSynthTrials.card_SWO, card_AW_min, Fintype.card_fin, Fintype.card_empty]
  simp only [ZeroTimeGateODE.zPool, card_AW_min, card_XW_min, Fintype.card_fin]
  ring

/-- **The wires tested by the zero tests on the trial register of the minimal register**:
`2 k + 2 k_x + 2 |Zs| + |Xa| + 17`. -/
theorem tested_minS :
    Fintype.card (GateODE.AW 0 0 0 0 k 0 0) + Fintype.card (XW Empty 0 0 0) +
      Fintype.card (GateSynthTrials.SX Zs
        (ZeroTimeGateODE.zPool 0 0 0 0 k 0 0 (Fin kx) Zs Empty 0 0 0) Xa) +
      Fintype.card (Fin kx) = 2 * k + 2 * kx + 2 * Fintype.card Zs + Fintype.card Xa + 17 := by
  simp only [GateSynthTrials.SX, OX, ZeroTimeGateODE.zPool, Fintype.card_sum, Fintype.card_unit,
    Fintype.card_fin, Fintype.card_empty, GateCircuit.Sim.card_wire, GateODE.card_oWire]
  ring

end Cards

/-! ### The query shape in the zero case -/

/-- **The query shape is at least one** for `T, η_H, η_D ≥ 0`, `g ≥ 1`, `0 < ε ≤ 1`:
`q* = √s Θ + √(s Θ ℓ) + ℓ ≥ ℓ ≥ 1`. -/
theorem one_le_qOf {s T ηH ηD g ε : ℝ} (hT : 0 ≤ T) (hH : 0 ≤ ηH) (hD : 0 ≤ ηD) (hg : 1 ≤ g)
    (hε : 0 < ε) (hε1 : ε ≤ 1) : 1 ≤ GateODEBudget.qOf s T ηH ηD g ε := by
  have hℓ := ImprovedODEQueryBudget.logBudget_ge_one g ε hg hε hε1
  have hΘ : 0 ≤ GateODEBudget.thetaOf T ηH ηD g ε := by
    unfold GateODEBudget.thetaOf ImprovedODEQueryBudget.theta
    have h1 := mul_nonneg hT hH
    have h2 := mul_nonneg (mul_nonneg hT hD) (by linarith : (0 : ℝ) ≤ logBudget g ε)
    linarith
  unfold GateODEBudget.qOf ImprovedODEQueryBudget.queryShape
  have h3 := mul_nonneg (Real.sqrt_nonneg s) hΘ
  have h4 := Real.sqrt_nonneg (s * GateODEBudget.thetaOf T ηH ηD g ε * logBudget g ε)
  linarith

/-- **The query shape in the zero case** is the logarithmic envelope: for `T = 0` or
`η_H + η_D = 0` (with `η_H, η_D ≥ 0`), `Θ = 0` and `q* = ℓ = log(10⁴ g/ε)`. -/
theorem qOf_zero {s T ηH ηD g ε : ℝ} (hH : 0 ≤ ηH) (hD : 0 ≤ ηD) (hz : T = 0 ∨ ηH + ηD = 0) :
    GateODEBudget.qOf s T ηH ηD g ε = logBudget g ε := by
  have hΘ : GateODEBudget.thetaOf T ηH ηD g ε = 0 := by
    unfold GateODEBudget.thetaOf ImprovedODEQueryBudget.theta
    rcases hz with h | h
    · rw [h]
      ring
    · have h1 : ηH = 0 := by linarith
      have h2 : ηD = 0 := by linarith
      rw [h1, h2]
      ring
  unfold GateODEBudget.qOf ImprovedODEQueryBudget.queryShape
  rw [hΘ]
  simp

/-! ### The word budget -/

/-- `log₂((Q g + 1)/ε) ≥ 0` for `Q g ≥ 0` and `0 < ε ≤ 1`. -/
theorem logb_X_nonneg {Q g ε : ℝ} (hQg : 0 ≤ Q * g) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ Real.logb 2 ((Q * g + 1) / ε) := by
  apply Real.logb_nonneg one_lt_two
  rw [le_div_iff₀ hε]
  linarith

/-- **The system qubits are at most `𝔟`**: `k_x ≤ bitB b_data (2^k_x) M m_src Q g ε` for
`Q g ≥ 0` and `0 < ε ≤ 1`. -/
theorem kx_le_bitB (bd kx M msrc : ℕ) {Q g ε : ℝ} (hQg : 0 ≤ Q * g) (hε : 0 < ε)
    (hε1 : ε ≤ 1) : (kx : ℝ) ≤ bitB bd (2 ^ kx) M msrc Q g ε := by
  have h1 := GateBitBudget.nat_le_logb kx
  have h2 := GateBitBudget.logb_succ_nonneg M
  have h3 := GateBitBudget.logb_succ_nonneg msrc
  have h4 := logb_X_nonneg hQg hε hε1
  have h5 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  unfold bitB
  linarith

/-- **The system qubits and the mesh bits are at most `𝔟`**:
`k_x + m ≤ bitB b_data (2^k_x) (2^m) m_src Q g ε` for `Q g ≥ 0` and `0 < ε ≤ 1`. -/
theorem kx_add_le_bitB (bd kx m msrc : ℕ) {Q g ε : ℝ} (hQg : 0 ≤ Q * g) (hε : 0 < ε)
    (hε1 : ε ≤ 1) : (kx : ℝ) + m ≤ bitB bd (2 ^ kx) (2 ^ m) msrc Q g ε := by
  have h1 := GateBitBudget.nat_le_logb kx
  have h2 := GateBitBudget.nat_le_logb m
  have h3 := GateBitBudget.logb_succ_nonneg msrc
  have h4 := logb_X_nonneg hQg hε hε1
  have h5 : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
  unfold bitB
  linarith

/-- **The logarithm of the synthesis accuracy in `𝔟`**: for `G ≥ 0`, `0 < c₂ ≤ 2^17`, `g ≥ 1`,
`0 < ε ≤ 1`, `Q ≥ 1` and `0 < x ≤ c₂ (G + 1) g/ε`,
`log x ≤ 12 + log(G + 1) + bitB b_data N M m_src Q g ε`. -/
theorem log_le_bitB (bd N M msrc : ℕ) {G c₂ g ε Q x : ℝ} (hG : 0 ≤ G) (hc : 0 < c₂)
    (hc2 : c₂ ≤ 2 ^ 17) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) (hQ : 1 ≤ Q) (hx0 : 0 < x)
    (hx : x ≤ c₂ * (G + 1) * (g / ε)) :
    Real.log x ≤ 12 + Real.log (G + 1) + bitB bd N M msrc Q g ε := by
  have hg0 : 0 < g := by linarith
  have h1 : Real.log x ≤ Real.log (c₂ * (G + 1) * (g / ε)) := Real.log_le_log hx0 hx
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    at h1
  have hc₂ : Real.log c₂ ≤ 12 := by
    have h := Real.log_le_log hc hc2
    rw [Real.log_pow] at h
    have h2 := Real.log_two_lt_d9
    norm_num at h h2 ⊢
    linarith
  have hQg : 0 ≤ Q * g := by positivity
  have hX : 1 ≤ (Q * g + 1) / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have h2 : Real.log (g / ε) ≤ Real.log ((Q * g + 1) / ε) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by nlinarith) hε.le)
  have h3 := GateBitBudget.log_le_logb _ hX
  have h4 : Real.logb 2 ((Q * g + 1) / ε) ≤ bitB bd N M msrc Q g ε := by
    have := GateBitBudget.logb_succ_nonneg N
    have := GateBitBudget.logb_succ_nonneg M
    have := GateBitBudget.logb_succ_nonneg msrc
    have : (0 : ℝ) ≤ bd := Nat.cast_nonneg _
    unfold bitB
    linarith
  linarith

/-- **The synthesis factor of the zero-case preparation, constant coefficients**: for
`N = G + 3` (the `G + 2` gates of the direct source assembly plus one), `ν = ε/(10⁴ g)`, `g ≥ 1`,
`0 < ε ≤ 1` and `Q ≥ 1`: `log(N/(ν/3)) ≤ 64 (𝔟 + 1) + log(G + 1)`,
`𝔟 = bitB b_data N' M m_src Q g ε`. -/
theorem log_trial_le (bd N' M msrc : ℕ) {G N g ε Q : ℝ} (hG : 0 ≤ G) (hN : N = G + 3)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) (hQ : 1 ≤ Q) :
    Real.log (N / (precision g ε / 3)) ≤
      64 * (bitB bd N' M msrc Q g ε + 1) + Real.log (G + 1) := by
  have hg0 : 0 < g := by linarith
  have e : N / (precision g ε / 3) = 30000 * N * (g / ε) := by
    unfold precision
    field_simp
    ring
  have hx : N / (precision g ε / 3) ≤ 90000 * (G + 1) * (g / ε) := by
    rw [e, hN]
    have : 0 ≤ g / ε := by positivity
    nlinarith
  have hpos : 0 < N / (precision g ε / 3) := by
    rw [e, hN]
    positivity
  have h := log_le_bitB bd N' M msrc hG (by norm_num) (by norm_num) hg hε hε1 hQ hpos hx
  have hB := GateBitBudget.bitB_nonneg bd N' M msrc (by positivity : (0 : ℝ) ≤ Q * g) hε hε1
  linarith

/-- **The synthesis factor of the zero-case preparation, time-dependent coefficients**: for
`N = G + 1` (the `G` gates of the direct source assembly plus one), `ν = (ε/2)/(10⁴ · 2g)`,
`g ≥ 1`, `0 < ε ≤ 1` and `Q ≥ 1`: `log(N/(ν/3)) ≤ 64 (𝔟 + 1) + log(G + 1)`,
`𝔟 = bitB b_data N' M m_src Q g ε`. -/
theorem log_trialT_le (bd N' M msrc : ℕ) {G N g ε Q : ℝ} (hG : 0 ≤ G) (hN : N = G + 1)
    (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1) (hQ : 1 ≤ Q) :
    Real.log (N / (precision (2 * g) (ε / 2) / 3)) ≤
      64 * (bitB bd N' M msrc Q g ε + 1) + Real.log (G + 1) := by
  have hg0 : 0 < g := by linarith
  have e : N / (precision (2 * g) (ε / 2) / 3) = 120000 * (G + 1) * (g / ε) := by
    rw [hN]
    unfold precision
    field_simp
    ring
  have hpos : 0 < N / (precision (2 * g) (ε / 2) / 3) := by
    rw [e]
    positivity
  have h := log_le_bitB bd N' M msrc hG (by norm_num) (by norm_num) hg hε hε1 hQ hpos e.le
  have hB := GateBitBudget.bitB_nonneg bd N' M msrc (by positivity : (0 : ℝ) ≤ Q * g) hε hε1
  linarith

end

end SparseHamiltonian.GateRemarks.ODE
