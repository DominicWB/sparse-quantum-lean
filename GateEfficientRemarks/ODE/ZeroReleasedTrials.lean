import GateEfficientRemarks.ODE.ZeroReleased
import GateEfficientBitBudget.Synth
import ZeroTimeGateODE.BinarySynth

/-!
# Zero time or a known zero generator over a finite gate set: the budgets in `𝔟` on the released
trial register

The finite-gate-set forms of `ZeroReleased` (equations `ode:eq:gate-main`, `ode:eq:gate-space` and
`ode:eq:gate-word-budget` of Theorem `ode:thm:gates` with its remark on zero time and a known zero
generator) with the per-trial claim: only the preparation is synthesised
(`GateSynthTrials.synthPrep hS (ν/3)`), as in the released
`GateBitBudget.binary_ode_budget_trials_bits` and in the released every-`T ≥ 0` form
`ZeroTimeGateODE.binary_ode_solver_nonneg_trials`, on the released trial register
`GateSynthTrials.SNW` (the released binary register with the synthesis ancillas `Xa`):

* `prepBound_le_zero`, `zero_gates_le_prepBound` (zero case): the released native preparation
  bound `B = GateODEBudget.prepBound q srcC` satisfies `B ≤ 2·10¹⁸ q* (𝔟+1)³ + G_src` (the bound
  of `GateBitBudget.prepBound_le`, for `𝔟 = bitB b_data (2^k_x) M m_src q* g ε` with every `M`,
  `m_src`), and the direct source assembly has `G_src + 2 ≤ B` gates; `trial_count_le` is the
  monotonicity of the synthesised count in the preparation bound;
* `binary_ode_budget_trials_bits_zero_released` (zero case `BZeroCase`, `γ` of bit length
  `b_data`): every bound of `GateBitBudget.binary_ode_budget_trials_bits`, in its order, for the
  protocol `nprotocol (synthPrep hS (ν/3) (bprepC q srcC)) g`: `B ≤ 2·10¹⁸ q* (𝔟+1)³ + G_src`; at
  most `40 g (2·10¹⁸ q* (𝔟+1)³ + G_src) (c₁ (64 (𝔟+1) + log(G_src+1)) + c₀) +
  20 g (4 (3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢` on at most
  `7·10¹¹ (𝔟+1)³ + 4 |Zs| + 2 |Xa|` qubits; valid trials of `𝒢`; one preparation within `B`
  gates; the synthesised count `40 g B (c₁ log((B+1)/(ν/3)) + c₀) + 20 g (4 n' + 3)`,
  `n' = 22 k_x + 12 m + 24 r + 4 k + 4 l + 8 b + 2 (bT + bP + A) + 2 |Zs| + |Xa| + 47`; at most
  `40 g` times the calls of the source circuits (no matrix call); and the register identity
  `|SNW| = 44 k_x + 24 m + 48 r + 8 k + 8 l + 16 b + 4 (bT + bP + A) + 4 |Zs| + 2 |Xa| + 95`;
  further `q* = ℓ`, the `N = G_src + 2` gates of one preparation, the sharper count
  `40 g N (c₁ log((N+1)/(ν/3)) + c₀) + 20 g (4 (n + |Xa|) + 3)` (`n` the qubits of the released
  register), no call of a kind that the source circuits do not call, and `NOutcome` under the
  zero-case conditions;
* `binary_ode_budget_trials_bits_nonneg` (every `T ≥ 0`): every conclusion of the released
  `GateBitBudget.binary_ode_budget_trials_bits`, in its order, for the protocol
  `nprotocol (synthPrep hS (ν/3) (bprepC q srcC)) g` (the calls with the matrix part
  `if BZeroCase q then 0 else 3932160 g q* (…)`, `NOutcome` under the released hypotheses), with
  `γ` of bit length `b_data` in the zero case and the public rescaling otherwise.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateBinary GateSynth GateSynthTrials
open ZeroTimeGateODE (zprepC srcRot bprepC BPublicOK0 BZeroCase)
open GateBinaryODE (Pub mLift SZ4 card_SZ4)
open SparseHamiltonian.GateBitBudget (bitB bitB_nonneg HasBits)
open GateODEBudget (qOf words gammaOf prepBound)
open ImprovedODEQueryBudget (logBudget)
open NativeSparseBlockEncoding (Data Query)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **The released form of a synthesised gate budget**: if
`W ≤ a₁ g N (c₁ L + c₀) + a₂ g (4 n + 3)` with `0 ≤ N ≤ 2·10¹⁸ Q Y + G`,
`0 ≤ L ≤ 64 (B + 1) + λ`, `n ≤ 3·10¹¹ Y + 2 Z + X` and nonnegative constants, then
`W ≤ a₁ g (2·10¹⁸ Q Y + G) (c₁ (64 (B + 1) + λ) + c₀) + a₂ g (4 (3·10¹¹ Y + 2 Z + X) + 3)`. -/
theorem trial_budget_le {W a₁ a₂ g c₀ c₁ N L Q Y G B lam n Z Xs : ℝ} (ha₁ : 0 ≤ a₁)
    (ha₂ : 0 ≤ a₂) (hg : 0 ≤ g) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hN0 : 0 ≤ N)
    (hN : N ≤ 2 * 10 ^ 18 * Q * Y + G) (hL0 : 0 ≤ L) (hL : L ≤ 64 * (B + 1) + lam)
    (hn : n ≤ 3 * 10 ^ 11 * Y + 2 * Z + Xs)
    (hW : W ≤ a₁ * g * (N * (c₁ * L + c₀)) + a₂ * g * (4 * n + 3)) :
    W ≤ a₁ * g * ((2 * 10 ^ 18 * Q * Y + G) * (c₁ * (64 * (B + 1) + lam) + c₀)) +
      a₂ * g * (4 * (3 * 10 ^ 11 * Y + 2 * Z + Xs) + 3) := by
  have hF : c₁ * L + c₀ ≤ c₁ * (64 * (B + 1) + lam) + c₀ := by
    have := mul_le_mul_of_nonneg_left hL hc₁
    linarith
  have hprod : N * (c₁ * L + c₀) ≤
      (2 * 10 ^ 18 * Q * Y + G) * (c₁ * (64 * (B + 1) + lam) + c₀) :=
    mul_le_mul hN hF (by positivity) (le_trans hN0 hN)
  have h1 := mul_le_mul_of_nonneg_left hprod (mul_nonneg ha₁ hg)
  have h2 : a₂ * g * (4 * n + 3) ≤ a₂ * g * (4 * (3 * 10 ^ 11 * Y + 2 * Z + Xs) + 3) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg ha₂ hg)
  linarith

/-- **The released trial register**: the wires tested by the zero tests of the trial register of
the released binary register are its `n` qubits plus the `|Xa|` synthesis ancillas, and the trial
register has `2 n + 2 |Xa| + 1` qubits. -/
theorem card_trial_released (q : Pub) (Zs Xa : Type*) [Fintype Zs] [DecidableEq Zs]
    [Fintype Xa] [DecidableEq Xa] :
    Fintype.card (GateODE.AW q.params.a q.params.m q.params.r q.params.K q.params.k q.params.l
      q.params.f) + Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
      Fintype.card (SX Zs (ZeroTimeGateODE.zPool q.params.a q.params.m q.params.r q.params.K
        q.params.k q.params.l q.params.f (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
        Xa) + Fintype.card (Fin q.kx) =
      Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
        Fintype.card Xa ∧
    Fintype.card (SNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) =
      2 * Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
        2 * Fintype.card Xa + 1 := by
  have hNW := (ZeroTimeGateODE.card_ZNW (S := Fin q.kx) (Zs := Zs) (Z := SZ4 q.kx q.b)
    q.params.a q.params.m q.params.r q.params.K q.params.k q.params.l q.params.f q.ar.bT q.ar.bP
    q.ar.A : Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) = _)
  have hSNW := (GateSynthTrials.card_SWO : Fintype.card
    (SNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) = _)
  have hnP : nPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A =
      ZeroTimeGateODE.zPool q.params.a q.params.m q.params.r q.params.K q.params.k q.params.l
        q.params.f (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A := rfl
  rw [hnP] at hSNW
  rw [card_SZ4, Fintype.card_fin] at hNW hSNW
  have hXW : Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3 := by
    simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin]
    ring
  have hSX : Fintype.card (SX Zs (ZeroTimeGateODE.zPool q.params.a q.params.m q.params.r
      q.params.K q.params.k q.params.l q.params.f (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
      q.ar.A) Xa) = Fintype.card Zs + 1 + ZeroTimeGateODE.zPool q.params.a q.params.m q.params.r
      q.params.K q.params.k q.params.l q.params.f (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
      q.ar.A + Fintype.card Xa := by
    simp only [SX, OX, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
    ring
  have hzP : ZeroTimeGateODE.zPool q.params.a q.params.m q.params.r q.params.K q.params.k
      q.params.l q.params.f (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A =
      Fintype.card (GateODE.AW q.params.a q.params.m q.params.r q.params.K q.params.k q.params.l
        q.params.f) + Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
        Fintype.card Zs + q.kx := by
    show _ + _ + _ + Fintype.card (Fin q.kx) = _
    rw [Fintype.card_fin]
  constructor
  · rw [hSX, hzP, hNW, Fintype.card_fin, hXW]
    omega
  · rw [hSNW, hNW, hzP, hXW]
    omega

/-- **The monotonicity of the synthesised count in the preparation bound**: if
`W ≤ a₁ g N (c₁ log((N+1)/(ν/3)) + c₀) + a₂ g (4 n + 3)` with `0 ≤ N ≤ B`, `0 < ν ≤ 1`, `n ≤ n'`
and nonnegative constants, then `W ≤ a₁ g B (c₁ log((B+1)/(ν/3)) + c₀) + a₂ g (4 n' + 3)` (the
released form of `GateODEBudget.binary_ode_budget_trials` with the preparation bound `B`). -/
theorem trial_count_le {W a₁ a₂ g c₀ c₁ N B ν n n' : ℝ} (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂)
    (hg : 0 ≤ g) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hN0 : 0 ≤ N) (hNB : N ≤ B) (hν : 0 < ν)
    (hν1 : ν ≤ 1) (hn : n ≤ n')
    (hW : W ≤ a₁ * g * (N * (c₁ * Real.log ((N + 1) / (ν / 3)) + c₀)) + a₂ * g * (4 * n + 3)) :
    W ≤ a₁ * g * (B * (c₁ * Real.log ((B + 1) / (ν / 3)) + c₀)) + a₂ * g * (4 * n' + 3) := by
  have hlog0 : 0 ≤ Real.log ((N + 1) / (ν / 3)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hlog : Real.log ((N + 1) / (ν / 3)) ≤ Real.log ((B + 1) / (ν / 3)) :=
    Real.log_le_log (div_pos (by linarith) (by positivity))
      (div_le_div_of_nonneg_right (by linarith) (by positivity))
  exact hW.trans (GateBitBudget.synth_arith ha₁ ha₂ hg hN0 hNB hlog0 hlog hc₀ hc₁ hn)

/-- **The preparation bound in `𝔟` in the zero case**, constant coefficients (equation
`ode:eq:gate-main` over a finite gate set, in the word budget `ode:eq:gate-word-budget`): for binary
public data with `BPublicOK0 q` in the zero case, a rescaling `γ` of bit length `b_data`, an
arithmetic accuracy `ζ ≥ ν/(196608 q*)`, stored bits `b ≤ b_data`, `c₀`, `η_H`, `η_D` of bit length
`b_data` and any `M`, `m_src`, the released native preparation bound
`B = GateODEBudget.prepBound q srcC` satisfies `B ≤ 2·10¹⁸ q* (𝔟+1)³ + G_src`,
`𝔟 = bitB b_data (2^k_x) M m_src q* g ε`: the bound of `GateBitBudget.prepBound_le`, from the word
budget `zero_words_le`. -/
theorem prepBound_le_zero (bd : ℕ) (q : Pub) (hq : BPublicOK0 q) (hz : BZeroCase q)
    (hγb : HasBits bd q.γ)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ) (hb : q.b ≤ bd)
    (hc0 : HasBits bd q.c0) (hH : HasBits bd q.etaH) (hD : HasBits bd q.etaD) {Zs : Type*}
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query)) (M msrc : ℕ) :
    prepBound q srcC ≤ 2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD q.g q.ε *
        (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
      ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) := by
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
  have hℓ := ImprovedODEQueryBudget.logBudget_ge_one q.g q.ε hq.g_ge hq.ε_pos hε1
  have hw0 := zero_words_le bd q hq hz hγb hζ hb hc0 hH hD
  have hmono := GateBitBudget.bitB_mono bd (2 ^ q.kx) 0 0 M msrc
    (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε (Nat.zero_le _) (Nat.zero_le _)
  have hw : (words q : ℝ) + logBudget q.g q.ε ≤
      300 * (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) := by
    linarith
  obtain ⟨hGC, -, -, -⟩ := GateODEBudget.binary_arith_words q
  have hσ := q.hσ
  have hQg : 0 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε * q.g := by positivity
  have hB0 := bitB_nonneg bd (2 ^ q.kx) M msrc hQg hq.ε_pos hε1
  have hwd0 : (0 : ℝ) ≤ words q := Nat.cast_nonneg _
  have hGC' : (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) :
      ℕ) : ℝ)) ≤ 65536 * ((words q : ℝ) + 1) ^ 3 := by exact_mod_cast hGC
  have hS : (q.kx : ℝ) + q.σ + q.params.m + q.params.r + q.params.k ≤ 2 * (words q : ℝ) := by
    have : q.kx + q.σ + q.params.m + q.params.r + q.params.k ≤ 2 * words q := by
      unfold words
      omega
    exact_mod_cast this
  have hl : (q.params.l : ℝ) ≤ words q := by
    have : q.params.l ≤ words q := by
      unfold words
      omega
    exact_mod_cast this
  have hin := GateBitBudget.inner_le hwd0 hℓ hGC' hS (Nat.cast_nonneg _) hl
  have hcube := GateBitBudget.cube_le (by linarith) hB0 hw
  unfold GateODEBudget.prepBound
  have h1 : (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) : ℕ) :
      ℝ) + q.kx + q.σ + q.params.m + q.params.r + q.params.k +
      logBudget q.g q.ε * ((q.params.l : ℝ) + 1) + 8) ≤
      65547 * ((300 + 1) ^ 3 * (bitB bd (2 ^ q.kx) M msrc
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3) := by
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 819400 *
    qOf q.s q.T q.etaH q.etaD q.g q.ε)
  have hY2 : 0 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε *
      (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 := by
    positivity
  linarith

/-- **The direct source assembly within the released preparation bound**, constant coefficients:
for binary public data with `BPublicOK0 q` (every `T ≥ 0`), `G_src + 2` is at most the released
native preparation bound `B = GateODEBudget.prepBound q srcC = 819400 q* (…) + G_src` (the
polynomial factor is at least `8` and `q* ≥ 1`). -/
theorem zero_gates_le_prepBound (q : Pub) (hq : BPublicOK0 q) {Zs : Type*}
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query)) :
    ((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) : ℝ) ≤ prepBound q srcC := by
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
  have hℓ := ImprovedODEQueryBudget.logBudget_ge_one q.g q.ε hq.g_ge hq.ε_pos hε1
  unfold GateODEBudget.prepBound
  have hS : (8 : ℝ) ≤ (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
      (2 * q.ar.bP + q.ar.bT + 1) : ℕ) : ℝ) + q.kx + q.σ + q.params.m + q.params.r + q.params.k +
      logBudget q.g q.ε * ((q.params.l : ℝ) + 1) + 8) :=
    le_add_of_nonneg_left (add_nonneg (by positivity) (mul_nonneg (by linarith) (by positivity)))
  have h1 := mul_le_mul hQ1 hS (by norm_num) (by linarith)
  have e : ((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) : ℝ) =
      (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) + 2 := by
    push_cast
    ring
  rw [e]
  linarith

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` over a finite gate set, with
the per-trial claim, on the released trial register, for zero time or a known zero generator,
constant coefficients** (Theorem `ode:thm:gates` with its remark).

Under `Synthesis 𝒢 Xa len` with `len ζ ≤ c₁ log(1/ζ) + c₀` (`c₀, c₁ ≥ 0`), `AdjClosed 𝒢` and
`zeroTestKinds ⊆ 𝒢`, for binary public data with `BPublicOK0 q` in the zero case, a rescaling `γ`
of bit length `b_data`, an arithmetic accuracy `ζ ≥ ν/(196608 q*)`, stored bits `b ≤ b_data`,
`c₀`, `η_H`, `η_D` of bit length `b_data`, valid source circuits and any `M`, `m_src`, with
`q* = qOf s T η_H η_D g ε` (`= ℓ`), `𝔟 = bitB b_data (2^k_x) M m_src q* g ε`,
`G_src = |srcC 0| + |srcC 1|` and the released preparation bound
`B = GateODEBudget.prepBound q srcC`, the protocol
`nprotocol (synthPrep hS (ν/3) (bprepC q srcC)) g` on the released trial register has every bound
of `GateBitBudget.binary_ode_budget_trials_bits`, in its order: `B ≤ 2·10¹⁸ q* (𝔟+1)³ + G_src`;
in every history at most
`40 g (2·10¹⁸ q* (𝔟+1)³ + G_src) (c₁ (64 (𝔟+1) + log(G_src+1)) + c₀) +
20 g (4 (3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢`; at most
`7·10¹¹ (𝔟+1)³ + 4 |Zs| + 2 |Xa|` qubits; every trial consists of valid gates of `𝒢` and
primitive calls; one preparation has at most `B` gates; at most
`40 g B (c₁ log((B+1)/(ν/3)) + c₀) + 20 g (4 n' + 3)` gates,
`n' = 22 k_x + 12 m + 24 r + 4 k + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + |Xa| + 47`; at most
`40 g (calls_c(srcC 0) + calls_c(srcC 1))` calls of every kind `c` (no matrix call); and
`|SNW| = 44 k_x + 24 m + 48 r + 8 k + 8 l + 16 b + 4 (bT + bP + A_arith) + 4 |Zs| + 2 |Xa| + 95`.
Further `q* = ℓ`; one preparation has exactly `N = G_src + 2` gates; at most
`40 g N (c₁ log((N+1)/(ν/3)) + c₀) + 20 g (4 (n + |Xa|) + 3)` gates, `n` the qubits of the
released register; every history makes no call of a kind that the source circuits do not call;
and under the zero-case conditions (row energy promises, sources within `ζs`, `2 ζs ≤ ν`, public
norms, seed promises, `x(T) ≠ 0`, `r₀ + T r_b ≤ g ‖x(T)‖`) the protocol has the guarantees
`NOutcome` against the solution `x(T)` of `x' = -M̂ x + b`. -/
theorem binary_ode_budget_trials_bits_zero_released (hS : Synthesis 𝒢 Xa len)
    (hadj : AdjClosed 𝒢) (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (bd : ℕ) (q : Pub) (hq : BPublicOK0 q) (hz : BZeroCase q) (hγb : HasBits bd q.γ)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ) (hb : q.b ≤ bd)
    (hc0 : HasBits bd q.c0) (hH : HasBits bd q.etaH) (hD : HasBits bd q.etaD)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (M msrc : ℕ) :
    prepBound q srcC ≤ 2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD q.g q.ε *
        (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
      ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * q.g * ((2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
          ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true))) *
        (c₁ * (64 * (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
            1) + Real.log ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true) + 1)) + c₀)) +
      20 * q.g * (4 * (3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) M msrc
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 + 2 * Fintype.card Zs +
        Fintype.card Xa) + 3) ∧
    (Fintype.card (SNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) : ℝ) ≤
      7 * 10 ^ 11 * (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
        1) ^ 3 + 4 * Fintype.card Zs + 2 * Fintype.card Xa ∧
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) j, i.Valid) ∧
      ∀ gt, NInstr.gate gt ∈ trialN (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) j →
        GateOf 𝒢 gt) ∧
    (nGatesN (bprepC q srcC) : ℝ) ≤ prepBound q srcC ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * q.g * (prepBound q srcC *
        (c₁ * Real.log ((prepBound q srcC + 1) / (q.params.nu / 3)) + c₀)) +
      20 * q.g * (4 * ((22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k +
        4 * q.params.l + 8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs +
        Fintype.card Xa + 47 : ℕ) : ℝ) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g hq.g_ge).worstCost
        (wCallN c) : ℝ) ≤ 40 * q.g * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true))) ∧
    Fintype.card (SNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) =
      44 * q.kx + 24 * q.params.m + 48 * q.params.r + 8 * q.params.k + 8 * q.params.l +
        16 * q.b + 4 * (q.ar.bT + q.ar.bP + q.ar.A) + 4 * Fintype.card Zs +
        2 * Fintype.card Xa + 95 ∧
    qOf q.s q.T q.etaH q.etaD q.g q.ε = logBudget q.g q.ε ∧
    nGatesN (bprepC q srcC) = nGatesN (srcC false) + nGatesN (srcC true) + 2 ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * q.g * ((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) *
        (c₁ * Real.log (((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) + 1) /
          (q.params.nu / 3)) + c₀)) +
        20 * q.g * (4 * ((Fintype.card
          (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card Xa : ℕ) : ℝ) + 3) ∧
    (∀ c : Query → Bool, nCallsN c (srcC false) = 0 → nCallsN c (srcC true) = 0 →
      (nprotocol (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g hq.g_ge).worstCost
        (wCallN c) = 0) ∧
    ∀ x : X,
      (∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      ∀ (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (x0 v : Reg (Fin q.kx) ℂ)
        (ζs : ℝ),
      (∀ c, IsUnitary (Jsrc c)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun (prims (R := ℂ) D en x) (srcC c))
        (liftB (srcIdeal c (Jsrc c))) ζs) →
      2 * ζs ≤ q.params.nu →
      ‖x0‖ = q.r₀ → ‖v‖ = q.rb →
      (x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = unitDirection x0) →
      (v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = unitDirection v) →
      ODEConstantForcing.solution (-mLift D en x) x0 v q.T ≠ 0 →
      q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en x) x0 v q.T‖ →
      NOutcome (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g q.ε hq.g_ge
        (prims (R := ℂ) D en x) (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  obtain ⟨hTr, -, -, hWC, -, hWGlog, -, hout⟩ := ZeroTimeGateODE.native_ode_solver_zero_trials
    (S := Fin q.kx) (Zs := Zs) (Z := SZ4 q.kx q.b) (Y := PY q.kx q.b) (J := Query) hS hadj hzt
    q.params.a q.params.m q.params.r q.params.K q.params.k q.params.l q.params.f q.ar.bT q.ar.bP
    q.ar.A q.T q.g q.ε q.r₀ q.rb hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hq.r₀_nonneg
    hq.rb_nonneg hq.B_pos srcC hsrcV
  obtain ⟨-, hG, -, -, -, -, -, -⟩ := ZeroTimeGateODE.native_ode_solver_zero
    (S := Fin q.kx) (Zs := Zs) (Z := SZ4 q.kx q.b) (Y := PY q.kx q.b) (J := Query)
    q.params.a q.params.m q.params.r q.params.K q.params.k q.params.l q.params.f
    q.ar.bT q.ar.bP q.ar.A q.T q.g q.ε q.r₀ q.rb hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half
    hq.r₀_nonneg hq.rb_nonneg hq.B_pos srcC hsrcV
  obtain ⟨-, hspace, -, -, -, -, -, -, hQz, -, -, -⟩ := binary_ode_budget_bits_zero_released bd
    q hq hz hγb hζ hb hc0 hH hD D en srcC hsrcV M msrc
  obtain ⟨htest, hcardS'⟩ := card_trial_released q Zs Xa
  have hPB := prepBound_le_zero bd q hq hz hγb hζ hb hc0 hH hD srcC M msrc
  have hNP := zero_gates_le_prepBound q hq srcC
  have hcardEq := card_NW_eq q (Zs := Zs)
  have hp : bprepC q srcC = zprepC (srcRot q.T q.r₀ q.rb) srcC := by
    rw [bprepC, if_pos hz]
  have hN : nGatesN (bprepC q srcC) = nGatesN (srcC false) + nGatesN (srcC true) + 2 := by
    rw [hp]
    exact hG
  have htest' : ((Fintype.card (GateODE.AW q.params.a q.params.m q.params.r q.params.K
      q.params.k q.params.l q.params.f) : ℕ) : ℝ) +
      (Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℕ) +
      (Fintype.card (SX Zs (ZeroTimeGateODE.zPool q.params.a q.params.m q.params.r q.params.K
        q.params.k q.params.l q.params.f (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
        Xa) : ℕ) + (Fintype.card (Fin q.kx) : ℕ) =
      ((Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
        Fintype.card Xa : ℕ) : ℝ) := by
    exact_mod_cast htest
  -- the explicit count
  have hexp : ((nprotocol (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g
        hq.g_ge).worstCost wGateN : ℝ) ≤
      40 * q.g * ((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) *
        (c₁ * Real.log (((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) + 1) /
          (q.params.nu / 3)) + c₀)) +
        20 * q.g * (4 * ((Fintype.card
          (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card Xa : ℕ) : ℝ) + 3) := by
    rw [hp]
    have h := hWGlog c₀ c₁ hc₀ hc₁ hlen
    rw [htest'] at h
    exact h
  have hno : ∀ c : Query → Bool, nCallsN c (srcC false) = 0 → nCallsN c (srcC true) = 0 →
      (nprotocol (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g hq.g_ge).worstCost
        (wCallN c) = 0 := by
    intro c h0 h1
    rw [hp]
    have h : ((nprotocol (synthPrep hS (q.params.nu / 3) (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
          (PY q.kx q.b) Query))) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤
        40 * q.g * (nCallsN c (srcC false) + nCallsN c (srcC true) : ℕ) := hWC c
    rw [h0, h1] at h
    have h' : ((nprotocol (synthPrep hS (q.params.nu / 3) (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
          (PY q.kx q.b) Query))) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤ 0 := by
      simpa using h
    exact_mod_cast le_antisymm h' (Nat.cast_nonneg _)
  -- the word budget
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
  have hQg : 0 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε * q.g := by positivity
  have hB0 := bitB_nonneg bd (2 ^ q.kx) M msrc hQg hq.ε_pos hε1
  have hL : Real.log ((((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) : ℝ) + 1) /
      (q.params.nu / 3)) ≤
      64 * (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) +
        Real.log ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true) + 1) :=
    log_trial_le bd (2 ^ q.kx) M msrc (by positivity) (by push_cast; ring) hq.g_ge hq.ε_pos hε1
      hQ1
  have hL0 : 0 ≤ Real.log ((((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) : ℝ) + 1) /
      (q.params.nu / 3)) := by
    have hν : 0 < q.params.nu := ImprovedODEQueryBudget.precision_pos q.g q.ε hq.g_ge hq.ε_pos
    have hν1 : q.params.nu ≤ 1 / 10000 :=
      ImprovedODEQueryBudget.precision_le_one_ten_thousandth q.g q.ε hq.g_ge hε1
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ ((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  have hν : 0 < q.params.nu := ImprovedODEQueryBudget.precision_pos q.g q.ε hq.g_ge hq.ε_pos
  have hν1 : q.params.nu ≤ 1 :=
    (ImprovedODEQueryBudget.precision_le_one_ten_thousandth q.g q.ε hq.g_ge hε1).trans
      (by norm_num)
  generalize hB : bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε = B
    at hB0 hL hspace hPB ⊢
  generalize hQ : qOf q.s q.T q.etaH q.etaD q.g q.ε = Q at hQ1 hQg hQz hPB ⊢
  have hY3 : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hQY : 1 ≤ Q * (B + 1) ^ 3 := one_le_mul_of_one_le_of_one_le hQ1 hY3
  have hG0 : (0 : ℝ) ≤ (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) := by positivity
  have hNb : (((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) : ℝ)) ≤
      2 * 10 ^ 18 * Q * (B + 1) ^ 3 + ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) := by
    push_cast
    nlinarith
  refine ⟨hPB, hexp.trans ?_, ?_, ?_, ?_, ?_, fun c => ?_, ?_, hQz, hN, hexp, hno, ?_⟩
  · -- the released form
    have hlog0 : 0 ≤ Real.log ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true) + 1) :=
      Real.log_nonneg (by linarith)
    have hn : (((Fintype.card
        (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
        Fintype.card Xa : ℕ) : ℝ)) ≤
        3 * 10 ^ 11 * (B + 1) ^ 3 + 2 * Fintype.card Zs + Fintype.card Xa := by
      push_cast
      linarith
    exact trial_budget_le (W := _) (a₁ := 40) (a₂ := 20) (by norm_num) (by norm_num) hg0 hc₀ hc₁
      (Nat.cast_nonneg _) hNb hL0 hL hn le_rfl
  · -- the qubits
    rw [hcardS']
    push_cast
    linarith
  · rw [hp]
    exact hTr
  · rw [hN]
    exact hNP
  · -- the synthesised count in the preparation bound
    have hnT : (((Fintype.card
        (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
        Fintype.card Xa : ℕ) : ℝ)) ≤ ((22 * q.kx + 12 * q.params.m + 24 * q.params.r +
        4 * q.params.k + 4 * q.params.l + 8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) +
        2 * Fintype.card Zs + Fintype.card Xa + 47 : ℕ) : ℝ) := by
      rw [hcardEq]
      push_cast
      linarith
    exact trial_count_le (by norm_num) (by norm_num) hg0 hc₀ hc₁ (Nat.cast_nonneg _) hNP hν hν1
      hnT hexp
  · rw [hp]
    have h := hWC c
    push_cast at h
    exact h
  · rw [hcardS', hcardEq]
    omega
  · intro x hrH hrD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hBud
    have ht := ZeroTimeGateODE.binary_target_zero q hq hz D en x hrH hrD x0 v
    rw [ht] at hne hBud ⊢
    have hnu : q.params.nu = ImprovedODEQueryBudget.precision q.g q.ε := rfl
    rw [hnu] at hbud
    rw [hp]
    exact hout (prims (R := ℂ) D en x) Jsrc x0 v ζs (prims_isUnitary D en x) hJ hζs hsrc hbud
      hx0 hv hpx hpv hne hBud

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` over a finite gate set, with
the per-trial claim, from binary sparse data for every `T ≥ 0`, constant coefficients**
(Theorem `ode:thm:gates`, equation `ode:eq:gate-word-budget`, with its remark on zero time and a
known zero generator).

Under the synthesis hypotheses of `GateBitBudget.binary_ode_budget_trials_bits`, for binary
public data with `BPublicOK0 q` (every `T ≥ 0`), the rescaling `γ` of bit length `b_data` in the
zero case `BZeroCase q` and the public rescaling `γ = gammaOf T η_H η_D g ε` otherwise, and the
remaining hypotheses of the released theorem, with `𝔟 = bitB b_data (2^k_x) (2^m) (2^k) q* g ε`
and `B = GateODEBudget.prepBound q srcC`, the protocol
`nprotocol (synthPrep hS (ν/3) (bprepC q srcC)) g` on the released trial register has every
conclusion of `GateBitBudget.binary_ode_budget_trials_bits`, in its order:
`B ≤ 2·10¹⁸ q* (𝔟+1)³ + G_src`; in every history at most
`40 g (2·10¹⁸ q* (𝔟+1)³ + G_src) (c₁ (64 (𝔟+1) + log(G_src+1)) + c₀) +
20 g (4 (3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢`; at most
`7·10¹¹ (𝔟+1)³ + 4 |Zs| + 2 |Xa|` qubits; every trial consists of valid gates of `𝒢` and
primitive calls; one preparation has at most `B` gates; at most
`40 g B (c₁ log((B+1)/(ν/3)) + c₀) + 20 g (4 n' + 3)` gates (`n'` as in
`binary_ode_budget_trials_bits_zero_released`); every history makes at most
`(if BZeroCase q then 0 else 3932160 g q* ([row] + [col] + [value])) +
40 g (calls_c(srcC 0) + calls_c(srcC 1))` calls of every kind `c`;
`|SNW| = 44 k_x + 24 m + 48 r + 8 k + 8 l + 16 b + 4 (bT + bP + A_arith) + 4 |Zs| + 2 |Xa| + 95`;
and for every input with the released energy and accretivity promises and the released source
hypotheses (`98304 q* ζ + 2 ζs ≤ ν`), the protocol has the guarantees `NOutcome` against `x(T)`. -/
theorem binary_ode_budget_trials_bits_nonneg (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (bd : ℕ) (q : Pub) (hq : BPublicOK0 q)
    (hγ : if BZeroCase q then HasBits bd q.γ else q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ) (hb : q.b ≤ bd)
    (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    prepBound q srcC ≤ 2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD q.g q.ε *
        (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
      ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * q.g * ((2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
            (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
          ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true))) *
        (c₁ * (64 * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
            (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) +
          Real.log ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true) + 1)) + c₀)) +
      20 * q.g * (4 * (3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 + 2 * Fintype.card Zs +
        Fintype.card Xa) + 3) ∧
    (Fintype.card (SNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) : ℝ) ≤
      7 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 + 4 * Fintype.card Zs +
        2 * Fintype.card Xa ∧
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) j →
        GateOf 𝒢 g) ∧
    (nGatesN (bprepC q srcC) : ℝ) ≤ prepBound q srcC ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * q.g * (prepBound q srcC *
        (c₁ * Real.log ((prepBound q srcC + 1) / (q.params.nu / 3)) + c₀)) +
      20 * q.g * (4 * ((22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k +
        4 * q.params.l + 8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs +
        Fintype.card Xa + 47 : ℕ) : ℝ) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g hq.g_ge).worstCost
        (wCallN c) : ℝ) ≤
      (if BZeroCase q then 0 else 3932160 * q.g * qOf q.s q.T q.etaH q.etaD q.g q.ε *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0))) +
        40 * q.g * ((nCallsN c (srcC false) : ℝ) + nCallsN c (srcC true))) ∧
    Fintype.card (SNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) =
      44 * q.kx + 24 * q.params.m + 48 * q.params.r + 8 * q.params.k + 8 * q.params.l +
        16 * q.b + 4 * (q.ar.bT + q.ar.bP + q.ar.A) + 4 * Fintype.card Zs +
        2 * Fintype.card Xa + 95 ∧
    ∀ x : X,
      (∀ i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re) →
      ∀ (Jsrc : Bool → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (x0 v : Reg (Fin q.kx) ℂ)
        (ζs : ℝ),
      (∀ c, IsUnitary (Jsrc c)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun (prims (R := ℂ) D en x) (srcC c))
        (liftB (srcIdeal c (Jsrc c))) ζs) →
      98304 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ + 2 * ζs ≤ q.params.nu →
      ‖x0‖ = q.r₀ → ‖v‖ = q.rb →
      (x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = unitDirection x0) →
      (v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = unitDirection v) →
      ODEConstantForcing.solution (-mLift D en x) x0 v q.T ≠ 0 →
      q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en x) x0 v q.T‖ →
      NOutcome (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g q.ε hq.g_ge
        (prims (R := ℂ) D en x) (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  have hV := (ZeroTimeGateODE.binary_ode_solver_nonneg_trials hS hadj hzt q hq D en hrange hdec
    srcC hsrcV).1
  by_cases hz : BZeroCase q
  · rw [if_pos hz] at hγ
    obtain ⟨hPB, hWg, hWc, -, hNle, hcnt, hWC, hcard, -, -, -, -, hout⟩ :=
      binary_ode_budget_trials_bits_zero_released hS hadj hzt hc₀ hc₁ hlen bd q hq hz hγ hζ hb
        hc0 hH hD D en srcC hsrcV (2 ^ q.params.m) (2 ^ q.params.k)
    refine ⟨hPB, hWg, hWc, hV, hNle, hcnt, fun c => ?_, hcard, ?_⟩
    · rw [if_pos hz, zero_add]
      exact hWC c
    · intro x hrH _ hrD _ _ Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hB
      have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
      have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε :=
        one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
      have h0 : 0 ≤ 98304 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ :=
        mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hq.ζ_pos.le
      exact hout x hrH hrD Jsrc x0 v ζs hJ hζs hsrc (by linarith) hx0 hv hpx hpv hne hB
  · rw [if_neg hz] at hγ
    have hP := ZeroTimeGateODE.bpublicOK_of hq hz
    obtain ⟨hPB, hWg, hWc, -, hNle, hcnt, hWC, hcard, hout⟩ :=
      GateBitBudget.binary_ode_budget_trials_bits hS hadj hzt hc₀ hc₁ hlen bd q hP hγ hζ hb hc0
        hT hH hD D en hrange hdec srcC hsrcV
    have hp : bprepC q srcC = q.prep srcC := by
      rw [bprepC, if_neg hz]
    refine ⟨hPB, ?_, hWc, hV, ?_, ?_, fun c => ?_, hcard, ?_⟩
    · rw [hp]
      exact hWg
    · rw [hp]
      exact hNle
    · rw [hp]
      exact hcnt
    · rw [hp, if_neg hz]
      exact hWC c
    · rw [hp]
      exact hout

end

end SparseHamiltonian.GateRemarks.ODE
