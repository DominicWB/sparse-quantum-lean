import GateEfficientRemarks.ODE.ZeroReleasedTime
import GateEfficientRemarks.ODE.ZeroReleasedTrials

/-!
# Zero time or a known zero generator over a finite gate set: the time-dependent budgets in `𝔟`
on the released trial register

The time-dependent counterpart of `ZeroReleasedTrials` (Theorem `ode:thm:gates`, time-dependent
part, equations `ode:eq:gate-main`, `ode:eq:gate-space`, `ode:eq:gate-word-budget`): only the
preparation is synthesised (`GateSynthTrials.synthPrep hS (ν/3)`), as in the released
`GateBitBudget.binary_ode_time_budget_trials_bits` and in the released every-`T ≥ 0` form
`ZeroTimeGateODE.binary_ode_time_solver_nonneg_trials`, on the released trial register
`GateSynthTrials.STW`:

* `prepBoundT_le_zero`, `zero_gates_le_prepBoundT` (zero case): the released native preparation
  bound `B = GateODEBudget.prepBoundT q loadC wpC` satisfies `B ≤ 2·10¹⁸ q*' (𝔟'+1)³ + G_src` (the
  bound of `GateBitBudget.prepBoundT_le`; `q*' = qOf s T η_H η_D (2g) (ε/2)`,
  `𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε`, `G_src = |loadC| + 2 |wpC|`), and the direct
  source assembly has `G_src ≤ B` gates;
* `binary_ode_time_budget_trials_bits_zero_released` (zero case `BTZeroCase`, `γ` of bit length
  `b_data`): every bound of `GateBitBudget.binary_ode_time_budget_trials_bits`, in its order, for
  the protocol `nprotocol (synthPrep hS (ν/3) (btprepC q loadC wpC)) (2g)`:
  `B ≤ 2·10¹⁸ q*' (𝔟'+1)³ + G_src`; at most
  `80 g (2·10¹⁸ q*' (𝔟'+1)³ + G_src) (c₁ (64 (𝔟'+1) + log(G_src+1)) + c₀) +
  40 g (4 (3·10¹¹ (𝔟'+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢` on at most
  `7·10¹¹ (𝔟'+1)³ + 4 |Zs| + 2 |Xa|` qubits; valid trials of `𝒢`; one preparation within `B`
  gates; the synthesised count `80 g B (c₁ log((B+1)/(ν/3)) + c₀) + 40 g (4 n' + 3)`,
  `n' = 22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (bT + bP + A) + 2 |Zs| + |Xa| + 47`; at most `80 g`
  times the calls of `loadC` and twice those of `wpC` (no matrix call); and the register identity
  `|STW| = 44 k_x + 32 m + 48 r + 8 l + 16 b + 4 (bT + bP + A) + 4 |Zs| + 2 |Xa| + 95`; further
  `q*' = ℓ'`, the `N = G_src` gates of one preparation, the sharper count
  `80 g N (c₁ log((N+1)/(ν/3)) + c₀) + 40 g (4 (n + |Xa|) + 3)` (`n` the qubits of the released
  register), no call of a kind that the supplied circuits do not call, and `NOutcome` under the
  zero-case conditions;
* `binary_ode_time_budget_trials_bits_nonneg` (every `T ≥ 0`): every conclusion of the released
  `GateBitBudget.binary_ode_time_budget_trials_bits`, in its order, for the protocol
  `nprotocol (synthPrep hS (ν/3) (btprepC q loadC wpC)) (2g)` (the calls with the matrix part
  `if BTZeroCase q then 0 else 7864320 g q*' (…)`, `NOutcome` under the released hypotheses), with
  `γ` of bit length `b_data` in the zero case and the public rescaling otherwise.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateBinary GateSynth GateSynthTrials
open ZeroTimeGateODE (tzprepC btprepC BTPublicOK0 BTZeroCase)
open GateBinaryODE (SZ4 card_SZ4)
open GateBinaryODETime (PubT HsT LsT)
open SparseHamiltonian.GateBitBudget (bitB bitB_nonneg HasBits)
open GateODEBudget (qOf wordsT gammaOf prepBoundT)
open ImprovedODEQueryBudget (logBudget)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct BigOperators

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **The released time-dependent trial register**: the wires tested by the zero tests of the
trial register of the released time-dependent binary register are its `n` qubits plus the `|Xa|`
synthesis ancillas, and the trial register has `2 n + 2 |Xa| + 1` qubits. -/
theorem card_trialT_released (q : PubT) (Zs Xa : Type*) [Fintype Zs] [DecidableEq Zs]
    [Fintype Xa] [DecidableEq Xa] :
    Fintype.card (GateODE.AW q.params.a q.params.m q.params.r q.params.K q.params.m q.params.l
      q.params.f) + Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
      Fintype.card (SX Zs (ZeroTimeGateODE.zPool q.params.a q.params.m q.params.r q.params.K
        q.params.m q.params.l q.params.f (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
        Xa) + Fintype.card (Fin q.kx) =
      Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
        Fintype.card Xa ∧
    Fintype.card (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) =
      2 * Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
        2 * Fintype.card Xa + 1 := by
  have hNW := (ZeroTimeGateODE.card_ZNW (S := Fin q.kx) (Zs := Zs) (Z := SZ4 q.kx q.b)
    q.params.a q.params.m q.params.r q.params.K q.params.m q.params.l q.params.f q.ar.bT q.ar.bP
    q.ar.A : Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) = _)
  have hSTW := (GateSynthTrials.card_SWO : Fintype.card
    (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) = _)
  have hnP : tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A =
      ZeroTimeGateODE.zPool q.params.a q.params.m q.params.r q.params.K q.params.m q.params.l
        q.params.f (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A := rfl
  rw [hnP] at hSTW
  rw [card_SZ4, Fintype.card_fin] at hNW hSTW
  have hXW : Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3 := by
    simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin]
    ring
  have hSX : Fintype.card (SX Zs (ZeroTimeGateODE.zPool q.params.a q.params.m q.params.r
      q.params.K q.params.m q.params.l q.params.f (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
      q.ar.A) Xa) = Fintype.card Zs + 1 + ZeroTimeGateODE.zPool q.params.a q.params.m q.params.r
      q.params.K q.params.m q.params.l q.params.f (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
      q.ar.A + Fintype.card Xa := by
    simp only [SX, OX, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
    ring
  have hzP : ZeroTimeGateODE.zPool q.params.a q.params.m q.params.r q.params.K q.params.m
      q.params.l q.params.f (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A =
      Fintype.card (GateODE.AW q.params.a q.params.m q.params.r q.params.K q.params.m q.params.l
        q.params.f) + Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
        Fintype.card Zs + q.kx := by
    show _ + _ + _ + Fintype.card (Fin q.kx) = _
    rw [Fintype.card_fin]
  constructor
  · rw [hSX, hzP, hNW, Fintype.card_fin, hXW]
    omega
  · rw [hSTW, hNW, hzP, hXW]
    omega

/-- **The preparation bound in `𝔟` in the zero case**, time-dependent coefficients (equation
`ode:eq:gate-main` over a finite gate set, in the word budget `ode:eq:gate-word-budget`): for
time-indexed binary public data with `BTPublicOK0 q` in the zero case, a rescaling `γ` of bit length
`b_data`, an arithmetic accuracy `ζ ≥ ν/(196608 q*')`, stored bits `b ≤ b_data` and `c₀`, `η_H`,
`η_D` of bit length `b_data`, the released native preparation bound
`B = GateODEBudget.prepBoundT q loadC wpC` satisfies `B ≤ 2·10¹⁸ q*' (𝔟'+1)³ + G_src`,
`q*' = qOf s T η_H η_D (2g) (ε/2)`, `𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε`: the bound of
`GateBitBudget.prepBoundT_le`, from the word budget `zero_wordsT_le`. -/
theorem prepBoundT_le_zero (bd : ℕ) (q : PubT) (hq : BTPublicOK0 q) (hz : BTZeroCase q)
    (hγb : HasBits bd q.γ)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hH : HasBits bd q.etaH) (hD : HasBits bd q.etaD)
    {Zs : Type*}
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    prepBoundT q loadC wpC ≤ 2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
      ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) := by
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hg2 : (1 : ℝ) ≤ 2 * q.g := by linarith [hq.g_ge]
  have hε2 : (0 : ℝ) < q.ε / 2 := by linarith [hq.ε_pos]
  have hε2' : q.ε / 2 ≤ 1 := by linarith [hq.ε_half]
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hg2 hε2 hε2'
  have hℓ := ImprovedODEQueryBudget.logBudget_ge_one (2 * q.g) (q.ε / 2) hg2 hε2 hε2'
  have hw := zero_wordsT_le bd q hq hz hγb hζ hb hc0 hH hD
  obtain ⟨hGC, -, -, -⟩ := GateODEBudget.binary_time_arith_words q
  have hσ := q.hσ
  have hQg : 0 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.g := by positivity
  have hB0 := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) hQg hq.ε_pos hε1
  have hwd0 : (0 : ℝ) ≤ wordsT q := Nat.cast_nonneg _
  have hGC' : (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) :
      ℕ) : ℝ)) ≤ 65536 * ((wordsT q : ℝ) + 1) ^ 3 := by exact_mod_cast hGC
  have hS : (q.kx : ℝ) + q.σ + q.params.m + q.params.r ≤ 2 * (wordsT q : ℝ) := by
    have : q.kx + q.σ + q.params.m + q.params.r ≤ 2 * wordsT q := by
      unfold wordsT
      omega
    exact_mod_cast this
  have hl : (q.params.l : ℝ) ≤ wordsT q := by
    have : q.params.l ≤ wordsT q := by
      unfold wordsT
      omega
    exact_mod_cast this
  have hin := GateBitBudget.inner_le hwd0 hℓ hGC' hS (Nat.cast_nonneg _) hl
  have hcube := GateBitBudget.cube_le (by linarith) hB0 hw
  unfold GateODEBudget.prepBoundT
  have h1 : (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) : ℕ) :
      ℝ) + q.kx + q.σ + q.params.m + q.params.r +
      logBudget (2 * q.g) (q.ε / 2) * ((q.params.l : ℝ) + 1) + 8) ≤
      65547 * ((300 + 1) ^ 3 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3) := by
    linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 819400 *
    qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
  have hY2 : 0 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
      (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 := by positivity
  linarith

/-- **The direct source assembly within the released preparation bound**, time-dependent
coefficients: for time-indexed binary public data with `BTPublicOK0 q` (every `T ≥ 0`),
`G_src = |loadC| + 2 |wpC|` is at most the released native preparation bound
`B = GateODEBudget.prepBoundT q loadC wpC = 819400 q*' (…) + G_src`. -/
theorem zero_gates_le_prepBoundT (q : PubT) (hq : BTPublicOK0 q) {Zs : Type*}
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query))
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query)) :
    ((nGatesN loadC + 2 * nGatesN wpC : ℕ) : ℝ) ≤ prepBoundT q loadC wpC := by
  have hg2 : (1 : ℝ) ≤ 2 * q.g := by linarith [hq.g_ge]
  have hε2 : (0 : ℝ) < q.ε / 2 := by linarith [hq.ε_pos]
  have hε2' : q.ε / 2 ≤ 1 := by linarith [hq.ε_half]
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hg2 hε2 hε2'
  have hℓ := ImprovedODEQueryBudget.logBudget_ge_one (2 * q.g) (q.ε / 2) hg2 hε2 hε2'
  unfold GateODEBudget.prepBoundT
  have hS : (0 : ℝ) ≤ (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
      (2 * q.ar.bP + q.ar.bT + 1) : ℕ) : ℝ) + q.kx + q.σ + q.params.m + q.params.r +
      logBudget (2 * q.g) (q.ε / 2) * ((q.params.l : ℝ) + 1) + 8) :=
    add_nonneg (add_nonneg (by positivity) (mul_nonneg (by linarith) (by positivity)))
      (by norm_num)
  have h1 := mul_nonneg (by positivity : (0 : ℝ) ≤ 819400 *
    qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) hS
  have e : ((nGatesN loadC + 2 * nGatesN wpC : ℕ) : ℝ) =
      (nGatesN loadC : ℝ) + 2 * nGatesN wpC := by
    push_cast
    ring
  rw [e]
  linarith

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` over a finite gate set, with
the per-trial claim, on the released time-dependent trial register, for zero time or a known zero
generator** (Theorem `ode:thm:gates`, time-dependent part, with its remark).

Under `Synthesis 𝒢 Xa len` with `len ζ ≤ c₁ log(1/ζ) + c₀` (`c₀, c₁ ≥ 0`), `AdjClosed 𝒢` and
`zeroTestKinds ⊆ 𝒢`, for time-indexed binary public data with `BTPublicOK0 q` in the zero case, a
rescaling `γ` of bit length `b_data`, an arithmetic accuracy `ζ ≥ ν/(196608 q*')`, stored bits
`b ≤ b_data`, `c₀`, `η_H`, `η_D` of bit length `b_data` and valid loading and weight-preparation
circuits, with `q*' = qOf s T η_H η_D (2g) (ε/2)` (`= ℓ'`),
`𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε`, `G_src = |loadC| + 2 |wpC|` and the released
preparation bound `B = GateODEBudget.prepBoundT q loadC wpC`, the protocol
`nprotocol (synthPrep hS (ν/3) (btprepC q loadC wpC)) (2g)` on the released trial register has
every bound of `GateBitBudget.binary_ode_time_budget_trials_bits`, in its order:
`B ≤ 2·10¹⁸ q*' (𝔟'+1)³ + G_src`; in every history at most
`80 g (2·10¹⁸ q*' (𝔟'+1)³ + G_src) (c₁ (64 (𝔟'+1) + log(G_src+1)) + c₀) +
40 g (4 (3·10¹¹ (𝔟'+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢`; at most
`7·10¹¹ (𝔟'+1)³ + 4 |Zs| + 2 |Xa|` qubits; every trial consists of valid gates of `𝒢` and
primitive calls; one preparation has at most `B` gates; at most
`80 g B (c₁ log((B+1)/(ν/3)) + c₀) + 40 g (4 n' + 3)` gates,
`n' = 22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + |Xa| + 47`; at most
`80 g (calls_c(loadC) + 2 calls_c(wpC))` calls of every kind `c` (no matrix call); and
`|STW| = 44 k_x + 32 m + 48 r + 8 l + 16 b + 4 (bT + bP + A_arith) + 4 |Zs| + 2 |Xa| + 95`.
Further `q*' = ℓ'`; one preparation has exactly `N = G_src` gates; at most
`80 g N (c₁ log((N+1)/(ν/3)) + c₀) + 40 g (4 (n + |Xa|) + 3)` gates, `n` the qubits of the
released register; every history makes no call of a kind that the supplied circuits do not call;
and for every input with the energy and accretivity promises of every sample, circuits within
`ζs`, `3 ζs ≤ ν` and `PubT.Rest`, the protocol has the guarantees `NOutcome` against `x(T)`. -/
theorem binary_ode_time_budget_trials_bits_zero_released (hS : Synthesis 𝒢 Xa len)
    (hadj : AdjClosed 𝒢) (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (bd : ℕ) (q : PubT) (hq : BTPublicOK0 q) (hz : BTZeroCase q) (hγb : HasBits bd q.γ)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hH : HasBits bd q.etaH) (hD : HasBits bd q.etaD)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    prepBoundT q loadC wpC ≤ 2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
      ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * ((2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
          ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)) *
        (c₁ * (64 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) +
          Real.log ((nGatesN loadC : ℝ) + 2 * nGatesN wpC + 1)) + c₀)) +
      40 * q.g * (4 * (3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        2 * Fintype.card Zs + Fintype.card Xa) + 3) ∧
    (Fintype.card (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) : ℝ) ≤
      7 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        4 * Fintype.card Zs + 2 * Fintype.card Xa ∧
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) j, i.Valid) ∧
      ∀ gt, NInstr.gate gt ∈ trialN (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) j →
        GateOf 𝒢 gt) ∧
    (nGatesN (btprepC q loadC wpC) : ℝ) ≤ prepBoundT q loadC wpC ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * (prepBoundT q loadC wpC *
        (c₁ * Real.log ((prepBoundT q loadC wpC + 1) / (q.params.nu / 3)) + c₀)) +
      40 * q.g * (4 * ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l +
        8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs +
        Fintype.card Xa + 47 : ℕ) : ℝ) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    Fintype.card (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) =
      44 * q.kx + 32 * q.params.m + 48 * q.params.r + 8 * q.params.l + 16 * q.b +
        4 * (q.ar.bT + q.ar.bP + q.ar.A) + 4 * Fintype.card Zs + 2 * Fintype.card Xa + 95 ∧
    qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) = logBudget (2 * q.g) (q.ε / 2) ∧
    nGatesN (btprepC q loadC wpC) = nGatesN loadC + 2 * nGatesN wpC ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * ((nGatesN loadC + 2 * nGatesN wpC : ℕ) *
        (c₁ * Real.log (((nGatesN loadC + 2 * nGatesN wpC : ℕ) + 1) / (q.params.nu / 3)) + c₀)) +
        40 * q.g * (4 * ((Fintype.card
          (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card Xa : ℕ) : ℝ) + 3) ∧
    (∀ c : Query → Bool, nCallsN c loadC = 0 → nCallsN c wpC = 0 →
      (nprotocol (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) = 0) ∧
    ∀ x : X,
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
        (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf xs : ℝ → Reg (Fin q.kx) ℂ)
        (bs : ℕ → Reg (Fin q.kx) ℂ) (βG δG βb δb bmax ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) wpC) (liftB (matOp Wp)) ζs →
      3 * ζs ≤ q.params.nu →
      q.Rest D en x Jl Wp G bf xs bs βG δG βb δb bmax →
      NOutcome (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (xs q.T) := by
  have hp := ZeroTimeGateODE.btparams_ok0 hq
  obtain ⟨hTr, -, -, hWC, -, hWGlog, -, hout⟩ :=
    ZeroTimeGateODE.native_ode_time_solver_zero_trials (S := Fin q.kx) (Zs := Zs)
      (Z := SZ4 q.kx q.b) (Y := Fin q.m ⊕ PY q.kx q.b) (J := Query) hS hadj hzt q.params
      q.params.a q.params.m q.params.r q.params.K q.params.l q.params.f q.ar.bT q.ar.bP q.ar.A
      hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hp.lamH_nonneg hp.lamD_nonneg
      (ZeroTimeGateODE.btzeroCase_params hq hz) loadC hloadV wpC hwpV
  obtain ⟨-, hG, -, -, -, -, -, -⟩ := ZeroTimeGateODE.native_ode_time_solver_zero
    (S := Fin q.kx) (Zs := Zs) (Z := SZ4 q.kx q.b) (Y := Fin q.m ⊕ PY q.kx q.b) (J := Query)
    q.params q.params.a q.params.m q.params.r q.params.K q.params.l q.params.f q.ar.bT q.ar.bP
    q.ar.A hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hp.lamH_nonneg hp.lamD_nonneg
    (ZeroTimeGateODE.btzeroCase_params hq hz) loadC hloadV wpC hwpV
  obtain ⟨-, hspace, -, -, -, -, -, -, -, -, hQz, -, -, -⟩ :=
    binary_ode_time_budget_bits_zero_released bd q hq hz hγb hζ hb hc0 hH hD D en loadC hloadV
      wpC hwpV
  obtain ⟨htest, hcardS'⟩ := card_trialT_released q Zs Xa
  have hPB := prepBoundT_le_zero bd q hq hz hγb hζ hb hc0 hH hD loadC wpC
  have hNP := zero_gates_le_prepBoundT q hq loadC wpC
  have hcardEq := card_TNW_eq q (Zs := Zs)
  have hpr : btprepC q loadC wpC = tzprepC loadC wpC := by
    rw [btprepC, if_pos hz]
  have hN : nGatesN (btprepC q loadC wpC) = nGatesN loadC + 2 * nGatesN wpC := by
    rw [hpr]
    exact hG
  have hr : q.params.ratio = 2 * q.g := rfl
  have htest' : ((Fintype.card (GateODE.AW q.params.a q.params.m q.params.r q.params.K
      q.params.m q.params.l q.params.f) : ℕ) : ℝ) +
      (Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℕ) +
      (Fintype.card (SX Zs (ZeroTimeGateODE.zPool q.params.a q.params.m q.params.r q.params.K
        q.params.m q.params.l q.params.f (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
        Xa) : ℕ) + (Fintype.card (Fin q.kx) : ℕ) =
      ((Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
        Fintype.card Xa : ℕ) : ℝ) := by
    exact_mod_cast htest
  -- the explicit count
  have hexp : ((nprotocol (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * ((nGatesN loadC + 2 * nGatesN wpC : ℕ) *
        (c₁ * Real.log (((nGatesN loadC + 2 * nGatesN wpC : ℕ) + 1) / (q.params.nu / 3)) + c₀)) +
        40 * q.g * (4 * ((Fintype.card
          (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card Xa : ℕ) : ℝ) + 3) := by
    rw [hpr]
    have h := hWGlog c₀ c₁ hc₀ hc₁ hlen
    rw [htest'] at h
    refine h.trans (le_of_eq ?_)
    rw [hr]
    ring
  have hno : ∀ c : Query → Bool, nCallsN c loadC = 0 → nCallsN c wpC = 0 →
      (nprotocol (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) = 0 := by
    intro c h0 h1
    rw [hpr]
    have h := hWC c
    rw [h0, h1] at h
    have h' : ((nprotocol (synthPrep hS (q.params.nu / 3) (tzprepC loadC wpC :
        List (NInstr (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
          (Fin q.m ⊕ PY q.kx q.b) Query))) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤ 0 := by
      simpa using h
    exact_mod_cast le_antisymm h' (Nat.cast_nonneg _)
  -- the word budget
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg (by linarith [hq.g_ge])
      (by linarith [hq.ε_pos]) (by linarith)
  have hQg : 0 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.g := by positivity
  have hB0 := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) hQg hq.ε_pos hε1
  have hL : Real.log ((((nGatesN loadC + 2 * nGatesN wpC : ℕ) : ℝ) + 1) / (q.params.nu / 3)) ≤
      64 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) +
        Real.log ((nGatesN loadC : ℝ) + 2 * nGatesN wpC + 1) :=
    log_trialT_le (g := q.g) (ε := q.ε) bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) (by positivity)
      (by push_cast; ring) hq.g_ge hq.ε_pos hε1 hQ1
  have hL0 : 0 ≤ Real.log ((((nGatesN loadC + 2 * nGatesN wpC : ℕ) : ℝ) + 1) /
      (q.params.nu / 3)) := by
    apply Real.log_nonneg
    have hν : 0 < q.params.nu := q.params.nu_pos hq.g_ge hq.ε_pos
    rw [le_div_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ ((nGatesN loadC + 2 * nGatesN wpC : ℕ) : ℝ) := Nat.cast_nonneg _
    have hν1 : q.params.nu ≤ 1 := q.params.nu_le_one hq.g_ge hε1
    linarith
  have hν : 0 < q.params.nu := q.params.nu_pos hq.g_ge hq.ε_pos
  have hν1 : q.params.nu ≤ 1 := q.params.nu_le_one hq.g_ge hε1
  generalize hB : bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
    (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε = B at hB0 hL hspace hPB ⊢
  generalize hQ : qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) = Q at hQ1 hQg hQz hPB ⊢
  have hY3 : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hQY : 1 ≤ Q * (B + 1) ^ 3 := one_le_mul_of_one_le_of_one_le hQ1 hY3
  have hG0 : (0 : ℝ) ≤ (nGatesN loadC : ℝ) + 2 * nGatesN wpC := by positivity
  have hNb : (((nGatesN loadC + 2 * nGatesN wpC : ℕ) : ℝ)) ≤
      2 * 10 ^ 18 * Q * (B + 1) ^ 3 + ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) := by
    push_cast
    nlinarith
  refine ⟨hPB, hexp.trans ?_, ?_, ?_, ?_, ?_, fun c => ?_, ?_, hQz, hN, hexp, hno, ?_⟩
  · -- the released form
    have hlog0 : 0 ≤ Real.log ((nGatesN loadC : ℝ) + 2 * nGatesN wpC + 1) :=
      Real.log_nonneg (by linarith)
    have hn : (((Fintype.card
        (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
        Fintype.card Xa : ℕ) : ℝ)) ≤
        3 * 10 ^ 11 * (B + 1) ^ 3 + 2 * Fintype.card Zs + Fintype.card Xa := by
      push_cast
      linarith
    exact trial_budget_le (W := _) (a₁ := 80) (a₂ := 40) (by norm_num) (by norm_num) hg0 hc₀ hc₁
      (Nat.cast_nonneg _) hNb hL0 hL hn le_rfl
  · -- the qubits
    rw [hcardS']
    push_cast
    linarith
  · rw [hpr]
    exact hTr
  · rw [hN]
    exact hNP
  · -- the synthesised count in the preparation bound
    have hnT : (((Fintype.card
        (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
        Fintype.card Xa : ℕ) : ℝ)) ≤ ((22 * q.kx + 16 * q.params.m + 24 * q.params.r +
        4 * q.params.l + 8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs +
        Fintype.card Xa + 47 : ℕ) : ℝ) := by
      rw [hcardEq]
      push_cast
      linarith
    exact trial_count_le (by norm_num) (by norm_num) hg0 hc₀ hc₁ (Nat.cast_nonneg _) hNP hν hν1
      hnT hexp
  · rw [hpr]
    refine (hWC c).trans (le_of_eq ?_)
    rw [hr]
    push_cast
    ring
  · rw [hcardS', hcardEq]
    omega
  · intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
    have hI := ZeroTimeGateODE.binary_tzInstanceOK q hq D en x hrH hcH hrD hcD hPSD Jl Wp G bf
      xs bs βG δG βb δb bmax hR
    rw [hpr]
    exact hout (primsT (R := ℂ) D en x) Jl Wp (HsT D en x) (LsT D en x) G bf xs bs βG δG βb δb
      bmax ζs (primsT_isUnitary D en x) hζs hload hwp hbud hI

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` over a finite gate set, with
the per-trial claim, from time-indexed binary sparse data for every `T ≥ 0`** (Theorem
`ode:thm:gates`, time-dependent part, equation `ode:eq:gate-word-budget`, with its remark on zero
time and a known zero generator).

Under the synthesis hypotheses of `GateBitBudget.binary_ode_time_budget_trials_bits`, for
time-indexed binary public data with `BTPublicOK0 q` (every `T ≥ 0`), the rescaling `γ` of bit
length `b_data` in the zero case `BTZeroCase q` and the public rescaling
`γ = gammaOf T η_H η_D (2g) (ε/2)` otherwise, and the remaining hypotheses of the released
endpoint, with `q*' = qOf s T η_H η_D (2g) (ε/2)`, `𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε`
and `B = GateODEBudget.prepBoundT q loadC wpC`, the protocol
`nprotocol (synthPrep hS (ν/3) (btprepC q loadC wpC)) (2g)` on the released trial register has
every conclusion of `GateBitBudget.binary_ode_time_budget_trials_bits`, in its order:
`B ≤ 2·10¹⁸ q*' (𝔟'+1)³ + G_src`; in every history at most
`80 g (2·10¹⁸ q*' (𝔟'+1)³ + G_src) (c₁ (64 (𝔟'+1) + log(G_src+1)) + c₀) +
40 g (4 (3·10¹¹ (𝔟'+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢`; at most
`7·10¹¹ (𝔟'+1)³ + 4 |Zs| + 2 |Xa|` qubits; every trial consists of valid gates of `𝒢` and
primitive calls; one preparation has at most `B` gates; at most
`80 g B (c₁ log((B+1)/(ν/3)) + c₀) + 40 g (4 n' + 3)` gates (`n'` as in
`binary_ode_time_budget_trials_bits_zero_released`); every history makes at most
`(if BTZeroCase q then 0 else 7864320 g q*' ([row] + [col] + [value])) +
80 g (calls_c(loadC) + 2 calls_c(wpC))` calls of every kind `c`;
`|STW| = 44 k_x + 32 m + 48 r + 8 l + 16 b + 4 (bT + bP + A_arith) + 4 |Zs| + 2 |Xa| + 95`; and
for every input with the released energy and accretivity promises of every sample, circuits
within `ζs` with `98304 q*' ζ + 3 ζs ≤ ν` and the released remaining conditions `PubT.Rest`, the
protocol has the guarantees `NOutcome` against `x(T)`. -/
theorem binary_ode_time_budget_trials_bits_nonneg (hS : Synthesis 𝒢 Xa len)
    (hadj : AdjClosed 𝒢) (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (bd : ℕ) (q : PubT) (hq : BTPublicOK0 q)
    (hγ : if BTZeroCase q then HasBits bd q.γ
      else q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    prepBoundT q loadC wpC ≤ 2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
      ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * ((2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
          ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)) *
        (c₁ * (64 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) +
          Real.log ((nGatesN loadC : ℝ) + 2 * nGatesN wpC + 1)) + c₀)) +
      40 * q.g * (4 * (3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        2 * Fintype.card Zs + Fintype.card Xa) + 3) ∧
    (Fintype.card (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) : ℝ) ≤
      7 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        4 * Fintype.card Zs + 2 * Fintype.card Xa ∧
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) j →
        GateOf 𝒢 g) ∧
    (nGatesN (btprepC q loadC wpC) : ℝ) ≤ prepBoundT q loadC wpC ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * (prepBoundT q loadC wpC *
        (c₁ * Real.log ((prepBoundT q loadC wpC + 1) / (q.params.nu / 3)) + c₀)) +
      40 * q.g * (4 * ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l +
        8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs +
        Fintype.card Xa + 47 : ℕ) : ℝ) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      (if BTZeroCase q then 0 else 7864320 * q.g *
          qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0))) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    Fintype.card (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) =
      44 * q.kx + 32 * q.params.m + 48 * q.params.r + 8 * q.params.l + 16 * q.b +
        4 * (q.ar.bT + q.ar.bP + q.ar.A) + 4 * Fintype.card Zs + 2 * Fintype.card Xa + 95 ∧
    ∀ x : X,
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaH ^ 2) →
      (∀ r i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix (x, r)) i j‖ ^ 2 ≤ q.etaD ^ 2) →
      (∀ r, ∀ w : EuclideanSpace ℂ n, 0 ≤ (inner ℂ w (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D.matrix (x, r))) w)).re) →
      ∀ (Jl : Bool × (Fin q.m → Bool) → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ)
        (Wp : Matrix (Cfg (Fin (q.m + 1))) (Cfg (Fin (q.m + 1))) ℂ)
        (G : ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf xs : ℝ → Reg (Fin q.kx) ℂ)
        (bs : ℕ → Reg (Fin q.kx) ℂ) (βG δG βb δb bmax ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) wpC) (liftB (matOp Wp)) ζs →
      98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ + 3 * ζs ≤ q.params.nu →
      q.Rest D en x Jl Wp G bf xs bs βG δG βb δb bmax →
      NOutcome (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (xs q.T) := by
  have hV := (ZeroTimeGateODE.binary_ode_time_solver_nonneg_trials hS hadj hzt q hq D en hrange
    hdec loadC hloadV wpC hwpV).1
  by_cases hz : BTZeroCase q
  · rw [if_pos hz] at hγ
    obtain ⟨hPB, hWg, hWc, -, hNle, hcnt, hWC, hcard, -, -, -, -, hout⟩ :=
      binary_ode_time_budget_trials_bits_zero_released hS hadj hzt hc₀ hc₁ hlen bd q hq hz hγ hζ
        hb hc0 hH hD D en loadC hloadV wpC hwpV
    refine ⟨hPB, hWg, hWc, hV, hNle, hcnt, fun c => ?_, hcard, ?_⟩
    · rw [if_pos hz, zero_add]
      exact hWC c
    · intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
      have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
        one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg (by linarith [hq.g_ge])
          (by linarith [hq.ε_pos]) (by linarith [hq.ε_half])
      have h0 : 0 ≤ 98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ :=
        mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hq.ζ_pos.le
      exact hout x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp
        (by linarith) hR
  · rw [if_neg hz] at hγ
    have hP := ZeroTimeGateODE.btpublicOK_of hq hz
    obtain ⟨hPB, hWg, hWc, -, hNle, hcnt, hWC, hcard, hout⟩ :=
      GateBitBudget.binary_ode_time_budget_trials_bits hS hadj hzt hc₀ hc₁ hlen bd q hP hγ hζ hb
        hc0 hT hH hD D en hrange hdec loadC hloadV wpC hwpV
    have hpr : btprepC q loadC wpC = q.prep loadC wpC := by
      rw [btprepC, if_neg hz]
    refine ⟨hPB, ?_, hWc, hV, ?_, ?_, fun c => ?_, hcard, ?_⟩
    · rw [hpr]
      exact hWg
    · rw [hpr]
      exact hNle
    · rw [hpr]
      exact hcnt
    · rw [hpr, if_neg hz]
      exact hWC c
    · rw [hpr]
      exact hout

end

end SparseHamiltonian.GateRemarks.ODE
