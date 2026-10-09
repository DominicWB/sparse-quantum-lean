import GateEfficientRemarks.ODE.ZeroWordsT

/-!
# Zero time or a known zero generator: the time-dependent budgets in `𝔟` on the released register

The time-dependent counterpart of `ZeroReleased`. The released library `GateEfficientBitBudget`
proves equations `ode:eq:gate-main` and `ode:eq:gate-space` in the word budget `𝔟` for the solver
from time-indexed binary data under the released public conditions (`T > 0`, `η_H + η_D > 0`,
the public rescaling `γ = gammaOf T η_H η_D (2g) (ε/2)`), and the released library
`ZeroTimeGateODE` gives, for every `T ≥ 0`, the combined preparation
`ZeroTimeGateODE.btprepC q loadC wpC` on the released register (the direct source assembly in the
zero case `BTZeroCase`). With `γ` of bit length `b_data` in the zero case, the released register
keeps every bound of the positive case with the same constants:

* `binary_ode_time_budget_count_zero` (zero case, no hypothesis on `γ`, `ζ` or the bit lengths):
  the explicit count `73746000 g [q*' (G_C + k_x + σ + m + r + ℓ' (l+1) + 8) + G_src + A]` of
  `GateODEBudget.binary_ode_time_budget` (`count_arithT` is its arithmetic);
* `binary_ode_time_budget_bits_zero_released` (zero case): the protocol
  `nprotocol (btprepC q loadC wpC) (2g)` on the released register has, in the order of
  `GateBitBudget.binary_ode_time_budget_bits`, at most `2·10²⁰ g [q*' (𝔟'+1)³ + G_src + |Zs|]`
  gates and `3·10¹¹ (𝔟'+1)³ + 2 |Zs|` qubits (`q*' = qOf s T η_H η_D (2g) (ε/2)`,
  `𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε`), the words `𝔴 + ℓ' ≤ 300 (𝔟'+1)`, the word
  forms `6·10¹² g [q*' (𝔴+ℓ'+1)³ + G_src + |Zs|]` and `10⁴ (𝔴+1)³ + 2 |Zs|`, the explicit count,
  at most `80 g` times the calls of `loadC` and twice those of `wpC` (no matrix call) and the
  register identity (`card_TNW_eq`); then both bounds of
  `GateBitBudget.binary_ode_time_budget_bits_user` (`2·10²² g [q* (𝔟+1)³ + G_src + |Zs|]` gates
  on `9·10¹² (𝔟+1)³ + 2 |Zs|` qubits, `q*`, `𝔟` of `(g, ε)`); and further `q*' = ℓ'`, valid
  trials, no call of a kind that the supplied circuits do not call, and `NOutcome` under the
  zero-case conditions;
* `binary_ode_time_budget_bits_nonneg` (every `T ≥ 0`): every conclusion of the released
  `GateBitBudget.binary_ode_time_budget_bits` (gates and qubits in `𝔟'`, words, word forms, the
  explicit count, the calls with the matrix part `if BTZeroCase q then 0 else 7864320 g q*' (…)`,
  the register identity and `NOutcome` under the released hypotheses), in the same order, for the
  protocol `nprotocol (btprepC q loadC wpC) (2g)`, with both bounds of
  `GateBitBudget.binary_ode_time_budget_bits_user` and the validity of the trials inserted before
  `NOutcome`, with `γ` of bit length `b_data` in the zero case and the public rescaling otherwise.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateBinary
open ZeroTimeGateODE (tzprepC btprepC BTPublicOK0 BTZeroCase)
open GateBinaryODE (SZ4 card_SZ4)
open GateBinaryODETime (PubT HsT LsT)
open SparseHamiltonian.GateBitBudget (bitB bitB_nonneg HasBits)
open GateODEBudget (qOf wordsT gammaOf)
open ImprovedODEQueryBudget (logBudget)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct BigOperators

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- **The arithmetic of the explicit count in the zero case, time-dependent coefficients**: the
gates `80 g G + 40 g (4 (|W| + |XW| + Z + k_x) + 3)` of the direct source assembly on the released
time-dependent register (ratio `2g`) are at most the released explicit count
`73746000 g [Q (G_C + k_x + σ + m + r + L (l+1) + 8) + G + (k_x + Z + (6 k_x + 4 b) + bT + bP +
A)]` for `Q, L ≥ 1` and nonnegative data (`G_C = 2 (28 k_x + 2) + 2 c + 2 bP + bT + 1`, `c` the
length of the arithmetic circuit). -/
theorem count_arithT {g Q L G Z kx σ m r l b bT bP A c : ℝ} (hg : 0 ≤ g) (hQ : 1 ≤ Q)
    (hL : 1 ≤ L) (hG : 0 ≤ G) (hZ : 0 ≤ Z) (hkx : 0 ≤ kx) (hσ : 0 ≤ σ) (hm : 0 ≤ m)
    (hr : 0 ≤ r) (hl : 0 ≤ l) (hb : 0 ≤ b) (hbT : 0 ≤ bT) (hbP : 0 ≤ bP) (hA : 0 ≤ A)
    (hc : 0 ≤ c) :
    40 * (2 * g) * G + 20 * (2 * g) * (4 * (4 * (kx + 3) + 8 * m + 12 * r + 2 * l + 8 +
      (6 * kx + 4 * b + bT + bP + A + 3) + Z + kx) + 3) ≤
    73746000 * g * (Q * (2 * (28 * kx + 2) + 2 * c + (2 * bP + bT + 1) + kx + σ + m + r +
      L * (l + 1) + 8) + G + (kx + Z + (6 * kx + 4 * b) + bT + bP + A)) := by
  set S := 2 * (28 * kx + 2) + 2 * c + (2 * bP + bT + 1) + kx + σ + m + r + L * (l + 1) + 8
    with hS
  have hl1 : l + 1 ≤ L * (l + 1) := le_mul_of_one_le_left (by linarith) hL
  have hS1 : kx + m + r + l + 9 ≤ S := by rw [hS]; linarith
  have hQS : S ≤ Q * S := le_mul_of_one_le_left (by linarith) hQ
  have key : 80 * G + 40 * (4 * (4 * (kx + 3) + 8 * m + 12 * r + 2 * l + 8 +
      (6 * kx + 4 * b + bT + bP + A + 3) + Z + kx) + 3) ≤
      73746000 * (Q * S + G + (kx + Z + (6 * kx + 4 * b) + bT + bP + A)) := by linarith
  have h := mul_le_mul_of_nonneg_left key hg
  linarith

/-- **The explicit count of `GateODEBudget.binary_ode_time_budget` in the zero case** (equation
`ode:eq:gate-main`, time-dependent part, with the remark on zero time and a known zero generator):
for time-indexed binary public data with `BTPublicOK0 q` in the zero case and valid loading and
weight-preparation circuits, the protocol `nprotocol (btprepC q loadC wpC) (2g)` on the released
register uses at most `73746000 g [q*' (G_C + k_x + σ + m + r + ℓ' (l+1) + 8) + G_src + A]` gates in
every history (`q*' = qOf s T η_H η_D (2g) (ε/2)`, `ℓ' = log(10⁴ · 2g/(ε/2))`,
`G_C = 2 (28 k_x + 2) + 2 |arith| + 2 bP + bT + 1`, `G_src = |loadC| + 2 |wpC|`,
`A = k_x + |Zs| + (6 k_x + 4 b) + bT + bP + A_arith`), with no hypothesis on the rescaling, the
arithmetic accuracy or the bit lengths. -/
theorem binary_ode_time_budget_count_zero (q : PubT) (hq : BTPublicOK0 q) (hz : BTZeroCase q)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    ((nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      73746000 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) : ℕ) : ℝ) +
            q.kx + q.σ + q.params.m + q.params.r +
            logBudget (2 * q.g) (q.ε / 2) * ((q.params.l : ℝ) + 1) + 8) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
        ((q.kx : ℝ) + Fintype.card Zs + ((6 * q.kx + 4 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP +
          q.ar.A)) := by
  have hp := ZeroTimeGateODE.btparams_ok0 hq
  obtain ⟨-, -, -, hWG, -, -, -, -⟩ := ZeroTimeGateODE.native_ode_time_solver_zero
    (S := Fin q.kx) (Zs := Zs) (Z := SZ4 q.kx q.b) (Y := Fin q.m ⊕ PY q.kx q.b) (J := Query)
    q.params q.params.a q.params.m q.params.r q.params.K q.params.l q.params.f q.ar.bT q.ar.bP
    q.ar.A hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hp.lamH_nonneg hp.lamD_nonneg
    (ZeroTimeGateODE.btzeroCase_params hq hz) loadC hloadV wpC hwpV
  have hpr : btprepC q loadC wpC = tzprepC loadC wpC := by
    rw [btprepC, if_pos hz]
  have hr : q.params.ratio = 2 * q.g := rfl
  rw [hpr]
  refine hWG.trans ?_
  rw [hr]
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hg2 : (1 : ℝ) ≤ 2 * q.g := by linarith [hq.g_ge]
  have hε2 : (0 : ℝ) < q.ε / 2 := by linarith [hq.ε_pos]
  have hε2' : q.ε / 2 ≤ 1 := by linarith [hq.ε_half]
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hg2 hε2 hε2'
  have hℓ1 := ImprovedODEQueryBudget.logBudget_ge_one (2 * q.g) (q.ε / 2) hg2 hε2 hε2'
  have h2 : Fintype.card (GateODE.AW q.params.a q.params.m q.params.r q.params.K q.params.m
      q.params.l q.params.f) =
      4 * (q.kx + 3) + 8 * q.params.m + 12 * q.params.r + 2 * q.params.l + 8 := q.params.card_W
  have hXW : Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3 := by
    simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin]
    ring
  rw [h2, hXW, Fintype.card_fin]
  generalize qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) = Q at hQ1 ⊢
  generalize logBudget (2 * q.g) (q.ε / 2) = L at hℓ1 ⊢
  push_cast
  exact count_arithT (G := (nGatesN loadC : ℝ) + 2 * nGatesN wpC)
    (Z := (Fintype.card Zs : ℝ)) (kx := (q.kx : ℝ)) (σ := (q.σ : ℝ)) (m := (q.params.m : ℝ))
    (r := (q.params.r : ℝ)) (l := (q.params.l : ℝ)) (b := (q.b : ℝ))
    (bT := (q.ar.bT : ℝ)) (bP := (q.ar.bP : ℝ)) (A := (q.ar.A : ℝ))
    (c := (q.ar.circ.length : ℝ)) hg0 hQ1 hℓ1
    (add_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) (Nat.cast_nonneg _)))
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` on the released time-dependent
binary register for zero time or a known zero generator** (Theorem `ode:thm:gates`,
time-dependent part, with its remark: direct source assembly, no matrix calls).

For time-indexed binary public data with `BTPublicOK0 q` in the zero case, a rescaling `γ` of bit
length `b_data`, an arithmetic accuracy `ζ ≥ ν/(196608 q*')`, stored bits `b ≤ b_data`, `c₀`,
`η_H`, `η_D` of bit length `b_data` and valid loading and weight-preparation circuits, put
`q*' = qOf s T η_H η_D (2g) (ε/2)` (`= ℓ'`), `𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε`, and
`q* = qOf s T η_H η_D g ε`, `𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε`. The protocol
`nprotocol (btprepC q loadC wpC) (2g)` on the released register has every bound of
`GateBitBudget.binary_ode_time_budget_bits`, in its order: at most
`2·10²⁰ g [q*' (𝔟'+1)³ + G_src + |Zs|]` gates in every history (`G_src = |loadC| + 2 |wpC|`) and
`3·10¹¹ (𝔟'+1)³ + 2 |Zs|` qubits; the words `𝔴 = GateODEBudget.wordsT q` satisfy
`𝔴 + ℓ' ≤ 300 (𝔟'+1)`; at most `6·10¹² g [q*' (𝔴+ℓ'+1)³ + G_src + |Zs|]` gates and
`10⁴ (𝔴+1)³ + 2 |Zs|` qubits; at most
`73746000 g [q*' (G_C + k_x + σ + m + r + ℓ' (l+1) + 8) + G_src + A]` gates; at most
`80 g (calls_c(loadC) + 2 calls_c(wpC))` calls of every kind `c` (no matrix call); and
`|TNW| = 22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + 47`. Then the bounds
of `GateBitBudget.binary_ode_time_budget_bits_user`: at most `2·10²² g [q* (𝔟+1)³ + G_src + |Zs|]`
gates and `9·10¹² (𝔟+1)³ + 2 |Zs|` qubits. Further `q*' = ℓ'`, the trials are valid, every
history makes no call of a kind that the supplied circuits do not call, and for every input with
the energy and accretivity promises of every sample, circuits within `ζs`, `3 ζs ≤ ν` and the
released remaining conditions `PubT.Rest`, the protocol has the guarantee `NOutcome` against
`x(T)`. -/
theorem binary_ode_time_budget_bits_zero_released (bd : ℕ) (q : PubT) (hq : BTPublicOK0 q)
    (hz : BTZeroCase q) (hγb : HasBits bd q.γ)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ)
    (hb : q.b ≤ bd) (hc0 : HasBits bd q.c0) (hH : HasBits bd q.etaH) (hD : HasBits bd q.etaD)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    ((nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      2 * 10 ^ 20 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    (Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        2 * Fintype.card Zs ∧
    (wordsT q : ℝ) + logBudget (2 * q.g) (q.ε / 2) ≤
      300 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ∧
    ((nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      6 * 10 ^ 12 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((wordsT q : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) ≤
      10000 * (wordsT q + 1) ^ 3 + 2 * Fintype.card Zs ∧
    ((nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      73746000 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) : ℕ) : ℝ) +
            q.kx + q.σ + q.params.m + q.params.r +
            logBudget (2 * q.g) (q.ε / 2) * ((q.params.l : ℝ) + 1) + 8) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
        ((q.kx : ℝ) + Fintype.card Zs + ((6 * q.kx + 4 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP +
          q.ar.A)) ∧
    (∀ c : Query → Bool,
      ((nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        (wCallN c) : ℝ) ≤ 80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
        2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs + 47 ∧
    ((nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      2 * 10 ^ 22 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
            1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    (Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℝ) ≤
      9 * 10 ^ 12 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 + 2 * Fintype.card Zs ∧
    qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) = logBudget (2 * q.g) (q.ε / 2) ∧
    (∀ j, ∀ i ∈ trialN (btprepC q loadC wpC) j, i.Valid) ∧
    (∀ c : Query → Bool, nCallsN c loadC = 0 → nCallsN c wpC = 0 →
      (nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        (wCallN c) = 0) ∧
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
      NOutcome (btprepC q loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
        (primsT (R := ℂ) D en x) (xs q.T) := by
  have hp := ZeroTimeGateODE.btparams_ok0 hq
  obtain ⟨hV, -, -, hWG, hWC, hno, hcardZ, hout⟩ := ZeroTimeGateODE.native_ode_time_solver_zero
    (S := Fin q.kx) (Zs := Zs) (Z := SZ4 q.kx q.b) (Y := Fin q.m ⊕ PY q.kx q.b) (J := Query)
    q.params q.params.a q.params.m q.params.r q.params.K q.params.l q.params.f q.ar.bT q.ar.bP
    q.ar.A hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hp.lamH_nonneg hp.lamD_nonneg
    (ZeroTimeGateODE.btzeroCase_params hq hz) loadC hloadV wpC hwpV
  have hpr : btprepC q loadC wpC = tzprepC loadC wpC := by
    rw [btprepC, if_pos hz]
  have hr : q.params.ratio = 2 * q.g := rfl
  -- the arithmetic of the bounds
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hg2 : (1 : ℝ) ≤ 2 * q.g := by linarith [hq.g_ge]
  have hε2 : (0 : ℝ) < q.ε / 2 := by linarith [hq.ε_pos]
  have hε2' : q.ε / 2 ≤ 1 := by linarith [hq.ε_half]
  have hQ1' : 1 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hg2 hε2 hε2'
  have hQz' : qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) = logBudget (2 * q.g) (q.ε / 2) :=
    qOf_zero hq.etaH_nonneg hq.etaD_nonneg hz
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
  have hQz : qOf q.s q.T q.etaH q.etaD q.g q.ε = logBudget q.g q.ε :=
    qOf_zero hq.etaH_nonneg hq.etaD_nonneg hz
  have hQQ : qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) ≤
      2 * qOf q.s q.T q.etaH q.etaD q.g q.ε := by
    rw [hQz', hQz]
    exact logBudget_two_le hq.g_ge hq.ε_pos hε1
  have hℓ1' := ImprovedODEQueryBudget.logBudget_ge_one (2 * q.g) (q.ε / 2) hg2 hε2 hε2'
  have hBB := bitB_le_succ bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) (by linarith) (by linarith) hQQ hg0
    hq.ε_pos
  have hQg' : 0 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.g := by positivity
  have hQg : 0 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε * q.g := by positivity
  have hB0' := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) hQg' hq.ε_pos hε1
  have hB0 := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) hQg hq.ε_pos hε1
  have hw := zero_wordsT_le bd q hq hz hγb hζ hb hc0 hH hD
  have hcW := card_TNW_le q (Zs := Zs)
  have hcnt := binary_ode_time_budget_count_zero q hq hz loadC hloadV wpC hwpV
  have hcardEq := card_TNW_eq q (Zs := Zs)
  have hcW' : (Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) :
      ℝ) ≤ 10000 * ((wordsT q : ℝ) + 1) ^ 3 + 2 * Fintype.card Zs := by
    exact_mod_cast hcW
  rw [card_SZ4] at hcardZ
  have htest : Fintype.card (GateODE.AW q.params.a q.params.m q.params.r q.params.K q.params.m
      q.params.l q.params.f) + Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
      Fintype.card Zs + Fintype.card (Fin q.kx) ≤
      Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) := by
    have h1 := (hcardZ : Fintype.card
      (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) = _)
    have h2 : Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
        6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3 := by
      simp only [XW, AWr, Fintype.card_sum, Fintype.card_fin]
      ring
    rw [h1, h2]
    omega
  have htest' : (Fintype.card (GateODE.AW q.params.a q.params.m q.params.r q.params.K q.params.m
      q.params.l q.params.f) : ℝ) + Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
      Fintype.card Zs + Fintype.card (Fin q.kx) ≤
      Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) := by
    exact_mod_cast htest
  have hW : ((nprotocol (btprepC q loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + 120 * q.g +
        160 * q.g * Fintype.card
          (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) := by
    rw [hpr]
    refine hWG.trans ?_
    rw [hr]
    push_cast
    have := mul_le_mul_of_nonneg_left htest' hg0
    linarith
  generalize hB' : bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
    (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε = B' at hB0' hw hBB
  generalize hB : bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
    (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε = B at hB0 hBB
  generalize hQ' : qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) = Q'
    at hQ1' hQg' hQz' hQQ hcnt
  generalize hQ : qOf q.s q.T q.etaH q.etaD q.g q.ε = Q at hQ1 hQg hQz hQQ
  generalize hN : Fintype.card
    (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) = N
    at hcW hcW' hW hcardEq
  have hwr0 : (0 : ℝ) ≤ wordsT q := Nat.cast_nonneg _
  have hZ0 : (0 : ℝ) ≤ Fintype.card Zs := Nat.cast_nonneg _
  have hG0 : (0 : ℝ) ≤ (nGatesN loadC : ℝ) + 2 * nGatesN wpC := by positivity
  have hcube := GateBitBudget.cube_le hwr0 hB0' (c := 300) (by linarith)
  have hY1' : 1 ≤ (B' + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hY1 : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by linarith)
  have hspace : (N : ℝ) ≤ 3 * 10 ^ 11 * (B' + 1) ^ 3 + 2 * Fintype.card Zs := by
    have : (10000 : ℝ) * ((wordsT q : ℝ) + 1) ^ 3 ≤ 10000 * ((300 + 1) ^ 3 * (B' + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left hcube (by norm_num)
    linarith
  have hYY : (B' + 1) ^ 3 ≤ 8 * (B + 1) ^ 3 := by
    have h1 : B' + 1 ≤ 2 * (B + 1) := by linarith
    calc (B' + 1) ^ 3 ≤ (2 * (B + 1)) ^ 3 := pow_le_pow_left₀ (by linarith) h1 3
      _ = 8 * (B + 1) ^ 3 := by ring
  have hspaceU : (N : ℝ) ≤ 9 * 10 ^ 12 * (B + 1) ^ 3 + 2 * Fintype.card Zs := by
    have : (0 : ℝ) ≤ (B + 1) ^ 3 := by positivity
    linarith
  have hV1 : 1 ≤ ((wordsT q : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3 :=
    one_le_pow₀ (by linarith)
  have hV2 : ((wordsT q : ℝ) + 1) ^ 3 ≤ ((wordsT q : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  have h4 : 0 ≤ q.g * ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) := mul_nonneg hg0 hG0
  have h5 : 0 ≤ q.g * (Fintype.card Zs : ℝ) := mul_nonneg hg0 hZ0
  refine ⟨?_, hspace, hw, ?_, hcW, hcnt, ?_, hcardEq, ?_, hspaceU, hQz', ?_, ?_, ?_⟩
  · -- gates in `𝔟'`
    refine hW.trans ?_
    have h1 : q.g * N ≤ q.g * (3 * 10 ^ 11 * (B' + 1) ^ 3 + 2 * Fintype.card Zs) :=
      mul_le_mul_of_nonneg_left hspace hg0
    have h2 : q.g * (B' + 1) ^ 3 ≤ q.g * (Q' * (B' + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith) hQ1') hg0
    have h3 : q.g * 1 ≤ q.g * (Q' * (B' + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hQ1' hY1') hg0
    linarith
  · -- gates in the words
    refine hW.trans ?_
    have h1 : q.g * N ≤ q.g * (10000 * ((wordsT q : ℝ) + 1) ^ 3 + 2 * Fintype.card Zs) :=
      mul_le_mul_of_nonneg_left hcW' hg0
    have h2 : q.g * ((wordsT q : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3 ≤
        q.g * (Q' * ((wordsT q : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith) hQ1') hg0
    have h3 : q.g * ((wordsT q : ℝ) + 1) ^ 3 ≤
        q.g * ((wordsT q : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3 :=
      mul_le_mul_of_nonneg_left hV2 hg0
    have h3' : q.g * 1 ≤ q.g * ((wordsT q : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3 :=
      mul_le_mul_of_nonneg_left hV1 hg0
    linarith
  · intro c
    rw [hpr]
    refine (hWC c).trans (le_of_eq ?_)
    rw [hr]
    push_cast
    ring
  · -- gates in `𝔟` of `(g, ε)`
    refine hW.trans ?_
    have h1 : q.g * N ≤ q.g * (9 * 10 ^ 12 * (B + 1) ^ 3 + 2 * Fintype.card Zs) :=
      mul_le_mul_of_nonneg_left hspaceU hg0
    have h2 : q.g * (B + 1) ^ 3 ≤ q.g * (Q * (B + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by linarith) hQ1) hg0
    have h3 : q.g * 1 ≤ q.g * (Q * (B + 1) ^ 3) :=
      mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hQ1 hY1) hg0
    linarith
  · rw [hpr]
    exact hV
  · intro c h0 h1
    rw [hpr]
    exact hno c h0 h1
  · intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
    have hI := ZeroTimeGateODE.binary_tzInstanceOK q hq D en x hrH hcH hrD hcD hPSD Jl Wp G bf
      xs bs βG δG βb δb bmax hR
    rw [hpr]
    exact hout (primsT (R := ℂ) D en x) Jl Wp (HsT D en x) (LsT D en x) G bf xs bs βG δG βb δb
      bmax ζs (primsT_isUnitary D en x) hζs hload hwp hbud hI

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` from time-indexed binary sparse
data for every `T ≥ 0`** (Theorem `ode:thm:gates`, time-dependent part, equation
`ode:eq:gate-word-budget`, with its remark on zero time and a known zero generator).

For time-indexed binary public data with `BTPublicOK0 q` (every `T ≥ 0`), the rescaling `γ` of
bit length `b_data` in the zero case `BTZeroCase q` and the public rescaling
`γ = gammaOf T η_H η_D (2g) (ε/2)` otherwise, an arithmetic accuracy `ζ ≥ ν/(196608 q*')`, stored
bits `b ≤ b_data` and `c₀`, `T`, `η_H`, `η_D` of bit length `b_data`, and the binary data and
valid circuits of the released `GateBitBudget.binary_ode_time_budget_bits`, put
`q*' = qOf s T η_H η_D (2g) (ε/2)`, `𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε` and `q*`, `𝔟`
those of `(g, ε)`. The protocol `nprotocol (btprepC q loadC wpC) (2g)` on the released register
uses at most `2·10²⁰ g [q*' (𝔟'+1)³ + G_src + |Zs|]` gates in every history and has at most
`3·10¹¹ (𝔟'+1)³ + 2 |Zs|` qubits; the words satisfy `𝔴 + ℓ' ≤ 300 (𝔟'+1)`; at most
`6·10¹² g [q*' (𝔴+ℓ'+1)³ + G_src + |Zs|]` gates and `10⁴ (𝔴+1)³ + 2 |Zs|` qubits; at most
`73746000 g [q*' (G_C + k_x + σ + m + r + ℓ' (l+1) + 8) + G_src + A]` gates; every history makes
at most `(if BTZeroCase q then 0 else 7864320 g q*' ([row] + [col] + [value])) +
80 g (calls_c(loadC) + 2 calls_c(wpC))` calls of every kind `c`; the register has
`22 k_x + 16 m + 24 r + 4 l + 8 b + 2 (bT + bP + A_arith) + 2 |Zs| + 47` qubits; at most
`2·10²² g [q* (𝔟+1)³ + G_src + |Zs|]` gates and `9·10¹² (𝔟+1)³ + 2 |Zs|` qubits; the trials are
valid; and for every input with the released energy and accretivity promises of every sample,
circuits within `ζs` with `98304 q*' ζ + 3 ζs ≤ ν` and the released remaining conditions
`PubT.Rest`, the protocol has the guarantee `NOutcome` against `x(T)`: every conclusion of
`GateBitBudget.binary_ode_time_budget_bits`, in its order, with both bounds of
`GateBitBudget.binary_ode_time_budget_bits_user` and the validity of the trials inserted before
`NOutcome`. -/
theorem binary_ode_time_budget_bits_nonneg (bd : ℕ) (q : PubT) (hq : BTPublicOK0 q)
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
    ((nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      2 * 10 ^ 20 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    (Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℝ) ≤
      3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        2 * Fintype.card Zs ∧
    (wordsT q : ℝ) + logBudget (2 * q.g) (q.ε / 2) ≤
      300 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ∧
    ((nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      6 * 10 ^ 12 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((wordsT q : ℝ) + logBudget (2 * q.g) (q.ε / 2) + 1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) ≤
      10000 * (wordsT q + 1) ^ 3 + 2 * Fintype.card Zs ∧
    ((nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      73746000 * q.g * (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (((2 * (28 * q.kx + 2) + 2 * q.ar.circ.length + (2 * q.ar.bP + q.ar.bT + 1) : ℕ) : ℝ) +
            q.kx + q.σ + q.params.m + q.params.r +
            logBudget (2 * q.g) (q.ε / 2) * ((q.params.l : ℝ) + 1) + 8) +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) +
        ((q.kx : ℝ) + Fintype.card Zs + ((6 * q.kx + 4 * q.b : ℕ) : ℝ) + q.ar.bT + q.ar.bP +
          q.ar.A)) ∧
    (∀ c : Query → Bool,
      ((nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        (wCallN c) : ℝ) ≤
      (if BTZeroCase q then 0 else 7864320 * q.g *
          qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0))) +
        80 * q.g * ((nCallsN c loadC : ℝ) + 2 * nCallsN c wpC)) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) =
      22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l + 8 * q.b +
        2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs + 47 ∧
    ((nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      2 * 10 ^ 22 * q.g * (qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
            1) ^ 3 +
        ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) + Fintype.card Zs) ∧
    (Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℝ) ≤
      9 * 10 ^ 12 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 + 2 * Fintype.card Zs ∧
    (∀ j, ∀ i ∈ trialN (btprepC q loadC wpC) j, i.Valid) ∧
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
      NOutcome (btprepC q loadC wpC) q.params.ratio q.ε (q.params.ratio_ge hq.g_ge)
        (primsT (R := ℂ) D en x) (xs q.T) := by
  have hV := (ZeroTimeGateODE.binary_ode_time_solver_nonneg q hq D en hrange hdec loadC hloadV
    wpC hwpV).1
  by_cases hz : BTZeroCase q
  · rw [if_pos hz] at hγ
    obtain ⟨hWg, hWc, hw, hWg', hWc', hcnt, hWC, hcard, hU, hUc, -, -, -, hout⟩ :=
      binary_ode_time_budget_bits_zero_released bd q hq hz hγ hζ hb hc0 hH hD D en loadC hloadV
        wpC hwpV
    refine ⟨hWg, hWc, hw, hWg', hWc', hcnt, fun c => ?_, hcard, hU, hUc, hV, ?_⟩
    · rw [if_pos hz, zero_add]
      exact hWC c
    · intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
      have hε2 : (0 : ℝ) < q.ε / 2 := by linarith [hq.ε_pos]
      have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
        one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg (by linarith [hq.g_ge]) hε2
          (by linarith [hq.ε_half])
      have h0 : 0 ≤ 98304 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.ζ :=
        mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hq.ζ_pos.le
      exact hout x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp
        (by linarith) hR
  · rw [if_neg hz] at hγ
    have hP := ZeroTimeGateODE.btpublicOK_of hq hz
    obtain ⟨hWg, hWc, hw, hWg', hWc', hcnt, hWC, hcard, hout⟩ :=
      GateBitBudget.binary_ode_time_budget_bits bd q hP hγ hζ hb hc0 hT hH hD D en hrange hdec
        loadC hloadV wpC hwpV
    obtain ⟨hU, hUc⟩ := GateBitBudget.binary_ode_time_budget_bits_user bd q hP hγ hζ hb hc0 hT
      hH hD D en hrange hdec loadC hloadV wpC hwpV
    have hpr : btprepC q loadC wpC = q.prep loadC wpC := by
      rw [btprepC, if_neg hz]
    refine ⟨?_, hWc, hw, ?_, hWc', ?_, fun c => ?_, hcard, ?_, hUc, hV, ?_⟩
    · rw [hpr]
      exact hWg
    · rw [hpr]
      exact hWg'
    · rw [hpr]
      exact hcnt
    · rw [hpr, if_neg hz]
      exact hWC c
    · rw [hpr]
      exact hU
    · rw [hpr]
      exact hout

end

end SparseHamiltonian.GateRemarks.ODE
