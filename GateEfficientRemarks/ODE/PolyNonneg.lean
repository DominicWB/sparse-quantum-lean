import GateEfficientRemarks.ODE.Absorb
import GateEfficientRemarks.ODE.ZeroReleasedTrialsTime

/-!
# Source costs polynomial in `𝔟` for every `T ≥ 0`

The remark of Theorem `ode:thm:gates` that source costs polynomial in `𝔟` give the gate bound
`ḡ q poly(𝔟)` (equations `ode:eq:gate-word-budget`, `ode:eq:gate-main`, `ode:eq:gate-space`),
stated in `Poly` and `PolySynth` under the released public conditions (`T > 0`,
`η_H + η_D > 0`), holds for every `T ≥ 0`, as corollaries of the combined forms
`binary_ode_budget_bits_nonneg`, `binary_ode_time_budget_bits_nonneg`,
`binary_ode_budget_trials_bits_nonneg` and `binary_ode_time_budget_trials_bits_nonneg` (zero time
and a known zero generator included, with `γ` of bit length `b_data` in the zero case and the
public rescaling otherwise), under their hypotheses and with the constants of `Poly` and
`PolySynth`. If `G_src ≤ c (𝔟+1)^j` and `|Zs| ≤ c (𝔟+1)^j` (then `c ≥ 0`), with `J = max j 3`:

* `binary_ode_budget_poly_nonneg`: at most `10²⁰ (1 + 2c) g q* (𝔟+1)^J` gates in every history
  and `(3·10¹¹ + 2c) (𝔟+1)^J` qubits;
* `binary_ode_time_budget_poly_nonneg` (internal `q*'` of `(2g, ε/2)` and its `𝔟'`):
  `2·10²⁰ (1 + 2c) g q*' (𝔟'+1)^J` gates, `(3·10¹¹ + 2c) (𝔟'+1)^J` qubits;
* `binary_ode_time_budget_poly_user_nonneg` (`q*`, `𝔟` of the user's `(g, ε)`):
  `2·10²² (1 + 2c) g q* (𝔟+1)^J` gates, `(9·10¹² + 2c) (𝔟+1)^J` qubits;
* `binary_ode_budget_trials_poly_nonneg`, `binary_ode_time_budget_trials_poly_nonneg` (finite gate
  set, per-trial claim): the bounds of `PolySynth`, with one more power of `𝔟 + 1` from the
  synthesis factor and the additive `80 g |Xa|` (respectively `160 g |Xa|`) and `2 |Xa|`.

The protocols are those of the combined forms (`ZeroTimeGateODE.bprepC`, `btprepC`), whose other
conclusions hold under the same hypotheses. The arithmetic uses `q* ≥ 1` (`one_le_qOf`, every
`T ≥ 0`) and `𝔟 ≥ 0`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateBinaryODETime
open SparseHamiltonian.GateSynth SparseHamiltonian.GateSynthTrials
open SparseHamiltonian.GateBitBudget (bitB HasBits bitB_nonneg)
open GateODEBudget (gammaOf qOf)
open NativeSparseBlockEncoding (Data Query)
open ZeroTimeGateODE (bprepC btprepC BPublicOK0 BZeroCase BTPublicOK0 BTZeroCase)

section Budget

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Source costs polynomial in `𝔟` for every `T ≥ 0`, constant coefficients** (remark of
Theorem `ode:thm:gates`: the total gate bound is `ḡ q poly(𝔟)`, with its remark on zero time and
a known zero generator). Under the hypotheses of `binary_ode_budget_bits_nonneg` (`BPublicOK0 q`,
`γ` of bit length `b_data` in the zero case and the public rescaling otherwise, and the remaining
hypotheses of `GateBitBudget.binary_ode_budget_bits`), with
`𝔟 = bitB b_data (2^k_x) (2^m) (2^k) q* g ε`: if the source gates `G_src = |srcC 0| + |srcC 1|`
and the source scratch `|Zs|` are at most `c (𝔟+1)^j`, then in every history the protocol
`nprotocol (bprepC q srcC) g` uses at most `10²⁰ (1 + 2c) g q* (𝔟+1)^(max j 3)` elementary gates,
and its register has at most `(3·10¹¹ + 2c) (𝔟+1)^(max j 3)` qubits. -/
theorem binary_ode_budget_poly_nonneg (bd : ℕ) (q : Pub) (hq : BPublicOK0 q)
    (hγ : if BZeroCase q then HasBits bd q.γ else q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
    (hζ : q.params.nu ≤ 196608 * qOf q.s q.T q.etaH q.etaD q.g q.ε * q.ζ) (hb : q.b ≤ bd)
    (hc0 : HasBits bd q.c0) (hT : HasBits bd q.T) (hH : HasBits bd q.etaH)
    (hD : HasBits bd q.etaD)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (c : ℝ) (j : ℕ)
    (hG : (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) ≤
      c * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ j)
    (hZ : (Fintype.card Zs : ℝ) ≤
      c * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ j) :
    ((nprotocol (bprepC q srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
      10 ^ 20 * (1 + 2 * c) * q.g * qOf q.s q.T q.etaH q.etaD q.g q.ε *
        (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ max j 3 ∧
    (Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℝ) ≤
      (3 * 10 ^ 11 + 2 * c) * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ max j 3 := by
  obtain ⟨hW, hA, -⟩ := binary_ode_budget_bits_nonneg bd q hq hγ hζ hb hc0 hT hH hD D en hrange
    hdec srcC hsrcV
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hB0 := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
    (mul_nonneg (by linarith : (0 : ℝ) ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε) hg0) hq.ε_pos hε1
  have hY : (1 : ℝ) ≤ bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
      (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1 := by linarith
  have hc := nonneg_of_le_mul_pow j (Nat.cast_nonneg _) (by linarith) hZ
  exact ⟨hW.trans (gates_absorb j (by norm_num) hg0 hQ1 hY hc hG hZ),
    hA.trans (space_absorb 2 j (by norm_num) (by norm_num) hY hc hZ)⟩

/-- **Source costs polynomial in `𝔟` for every `T ≥ 0`, time-dependent coefficients** (remark of
Theorem `ode:thm:gates`, time-dependent part). Under the hypotheses of
`binary_ode_time_budget_bits_nonneg`, with the internal `q*' = qOf s T η_H η_D (2g) (ε/2)` and
`𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε`: if `G_src = |loadC| + 2 |wpC|` and `|Zs|` are at
most `c (𝔟'+1)^j`, then in every history the protocol `nprotocol (btprepC q loadC wpC) (2g)` uses
at most `2·10²⁰ (1 + 2c) g q*' (𝔟'+1)^(max j 3)` elementary gates, and its register has at most
`(3·10¹¹ + 2c) (𝔟'+1)^(max j 3)` qubits. -/
theorem binary_ode_time_budget_poly_nonneg (bd : ℕ) (q : PubT) (hq : BTPublicOK0 q)
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
    (hwpV : ∀ i ∈ wpC, i.Valid) (c : ℝ) (j : ℕ)
    (hG : (nGatesN loadC : ℝ) + 2 * nGatesN wpC ≤
      c * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ j)
    (hZ : (Fintype.card Zs : ℝ) ≤
      c * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ j) :
    ((nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      2 * 10 ^ 20 * (1 + 2 * c) * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ max j 3 ∧
    (Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℝ) ≤
      (3 * 10 ^ 11 + 2 * c) * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ max j 3 := by
  obtain ⟨hW, hA, -⟩ := binary_ode_time_budget_bits_nonneg bd q hq hγ hζ hb hc0 hT hH hD D en
    hrange hdec loadC hloadV wpC hwpV
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg (by linarith [hq.g_ge])
      (by linarith [hq.ε_pos]) (by linarith [hq.ε_half])
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hB0 := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
    (mul_nonneg (by linarith : (0 : ℝ) ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) hg0)
    hq.ε_pos hε1
  have hY : (1 : ℝ) ≤ bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1 := by linarith
  have hc := nonneg_of_le_mul_pow j (Nat.cast_nonneg _) (by linarith) hZ
  exact ⟨hW.trans (gates_absorb j (by norm_num) hg0 hQ1 hY hc hG hZ),
    hA.trans (space_absorb 2 j (by norm_num) (by norm_num) hY hc hZ)⟩

/-- **Source costs polynomial in `𝔟` for every `T ≥ 0`, time-dependent coefficients, with the
query shape of `(g, ε)`** (remark of Theorem `ode:thm:gates`, time-dependent part). Under the
hypotheses of `binary_ode_time_budget_bits_nonneg`, with `q* = qOf s T η_H η_D g ε` and
`𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε`: if `G_src = |loadC| + 2 |wpC|` and `|Zs|` are at
most `c (𝔟+1)^j`, then in every history the protocol `nprotocol (btprepC q loadC wpC) (2g)` uses
at most `2·10²² (1 + 2c) g q* (𝔟+1)^(max j 3)` elementary gates, and its register has at most
`(9·10¹² + 2c) (𝔟+1)^(max j 3)` qubits. -/
theorem binary_ode_time_budget_poly_user_nonneg (bd : ℕ) (q : PubT) (hq : BTPublicOK0 q)
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
    (hwpV : ∀ i ∈ wpC, i.Valid) (c : ℝ) (j : ℕ)
    (hG : (nGatesN loadC : ℝ) + 2 * nGatesN wpC ≤
      c * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
        1) ^ j)
    (hZ : (Fintype.card Zs : ℝ) ≤
      c * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
        1) ^ j) :
    ((nprotocol (btprepC q loadC wpC) q.params.ratio (q.params.ratio_ge hq.g_ge)).worstCost
        wGateN : ℝ) ≤
      2 * 10 ^ 22 * (1 + 2 * c) * q.g * qOf q.s q.T q.etaH q.etaD q.g q.ε *
        (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m) (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
          1) ^ max j 3 ∧
    (Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) : ℝ) ≤
      (9 * 10 ^ 12 + 2 * c) * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ max j 3 := by
  obtain ⟨-, -, -, -, -, -, -, -, hW, hA, -⟩ := binary_ode_time_budget_bits_nonneg bd q hq hγ hζ
    hb hc0 hT hH hD D en hrange hdec loadC hloadV wpC hwpV
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hB0 := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
    (mul_nonneg (by linarith : (0 : ℝ) ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε) hg0) hq.ε_pos hε1
  have hY : (1 : ℝ) ≤ bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1 := by linarith
  have hc := nonneg_of_le_mul_pow j (Nat.cast_nonneg _) (by linarith) hZ
  exact ⟨hW.trans (gates_absorb j (by norm_num) hg0 hQ1 hY hc hG hZ),
    hA.trans (space_absorb 2 j (by norm_num) (by norm_num) hY hc hZ)⟩

/-- **Source costs polynomial in `𝔟` over a finite gate set for every `T ≥ 0`, constant
coefficients** (remark of Theorem `ode:thm:gates`). Under the hypotheses of
`binary_ode_budget_trials_bits_nonneg`, with `𝔟 = bitB b_data (2^k_x) (2^m) (2^k) q* g ε`: if
`G_src = |srcC 0| + |srcC 1|` and `|Zs|` are at most `c (𝔟+1)^j`, then in every history the
protocol `nprotocol (synthPrep hS (ν/3) (bprepC q srcC)) g` uses at most
`[40 (2·10¹⁸ + c) (c₁ (64 + j + c) + c₀) + 20 (12·10¹¹ + 8c + 3)] g q* (𝔟+1)^(max j 3 + 1) +
80 g |Xa|` gates of `𝒢`, and its register has at most `(7·10¹¹ + 4c) (𝔟+1)^(max j 3) + 2 |Xa|`
qubits. -/
theorem binary_ode_budget_trials_poly_nonneg (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
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
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (c : ℝ) (j : ℕ)
    (hG : (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) ≤
      c * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ j)
    (hZ : (Fintype.card Zs : ℝ) ≤
      c * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
        (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ j) :
    ((nprotocol (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      (40 * (2 * 10 ^ 18 + c) * (c₁ * (64 + j + c) + c₀) + 20 * (12 * 10 ^ 11 + 8 * c + 3)) *
          q.g * qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
            (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ (max j 3 + 1) +
        80 * q.g * Fintype.card Xa ∧
    (Fintype.card (SNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) : ℝ) ≤
      (7 * 10 ^ 11 + 4 * c) * (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ max j 3 +
        2 * Fintype.card Xa := by
  obtain ⟨-, hW, hA, -⟩ := binary_ode_budget_trials_bits_nonneg hS hadj hzt hc₀ hc₁ hlen bd q hq
    hγ hζ hb hc0 hT hH hD D en hrange hdec srcC hsrcV
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hB0 := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
    (mul_nonneg (by linarith : (0 : ℝ) ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε) hg0) hq.ε_pos hε1
  have hY : (1 : ℝ) ≤ bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
      (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1 := by linarith
  have hc := nonneg_of_le_mul_pow j (Nat.cast_nonneg _) (by linarith) hZ
  have hG0 : (0 : ℝ) ≤ (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) := by positivity
  have hS' := synth_absorb (K₁ := 40) (K₂ := 20) (P₁ := 2 * 10 ^ 18) (P₂ := 3 * 10 ^ 11)
    (X := (Fintype.card Xa : ℝ)) j (by norm_num) (by norm_num) (by norm_num) (by norm_num) hg0
    hQ1 hY hc hc₀ hc₁ hG0 hG hZ
  have hsp := space_absorb (P := 7 * 10 ^ 11) 4 j (by norm_num) (by norm_num) hY hc hZ
  refine ⟨(hW.trans hS').trans (le_of_eq (by ring)), by linarith⟩

/-- **Source costs polynomial in `𝔟` over a finite gate set for every `T ≥ 0`, time-dependent
coefficients** (remark of Theorem `ode:thm:gates`, time-dependent part). Under the hypotheses of
`binary_ode_time_budget_trials_bits_nonneg`, with the internal
`q*' = qOf s T η_H η_D (2g) (ε/2)` and `𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε`: if
`G_src = |loadC| + 2 |wpC|` and `|Zs|` are at most `c (𝔟'+1)^j`, then in every history the
protocol `nprotocol (synthPrep hS (ν/3) (btprepC q loadC wpC)) (2g)` uses at most
`[80 (2·10¹⁸ + c) (c₁ (64 + j + c) + c₀) + 40 (12·10¹¹ + 8c + 3)] g q*' (𝔟'+1)^(max j 3 + 1) +
160 g |Xa|` gates of `𝒢`, and its register has at most `(7·10¹¹ + 4c) (𝔟'+1)^(max j 3) + 2 |Xa|`
qubits. -/
theorem binary_ode_time_budget_trials_poly_nonneg (hS : Synthesis 𝒢 Xa len)
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
    (hwpV : ∀ i ∈ wpC, i.Valid) (c : ℝ) (j : ℕ)
    (hG : (nGatesN loadC : ℝ) + 2 * nGatesN wpC ≤
      c * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ j)
    (hZ : (Fintype.card Zs : ℝ) ≤
      c * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
        (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ j) :
    ((nprotocol (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      (80 * (2 * 10 ^ 18 + c) * (c₁ * (64 + j + c) + c₀) + 40 * (12 * 10 ^ 11 + 8 * c + 3)) *
          q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
            (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ (max j 3 + 1) +
        160 * q.g * Fintype.card Xa ∧
    (Fintype.card (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) : ℝ) ≤
      (7 * 10 ^ 11 + 4 * c) * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ max j 3 +
        2 * Fintype.card Xa := by
  obtain ⟨-, hW, hA, -⟩ := binary_ode_time_budget_trials_bits_nonneg hS hadj hzt hc₀ hc₁ hlen bd
    q hq hγ hζ hb hc0 hT hH hD D en hrange hdec loadC hloadV wpC hwpV
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg (by linarith [hq.g_ge])
      (by linarith [hq.ε_pos]) (by linarith [hq.ε_half])
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hB0 := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
    (mul_nonneg (by linarith : (0 : ℝ) ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) hg0)
    hq.ε_pos hε1
  have hY : (1 : ℝ) ≤ bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1 := by linarith
  have hc := nonneg_of_le_mul_pow j (Nat.cast_nonneg _) (by linarith) hZ
  have hG0 : (0 : ℝ) ≤ (nGatesN loadC : ℝ) + 2 * nGatesN wpC := by positivity
  have hS' := synth_absorb (K₁ := 80) (K₂ := 40) (P₁ := 2 * 10 ^ 18) (P₂ := 3 * 10 ^ 11)
    (X := (Fintype.card Xa : ℝ)) j (by norm_num) (by norm_num) (by norm_num) (by norm_num) hg0
    hQ1 hY hc hc₀ hc₁ hG0 hG hZ
  have hsp := space_absorb (P := 7 * 10 ^ 11) 4 j (by norm_num) (by norm_num) hY hc hZ
  refine ⟨(hW.trans hS').trans (le_of_eq (by ring)), by linarith⟩

end Budget

end

end SparseHamiltonian.GateRemarks.ODE
