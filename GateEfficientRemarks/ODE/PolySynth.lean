import GateEfficientRemarks.ODE.Absorb
import GateEfficientBitBudget.Synth

/-!
# Source costs polynomial in `𝔟` over a finite gate set

The finite-gate-set forms of equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟`
(`GateBitBudget.binary_ode_budget_trials_bits`, `GateBitBudget.binary_ode_time_budget_trials_bits`:
one native preparation synthesised over `𝒢` at accuracy `ν/3`, with the per-trial claim) have the
synthesis factor `c₁ (64 (𝔟+1) + log(G_src+1)) + c₀` (`c₀, c₁ ≥ 0` the synthesis constants of
`len ζ ≤ c₁ log(1/ζ) + c₀`, not the decoder scale) multiplying the whole native preparation. If
`G_src ≤ c (𝔟+1)^j` and `|Zs| ≤ c (𝔟+1)^j`, then `log(G_src + 1) ≤ c + j (𝔟+1)`
(`log_succ_le`), so the factor is at most `(c₁ (64 + j + c) + c₀) (𝔟+1)` and the gate bound
gains one power of `𝔟 + 1` (`J = max j 3`):

* `binary_ode_budget_trials_poly`: at most
  `[40 (2·10¹⁸ + c) (c₁ (64 + j + c) + c₀) + 20 (12·10¹¹ + 8c + 3)] g q* (𝔟+1)^(J+1) + 80 g |Xa|`
  gates of `𝒢` in every history and at most `(7·10¹¹ + 4c) (𝔟+1)^J + 2 |Xa|` qubits;
* `binary_ode_time_budget_trials_poly`: the same with `80`, `40` in place of `40`, `20` and
  `160 g |Xa|` (internal `q*` of `(2g, ε/2)`).

The synthesis ancillas `Xa` of the hypothesis `GateSynth.Synthesis 𝒢 Xa len` do not depend on the
instance; they are kept as the additive parameter of the released bounds (`4 · 20 g |Xa|`,
`2 |Xa|`). The protocols are those of the endpoints, whose other conclusions hold under the same
hypotheses.
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

section Budget

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Source costs polynomial in `𝔟` over a finite gate set, constant coefficients** (partial
formalisation, under this package's format hypotheses, of the finite-set form of the remark of
Theorem `ode:thm:gates`). Under the hypotheses of
`GateBitBudget.binary_ode_budget_trials_bits` (`Synthesis 𝒢 Xa len` with `len ζ ≤ c₁ log(1/ζ) + c₀`,
`c₀, c₁ ≥ 0`, `AdjClosed 𝒢`, `zeroTestKinds ⊆ 𝒢`, and the hypotheses of `binary_ode_budget_bits`),
with `𝔟 = bitB b_data (2^k_x) (2^m) (2^k) q* g ε`: if `G_src = |srcC 0| + |srcC 1|` and `|Zs|` are
at most `c (𝔟+1)^j`, then in every history the protocol
`nprotocol (synthPrep hS (ν/3) (q.prep srcC)) g` uses at most
`[40 (2·10¹⁸ + c) (c₁ (64 + j + c) + c₀) + 20 (12·10¹¹ + 8c + 3)] g q* (𝔟+1)^(max j 3 + 1) +
80 g |Xa|` gates of `𝒢`, and its register has at most `(7·10¹¹ + 4c) (𝔟+1)^(max j 3) + 2 |Xa|`
qubits. -/
theorem binary_ode_budget_trials_poly (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (bd : ℕ) (q : Pub) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD q.g q.ε)
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
    ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep srcC)) q.g hq.g_ge).worstCost
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
  obtain ⟨-, hW, hA, -⟩ := GateBitBudget.binary_ode_budget_trials_bits hS hadj hzt hc₀ hc₁ hlen
    bd q hq hγ hζ hb hc0 hT hH hD D en hrange hdec srcC hsrcV
  have hQ1 := (GateODEBudget.pub_shapeOK q hq).one_le_q
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
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

/-- **Source costs polynomial in `𝔟` over a finite gate set, time-dependent coefficients**
(partial formalisation, under this package's format hypotheses, of the finite-set form of the
remark of Theorem `ode:thm:gates`, time-dependent part). Under the
hypotheses of `GateBitBudget.binary_ode_time_budget_trials_bits`, with the internal
`q* = qOf s T η_H η_D (2g) (ε/2)` and `𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε`: if
`G_src = |loadC| + 2 |wpC|` and `|Zs|` are at most `c (𝔟+1)^j`, then in every history the
synthesised protocol (ratio `2g`) uses at most
`[80 (2·10¹⁸ + c) (c₁ (64 + j + c) + c₀) + 40 (12·10¹¹ + 8c + 3)] g q* (𝔟+1)^(max j 3 + 1) +
160 g |Xa|` gates of `𝒢`, and its register has at most `(7·10¹¹ + 4c) (𝔟+1)^(max j 3) + 2 |Xa|`
qubits. -/
theorem binary_ode_time_budget_trials_poly (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (bd : ℕ) (q : PubT) (hq : q.OK) (hγ : q.γ = gammaOf q.T q.etaH q.etaD (2 * q.g) (q.ε / 2))
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
    ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
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
  obtain ⟨-, hW, hA, -⟩ := GateBitBudget.binary_ode_time_budget_trials_bits hS hadj hzt hc₀ hc₁
    hlen bd q hq hγ hζ hb hc0 hT hH hD D en hrange hdec loadC hloadV wpC hwpV
  have hQ1 := (GateODEBudget.pubT_shapeOK q hq).one_le_q
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
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
