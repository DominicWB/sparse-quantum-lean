import GateEfficientBitBudget.SynthWords

/-!
# Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` over a finite gate set

The finite-gate-set forms of the released budgets (`GateODEBudget.binary_ode_budget_trials`,
`GateODEBudget.binary_ode_time_budget_trials`: one native preparation synthesised over `𝒢` at
accuracy `ν/3`, its inverse the exact adjoint, the zero tests and the sign exact) in the word
budget `𝔟` of `binary_ode_budget_bits` (respectively `binary_ode_time_budget_bits`), under the
hypotheses of those theorems and the released synthesis hypotheses (`GateSynth.Synthesis` with
`len ζ ≤ c₁ log(1/ζ) + c₀`, `c₀, c₁ ≥ 0` the synthesis constants, not the decoder scale `c₀`;
`AdjClosed 𝒢`, `zeroTestKinds ⊆ 𝒢`):

* `binary_ode_budget_trials_bits`: the native preparation has at most
  `B ≤ 2·10¹⁸ q* (𝔟+1)³ + G_src` gates; in every history the synthesised protocol uses at most
  `40 g (2·10¹⁸ q* (𝔟+1)³ + G_src) (c₁ (64 (𝔟+1) + log(G_src+1)) + c₀) +
  20 g (4 (3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢`; its register has at most
  `7·10¹¹ (𝔟+1)³ + 4 |Zs| + 2 |Xa|` qubits; every conclusion of `binary_ode_budget_trials` is kept
  (validity and gate kinds of every trial, the released gate, call and qubit counts, and the
  guarantees `NOutcome`, every successful trial included).
* `binary_ode_time_budget_trials_bits`: the same for time-dependent coefficients (`80 g`, `40 g`).

The synthesis factor multiplies the whole native preparation, the source circuits included, as in
the released finite-gate-set budgets. `synth_arith` is the monotonicity of the synthesised gate
count used for both.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBitBudget

noncomputable section
open ContinuousLinearMap SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateBinaryODETime SparseHamiltonian.OracleCircuit
open SparseHamiltonian.GateSynth SparseHamiltonian.GateSynthTrials
open GateODEBudget (gammaOf qOf prepBound prepBoundT binary_ode_budget_trials
  binary_ode_time_budget_trials)
open ImprovedODEQueryBudget (precision logBudget)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

/-- The arithmetic of the synthesised gate count: `c g (B (c₁ λ + c₀)) + d g (4 n + 3) ≤
c g (B' (c₁ λ' + c₀)) + d g (4 n' + 3)` for `0 ≤ B ≤ B'`, `0 ≤ λ ≤ λ'`, `n ≤ n'`. -/
theorem synth_arith {c d g B B' lam lam' c₀ c₁ n n' : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d) (hg : 0 ≤ g)
    (hB0 : 0 ≤ B) (hB : B ≤ B') (hlam0 : 0 ≤ lam) (hlam : lam ≤ lam') (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (hn : n ≤ n') :
    c * g * (B * (c₁ * lam + c₀)) + d * g * (4 * n + 3) ≤
      c * g * (B' * (c₁ * lam' + c₀)) + d * g * (4 * n' + 3) := by
  have hf0 : 0 ≤ c₁ * lam + c₀ := by positivity
  have hf : c₁ * lam + c₀ ≤ c₁ * lam' + c₀ := by
    have := mul_le_mul_of_nonneg_left hlam hc₁
    linarith
  have h1 : B * (c₁ * lam + c₀) ≤ B' * (c₁ * lam' + c₀) :=
    mul_le_mul hB hf hf0 (hB0.trans hB)
  have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hc hg)
  have h3 : d * g * (4 * n + 3) ≤ d * g * (4 * n' + 3) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hd hg)
  linarith

section Budget

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` over a finite gate set,
constant coefficients** (Theorem `ode:thm:gates`). Under `Synthesis 𝒢 Xa len` with
`len ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]` (`c₀, c₁ ≥ 0` the synthesis constants, not the decoder
scale `c₀`), `AdjClosed 𝒢`, `zeroTestKinds ⊆ 𝒢` and the hypotheses of
`binary_ode_budget_bits` (public rescaling, `ζ ≥ ν/(196608 q*)`, `b ≤ b_data`, `c₀`, `T`, `η_H`,
`η_D` of bit length `b_data`), with `𝔟 = bitB b_data (2^k_x) (2^m) (2^k) q* g ε` and
`G_src = |srcC 0| + |srcC 1|`: the native preparation bound is
`B = prepBound q srcC ≤ 2·10¹⁸ q* (𝔟+1)³ + G_src`; in every history the synthesised protocol
`nprotocol (synthPrep hS (ν/3) (q.prep srcC)) g` uses at most
`40 g (2·10¹⁸ q* (𝔟+1)³ + G_src) (c₁ (64 (𝔟+1) + log(G_src+1)) + c₀) +
20 g (4 (3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢`; its register has at most
`7·10¹¹ (𝔟+1)³ + 4 |Zs| + 2 |Xa|` qubits; and every conclusion of
`GateODEBudget.binary_ode_budget_trials` holds (every instruction of every trial is valid and
every gate is a gate of `𝒢`; one native preparation has at most `B` gates; the released gate
count `40 g B (c₁ log((B+1)/(ν/3)) + c₀) + 20 g (4 n + 3)`; at most `3932160 g q*` calls of each
matrix oracle besides `40 g` times the calls of the source circuits; the register size; and,
with `98304 q* ζ + 2 ζs ≤ ν`, the guarantees `NOutcome`, every successful trial within `ε/500` of
the normalised solution up to a global phase). -/
theorem binary_ode_budget_trials_bits (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
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
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    prepBound q srcC ≤ 2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD q.g q.ε *
        (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
      ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep srcC)) q.g hq.g_ge).worstCost
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
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep srcC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep srcC)) j →
        GateOf 𝒢 g) ∧
    (nGatesN (q.prep srcC) : ℝ) ≤ prepBound q srcC ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep srcC)) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * q.g * (prepBound q srcC *
        (c₁ * Real.log ((prepBound q srcC + 1) / (q.params.nu / 3)) + c₀)) +
      20 * q.g * (4 * ((22 * q.kx + 12 * q.params.m + 24 * q.params.r + 4 * q.params.k +
        4 * q.params.l + 8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs +
        Fintype.card Xa + 47 : ℕ) : ℝ) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep srcC)) q.g hq.g_ge).worstCost
        (wCallN c) : ℝ) ≤
      3932160 * q.g * qOf q.s q.T q.etaH q.etaD q.g q.ε *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
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
      (x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection x0) →
      (v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection v) →
      ODEConstantForcing.solution (-mLift D en x) x0 v q.T ≠ 0 →
      q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en x) x0 v q.T‖ →
      NOutcome (synthPrep hS (q.params.nu / 3) (q.prep srcC)) q.g q.ε hq.g_ge
        (prims (R := ℂ) D en x) (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  obtain ⟨hV, hN, hWG, hC, hcard, hout⟩ :=
    binary_ode_budget_trials hS hadj hzt hc₀ hc₁ hlen q hq hγ D en hrange hdec srcC hsrcV
  have hBp := prepBound_le bd q hq hγ hζ hb hc0 hT hH hD srcC
  have hB0 : 0 ≤ prepBound q srcC := le_trans (Nat.cast_nonneg _) hN
  have hlog := log_factor_le bd q hq hγ hζ hb hc0 hT hH hD srcC hB0
  have hn := tested_le bd q hq hγ hζ hb hc0 hT hH hD
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hY : 1 ≤ (bitB bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
      (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 := by
    have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
    have := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.params.m) (2 ^ q.params.k)
      (mul_nonneg (le_trans zero_le_one (GateODEBudget.pub_shapeOK q hq).one_le_q) hg0)
      hq.ε_pos hε1
    exact one_le_pow₀ (by linarith)
  refine ⟨hBp, ?_, ?_, hV, hN, hWG, hC, hcard, hout⟩
  · refine hWG.trans (synth_arith (by norm_num) (by norm_num) hg0 hB0 hBp ?_ hlog hc₀ hc₁ ?_)
    · apply Real.log_nonneg
      have hν : 0 < q.params.nu := (q.params_ok hq).nu_pos
      have hν1 : q.params.nu ≤ 1 :=
        (ImprovedODEQueryBudget.precision_le_one_ten_thousandth q.g q.ε hq.g_ge
          (hq.ε_half.trans (by norm_num))).trans (by norm_num)
      rw [le_div_iff₀ (by positivity)]
      linarith
    · push_cast at hn ⊢
      linarith
  · rw [hcard]
    push_cast at hn ⊢
    linarith

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` over a finite gate set,
time-dependent coefficients** (Theorem `ode:thm:gates`, time-dependent part). Under the synthesis
hypotheses of `binary_ode_budget_trials_bits` (`c₀, c₁ ≥ 0` the synthesis constants, not the
decoder scale `c₀`) and the hypotheses of
`binary_ode_time_budget_bits`, with `𝔟 = bitB b_data (2^k_x) (2^m) (2^m) q* g ε`
(`q* = qOf s T η_H η_D (2g) (ε/2)`) and `G_src = |loadC| + 2 |wpC|`: the native preparation bound
is `B = prepBoundT q loadC wpC ≤ 2·10¹⁸ q* (𝔟+1)³ + G_src`; in every history the synthesised
protocol (ratio `2g`) uses at most
`80 g (2·10¹⁸ q* (𝔟+1)³ + G_src) (c₁ (64 (𝔟+1) + log(G_src+1)) + c₀) +
40 g (4 (3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢`; its register has at most
`7·10¹¹ (𝔟+1)³ + 4 |Zs| + 2 |Xa|` qubits; and every conclusion of
`GateODEBudget.binary_ode_time_budget_trials` holds (with `98304 q* ζ + 3 ζs ≤ ν` for the
guarantees `NOutcome`). -/
theorem binary_ode_time_budget_trials_bits (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
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
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    prepBoundT q loadC wpC ≤ 2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
        (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
      ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
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
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j →
        GateOf 𝒢 g) ∧
    (nGatesN (q.prep loadC wpC) : ℝ) ≤ prepBoundT q loadC wpC ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * (prepBoundT q loadC wpC *
        (c₁ * Real.log ((prepBoundT q loadC wpC + 1) / (q.params.nu / 3)) + c₀)) +
      40 * q.g * (4 * ((22 * q.kx + 16 * q.params.m + 24 * q.params.r + 4 * q.params.l +
        8 * q.b + 2 * (q.ar.bT + q.ar.bP + q.ar.A) + 2 * Fintype.card Zs +
        Fintype.card Xa + 47 : ℕ) : ℝ) + 3) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      7864320 * q.g * qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) *
          ((if c Query.rowLocation then 1 else 0) + (if c Query.columnLocation then 1 else 0) +
            (if c Query.value then 1 else 0)) +
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
      NOutcome (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (xs q.T) := by
  obtain ⟨hV, hN, hWG, hC, hcard, hout⟩ :=
    binary_ode_time_budget_trials hS hadj hzt hc₀ hc₁ hlen q hq hγ D en hrange hdec loadC hloadV
      wpC hwpV
  have hBp := prepBoundT_le bd q hq hγ hζ hb hc0 hT hH hD loadC wpC
  have hB0 : 0 ≤ prepBoundT q loadC wpC := le_trans (Nat.cast_nonneg _) hN
  have hlog := log_factorT_le bd q hq hγ hζ hb hc0 hT hH hD loadC wpC hB0
  have hn := testedT_le bd q hq hγ hζ hb hc0 hT hH hD
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hY : 1 ≤ (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 := by
    have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
    have := bitB_nonneg bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
      (mul_nonneg (le_trans zero_le_one (GateODEBudget.pubT_shapeOK q hq).one_le_q) hg0)
      hq.ε_pos hε1
    exact one_le_pow₀ (by linarith)
  refine ⟨hBp, ?_, ?_, hV, hN, hWG, hC, hcard, hout⟩
  · refine hWG.trans (synth_arith (by norm_num) (by norm_num) hg0 hB0 hBp ?_ hlog hc₀ hc₁ ?_)
    · apply Real.log_nonneg
      have hν : 0 < q.params.nu := q.params.nu_pos hq.g_ge hq.ε_pos
      have hν1 : q.params.nu ≤ 1 :=
        (ImprovedODEQueryBudget.precision_le_one_ten_thousandth (2 * q.g) (q.ε / 2)
          (by linarith [hq.g_ge]) (by linarith [hq.ε_half])).trans (by norm_num)
      rw [le_div_iff₀ (by positivity)]
      linarith
    · push_cast at hn ⊢
      linarith
  · rw [hcard]
    push_cast at hn ⊢
    linarith

end Budget

end

end SparseHamiltonian.GateBitBudget
