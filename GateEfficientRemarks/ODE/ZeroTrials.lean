import GateEfficientRemarks.ODE.ZeroBudget

/-!
# Zero time or a known zero generator over a finite gate set: the budgets in `𝔟`

The finite-gate-set forms of Theorem `ode:thm:gates` in this module are a partial formalisation of
its finite-set statement, under this package's format hypotheses: the manuscript states Theorem
`ode:thm:gates` over a finite gate set; the conformance endpoints count native gates.

The finite-gate-set form of `binary_ode_budget_bits_zero` (equations `ode:eq:gate-main` and
`ode:eq:gate-space` of Theorem `ode:thm:gates` with its remark on zero time and a known zero
generator) with the per-trial claim: only the preparation is synthesised
(`GateSynthTrials.synthPrep hS (ν/3)`, its inverse the adjoint of the synthesised circuit, the zero
tests and the sign exact), as in the released `GateBitBudget.binary_ode_budget_trials_bits` and in
the zero-case form `ZeroTimeGateODE.native_ode_solver_zero_trials`. On the trial register
`MinSW 0 k_x Zs Xa` of the minimal register, for binary data in the zero case (`BZeroCase`):

* `binary_ode_budget_trials_bits_zero`: in every history at most
  `40 g (2·10¹⁸ q* (𝔟+1)³ + G_src) (c₁ (64 (𝔟+1) + log(G_src+1)) + c₀) +
  20 g (4 (3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢` on at most
  `7·10¹¹ (𝔟+1)³ + 4 |Zs| + 2 |Xa|` qubits (the bounds of the released form with the same
  constants), for `𝔟 = bitB b_data (2^k_x) M m_src q* g ε` with every `M`, `m_src`; the explicit
  counts `40 g N (c₁ log((N+1)/(ν/3)) + c₀) + 20 g (4 (2 k_x + 2 |Zs| + |Xa| + 17) + 3)`
  (`N = G_src + 2`) and `4 k_x + 4 |Zs| + 2 |Xa| + 35` qubits; valid trials of `𝒢`; no call of a
  kind that the source circuits do not call; `GateNative.NOutcome` (every successful trial
  within `ε/500` of the normalised solution) under the zero-case conditions.

The synthesis factor is controlled by `log_trial_le`: `log((N+1)/(ν/3)) ≤ 64 (𝔟+1) + log(G_src+1)`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateBinary GateSynth GateSynthTrials
open ZeroTimeGateODE (zprepC srcRot BPublicOK0 BZeroCase)
open GateBinaryODE (Pub mLift)
open SparseHamiltonian.GateBitBudget (bitB bitB_nonneg)
open GateODEBudget (qOf)
open NativeSparseBlockEncoding (Data Query)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

section Trials

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` over a finite gate set, with
the per-trial claim, for zero time or a known zero generator, constant coefficients**
(partial formalisation, under this package's format hypotheses, of the finite-set statement of
Theorem `ode:thm:gates` with its remark).

Under `Synthesis 𝒢 Xa len` with `len ζ ≤ c₁ log(1/ζ) + c₀` (`c₀, c₁ ≥ 0` the synthesis
constants), `AdjClosed 𝒢` and `zeroTestKinds ⊆ 𝒢`, for binary public data with `BPublicOK0 q` in
the zero case, valid source circuits, any `b_data`, `M`, `m_src`, with `q* = qOf s T η_H η_D g ε`
(`= ℓ`) and `𝔟 = bitB b_data (2^k_x) M m_src q* g ε`, the protocol
`nprotocol (synthPrep hS (ν/3) (zprepC (srcRot T r₀ r_b) srcC)) g` on the trial register
`MinSW 0 k_x Zs Xa`: in every history at most
`40 g (2·10¹⁸ q* (𝔟+1)³ + G_src) (c₁ (64 (𝔟+1) + log(G_src+1)) + c₀) +
20 g (4 (3·10¹¹ (𝔟+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢` (`G_src = |srcC 0| + |srcC 1|`) and
at most `7·10¹¹ (𝔟+1)³ + 4 |Zs| + 2 |Xa|` qubits (the bounds of
`GateBitBudget.binary_ode_budget_trials_bits`); in fact at most
`40 g N (c₁ log((N+1)/(ν/3)) + c₀) + 20 g (4 (2 k_x + 2 |Zs| + |Xa| + 17) + 3)` gates
(`N = G_src + 2`) on exactly `4 k_x + 4 |Zs| + 2 |Xa| + 35` qubits; `q* = ℓ`; every trial
consists of valid gates of `𝒢` and primitive calls; every history makes at most
`40 g (calls_c(srcC 0) + calls_c(srcC 1))` calls of every kind `c`, so none of a kind that the
source circuits do not call; and under the zero-case conditions (row energy promises, sources
within `ζs`, `2 ζs ≤ ν`, public norms, seed promises, `x(T) ≠ 0`, `r₀ + T r_b ≤ g ‖x(T)‖`) the
protocol has the guarantees `NOutcome` against the solution `x(T)` of `x' = -M̂ x + b`. -/
theorem binary_ode_budget_trials_bits_zero (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (bd : ℕ) (q : Pub) (hq : BPublicOK0 q) (hz : BZeroCase q)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) (M msrc : ℕ) :
    ((nprotocol (synthPrep hS (q.params.nu / 3) (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query))) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * q.g * ((2 * 10 ^ 18 * qOf q.s q.T q.etaH q.etaD q.g q.ε *
          (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 +
          ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true))) *
        (c₁ * (64 * (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
            1) + Real.log ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true) + 1)) + c₀)) +
      20 * q.g * (4 * (3 * 10 ^ 11 * (bitB bd (2 ^ q.kx) M msrc
          (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) ^ 3 + 2 * Fintype.card Zs +
        Fintype.card Xa) + 3) ∧
    (Fintype.card (MinSW 0 q.kx Zs Xa) : ℝ) ≤
      7 * 10 ^ 11 * (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε +
        1) ^ 3 + 4 * Fintype.card Zs + 2 * Fintype.card Xa ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query))) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * q.g * ((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) *
        (c₁ * Real.log (((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) + 1) /
          (q.params.nu / 3)) + c₀)) +
        20 * q.g * (4 * (2 * q.kx + 2 * Fintype.card Zs + Fintype.card Xa + 17 : ℕ) + 3) ∧
    Fintype.card (MinSW 0 q.kx Zs Xa) =
      4 * q.kx + 4 * Fintype.card Zs + 2 * Fintype.card Xa + 35 ∧
    qOf q.s q.T q.etaH q.etaD q.g q.ε = ImprovedODEQueryBudget.logBudget q.g q.ε ∧
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query))) j, i.Valid) ∧
      ∀ gt, NInstr.gate gt ∈ trialN (synthPrep hS (q.params.nu / 3)
        (zprepC (srcRot q.T q.r₀ q.rb) srcC :
          List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query))) j → GateOf 𝒢 gt) ∧
    (∀ c : Query → Bool, ((nprotocol (synthPrep hS (q.params.nu / 3)
        (zprepC (srcRot q.T q.r₀ q.rb) srcC :
          List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query))) q.g hq.g_ge).worstCost
        (wCallN c) : ℝ) ≤ 40 * q.g * (nCallsN c (srcC false) + nCallsN c (srcC true) : ℕ)) ∧
    (∀ c : Query → Bool, nCallsN c (srcC false) = 0 → nCallsN c (srcC true) = 0 →
      (nprotocol (synthPrep hS (q.params.nu / 3) (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query))) q.g hq.g_ge).worstCost
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
      NOutcome (synthPrep hS (q.params.nu / 3) (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query))) q.g q.ε hq.g_ge
        (prims (R := ℂ) D en x) (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  obtain ⟨hTr, -, -, hWC, -, hWGlog, -, hout⟩ := ZeroTimeGateODE.native_ode_solver_zero_trials
    (S := Fin q.kx) (Zs := Zs) (Z := Empty) (Y := PY q.kx q.b) (J := Query) (X := Xa) hS hadj hzt
    0 0 0 0 0 0 0 0 0 0 q.T q.g q.ε q.r₀ q.rb hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half
    hq.r₀_nonneg hq.rb_nonneg hq.B_pos srcC hsrcV
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hnu : q.params.nu = ImprovedODEQueryBudget.precision q.g q.ε := rfl
  have hν : 0 < q.params.nu := by
    rw [hnu]
    exact ImprovedODEQueryBudget.precision_pos q.g q.ε hq.g_ge hq.ε_pos
  have hν1 : q.params.nu ≤ 1 / 10000 := by
    rw [hnu]
    exact ImprovedODEQueryBudget.precision_le_one_ten_thousandth q.g q.ε hq.g_ge hε1
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg hq.g_ge hq.ε_pos hε1
  have hQg : 0 ≤ qOf q.s q.T q.etaH q.etaD q.g q.ε * q.g := by positivity
  have hkx := kx_le_bitB bd q.kx M msrc hQg hq.ε_pos hε1
  have hB0 := bitB_nonneg bd (2 ^ q.kx) M msrc hQg hq.ε_pos hε1
  have hcard : Fintype.card (MinSW 0 q.kx Zs Xa) =
      4 * q.kx + 4 * Fintype.card Zs + 2 * Fintype.card Xa + 35 := by
    rw [card_MinSW]
    ring
  -- the explicit count
  have hexp : ((nprotocol (synthPrep hS (q.params.nu / 3) (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query))) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * q.g * ((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) *
        (c₁ * Real.log (((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) + 1) /
          (q.params.nu / 3)) + c₀)) +
        20 * q.g * (4 * (2 * q.kx + 2 * Fintype.card Zs + Fintype.card Xa + 17 : ℕ) + 3) := by
    have h := hWGlog c₀ c₁ hc₀ hc₁ hlen
    refine h.trans (le_of_eq ?_)
    have hn := tested_minS 0 q.kx Zs Xa
    rw [mul_zero, zero_add] at hn
    have hn' : ((Fintype.card (GateODE.AW 0 0 0 0 0 0 0) : ℕ) : ℝ) +
        (Fintype.card (XW Empty 0 0 0) : ℕ) +
        (Fintype.card (SX Zs (ZeroTimeGateODE.zPool 0 0 0 0 0 0 0 (Fin q.kx) Zs Empty 0 0 0)
          Xa) : ℕ) + (Fintype.card (Fin q.kx) : ℕ) =
        ((2 * q.kx + 2 * Fintype.card Zs + Fintype.card Xa + 17 : ℕ) : ℝ) := by
      exact_mod_cast hn
    rw [hn']
    rfl
  have hQz := qOf_zero (s := (q.s : ℝ)) (g := q.g) (ε := q.ε) hq.etaH_nonneg hq.etaD_nonneg hz
  have hno : ∀ c : Query → Bool, nCallsN c (srcC false) = 0 → nCallsN c (srcC true) = 0 →
      (nprotocol (synthPrep hS (q.params.nu / 3) (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query))) q.g hq.g_ge).worstCost
        (wCallN c) = 0 := by
    intro c h0 h1
    have h : ((nprotocol (synthPrep hS (q.params.nu / 3) (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query))) q.g hq.g_ge).worstCost
        (wCallN c) : ℝ) ≤ 40 * q.g * (nCallsN c (srcC false) + nCallsN c (srcC true) : ℕ) :=
      hWC c
    rw [h0, h1] at h
    have h' : ((nprotocol (synthPrep hS (q.params.nu / 3) (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query))) q.g hq.g_ge).worstCost
        (wCallN c) : ℝ) ≤ 0 := by simpa using h
    exact_mod_cast le_antisymm h' (Nat.cast_nonneg _)
  have hout' : ∀ x : X,
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
      NOutcome (synthPrep hS (q.params.nu / 3) (zprepC (srcRot q.T q.r₀ q.rb) srcC :
        List (NInstr (MinW 0 q.kx Zs) (PY q.kx q.b) Query))) q.g q.ε hq.g_ge
        (prims (R := ℂ) D en x) (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
    intro x hrH hrD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hBud
    have ht := ZeroTimeGateODE.binary_target_zero q hq hz D en x hrH hrD x0 v
    rw [ht] at hne hBud ⊢
    rw [hnu] at hbud
    exact hout (prims (R := ℂ) D en x) Jsrc x0 v ζs (prims_isUnitary D en x) hJ hζs hsrc hbud
      hx0 hv hpx hpv hne hBud
  have hL : Real.log ((((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) : ℝ) + 1) /
      (q.params.nu / 3)) ≤
      64 * (bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε + 1) +
        Real.log ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true) + 1) :=
    log_trial_le bd (2 ^ q.kx) M msrc (by positivity) (by push_cast; ring) hq.g_ge hq.ε_pos hε1
      hQ1
  have hL0 : 0 ≤ Real.log ((((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) : ℝ) + 1) /
      (q.params.nu / 3)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ ((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) : ℝ) :=
      Nat.cast_nonneg _
    linarith
  generalize hB : bitB bd (2 ^ q.kx) M msrc (qOf q.s q.T q.etaH q.etaD q.g q.ε) q.g q.ε = B
    at hkx hB0 hL ⊢
  generalize hQ : qOf q.s q.T q.etaH q.etaD q.g q.ε = Q at hQ1 hQg hQz ⊢
  refine ⟨hexp.trans ?_, ?_, hexp, hcard, hQz, hTr, hWC, hno, hout'⟩
  · -- the released form
    generalize Real.log ((((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) : ℝ) + 1) /
        (q.params.nu / 3)) = L at hL hL0
    have hG0 : (0 : ℝ) ≤ (nGatesN (srcC false) : ℝ) + nGatesN (srcC true) := by positivity
    have hlog0 : 0 ≤ Real.log ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true) + 1) :=
      Real.log_nonneg (by linarith)
    have hY3 : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by linarith)
    have hY3' : B + 1 ≤ (B + 1) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have hQY : 1 ≤ Q * (B + 1) ^ 3 := one_le_mul_of_one_le_of_one_le hQ1 hY3
    have hN : (((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) : ℝ)) ≤
        2 * 10 ^ 18 * Q * (B + 1) ^ 3 + ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true)) := by
      push_cast
      nlinarith
    have hF : c₁ * L + c₀ ≤
        c₁ * (64 * (B + 1) + Real.log ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true) + 1)) +
          c₀ := by
      have := mul_le_mul_of_nonneg_left hL hc₁
      linarith
    have hprod : (((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) : ℝ)) *
        (c₁ * L + c₀) ≤
        (2 * 10 ^ 18 * Q * (B + 1) ^ 3 + ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true))) *
          (c₁ * (64 * (B + 1) + Real.log ((nGatesN (srcC false) : ℝ) + nGatesN (srcC true) + 1)) +
            c₀) :=
      mul_le_mul hN hF (by positivity) (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 40 * q.g)
    have hn : (((2 * q.kx + 2 * Fintype.card Zs + Fintype.card Xa + 17 : ℕ) : ℝ)) ≤
        3 * 10 ^ 11 * (B + 1) ^ 3 + 2 * Fintype.card Zs + Fintype.card Xa := by
      push_cast
      nlinarith
    have h2 : 20 * q.g * (4 * (((2 * q.kx + 2 * Fintype.card Zs + Fintype.card Xa + 17 : ℕ) :
        ℝ)) + 3) ≤ 20 * q.g * (4 * (3 * 10 ^ 11 * (B + 1) ^ 3 + 2 * Fintype.card Zs +
          Fintype.card Xa) + 3) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  · -- the qubits
    rw [hcard]
    push_cast
    have hY3 : B + 1 ≤ (B + 1) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    nlinarith

end Trials

end

end SparseHamiltonian.GateRemarks.ODE
