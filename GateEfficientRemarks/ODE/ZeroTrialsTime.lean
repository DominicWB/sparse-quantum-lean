import GateEfficientRemarks.ODE.ZeroBudgetTime

/-!
# Zero time or a known zero generator over a finite gate set, time-dependent coefficients

The finite-gate-set form of `binary_ode_time_budget_bits_zero` (equations `ode:eq:gate-main` and
`ode:eq:gate-space` of Theorem `ode:thm:gates`, time-dependent part, with its remark on zero time
and a known zero generator) with the per-trial claim (only the preparation synthesised,
`GateSynthTrials.synthPrep hS (ν/3)`, `ν = (ε/2)/(10⁴ · 2g)`), as in the released
`GateBitBudget.binary_ode_time_budget_trials_bits` and the zero-case form
`ZeroTimeGateODE.native_ode_time_solver_zero_trials`: on the trial register `MinSW m k_x Zs Xa` of
the minimal register, for time-indexed binary data in the zero case (`BTZeroCase`),

* `binary_ode_time_budget_trials_bits_zero`: in every history at most
  `80 g (2·10¹⁸ q*' (𝔟'+1)³ + G_src) (c₁ (64 (𝔟'+1) + log(G_src+1)) + c₀) +
  40 g (4 (3·10¹¹ (𝔟'+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢` on at most
  `7·10¹¹ (𝔟'+1)³ + 4 |Zs| + 2 |Xa|` qubits (the bounds of the released form with the same
  constants; internal `q*'` of `(2g, ε/2)`, `𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε`,
  `G_src = |loadC| + 2 |wpC|`); the explicit counts
  `80 g G_src (c₁ log((G_src+1)/(ν/3)) + c₀) + 40 g (4 (2 m + 2 k_x + 2 |Zs| + |Xa| + 17) + 3)` and
  `4 k_x + 4 m + 4 |Zs| + 2 |Xa| + 35` qubits; valid trials of `𝒢`; no call of a kind that the
  supplied circuits do not call; `GateNative.NOutcome` against `x(T)` under the zero-case
  conditions.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateBinary GateSynth GateSynthTrials
open ZeroTimeGateODE (tzprepC BTPublicOK0 BTZeroCase)
open GateBinaryODETime (PubT HsT LsT)
open SparseHamiltonian.GateBitBudget (bitB bitB_nonneg)
open GateODEBudget (qOf)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct BigOperators

section Trials

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Equations `ode:eq:gate-main` and `ode:eq:gate-space` in `𝔟` over a finite gate set, with
the per-trial claim, for zero time or a known zero generator, time-dependent coefficients**
(Theorem `ode:thm:gates`, time-dependent part, with its remark).

Under the synthesis hypotheses of `binary_ode_budget_trials_bits_zero`, for time-indexed binary
public data with `BTPublicOK0 q` in the zero case, valid loading and weight-preparation circuits
and any `b_data`, with the internal `q*' = qOf s T η_H η_D (2g) (ε/2)` (`= log(4·10⁴ g/ε)`) and
`𝔟' = bitB b_data (2^k_x) (2^m) (2^m) q*' g ε`, the protocol
`nprotocol (synthPrep hS (ν/3) (tzprepC loadC wpC)) (2g)` on the trial register
`MinSW m k_x Zs Xa`: in every history at most
`80 g (2·10¹⁸ q*' (𝔟'+1)³ + G_src) (c₁ (64 (𝔟'+1) + log(G_src+1)) + c₀) +
40 g (4 (3·10¹¹ (𝔟'+1)³ + 2 |Zs| + |Xa|) + 3)` gates of `𝒢` (`G_src = |loadC| + 2 |wpC|`) and at
most `7·10¹¹ (𝔟'+1)³ + 4 |Zs| + 2 |Xa|` qubits (the bounds of
`GateBitBudget.binary_ode_time_budget_trials_bits`); in fact at most
`80 g G_src (c₁ log((G_src+1)/(ν/3)) + c₀) + 40 g (4 (2 m + 2 k_x + 2 |Zs| + |Xa| + 17) + 3)`
gates on exactly `4 k_x + 4 m + 4 |Zs| + 2 |Xa| + 35` qubits; every trial consists of valid
gates of `𝒢` and primitive calls; every history makes at most
`80 g (calls_c(loadC) + 2 calls_c(wpC))` calls of every kind `c`, so none of a kind that the
supplied circuits do not call; and under the zero-case conditions (energy and accretivity
promises of every sample, circuits within `ζs`, `3 ζs ≤ ν`, `PubT.Rest`) the protocol has the
guarantees `NOutcome` against `x(T)`. -/
theorem binary_ode_time_budget_trials_bits_zero (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hlen : ∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀)
    (bd : ℕ) (q : PubT) (hq : BTPublicOK0 q) (hz : BTZeroCase q)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    ((nprotocol (synthPrep hS (q.params.nu / 3) (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query))) q.params.ratio
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
    (Fintype.card (MinSW q.params.m q.kx Zs Xa) : ℝ) ≤
      7 * 10 ^ 11 * (bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
          (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε + 1) ^ 3 +
        4 * Fintype.card Zs + 2 * Fintype.card Xa ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query))) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * ((nGatesN loadC + 2 * nGatesN wpC : ℕ) *
        (c₁ * Real.log (((nGatesN loadC + 2 * nGatesN wpC : ℕ) + 1) / (q.params.nu / 3)) + c₀)) +
        40 * q.g * (4 * (2 * q.m + 2 * q.kx + 2 * Fintype.card Zs + Fintype.card Xa + 17 : ℕ) +
          3) ∧
    Fintype.card (MinSW q.params.m q.kx Zs Xa) =
      4 * q.kx + 4 * q.m + 4 * Fintype.card Zs + 2 * Fintype.card Xa + 35 ∧
    qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) =
      ImprovedODEQueryBudget.logBudget (2 * q.g) (q.ε / 2) ∧
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query))) j, i.Valid) ∧
      ∀ gt, NInstr.gate gt ∈ trialN (synthPrep hS (q.params.nu / 3) (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query))) j →
          GateOf 𝒢 gt) ∧
    (∀ c : Query → Bool, ((nprotocol (synthPrep hS (q.params.nu / 3) (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query))) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      80 * q.g * (nCallsN c loadC + 2 * nCallsN c wpC : ℕ)) ∧
    (∀ c : Query → Bool, nCallsN c loadC = 0 → nCallsN c wpC = 0 →
      (nprotocol (synthPrep hS (q.params.nu / 3) (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query))) q.params.ratio
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
      NOutcome (synthPrep hS (q.params.nu / 3) (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query))) q.params.ratio
        q.ε (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (xs q.T) := by
  have hp := ZeroTimeGateODE.btparams_ok0 hq
  obtain ⟨hTr, -, -, hWC, -, hWGlog, -, hout⟩ :=
    ZeroTimeGateODE.native_ode_time_solver_zero_trials (S := Fin q.kx) (Zs := Zs) (Z := Empty)
      (Y := Fin q.m ⊕ PY q.kx q.b) (J := Query) (X := Xa) hS hadj hzt q.params 0 0 0 0 0 0 0 0 0
      hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hp.lamH_nonneg hp.lamD_nonneg
      (ZeroTimeGateODE.btzeroCase_params hq hz) loadC hloadV wpC hwpV
  have hr : q.params.ratio = 2 * q.g := rfl
  have hm : q.params.m = q.m := rfl
  have hε1 : q.ε ≤ 1 := hq.ε_half.trans (by norm_num)
  have hg0 : 0 ≤ q.g := le_trans zero_le_one hq.g_ge
  have hν : 0 < q.params.nu := q.params.nu_pos hq.g_ge hq.ε_pos
  have hcard : Fintype.card (MinSW q.params.m q.kx Zs Xa) =
      4 * q.kx + 4 * q.m + 4 * Fintype.card Zs + 2 * Fintype.card Xa + 35 := by
    rw [card_MinSW, hm]
  -- the explicit count
  have hexp : ((nprotocol (synthPrep hS (q.params.nu / 3) (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query))) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      80 * q.g * ((nGatesN loadC + 2 * nGatesN wpC : ℕ) *
        (c₁ * Real.log (((nGatesN loadC + 2 * nGatesN wpC : ℕ) + 1) / (q.params.nu / 3)) + c₀)) +
        40 * q.g * (4 * (2 * q.m + 2 * q.kx + 2 * Fintype.card Zs + Fintype.card Xa + 17 : ℕ) +
          3) := by
    have h := hWGlog c₀ c₁ hc₀ hc₁ hlen
    refine h.trans (le_of_eq ?_)
    have hn := tested_minS q.params.m q.kx Zs Xa
    rw [hm] at hn
    have hn' : ((Fintype.card (GateODE.AW 0 0 0 0 q.params.m 0 0) : ℕ) : ℝ) +
        (Fintype.card (XW Empty 0 0 0) : ℕ) +
        (Fintype.card (SX Zs
          (ZeroTimeGateODE.zPool 0 0 0 0 q.params.m 0 0 (Fin q.kx) Zs Empty 0 0 0) Xa) : ℕ) +
        (Fintype.card (Fin q.kx) : ℕ) =
        ((2 * q.m + 2 * q.kx + 2 * Fintype.card Zs + Fintype.card Xa + 17 : ℕ) : ℝ) := by
      exact_mod_cast hn
    rw [hn', hr]
    ring
  have hQz := qOf_zero (s := (q.s : ℝ)) (g := 2 * q.g) (ε := q.ε / 2) hq.etaH_nonneg
    hq.etaD_nonneg hz
  have hno : ∀ c : Query → Bool, nCallsN c loadC = 0 → nCallsN c wpC = 0 →
      (nprotocol (synthPrep hS (q.params.nu / 3) (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query))) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) = 0 := by
    intro c h0 h1
    have h := hWC c
    rw [h0, h1] at h
    have h' : ((nprotocol (synthPrep hS (q.params.nu / 3) (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query))) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤ 0 := by simpa using h
    exact_mod_cast le_antisymm h' (Nat.cast_nonneg _)
  have hWC' : ∀ c : Query → Bool, ((nprotocol (synthPrep hS (q.params.nu / 3)
      (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query))) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
      80 * q.g * (nCallsN c loadC + 2 * nCallsN c wpC : ℕ) := by
    intro c
    refine (hWC c).trans (le_of_eq ?_)
    rw [hr]
    ring
  have hout' : ∀ x : X,
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
      NOutcome (synthPrep hS (q.params.nu / 3) (tzprepC loadC wpC :
        List (NInstr (MinW q.params.m q.kx Zs) (Fin q.m ⊕ PY q.kx q.b) Query))) q.params.ratio
        q.ε (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (xs q.T) := by
    intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
    have hI := ZeroTimeGateODE.binary_tzInstanceOK q hq D en x hrH hcH hrD hcD hPSD Jl Wp G bf
      xs bs βG δG βb δb bmax hR
    exact hout (primsT (R := ℂ) D en x) Jl Wp (HsT D en x) (LsT D en x) G bf xs bs βG δG βb δb
      bmax ζs (primsT_isUnitary D en x) hζs hload hwp hbud hI
  -- the word budget
  have hQ1 : 1 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) :=
    one_le_qOf hq.T_nonneg hq.etaH_nonneg hq.etaD_nonneg (by linarith [hq.g_ge])
      (by linarith [hq.ε_pos]) (by linarith)
  have hQg : 0 ≤ qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) * q.g := by positivity
  have hw := kx_add_le_bitB bd q.kx q.m (2 ^ q.m) hQg hq.ε_pos hε1
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
    rw [le_div_iff₀ (by positivity)]
    have : (0 : ℝ) ≤ ((nGatesN loadC + 2 * nGatesN wpC : ℕ) : ℝ) := Nat.cast_nonneg _
    have hν1 : q.params.nu ≤ 1 := q.params.nu_le_one hq.g_ge hε1
    linarith
  generalize hB : bitB bd (2 ^ q.kx) (2 ^ q.m) (2 ^ q.m)
    (qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2)) q.g q.ε = B at hw hB0 hL ⊢
  generalize hQ : qOf q.s q.T q.etaH q.etaD (2 * q.g) (q.ε / 2) = Q at hQ1 hQg hQz ⊢
  refine ⟨hexp.trans ?_, ?_, hexp, hcard, hQz, hTr, hWC', hno, hout'⟩
  · -- the released form
    generalize Real.log ((((nGatesN loadC + 2 * nGatesN wpC : ℕ) : ℝ) + 1) /
        (q.params.nu / 3)) = L at hL hL0
    have hG0 : (0 : ℝ) ≤ (nGatesN loadC : ℝ) + 2 * nGatesN wpC := by positivity
    have hlog0 : 0 ≤ Real.log ((nGatesN loadC : ℝ) + 2 * nGatesN wpC + 1) :=
      Real.log_nonneg (by linarith)
    have hY3 : 1 ≤ (B + 1) ^ 3 := one_le_pow₀ (by linarith)
    have hY3' : B + 1 ≤ (B + 1) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
    have hQY : 1 ≤ Q * (B + 1) ^ 3 := one_le_mul_of_one_le_of_one_le hQ1 hY3
    have hN : (((nGatesN loadC + 2 * nGatesN wpC : ℕ) : ℝ)) ≤
        2 * 10 ^ 18 * Q * (B + 1) ^ 3 + ((nGatesN loadC : ℝ) + 2 * nGatesN wpC) := by
      push_cast
      nlinarith
    have hF : c₁ * L + c₀ ≤
        c₁ * (64 * (B + 1) + Real.log ((nGatesN loadC : ℝ) + 2 * nGatesN wpC + 1)) + c₀ := by
      have := mul_le_mul_of_nonneg_left hL hc₁
      linarith
    have hprod : (((nGatesN loadC + 2 * nGatesN wpC : ℕ) : ℝ)) * (c₁ * L + c₀) ≤
        (2 * 10 ^ 18 * Q * (B + 1) ^ 3 + ((nGatesN loadC : ℝ) + 2 * nGatesN wpC)) *
          (c₁ * (64 * (B + 1) + Real.log ((nGatesN loadC : ℝ) + 2 * nGatesN wpC + 1)) + c₀) :=
      mul_le_mul hN hF (by positivity) (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ 80 * q.g)
    have hn : (((2 * q.m + 2 * q.kx + 2 * Fintype.card Zs + Fintype.card Xa + 17 : ℕ) : ℝ)) ≤
        3 * 10 ^ 11 * (B + 1) ^ 3 + 2 * Fintype.card Zs + Fintype.card Xa := by
      push_cast
      nlinarith
    have h2 : 40 * q.g * (4 * (((2 * q.m + 2 * q.kx + 2 * Fintype.card Zs + Fintype.card Xa +
        17 : ℕ) : ℝ)) + 3) ≤ 40 * q.g * (4 * (3 * 10 ^ 11 * (B + 1) ^ 3 + 2 * Fintype.card Zs +
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
