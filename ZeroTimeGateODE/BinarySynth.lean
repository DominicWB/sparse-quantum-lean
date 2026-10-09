import ZeroTimeGateODE.SynthCombined
import ZeroTimeGateODE.Binary
import ZeroTimeGateODE.BinaryTime
import GateEfficientSynthesisTrials.Binary

/-!
# Binary data over a finite gate set, with the per-trial claim, for every `T ≥ 0`

The released finite-gate-set forms from binary data with the per-trial claim
(`GateSynthTrials.binary_ode_solver_trials`, `binary_ode_time_solver_trials`) synthesise the
released binary preparation with budget `ν/3`; they require `T > 0` and `η_H + η_D > 0`.  For
every `T ≥ 0` the same synthesis applies to the preparations `bprepC` and `btprepC` (direct
source assembly in the zero case): the synthesised preparation has the released synthesis counts
in terms of the counts of `bprepC q srcC` (resp. `btprepC q loadC wpC`), which are
`if <zero case> then <direct source assembly> else <released>`, and the guarantees `NOutcome`
under the released hypotheses on the input and the sources.

* `binary_ode_solver_nonneg_trials` (constant coefficients);
* `binary_ode_time_solver_nonneg_trials` (time-dependent coefficients).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth GateSynthTrials GateBinary
open GateBinaryODE (Pub mLift SZ4 card_SZ4)
open GateBinaryODETime (PubT HsT LsT)
open NativeSparseBlockEncoding (Data Query)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

section Binary

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Dissipative ODE from binary sparse data over a finite gate set, with the per-trial claim,
for every `T ≥ 0`, constant coefficients** (Theorem `ode:thm:gates` with its remark on zero time
and a known zero generator).

For binary public data with `BPublicOK0 q` and the synthesis hypotheses, the protocol
`nprotocol (synthPrep hS (ν/3) (bprepC q srcC)) g` on the released trial register: every trial
consists of valid gates of `𝒢` and primitive calls; the unsynthesised preparation has the counts
of `binary_ode_solver_nonneg`; the synthesised preparation has at most `N len(ν/3/(N+1))` gates
and exactly the calls of `bprepC q srcC` (`N` its gates); every history makes at most `40 g` times
these calls and uses at most `40 g N_S + 20 g (4 n + 3)` gates, and at most
`40 g N (c₁ log((N+1)/(ν/3)) + c₀) + 20 g (4 n + 3)` gates if `len ζ ≤ c₁ log(1/ζ) + c₀`; the
trial register has the released qubit count.  For every input and instance satisfying the
hypotheses of the released `GateBinaryODE.binary_ode_solver` (for every `T ≥ 0`), the protocol
has the guarantees `NOutcome` against the solution `x(T)` of `x' = -M̂ x + b`. -/
theorem binary_ode_solver_nonneg_trials (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) (q : Pub) (hq : BPublicOK0 q)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) j →
        GateOf 𝒢 g) ∧
    nGatesN (bprepC q srcC) ≤
      (if BZeroCase q then nGatesN (srcC false) + nGatesN (srcC true) + 2
      else q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
        6 * q.params.d * (2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
          (2 * q.ar.bP + q.ar.bT + 1)) + nGatesN (srcC false) + nGatesN (srcC true)) ∧
    (∀ c : Query → Bool, nCallsN c (bprepC q srcC) ≤
      (if BZeroCase q then nCallsN c (srcC false) + nCallsN c (srcC true)
      else 12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c (srcC false) + nCallsN c (srcC true))) ∧
    nGatesN (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) ≤
      nGatesN (bprepC q srcC) * len (q.params.nu / 3 / (nGatesN (bprepC q srcC) + 1)) ∧
    (∀ c : Query → Bool, nCallsN c (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) =
      nCallsN c (bprepC q srcC)) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g hq.g_ge).worstCost
        (wCallN c) : ℝ) ≤ 40 * q.g * nCallsN c (bprepC q srcC)) ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * q.g * nGatesN (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) +
        20 * q.g * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card (SX Zs (nPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
            Xa) + q.kx) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g hq.g_ge).worstCost
          wGateN : ℝ) ≤
        40 * q.g * (nGatesN (bprepC q srcC) *
          (c₁ * Real.log ((nGatesN (bprepC q srcC) + 1) / (q.params.nu / 3)) + c₀)) +
        20 * q.g * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card (SX Zs (nPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
            Xa) + q.kx) + 3)) ∧
    Fintype.card (SNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) =
      q.kx + 2 * (Fintype.card q.params.W +
        (6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3) +
        (Fintype.card Zs + 1 + nPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A +
          Fintype.card Xa)) + q.kx + 1 ∧
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
      24 * (q.params.d : ℝ) * q.ζ + 2 * ζs ≤ q.params.nu →
      ‖x0‖ = q.r₀ → ‖v‖ = q.rb →
      (x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = unitDirection x0) →
      (v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = unitDirection v) →
      ODEConstantForcing.solution (-mLift D en x) x0 v q.T ≠ 0 →
      q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en x) x0 v q.T‖ →
      NOutcome (synthPrep hS (q.params.nu / 3) (bprepC q srcC)) q.g q.ε hq.g_ge
        (prims (R := ℂ) D en x) (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  obtain ⟨hV, hG, hC, -, -, -, -⟩ := binary_ode_solver_nonneg q hq D en hrange hdec srcC hsrcV
  have hprepV : ∀ i ∈ bprepC q srcC, i.Valid := fun i hi => hV 0 i (List.mem_append_left _ hi)
  have hnu : q.params.nu = ImprovedODEQueryBudget.precision q.g q.ε := rfl
  have hν : 0 < q.params.nu := by
    rw [hnu]
    exact ImprovedODEQueryBudget.precision_pos q.g q.ε hq.g_ge hq.ε_pos
  have hν1 : q.params.nu ≤ 1 / 10000 := by
    rw [hnu]
    exact ImprovedODEQueryBudget.precision_le_one_ten_thousandth q.g q.ε hq.g_ge
      (hq.ε_half.trans (by norm_num))
  have hη : 0 < q.params.nu / 3 := by positivity
  have hη1 : q.params.nu / 3 ≤ 1 := by linarith
  obtain ⟨hSG, hSC⟩ := synthPrep_counts hS hη _ hprepV
  obtain ⟨hWC, hWG⟩ := synth_protocol_worst hS hη _ hprepV q.g hq.g_ge
  refine ⟨fun j => ⟨trialS_valid hS hη _ hprepV j, trialS_gateOf hS hadj hzt hη _ hprepV j⟩,
    hG, hC, hSG, hSC, hWC, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_fin] at hWG
    exact hWG
  · intro c₀ c₁ hc₀ hc₁ hlen
    have h := synth_protocol_worst_log hS hη hη1 _ hprepV q.g hq.g_ge hc₀ hc₁ hlen
    rw [Fintype.card_fin] at h
    exact h
  · rw [card_SWO, card_SZ4, Fintype.card_fin]
  · intro x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hB
    by_cases hz : BZeroCase q
    · have ht := binary_target_zero q hq hz D en x hrH hrD x0 v
      rw [ht] at hne hB ⊢
      have hd : 0 ≤ 24 * (q.params.d : ℝ) * q.ζ :=
        mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hq.ζ_pos.le
      rw [hnu] at hbud
      obtain ⟨-, -, -, -, -, -, -, hout⟩ := native_ode_solver_zero_trials (S := Fin q.kx)
        (Zs := Zs) (Z := SZ4 q.kx q.b) (Y := PY q.kx q.b) (J := Query) hS hadj hzt q.params.a
        q.params.m q.params.r q.params.K q.params.k q.params.l q.params.f q.ar.bT q.ar.bP q.ar.A
        q.T q.g q.ε q.r₀ q.rb hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hq.r₀_nonneg hq.rb_nonneg
        hq.B_pos srcC hsrcV
      rw [bprepC, if_pos hz]
      exact hout (prims (R := ℂ) D en x) Jsrc x0 v ζs (prims_isUnitary D en x) hJ hζs hsrc
        (by linarith) hx0 hv hpx hpv hne hB
    · obtain ⟨-, -, -, -, -, -, -, -, -, hout⟩ :=
        binary_ode_solver_trials hS hadj hzt q (bpublicOK_of hq hz) D en hrange hdec srcC hsrcV
      rw [bprepC, if_neg hz]
      exact hout x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hB

/-- **Dissipative ODE from time-indexed binary sparse data over a finite gate set, with the
per-trial claim, for every `T ≥ 0`** (Theorem `ode:thm:gates`, time-dependent part, with its
remark on zero time and a known zero generator).

For binary public data with `BTPublicOK0 q` and the synthesis hypotheses, the protocol
`nprotocol (synthPrep hS (ν/3) (btprepC q loadC wpC)) (2g)` on the released trial register: every
trial consists of valid gates of `𝒢` and primitive calls; the unsynthesised preparation has the
counts of `binary_ode_time_solver_nonneg`; the synthesised preparation has at most
`N len(ν/3/(N+1))` gates and exactly the calls of `btprepC q loadC wpC`; every history makes at
most `40 · 2g` times these calls and uses at most `40 · 2g N_S + 20 · 2g (4 n + 3)` gates, and at
most `40 · 2g N (c₁ log((N+1)/(ν/3)) + c₀) + 20 · 2g (4 n + 3)` gates if
`len ζ ≤ c₁ log(1/ζ) + c₀`; the trial register has the released qubit count.  For every input
and instance satisfying the hypotheses of the released `GateBinaryODETime.binary_ode_time_solver`
(for every `T ≥ 0`), the protocol has the guarantees `NOutcome` against `x(T)`. -/
theorem binary_ode_time_solver_nonneg_trials (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) (q : PubT) (hq : BTPublicOK0 q)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) j →
        GateOf 𝒢 g) ∧
    nGatesN (btprepC q loadC wpC) ≤
      (if BTZeroCase q then nGatesN loadC + 2 * nGatesN wpC
      else q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
        6 * q.params.d * (2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
          (2 * q.ar.bP + q.ar.bT + 1)) + nGatesN loadC + 2 * nGatesN wpC) ∧
    (∀ c : Query → Bool, nCallsN c (btprepC q loadC wpC) ≤
      (if BTZeroCase q then nCallsN c loadC + 2 * nCallsN c wpC
      else 12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c loadC + 2 * nCallsN c wpC)) ∧
    nGatesN (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) ≤
      nGatesN (btprepC q loadC wpC) *
        len (q.params.nu / 3 / (nGatesN (btprepC q loadC wpC) + 1)) ∧
    (∀ c : Query → Bool, nCallsN c (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) =
      nCallsN c (btprepC q loadC wpC)) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
        40 * q.params.ratio * nCallsN c (btprepC q loadC wpC)) ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      40 * q.params.ratio * nGatesN (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
            q.ar.A) Xa) + q.kx) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio
          (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
        40 * q.params.ratio * (nGatesN (btprepC q loadC wpC) *
          (c₁ * Real.log ((nGatesN (btprepC q loadC wpC) + 1) / (q.params.nu / 3)) + c₀)) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
            q.ar.A) Xa) + q.kx) + 3)) ∧
    Fintype.card (STW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A Xa) =
      q.kx + 2 * (Fintype.card q.params.W +
        (6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3) +
        (Fintype.card Zs + 1 + tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A +
          Fintype.card Xa)) + q.kx + 1 ∧
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
      24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu →
      q.Rest D en x Jl Wp G bf xs bs βG δG βb δb bmax →
      NOutcome (synthPrep hS (q.params.nu / 3) (btprepC q loadC wpC)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (xs q.T) := by
  obtain ⟨hV, hG, hC, -, -, -, -⟩ :=
    binary_ode_time_solver_nonneg q hq D en hrange hdec loadC hloadV wpC hwpV
  have hprepV : ∀ i ∈ btprepC q loadC wpC, i.Valid :=
    fun i hi => hV 0 i (List.mem_append_left _ hi)
  have hν : 0 < q.params.nu := q.params.nu_pos hq.g_ge hq.ε_pos
  have hν1 : q.params.nu ≤ 1 := q.params.nu_le_one hq.g_ge (hq.ε_half.trans (by norm_num))
  have hη : 0 < q.params.nu / 3 := by positivity
  have hη1 : q.params.nu / 3 ≤ 1 := by linarith
  obtain ⟨hSG, hSC⟩ := synthPrep_counts hS hη _ hprepV
  obtain ⟨hWC, hWG⟩ :=
    synth_protocol_worst hS hη _ hprepV q.params.ratio (q.params.ratio_ge hq.g_ge)
  refine ⟨fun j => ⟨trialS_valid hS hη _ hprepV j, trialS_gateOf hS hadj hzt hη _ hprepV j⟩,
    hG, hC, hSG, hSC, hWC, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_fin] at hWG
    exact hWG
  · intro c₀ c₁ hc₀ hc₁ hlen
    have h := synth_protocol_worst_log hS hη hη1 _ hprepV q.params.ratio
      (q.params.ratio_ge hq.g_ge) hc₀ hc₁ hlen
    rw [Fintype.card_fin] at h
    exact h
  · rw [card_SWO, card_SZ4, Fintype.card_fin]
  · intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
    by_cases hz : BTZeroCase q
    · have hp := btparams_ok0 hq
      have hI := binary_tzInstanceOK q hq D en x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb
        δb bmax hR
      have hd : 0 ≤ 24 * (q.params.d : ℝ) * q.ζ :=
        mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hq.ζ_pos.le
      obtain ⟨-, -, -, -, -, -, -, hout⟩ := native_ode_time_solver_zero_trials (S := Fin q.kx)
        (Zs := Zs) (Z := SZ4 q.kx q.b) (Y := Fin q.m ⊕ PY q.kx q.b) (J := Query) hS hadj hzt
        q.params q.params.a q.params.m q.params.r q.params.K q.params.l q.params.f q.ar.bT
        q.ar.bP q.ar.A hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hp.lamH_nonneg hp.lamD_nonneg
        (btzeroCase_params hq hz) loadC hloadV wpC hwpV
      rw [btprepC, if_pos hz]
      exact hout (primsT (R := ℂ) D en x) Jl Wp (HsT D en x) (LsT D en x) G bf xs bs βG δG βb δb
        bmax ζs (primsT_isUnitary D en x) hζs hload hwp (by linarith) hI
    · obtain ⟨-, -, -, -, -, -, -, -, -, hout⟩ := binary_ode_time_solver_trials hS hadj hzt q
        (btpublicOK_of hq hz) D en hrange hdec loadC hloadV wpC hwpV
      rw [btprepC, if_neg hz]
      exact hout x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud
        hR

end Binary

end

end SparseHamiltonian.ZeroTimeGateODE
