import GateEfficientRemarks.ODE.SynthZero
import ZeroTimeGateODE.BinaryTime

/-!
# Time-indexed binary data over a finite gate set, every trial synthesised, for every `T ≥ 0`

The finite-gate-set forms of Theorem `ode:thm:gates` in this module are a partial formalisation of
its finite-set statement, under this package's format hypotheses: the manuscript states Theorem
`ode:thm:gates` over a finite gate set; the conformance endpoints count native gates.

The released time-dependent solver from time-indexed binary sparse data with every trial
synthesised (`GateBinaryODETime.binary_ode_time_solver_synth`, Theorem `ode:thm:gates`,
time-dependent part) requires `T > 0` and `η_H + η_D > 0` (`GateBinaryODETime.PubT.OK`). The
released library `ZeroTimeGateODE` gives, for every `T ≥ 0` (`BTPublicOK0`, with the released mesh
condition), the combined preparation

`btprepC q loadC wpC = if T = 0 ∨ η_H + η_D = 0 then tzprepC loadC wpC else q.prep loadC wpC`

on the released binary register (`BTZeroCase` the zero case). With every trial synthesised
(`GateSynth.sprotocol hS (ε/200)`, ratio `2g`):

* `binary_ode_time_solver_synth_zero`: in the zero case, the direct source assembly has exactly
  `|loadC| + 2 |wpC|` gates and the calls of the loading and weight-preparation circuits, the
  protocol makes no call of a kind of the time-indexed binary sparse oracles that these circuits
  do not call, and it has the guarantee `GateSynth.SOutcome` against `x(T)` under the energy and
  accretivity promises of every sample, circuits within `ζs`, `3 ζs ≤ ν` and the released remaining
  conditions `PubT.Rest` (`ZeroTimeGateODE.binary_tzInstanceOK`);
* `binary_ode_time_solver_synth_nonneg`: for every `T ≥ 0`, the conclusions of the released
  `GateBinaryODETime.binary_ode_time_solver_synth` with the counts of `btprepC`,
  `if BTZeroCase q then <direct source assembly> else <released>`, and `SOutcome` under the
  released hypotheses (those of `ZeroTimeGateODE.binary_ode_time_solver_nonneg`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth GateBinary
open ZeroTimeGateODE (btprepC tzprepC BTPublicOK0 BTZeroCase)
open GateBinaryODE (SZ4 card_SZ4)
open GateBinaryODETime (PubT HsT LsT)
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct BigOperators

section BinaryTime

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Zero time or a known zero generator from time-indexed binary sparse data over a finite
gate set, every trial synthesised** (partial formalisation, under this package's format hypotheses,
of the finite-set form of the remark of Theorem `ode:thm:gates`,
time-dependent part: direct source assembly, no matrix calls).

For binary public data with `BTPublicOK0 q` in the zero case `T = 0 ∨ η_H + η_D = 0`, with the
synthesis hypothesis `Synthesis 𝒢 Xa len`, the synthesised protocol
`sprotocol hS (ε/200) (btprepC q loadC wpC) (2g)` on the released binary register with `|Xa|`
ancillas: every synthesised trial consists of valid gates of `𝒢` and primitive calls; the
preparation (the direct source assembly) has `N = |loadC| + 2 |wpC|` gates and exactly
`calls_c(loadC) + 2 calls_c(wpC)` calls of every kind `c`; every history makes at most `40 · 2g`
times these calls, so no call of a time-indexed binary sparse oracle that the supplied circuits
do not call, and, if `len ζ ≤ c₁ log(1/ζ) + c₀`, uses at most
`(40 · 2g N + 20 · 2g (4 n + 3)) (c₁ log((10 · 2g N + 5 · 2g (4 n + 3) + 1)/(ε/200)) + c₀)` gates
of `𝒢`; the register has the released qubits plus `|Xa|`. For every input with the energy and
accretivity promises of every sample, loading and weight-preparation circuits within `ζs`,
`3 ζs ≤ ν` and the released remaining conditions `PubT.Rest`, the protocol has the guarantee
`SOutcome` against `x(T)`. -/
theorem binary_ode_time_solver_synth_zero (hS : Synthesis 𝒢 Xa len) (q : PubT)
    (hq : BTPublicOK0 q) (hz : BTZeroCase q) (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ synthBudget hS (q.ε / 200) (trialN (btprepC q loadC wpC) j), i.Valid) ∧
      ∀ g, NInstr.gate g ∈ synthBudget hS (q.ε / 200) (trialN (btprepC q loadC wpC) j) →
        GateOf 𝒢 g) ∧
    nGatesN (btprepC q loadC wpC) = nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ c : Query → Bool,
      nCallsN c (btprepC q loadC wpC) = nCallsN c loadC + 2 * nCallsN c wpC) ∧
    (∀ c : Query → Bool,
      ((sprotocol hS (q.ε / 200) (btprepC q loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
        40 * q.params.ratio * (nCallsN c loadC + 2 * nCallsN c wpC : ℕ)) ∧
    (∀ c : Query → Bool, nCallsN c loadC = 0 → nCallsN c wpC = 0 →
      (sprotocol hS (q.ε / 200) (btprepC q loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) = 0) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((sprotocol hS (q.ε / 200) (btprepC q loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
        (40 * q.params.ratio * (nGatesN loadC + 2 * nGatesN wpC : ℕ) +
          20 * q.params.ratio * (4 * (Fintype.card q.params.W +
            Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) + Fintype.card Zs + q.kx) +
              3)) *
        (c₁ * Real.log ((10 * q.params.ratio * (nGatesN loadC + 2 * nGatesN wpC : ℕ) +
          5 * q.params.ratio * (4 * (Fintype.card q.params.W +
            Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) + Fintype.card Zs + q.kx) +
              3) + 1) / (q.ε / 200)) + c₀)) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A ⊕ Xa) =
      q.kx + 2 * (Fintype.card q.params.W +
        (6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3) + Fintype.card Zs) + q.kx + 1 +
        Fintype.card Xa ∧
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
      SOutcome (sprotocol hS (q.ε / 200) (btprepC q loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)) q.ε (primsT (R := ℂ) D en x) (xs q.T) := by
  have hp := ZeroTimeGateODE.btparams_ok0 hq
  obtain ⟨hV, hG, hC, hWC, hno, hWG, hcard, hout⟩ := native_ode_time_solver_synth_zero
    (S := Fin q.kx) (Zs := Zs) (Z := SZ4 q.kx q.b) (Y := Fin q.m ⊕ PY q.kx q.b) (J := Query)
    (X := Xa) hS q.params q.params.a q.params.m q.params.r q.params.K q.params.l q.params.f
    q.ar.bT q.ar.bP q.ar.A hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hp.lamH_nonneg hp.lamD_nonneg
    (ZeroTimeGateODE.btzeroCase_params hq hz) loadC hloadV wpC hwpV
  have hb : btprepC q loadC wpC = tzprepC loadC wpC := by
    rw [btprepC, if_pos hz]
  rw [hb]
  refine ⟨hV, hG, hC, hWC, hno, ?_, ?_, ?_⟩
  · intro c₀ c₁ hc₀ hc₁ hlen
    have h := hWG c₀ c₁ hc₀ hc₁ hlen
    rw [Fintype.card_fin] at h
    exact h
  · rw [card_SZ4, Fintype.card_fin] at hcard
    exact hcard
  · intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
    have hI := ZeroTimeGateODE.binary_tzInstanceOK q hq D en x hrH hcH hrD hcD hPSD Jl Wp G bf
      xs bs βG δG βb δb bmax hR
    exact hout (primsT (R := ℂ) D en x) Jl Wp (HsT D en x) (LsT D en x) G bf xs bs βG δG βb δb
      bmax ζs (primsT_isUnitary D en x) hζs hload hwp hbud hI

/-- **Dissipative ODE from time-indexed binary sparse data over a finite gate set, every trial
synthesised, for every `T ≥ 0`** (partial formalisation, under this package's format hypotheses, of
the finite-set statement of Theorem `ode:thm:gates`, time-dependent part,
with its remark on zero time and a known zero generator, finite-set synthesis as a hypothesis).

For binary public data with `BTPublicOK0 q` and the time-indexed binary data and circuits of the
released `GateBinaryODETime.binary_ode_time_solver_synth`, the synthesised protocol
`sprotocol hS (ε/200) (btprepC q loadC wpC) (2g)` on the released binary register with `|Xa|`
ancillas: every synthesised trial consists of valid gates of `𝒢` and primitive calls; one
preparation uses at most `if BTZeroCase q then |loadC| + 2 |wpC| else <the released binary
count>` gates and at most `if BTZeroCase q then calls(loadC) + 2 calls(wpC) else
12 d (2 [row] + 2 [col] + 2 [value]) + calls(loadC) + 2 calls(wpC)` calls of every kind; every
history makes at most `40 · 2g` times the calls of the preparation and, if
`len ζ ≤ c₁ log(1/ζ) + c₀`, uses at most
`(40 · 2g N + 20 · 2g (4 n + 3)) (c₁ log((10 · 2g N + 5 · 2g (4 n + 3) + 1)/(ε/200)) + c₀)` gates
of `𝒢`; the register has the released qubits plus `|Xa|`. For every input with the released
energy and accretivity promises of every sample, circuits within `ζs` with
`24 d ζ + 3 ζs ≤ ν` and the released remaining conditions `PubT.Rest`, the protocol has the
guarantee `SOutcome` against `x(T)`. -/
theorem binary_ode_time_solver_synth_nonneg (hS : Synthesis 𝒢 Xa len) (q : PubT)
    (hq : BTPublicOK0 q) (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s)
    (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ synthBudget hS (q.ε / 200) (trialN (btprepC q loadC wpC) j), i.Valid) ∧
      ∀ g, NInstr.gate g ∈ synthBudget hS (q.ε / 200) (trialN (btprepC q loadC wpC) j) →
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
    (∀ c : Query → Bool,
      ((sprotocol hS (q.ε / 200) (btprepC q loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
        40 * q.params.ratio * nCallsN c (btprepC q loadC wpC)) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((sprotocol hS (q.ε / 200) (btprepC q loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
        (40 * q.params.ratio * nGatesN (btprepC q loadC wpC) +
          20 * q.params.ratio * (4 * (Fintype.card q.params.W +
            Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) + Fintype.card Zs + q.kx) +
              3)) *
        (c₁ * Real.log ((10 * q.params.ratio * nGatesN (btprepC q loadC wpC) +
          5 * q.params.ratio * (4 * (Fintype.card q.params.W +
            Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) + Fintype.card Zs + q.kx) +
              3) + 1) / (q.ε / 200)) + c₀)) ∧
    Fintype.card (TNW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A ⊕ Xa) =
      q.kx + 2 * (Fintype.card q.params.W +
        (6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3) + Fintype.card Zs) + q.kx + 1 +
        Fintype.card Xa ∧
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
      SOutcome (sprotocol hS (q.ε / 200) (btprepC q loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)) q.ε (primsT (R := ℂ) D en x) (xs q.T) := by
  obtain ⟨hV, hG, hC, -, -, hcard, hout⟩ := ZeroTimeGateODE.binary_ode_time_solver_nonneg q hq
    D en hrange hdec loadC hloadV wpC hwpV
  have hε := hq.ε_pos
  have hεh := hq.ε_half
  have hη : 0 < q.ε / 200 := by positivity
  refine ⟨fun j => sprotocol_valid hS hη _ hV j, hG, hC,
    fun c => (sprotocol_worst hS hη _ hV q.params.ratio (q.params.ratio_ge hq.g_ge) c).2, ?_, ?_,
    ?_⟩
  · intro c₀ c₁ hc₀ hc₁ hlen
    have h := sprotocol_worst_log hS hη (by linarith) _ hV q.params.ratio
      (q.params.ratio_ge hq.g_ge) hc₀ hc₁ hlen
    rw [Fintype.card_fin] at h
    exact h
  · rw [Fintype.card_sum, hcard]
  · intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
    exact soutcome hS hη (by linarith) (by linarith) _ hV q.params.ratio
      (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (primsT_isUnitary D en x) _
      hR.target_ne
      (hout x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR)

end BinaryTime

end

end SparseHamiltonian.GateRemarks.ODE
