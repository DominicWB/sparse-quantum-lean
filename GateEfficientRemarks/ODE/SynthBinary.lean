import GateEfficientRemarks.ODE.SynthZero
import ZeroTimeGateODE.Binary

/-!
# Binary sparse data over a finite gate set, every trial synthesised, for every `T ≥ 0`

The finite-gate-set forms of Theorem `ode:thm:gates` in this module are a partial formalisation of
its finite-set statement, under this package's format hypotheses: the manuscript states Theorem
`ode:thm:gates` over a finite gate set; the conformance endpoints count native gates.

The released solver from binary sparse data with every trial synthesised
(`GateBinaryODE.binary_ode_solver_synth`, Theorem `ode:thm:gates` with finite-set synthesis as a
hypothesis) requires `T > 0` and `η_H + η_D > 0` (`GateBinaryODE.Pub.OK`). The released library
`ZeroTimeGateODE` gives, for every `T ≥ 0` (`BPublicOK0`), the combined preparation

`bprepC q srcC = if T = 0 ∨ η_H + η_D = 0 then zprepC (srcRot T r₀ r_b) srcC else q.prep srcC`

on the released binary register (`BZeroCase` the zero case). With every trial synthesised
(`GateSynth.sprotocol hS (ε/200)`):

* `binary_ode_solver_synth_zero`: in the zero case, the direct source assembly has exactly
  `|srcC 0| + |srcC 1| + 2` gates and the calls of the source circuits, the protocol makes no call
  of a kind of the binary sparse oracles (row location, column location, value) that the source
  circuits do not call, and it has the guarantee `GateSynth.SOutcome` against the solution `x(T)`
  of `x' = -M̂ x + b` (which is `x₀ + T b`, `ZeroTimeGateODE.binary_target_zero`) under the
  zero-case conditions: the row energy promises, sources within `ζs`, `2 ζs ≤ ν`, public norms,
  seed promises, `x(T) ≠ 0` and `r₀ + T r_b ≤ g ‖x(T)‖`;
* `binary_ode_solver_synth_nonneg`: for every `T ≥ 0`, the conclusions of the released
  `GateBinaryODE.binary_ode_solver_synth` with the counts of `bprepC`,
  `if BZeroCase q then <direct source assembly> else <released>`, and `SOutcome` under the
  released hypotheses on the input and the sources (those of `binary_ode_solver_nonneg`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth GateBinary
open ZeroTimeGateODE (bprepC zprepC srcRot BPublicOK0 BZeroCase)
open GateBinaryODE (Pub mLift SZ4 card_SZ4)
open NativeSparseBlockEncoding (Data Query)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

section Binary

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Zero time or a known zero generator from binary sparse data over a finite gate set, every
trial synthesised** (partial formalisation, under this package's format hypotheses, of the
finite-set form of the remark of Theorem `ode:thm:gates`: direct source
assembly, no matrix calls).

For binary public data with `BPublicOK0 q` in the zero case `T = 0 ∨ η_H + η_D = 0`, with the
synthesis hypothesis `Synthesis 𝒢 Xa len`, the synthesised protocol
`sprotocol hS (ε/200) (bprepC q srcC) g` on the released binary register with the `|Xa|`
synthesis ancillas: every synthesised trial consists of valid gates of `𝒢` and primitive calls;
the preparation (the direct source assembly) has `N = |srcC 0| + |srcC 1| + 2` gates and exactly
`calls_c(srcC 0) + calls_c(srcC 1)` calls of every kind `c`; every history makes at most `40 g`
times these calls, so no call of a binary sparse oracle (row location, column location, value)
that the source circuits do not call, and, if `len ζ ≤ c₁ log(1/ζ) + c₀`, uses at most
`(40 g N + 20 g (4 n + 3)) (c₁ log((10 g N + 5 g (4 n + 3) + 1)/(ε/200)) + c₀)` gates of `𝒢`
(`n = |W| + |XW| + |Zs| + k_x`); the register has the released qubits plus `|Xa|`. For every
input whose Hamiltonian and dissipative parts have row energies at most `η_H²`, `η_D²`, unitary
source interfaces approximated by the source circuits within `ζs`, `2 ζs ≤ ν`, the public norms,
the seed promises, `x(T) ≠ 0` and `r₀ + T r_b ≤ g ‖x(T)‖`, the protocol has the guarantee
`SOutcome` against the solution `x(T)` of `x' = -M̂ x + b`. -/
theorem binary_ode_solver_synth_zero (hS : Synthesis 𝒢 Xa len) (q : Pub) (hq : BPublicOK0 q)
    (hz : BZeroCase q) (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, (∀ i ∈ synthBudget hS (q.ε / 200) (trialN (bprepC q srcC) j), i.Valid) ∧
      ∀ g, NInstr.gate g ∈ synthBudget hS (q.ε / 200) (trialN (bprepC q srcC) j) →
        GateOf 𝒢 g) ∧
    nGatesN (bprepC q srcC) = nGatesN (srcC false) + nGatesN (srcC true) + 2 ∧
    (∀ c : Query → Bool,
      nCallsN c (bprepC q srcC) = nCallsN c (srcC false) + nCallsN c (srcC true)) ∧
    (∀ c : Query → Bool,
      ((sprotocol hS (q.ε / 200) (bprepC q srcC) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤
        40 * q.g * (nCallsN c (srcC false) + nCallsN c (srcC true) : ℕ)) ∧
    (∀ c : Query → Bool, nCallsN c (srcC false) = 0 → nCallsN c (srcC true) = 0 →
      (sprotocol hS (q.ε / 200) (bprepC q srcC) q.g hq.g_ge).worstCost (wCallN c) = 0) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((sprotocol hS (q.ε / 200) (bprepC q srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
        (40 * q.g * (nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) +
          20 * q.g * (4 * (Fintype.card q.params.W +
            Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) + Fintype.card Zs + q.kx) +
              3)) *
        (c₁ * Real.log ((10 * q.g * (nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) +
          5 * q.g * (4 * (Fintype.card q.params.W +
            Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) + Fintype.card Zs + q.kx) +
              3) + 1) / (q.ε / 200)) + c₀)) ∧
    Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A ⊕ Xa) =
      q.kx + 2 * (Fintype.card q.params.W +
        (6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3) + Fintype.card Zs) + q.kx + 1 +
        Fintype.card Xa ∧
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
      SOutcome (sprotocol hS (q.ε / 200) (bprepC q srcC) q.g hq.g_ge) q.ε
        (prims (R := ℂ) D en x) (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  obtain ⟨hV, hG, hC, hWC, hno, hWG, hcard, hout⟩ := native_ode_solver_synth_zero
    (S := Fin q.kx) (Zs := Zs) (Z := SZ4 q.kx q.b) (Y := PY q.kx q.b) (J := Query) (X := Xa) hS
    q.params.a q.params.m q.params.r q.params.K q.params.k q.params.l q.params.f q.ar.bT q.ar.bP
    q.ar.A q.T q.g q.ε q.r₀ q.rb hq.T_nonneg hq.g_ge hq.ε_pos hq.ε_half hq.r₀_nonneg
    hq.rb_nonneg hq.B_pos srcC hsrcV
  have hb : bprepC q srcC = zprepC (srcRot q.T q.r₀ q.rb) srcC := by
    rw [bprepC, if_pos hz]
  rw [hb]
  refine ⟨hV, hG, hC, hWC, hno, ?_, ?_, ?_⟩
  · intro c₀ c₁ hc₀ hc₁ hlen
    have h := hWG c₀ c₁ hc₀ hc₁ hlen
    rw [Fintype.card_fin] at h
    exact h
  · rw [card_SZ4, Fintype.card_fin] at hcard
    exact hcard
  · intro x hrH hrD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hB
    have ht := ZeroTimeGateODE.binary_target_zero q hq hz D en x hrH hrD x0 v
    rw [ht] at hne hB ⊢
    have hnu : q.params.nu = ImprovedODEQueryBudget.precision q.g q.ε := rfl
    rw [hnu] at hbud
    exact hout (prims (R := ℂ) D en x) Jsrc x0 v ζs (prims_isUnitary D en x) hJ hζs hsrc hbud
      hx0 hv hpx hpv hne hB

/-- **Dissipative ODE from binary sparse data over a finite gate set, every trial synthesised,
for every `T ≥ 0`, constant coefficients** (partial formalisation, under this package's format
hypotheses, of the finite-set statement of Theorem `ode:thm:gates` with its
remark on zero time and a known zero generator, finite-set synthesis as a hypothesis).

For binary public data with `BPublicOK0 q` and the binary data and source circuits of the
released `GateBinaryODE.binary_ode_solver_synth`, the synthesised protocol
`sprotocol hS (ε/200) (bprepC q srcC) g` on the released binary register with `|Xa|` ancillas:
every synthesised trial consists of valid gates of `𝒢` and primitive calls; one preparation uses
at most `if BZeroCase q then |srcC 0| + |srcC 1| + 2 else <the released binary count>` gates and
at most `if BZeroCase q then calls(srcC 0) + calls(srcC 1) else 12 d (2 [row] + 2 [col] +
2 [value]) + calls(srcC 0) + calls(srcC 1)` calls of every kind; every history makes at most
`40 g` times the calls of the preparation and, if `len ζ ≤ c₁ log(1/ζ) + c₀`, uses at most
`(40 g N + 20 g (4 n + 3)) (c₁ log((10 g N + 5 g (4 n + 3) + 1)/(ε/200)) + c₀)` gates of `𝒢`;
the register has the released qubits plus `|Xa|`. For every input with the released energy and
accretivity promises and the released source hypotheses (`24 d ζ + 2 ζs ≤ ν`), the protocol has
the guarantee `SOutcome` against the solution `x(T)` of `x' = -M̂ x + b`. -/
theorem binary_ode_solver_synth_nonneg (hS : Synthesis 𝒢 Xa len) (q : Pub) (hq : BPublicOK0 q)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, (∀ i ∈ synthBudget hS (q.ε / 200) (trialN (bprepC q srcC) j), i.Valid) ∧
      ∀ g, NInstr.gate g ∈ synthBudget hS (q.ε / 200) (trialN (bprepC q srcC) j) →
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
    (∀ c : Query → Bool,
      ((sprotocol hS (q.ε / 200) (bprepC q srcC) q.g hq.g_ge).worstCost (wCallN c) : ℝ) ≤
        40 * q.g * nCallsN c (bprepC q srcC)) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((sprotocol hS (q.ε / 200) (bprepC q srcC) q.g hq.g_ge).worstCost wGateN : ℝ) ≤
        (40 * q.g * nGatesN (bprepC q srcC) +
          20 * q.g * (4 * (Fintype.card q.params.W +
            Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) + Fintype.card Zs + q.kx) +
              3)) *
        (c₁ * Real.log ((10 * q.g * nGatesN (bprepC q srcC) +
          5 * q.g * (4 * (Fintype.card q.params.W +
            Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) + Fintype.card Zs + q.kx) +
              3) + 1) / (q.ε / 200)) + c₀)) ∧
    Fintype.card (NW q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A ⊕ Xa) =
      q.kx + 2 * (Fintype.card q.params.W +
        (6 * q.kx + 4 * q.b + q.ar.bT + q.ar.bP + q.ar.A + 3) + Fintype.card Zs) + q.kx + 1 +
        Fintype.card Xa ∧
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
      SOutcome (sprotocol hS (q.ε / 200) (bprepC q srcC) q.g hq.g_ge) q.ε
        (prims (R := ℂ) D en x) (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  obtain ⟨hV, hG, hC, -, -, hcard, hout⟩ :=
    ZeroTimeGateODE.binary_ode_solver_nonneg q hq D en hrange hdec srcC hsrcV
  have hε := hq.ε_pos
  have hεh := hq.ε_half
  have hη : 0 < q.ε / 200 := by positivity
  refine ⟨fun j => sprotocol_valid hS hη _ hV j, hG, hC,
    fun c => (sprotocol_worst hS hη _ hV q.g hq.g_ge c).2, ?_, ?_, ?_⟩
  · intro c₀ c₁ hc₀ hc₁ hlen
    have h := sprotocol_worst_log hS hη (by linarith) _ hV q.g hq.g_ge hc₀ hc₁ hlen
    rw [Fintype.card_fin] at h
    exact h
  · rw [Fintype.card_sum, hcard]
  · intro x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hB
    exact soutcome hS hη (by linarith) (by linarith) _ hV q.g hq.g_ge (prims (R := ℂ) D en x)
      (prims_isUnitary D en x) _ hne
      (hout x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hB)

end Binary

end

end SparseHamiltonian.GateRemarks.ODE
