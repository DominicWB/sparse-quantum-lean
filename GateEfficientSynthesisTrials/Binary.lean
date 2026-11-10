import GateEfficientSynthesisTrials.Solver
import GateEfficientBinaryODE.Solver
import GateEfficientBinaryODETime.Solver

/-!
# Theorem `ode:thm:gates` from binary data over a finite gate set, trial by trial

The finite-gate-set forms of Theorem `ode:thm:gates` in this module are a partial formalisation of
its finite-set statement, under this package's format hypotheses: the manuscript states Theorem
`ode:thm:gates` over a finite gate set; the conformance endpoints count native gates.

The dissipative solvers from binary sparse data (`GateBinaryODE.binary_ode_solver`, constant
coefficients) and from time-indexed binary sparse data (`GateBinaryODETime.binary_ode_time_solver`,
time-dependent coefficients) with the preparation synthesised over a finite gate set and the
zero tests, the sign and the inverse preparation kept exact (`native_ode_solver_trials`,
`native_ode_time_solver_trials`). All ingredients of the released native solvers are
constructed from the binary data as in the released binary solvers; the synthesis is the
hypothesis `Synthesis 𝒢 Xa len`, with `AdjClosed 𝒢` and `zeroTestKinds ⊆ 𝒢`.

* `binary_ode_solver_trials`: constant coefficients.
* `binary_ode_time_solver_trials`: time-dependent coefficients.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSynthTrials

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth GateBinary
open GateBinaryODE GateBinaryODETime
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

section Binary

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Gate-efficient dissipative ODE solver from binary sparse data over a finite gate set with
exact reflections, constant coefficients** (partial formalisation, under this package's format
hypotheses, of the finite-set statement of Theorem `ode:thm:gates`, constant
coefficients, with finite-set synthesis as a hypothesis, including the per-trial claim).

For the public data `q`, the binary sparse data `D` and the source circuits `srcC` of
`binary_ode_solver`, the synthesised protocol `nprotocol (synthPrep hS (ν/3) (q.prep srcC)) g`
depends only on the public data. Under `Synthesis 𝒢 Xa len`, `AdjClosed 𝒢` and
`zeroTestKinds ⊆ 𝒢` its trials consist of valid gates of `𝒢` and primitive calls; one native
preparation has the counts of `binary_ode_counts`, the synthesised preparation at most
`N len(ν/3/(N+1))` gates and exactly the native calls; in every history the protocol makes at
most `40 g` times the native calls and uses at most `40 g N_S + 20 g (4 n + 3)` gates
(`n = |W| + |XW| + |SX| + k`), at most `40 g N (c₁ log((N+1)/(ν/3)) + c₀) + 20 g (4 n + 3)` if
`len ζ ≤ c₁ log(1/ζ) + c₀`. For every input and instance satisfying the hypotheses of
`binary_ode_solver` it has the guarantees `NOutcome`: every successful trial is within `ε/500`
of the normalised solution of `x' = -M̂ x + b` up to a global phase, the success probability is
at least `2/3`, and the conditional output is within trace distance `ε`. -/
theorem binary_ode_solver_trials (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) (q : Pub) (hq : q.OK)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep srcC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep srcC)) j →
        GateOf 𝒢 g) ∧
    nGatesN (q.prep srcC) ≤ q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
      6 * q.params.d * (2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
        (2 * q.ar.bP + q.ar.bT + 1)) + nGatesN (srcC false) + nGatesN (srcC true) ∧
    (∀ c : Query → Bool, nCallsN c (q.prep srcC) ≤
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c (srcC false) + nCallsN c (srcC true)) ∧
    nGatesN (synthPrep hS (q.params.nu / 3) (q.prep srcC)) ≤
      nGatesN (q.prep srcC) * len (q.params.nu / 3 / (nGatesN (q.prep srcC) + 1)) ∧
    (∀ c : Query → Bool, nCallsN c (synthPrep hS (q.params.nu / 3) (q.prep srcC)) =
      nCallsN c (q.prep srcC)) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep srcC)) q.g hq.g_ge).worstCost
        (wCallN c) : ℝ) ≤ 40 * q.g * nCallsN c (q.prep srcC)) ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep srcC)) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * q.g * nGatesN (synthPrep hS (q.params.nu / 3) (q.prep srcC)) +
        20 * q.g * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card (SX Zs (nPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A)
            Xa) + q.kx) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep srcC)) q.g hq.g_ge).worstCost
          wGateN : ℝ) ≤
        40 * q.g * (nGatesN (q.prep srcC) *
          (c₁ * Real.log ((nGatesN (q.prep srcC) + 1) / (q.params.nu / 3)) + c₀)) +
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
      (x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection x0) →
      (v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection v) →
      ODEConstantForcing.solution (-mLift D en x) x0 v q.T ≠ 0 →
      q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en x) x0 v q.T‖ →
      NOutcome (synthPrep hS (q.params.nu / 3) (q.prep srcC)) q.g q.ε hq.g_ge
        (prims (R := ℂ) D en x) (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  obtain ⟨-, hG, hC, -, -, -⟩ := GateBinaryODE.binary_ode_counts q hq srcC hsrcV
  obtain ⟨hV, -, -, hSG, hSC, hWC, hWG, hWL, hcard, hout⟩ :=
    native_ode_solver_trials hS hadj hzt q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ)
      q.nd q.nd_public q.ar q.ζ hq.ζ_pos.le (q.ar_ok hq) srcC hsrcV
  refine ⟨hV, hG, hC, hSG, hSC, hWC, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_fin] at hWG
    exact hWG
  · intro c₀ c₁ hc₀ hc₁ hlen
    have h := hWL c₀ c₁ hc₀ hc₁ hlen
    rw [Fintype.card_fin] at h
    exact h
  · rw [hcard, card_SZ4, Fintype.card_fin]
  · intro x hrH hcH hrD hcD hPSD Jsrc x0 v ζs hJ hζs hsrc hbud hx0 hv hpx hpv hne hB
    have h := hout (prims (R := ℂ) D en x) (privFam q.params D en x q.rho q.γ) Jsrc
      (hLift D en x) (lLift D en x) x0 v ζs (prims_isUnitary D en x)
      (q.nativeOK hq D en hrange hdec x) hζs hsrc hbud
      (q.instanceOK hq D en hrange x hrH hcH hrD hcD hPSD Jsrc x0 v hJ hx0 hv hpx hpv hne hB)
    rw [target_lift] at h
    exact h

/-- **Gate-efficient dissipative ODE solver from time-indexed binary sparse data over a finite
gate set with exact reflections, time-dependent coefficients** (partial formalisation, under this
package's format hypotheses, of the finite-set statement of Theorem `ode:thm:gates`, time-dependent
part, with finite-set synthesis as a hypothesis, including the
per-trial claim).

For the public data `q`, the time-indexed binary sparse data `D` and the source circuits
`loadC`, `wpC` of `binary_ode_time_solver`, the synthesised protocol
`nprotocol (synthPrep hS (ν/3) (q.prep loadC wpC)) (2g)` depends only on the public data. Under
`Synthesis 𝒢 Xa len`, `AdjClosed 𝒢` and `zeroTestKinds ⊆ 𝒢` its trials consist of valid gates of
`𝒢` and primitive calls; one native preparation has the counts of `binary_ode_time_counts`, the
synthesised preparation at most `N len(ν/3/(N+1))` gates and exactly the native calls; in every
history the protocol makes at most `80 g` times the native calls and uses at most
`80 g N_S + 40 g (4 n + 3)` gates (`n = |W| + |XW| + |SX| + k`), at most
`80 g N (c₁ log((N+1)/(ν/3)) + c₀) + 40 g (4 n + 3)` if `len ζ ≤ c₁ log(1/ζ) + c₀`. For every
input and instance satisfying the hypotheses of `binary_ode_time_solver` it has the guarantees
`NOutcome`: every successful trial is within `ε/500` of `x(T)/‖x(T)‖` up to a global phase, the
success probability is at least `2/3`, and the conditional output is within trace distance
`ε`. -/
theorem binary_ode_time_solver_trials (hS : Synthesis 𝒢 Xa len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) (q : PubT) (hq : q.OK)
    (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) j →
        GateOf 𝒢 g) ∧
    nGatesN (q.prep loadC wpC) ≤ q.params.prepGates + 84 * q.params.d * (q.σ + 3) +
      6 * q.params.d * (2 * (28 * q.kx + 2) + 2 * q.ar.circ.length +
        (2 * q.ar.bP + q.ar.bT + 1)) + nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ c : Query → Bool, nCallsN c (q.prep loadC wpC) ≤
      12 * q.params.d * (2 * (if c Query.rowLocation then 1 else 0) +
        2 * (if c Query.columnLocation then 1 else 0) + 2 * (if c Query.value then 1 else 0)) +
        nCallsN c loadC + 2 * nCallsN c wpC) ∧
    nGatesN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) ≤
      nGatesN (q.prep loadC wpC) * len (q.params.nu / 3 / (nGatesN (q.prep loadC wpC) + 1)) ∧
    (∀ c : Query → Bool, nCallsN c (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) =
      nCallsN c (q.prep loadC wpC)) ∧
    (∀ c : Query → Bool,
      ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
        40 * q.params.ratio * nCallsN c (q.prep loadC wpC)) ∧
    ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
      40 * q.params.ratio * nGatesN (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) +
        20 * q.params.ratio * (4 * (Fintype.card q.params.W +
          Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) +
          Fintype.card (SX Zs (tnPool q.params (Fin q.kx) Zs (SZ4 q.kx q.b) q.ar.bT q.ar.bP
            q.ar.A) Xa) + q.kx) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio
          (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
        40 * q.params.ratio * (nGatesN (q.prep loadC wpC) *
          (c₁ * Real.log ((nGatesN (q.prep loadC wpC) + 1) / (q.params.nu / 3)) + c₀)) +
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
      NOutcome (synthPrep hS (q.params.nu / 3) (q.prep loadC wpC)) q.params.ratio q.ε
        (q.params.ratio_ge hq.g_ge) (primsT (R := ℂ) D en x) (xs q.T) := by
  obtain ⟨-, hG, hC, -, -, -⟩ := GateBinaryODETime.binary_ode_time_counts q hq loadC hloadV wpC hwpV
  obtain ⟨hV, -, -, hSG, hSC, hWC, hWG, hWL, hcard, hout⟩ :=
    native_ode_time_solver_trials hS hadj hzt q.params (q.params_ok hq) q.UJg
      (hadUJ4_ok q.σ q.hσ) q.nd q.nd_public q.ar q.ζ hq.ζ_pos.le (q.ar_ok hq) loadC hloadV wpC
      hwpV
  refine ⟨hV, hG, hC, hSG, hSC, hWC, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_fin] at hWG
    exact hWG
  · intro c₀ c₁ hc₀ hc₁ hlen
    have h := hWL c₀ c₁ hc₀ hc₁ hlen
    rw [Fintype.card_fin] at h
    exact h
  · rw [hcard, card_SZ4, Fintype.card_fin]
  · intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
    exact hout (primsT (R := ℂ) D en x) (privFamT q.params D en x q.rho q.γ) Jl Wp (HsT D en x)
      (LsT D en x) G bf xs bs βG δG βb δb bmax ζs (primsT_isUnitary D en x)
      (q.nativeOK hq D en hrange hdec x) hζs hload hwp hbud
      (q.instanceOK hq D en hrange x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax hR)

end Binary

end

end SparseHamiltonian.GateSynthTrials
