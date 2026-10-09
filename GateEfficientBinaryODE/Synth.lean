import GateEfficientBinaryODE.Solver
import GateEfficientSynthesis.ODESolver

/-!
# Theorem `ode:thm:gates` from binary sparse data over a finite gate set

The native solver from binary sparse data (`binary_ode_solver`) with every trial synthesised over
a finite gate set under the synthesis hypothesis `GateSynth.Synthesis 𝒢 Xa len` of
`GateEfficientSynthesis` (gate set `𝒢`, synthesis ancillas `Xa`, synthesis length `len`), with
the synthesis budget `ε/200` per trial (`GateSynth.sprotocol`). All ingredients of the released
native solver are constructed from the binary data as in `binary_ode_solver`; the synthesis is
the hypothesis `hS`.

`binary_ode_solver_synth`: the synthesised protocol depends only on the public data; its trials
consist of valid gates of `𝒢` and primitive calls; in every history it makes at most `40 g` times
the primitive calls of one native preparation (bounded in `binary_ode_counts`) and, if
`len ζ ≤ c₁ log(1/ζ) + c₀`, uses at most `(40 g N + 20 g (4 n + 3)) (c₁ log((G + 1)/(ε/200)) + c₀)`
elementary gates (`N` the gates of one native preparation, bounded in `binary_ode_counts`, `n` the
wires tested by the seed reflection and `G = 10 g N + 5 g (4 n + 3)`); its register has the native
wires and the `|Xa|` synthesis ancillas; and on every instance satisfying the hypotheses of
`binary_ode_solver` it succeeds with probability at least `2/3` and its conditional output is
within trace distance `ε` of the normalised solution of `x' = -M̂ x + b`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryODE

noncomputable section
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative SparseHamiltonian.GateBinary
open SparseHamiltonian.OracleCircuit
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

section Synth

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set GateSynth.Kind} {len : ℝ → ℕ}

/-- **Gate-efficient dissipative ODE solver from binary sparse data over a finite gate set,
constant coefficients** (Theorem `ode:thm:gates`, constant coefficients, with finite-set
synthesis as a hypothesis).

For the public data `q`, the binary sparse data `D` and the source circuits `srcC` of
`binary_ode_solver`, the synthesised protocol `sprotocol hS (ε/200) (q.prep srcC) g` depends only
on the public data. Its trials consist of valid gates of `𝒢` and primitive calls; in every
history it makes at most `40 g` times the primitive calls of one native preparation and, if
`len ζ ≤ c₁ log(1/ζ) + c₀`, uses at most `(40 g N + 20 g (4 n + 3)) (c₁ log((G + 1)/(ε/200)) + c₀)`
elementary gates (`N` the gates of one native preparation, bounded in `binary_ode_counts`,
`n = |W| + |XW| + |Zs| + k` and `G = 10 g N + 5 g (4 n + 3)`); its register has the native wires
and the `|Xa|` synthesis ancillas. For every input and instance satisfying the hypotheses of
`binary_ode_solver` it succeeds with probability at least `2/3`, and its conditional output is
within trace distance `ε` of the normalised solution of `x' = -M̂ x + b`. -/
theorem binary_ode_solver_synth (hS : GateSynth.Synthesis 𝒢 Xa len) (q : Pub) (hq : q.OK)
    (D : Data X n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (srcC : Bool → List (NInstr ((Unit ⊕ Fin q.kx) ⊕ Zs) (PY q.kx q.b) Query))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, (∀ i ∈ GateSynth.synthBudget hS (q.ε / 200) (trialN (q.prep srcC) j), i.Valid) ∧
      ∀ g, NInstr.gate g ∈ GateSynth.synthBudget hS (q.ε / 200) (trialN (q.prep srcC) j) →
        GateSynth.GateOf 𝒢 g) ∧
    (∀ c : Query → Bool,
      ((GateSynth.sprotocol hS (q.ε / 200) (q.prep srcC) q.g hq.g_ge).worstCost
        (wCallN c) : ℝ) ≤ 40 * q.g * nCallsN c (q.prep srcC)) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((GateSynth.sprotocol hS (q.ε / 200) (q.prep srcC) q.g hq.g_ge).worstCost
        wGateN : ℝ) ≤
        (40 * q.g * nGatesN (q.prep srcC) +
          20 * q.g * (4 * (Fintype.card q.params.W +
            Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) + Fintype.card Zs + q.kx) +
              3)) *
        (c₁ * Real.log ((10 * q.g * nGatesN (q.prep srcC) +
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
      (x0 ≠ 0 → Jsrc false (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection x0) →
      (v ≠ 0 → Jsrc true (seedV (S := Fin q.kx)) = ODEStateNormalization.unitDirection v) →
      ODEConstantForcing.solution (-mLift D en x) x0 v q.T ≠ 0 →
      q.r₀ + q.T * q.rb ≤ q.g * ‖ODEConstantForcing.solution (-mLift D en x) x0 v q.T‖ →
      GateSynth.SOutcome (GateSynth.sprotocol hS (q.ε / 200) (q.prep srcC) q.g hq.g_ge) q.ε
        (prims (R := ℂ) D en x) (ODEConstantForcing.solution (-mLift D en x) x0 v q.T) := by
  obtain ⟨hV, -, -, hWC, hWG, hcard, hout⟩ :=
    GateSynth.native_ode_solver_synth hS q.params (q.params_ok hq) q.UJg (hadUJ4_ok q.σ q.hσ)
      q.nd q.nd_public q.ar q.ζ hq.ζ_pos.le (q.ar_ok hq) srcC hsrcV
  refine ⟨hV, hWC, ?_, ?_, ?_⟩
  · intro c₀ c₁ hc₀ hc₁ hlen
    have h := hWG c₀ c₁ hc₀ hc₁ hlen
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

end Synth

end

end SparseHamiltonian.GateBinaryODE
