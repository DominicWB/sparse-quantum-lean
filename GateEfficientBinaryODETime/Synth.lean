import GateEfficientBinaryODETime.Solver
import GateEfficientSynthesis.ODESolver

/-!
# Theorem `ode:thm:gates` from time-indexed binary sparse data over a finite gate set

The time-dependent native solver from binary data (`binary_ode_time_solver`) with every trial
synthesised over a finite gate set under the synthesis hypothesis `GateSynth.Synthesis 𝒢 Xa len`
of `GateEfficientSynthesis` (gate set `𝒢`, synthesis ancillas `Xa`, synthesis length `len`),
with the synthesis budget `ε/200` per trial (`GateSynth.sprotocol`), through
`GateSynth.native_ode_time_solver_synth`. All ingredients of the released native solver are
constructed from the binary data as in `binary_ode_time_solver`; the synthesis is the hypothesis
`hS`.

`binary_ode_time_solver_synth`: the synthesised protocol depends only on the public data; its
trials consist of valid gates of `𝒢` and primitive calls; in every history it makes at most
`80 g` times the primitive calls of one native preparation (bounded in
`binary_ode_time_counts`) and, if `len ζ ≤ c₁ log(1/ζ) + c₀`, uses at most
`(80 g N + 40 g (4 n + 3)) (c₁ log((G + 1)/(ε/200)) + c₀)` elementary gates (`N` the gates of
one native preparation, `n` the wires tested by the seed reflection and
`G = 20 g N + 10 g (4 n + 3)`); its register has the native wires and the `|Xa|` synthesis
ancillas; and on every instance satisfying the hypotheses of `binary_ode_time_solver` it
succeeds with probability at least `2/3` and its conditional output is within trace distance
`ε` of `x(T)/‖x(T)‖`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateBinaryODETime

noncomputable section
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative SparseHamiltonian.GateBinary
open SparseHamiltonian.GateBinaryODE SparseHamiltonian.OracleCircuit
open NativeSparseBlockEncoding (Data Query)
open scoped InnerProduct

section Synth

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set GateSynth.Kind} {len : ℝ → ℕ}

/-- **Gate-efficient dissipative ODE solver from time-indexed binary sparse data over a finite
gate set, time-dependent coefficients** (Theorem `ode:thm:gates`, time-dependent part, with
finite-set synthesis as a hypothesis).

For the public data `q`, the time-indexed binary sparse data `D` and the source circuits
`loadC`, `wpC` of `binary_ode_time_solver`, the synthesised protocol
`sprotocol hS (ε/200) (q.prep loadC wpC) (2g)` depends only on the public data. Its trials
consist of valid gates of `𝒢` and primitive calls; in every history it makes at most `80 g` times
the primitive calls of one native preparation and, if `len ζ ≤ c₁ log(1/ζ) + c₀`, uses at most
`(80 g N + 40 g (4 n + 3)) (c₁ log((G + 1)/(ε/200)) + c₀)` elementary gates (`N` the gates of
one native preparation, bounded in `binary_ode_time_counts`, `n = |W| + |XW| + |Zs| + k` and
`G = 20 g N + 10 g (4 n + 3)`); its register has the native wires and the `|Xa|` synthesis
ancillas. For every input and instance satisfying the hypotheses of `binary_ode_time_solver` it
succeeds with probability at least `2/3`, and its conditional output is within trace distance
`ε` of `x(T)/‖x(T)‖`. -/
theorem binary_ode_time_solver_synth (hS : GateSynth.Synthesis 𝒢 Xa len) (q : PubT)
    (hq : q.OK) (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ GateSynth.synthBudget hS (q.ε / 200) (trialN (q.prep loadC wpC) j),
        i.Valid) ∧
      ∀ g, NInstr.gate g ∈ GateSynth.synthBudget hS (q.ε / 200) (trialN (q.prep loadC wpC) j) →
        GateSynth.GateOf 𝒢 g) ∧
    (∀ c : Query → Bool,
      ((GateSynth.sprotocol hS (q.ε / 200) (q.prep loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
        40 * q.params.ratio * nCallsN c (q.prep loadC wpC)) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((GateSynth.sprotocol hS (q.ε / 200) (q.prep loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost wGateN : ℝ) ≤
        (40 * q.params.ratio * nGatesN (q.prep loadC wpC) +
          20 * q.params.ratio * (4 * (Fintype.card q.params.W +
            Fintype.card (XW (SZ4 q.kx q.b) q.ar.bT q.ar.bP q.ar.A) + Fintype.card Zs + q.kx) +
              3)) *
        (c₁ * Real.log ((10 * q.params.ratio * nGatesN (q.prep loadC wpC) +
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
      GateSynth.SOutcome (GateSynth.sprotocol hS (q.ε / 200) (q.prep loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)) q.ε (primsT (R := ℂ) D en x) (xs q.T) := by
  obtain ⟨hV, -, -, hWC, hWG, hcard, hout⟩ :=
    GateSynth.native_ode_time_solver_synth hS q.params (q.params_ok hq) q.UJg
      (hadUJ4_ok q.σ q.hσ) q.nd q.nd_public q.ar q.ζ hq.ζ_pos.le (q.ar_ok hq) loadC hloadV wpC
      hwpV
  refine ⟨hV, hWC, ?_, ?_, ?_⟩
  · intro c₀ c₁ hc₀ hc₁ hlen
    have h := hWG c₀ c₁ hc₀ hc₁ hlen
    rw [Fintype.card_fin] at h
    exact h
  · rw [hcard, card_SZ4, Fintype.card_fin]
  · intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax ζs hζs hload hwp hbud hR
    exact hout (primsT (R := ℂ) D en x) (privFamT q.params D en x q.rho q.γ) Jl Wp (HsT D en x)
      (LsT D en x) G bf xs bs βG δG βb δb bmax ζs (primsT_isUnitary D en x)
      (q.nativeOK hq D en hrange hdec x) hζs hload hwp hbud
      (q.instanceOK hq D en hrange x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs βG δG βb δb bmax hR)

end Synth

end

end SparseHamiltonian.GateBinaryODETime
