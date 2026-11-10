import ZeroTimeGateODE.Combined
import ZeroTimeGateODE.TimeCombined
import GateEfficientSynthesis.ODESolver

/-!
# The native solvers over a finite gate set for every `T ≥ 0`, every trial synthesised

The finite-gate-set forms of Theorem `ode:thm:gates` in this module are a partial formalisation of
its finite-set statement, under this package's format hypotheses: the manuscript states Theorem
`ode:thm:gates` over a finite gate set; the conformance endpoints count native gates.

The released finite-gate-set solvers that synthesise every trial
(`GateSynth.native_ode_solver_synth`, `GateSynth.native_ode_time_solver_synth`, Theorem
`ode:thm:gates` with synthesis as a hypothesis) require `T > 0` and `λ_H + R λ_D > 0`. For every
`T ≥ 0` and all bounds `λ_H, λ_D ≥ 0` (`ZeroTimeGateODE.PublicOK0`, `ZeroTimeGateODE.TPublicOK0`)
the same synthesis applies to the combined preparations of the released library
`ZeroTimeGateODE`,

`cprepC p … = if ZeroCase p then zprepC (srcRot T r₀ r_b) srcC else nprepC p UJg nd ar srcC`,
`ctprepC p … = if TZeroCase p then tzprepC loadC wpC else tnprepC p UJg nd ar loadC wpC`,

on the released registers `NW p ⊕ X`, `TNW p ⊕ X`:

* `native_ode_solver_synth_nonneg`, `native_ode_time_solver_synth_nonneg`: the conclusions of the
  released synthesised solvers with the counts of `cprepC` (resp. `ctprepC`), which are
  `if <zero case> then <direct source assembly> else <released>`, and the guarantee
  `GateSynth.SOutcome` under the case-dependent instance hypotheses of
  `ZeroTimeGateODE.native_ode_solver_nonneg` (resp. `native_ode_time_solver_nonneg`): the
  zero-case conditions in the zero case, the released conditions otherwise.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth
open ZeroTimeGateODE (cprepC ctprepC PublicOK0 TPublicOK0 ZeroCase TZeroCase ZInstanceOK
  TZInstanceOK)
open GateODE (Params Label Oracles)
open GateODE.Time (TParams TOracles)
open scoped InnerProduct BigOperators

section Synth

variable {S Zs Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Native dissipative ODE solver over a finite gate set, every trial synthesised, for every
`T ≥ 0`, constant coefficients** (partial formalisation, under this package's format hypotheses, of
the finite-set statement of Theorem `ode:thm:gates` with its remark on
zero time and a known zero generator, finite-set synthesis as a hypothesis).

For public data `p` with `PublicOK0 p` and the released public native data (`U_J` gates, a
public native private operation, arithmetic with `ArithOK` at accuracy `ζ`, valid source
circuits), the synthesised protocol `sprotocol hS (ε/200) (cprepC p UJg nd ar srcC) g` on
`NW p ⊕ X`: every synthesised trial consists of valid gates of `𝒢` and primitive calls; one
preparation uses at most `if ZeroCase p then |srcC 0| + |srcC 1| + 2 else
prepGates + 84 d C_J + 6 d G_C + |srcC 0| + |srcC 1|` elementary gates and at most
`if ZeroCase p then calls(srcC 0) + calls(srcC 1) else 12 d calls(V) + calls(srcC 0) +
calls(srcC 1)` calls of every kind; every history makes at most `40 g` times the calls of the
preparation and, if `len ζ ≤ c₁ log(1/ζ) + c₀`, uses at most
`(40 g N + 20 g (4 n + 3)) (c₁ log((10 g N + 5 g (4 n + 3) + 1)/(ε/200)) + c₀)` gates of `𝒢`
(`N` the gates of the preparation, `n = |W| + |XW| + |Zs| + |S|`); the register has the released
qubits plus `|X|`. For every instance with unitary primitive oracles and source circuits within
`ζs`, under `2 ζs ≤ ν` and `ZInstanceOK` in the zero case and under the released conditions
(`NativeOK`, `24 d ζ + 2 ζs ≤ ν`, `InstanceOK`) otherwise, the protocol has the guarantee
`SOutcome` against the released target `x(T)`. -/
theorem native_ode_solver_synth_nonneg (hS : Synthesis 𝒢 X len) (p : Params) (hp : PublicOK0 p)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (LabW p.k p.l) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (LabW p.k p.l) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (hsrcV : ∀ b, ∀ i ∈ srcC b, i.Valid) :
    (∀ j, (∀ i ∈ synthBudget hS (p.ε / 200) (trialN (cprepC p UJg nd ar srcC) j), i.Valid) ∧
      ∀ g, NInstr.gate g ∈ synthBudget hS (p.ε / 200) (trialN (cprepC p UJg nd ar srcC) j) →
        GateOf 𝒢 g) ∧
    nGatesN (cprepC p UJg nd ar srcC) ≤
      (if ZeroCase p then nGatesN (srcC false) + nGatesN (srcC true) + 2
      else p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar +
        nGatesN (srcC false) + nGatesN (srcC true)) ∧
    (∀ q : J → Bool, nCallsN q (cprepC p UJg nd ar srcC) ≤
      (if ZeroCase p then nCallsN q (srcC false) + nCallsN q (srcC true)
      else 12 * p.d * nCallsN q nd.V + nCallsN q (srcC false) + nCallsN q (srcC true))) ∧
    (∀ q : J → Bool,
      ((sprotocol hS (p.ε / 200) (cprepC p UJg nd ar srcC) p.g hp.g_ge).worstCost
        (wCallN q) : ℝ) ≤ 40 * p.g * nCallsN q (cprepC p UJg nd ar srcC)) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((sprotocol hS (p.ε / 200) (cprepC p UJg nd ar srcC) p.g hp.g_ge).worstCost
        wGateN : ℝ) ≤
        (40 * p.g * nGatesN (cprepC p UJg nd ar srcC) +
          20 * p.g * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
            Fintype.card Zs + Fintype.card S) + 3)) *
        (c₁ * Real.log ((10 * p.g * nGatesN (cprepC p UJg nd ar srcC) +
          5 * p.g * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
            Fintype.card Zs + Fintype.card S) + 3) + 1) / (p.ε / 200)) + c₀)) ∧
    Fintype.card (NW p S Zs Z ar.bT ar.bP ar.A ⊕ X) =
      Fintype.card S + 2 * (Fintype.card p.W + (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) +
        Fintype.card Zs) + Fintype.card S + 1 + Fintype.card X ∧
    ∀ (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
      (D : Label p.k p.l → Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ))
      (Jsrc : Bool → Reg S ℂ →L[ℂ] Reg S ℂ) (H L : Reg S ℂ →L[ℂ] Reg S ℂ) (x0 b : Reg S ℂ)
      (ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun prim (srcC c)) (liftB (srcIdeal c (Jsrc c))) ζs) →
      (if ZeroCase p then 2 * ζs ≤ p.nu ∧ ZInstanceOK p (seedV (S := S)) Jsrc H L x0 b
      else NativeOK prim nd (selOp (labFam D false)) ∧ 24 * (p.d : ℝ) * ζ + 2 * ζs ≤ p.nu ∧
        p.InstanceOK (seedV (S := S))
          (⟨UJop (R := ℂ) UJg, D, Jsrc⟩ : Oracles p.a (Label p.k p.l) (Reg S ℂ)) H L x0 b) →
      SOutcome (sprotocol hS (p.ε / 200) (cprepC p UJg nd ar srcC) p.g hp.g_ge) p.ε prim
        (p.target H L x0 b) := by
  obtain ⟨hV, hG, hC, -, -, hcard, hout⟩ := ZeroTimeGateODE.native_ode_solver_nonneg p hp UJg
    hUJg nd hnd ar ζ hζ har srcC hsrcV
  have hε := hp.ε_pos
  have hεh := hp.ε_half
  have hη : 0 < p.ε / 200 := by positivity
  refine ⟨fun j => sprotocol_valid hS hη _ hV j, hG, hC,
    fun q => (sprotocol_worst hS hη _ hV p.g hp.g_ge q).2,
    fun c₀ c₁ hc₀ hc₁ hlen =>
      sprotocol_worst_log hS hη (by linarith) _ hV p.g hp.g_ge hc₀ hc₁ hlen,
    by rw [Fintype.card_sum, hcard], ?_⟩
  intro prim D Jsrc H L x0 b ζs hprim hζs hsrc hcase
  have hne : p.target H L x0 b ≠ 0 := by
    by_cases hz : ZeroCase p
    · rw [if_pos hz] at hcase
      exact hcase.2.target_ne
    · rw [if_neg hz] at hcase
      exact hcase.2.2.target_ne
  exact soutcome hS hη (by linarith) (by linarith) _ hV p.g hp.g_ge prim hprim _ hne
    (hout prim D Jsrc H L x0 b ζs hprim hζs hsrc hcase)

/-- **Native dissipative ODE solver over a finite gate set, every trial synthesised, for every
`T ≥ 0`, time-dependent coefficients** (partial formalisation, under this package's format
hypotheses, of the finite-set statement of Theorem `ode:thm:gates`, time-dependent
part, with its remark on zero time and a known zero generator, finite-set synthesis as a
hypothesis).

For public data `p` with `TPublicOK0 p` and the released public native data, the synthesised
protocol `sprotocol hS (ε/200) (ctprepC p UJg nd ar loadC wpC) (2g)` on `TNW p ⊕ X`: every
synthesised trial consists of valid gates of `𝒢` and primitive calls; one preparation uses at
most `if TZeroCase p then |loadC| + 2 |wpC| else prepGates + 84 d C_J + 6 d G_C + |loadC| +
2 |wpC|` gates and at most `if TZeroCase p then calls(loadC) + 2 calls(wpC) else
12 d calls(V) + calls(loadC) + 2 calls(wpC)` calls of every kind; every history makes at most
`40 · 2g` times the calls of the preparation and, if `len ζ ≤ c₁ log(1/ζ) + c₀`, uses at most
`(40 · 2g N + 20 · 2g (4 n + 3)) (c₁ log((10 · 2g N + 5 · 2g (4 n + 3) + 1)/(ε/200)) + c₀)` gates
of `𝒢`; the register has the released qubits plus `|X|`. For every instance with unitary
primitive oracles and loading and weight-preparation circuits within `ζs`, under `3 ζs ≤ ν` and
`TZInstanceOK` in the zero case and under the released conditions (`NativeOK`,
`24 d ζ + 3 ζs ≤ ν`, `InstanceOK`) otherwise, the protocol has the guarantee `SOutcome` against
`x(T)`. -/
theorem native_ode_time_solver_synth_nonneg (hS : Synthesis 𝒢 X len) (p : TParams)
    (hp : TPublicOK0 p) (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ synthBudget hS (p.ε / 200) (trialN (ctprepC p UJg nd ar loadC wpC) j),
        i.Valid) ∧
      ∀ g, NInstr.gate g ∈ synthBudget hS (p.ε / 200) (trialN (ctprepC p UJg nd ar loadC wpC) j) →
        GateOf 𝒢 g) ∧
    nGatesN (ctprepC p UJg nd ar loadC wpC) ≤
      (if TZeroCase p then nGatesN loadC + 2 * nGatesN wpC
      else p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar + nGatesN loadC +
        2 * nGatesN wpC) ∧
    (∀ q : J → Bool, nCallsN q (ctprepC p UJg nd ar loadC wpC) ≤
      (if TZeroCase p then nCallsN q loadC + 2 * nCallsN q wpC
      else 12 * p.d * nCallsN q nd.V + nCallsN q loadC + 2 * nCallsN q wpC)) ∧
    (∀ q : J → Bool,
      ((sprotocol hS (p.ε / 200) (ctprepC p UJg nd ar loadC wpC) p.ratio
        (p.ratio_ge hp.g_ge)).worstCost (wCallN q) : ℝ) ≤
        40 * p.ratio * nCallsN q (ctprepC p UJg nd ar loadC wpC)) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((sprotocol hS (p.ε / 200) (ctprepC p UJg nd ar loadC wpC) p.ratio
        (p.ratio_ge hp.g_ge)).worstCost wGateN : ℝ) ≤
        (40 * p.ratio * nGatesN (ctprepC p UJg nd ar loadC wpC) +
          20 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
            Fintype.card Zs + Fintype.card S) + 3)) *
        (c₁ * Real.log ((10 * p.ratio * nGatesN (ctprepC p UJg nd ar loadC wpC) +
          5 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
            Fintype.card Zs + Fintype.card S) + 3) + 1) / (p.ε / 200)) + c₀)) ∧
    Fintype.card (TNW p S Zs Z ar.bT ar.bP ar.A ⊕ X) =
      Fintype.card S + 2 * (Fintype.card p.W + (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) +
        Fintype.card Zs) + Fintype.card S + 1 + Fintype.card X ∧
    ∀ (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
      (D : Label p.m p.l → ℕ → Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ))
      (Jl : Bool × (Fin p.m → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ)
      (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ)
      (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
      (bs : ℕ → Reg S ℂ) (βG δG βb δb bmax ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      0 ≤ ζs →
      ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs →
      (if TZeroCase p then 3 * ζs ≤ p.nu ∧
        TZInstanceOK p (seedV (S := S)) Jl Wp Hs Ls G b x bs βG δG βb δb bmax
      else NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) D false)) ∧
        24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu ∧
        p.InstanceOK (seedV (S := S))
          (⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ : TOracles p.a p.m p.l (Reg S ℂ))
          Hs Ls G b x bs βG δG βb δb bmax) →
      SOutcome (sprotocol hS (p.ε / 200) (ctprepC p UJg nd ar loadC wpC) p.ratio
        (p.ratio_ge hp.g_ge)) p.ε prim (x p.T) := by
  obtain ⟨hV, hG, hC, -, -, hcard, hout⟩ := ZeroTimeGateODE.native_ode_time_solver_nonneg p hp
    UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV
  have hε := hp.ε_pos
  have hεh := hp.ε_half
  have hη : 0 < p.ε / 200 := by positivity
  refine ⟨fun j => sprotocol_valid hS hη _ hV j, hG, hC,
    fun q => (sprotocol_worst hS hη _ hV p.ratio (p.ratio_ge hp.g_ge) q).2,
    fun c₀ c₁ hc₀ hc₁ hlen =>
      sprotocol_worst_log hS hη (by linarith) _ hV p.ratio (p.ratio_ge hp.g_ge) hc₀ hc₁ hlen,
    by rw [Fintype.card_sum, hcard], ?_⟩
  intro prim D Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hζs hload hwp hcase
  have hne : x p.T ≠ 0 := by
    by_cases hz : TZeroCase p
    · rw [if_pos hz] at hcase
      exact hcase.2.target_ne
    · rw [if_neg hz] at hcase
      exact hcase.2.2.target_ne
  exact soutcome hS hη (by linarith) (by linarith) _ hV p.ratio (p.ratio_ge hp.g_ge) prim hprim
    _ hne (hout prim D Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hζs hload hwp hcase)

end Synth

end

end SparseHamiltonian.GateRemarks.ODE
