import ZeroTimeGateODE.Time
import GateEfficientSynthesis.ODE

/-!
# Zero time or a known zero generator over a finite gate set, every trial synthesised

The finite-gate-set forms of Theorem `ode:thm:gates` of the accompanying paper that synthesise
every trial (`GateSynth.native_ode_solver_synth`, `GateSynth.native_ode_time_solver_synth`) run
the protocol `GateSynth.sprotocol hS (ε/200) prepN g`: every gate of every trial (the
preparation, its inverse, the zero tests and the sign) is synthesised over the finite gate set
`𝒢` under the hypothesis `GateSynth.Synthesis 𝒢 X len`, with the synthesis budget `ε/200` per
trial; its guarantee is `GateSynth.SOutcome` (success probability at least `2/3`, conditional
output within trace distance `ε`). The released library `ZeroTimeGateODE` proves the remark of
`ode:thm:gates` ("Zero time or a known zero generator uses direct source assembly and needs no
matrix calls") with the direct source assembly `zprepC (srcRot T r₀ r_b) srcC` (resp.
`tzprepC loadC wpC`) on every native register `ZNW …`, and lists its every-trial synthesised forms
as not formalised. They follow from its `GateNative.NOutcome` statements by the released
`GateSynth.soutcome`:

* `native_ode_solver_synth_zero` (constant coefficients): the protocol
  `sprotocol hS (ε/200) (zprepC (srcRot T r₀ r_b) srcC) g` on `ZNW … ⊕ X`;
* `native_ode_time_solver_synth_zero` (time-dependent coefficients): the protocol
  `sprotocol hS (ε/200) (tzprepC loadC wpC) (2g)` on `ZNW a m r K p.m l f … ⊕ X`.

Both: every synthesised trial consists of valid gates of `𝒢` and primitive calls; the counts of
one direct source assembly are exact; every history makes at most `40 g'` times the calls of the
supplied circuits (`g' = g`, resp. `2g`), hence no call of a kind they do not call (in particular
no matrix-oracle call if they make none); with `len ζ ≤ c₁ log(1/ζ) + c₀` the gates are at most
`(40 g' N + 20 g' (4 n + 3)) (c₁ log((10 g' N + 5 g' (4 n + 3) + 1)/(ε/200)) + c₀)`; the register
has the native qubits and `|X|` synthesis ancillas; under the hypotheses of the native zero-case
solvers the guarantee `SOutcome` holds.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateRemarks.ODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth
open ZeroTimeGateODE (zprepC tzprepC srcRot ZNW TZInstanceOK)
open GateODE (AW)
open GateODE.Time (TParams)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

section Synth

variable {S Zs Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Zero time or a known zero generator over a finite gate set, every trial synthesised,
constant coefficients** (remark of Theorem `ode:thm:gates`: direct source assembly, no matrix
calls).

With the synthesis hypothesis `Synthesis 𝒢 X len`, on every native ODE register
`ZNW a m r K k l f S Zs Z bT bP A` with the `|X|` synthesis ancillas, the synthesised protocol
`sprotocol hS (ε/200) (zprepC (srcRot T r₀ r_b) srcC) g` depends only on `T, g, ε, r₀, r_b`, the
source circuits and the synthesis. Every synthesised trial consists of valid gates of `𝒢` and
primitive calls; the direct source assembly has `N = |srcC 0| + |srcC 1| + 2` elementary gates
and exactly `calls_q(srcC 0) + calls_q(srcC 1)` calls of every kind `q`; in every history the
protocol makes at most `40 g` times these calls, so none of a kind that the source circuits do
not call, and, if `len ζ ≤ c₁ log(1/ζ) + c₀` (`c₀, c₁ ≥ 0`), uses at most
`(40 g N + 20 g (4 n + 3)) (c₁ log((10 g N + 5 g (4 n + 3) + 1)/(ε/200)) + c₀)` gates of `𝒢`
(`n = |AW| + |XW| + |Zs| + |S|`); its register has the native qubits plus `|X|`. For every
instance with the hypotheses of `ZeroTimeGateODE.native_ode_solver_zero` (unitary primitive
oracles and source interfaces, source circuits within `ζs`, `2 ζs ≤ ν`, `‖x₀‖ = r₀`, `‖b‖ = r_b`,
the seed promises, `x₀ + T b ≠ 0`, `r₀ + T r_b ≤ g ‖x₀ + T b‖`), the protocol has the guarantee
`SOutcome` against `x₀ + T b`: success probability at least `2/3` and a conditional output within
trace distance `ε` of `(x₀ + T b)/‖x₀ + T b‖`. -/
theorem native_ode_solver_synth_zero (hS : Synthesis 𝒢 X len) (a m r K k l f bT bP A : ℕ)
    (T g ε r₀ rb : ℝ) (hT : 0 ≤ T) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hr₀ : 0 ≤ r₀) (hrb : 0 ≤ rb) (hB : 0 < r₀ + T * rb)
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, (∀ i ∈ synthBudget hS (ε / 200) (trialN (zprepC (srcRot T r₀ rb) srcC :
        List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) j), i.Valid) ∧
      ∀ gt, NInstr.gate gt ∈ synthBudget hS (ε / 200) (trialN (zprepC (srcRot T r₀ rb) srcC :
        List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) j) → GateOf 𝒢 gt) ∧
    nGatesN (zprepC (srcRot T r₀ rb) srcC :
      List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) =
      nGatesN (srcC false) + nGatesN (srcC true) + 2 ∧
    (∀ q : J → Bool, nCallsN q (zprepC (srcRot T r₀ rb) srcC :
      List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) =
      nCallsN q (srcC false) + nCallsN q (srcC true)) ∧
    (∀ q : J → Bool, ((sprotocol hS (ε / 200) (zprepC (srcRot T r₀ rb) srcC :
      List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) g hg).worstCost (wCallN q) : ℝ) ≤
      40 * g * (nCallsN q (srcC false) + nCallsN q (srcC true) : ℕ)) ∧
    (∀ q : J → Bool, nCallsN q (srcC false) = 0 → nCallsN q (srcC true) = 0 →
      (sprotocol hS (ε / 200) (zprepC (srcRot T r₀ rb) srcC :
        List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) g hg).worstCost (wCallN q) = 0) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((sprotocol hS (ε / 200) (zprepC (srcRot T r₀ rb) srcC :
        List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) g hg).worstCost wGateN : ℝ) ≤
        (40 * g * (nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) +
          20 * g * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
            Fintype.card Zs + Fintype.card S) + 3)) *
        (c₁ * Real.log ((10 * g * (nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) +
          5 * g * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
            Fintype.card Zs + Fintype.card S) + 3) + 1) / (ε / 200)) + c₀)) ∧
    Fintype.card (ZNW a m r K k l f S Zs Z bT bP A ⊕ X) =
      Fintype.card S + 2 * (Fintype.card (AW a m r K k l f) +
        (Fintype.card Z + bT + bP + A + 3) + Fintype.card Zs) + Fintype.card S + 1 +
        Fintype.card X ∧
    ∀ (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (Jsrc : Bool → Reg S ℂ →L[ℂ] Reg S ℂ)
      (x0 b : Reg S ℂ) (ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      (∀ c, IsUnitary (Jsrc c)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun prim (srcC c)) (liftB (srcIdeal c (Jsrc c))) ζs) →
      2 * ζs ≤ ImprovedODEQueryBudget.precision g ε →
      ‖x0‖ = r₀ → ‖b‖ = rb →
      (x0 ≠ 0 → Jsrc false seedV = unitDirection x0) →
      (b ≠ 0 → Jsrc true seedV = unitDirection b) →
      x0 + T • b ≠ 0 →
      r₀ + T * rb ≤ g * ‖x0 + T • b‖ →
      SOutcome (sprotocol hS (ε / 200) (zprepC (srcRot T r₀ rb) srcC :
        List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) g hg) ε prim (x0 + T • b) := by
  obtain ⟨hV, hG, hC, -, -, -, hcard, hout⟩ := ZeroTimeGateODE.native_ode_solver_zero (S := S)
    (Zs := Zs) (Z := Z) (Y := Y) (J := J) a m r K k l f bT bP A T g ε r₀ rb hT hg hε hεHalf hr₀
    hrb hB srcC hsrcV
  have hη : 0 < ε / 200 := by positivity
  refine ⟨fun j => sprotocol_valid hS hη _ hV j, hG, hC, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    have h := (sprotocol_worst hS hη _ hV g hg q).2
    rw [hC q] at h
    exact h
  · intro q h0 h1
    have h := (sprotocol_worst hS hη _ hV g hg q).2
    rw [hC q, h0, h1] at h
    have h' : ((sprotocol hS (ε / 200) (zprepC (srcRot T r₀ rb) srcC :
        List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) g hg).worstCost (wCallN q) : ℝ) ≤
        0 := by simpa using h
    exact_mod_cast le_antisymm h' (Nat.cast_nonneg _)
  · intro c₀ c₁ hc₀ hc₁ hlen
    have h := sprotocol_worst_log hS hη (by linarith) _ hV g hg hc₀ hc₁ hlen
    rw [hG] at h
    exact h
  · rw [Fintype.card_sum, hcard]
  · intro prim Jsrc x0 b ζs hprim hJ hζs hsrc hbud h₀ hb hJ0 hJb hne hbudg
    exact soutcome hS hη (by linarith) (by linarith) _ hV g hg prim hprim _ hne
      (hout prim Jsrc x0 b ζs hprim hJ hζs hsrc hbud h₀ hb hJ0 hJb hne hbudg)

/-- **Zero time or a known zero generator over a finite gate set, every trial synthesised,
time-dependent coefficients** (remark of Theorem `ode:thm:gates`, time-dependent part).

For time-dependent public data `p` with `T ≥ 0`, `g ≥ 1`, `0 < ε ≤ 1/2`, `λ_H, λ_D ≥ 0` and
`T = 0 ∨ λ_H + R λ_D = 0`, with the synthesis hypothesis `Synthesis 𝒢 X len`, on every native
ODE register `ZNW a m r K p.m l f S Zs Z bT bP A` with the `|X|` synthesis ancillas, the
synthesised protocol `sprotocol hS (ε/200) (tzprepC loadC wpC) (2g)`: every synthesised trial
consists of valid gates of `𝒢` and primitive calls; the direct source assembly has
`N = |loadC| + 2 |wpC|` elementary gates and exactly `calls_q(loadC) + 2 calls_q(wpC)` calls of
every kind `q`; every history makes at most `40 · 2g` times these calls, so none of a kind that
the supplied circuits do not call, and, if `len ζ ≤ c₁ log(1/ζ) + c₀`, uses at most
`(40 · 2g N + 20 · 2g (4 n + 3)) (c₁ log((10 · 2g N + 5 · 2g (4 n + 3) + 1)/(ε/200)) + c₀)` gates
of `𝒢`; the register has the native qubits plus `|X|`. For every instance with the hypotheses of
`ZeroTimeGateODE.native_ode_time_solver_zero` (unitary primitive oracles, loading and
weight-preparation circuits within `ζs`, `3 ζs ≤ ν`, `TZInstanceOK`), the protocol has the
guarantee `SOutcome` against `x(T)`. -/
theorem native_ode_time_solver_synth_zero (hS : Synthesis 𝒢 X len) (p : TParams)
    (a m r K l f bT bP A : ℕ) (hT : 0 ≤ p.T) (hg : 1 ≤ p.g) (hε : 0 < p.ε)
    (hεHalf : p.ε ≤ 1 / 2) (hlamH : 0 ≤ p.lamH) (hlamD : 0 ≤ p.lamD)
    (hz : p.T = 0 ∨ p.lamH + p.R * p.lamD = 0)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ synthBudget hS (p.ε / 200) (trialN (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) j), i.Valid) ∧
      ∀ gt, NInstr.gate gt ∈ synthBudget hS (p.ε / 200) (trialN (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) j) → GateOf 𝒢 gt) ∧
    nGatesN (tzprepC loadC wpC : List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) =
      nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ q : J → Bool, nCallsN q (tzprepC loadC wpC :
      List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) =
      nCallsN q loadC + 2 * nCallsN q wpC) ∧
    (∀ q : J → Bool, ((sprotocol hS (p.ε / 200) (tzprepC loadC wpC :
      List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) p.ratio
        (p.ratio_ge hg)).worstCost (wCallN q) : ℝ) ≤
      40 * p.ratio * (nCallsN q loadC + 2 * nCallsN q wpC : ℕ)) ∧
    (∀ q : J → Bool, nCallsN q loadC = 0 → nCallsN q wpC = 0 →
      (sprotocol hS (p.ε / 200) (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) p.ratio
          (p.ratio_ge hg)).worstCost (wCallN q) = 0) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((sprotocol hS (p.ε / 200) (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) p.ratio
          (p.ratio_ge hg)).worstCost wGateN : ℝ) ≤
        (40 * p.ratio * (nGatesN loadC + 2 * nGatesN wpC : ℕ) +
          20 * p.ratio * (4 * (Fintype.card (AW a m r K p.m l f) + Fintype.card (XW Z bT bP A) +
            Fintype.card Zs + Fintype.card S) + 3)) *
        (c₁ * Real.log ((10 * p.ratio * (nGatesN loadC + 2 * nGatesN wpC : ℕ) +
          5 * p.ratio * (4 * (Fintype.card (AW a m r K p.m l f) + Fintype.card (XW Z bT bP A) +
            Fintype.card Zs + Fintype.card S) + 3) + 1) / (p.ε / 200)) + c₀)) ∧
    Fintype.card (ZNW a m r K p.m l f S Zs Z bT bP A ⊕ X) =
      Fintype.card S + 2 * (Fintype.card (AW a m r K p.m l f) +
        (Fintype.card Z + bT + bP + A + 3) + Fintype.card Zs) + Fintype.card S + 1 +
        Fintype.card X ∧
    ∀ (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ) (Jl : Bool × (Fin p.m → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ)
      (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ)
      (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b x : ℝ → Reg S ℂ)
      (bs : ℕ → Reg S ℂ) (βG δG βb δb bmax ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      0 ≤ ζs →
      ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs →
      3 * ζs ≤ p.nu →
      TZInstanceOK p (seedV (S := S)) Jl Wp Hs Ls G b x bs βG δG βb δb bmax →
      SOutcome (sprotocol hS (p.ε / 200) (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) p.ratio (p.ratio_ge hg)) p.ε
        prim (x p.T) := by
  obtain ⟨hV, hG, hC, -, -, -, hcard, hout⟩ := ZeroTimeGateODE.native_ode_time_solver_zero
    (S := S) (Zs := Zs) (Z := Z) (Y := Y) (J := J) p a m r K l f bT bP A hT hg hε hεHalf hlamH
    hlamD hz loadC hloadV wpC hwpV
  have hη : 0 < p.ε / 200 := by positivity
  refine ⟨fun j => sprotocol_valid hS hη _ hV j, hG, hC, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    have h := (sprotocol_worst hS hη _ hV p.ratio (p.ratio_ge hg) q).2
    rw [hC q] at h
    exact h
  · intro q h0 h1
    have h := (sprotocol_worst hS hη _ hV p.ratio (p.ratio_ge hg) q).2
    rw [hC q, h0, h1] at h
    have h' : ((sprotocol hS (p.ε / 200) (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) p.ratio
          (p.ratio_ge hg)).worstCost (wCallN q) : ℝ) ≤ 0 := by simpa using h
    exact_mod_cast le_antisymm h' (Nat.cast_nonneg _)
  · intro c₀ c₁ hc₀ hc₁ hlen
    have h := sprotocol_worst_log hS hη (by linarith) _ hV p.ratio (p.ratio_ge hg) hc₀ hc₁ hlen
    rw [hG] at h
    exact h
  · rw [Fintype.card_sum, hcard]
  · intro prim Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hζs hload hwp hbud hI
    exact soutcome hS hη (by linarith) (by linarith) _ hV p.ratio (p.ratio_ge hg) prim hprim _
      hI.target_ne
      (hout prim Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hζs hload hwp hbud hI)

end Synth

end

end SparseHamiltonian.GateRemarks.ODE
