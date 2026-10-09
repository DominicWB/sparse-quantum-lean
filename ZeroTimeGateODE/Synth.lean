import ZeroTimeGateODE.Time
import GateEfficientSynthesisTrials.Solver

/-!
# Zero time or a known zero generator over a finite gate set, with the per-trial claim

The finite-gate-set forms of Theorem `ode:thm:gates` with its per-trial claim
(`GateSynthTrials.native_ode_solver_trials`, `native_ode_time_solver_trials`) synthesise only the
native preparation, keep its exact adjoint as the inverse and the zero tests exact, on the trial
register `GateSynthTrials.SWO`.  The same released construction applies to the direct source
assembly: the synthesised preparation `synthPrep hS (ν/3) (zprepC …)` (resp. `tzprepC …`) is
within `ν/3 + 2 ζs` (resp. `ν/3 + 3 ζs`) of the lifted released counterpart
(`GateSynthTrials.synthPrep_approx`), which is at most `2ν` under the native budgets, so the
certificate of the direct source assembly (`noutcome_of_released`, `noutcome_direct_retarget`)
gives the per-trial guarantees.

* `native_ode_solver_zero_trials` (constant coefficients) and
  `native_ode_time_solver_zero_trials` (time-dependent coefficients): every trial consists of
  valid gates of `𝒢` and primitive calls; the synthesised preparation has at most
  `N len(ν/3/(N+1))` gates for the `N` gates of the direct source assembly and exactly its
  primitive calls (those of the source circuits); every history makes at most `40 g` (resp.
  `80 g`) times these calls and uses at most `40 g N_S + 20 g (4 n + 3)` gates (resp. with `2g`),
  and with `len ζ ≤ c₁ log(1/ζ) + c₀` at most `40 g N (c₁ log((N+1)/(ν/3)) + c₀) + 20 g (4 n + 3)`;
  the guarantees `NOutcome` hold under the hypotheses of the native zero-case solvers.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth GateSynthTrials
open GateCircuit.Sim (Wire)
open GateODE (OInstr OWire AW goodF Label Oracles wiring)
open GateODE.Time (TParams TOracles trun)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

section Synth

variable {S Zs Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Zero time or a known zero generator over a finite gate set, with the per-trial claim,
constant coefficients** (remark of Theorem `ode:thm:gates`).

With the synthesis hypothesis `Synthesis 𝒢 X len`, an adjoint-closed `𝒢` containing the four
kinds of the exact zero tests, and `ν = ε / (10000 g)`, the protocol
`nprotocol (synthPrep hS (ν/3) (zprepC (srcRot T r₀ r_b) srcC)) g` on the trial register
`SWO … X` of the native register `ZNW a m r K k l f S Zs Z bT bP A`: every trial consists of
valid gates of `𝒢` and primitive calls; the synthesised preparation has at most
`N len(ν/3/(N+1))` gates, `N = |srcC 0| + |srcC 1| + 2`, and exactly the calls of the source
circuits; every history makes at most `40 g` times these calls and uses at most
`40 g N_S + 20 g (4 n + 3)` gates (`N_S` the synthesised gates, `n` the tested wires), and at
most `40 g N (c₁ log((N+1)/(ν/3)) + c₀) + 20 g (4 n + 3)` gates if
`len ζ ≤ c₁ log(1/ζ) + c₀`; the trial register has
`|S| + 2 (|AW| + (|Z| + bT + bP + A + 3) + (|Zs| + 1 + n_P + |X|)) + |S| + 1` qubits.  Under the
hypotheses of `native_ode_solver_zero` the protocol has the guarantees `NOutcome` against
`x₀ + T b`; in particular every successful trial is within `ε/500` of the normalised target up
to a global phase. -/
theorem native_ode_solver_zero_trials (hS : Synthesis 𝒢 X len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) (a m r K k l f bT bP A : ℕ) (T g ε r₀ rb : ℝ) (hT : 0 ≤ T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) (hr₀ : 0 ≤ r₀) (hrb : 0 ≤ rb)
    (hB : 0 < r₀ + T * rb) (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J))
    (hsrcV : ∀ c, ∀ i ∈ srcC c, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (ImprovedODEQueryBudget.precision g ε / 3)
        (zprepC (srcRot T r₀ rb) srcC :
          List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J))) j, i.Valid) ∧
      ∀ gt, NInstr.gate gt ∈ trialN (synthPrep hS (ImprovedODEQueryBudget.precision g ε / 3)
        (zprepC (srcRot T r₀ rb) srcC :
          List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J))) j → GateOf 𝒢 gt) ∧
    nGatesN (synthPrep hS (ImprovedODEQueryBudget.precision g ε / 3)
        (zprepC (srcRot T r₀ rb) srcC : List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J))) ≤
      (nGatesN (srcC false) + nGatesN (srcC true) + 2) *
        len (ImprovedODEQueryBudget.precision g ε / 3 /
          ((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) + 1)) ∧
    (∀ q : J → Bool, nCallsN q (synthPrep hS (ImprovedODEQueryBudget.precision g ε / 3)
        (zprepC (srcRot T r₀ rb) srcC : List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J))) =
      nCallsN q (srcC false) + nCallsN q (srcC true)) ∧
    (∀ q : J → Bool, ((nprotocol (synthPrep hS (ImprovedODEQueryBudget.precision g ε / 3)
        (zprepC (srcRot T r₀ rb) srcC : List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)))
          g hg).worstCost (wCallN q) : ℝ) ≤
      40 * g * (nCallsN q (srcC false) + nCallsN q (srcC true) : ℕ)) ∧
    ((nprotocol (synthPrep hS (ImprovedODEQueryBudget.precision g ε / 3)
        (zprepC (srcRot T r₀ rb) srcC : List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)))
          g hg).worstCost wGateN : ℝ) ≤
      40 * g * nGatesN (synthPrep hS (ImprovedODEQueryBudget.precision g ε / 3)
        (zprepC (srcRot T r₀ rb) srcC : List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J))) +
        20 * g * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card (SX Zs (zPool a m r K k l f S Zs Z bT bP A) X) + Fintype.card S) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (synthPrep hS (ImprovedODEQueryBudget.precision g ε / 3)
        (zprepC (srcRot T r₀ rb) srcC : List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)))
          g hg).worstCost wGateN : ℝ) ≤
        40 * g * ((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) *
          (c₁ * Real.log (((nGatesN (srcC false) + nGatesN (srcC true) + 2 : ℕ) + 1) /
            (ImprovedODEQueryBudget.precision g ε / 3)) + c₀)) +
        20 * g * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card (SX Zs (zPool a m r K k l f S Zs Z bT bP A) X) + Fintype.card S) + 3)) ∧
    Fintype.card (SWO a m r K k l f S Zs (zPool a m r K k l f S Zs Z bT bP A) Z bT bP A X) =
      Fintype.card S + 2 * (Fintype.card (AW a m r K k l f) + (Fintype.card Z + bT + bP + A + 3) +
        (Fintype.card Zs + 1 + zPool a m r K k l f S Zs Z bT bP A + Fintype.card X)) +
        Fintype.card S + 1 ∧
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
      NOutcome (synthPrep hS (ImprovedODEQueryBudget.precision g ε / 3)
        (zprepC (srcRot T r₀ rb) srcC : List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)))
          g ε hg prim (x0 + T • b) := by
  have hu := srcRot_unitary T r₀ rb hT hr₀ hrb hB
  have hprepV := zprepC_valid (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
    (nP := zPool a m r K k l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A)
    (srcRot T r₀ rb) hu srcC hsrcV
  have hcount := fun q => zprepC_counts (a := a) (m := m) (r := r) (K := K) (k := k) (l := l)
    (f := f) (nP := zPool a m r K k l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A)
    (srcRot T r₀ rb) srcC q
  have hν : 0 < ImprovedODEQueryBudget.precision g ε :=
    ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hν1 : ImprovedODEQueryBudget.precision g ε ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth g ε hg (hεHalf.trans (by norm_num))
  have hη : 0 < ImprovedODEQueryBudget.precision g ε / 3 := by positivity
  have hη1 : ImprovedODEQueryBudget.precision g ε / 3 ≤ 1 := by linarith
  obtain ⟨hSG, hSC⟩ := synthPrep_counts hS hη _ hprepV
  obtain ⟨hWC, hWG⟩ := synth_protocol_worst hS hη _ hprepV g hg
  have hG : nGatesN (zprepC (srcRot T r₀ rb) srcC :
      List (NInstr (ZNW a m r K k l f S Zs Z bT bP A) Y J)) =
      nGatesN (srcC false) + nGatesN (srcC true) + 2 := (hcount (fun _ => true)).1
  refine ⟨fun j => ⟨trialS_valid hS hη _ hprepV j, trialS_gateOf hS hadj hzt hη _ hprepV j⟩,
    ?_, ?_, ?_, hWG, ?_, card_SWO, ?_⟩
  · rw [← hG]
    exact hSG
  · intro q
    rw [hSC q, (hcount q).2]
  · intro q
    rw [← (hcount q).2]
    exact hWC q
  · intro c₀ c₁ hc₀ hc₁ hlen
    rw [← hG]
    exact synth_protocol_worst_log hS hη hη1 _ hprepV g hg hc₀ hc₁ hlen
  · intro prim Jsrc x0 b ζs hprim hJ hζs hsrc hbudget h₀ hb hJ0 hJb hne hbud
    let σ : Oracles a (Label k l) (Reg S ℂ) := ⟨1, fun _ => 1, Jsrc⟩
    have hA := zprepC_approx (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
      (nP := zPool a m r K k l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A) prim
      hprim (srcRot T r₀ rb) hu srcC hsrcV seedV σ hJ hζs hsrc
    have hrel := srcRot_decoded (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
      T r₀ rb hT hr₀ hrb hB seedV σ x0 b h₀ hb hJ0 hJb
    generalize GateODE.run (wiring (a := a) (m := m) (r := r) (K := K) (k := k) (l := l) (f := f)
      seedV) σ (zrelC (srcRot T r₀ rb)) = Urel at hA hrel
    have hAS := synthPrep_approx hS hη _ hprepV prim hprim Urel (by linarith) hA
    exact noutcome_of_released hnP_SWO _ prim hprim (synthPrep_valid hS hη _ hprepV)
      (synthPrep_pres hS _ _ prim) Urel hAS (x0 + T • b) (r₀ + T * rb) g ε hne hg hε hεHalf hB
      hbud hrel (by linarith)

/-- **Zero time or a known zero generator over a finite gate set, with the per-trial claim,
time-dependent coefficients** (remark of Theorem `ode:thm:gates`, time-dependent part).

With the synthesis hypotheses and `ν = (ε/2) / (10000 · 2g)`, the protocol
`nprotocol (synthPrep hS (ν/3) (tzprepC loadC wpC)) (2g)` on the trial register of
`ZNW a m r K p.m l f S Zs Z bT bP A`: every trial consists of valid gates of `𝒢` and primitive
calls; the synthesised preparation has at most `N len(ν/3/(N+1))` gates,
`N = |loadC| + 2 |wpC|`, and exactly the calls of the supplied circuits; every history makes at
most `40 · 2g` times these calls and uses at most `40 · 2g N_S + 20 · 2g (4 n + 3)` gates, and
at most `40 · 2g N (c₁ log((N+1)/(ν/3)) + c₀) + 20 · 2g (4 n + 3)` gates if
`len ζ ≤ c₁ log(1/ζ) + c₀`.  Under the hypotheses of `native_ode_time_solver_zero` the protocol
has the guarantees `NOutcome` against `x(T)`. -/
theorem native_ode_time_solver_zero_trials (hS : Synthesis 𝒢 X len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) (p : TParams) (a m r K l f bT bP A : ℕ) (hT : 0 ≤ p.T)
    (hg : 1 ≤ p.g) (hε : 0 < p.ε) (hεHalf : p.ε ≤ 1 / 2) (hlamH : 0 ≤ p.lamH)
    (hlamD : 0 ≤ p.lamD) (hz : p.T = 0 ∨ p.lamH + p.R * p.lamD = 0)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (p.nu / 3) (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))) j, i.Valid) ∧
      ∀ gt, NInstr.gate gt ∈ trialN (synthPrep hS (p.nu / 3) (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))) j → GateOf 𝒢 gt) ∧
    nGatesN (synthPrep hS (p.nu / 3) (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))) ≤
      (nGatesN loadC + 2 * nGatesN wpC) *
        len (p.nu / 3 / ((nGatesN loadC + 2 * nGatesN wpC : ℕ) + 1)) ∧
    (∀ q : J → Bool, nCallsN q (synthPrep hS (p.nu / 3) (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))) =
      nCallsN q loadC + 2 * nCallsN q wpC) ∧
    (∀ q : J → Bool, ((nprotocol (synthPrep hS (p.nu / 3) (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))) p.ratio
          (p.ratio_ge hg)).worstCost (wCallN q) : ℝ) ≤
      40 * p.ratio * (nCallsN q loadC + 2 * nCallsN q wpC : ℕ)) ∧
    ((nprotocol (synthPrep hS (p.nu / 3) (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))) p.ratio
          (p.ratio_ge hg)).worstCost wGateN : ℝ) ≤
      40 * p.ratio * nGatesN (synthPrep hS (p.nu / 3) (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))) +
        20 * p.ratio * (4 * (Fintype.card (AW a m r K p.m l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card (SX Zs (zPool a m r K p.m l f S Zs Z bT bP A) X) + Fintype.card S) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (synthPrep hS (p.nu / 3) (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))) p.ratio
          (p.ratio_ge hg)).worstCost wGateN : ℝ) ≤
        40 * p.ratio * ((nGatesN loadC + 2 * nGatesN wpC : ℕ) *
          (c₁ * Real.log (((nGatesN loadC + 2 * nGatesN wpC : ℕ) + 1) / (p.nu / 3)) + c₀)) +
        20 * p.ratio * (4 * (Fintype.card (AW a m r K p.m l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card (SX Zs (zPool a m r K p.m l f S Zs Z bT bP A) X) + Fintype.card S) + 3)) ∧
    Fintype.card (SWO a m r K p.m l f S Zs (zPool a m r K p.m l f S Zs Z bT bP A) Z bT bP A X) =
      Fintype.card S + 2 * (Fintype.card (AW a m r K p.m l f) +
        (Fintype.card Z + bT + bP + A + 3) +
        (Fintype.card Zs + 1 + zPool a m r K p.m l f S Zs Z bT bP A + Fintype.card X)) +
        Fintype.card S + 1 ∧
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
      NOutcome (synthPrep hS (p.nu / 3) (tzprepC loadC wpC :
        List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))) p.ratio p.ε (p.ratio_ge hg) prim
          (x p.T) := by
  have hεOne : p.ε ≤ 1 := hεHalf.trans (by norm_num)
  have hprepV := tzprepC_valid (a := a) (m := m) (r := r) (K := K) (k := p.m) (l := l) (f := f)
    (nP := zPool a m r K p.m l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A)
    loadC hloadV wpC hwpV
  have hcount := fun q => tzprepC_counts (a := a) (m := m) (r := r) (K := K) (k := p.m) (l := l)
    (f := f) (nP := zPool a m r K p.m l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A)
    loadC wpC q
  have hν : 0 < p.nu := p.nu_pos hg hε
  have hν1 : p.nu ≤ 1 := p.nu_le_one hg hεOne
  have hη : 0 < p.nu / 3 := by positivity
  have hη1 : p.nu / 3 ≤ 1 := by linarith
  obtain ⟨hSG, hSC⟩ := synthPrep_counts hS hη _ hprepV
  obtain ⟨hWC, hWG⟩ := synth_protocol_worst hS hη _ hprepV p.ratio (p.ratio_ge hg)
  have hG : nGatesN (tzprepC loadC wpC : List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J)) =
      nGatesN loadC + 2 * nGatesN wpC := (hcount (fun _ => true)).1
  refine ⟨fun j => ⟨trialS_valid hS hη _ hprepV j, trialS_gateOf hS hadj hzt hη _ hprepV j⟩,
    ?_, ?_, ?_, hWG, ?_, card_SWO, ?_⟩
  · rw [← hG]
    exact hSG
  · intro q
    rw [hSC q, (hcount q).2]
  · intro q
    rw [← (hcount q).2]
    exact hWC q
  · intro c₀ c₁ hc₀ hc₁ hlen
    rw [← hG]
    exact synth_protocol_worst_log hS hη hη1 _ hprepV p.ratio (p.ratio_ge hg) hc₀ hc₁ hlen
  · intro prim Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hζs hload hwp hbudget hI
    let σ : TOracles a p.m l (Reg S ℂ) := ⟨1, fun _ _ => 1, Jl, Wp⟩
    have hσ : σ.Unitary m := ⟨isUnitary_one, fun _ _ _ => isUnitary_one, hI.load_unitary,
      hI.prep_left, hI.prep_right⟩
    have hA := tzprepC_approx (a := a) (m := m) (r := r) (K := K) (k := p.m) (l := l) (f := f)
      (nP := zPool a m r K p.m l f S Zs Z bT bP A) (Z := Z) (bT := bT) (bP := bP) (A := A) prim
      hprim loadC hloadV wpC hwpV seedV σ hσ hζs hload hwp
    have hzero := tzero_samples p hg hε hεOne hlamH hlamD hz Hs Ls hI.normH hI.normL
    have hy : p.target Hs Ls (x 0) bs = ∑ s, p.zsrc (x 0) bs s := by
      rw [ttarget_zero p Hs Ls (x 0) bs hzero, zsrc_sum]
    have hErr := p.discretisation_error hT G b x Hs Ls bs βG δG βb δb bmax hI.βG_nonneg
      hI.βb_nonneg hI.solves hI.accretive hI.lipG hI.sampleG hI.lipb hI.sampleb hI.boundb
      hI.selfH hI.psd hI.normH hI.normL
    obtain ⟨hy0, hbud, hdirY⟩ := TimeDependentODE.Sampling.target_budget (x p.T)
      (p.target Hs Ls (x 0) bs) (p.mass (x 0) bs) p.g p.ε _ hg hε hεOne hI.target_ne hI.budget
      hErr hI.disc
    have hNorm := p.target_norm_le hT Hs Ls hI.selfH hI.psd (x 0) bs
    have hB : 0 < p.mass (x 0) bs := (norm_pos_iff.mpr hy0).trans_le hNorm
    have hrel := tz_decoded p (a := a) (m := m) (r := r) (K := K) (l := l) (f := f) hT seedV σ
      (x 0) bs hB hI.prep hI.init_load hI.forcing_load
    rw [← hy] at hrel
    have hacc : p.acc ≤ 1 / 2 := by
      simp only [GateODE.Time.TParams.acc]
      linarith
    generalize trun (a := a) (m := m) (r := r) (K := K) (l := l) (f := f) seedV σ tzrelC = Urel
      at hA hrel
    have hAS := synthPrep_approx hS hη _ hprepV prim hprim Urel (by linarith) hA
    have hvec := vector_error_direct _ Urel hAS (p.target Hs Ls (x 0) bs) (p.mass (x 0) bs)
      hB.le hrel
    have hvec' : ‖p.mass (x 0) bs • (goodN†) (nrun prim (synthPrep hS (p.nu / 3)
        (tzprepC loadC wpC : List (NInstr (ZNW a m r K p.m l f S Zs Z bT bP A) Y J))) sN) -
        p.target Hs Ls (x 0) bs‖ ≤
        2 * ImprovedODEQueryBudget.precision p.ratio p.acc * p.mass (x 0) bs := by
      refine hvec.trans ?_
      have e : p.nu = ImprovedODEQueryBudget.precision p.ratio p.acc := rfl
      nlinarith
    have hbud' : p.mass (x 0) bs ≤ p.ratio * ‖p.target Hs Ls (x 0) bs‖ := hbud
    have e : p.acc / 500 + p.ε / 1000 = p.ε / 500 := by
      simp only [GateODE.Time.TParams.acc]
      ring
    exact noutcome_direct_retarget hnP_SWO _ prim hprim (synthPrep_valid hS hη _ hprepV)
      (synthPrep_pres hS _ _ prim) (p.target Hs Ls (x 0) bs) (x p.T) (p.mass (x 0) bs) p.ratio
      p.ε p.acc (p.ε / 1000) hy0 hI.target_ne (p.ratio_ge hg) hε (p.acc_pos hε) hacc hB hbud'
      hvec' hdirY e.le

end Synth

end

end SparseHamiltonian.ZeroTimeGateODE
