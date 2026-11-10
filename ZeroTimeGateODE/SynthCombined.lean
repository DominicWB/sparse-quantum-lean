import ZeroTimeGateODE.Synth
import ZeroTimeGateODE.Combined
import ZeroTimeGateODE.TimeCombined

/-!
# The finite-gate-set solvers with the per-trial claim for every `T ≥ 0`

The released finite-gate-set forms with the per-trial claim
(`GateSynthTrials.native_ode_solver_trials`, `native_ode_time_solver_trials`) synthesise the
released native preparation with budget `ν/3`.  For every `T ≥ 0` the same synthesis applies to
the preparations `cprepC` and `ctprepC` (direct source assembly in the zero case, released
preparation otherwise): the synthesised preparation `synthPrep hS (ν/3) (cprepC p …)` has the
released synthesis counts in terms of the counts of `cprepC p …`, which are
`if ZeroCase p then <direct source assembly> else <released>`, and the guarantees `NOutcome`
under the zero-case conditions in the zero case (`native_ode_solver_zero_trials`,
`native_ode_time_solver_zero_trials`) and under the released conditions otherwise.

* `native_ode_solver_nonneg_trials` (constant coefficients);
* `native_ode_time_solver_nonneg_trials` (time-dependent coefficients).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.ZeroTimeGateODE

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth GateSynthTrials
open GateODE (Params Label Oracles)
open GateODE.Time (TParams TOracles)
open scoped InnerProduct BigOperators

section Main

variable {S Zs Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Native solver over a finite gate set, with the per-trial claim, for every `T ≥ 0`,
constant coefficients** (partial formalisation, under this package's format hypotheses, of the
finite-set statement of Theorem `ode:thm:gates` with its remark on zero time
and a known zero generator).

For public data `p` with `PublicOK0 p`, the released public native data and the synthesis
hypotheses (`Synthesis 𝒢 X len`, `𝒢` adjoint-closed and containing the kinds of the exact zero
tests), the protocol `nprotocol (synthPrep hS (ν/3) (cprepC p UJg nd ar srcC)) g` on the trial
register `SNW p S Zs Z bT bP A X`: every trial consists of valid gates of `𝒢` and primitive
calls; the unsynthesised preparation `cprepC p …` has at most
`if ZeroCase p then |srcC 0| + |srcC 1| + 2 else <released>` gates and
`if ZeroCase p then calls(srcC 0) + calls(srcC 1) else <released>` calls of every kind; the
synthesised preparation has at most `N len(ν/3/(N+1))` gates and exactly the calls of `cprepC`
(`N` its gates); every history makes at most `40 g` times these calls and uses at most
`40 g N_S + 20 g (4 n + 3)` gates, and at most `40 g N (c₁ log((N+1)/(ν/3)) + c₀) + 20 g (4 n + 3)`
gates if `len ζ ≤ c₁ log(1/ζ) + c₀`; the trial register has the released qubit count.  For every
instance with unitary primitive oracles and source circuits within `ζs`, the protocol has the
guarantees `NOutcome` against the released target `x(T)`, under `2 ζs ≤ ν` and `ZInstanceOK` in
the zero case and under the released conditions otherwise. -/
theorem native_ode_solver_nonneg_trials (hS : Synthesis 𝒢 X len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) (p : Params) (hp : PublicOK0 p)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (LabW p.k p.l) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (LabW p.k p.l) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (hsrcV : ∀ b, ∀ i ∈ srcC b, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (p.nu / 3) (cprepC p UJg nd ar srcC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (p.nu / 3) (cprepC p UJg nd ar srcC)) j →
        GateOf 𝒢 g) ∧
    nGatesN (cprepC p UJg nd ar srcC) ≤
      (if ZeroCase p then nGatesN (srcC false) + nGatesN (srcC true) + 2
      else p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar +
        nGatesN (srcC false) + nGatesN (srcC true)) ∧
    (∀ q : J → Bool, nCallsN q (cprepC p UJg nd ar srcC) ≤
      (if ZeroCase p then nCallsN q (srcC false) + nCallsN q (srcC true)
      else 12 * p.d * nCallsN q nd.V + nCallsN q (srcC false) + nCallsN q (srcC true))) ∧
    nGatesN (synthPrep hS (p.nu / 3) (cprepC p UJg nd ar srcC)) ≤
      nGatesN (cprepC p UJg nd ar srcC) *
        len (p.nu / 3 / (nGatesN (cprepC p UJg nd ar srcC) + 1)) ∧
    (∀ q : J → Bool, nCallsN q (synthPrep hS (p.nu / 3) (cprepC p UJg nd ar srcC)) =
      nCallsN q (cprepC p UJg nd ar srcC)) ∧
    (∀ q : J → Bool,
      ((nprotocol (synthPrep hS (p.nu / 3) (cprepC p UJg nd ar srcC)) p.g hp.g_ge).worstCost
        (wCallN q) : ℝ) ≤ 40 * p.g * nCallsN q (cprepC p UJg nd ar srcC)) ∧
    ((nprotocol (synthPrep hS (p.nu / 3) (cprepC p UJg nd ar srcC)) p.g hp.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * p.g * nGatesN (synthPrep hS (p.nu / 3) (cprepC p UJg nd ar srcC)) +
        20 * p.g * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card (SX Zs (nPool p S Zs Z ar.bT ar.bP ar.A) X) + Fintype.card S) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (synthPrep hS (p.nu / 3) (cprepC p UJg nd ar srcC)) p.g hp.g_ge).worstCost
          wGateN : ℝ) ≤
        40 * p.g * (nGatesN (cprepC p UJg nd ar srcC) *
          (c₁ * Real.log ((nGatesN (cprepC p UJg nd ar srcC) + 1) / (p.nu / 3)) + c₀)) +
        20 * p.g * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card (SX Zs (nPool p S Zs Z ar.bT ar.bP ar.A) X) + Fintype.card S) + 3)) ∧
    Fintype.card (SNW p S Zs Z ar.bT ar.bP ar.A X) =
      Fintype.card S + 2 * (Fintype.card p.W + (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) +
        (Fintype.card Zs + 1 + nPool p S Zs Z ar.bT ar.bP ar.A + Fintype.card X)) +
        Fintype.card S + 1 ∧
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
      NOutcome (synthPrep hS (p.nu / 3) (cprepC p UJg nd ar srcC)) p.g p.ε hp.g_ge prim
        (p.target H L x0 b) := by
  obtain ⟨hV, hG, hC, -, -, -, -⟩ :=
    native_ode_solver_nonneg p hp UJg hUJg nd hnd ar ζ hζ har srcC hsrcV
  have hprepV : ∀ i ∈ cprepC p UJg nd ar srcC, i.Valid :=
    fun i hi => hV 0 i (List.mem_append_left _ hi)
  have hν : 0 < p.nu := ImprovedODEQueryBudget.precision_pos p.g p.ε hp.g_ge hp.ε_pos
  have hν1 : p.nu ≤ 1 / 10000 := ImprovedODEQueryBudget.precision_le_one_ten_thousandth p.g p.ε
    hp.g_ge (hp.ε_half.trans (by norm_num))
  have hη : 0 < p.nu / 3 := by positivity
  have hη1 : p.nu / 3 ≤ 1 := by linarith
  obtain ⟨hSG, hSC⟩ := synthPrep_counts hS hη _ hprepV
  obtain ⟨hWC, hWG⟩ := synth_protocol_worst hS hη _ hprepV p.g hp.g_ge
  refine ⟨fun j => ⟨trialS_valid hS hη _ hprepV j, trialS_gateOf hS hadj hzt hη _ hprepV j⟩,
    hG, hC, hSG, hSC, hWC, hWG,
    fun c₀ c₁ hc₀ hc₁ hlen =>
      synth_protocol_worst_log hS hη hη1 _ hprepV p.g hp.g_ge hc₀ hc₁ hlen, card_SWO, ?_⟩
  intro prim D Jsrc H L x0 b ζs hprim hζs hsrc hcase
  by_cases hz : ZeroCase p
  · rw [if_pos hz] at hcase
    obtain ⟨hbudget, hI⟩ := hcase
    have ht := target_zero hp hz H L x0 b hI.normH hI.normL
    have hne := hI.target_ne
    have hbud := hI.budget
    rw [ht] at hne hbud ⊢
    obtain ⟨-, -, -, -, -, -, -, hout⟩ := native_ode_solver_zero_trials (S := S) (Zs := Zs)
      (Z := Z) (Y := Y) (J := J) hS hadj hzt p.a p.m p.r p.K p.k p.l p.f ar.bT ar.bP ar.A p.T
      p.g p.ε p.r₀ p.rb hp.T_nonneg hp.g_ge hp.ε_pos hp.ε_half hp.r₀_nonneg hp.rb_nonneg hp.B_pos
      srcC hsrcV
    rw [cprepC, if_pos hz]
    exact hout prim Jsrc x0 b ζs hprim hI.src_unitary hζs hsrc hbudget hI.init_norm
      hI.forcing_norm hI.init_prep hI.forcing_prep hne hbud
  · rw [if_neg hz] at hcase
    obtain ⟨hN, hbud, hI⟩ := hcase
    obtain ⟨-, -, -, -, -, -, -, -, -, hout⟩ := native_ode_solver_trials hS hadj hzt p
      (publicOK_of hp hz) UJg hUJg nd hnd ar ζ hζ har srcC hsrcV
    rw [cprepC, if_neg hz]
    exact hout prim D Jsrc H L x0 b ζs hprim hN hζs hsrc hbud hI

/-- **Native solver over a finite gate set, with the per-trial claim, for every `T ≥ 0`,
time-dependent coefficients** (partial formalisation, under this package's format hypotheses, of
the finite-set statement of Theorem `ode:thm:gates`, time-dependent part,
with its remark on zero time and a known zero generator).

For public data `p` with `TPublicOK0 p`, the released public native data and the synthesis
hypotheses, the protocol `nprotocol (synthPrep hS (ν/3) (ctprepC p UJg nd ar loadC wpC)) (2g)` on
the trial register `STW p S Zs Z bT bP A X`: every trial consists of valid gates of `𝒢` and
primitive calls; the unsynthesised preparation has at most
`if TZeroCase p then |loadC| + 2 |wpC| else <released>` gates and the corresponding calls; the
synthesised preparation has at most `N len(ν/3/(N+1))` gates and exactly the calls of
`ctprepC`; every history makes at most `40 · 2g` times these calls and uses at most
`40 · 2g N_S + 20 · 2g (4 n + 3)` gates, and at most
`40 · 2g N (c₁ log((N+1)/(ν/3)) + c₀) + 20 · 2g (4 n + 3)` gates if `len ζ ≤ c₁ log(1/ζ) + c₀`; the
trial register has the released qubit count.  For every instance with unitary primitive oracles
and loading and weight-preparation circuits within `ζs`, the protocol has the guarantees
`NOutcome` against `x(T)`, under `3 ζs ≤ ν` and `TZInstanceOK` in the zero case and under the
released conditions otherwise. -/
theorem native_ode_time_solver_nonneg_trials (hS : Synthesis 𝒢 X len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) (p : TParams) (hp : TPublicOK0 p)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (p.nu / 3) (ctprepC p UJg nd ar loadC wpC)) j,
        i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (p.nu / 3) (ctprepC p UJg nd ar loadC wpC)) j →
        GateOf 𝒢 g) ∧
    nGatesN (ctprepC p UJg nd ar loadC wpC) ≤
      (if TZeroCase p then nGatesN loadC + 2 * nGatesN wpC
      else p.prepGates + 84 * p.d * UJg.length + 6 * p.d * privGates nd ar + nGatesN loadC +
        2 * nGatesN wpC) ∧
    (∀ q : J → Bool, nCallsN q (ctprepC p UJg nd ar loadC wpC) ≤
      (if TZeroCase p then nCallsN q loadC + 2 * nCallsN q wpC
      else 12 * p.d * nCallsN q nd.V + nCallsN q loadC + 2 * nCallsN q wpC)) ∧
    nGatesN (synthPrep hS (p.nu / 3) (ctprepC p UJg nd ar loadC wpC)) ≤
      nGatesN (ctprepC p UJg nd ar loadC wpC) *
        len (p.nu / 3 / (nGatesN (ctprepC p UJg nd ar loadC wpC) + 1)) ∧
    (∀ q : J → Bool, nCallsN q (synthPrep hS (p.nu / 3) (ctprepC p UJg nd ar loadC wpC)) =
      nCallsN q (ctprepC p UJg nd ar loadC wpC)) ∧
    (∀ q : J → Bool,
      ((nprotocol (synthPrep hS (p.nu / 3) (ctprepC p UJg nd ar loadC wpC)) p.ratio
        (p.ratio_ge hp.g_ge)).worstCost (wCallN q) : ℝ) ≤
        40 * p.ratio * nCallsN q (ctprepC p UJg nd ar loadC wpC)) ∧
    ((nprotocol (synthPrep hS (p.nu / 3) (ctprepC p UJg nd ar loadC wpC)) p.ratio
        (p.ratio_ge hp.g_ge)).worstCost wGateN : ℝ) ≤
      40 * p.ratio * nGatesN (synthPrep hS (p.nu / 3) (ctprepC p UJg nd ar loadC wpC)) +
        20 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card (SX Zs (tnPool p S Zs Z ar.bT ar.bP ar.A) X) + Fintype.card S) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (synthPrep hS (p.nu / 3) (ctprepC p UJg nd ar loadC wpC)) p.ratio
          (p.ratio_ge hp.g_ge)).worstCost wGateN : ℝ) ≤
        40 * p.ratio * (nGatesN (ctprepC p UJg nd ar loadC wpC) *
          (c₁ * Real.log ((nGatesN (ctprepC p UJg nd ar loadC wpC) + 1) / (p.nu / 3)) + c₀)) +
        20 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card (SX Zs (tnPool p S Zs Z ar.bT ar.bP ar.A) X) + Fintype.card S) + 3)) ∧
    Fintype.card (STW p S Zs Z ar.bT ar.bP ar.A X) =
      Fintype.card S + 2 * (Fintype.card p.W + (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) +
        (Fintype.card Zs + 1 + tnPool p S Zs Z ar.bT ar.bP ar.A + Fintype.card X)) +
        Fintype.card S + 1 ∧
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
      NOutcome (synthPrep hS (p.nu / 3) (ctprepC p UJg nd ar loadC wpC)) p.ratio p.ε
        (p.ratio_ge hp.g_ge) prim (x p.T) := by
  obtain ⟨hV, hG, hC, -, -, -, -⟩ :=
    native_ode_time_solver_nonneg p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV
  have hprepV : ∀ i ∈ ctprepC p UJg nd ar loadC wpC, i.Valid :=
    fun i hi => hV 0 i (List.mem_append_left _ hi)
  have hν : 0 < p.nu := p.nu_pos hp.g_ge hp.ε_pos
  have hν1 : p.nu ≤ 1 := p.nu_le_one hp.g_ge (hp.ε_half.trans (by norm_num))
  have hη : 0 < p.nu / 3 := by positivity
  have hη1 : p.nu / 3 ≤ 1 := by linarith
  obtain ⟨hSG, hSC⟩ := synthPrep_counts hS hη _ hprepV
  obtain ⟨hWC, hWG⟩ := synth_protocol_worst hS hη _ hprepV p.ratio (p.ratio_ge hp.g_ge)
  refine ⟨fun j => ⟨trialS_valid hS hη _ hprepV j, trialS_gateOf hS hadj hzt hη _ hprepV j⟩,
    hG, hC, hSG, hSC, hWC, hWG,
    fun c₀ c₁ hc₀ hc₁ hlen =>
      synth_protocol_worst_log hS hη hη1 _ hprepV p.ratio (p.ratio_ge hp.g_ge) hc₀ hc₁ hlen,
    card_SWO, ?_⟩
  intro prim D Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hζs hload hwp hcase
  by_cases hz : TZeroCase p
  · rw [if_pos hz] at hcase
    obtain ⟨-, -, -, -, -, -, -, hout⟩ := native_ode_time_solver_zero_trials (S := S)
      (Zs := Zs) (Z := Z) (Y := Y) (J := J) hS hadj hzt p p.a p.m p.r p.K p.l p.f ar.bT ar.bP
      ar.A hp.T_nonneg hp.g_ge hp.ε_pos hp.ε_half hp.lamH_nonneg hp.lamD_nonneg hz loadC hloadV
      wpC hwpV
    rw [ctprepC, if_pos hz]
    exact hout prim Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hζs hload hwp hcase.1
      hcase.2
  · rw [if_neg hz] at hcase
    obtain ⟨hN, hbud, hI⟩ := hcase
    obtain ⟨-, -, -, -, -, -, -, -, -, hout⟩ := native_ode_time_solver_trials hS hadj hzt p
      (tpublicOK_of hp hz) UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV
    rw [ctprepC, if_neg hz]
    exact hout prim D Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hN hζs hload hwp hbud hI

end Main

end

end SparseHamiltonian.ZeroTimeGateODE
