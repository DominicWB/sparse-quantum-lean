import GateEfficientSynthesisTrials.Protocol
import GateEfficientNative.ODE.Time

/-!
# Theorem `ode:thm:gates` over a finite gate set, trial by trial: the native solvers

The native gate-efficient dissipative ODE solvers of `GateEfficientNative`
(`native_ode_solver`, `native_ode_time_solver`) with the preparation synthesised over a finite
gate set under the synthesis hypothesis `Synthesis 𝒢 X len`, with the synthesis budget `ν/3`
(`ν` the precision unit of the released parameters), and the zero tests, the sign and the
inverse preparation kept exact: the synthesised protocol is the released native protocol
`nprotocol (synthPrep hS (ν/3) prepN) g` on the trial register (`SNW`, `STW`), whose trials
are Grover iterations on the actual synthesised preparation and its actual inverse. Besides the
synthesis hypothesis the gate set is adjoint-closed (`AdjClosed 𝒢`, for the actual inverse) and
contains the kinds of the exact zero tests (`zeroTestKinds ⊆ 𝒢`).

* `native_ode_solver_trials`: constant coefficients.
* `native_ode_time_solver_trials`: time-dependent coefficients.

Every trial consists of valid gates of `𝒢` and primitive calls; one native preparation has the
native counts, and the synthesised preparation at most `N len(ν/3/(N+1))` gates and exactly the
native calls; in every history the protocol makes at most `40 g` times (respectively `80 g`
times) the native primitive calls, and uses at most `40 g N_S + 20 g (4 n + 3)` gates (with `2g`
in place of `g` in the time-dependent case), `N_S` the gates of the synthesised preparation and
`n` the tested wires; with a logarithmic synthesis length this is
`40 g N (c₁ log((N+1)/(ν/3)) + c₀) + 20 g (4 n + 3)`. On every instance satisfying the
hypotheses of the native solver, unchanged, the protocol has the guarantees
`GateNative.NOutcome`, in particular every successful trial is within `ε/500` of the
normalised solution up to a global phase (the last claim of Theorem `ode:thm:gates`), the
success probability is at least `2/3` and the conditional output is within trace distance `ε`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSynthTrials

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth
open GateODE (OInstr Params Label Oracles goodF)
open GateODE.Time (TParams TOracles teval trun)
open ODEStateNormalization (unitDirection)
open scoped InnerProduct BigOperators

/-- The trial register of the constant-coefficient solver. -/
abbrev SNW (p : Params) (S Zs Z : Type*) [Fintype S] [Fintype Zs] [Fintype Z] (bT bP A : ℕ)
    (X : Type*) [Fintype X] :=
  SWO p.a p.m p.r p.K p.k p.l p.f S Zs (nPool p S Zs Z bT bP A) Z bT bP A X

/-- The trial register of the time-dependent solver. -/
abbrev STW (p : TParams) (S Zs Z : Type*) [Fintype S] [Fintype Zs] [Fintype Z] (bT bP A : ℕ)
    (X : Type*) [Fintype X] :=
  SWO p.a p.m p.r p.K p.m p.l p.f S Zs (tnPool p S Zs Z bT bP A) Z bT bP A X

section Solvers

variable {S Zs Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Gate-efficient dissipative ODE solver over a finite gate set with exact reflections,
constant coefficients** (Theorem `ode:thm:gates`, constant coefficients, with finite-set
synthesis as a hypothesis, including the per-trial claim).

The synthesised protocol `nprotocol (synthPrep hS (ν/3) (nprepC p UJg nd ar srcC)) g` depends
only on the public data. Under `Synthesis 𝒢 X len`, `AdjClosed 𝒢` and `zeroTestKinds ⊆ 𝒢`,
every trial consists of valid gates of `𝒢` and primitive calls. One native preparation uses at
most `prepGates + 84 d C_J + 6 d G_C + |srcC 0| + |srcC 1|` gates and
`12 d · calls(V) + calls(srcC 0) + calls(srcC 1)` primitive calls of every kind; the synthesised
preparation has at most `N len(ν/3/(N+1))` gates (`N` the native gates) and exactly the native
calls. In every history the protocol makes at most `40 g` times the native calls and uses at most
`40 g N_S + 20 g (4 n + 3)` gates, `N_S` the gates of the synthesised preparation and
`n = |W| + |XW| + |SX| + |S|` the tested wires, and, if `len ζ ≤ c₁ log(1/ζ) + c₀`, at most
`40 g N (c₁ log((N+1)/(ν/3)) + c₀) + 20 g (4 n + 3)` gates. The register `SNW` has
`|S| + 2 (|W| + (|Z| + bT + bP + A + 3) + (|Zs| + 1 + n_P + |X|)) + |S| + 1` qubits, `n_P` the
native pool. For every instance satisfying the hypotheses of `native_ode_solver` (unchanged)
the protocol has the guarantees `NOutcome`: every successful trial is within `ε/500` of the
normalised solution up to a global phase, the success probability is at least `175/256 ≥ 2/3`,
and the conditional output is within trace distance `ε` of the normalised solution. -/
theorem native_ode_solver_trials (hS : Synthesis 𝒢 X len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) (p : Params) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (LabW p.k p.l) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (LabW p.k p.l) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (hsrcV : ∀ b, ∀ i ∈ srcC b, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) j, i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) j →
        GateOf 𝒢 g) ∧
    nGatesN (nprepC p UJg nd ar srcC) ≤ p.prepGates + 84 * p.d * UJg.length +
      6 * p.d * privGates nd ar + nGatesN (srcC false) + nGatesN (srcC true) ∧
    (∀ q : J → Bool, nCallsN q (nprepC p UJg nd ar srcC) ≤
      12 * p.d * nCallsN q nd.V + nCallsN q (srcC false) + nCallsN q (srcC true)) ∧
    nGatesN (synthPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) ≤
      nGatesN (nprepC p UJg nd ar srcC) *
        len (p.nu / 3 / (nGatesN (nprepC p UJg nd ar srcC) + 1)) ∧
    (∀ q : J → Bool, nCallsN q (synthPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) =
      nCallsN q (nprepC p UJg nd ar srcC)) ∧
    (∀ q : J → Bool,
      ((nprotocol (synthPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) p.g hp.g_ge).worstCost
        (wCallN q) : ℝ) ≤ 40 * p.g * nCallsN q (nprepC p UJg nd ar srcC)) ∧
    ((nprotocol (synthPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) p.g hp.g_ge).worstCost
        wGateN : ℝ) ≤
      40 * p.g * nGatesN (synthPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) +
        20 * p.g * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card (SX Zs (nPool p S Zs Z ar.bT ar.bP ar.A) X) + Fintype.card S) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (synthPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) p.g hp.g_ge).worstCost
          wGateN : ℝ) ≤
        40 * p.g * (nGatesN (nprepC p UJg nd ar srcC) *
          (c₁ * Real.log ((nGatesN (nprepC p UJg nd ar srcC) + 1) / (p.nu / 3)) + c₀)) +
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
      NativeOK prim nd (selOp (labFam D false)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun prim (srcC c)) (liftB (srcIdeal c (Jsrc c))) ζs) →
      24 * (p.d : ℝ) * ζ + 2 * ζs ≤ p.nu →
      p.InstanceOK (seedV (S := S))
        (⟨UJop (R := ℂ) UJg, D, Jsrc⟩ : Oracles p.a (Label p.k p.l) (Reg S ℂ)) H L x0 b →
      NOutcome (synthPrep hS (p.nu / 3) (nprepC p UJg nd ar srcC)) p.g p.ε hp.g_ge prim
        (p.target H L x0 b) := by
  obtain ⟨hV, hG, hC, -, -, -, -⟩ :=
    native_ode_solver p hp UJg hUJg nd hnd ar ζ hζ har srcC hsrcV
  have hprepV : ∀ i ∈ nprepC p UJg nd ar srcC, i.Valid :=
    fun i hi => hV 0 i (List.mem_append_left _ hi)
  have hν := hp.nu_pos
  have hν1 : p.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth p.g p.ε hp.g_ge hp.eps_le_one
  have hη : 0 < p.nu / 3 := by positivity
  have hη1 : p.nu / 3 ≤ 1 := by linarith
  obtain ⟨hSG, hSC⟩ := synthPrep_counts hS hη _ hprepV
  obtain ⟨hWC, hWG⟩ := synth_protocol_worst hS hη _ hprepV p.g hp.g_ge
  refine ⟨fun j => ⟨trialS_valid hS hη _ hprepV j, trialS_gateOf hS hadj hzt hη _ hprepV j⟩,
    hG, hC, hSG, hSC, hWC, hWG,
    fun c₀ c₁ hc₀ hc₁ hlen =>
      synth_protocol_worst_log hS hη hη1 _ hprepV p.g hp.g_ge hc₀ hc₁ hlen, card_SWO, ?_⟩
  intro prim D Jsrc H L x0 b ζs hprim hN hζs hsrc hbudget hI
  have hτ := hp.tau_pos.le
  obtain ⟨cP, -, cS, -, -⟩ := p.prepC_counts hτ hν
  have hvalid := p.prepC_valid hτ hν hp.r₀_nonneg hp.rb_nonneg hp.T_pos.le hp.B_pos
  let σ : Oracles p.a (Label p.k p.l) (Reg S ℂ) := ⟨UJop (R := ℂ) UJg, D, Jsrc⟩
  have hU := p.unitaries_of (norm_seedV (S := S)) hI
  have hJ : ∀ c, IsUnitary (Jsrc c) := hU.src
  have hDu : ∀ w, IsUnitary (labFam D false w) := fun w => hU.priv _
  have hDadj : ∀ w, labFam D true w = (labFam D false w)† := fun _ => rfl
  have hA := oprep_approx prim hprim labSel UJg hUJg nd hnd ar hζ har (labFam D) hDu hDadj hN
    (OInstr.eval (GateODE.wiring (seedV (S := S))) σ) (fun _ => rfl)
    (fun adj => ode_eval_uj (seedV (S := S)) σ UJg rfl labSel (labFam D) adj)
    (fun adj => ode_eval_priv (seedV (S := S)) σ UJg adj)
    (srcMacro p srcC) hζs
    (fun c adj => srcMacro_approx p prim hprim srcC hsrcV Jsrc hJ hζs hsrc (seedV (S := S)) D
      (UJop (R := ℂ) UJg) c adj)
    (srcMacro_valid p srcC hsrcV) p.prepC (osec_prepC p) (noseed_prepC p hτ hν) hvalid
    (fun i hi => OInstr.eval_isUnitary (GateODE.wiring (seedV (S := S))) σ hU.uj hU.priv hU.src
      hU.seed i (hvalid i hi))
  rw [prodOps_oeval, nSrcAny_eq, cP, cS false, cS true] at hA
  -- the released certificate
  have hT := hp.T_pos.le
  have hSel := hI.select
  have hCert := p.prep_certificate hp (seedV (S := S)) norm_seedV σ H L x0 b hI
  have hdec := p.decoded_eq hp (seedV (S := S)) σ x0 b hI.init_norm hI.forcing_norm
  have hmass := p.mass_zsrc x0 b hT hI.init_norm hI.forcing_norm
  have hNorm : ‖p.target H L x0 b‖ ≤ p.B := by
    rw [← hmass]
    exact p.solution_le_mass hT H L hSel.selfH hSel.selfL hI.psd x0 b hI.init_norm
      hI.forcing_norm
  have h := hCert.vector_error
  rw [hmass, ← hdec] at h
  have hδ0 : 0 ≤ ((6 * p.d : ℕ) : ℝ) * (4 * ζ) + ((1 + 1 : ℕ) : ℝ) * ζs :=
    add_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (mul_nonneg (Nat.cast_nonneg _) hζs)
  have hηδ : p.nu / 3 + (((6 * p.d : ℕ) : ℝ) * (4 * ζ) + ((1 + 1 : ℕ) : ℝ) * ζs) ≤
      4 / 3 * ImprovedODEQueryBudget.precision p.g p.ε := by
    have e : p.nu = ImprovedODEQueryBudget.precision p.g p.ε := rfl
    have e2 : ((6 * p.d : ℕ) : ℝ) = 6 * (p.d : ℝ) := by rw [Nat.cast_mul, Nat.cast_ofNat]
    have e3 : ((1 + 1 : ℕ) : ℝ) = 2 := by norm_num
    rw [e2, e3]
    linarith only [hbudget, e]
  have hne := hI.target_ne
  have hbud := hI.budget
  generalize GateODE.run (GateODE.wiring (seedV (S := S))) σ p.prepC = Urel at h hA
  generalize p.target H L x0 b = x at h hNorm hne hbud ⊢
  exact synth_noutcome prim hS hη (nprepC p UJg nd ar srcC) hprepV hprim Urel hδ0 hA x p.B p.g
    p.ε hne hp.g_ge hp.ε_pos hp.ε_half hNorm hbud h hηδ

/-- **Gate-efficient dissipative ODE solver over a finite gate set with exact reflections,
time-dependent coefficients** (Theorem `ode:thm:gates`, time-dependent part, with finite-set
synthesis as a hypothesis, including the per-trial claim).

The synthesised protocol `nprotocol (synthPrep hS (ν/3) (tnprepC p UJg nd ar loadC wpC)) (2g)`
depends only on the public data. Under `Synthesis 𝒢 X len`, `AdjClosed 𝒢` and
`zeroTestKinds ⊆ 𝒢`, every trial consists of valid gates of `𝒢` and primitive calls. One native
preparation uses at most `prepGates + 84 d C_J + 6 d G_C + |loadC| + 2 |wpC|` gates and
`12 d · calls(V) + calls(loadC) + 2 calls(wpC)` primitive calls of every kind; the synthesised
preparation has at most `N len(ν/3/(N+1))` gates and exactly the native calls. In every history
the protocol makes at most `80 g` times the native calls and uses at most
`80 g N_S + 40 g (4 n + 3)` gates (`N_S` the gates of the synthesised preparation,
`n = |W| + |XW| + |SX| + |S|`), and, if `len ζ ≤ c₁ log(1/ζ) + c₀`, at most
`80 g N (c₁ log((N+1)/(ν/3)) + c₀) + 40 g (4 n + 3)` gates. For every instance satisfying the
hypotheses of `native_ode_time_solver` (unchanged) the protocol has the guarantees `NOutcome`:
every successful trial is within `ε/500` of `x(T)/‖x(T)‖` up to a global phase, the success
probability is at least `175/256 ≥ 2/3`, and the conditional output is within trace distance
`ε` of `x(T)/‖x(T)‖`. -/
theorem native_ode_time_solver_trials (hS : Synthesis 𝒢 X len) (hadj : AdjClosed 𝒢)
    (hzt : zeroTestKinds ⊆ 𝒢) (p : TParams) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ trialN (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) j,
        i.Valid) ∧
      ∀ g, NInstr.gate g ∈ trialN (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) j →
        GateOf 𝒢 g) ∧
    nGatesN (tnprepC p UJg nd ar loadC wpC) ≤ p.prepGates + 84 * p.d * UJg.length +
      6 * p.d * privGates nd ar + nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ q : J → Bool, nCallsN q (tnprepC p UJg nd ar loadC wpC) ≤
      12 * p.d * nCallsN q nd.V + nCallsN q loadC + 2 * nCallsN q wpC) ∧
    nGatesN (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) ≤
      nGatesN (tnprepC p UJg nd ar loadC wpC) *
        len (p.nu / 3 / (nGatesN (tnprepC p UJg nd ar loadC wpC) + 1)) ∧
    (∀ q : J → Bool, nCallsN q (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) =
      nCallsN q (tnprepC p UJg nd ar loadC wpC)) ∧
    (∀ q : J → Bool,
      ((nprotocol (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio
        (p.ratio_ge hp.g_ge)).worstCost (wCallN q) : ℝ) ≤
        40 * p.ratio * nCallsN q (tnprepC p UJg nd ar loadC wpC)) ∧
    ((nprotocol (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio
        (p.ratio_ge hp.g_ge)).worstCost wGateN : ℝ) ≤
      40 * p.ratio * nGatesN (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) +
        20 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
          Fintype.card (SX Zs (tnPool p S Zs Z ar.bT ar.bP ar.A) X) + Fintype.card S) + 3) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((nprotocol (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio
          (p.ratio_ge hp.g_ge)).worstCost wGateN : ℝ) ≤
        40 * p.ratio * (nGatesN (tnprepC p UJg nd ar loadC wpC) *
          (c₁ * Real.log ((nGatesN (tnprepC p UJg nd ar loadC wpC) + 1) / (p.nu / 3)) + c₀)) +
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
      NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) D false)) →
      0 ≤ ζs →
      ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs →
      24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu →
      p.InstanceOK (seedV (S := S))
        (⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ : TOracles p.a p.m p.l (Reg S ℂ))
        Hs Ls G b x bs βG δG βb δb bmax →
      NOutcome (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) p.ratio p.ε
        (p.ratio_ge hp.g_ge) prim (x p.T) := by
  obtain ⟨-, hG, hC, -, -, -, -⟩ :=
    native_ode_time_solver p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV
  have hprepV := tnprepC_valid p hp UJg hUJg nd hnd ar har loadC hloadV wpC hwpV
  have hν := hp.nu_pos
  have hν1 : p.nu ≤ 1 / 10000 :=
    ImprovedODEQueryBudget.precision_le_one_ten_thousandth p.ratio p.acc
      (p.ratio_ge hp.g_ge) (by have := hp.ε_half; simp only [TParams.acc]; linarith)
  have hη : 0 < p.nu / 3 := by positivity
  have hη1 : p.nu / 3 ≤ 1 := by linarith
  obtain ⟨hSG, hSC⟩ := synthPrep_counts hS hη _ hprepV
  obtain ⟨hWC, hWG⟩ := synth_protocol_worst hS hη _ hprepV p.ratio (p.ratio_ge hp.g_ge)
  refine ⟨fun j => ⟨trialS_valid hS hη _ hprepV j, trialS_gateOf hS hadj hzt hη _ hprepV j⟩,
    hG, hC, hSG, hSC, hWC, hWG,
    fun c₀ c₁ hc₀ hc₁ hlen =>
      synth_protocol_worst_log hS hη hη1 _ hprepV p.ratio (p.ratio_ge hp.g_ge) hc₀ hc₁ hlen,
    card_SWO, ?_⟩
  intro prim D Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hN hζs hload hwp hbudget hI
  let σ : TOracles p.a p.m p.l (Reg S ℂ) := ⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩
  obtain ⟨cP, -, cSF, cST, -, -⟩ := p.prepC_counts hp.tau_pos.le hp.nu_pos hp.mesh
  have hvalid := p.prepC_valid hp.tau_pos.le hp.nu_pos hp.mesh
  have hU := p.unitary_of hI
  have hDu : ∀ w, IsUnitary (tlabFam (m := p.m) (P := Reg S ℂ) σ.D false w) := fun w =>
    hU.priv _ _ (GatePointerEncoding.wordEquivFin p.m (fun i => w (Sum.inr i))).isLt
  have hDadj : ∀ w, tlabFam (m := p.m) (P := Reg S ℂ) σ.D true w =
      (tlabFam (m := p.m) (P := Reg S ℂ) σ.D false w)† := fun _ => rfl
  have hA := oprep_approx prim hprim tlabSel UJg hUJg nd hnd ar hζ har
    (tlabFam (P := Reg S ℂ) σ.D) hDu hDadj hN (teval (seedV (S := S)) σ) (fun _ => rfl)
    (fun adj => tode_eval_uj (seedV (S := S)) σ UJg rfl tlabSel (tlabFam (P := Reg S ℂ) σ.D) adj)
    (fun adj => tode_eval_priv (seedV (S := S)) σ UJg adj)
    (tsrcMacro p loadC wpC) hζs
    (fun c adj => tsrcMacro_approx p prim hprim loadC hloadV wpC hwpV (seedV (S := S)) σ hU hζs
      hload hwp c adj)
    (tsrcMacro_valid p loadC hloadV wpC hwpV) p.prepC (osec_tprepC p) (noseed_tprepC p hp) hvalid
    (fun i hi => GateODE.Time.teval_isUnitary (seedV (S := S)) σ hU norm_seedV i (hvalid i hi))
  rw [prodOps_teval, nSrcAny_eq, cP, cSF, cST] at hA
  have hδ : ((6 * p.d : ℕ) : ℝ) * (4 * ζ) + ((1 + 2 : ℕ) : ℝ) * ζs ≤ p.nu := by
    have e2 : ((6 * p.d : ℕ) : ℝ) = 6 * (p.d : ℝ) := by rw [Nat.cast_mul, Nat.cast_ofNat]
    have e3 : ((1 + 2 : ℕ) : ℝ) = 3 := by norm_num
    rw [e2, e3]
    linarith only [hbudget]
  have hA' := hA.mono hδ
  -- the released certificate of the discretised target
  have hCert := p.prep_certificate hp (seedV (S := S)) norm_seedV σ Hs Ls G b x bs βG δG βb δb
    bmax hI
  obtain ⟨hy, hbud, hdirY⟩ := p.target_facts hp hI
  have hNorm := p.target_norm_le hp.T_pos.le Hs Ls hI.select.selfH hI.psd (x 0) bs
  have hB : 0 < p.mass (x 0) bs := (norm_pos_iff.mpr hy).trans_le hNorm
  have hdec := p.decoded_eq hp (seedV (S := S)) σ (x 0) bs hB hI.prep
  have h := hCert.vector_error
  have hm : p.mass (x 0) bs = ODESourceBranches.mass (p.zsrc (x 0) bs) := rfl
  rw [← hdec, ← hm] at h
  have hacc : p.acc ≤ 1 / 2 := by
    have := hp.ε_half
    simp only [TParams.acc]
    linarith
  have hUS : IsUnitary (nrun prim (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC))) :=
    nrun_isUnitary prim hprim _ (synthPrep_valid hS hη _ hprepV)
  have hne := hI.target_ne
  have hηδ : p.nu / 3 + p.nu ≤ 4 / 3 * ImprovedODEQueryBudget.precision p.ratio p.acc := by
    have e : p.nu = ImprovedODEQueryBudget.precision p.ratio p.acc := rfl
    linarith only [e]
  generalize trun (seedV (S := S)) σ p.prepC = Urel at h hA'
  generalize p.target Hs Ls (x 0) bs = y at h hy hbud hdirY hNorm
  have hbud' : p.mass (x 0) bs ≤ p.ratio * ‖y‖ := hbud
  have hdirY' : ‖unitDirection y - unitDirection (x p.T)‖ ≤ p.ε / 1000 := hdirY
  have hAT := synthPrep_approx hS hη (tnprepC p UJg nd ar loadC wpC) hprepV prim hprim Urel
    hν.le hA'
  obtain ⟨-, -, hmean, hdir⟩ := native_trial_bounds10 prim hnP_SWO
    (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) hUS
    (synthPrep_pres hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC) prim) Urel hAT y
    (p.mass (x 0) bs) p.ratio p.acc hy (p.ratio_ge hp.g_ge) (p.acc_pos hp.ε_pos) hacc hNorm hbud'
    h hηδ
  refine noutcome_of_bounds (synthPrep hS (p.nu / 3) (tnprepC p UJg nd ar loadC wpC)) prim hprim
    (synthPrep_valid hS hη _ hprepV) (x p.T) hne p.ratio p.ε (p.ratio_ge hp.g_ge) hp.ε_pos hmean ?_
  intro j hj
  obtain ⟨ω, hω, hd⟩ := hdir j hj
  refine ⟨ω, hω, ?_⟩
  refine (norm_sub_le_norm_sub_add_norm_sub _ (unitDirection y) _).trans ?_
  have e : p.acc / 500 + p.ε / 1000 = p.ε / 500 := by
    simp only [TParams.acc]
    ring
  linarith only [hd, hdirY', e]

end Solvers

end

end SparseHamiltonian.GateSynthTrials
