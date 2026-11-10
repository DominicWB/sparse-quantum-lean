import GateEfficientSynthesis.ODE

/-!
# Theorem `ode:thm:gates` over a finite gate set: the solvers

The finite-gate-set forms of Theorem `ode:thm:gates` in this module are a partial formalisation of
its finite-set statement, under this package's format hypotheses: the manuscript states Theorem
`ode:thm:gates` over a finite gate set; the conformance endpoints count native gates.

The native gate-efficient dissipative ODE solvers of `GateEfficientNative` (`native_ode_solver`,
`native_ode_time_solver`) with every trial synthesised over a finite gate set under the
synthesis hypothesis `Synthesis 𝒢 X len`, with the synthesis budget `ε/200` per trial
(`sprotocol`). The synthesised protocol depends only on the public data; its trials consist of
valid gates of `𝒢` and the primitive calls of the native trials, and the synthesis ancillas `X`
are added to the native register. With `len ζ ≤ c₁ log(1/ζ) + c₀` the worst-case gate count is
at most the native gate bound times `c₁ log((G + 1)/(ε/200)) + c₀`, where `G` is the native gate
bound of one trial; the worst-case number of primitive calls is at most the native bound. On
every instance satisfying the native hypotheses the synthesised protocol succeeds with
probability at least `2/3` and its conditional output is within trace distance `ε` of the
normalised solution.

* `native_ode_solver_synth`: constant coefficients.
* `native_ode_time_solver_synth`: time-dependent coefficients.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSynth

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative
open GateODE (Params Label Oracles)
open GateODE.Time (TParams TOracles)
open scoped InnerProduct BigOperators

section Solvers

variable {S Zs Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Gate-efficient dissipative ODE solver over a finite gate set, constant coefficients**
(partial formalisation, under this package's format hypotheses, of the finite-set statement of
Theorem `ode:thm:gates`, constant coefficients, with finite-set synthesis as a
hypothesis).

The synthesised protocol `sprotocol hS (ε/200) (nprepC p UJg nd ar srcC) g` depends only on the
public data. Its trials consist of valid gates of `𝒢` and primitive calls; one native
preparation uses at most `prepGates + 84 d C_J + 6 d G_C + |srcC 0| + |srcC 1|` elementary gates
and at most `12 d · calls(V) + calls(srcC 0) + calls(srcC 1)` primitive calls of every kind; in
every history the protocol uses at most `40 g` times these primitive calls and, if
`len ζ ≤ c₁ log(1/ζ) + c₀`, at most `(40 g N + 20 g (4 n + 3)) (c₁ log((G + 1)/(ε/200)) + c₀)`
elementary gates (`N` the native preparation gates, `n` the wires tested by the seed reflection,
`|W| + |XW| + |Zs| + |S|`, and `G = 10 g N + 5 g (4 n + 3)`). Its register
has the native wires and the `|X|` synthesis ancillas. For every instance satisfying the
hypotheses of `native_ode_solver` it succeeds with probability at least `2/3`, and its
conditional output is within trace distance `ε` of the normalised solution. -/
theorem native_ode_solver_synth (hS : Synthesis 𝒢 X len) (p : Params) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (LabW p.k p.l) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (LabW p.k p.l) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (srcC : Bool → List (NInstr ((Unit ⊕ S) ⊕ Zs) Y J)) (hsrcV : ∀ b, ∀ i ∈ srcC b, i.Valid) :
    (∀ j, (∀ i ∈ synthBudget hS (p.ε / 200) (trialN (nprepC p UJg nd ar srcC) j), i.Valid) ∧
      ∀ g, NInstr.gate g ∈ synthBudget hS (p.ε / 200) (trialN (nprepC p UJg nd ar srcC) j) →
        GateOf 𝒢 g) ∧
    nGatesN (nprepC p UJg nd ar srcC) ≤ p.prepGates + 84 * p.d * UJg.length +
      6 * p.d * privGates nd ar + nGatesN (srcC false) + nGatesN (srcC true) ∧
    (∀ q : J → Bool, nCallsN q (nprepC p UJg nd ar srcC) ≤
      12 * p.d * nCallsN q nd.V + nCallsN q (srcC false) + nCallsN q (srcC true)) ∧
    (∀ q : J → Bool,
      ((sprotocol hS (p.ε / 200) (nprepC p UJg nd ar srcC) p.g hp.g_ge).worstCost
        (wCallN q) : ℝ) ≤ 40 * p.g * nCallsN q (nprepC p UJg nd ar srcC)) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((sprotocol hS (p.ε / 200) (nprepC p UJg nd ar srcC) p.g hp.g_ge).worstCost
        wGateN : ℝ) ≤
        (40 * p.g * nGatesN (nprepC p UJg nd ar srcC) +
          20 * p.g * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
            Fintype.card Zs + Fintype.card S) + 3)) *
        (c₁ * Real.log ((10 * p.g * nGatesN (nprepC p UJg nd ar srcC) +
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
      NativeOK prim nd (selOp (labFam D false)) →
      0 ≤ ζs →
      (∀ c, ApproxOn CleanX (nrun prim (srcC c)) (liftB (srcIdeal c (Jsrc c))) ζs) →
      24 * (p.d : ℝ) * ζ + 2 * ζs ≤ p.nu →
      p.InstanceOK (seedV (S := S))
        (⟨UJop (R := ℂ) UJg, D, Jsrc⟩ : Oracles p.a (Label p.k p.l) (Reg S ℂ)) H L x0 b →
      SOutcome (sprotocol hS (p.ε / 200) (nprepC p UJg nd ar srcC) p.g hp.g_ge) p.ε prim
        (p.target H L x0 b) := by
  obtain ⟨hV, hG, hC, -, -, hcard, hout⟩ :=
    native_ode_solver p hp UJg hUJg nd hnd ar ζ hζ har srcC hsrcV
  have hε := hp.ε_pos
  have hεh := hp.ε_half
  have hη : 0 < p.ε / 200 := by positivity
  refine ⟨fun j => sprotocol_valid hS hη _ hV j, hG, hC,
    fun q => (sprotocol_worst hS hη _ hV p.g hp.g_ge q).2,
    fun c₀ c₁ hc₀ hc₁ hlen =>
      sprotocol_worst_log hS hη (by linarith) _ hV p.g hp.g_ge hc₀ hc₁ hlen,
    by rw [Fintype.card_sum, hcard], ?_⟩
  intro prim D Jsrc H L x0 b ζs hprim hN hζs hsrc hbudget hI
  exact soutcome hS hη (by linarith) (by linarith) _ hV p.g hp.g_ge prim hprim _ hI.target_ne
    (hout prim D Jsrc H L x0 b ζs hprim hN hζs hsrc hbudget hI)

/-- **Gate-efficient dissipative ODE solver over a finite gate set, time-dependent
coefficients** (partial formalisation, under this package's format hypotheses, of the finite-set
statement of Theorem `ode:thm:gates`, time-dependent part, with finite-set
synthesis as a hypothesis).

The synthesised protocol `sprotocol hS (ε/200) (tnprepC p UJg nd ar loadC wpC) (2g)` depends
only on the public data. Its trials consist of valid gates of `𝒢` and primitive calls;
one native preparation uses at most `prepGates + 84 d C_J + 6 d G_C + |loadC| + 2 |wpC|`
elementary gates and at most `12 d · calls(V) + calls(loadC) + 2 calls(wpC)` primitive calls of
every kind; in every history the protocol uses at most `80 g` times these primitive calls and,
if `len ζ ≤ c₁ log(1/ζ) + c₀`, at most
`(80 g N + 40 g (4 n + 3)) (c₁ log((G + 1)/(ε/200)) + c₀)` elementary gates (`N` the native
preparation gates, `n = |W| + |XW| + |Zs| + |S|` the wires tested by the seed reflection, and
`G = 20 g N + 10 g (4 n + 3)`). Its register has the native wires and the
`|X|` synthesis ancillas. For every instance satisfying the hypotheses of
`native_ode_time_solver` it succeeds with probability at least `2/3`, and its conditional output
is within trace distance `ε` of `x(T)/‖x(T)‖`. -/
theorem native_ode_time_solver_synth (hS : Synthesis 𝒢 X len) (p : TParams) (hp : p.PublicOK)
    (UJg : List (Gate (Fin p.a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (TSel p.m p.l p.m) (Fin p.a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (loadC : List (NInstr ((Fin (p.m + 1) ⊕ S) ⊕ Zs) Y J)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (p.m + 1) ⊕ Zs) Y J)) (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ synthBudget hS (p.ε / 200) (trialN (tnprepC p UJg nd ar loadC wpC) j),
        i.Valid) ∧
      ∀ g, NInstr.gate g ∈ synthBudget hS (p.ε / 200) (trialN (tnprepC p UJg nd ar loadC wpC) j) →
        GateOf 𝒢 g) ∧
    nGatesN (tnprepC p UJg nd ar loadC wpC) ≤ p.prepGates + 84 * p.d * UJg.length +
      6 * p.d * privGates nd ar + nGatesN loadC + 2 * nGatesN wpC ∧
    (∀ q : J → Bool, nCallsN q (tnprepC p UJg nd ar loadC wpC) ≤
      12 * p.d * nCallsN q nd.V + nCallsN q loadC + 2 * nCallsN q wpC) ∧
    (∀ q : J → Bool,
      ((sprotocol hS (p.ε / 200) (tnprepC p UJg nd ar loadC wpC) p.ratio
        (p.ratio_ge hp.g_ge)).worstCost (wCallN q) : ℝ) ≤
        40 * p.ratio * nCallsN q (tnprepC p UJg nd ar loadC wpC)) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((sprotocol hS (p.ε / 200) (tnprepC p UJg nd ar loadC wpC) p.ratio
        (p.ratio_ge hp.g_ge)).worstCost wGateN : ℝ) ≤
        (40 * p.ratio * nGatesN (tnprepC p UJg nd ar loadC wpC) +
          20 * p.ratio * (4 * (Fintype.card p.W + Fintype.card (XW Z ar.bT ar.bP ar.A) +
            Fintype.card Zs + Fintype.card S) + 3)) *
        (c₁ * Real.log ((10 * p.ratio * nGatesN (tnprepC p UJg nd ar loadC wpC) +
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
      NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) D false)) →
      0 ≤ ζs →
      ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs →
      24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu →
      p.InstanceOK (seedV (S := S))
        (⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ : TOracles p.a p.m p.l (Reg S ℂ))
        Hs Ls G b x bs βG δG βb δb bmax →
      SOutcome (sprotocol hS (p.ε / 200) (tnprepC p UJg nd ar loadC wpC) p.ratio
        (p.ratio_ge hp.g_ge)) p.ε prim (x p.T) := by
  obtain ⟨hV, hG, hC, -, -, hcard, hout⟩ :=
    native_ode_time_solver p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV
  have hε := hp.ε_pos
  have hεh := hp.ε_half
  have hη : 0 < p.ε / 200 := by positivity
  refine ⟨fun j => sprotocol_valid hS hη _ hV j, hG, hC,
    fun q => (sprotocol_worst hS hη _ hV p.ratio (p.ratio_ge hp.g_ge) q).2,
    fun c₀ c₁ hc₀ hc₁ hlen =>
      sprotocol_worst_log hS hη (by linarith) _ hV p.ratio (p.ratio_ge hp.g_ge) hc₀ hc₁ hlen,
    by rw [Fintype.card_sum, hcard], ?_⟩
  intro prim D Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hN hζs hload hwp hbudget hI
  exact soutcome hS hη (by linarith) (by linarith) _ hV p.ratio (p.ratio_ge hp.g_ge) prim hprim _
    hI.target_ne
    (hout prim D Jl Wp Hs Ls G b x bs βG δG βb δb bmax ζs hprim hN hζs hload hwp hbudget hI)

end Solvers

end

end SparseHamiltonian.GateSynth
