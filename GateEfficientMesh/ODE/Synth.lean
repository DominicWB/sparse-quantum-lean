import GateEfficientMesh.ODE.BinaryMesh
import GateEfficientBinaryODETime.Synth

/-!
# The ODE endpoints over a finite gate set

The finite-gate-set forms of Theorem `ode:thm:gates` in this module are a partial formalisation of
its finite-set statement, under this package's format hypotheses: the manuscript states Theorem
`ode:thm:gates` over a finite gate set; the conformance endpoints count native gates.

The released finite-set forms of Theorem `ode:thm:gates`, time-dependent part
(`GateSynth.native_ode_time_solver_synth`, `GateBinaryODETime.binary_ode_time_solver_synth`),
synthesise every trial of the native protocol with the synthesis budget `ε/200`
(`GateSynth.sprotocol`) under the synthesis hypothesis `Synthesis 𝒢 X len`; their guarantee
`SOutcome` (success at least `2/3`, conditional output within trace distance `ε`) follows from
the native guarantee `NOutcome` of the same instance by the released `GateSynth.soutcome`. With
the native guarantees of this library:

* `native_ode_time_solver_certified_synth`, `native_ode_time_solver_mesh_synth`: the released
  synthesised protocol and counts, under the integrated certificate on the uniform slots,
  respectively on a nonuniform mesh;
* `binary_ode_time_solver_certified_synth`, `binary_ode_time_solver_mesh_synth`: the same from
  binary sparse data (on a mesh, through the clock data `clockData`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateMesh.ODE

noncomputable section
open ContinuousLinearMap MeasureTheory Set OracleCircuit GateCircuit GateNative GateSynth
open SparseHamiltonian.GateBinary SparseHamiltonian.GateBinaryODE
open SparseHamiltonian.GateBinaryODETime
open NativeSparseBlockEncoding (Data Query)
open GateODE (Label)
open GateODE.Time (TParams TOracles)
open TimeDependentODE (SolvesODE Accretive)
open TimeDependentExtensions (IsMesh slotPiece)
open scoped InnerProduct BigOperators

section Native

variable {S Zs Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Native dissipative ODE solver under the integrated certificate on the uniform slots over a
finite gate set** (partial formalisation, under this package's format hypotheses, of the finite-set
statement of Theorem `ode:thm:gates`, time-dependent part, with
finite-set synthesis as a hypothesis). The synthesised protocol
`sprotocol hS (ε/200) (tnprepC p UJg nd ar loadC wpC) (2g)` has the released validity, gates of `𝒢`,
call, gate and qubit counts of `GateSynth.native_ode_time_solver_synth`; for every instance as in
`native_ode_time_solver_certified` it succeeds with probability at least `2/3`, and its
conditional output is within trace distance `ε` of `x(T)/‖x(T)‖` (`SOutcome`). -/
theorem native_ode_time_solver_certified_synth (hS : Synthesis 𝒢 X len) (p : TParams)
    (hp : p.PublicOK)
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
      (Hs Ls : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (G : ℕ → ℝ → Reg S ℂ →L[ℂ] Reg S ℂ)
      (b : ℕ → ℝ → Reg S ℂ) (x : ℝ → Reg S ℂ) (bs : ℕ → Reg S ℂ) (bmax ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) D false)) →
      0 ≤ ζs →
      ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs →
      24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu →
      CoreOK p (seedV (S := S))
        (⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ : TOracles p.a p.m p.l (Reg S ℂ)) Hs Ls (x 0) bs →
      (∀ k < p.M, SolvesODE (G k) (b k) x (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1))) →
      (∀ k < p.M, ∀ u ∈ Icc (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1)),
        Accretive (G k u)) →
      (∀ k < p.M, IntervalIntegrable (G k) volume (slotMesh p.T p.m k)
        (slotMesh p.T p.m (k + 1))) →
      (∀ k < p.M, IntervalIntegrable (b k) volume (slotMesh p.T p.m k)
        (slotMesh p.T p.m (k + 1))) →
      0 ≤ bmax →
      (∀ k < p.M, ∀ u ∈ Icc (slotMesh p.T p.m k) (slotMesh p.T p.m (k + 1)), ‖b k u‖ ≤ bmax) →
      x p.T ≠ 0 → p.mass (x 0) bs ≤ p.g * ‖x p.T‖ →
      slotCertificate p Hs Ls bs G b ‖x 0‖ bmax ≤ p.ε * p.mass (x 0) bs / (2000 * p.g) →
      SOutcome (sprotocol hS (p.ε / 200) (tnprepC p UJg nd ar loadC wpC) p.ratio
        (p.ratio_ge hp.g_ge)) p.ε prim (x p.T) := by
  obtain ⟨hV, hG, hC, hWC, hWG, hcard, -⟩ :=
    native_ode_time_solver_synth hS p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV
  obtain ⟨hVN, -, -, -, -, -, hout⟩ :=
    native_ode_time_solver_certified p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV
  refine ⟨hV, hG, hC, hWC, hWG, hcard, ?_⟩
  intro prim D Jl Wp Hs Ls G b x bs bmax ζs hprim hN hζs hload hwp hbudget hCore hx hGa hGint
    hbint hbmax hb hne hbud hcert
  have hε := hp.ε_pos
  have hεh := hp.ε_half
  have hη : 0 < p.ε / 200 := by positivity
  exact soutcome hS hη (by linarith) (by linarith) _ hVN p.ratio (p.ratio_ge hp.g_ge) prim hprim _
    hne (hout prim D Jl Wp Hs Ls G b x bs bmax ζs hprim hN hζs hload hwp hbudget hCore hx hGa
      hGint hbint hbmax hb hne hbud hcert)

/-- **Native dissipative ODE solver on a nonuniform mesh over a finite gate set** (partial
formalisation, under this package's format hypotheses, of the finite-set statement of Theorem
`ode:thm:gates`, time-dependent part, extended by uniform refinement to nonuniform meshes
with breakpoints, with finite-set synthesis as a hypothesis). The synthesised protocol has the
counts of `native_ode_time_solver_certified_synth`; for every mesh and instance as in
`native_ode_time_solver_mesh` it has the guarantees `SOutcome`. -/
theorem native_ode_time_solver_mesh_synth (hS : Synthesis 𝒢 X len) (p : TParams)
    (hp : p.PublicOK)
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
    ∀ (tm : ℕ → ℝ) (Mm : ℕ), 0 < Mm → IsMesh tm Mm p.T →
    ∀ (prim : J → Reg Y ℂ →L[ℂ] Reg Y ℂ)
      (D : Label p.m p.l → ℕ → Anc p.a (Reg S ℂ) →L[ℂ] Anc p.a (Reg S ℂ))
      (Jl : Bool × (Fin p.m → Bool) → Reg S ℂ →L[ℂ] Reg S ℂ)
      (Wp : Matrix (Cfg (Fin (p.m + 1))) (Cfg (Fin (p.m + 1))) ℂ)
      (Hm Lm : ℕ → Reg S ℂ →L[ℂ] Reg S ℂ) (bm : ℕ → Reg S ℂ)
      (G : ℕ → ℝ → Reg S ℂ →L[ℂ] Reg S ℂ) (b : ℕ → ℝ → Reg S ℂ) (x : ℝ → Reg S ℂ)
      (bmax ζs : ℝ),
      (∀ j, IsUnitary (prim j)) →
      NativeOK prim nd (selOp (tlabFam (P := Reg S ℂ) D false)) →
      0 ≤ ζs →
      ApproxOn CleanX (nrun prim loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun prim wpC) (liftB (matOp Wp)) ζs →
      24 * (p.d : ℝ) * ζ + 3 * ζs ≤ p.nu →
      CoreOK p (seedV (S := S))
        (⟨UJop (R := ℂ) UJg, D, Jl, Wp⟩ : TOracles p.a p.m p.l (Reg S ℂ))
        (fun k => Hm (slotPiece tm p.T p.M Mm k)) (fun k => Lm (slotPiece tm p.T p.M Mm k))
        (x 0) (fun k => bm (slotPiece tm p.T p.M Mm k)) →
      (∀ q < Mm, star (Hm q) = Hm q) →
      (∀ q < Mm, ∀ w : Reg S ℂ, 0 ≤ (inner ℂ w (Lm q w)).re) →
      (∀ q < Mm, ‖Hm q‖ ≤ p.lamH) → (∀ q < Mm, ‖Lm q‖ ≤ p.lamD) →
      (∀ q < Mm, SolvesODE (G q) (b q) x (tm q) (tm (q + 1))) →
      (∀ q < Mm, ∀ u ∈ Icc (tm q) (tm (q + 1)), Accretive (G q u)) →
      (∀ q < Mm, IntervalIntegrable (G q) volume (tm q) (tm (q + 1))) →
      (∀ q < Mm, IntervalIntegrable (b q) volume (tm q) (tm (q + 1))) →
      0 ≤ bmax →
      (∀ q < Mm, ∀ u ∈ Icc (tm q) (tm (q + 1)), ‖b q u‖ ≤ bmax) →
      x p.T ≠ 0 →
      p.mass (x 0) (fun k => bm (slotPiece tm p.T p.M Mm k)) ≤ p.g * ‖x p.T‖ →
      meshCertificate p tm Mm Hm Lm bm G b ‖x 0‖ bmax ≤
        p.ε * p.mass (x 0) (fun k => bm (slotPiece tm p.T p.M Mm k)) / (2000 * p.g) →
      SOutcome (sprotocol hS (p.ε / 200) (tnprepC p UJg nd ar loadC wpC) p.ratio
        (p.ratio_ge hp.g_ge)) p.ε prim (x p.T) := by
  obtain ⟨hV, hG, hC, hWC, hWG, hcard, -⟩ :=
    native_ode_time_solver_synth hS p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV
  obtain ⟨hVN, -, -, -, -, -, hout⟩ :=
    native_ode_time_solver_mesh p hp UJg hUJg nd hnd ar ζ hζ har loadC hloadV wpC hwpV
  refine ⟨hV, hG, hC, hWC, hWG, hcard, ?_⟩
  intro tm Mm hMm hmesh prim D Jl Wp Hm Lm bm G b x bmax ζs hprim hN hζs hload hwp hbudget hCore
    hH hPSD hHn hLn hx hGa hGint hbint hbmax hb hne hbud hcert
  have hε := hp.ε_pos
  have hεh := hp.ε_half
  have hη : 0 < p.ε / 200 := by positivity
  exact soutcome hS hη (by linarith) (by linarith) _ hVN p.ratio (p.ratio_ge hp.g_ge) prim hprim _
    hne (hout tm Mm hMm hmesh prim D Jl Wp Hm Lm bm G b x bmax ζs hprim hN hζs hload hwp hbudget
      hCore hH hPSD hHn hLn hx hGa hGint hbint hbmax hb hne hbud hcert)

end Native

section Binary

variable {X n : Type*} [Fintype n] [DecidableEq n] {Zs : Type*} [Fintype Zs] [DecidableEq Zs]
variable {Xa : Type*} [Fintype Xa] [DecidableEq Xa] {𝒢 : Set Kind} {len : ℝ → ℕ}

/-- **Dissipative ODE solver from time-indexed binary sparse data under the integrated
certificate on the uniform slots over a finite gate set** (partial formalisation, under this
package's format hypotheses, of the finite-set statement of Theorem `ode:thm:gates`, time-dependent
part, with finite-set synthesis as a hypothesis). The synthesised
protocol `sprotocol hS (ε/200) (q.prep loadC wpC) (2g)` has the released counts of
`GateBinaryODETime.binary_ode_time_solver_synth`; for every input and instance as in
`binary_ode_time_solver_certified` it has the guarantees `SOutcome`. -/
theorem binary_ode_time_solver_certified_synth (hS : Synthesis 𝒢 Xa len) (q : PubT)
    (hq : q.OK) (D : Data (X × Fin (2 ^ q.m)) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ synthBudget hS (q.ε / 200) (trialN (q.prep loadC wpC) j), i.Valid) ∧
      ∀ g, NInstr.gate g ∈ synthBudget hS (q.ε / 200) (trialN (q.prep loadC wpC) j) →
        GateOf 𝒢 g) ∧
    (∀ c : Query → Bool,
      ((sprotocol hS (q.ε / 200) (q.prep loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
        40 * q.params.ratio * nCallsN c (q.prep loadC wpC)) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((sprotocol hS (q.ε / 200) (q.prep loadC wpC) q.params.ratio
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
        (G : ℕ → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf : ℕ → ℝ → Reg (Fin q.kx) ℂ)
        (xs : ℝ → Reg (Fin q.kx) ℂ) (bs : ℕ → Reg (Fin q.kx) ℂ) (bmax ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) loadC) (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) D en x) wpC) (liftB (matOp Wp)) ζs →
      24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu →
      SourceOK q.params (seedV (S := Fin q.kx)) Jl Wp (xs 0) bs →
      (∀ k < q.params.M, SolvesODE (G k) (bf k) xs (slotMesh q.T q.m k)
        (slotMesh q.T q.m (k + 1))) →
      (∀ k < q.params.M, ∀ u ∈ Icc (slotMesh q.T q.m k) (slotMesh q.T q.m (k + 1)),
        Accretive (G k u)) →
      (∀ k < q.params.M, IntervalIntegrable (G k) volume (slotMesh q.T q.m k)
        (slotMesh q.T q.m (k + 1))) →
      (∀ k < q.params.M, IntervalIntegrable (bf k) volume (slotMesh q.T q.m k)
        (slotMesh q.T q.m (k + 1))) →
      0 ≤ bmax →
      (∀ k < q.params.M, ∀ u ∈ Icc (slotMesh q.T q.m k) (slotMesh q.T q.m (k + 1)),
        ‖bf k u‖ ≤ bmax) →
      xs q.T ≠ 0 → q.params.mass (xs 0) bs ≤ q.g * ‖xs q.T‖ →
      slotCertificate q.params (GateBinaryODETime.HsT D en x) (GateBinaryODETime.LsT D en x) bs G
        bf ‖xs 0‖ bmax ≤
        q.ε * q.params.mass (xs 0) bs / (2000 * q.g) →
      SOutcome (sprotocol hS (q.ε / 200) (q.prep loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)) q.ε (primsT (R := ℂ) D en x) (xs q.T) := by
  obtain ⟨hV, hWC, hWG, hcard, -⟩ :=
    binary_ode_time_solver_synth hS q hq D en hrange hdec loadC hloadV wpC hwpV
  obtain ⟨hVN, -, -, -, -, -⟩ := binary_ode_time_counts q hq loadC hloadV wpC hwpV
  obtain ⟨-, -, -, -, -, -, hout⟩ :=
    binary_ode_time_solver_certified q hq D en hrange hdec loadC hloadV wpC hwpV
  refine ⟨hV, hWC, hWG, hcard, ?_⟩
  intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs bmax ζs hζs hload hwp hbud hS' hx hGa hGint
    hbint hbmax hb hne hB hcert
  have hε := hq.ε_pos
  have hεh := hq.ε_half
  have hη : 0 < q.ε / 200 := by positivity
  exact soutcome hS hη (by linarith) (by linarith) _ hVN q.params.ratio
    (q.params.ratio_ge hq.g_ge) _ (primsT_isUnitary D en x) _ hne
    (hout x hrH hcH hrD hcD hPSD Jl Wp G bf xs bs bmax ζs hζs hload hwp hbud hS' hx hGa hGint
      hbint hbmax hb hne hB hcert)

/-- **Dissipative ODE solver from binary sparse data on a nonuniform mesh over a finite gate
set** (partial formalisation, under this package's format hypotheses, of the finite-set statement
of Theorem `ode:thm:gates`, time-dependent part, extended by uniform
refinement to nonuniform meshes with breakpoints, with finite-set synthesis as a hypothesis). The
synthesised protocol has the counts of `binary_ode_time_solver_certified_synth`; it runs on the
clock data `clockData D_m`, and for
every input and instance as in `binary_ode_time_solver_mesh` it has the guarantees
`SOutcome`. -/
theorem binary_ode_time_solver_mesh_synth (hS : Synthesis 𝒢 Xa len) (q : PubT) (hq : q.OK)
    {Mm : ℕ} (hMm : 0 < Mm) (tm : ℕ → ℝ) (hmesh : IsMesh tm Mm q.T)
    (D : Data (X × Fin Mm) n (Cfg (VW q.b)) q.s) (en : Cfg (Fin q.kx) ≃ n)
    (hrange : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin q.σ → Bool, j = en (lowWord q.σ u))
    (hdec : ∀ e z, D.decode e z = (q.c0 : ℂ) * gauss z)
    (loadC : List (NInstr ((Fin (q.params.m + 1) ⊕ Fin q.kx) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b)
      Query)) (hloadV : ∀ i ∈ loadC, i.Valid)
    (wpC : List (NInstr (Fin (q.params.m + 1) ⊕ Zs) (Fin q.m ⊕ PY q.kx q.b) Query))
    (hwpV : ∀ i ∈ wpC, i.Valid) :
    (∀ j, (∀ i ∈ synthBudget hS (q.ε / 200) (trialN (q.prep loadC wpC) j), i.Valid) ∧
      ∀ g, NInstr.gate g ∈ synthBudget hS (q.ε / 200) (trialN (q.prep loadC wpC) j) →
        GateOf 𝒢 g) ∧
    (∀ c : Query → Bool,
      ((sprotocol hS (q.ε / 200) (q.prep loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)).worstCost (wCallN c) : ℝ) ≤
        40 * q.params.ratio * nCallsN c (q.prep loadC wpC)) ∧
    (∀ c₀ c₁ : ℝ, 0 ≤ c₀ → 0 ≤ c₁ →
      (∀ ζ' : ℝ, 0 < ζ' → ζ' ≤ 1 → (len ζ' : ℝ) ≤ c₁ * Real.log (1 / ζ') + c₀) →
      ((sprotocol hS (q.ε / 200) (q.prep loadC wpC) q.params.ratio
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
        (G : ℕ → ℝ → Reg (Fin q.kx) ℂ →L[ℂ] Reg (Fin q.kx) ℂ) (bf : ℕ → ℝ → Reg (Fin q.kx) ℂ)
        (xs : ℝ → Reg (Fin q.kx) ℂ) (bm : ℕ → Reg (Fin q.kx) ℂ) (bmax ζs : ℝ),
      0 ≤ ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (clockData D hMm tm q.T q.m) en x) loadC)
        (liftB (loadIdeal Jl)) ζs →
      ApproxOn CleanX (nrun (primsT (R := ℂ) (clockData D hMm tm q.T q.m) en x) wpC)
        (liftB (matOp Wp)) ζs →
      24 * (q.params.d : ℝ) * q.ζ + 3 * ζs ≤ q.params.nu →
      SourceOK q.params (seedV (S := Fin q.kx)) Jl Wp (xs 0)
        (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) →
      (∀ r < Mm, SolvesODE (G r) (bf r) xs (tm r) (tm (r + 1))) →
      (∀ r < Mm, ∀ u ∈ Icc (tm r) (tm (r + 1)), Accretive (G r u)) →
      (∀ r < Mm, IntervalIntegrable (G r) volume (tm r) (tm (r + 1))) →
      (∀ r < Mm, IntervalIntegrable (bf r) volume (tm r) (tm (r + 1))) →
      0 ≤ bmax →
      (∀ r < Mm, ∀ u ∈ Icc (tm r) (tm (r + 1)), ‖bf r u‖ ≤ bmax) →
      xs q.T ≠ 0 →
      q.params.mass (xs 0) (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) ≤ q.g * ‖xs q.T‖ →
      meshCertificate q.params tm Mm (meshH D en x) (meshL D en x) bm G bf ‖xs 0‖ bmax ≤
        q.ε * q.params.mass (xs 0) (fun k => bm (slotPiece tm q.T (2 ^ q.m) Mm k)) /
          (2000 * q.g) →
      SOutcome (sprotocol hS (q.ε / 200) (q.prep loadC wpC) q.params.ratio
        (q.params.ratio_ge hq.g_ge)) q.ε (primsT (R := ℂ) (clockData D hMm tm q.T q.m) en x)
        (xs q.T) := by
  obtain ⟨hV, hWC, hWG, hcard, -⟩ :=
    binary_ode_time_solver_synth hS q hq (clockData D hMm tm q.T q.m) en hrange hdec loadC
      hloadV wpC hwpV
  obtain ⟨hVN, -, -, -, -, -⟩ := binary_ode_time_counts q hq loadC hloadV wpC hwpV
  obtain ⟨-, -, -, -, -, -, hout⟩ :=
    binary_ode_time_solver_mesh q hq hMm tm hmesh D en hrange hdec loadC hloadV wpC hwpV
  refine ⟨hV, hWC, hWG, hcard, ?_⟩
  intro x hrH hcH hrD hcD hPSD Jl Wp G bf xs bm bmax ζs hζs hload hwp hbud hS' hx hGa hGint
    hbint hbmax hb hne hB hcert
  have hε := hq.ε_pos
  have hεh := hq.ε_half
  have hη : 0 < q.ε / 200 := by positivity
  exact soutcome hS hη (by linarith) (by linarith) _ hVN q.params.ratio
    (q.params.ratio_ge hq.g_ge) _ (primsT_isUnitary (clockData D hMm tm q.T q.m) en x) _ hne
    (hout x hrH hcH hrD hcD hPSD Jl Wp G bf xs bm bmax ζs hζs hload hwp hbud hS' hx hGa hGint
      hbint hbmax hb hne hB hcert)

end Binary

end

end SparseHamiltonian.GateMesh.ODE
