import GateEfficientSelective.HamSim
import GateEfficientSynthesisTrials.Register

/-!
# A finite-set controlled private circuit from the native data

The endpoints of `GateEfficientSelective.HamSim` take a supplied finite-set circuit for the
enable-controlled private Cayley operation. This file constructs one from the native data of
`GateEfficientNative` (a public compute circuit `V` with the native identity `NativeOK`, and
public reversible angle arithmetic within `ζ`): the native implementation `privMacro nd ar`
compiled **selectively** (its gates of `𝒢` and its oracle calls retained, its remaining exact
gates synthesised with the budget `η`), with the synthesis ancillas `X` joined to the scratch
wires of the private register (`privSel`, on `PWr Sel PR (Z ⊕ X) bT bP A`).

* `privSel_spec`: valid, every gate a gate of `𝒢`, exactly `2 |V|_calls` primitive calls, at most
  `nKeepN + K L(η/(K+1))` gates (`K` the synthesised occurrences of the native implementation),
  and within `η + 4ζ` of the enable-controlled private operation on clean work wires (the full
  output, with the joined ancillas clean at the start).
* `nSynN_privMacro_le`: `K ≤ 2 nSynN V + 2 |arith| + 2 bP + bT + 1` (adjoint-closed `𝒢`).
* `sel_simulation_native`, `sel_time_simulation_native`: the selective endpoints of `HamSim` for
  this circuit, with `24 d (η + 4ζ) ≤ ε`.

So the supplied-circuit hypothesis of `HamSim` is met by an actual finite-set circuit whenever the
native data of the released endpoints are given, with `G_C(ξ) = |privSel|`,
`A_C(ξ) = |Z| + |X| + bT + bP + A` and `ξ = η + 4ζ`.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSelective

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim GateNative GateSynth
open GateSynthTrials (AdjClosed mem_map_gate)
open GatePointerEncoding (wordEquivFin)
open scoped InnerProduct

/-! ### Approximation on smaller sets, and the triangle inequality -/

section ApproxAux

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {Q : Type*} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]

/-- An approximation on `S` holds on every smaller set of configurations. -/
theorem approxOn_restrict {S S' : Cfg W → Prop} {C O : Reg W Q →L[ℂ] Reg W Q} {δ : ℝ}
    (h : ApproxOn S C O δ) (hS : ∀ y, S' y → S y) : ApproxOn S' C O δ := by
  intro ψ hψ
  exact h ψ (fun y hy => hψ y (fun h' => hy (hS y h')))

/-- Errors of successive approximations add. -/
theorem approxOn_trans {S : Cfg W → Prop} {C₁ C₂ O : Reg W Q →L[ℂ] Reg W Q} {δ₁ δ₂ : ℝ}
    (h₁ : ApproxOn S C₁ C₂ δ₁) (h₂ : ApproxOn S C₂ O δ₂) : ApproxOn S C₁ O (δ₁ + δ₂) := by
  intro ψ hψ
  calc ‖C₁ ψ - O ψ‖ = ‖(C₁ ψ - C₂ ψ) + (C₂ ψ - O ψ)‖ := by congr 1; abel
    _ ≤ ‖C₁ ψ - C₂ ψ‖ + ‖C₂ ψ - O ψ‖ := norm_add_le _ _
    _ ≤ δ₁ * ‖ψ‖ + δ₂ * ‖ψ‖ := add_le_add (h₁ ψ hψ) (h₂ ψ hψ)
    _ = (δ₁ + δ₂) * ‖ψ‖ := by ring

end ApproxAux

/-! ### Joining the synthesis ancillas to the scratch wires -/

section Reassoc

variable {Sel PR Z X : Type*} {bT bP A : ℕ}

/-- The wires of the private register with the synthesis ancillas, mapped into the private
register whose scratch is `Z ⊕ X`. -/
def reW : PWr Sel PR Z bT bP A ⊕ X → PWr Sel PR (Z ⊕ X) bT bP A
  | .inl (.inl u) => .inl u
  | .inl (.inr (.inl (.inl s))) => .inr (.inl (.inl s))
  | .inl (.inr (.inl (.inr z))) => .inr (.inl (.inr (.inl z)))
  | .inl (.inr (.inr w)) => .inr (.inr w)
  | .inr x => .inr (.inl (.inr (.inr x)))

theorem reW_injective : Function.Injective (reW (Sel := Sel) (PR := PR) (Z := Z) (X := X)
    (bT := bT) (bP := bP) (A := A)) := by
  intro p q h
  rcases p with (u | ((s | z) | w)) | x <;> rcases q with (u' | ((s' | z') | w')) | x' <;>
    simp_all [reW]

/-- The joining embedding (a bijection of the wires). -/
def rePW : PWr Sel PR Z bT bP A ⊕ X ↪ PWr Sel PR (Z ⊕ X) bT bP A :=
  ⟨reW, reW_injective⟩

theorem rePW_inl_selPR (s : Sel ⊕ PR) :
    rePW (X := X) (Sum.inl (selPR (Z := Z) (bT := bT) (bP := bP) (A := A) s)) = selPR s := rfl

theorem rePW_inl_enW :
    rePW (X := X) (Sum.inl (enW : PWr Sel PR Z bT bP A)) = (enW : PWr Sel PR (Z ⊕ X) bT bP A) :=
  rfl

theorem enW_ne_selPR (s : Sel ⊕ PR) :
    (selPR (Z := Z) (bT := bT) (bP := bP) (A := A) s : PWr Sel PR Z bT bP A) ≠ enW := by
  simp [selPR, enW]

variable [Fintype Sel] [DecidableEq Sel] [Fintype PR] [DecidableEq PR] [Fintype Z]
  [DecidableEq Z] [Fintype X] [DecidableEq X]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The lifted enable-controlled operation, joined, is the enable-controlled operation of the
joined register.** -/
theorem localOp_rePW_liftB_ctrlIdeal (Dsel : Reg (Sel ⊕ PR) R →L[ℂ] Reg (Sel ⊕ PR) R) :
    localOp (rePW (X := X)) rePW.injective
        (fun _ => liftB (X := X) (ctrlIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) Dsel)) =
      ctrlIdeal (Z := Z ⊕ X) (bT := bT) (bP := bP) (A := A) Dsel := by
  have h1 : liftB (X := X) (ctrlIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) Dsel) =
      localOp ((Sum.inl : PWr Sel PR Z bT bP A → PWr Sel PR Z bT bP A ⊕ X) ∘ selPR)
        (Sum.inl_injective.comp selPR.injective)
        (fun z => if (clearCfg selPR (fun a => z (Sum.inl a))) enW then Dsel else 1) := by
    unfold liftB ctrlIdeal
    exact GateODE.localOp_localOp Sum.inl_injective selPR.injective
      (fun _ y => if y enW then Dsel else 1)
  rw [h1]
  have h2 := GateODE.localOp_localOp' (rePW (X := X)).injective
    (Sum.inl_injective.comp (selPR (Sel := Sel) (PR := PR) (Z := Z) (bT := bT) (bP := bP)
      (A := A)).injective) (selPR (Z := Z ⊕ X) (bT := bT) (bP := bP) (A := A))
    (selPR (Z := Z ⊕ X) (bT := bT) (bP := bP) (A := A)).injective (fun b => rfl)
    (fun _ z => if (clearCfg selPR (fun a => z (Sum.inl a))) enW then Dsel else (1 : Reg (Sel ⊕ PR) R →L[ℂ] Reg (Sel ⊕ PR) R))
  refine h2.trans ?_
  unfold ctrlIdeal
  congr 1
  funext z'
  rw [clearCfg_apply_out _ _ _ (fun a => enW_ne_selPR a),
    clearCfg_apply_out _ _ _ (fun a => by
      simp only [Function.comp_apply, ne_eq, Sum.inl.injEq]
      exact enW_ne_selPR a)]
  rfl

end Reassoc

/-! ### The selective private circuit -/

section Private

variable {Sel PR Z Y J X : Type*} [Fintype Sel] [DecidableEq Sel] [Fintype PR] [DecidableEq PR]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **The finite-set controlled private circuit from the native data**: the native
implementation compiled selectively with the budget `η`, the synthesis ancillas joined to the
scratch wires. -/
def privSel (hS : Synthesis 𝒢 X L) (η : ℝ) (nd : NativeOp Sel PR Z Y J)
    (ar : Arith (NB Sel PR Z)) : List (NInstr (PWr Sel PR (Z ⊕ X) ar.bT ar.bP ar.A) Y J) :=
  (selBudget hS η (privMacro nd ar)).map (NInstr.map rePW)

omit [Fintype Sel] [DecidableEq Sel] [Fintype PR] [DecidableEq PR] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X] in
/-- The synthesised gate occurrences of the native implementation: the exact gates of the two
copies of `V`, the arithmetic, its inverse and the rotation gates. -/
theorem nSynN_privMacro_le (hadj : AdjClosed 𝒢) (nd : NativeOp Sel PR Z Y J)
    (ar : Arith (NB Sel PR Z)) :
    nSynN 𝒢 (privMacro nd ar) ≤
      2 * nSynN 𝒢 nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1) := by
  have h1 := nSynN_nGatesOf (Y := Y) (J := J) 𝒢 (ar.circ.map (GateODE.Gate.map aEmb))
  have h2 := nSynN_nGatesOf (Y := Y) (J := J) 𝒢
    (rotGates enW (tgtW (Sel := Sel) (Z := Z) (bT := ar.bT) (bP := ar.bP) (A := ar.A) nd.o)
      twW pwW)
  have h3 := nSynN_nGatesOf (Y := Y) (J := J) 𝒢 (gInv (ar.circ.map (GateODE.Gate.map aEmb)))
  rw [List.length_map] at h1
  rw [gInv_length, List.length_map] at h3
  rw [rotGates_length] at h2
  simp only [privMacro, nSynN_append, nSynN_ninv 𝒢 hadj, nSynN_map]
  omega

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The selective private circuit**: valid, over `𝒢`, with the calls of the native
implementation, at most `nKeepN + K L(η/(K+1))` gates, and within `η + 4ζ` of the enable-controlled
private operation on clean work wires (scratch, joined ancillas and arithmetic wires). -/
theorem privSel_spec (hS : Synthesis 𝒢 X L) {η : ℝ} (hη : 0 < η) (nd : NativeOp Sel PR Z Y J)
    (hnd : nd.Public) (ar : Arith (NB Sel PR Z)) {ζ : ℝ} (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ) :
    (∀ i ∈ privSel hS η nd ar, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ privSel hS η nd ar → GateOf 𝒢 g) ∧
    nGatesN (privSel hS η nd ar) ≤ nKeepN 𝒢 (privMacro nd ar) +
      nSynN 𝒢 (privMacro nd ar) * L (η / (nSynN 𝒢 (privMacro nd ar) + 1)) ∧
    (∀ p : J → Bool, nCallsN p (privSel hS η nd ar) = 2 * nCallsN p nd.V) ∧
    ∀ (prim : J → Reg Y R →L[ℂ] Reg Y R), (∀ j, IsUnitary (prim j)) →
      ∀ Dsel : Reg (Sel ⊕ PR) R →L[ℂ] Reg (Sel ⊕ PR) R, NativeOK prim nd Dsel →
      ApproxOn CleanP (nrun prim (privSel hS η nd ar)) (ctrlIdeal Dsel) (η + 4 * ζ) := by
  have hV := privMacro_valid nd hnd ar har.elem har.classical
  obtain ⟨hv, hk, hg, hc⟩ := selBudget_spec hS hη _ hV
  refine ⟨valid_map_list _ _ hv, fun g hg' => ?_, ?_, fun p => ?_, ?_⟩
  · obtain ⟨g', hg'', rfl⟩ := mem_map_gate _ _ g hg'
    exact (hk g' hg'').map _
  · rw [privSel, nGatesN_map]
    exact hg
  · rw [privSel, nCallsN_map, hc p, privMacro_nCalls]
  · intro prim hprim Dsel hN
    have h1 := selBudget_approxOn prim hS hη _ hV hprim
    have h2 : ApproxOn (fun y : Cfg (PWr Sel PR Z ar.bT ar.bP ar.A ⊕ X) =>
        CleanP (fun p => y (Sum.inl p)))
        (localOp Sum.inl Sum.inl_injective (fun _ => nrun prim (privMacro nd ar)))
        (localOp Sum.inl Sum.inl_injective (fun _ => ctrlIdeal Dsel)) (4 * ζ) :=
      approxOn_localOp Sum.inl_injective _ _ (by linarith) (SA := CleanP) (fun y hy => hy)
        (fun _ => privMacro_approx prim hprim nd hnd ar hζ har Dsel hN)
    have h3 : ApproxOn (fun y : Cfg (PWr Sel PR Z ar.bT ar.bP ar.A ⊕ X) =>
        CleanP (fun p => y (Sum.inl p)) ∧ CleanX y)
        (nrun prim (selBudget hS η (privMacro nd ar)))
        (liftB (X := X) (ctrlIdeal Dsel)) (η + 4 * ζ) :=
      approxOn_trans (approxOn_restrict h1 (fun y hy => hy.2))
        (approxOn_restrict h2 (fun y hy => hy.1))
    unfold privSel
    rw [nrun_map, ← localOp_rePW_liftB_ctrlIdeal]
    refine approxOn_localOp rePW.injective _ _ (by linarith)
      (SA := fun y : Cfg (PWr Sel PR Z ar.bT ar.bP ar.A ⊕ X) =>
        CleanP (fun p => y (Sum.inl p)) ∧ CleanX y) ?_ (fun _ => h3)
    intro y hy
    exact ⟨⟨fun z => hy.1 (Sum.inl z), fun w => hy.2 w⟩, fun x => hy.1 (Sum.inr x)⟩

end Private

/-! ### The selective endpoints with the native data -/

section Endpoints

variable {S Z Y J X : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **Theorem `hs:thm:gates` over a finite gate set from the native data, with the private
circuit compiled selectively once** (time-independent part). Under the hypotheses of
`GateNative.native_simulation` (with `24 d (η + 4ζ) ≤ ε` for the private budget), the synthesis
hypothesis with `L ζ ≤ c₁ log(1/ζ) + c₀` and an adjoint-closed `𝒢`: the circuit
`selSim hS … (privSel hS η nd ar)` consists of valid gates of `𝒢` and primitive calls, makes
exactly `12 d` times the primitive calls of `V`, has at most
`6 d |privSel| + G₀ (c₁ log((G₀+1)/(ε/4)) + c₀ + 1)` gates, with
`|privSel| ≤ nKeepN + K L(η/(K+1))` and `K ≤ 2 nSynN V + 2 |arith| + 2 bP + bT + 1`, and its full
output on the clean system embedding is within `ε` of `exp(-iτH)`. -/
theorem sel_simulation_native (hS : Synthesis 𝒢 X L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (a : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp Empty (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB Empty (Fin a ⊕ S) Z)) (ζ η : ℝ) (hζ : 0 ≤ ζ) (hη : 0 < η)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D R1 : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (H : Reg S R →L[ℂ] Reg S R)
    (hD : IsUnitary D) (hN : NativeOK prim nd (selOp (fun _ : Cfg Empty => D)))
    (τ Q b qbar ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hξε : 24 * (fDeg Q τ qbar (ε / 2) : ℝ) * (η + 4 * ζ) ≤ ε) :
    (∀ i ∈ selSim hS a τ Q qbar ε UJg (privSel hS η nd ar), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selSim hS a τ Q qbar ε UJg (privSel hS η nd ar) → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selSim hS a τ Q qbar ε UJg (privSel hS η nd ar)) =
      12 * fDeg Q τ qbar (ε / 2) * nCallsN p nd.V) ∧
    (nGatesN (selSim hS a τ Q qbar ε UJg (privSel hS η nd ar)) : ℝ) ≤
      6 * (fDeg Q τ qbar (ε / 2) : ℝ) * nGatesN (privSel hS η nd ar) +
        ((200 * (fDeg Q τ qbar (ε / 2) + 1) * (a + simM τ (ε / 2) + simR Q τ qbar (ε / 2) + 1) +
          84 * fDeg Q τ qbar (ε / 2) * UJg.length : ℕ) : ℝ) *
        (c₁ * Real.log ((((200 * (fDeg Q τ qbar (ε / 2) + 1) *
          (a + simM τ (ε / 2) + simR Q τ qbar (ε / 2) + 1) +
          84 * fDeg Q τ qbar (ε / 2) * UJg.length : ℕ) : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    nGatesN (privSel hS η nd ar) ≤ nKeepN 𝒢 (privMacro nd ar) +
      nSynN 𝒢 (privMacro nd ar) * L (η / (nSynN 𝒢 (privMacro nd ar) + 1)) ∧
    nSynN 𝒢 (privMacro nd ar) ≤
      2 * nSynN 𝒢 nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1) ∧
    Fintype.card (HW (SimWire a Q τ qbar (ε / 2)) S Empty (Z ⊕ X) ar.bT ar.bP ar.A ⊕ X) =
      Fintype.card S + (2 * a + 3 * simM τ (ε / 2) + 6 * simR Q τ qbar (ε / 2) + 3) +
        (Fintype.card Z + Fintype.card X + ar.bT + ar.bP + ar.A + 3) + Fintype.card X ∧
    ‖nrun prim (selSim hS a τ Q qbar ε UJg (privSel hS η nd ar)) ∘L
        (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ ε := by
  obtain ⟨hpV, hpG, hpN, hpC, hpA⟩ := privSel_spec (R := R) hS hη nd hnd ar hζ har
  have hξ : 0 ≤ η + 4 * ζ := by linarith
  obtain ⟨hv, hk, hcalls, -, hgates, hcard, herr, -⟩ := sel_simulation hS hadj hc₀ hc₁ hL a prim
    hprim UJg hUJg (privSel hS η nd ar) hpV hpG (η + 4 * ζ) hξ D R1 H hD
    (hpA prim hprim _ hN) τ Q b qbar ε hτ hQ hRight hLeft hR1 hBoundary hSelf hH hEndpoint hbq hqQ
    hε hε1 hξε
  refine ⟨hv, hk, fun p => ?_, hgates, hpN, nSynN_privMacro_le hadj nd ar, ?_, ?_⟩
  · rw [hcalls p, hpC p]
    ring
  · rw [hcard, Fintype.card_sum]
  · -- the same bound, up to the instance paths of the joined scratch `Z ⊕ X`
    convert herr using 4

/-- **Theorem `hs:thm:gates` over a finite gate set from the native data, time-dependent
part**: the selective time-dependent endpoint `sel_time_simulation` for the slot-selected native
data of `GateNative.native_time_simulation`, with the private circuit compiled selectively once
(`privSel`), under `24 d (η + 4ζ) ≤ ε`. -/
theorem sel_time_simulation_native (hS : Synthesis 𝒢 X L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (a m : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (Fin m) (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (Fin m) (Fin a ⊕ S) Z)) (ζ η : ℝ) (hζ : 0 ≤ ζ) (hη : 0 < η)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D R1 : ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R))
    (hN : NativeOK prim nd (selOp (fun w : Cfg (Fin m) => D (wordEquivFin m w))))
    (Hpath : ℝ → Reg S R →L[ℂ] Reg S R) (Hs : ℕ → Reg S R →L[ℂ] Reg S R)
    (t α β δ Q b qbar ε : ℝ) (ht : 0 ≤ t) (hα : 0 < α) (hβ : 0 ≤ β) (hQ : 1 ≤ Q)
    (hqQ : qbar ≤ Q) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hCayley : TimeSchedule.steps (α * t) (ε / 12) ≤ 2 ^ m)
    (hFreeze : 8 * β * t ^ 2 ≤ ε * 2 ^ m)
    (hD : ∀ k < 2 ^ m, IsUnitary (D k))
    (hRight : ∀ k < 2 ^ m, (1 - D k) ∘L R1 k = 1)
    (hLeft : ∀ k < 2 ^ m, R1 k ∘L (1 - D k) = 1) (hR1 : ∀ k < 2 ^ m, ‖R1 k‖ ≤ Q)
    (hBoundary : ∀ k < 2 ^ m, (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 k ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) =
        (2 : ℂ)⁻¹ • (1 + Complex.I • ((α : ℂ)⁻¹ • Hs k)))
    (hEndpoint : ∀ k < 2 ^ m, ‖R1 k ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2)
    (hSelf : ∀ k < 2 ^ m, star (Hs k) = Hs k) (hHs : ∀ k < 2 ^ m, ‖Hs k‖ ≤ α)
    (hPath : ∀ u ∈ Set.Icc 0 t, star (Hpath u) = Hpath u)
    (hLip : ∀ u ∈ Set.Icc 0 t, ∀ v ∈ Set.Icc 0 t, ‖Hpath u - Hpath v‖ ≤ β * |u - v|)
    (hVal : ∀ k : ℕ, k < 2 ^ m → ‖Hpath (k * t / 2 ^ m) - Hs k‖ ≤ δ)
    (hValBudget : 8 * t * δ ≤ ε)
    (hξε : 24 * (fDeg Q (α * t) qbar (ε / 4) : ℝ) * (η + 4 * ζ) ≤ ε) :
    (∀ i ∈ selSimT hS a m (α * t) Q qbar ε UJg (privSel hS η nd ar), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selSimT hS a m (α * t) Q qbar ε UJg (privSel hS η nd ar) →
      GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selSimT hS a m (α * t) Q qbar ε UJg (privSel hS η nd ar)) =
      12 * fDeg Q (α * t) qbar (ε / 4) * nCallsN p nd.V) ∧
    (nGatesN (selSimT hS a m (α * t) Q qbar ε UJg (privSel hS η nd ar)) : ℝ) ≤
      6 * (fDeg Q (α * t) qbar (ε / 4) : ℝ) * nGatesN (privSel hS η nd ar) +
        ((200 * (fDeg Q (α * t) qbar (ε / 4) + 1) * (a + m + simR Q (α * t) qbar (ε / 4) + 1) +
          84 * fDeg Q (α * t) qbar (ε / 4) * UJg.length : ℕ) : ℝ) *
        (c₁ * Real.log ((((200 * (fDeg Q (α * t) qbar (ε / 4) + 1) *
          (a + m + simR Q (α * t) qbar (ε / 4) + 1) +
          84 * fDeg Q (α * t) qbar (ε / 4) * UJg.length : ℕ) : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    nGatesN (privSel hS η nd ar) ≤ nKeepN 𝒢 (privMacro nd ar) +
      nSynN 𝒢 (privMacro nd ar) * L (η / (nSynN 𝒢 (privMacro nd ar) + 1)) ∧
    nSynN 𝒢 (privMacro nd ar) ≤
      2 * nSynN 𝒢 nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1) ∧
    ∀ U : ℝ → Reg S R →L[ℂ] Reg S R, U 0 = 1 → TimeDependent.SolvesOn Hpath U 0 t →
      ‖nrun prim (selSimT hS a m (α * t) Q qbar ε UJg (privSel hS η nd ar)) ∘L
          (cleanEmb (X := X) ∘L sysEmb (io (P := Reg S R))) -
          (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L U t‖ ≤ ε := by
  obtain ⟨hpV, hpG, hpN, hpC, hpA⟩ := privSel_spec (R := R) hS hη nd hnd ar hζ har
  have hξ : 0 ≤ η + 4 * ζ := by linarith
  obtain ⟨hv, hk, hcalls, -, hgates, -, -, -, herr⟩ := sel_time_simulation hS hadj hc₀ hc₁ hL a m
    prim hprim UJg hUJg (privSel hS η nd ar) hpV hpG (η + 4 * ζ) hξ D R1 (hpA prim hprim _ hN)
    Hpath Hs t α β δ Q b qbar ε ht hα hβ hQ hqQ hε hε1 hCayley hFreeze hD hRight hLeft hR1
    hBoundary hEndpoint hbq hSelf hHs hPath hLip hVal hValBudget hξε
  refine ⟨hv, hk, fun p => ?_, hgates, hpN, nSynN_privMacro_le hadj nd ar,
    fun U hU0 hU => ?_⟩
  · rw [hcalls p, hpC p]
    ring
  · -- the same bound, up to the instance paths of the joined scratch `Z ⊕ X`
    convert herr U hU0 hU using 4

end Endpoints

end

end SparseHamiltonian.GateSelective
