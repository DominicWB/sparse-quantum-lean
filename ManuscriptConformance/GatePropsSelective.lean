import ManuscriptConformance.GateProps
import GateEfficientSelective.HamBridge

/-!
# Conformance: finite-set forms of `gate:prop:finite` and `gate:prop:core` with a supplied private circuit

Item B3 asks that the selective-synthesis transfer of Appendix `gate:sec:proof` accept an allowed
controlled private circuit with explicit gate and work costs and a clean full-output error,
leaving the supplied finite-set subcircuit charged at its actual linear cost and synthesising only
the remaining known gates. The native-model forms of `GateProps` (`gate_prop_finite`,
`gate_prop_core_native`) have no synthesis; the finite-set theorems of the package synthesise end
to end. Here:

* `selOf hS δ UJg pc l`: the released circuit `l` (sector-controlled oracle calls, `SecOK`) with every
  private call replaced by the supplied circuit `pc` (inverse calls by its literal reverse-adjoint),
  every boundary call by the controlled gates of `U_J`, and the remaining exact gates outside `𝒢`
  synthesised with the budget `δ` (`GateSelective.selBudget`); the work wires of `pc` are shared by
  all private calls and returned clean;
* `sel_transfer` (the generic transfer): if `pc` is valid, over `𝒢` and within `ξ` of the
  enable-controlled private operation on clean work wires, and the released circuit is within `ε₀`
  of `U`, then `selOf` is valid and over `𝒢`, makes exactly `n_P` copies of the calls of `pc`,
  synthesises at most `G_known = nGates l + 7 C_J n_UJ` occurrences, has at most
  `n_P |pc| + G_known (c₁ log((G_known+1)/δ) + c₀ + 1)` gates on
  `|wires of l| + |S| + (|Z| + b_T + b_P + A + 3) + |X|` qubits, and is within `ε₀ + n_P ξ + δ` of `U`
  on the clean system embedding (replacement and telescoping: `GateSelective.hcircP_error`;
  inverse calls: `GateSelective.ctrl_inv_approx`; synthesis: `GateSelective.selBudget_error`);
* `pcSel hS η pc`, `pcSel_spec`: any valid private circuit compiled selectively once, the synthesis
  ancillas joined to the scratch: over `𝒢`, the same calls, at most `nKeepN + K L(η/(K+1))` gates, and
  within `η + ξ` of the enable-controlled operation when `pc` is within `ξ`
  (`GateSelective.privSel_spec` is the instance `pc = privMacro nd ar`);
* `gate_prop_finite_sel`: Proposition `gate:prop:finite` over a finite gate set with a supplied
  finite-set private circuit: with `n_P ≤ c_* R`, `ξ ≤ ε/(4 c_* R)` and `δ = ε/4`, error `ε`;
  `gate_prop_finite_sel_native`: the private circuit compiled from the native data
  (`GateSelective.privSel`);
* `gate_prop_core_sel`: Proposition `gate:prop:core` over a finite gate set with a supplied finite-set
  private circuit: `6 d` private calls, at most
  `6 d |pc| + G (c₁ log((G+1)/δ) + c₀ + 1)` gates with
  `G = 200 (d+1)(a+m+r+1) + 84 d C_J`, error `ε + 6 d ξ + δ`; `gate_prop_core_sel_native`: the
  factor-conjugated native private call `GateOptimalBinary.ClipNative` compiled selectively, error
  `ε + 6 d (η + 6ξ + 4ζ) + δ`.

* the signed regime, whose factor calls are unconditional: `unc_inv_approx`,
  `localOp_rePW_liftB_uncIdeal`, `pcSel_unc` (the inverse and the selective compilation of a supplied
  circuit for the unconditional factor), `hmacroP_unc_approx`, `hcircP_unc_approx`,
  `hcircP_unc_error` (the same macros, with the private calls read as unconditional factor calls:
  the errors add over the factor calls), `sel_signed_transfer` (the finite-set transfer for circuits
  of the signed form, `UncOK`, on `a + 1` ancillas with `U_J` on the last `a`), and
  `gate_prop_signed_sel` (Proposition `gate:prop:signed` over a finite gate set with a supplied
  finite-set factor circuit: error `ε + n_P ξ + δ`), `gate_prop_signed_sel_native` (the native factor
  `factorMacro` compiled selectively: error `ε + n_P (η + 3ξ) + δ`).

Scope: the success projection and the sign reflection of the signed proposition are those of
`wKnown` (designated flag qubits), as in `gate_prop_signed`; a general known projection `Π` and
reflection `Z` with their implementation charged is not formalised. The exact coefficient rounding of
the manuscript (`Σ |λ̂ - λ| ≤ ε²/144`) is not formalised: finite synthesis here follows the selective
construction (the supplied subcircuits retained, the other exact gates synthesised), and the
propositions are matched at the level of their existence and resource statements. The released
circuits keep their `SecOK`/`UncOK` forms.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 8192

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.OracleCircuit
  SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim SparseHamiltonian.GateNative
  SparseHamiltonian.GateSynth SparseHamiltonian.GateSelective GateOptimalPrecision
open SparseHamiltonian.GateSynthTrials (AdjClosed mem_map_gate)
open GateODE (localOp_gateOp overwrite_apply_out)
open LargeSparsityCore LargeSparsityCore.Parameters
open SignedFactorSimulation (rb)
open scoped InnerProduct InnerProductSpace

/-! ### The selective compilation of a supplied private circuit -/

section PcSel

variable {Sel PR Z Y J Xs : Type*} [Fintype Sel] [DecidableEq Sel] [Fintype PR] [DecidableEq PR]
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] [Fintype Xs] [DecidableEq Xs]
variable {𝒢 : Set Kind} {L : ℝ → ℕ} {bT bP A : ℕ}

/-- **A private circuit compiled selectively once**: its gates of `𝒢` and its oracle calls retained,
its other exact gates synthesised with the budget `η`, the synthesis ancillas joined to the
scratch wires. -/
def pcSel (hS : Synthesis 𝒢 Xs L) (η : ℝ) (pc : List (NInstr (PWr Sel PR Z bT bP A) Y J)) :
    List (NInstr (PWr Sel PR (Z ⊕ Xs) bT bP A) Y J) :=
  (selBudget hS η pc).map (NInstr.map rePW)

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The selectively compiled private circuit**: valid, over `𝒢`, the same calls, at most
`nKeepN + K L(η/(K+1))` gates, and within `η + ξ` of the enable-controlled operation on clean work
wires (scratch, joined ancillas, arithmetic wires) when the supplied circuit is within `ξ`. -/
theorem pcSel_spec (hS : Synthesis 𝒢 Xs L) {η : ℝ} (hη : 0 < η)
    (pc : List (NInstr (PWr Sel PR Z bT bP A) Y J)) (hpcV : ∀ i ∈ pc, i.Valid) :
    (∀ i ∈ pcSel hS η pc, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ pcSel hS η pc → GateOf 𝒢 g) ∧
    nGatesN (pcSel hS η pc) ≤ nKeepN 𝒢 pc + nSynN 𝒢 pc * L (η / (nSynN 𝒢 pc + 1)) ∧
    (∀ p : J → Bool, nCallsN p (pcSel hS η pc) = nCallsN p pc) ∧
    ∀ (prim : J → Reg Y R →L[ℂ] Reg Y R), (∀ j, IsUnitary (prim j)) →
      ∀ (Dsel : Reg (Sel ⊕ PR) R →L[ℂ] Reg (Sel ⊕ PR) R) {ξ : ℝ}, 0 ≤ ξ →
      ApproxOn CleanP (nrun prim pc) (ctrlIdeal Dsel) ξ →
      ApproxOn CleanP (nrun prim (pcSel hS η pc)) (ctrlIdeal Dsel) (η + ξ) := by
  obtain ⟨hv, hk, hg, hc⟩ := selBudget_spec hS hη _ hpcV
  refine ⟨valid_map_list _ _ hv, fun g hg' => ?_, ?_, fun p => ?_, ?_⟩
  · obtain ⟨g', hg'', rfl⟩ := mem_map_gate _ _ g hg'
    exact (hk g' hg'').map _
  · rw [pcSel, nGatesN_map]
    exact hg
  · rw [pcSel, nCallsN_map, hc p]
  · intro prim hprim Dsel ξ hξ hpc
    have h1 := selBudget_approxOn prim hS hη _ hpcV hprim
    have h2 : ApproxOn (fun y : Cfg (PWr Sel PR Z bT bP A ⊕ Xs) =>
        CleanP (fun p => y (Sum.inl p)))
        (localOp Sum.inl Sum.inl_injective (fun _ => nrun prim pc))
        (localOp Sum.inl Sum.inl_injective (fun _ => ctrlIdeal Dsel)) ξ :=
      approxOn_localOp Sum.inl_injective _ _ hξ (SA := CleanP) (fun y hy => hy)
        (fun _ => hpc)
    have h3 : ApproxOn (fun y : Cfg (PWr Sel PR Z bT bP A ⊕ Xs) =>
        CleanP (fun p => y (Sum.inl p)) ∧ CleanX y)
        (nrun prim (selBudget hS η pc))
        (liftB (X := Xs) (ctrlIdeal Dsel)) (η + ξ) :=
      approxOn_trans (approxOn_restrict h1 (fun y hy => hy.2))
        (approxOn_restrict h2 (fun y hy => hy.1))
    unfold pcSel
    rw [nrun_map, ← localOp_rePW_liftB_ctrlIdeal]
    refine approxOn_localOp rePW.injective _ _ (by linarith)
      (SA := fun y : Cfg (PWr Sel PR Z bT bP A ⊕ Xs) =>
        CleanP (fun p => y (Sum.inl p)) ∧ CleanX y) ?_ (fun _ => h3)
    intro y hy
    exact ⟨⟨fun z => hy.1 (Sum.inl z), fun w => hy.2 w⟩, fun x => hy.1 (Sum.inr x)⟩

end PcSel

/-! ### The generic finite-set transfer -/

section Transfer

variable {S Z Y J Xs : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y] [Fintype Xs] [DecidableEq Xs] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **The selective finite-set circuit of a released circuit with a supplied private circuit.** -/
abbrev selOf (hS : Synthesis 𝒢 Xs L) (δ : ℝ) {a m r K : ℕ} (UJg : List (Gate (Fin a ⊕ S)))
    (pc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J))
    (l : List (Instr (Wire a m r K))) :
    List (NInstr (HW (Wire a m r K) S Empty Z bT bP A ⊕ Xs) Y J) :=
  selBudget hS δ (hcircP (X' := Empty) (wireRel a m r K) (noSel _) UJg pc l)

/-- **The known gates of a released circuit**: its elementary gates and the `7 C_J` controlled
gates of each boundary call. -/
abbrev knownG {a m r K : ℕ} (CJ : ℕ) (l : List (Instr (Wire a m r K))) : ℕ :=
  nGates l + nUJ l * (7 * CJ)

/-- **The finite-set transfer with a supplied private circuit** (the generic step of
`gate:prop:finite`). For a valid released circuit `l` with sector-controlled oracle calls whose
full output, with `U_J = UJop UJg` and the private operation `D`, is within `ε₀` of `U`, and a valid
supplied private circuit `pc` over `𝒢` within `ξ` of the enable-controlled `D` on clean work wires:
the selective circuit is valid and over `𝒢`; it makes exactly `n_P` copies of the calls of `pc`; it
synthesises at most `G_known` occurrences; it has at most
`n_P |pc| + G_known (c₁ log((G_known+1)/δ) + c₀ + 1)` gates; it has
`|wires of l| + |S| + (|Z| + b_T + b_P + A + 3) + |X|` qubits; and its full output, every qubit
outside the system clean, is within `ε₀ + n_P ξ + δ` of `U`. -/
theorem sel_transfer (hS : Synthesis 𝒢 Xs L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    {a m r K : ℕ} (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (pc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J)) (hpcV : ∀ i ∈ pc, i.Valid)
    (hpcG : ∀ g, NInstr.gate g ∈ pc → GateOf 𝒢 g) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (hD : IsUnitary D)
    (hpc : ApproxOn CleanP (nrun prim pc) (ctrlIdeal (selOp (fun _ : Cfg Empty => D))) ξ)
    (l : List (Instr (Wire a m r K))) (hv : ∀ i ∈ l, i.Valid Wire.anc)
    (hsec : ∀ i ∈ l, SecOK (wireRel a m r K) i) (U : Reg S R →L[ℂ] Reg S R) {ε₀ δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hrel : ‖run (simSem (P := Reg S R) (UJop (R := R) UJg) D) l ∘L io - io ∘L U‖ ≤ ε₀) :
    (∀ i ∈ selOf hS δ UJg pc l, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selOf hS δ UJg pc l → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selOf hS δ UJg pc l) = nPriv l * nCallsN p pc) ∧
    nSynN 𝒢 (hcircP (X' := Empty) (wireRel a m r K) (noSel _) UJg pc l) ≤
      knownG UJg.length l ∧
    (nGatesN (selOf hS δ UJg pc l) : ℝ) ≤
      (nPriv l : ℝ) * nGatesN pc + (knownG UJg.length l : ℝ) *
        (c₁ * Real.log (((knownG UJg.length l : ℝ) + 1) / δ) + c₀ + 1) ∧
    Fintype.card (HW (Wire a m r K) S Empty Z bT bP A ⊕ Xs) =
      Fintype.card (Wire a m r K) + Fintype.card S + (Fintype.card Z + bT + bP + A + 3) +
        Fintype.card Xs ∧
    ‖nrun prim (selOf hS δ UJg pc l) ∘L (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L U‖ ≤ ε₀ + (nPriv l : ℝ) * ξ + δ := by
  have hvN := hcircP_valid (X' := Empty) (wireRel a m r K) (noSel _) UJg hUJg pc hpcV l hv
  obtain ⟨hv', hk, -, hc⟩ := selBudget_spec hS hδ _ hvN
  have h0 := hcircP_nil_nGates (X' := Empty) (Z := Z) (bT := bT) (bP := bP) (A := A) (Y := Y)
    (J := J) (wireRel a m r K) (noSel _) UJg hUJg l
  rw [mul_one] at h0
  have hsyn : nSynN 𝒢 (hcircP (X' := Empty) (wireRel a m r K) (noSel _) UJg pc l) ≤
      knownG UJg.length l :=
    (nSynN_hcircP_le 𝒢 hadj _ _ UJg pc hpcG l).trans h0
  refine ⟨hv', hk, fun p => (hc p).trans (hcircP_nCalls p _ _ UJg pc l), hsyn, ?_, ?_, ?_⟩
  · have h1 := selBudget_gates_log hS hc₀ hc₁ hL hδ hδ1 _ hvN (knownG UJg.length l : ℝ)
      (by exact_mod_cast hsyn)
    have hNk : (nKeepN 𝒢 (hcircP (X' := Empty) (wireRel a m r K) (noSel _) UJg pc l) : ℝ) ≤
        (nPriv l : ℝ) * nGatesN pc + (knownG UJg.length l : ℝ) := by
      have h2 : nKeepN 𝒢 (hcircP (X' := Empty) (wireRel a m r K) (noSel _) UJg pc l) ≤
          nPriv l * nGatesN pc + knownG UJg.length l := by
        have := nKeepN_le 𝒢 (hcircP (X' := Empty) (wireRel a m r K) (noSel _) UJg pc l)
        rw [hcircP_nGates] at this
        unfold knownG
        omega
      exact_mod_cast h2
    exact sel_count_arith hNk h1
  · rw [Fintype.card_sum, card_HW]
    simp only [Fintype.card_empty, add_zero]
  · have hDu : ∀ w, IsUnitary (constFam D false w) := fun _ => hD
    have hDadj : ∀ w, constFam D true w = (constFam D false w)† := fun _ => rfl
    have hio : ∀ ψ : Reg S R, ‖(io (P := Reg S R) (a := a) (m := m) (r := r) (K := K)) ψ‖ = ‖ψ‖ :=
      fun ψ => by rw [io_apply, norm_bas]
    have herr := hcircP_error (X' := Empty) prim hprim (wireRel _ _ _ _) (noSel _) UJg hUJg pc
      hpcV hξ (constFam D) hDu hDadj hpc l hv io hio U _
      (prodOps_evalSel_const UJg D l hsec) hrel
    refine (selBudget_error_of hS hδ _ hvN prim hprim _ ?_ U herr).trans le_rfl
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le

end Transfer

/-! ### Proposition `gate:prop:finite` over a finite gate set -/

section FiniteSel

variable {S Z Y J Xs : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y] [Fintype Xs] [DecidableEq Xs] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **Proposition `gate:prop:finite` over a finite gate set with a supplied finite-set private
circuit.** For an ideal sector-controlled circuit with error at most `ε/2` and `n_P ≤ c_* R` private
calls, and a supplied private circuit over `𝒢` within `ξ ≤ ε/(4 c_* R)` of the enable-controlled
private operation on clean work wires, the selective circuit with the synthesis budget `ε/4`
(`selOf hS (ε/4)`) is valid and over `𝒢`, makes exactly `n_P` copies of the calls of the private
circuit, synthesises at most `G_known` occurrences, has at most
`n_P G_C + G_known (c₁ log((G_known+1)/(ε/4)) + c₀ + 1)` gates (`G_C = |pc|`, charged linearly), the
stated qubits, and full-output error at most `ε`. -/
theorem gate_prop_finite_sel (hS : Synthesis 𝒢 Xs L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    {a m r K : ℕ} (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (pc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J)) (hpcV : ∀ i ∈ pc, i.Valid)
    (hpcG : ∀ g, NInstr.gate g ∈ pc → GateOf 𝒢 g) {ε cR ξ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcR : 0 < cR) (hξ : 0 ≤ ξ) (hξε : ξ ≤ ε / (4 * cR))
    (D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (hD : IsUnitary D)
    (hpc : ApproxOn CleanP (nrun prim pc) (ctrlIdeal (selOp (fun _ : Cfg Empty => D))) ξ)
    (l : List (Instr (Wire a m r K))) (hv : ∀ i ∈ l, i.Valid Wire.anc)
    (hsec : ∀ i ∈ l, SecOK (wireRel a m r K) i) (hR : (nPriv l : ℝ) ≤ cR)
    (U : Reg S R →L[ℂ] Reg S R)
    (hrel : ‖run (simSem (P := Reg S R) (UJop (R := R) UJg) D) l ∘L io - io ∘L U‖ ≤ ε / 2) :
    (∀ i ∈ selOf hS (ε / 4) UJg pc l, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selOf hS (ε / 4) UJg pc l → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selOf hS (ε / 4) UJg pc l) = nPriv l * nCallsN p pc) ∧
    nSynN 𝒢 (hcircP (X' := Empty) (wireRel a m r K) (noSel _) UJg pc l) ≤
      knownG UJg.length l ∧
    (nGatesN (selOf hS (ε / 4) UJg pc l) : ℝ) ≤
      (nPriv l : ℝ) * nGatesN pc + (knownG UJg.length l : ℝ) *
        (c₁ * Real.log (((knownG UJg.length l : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    Fintype.card (HW (Wire a m r K) S Empty Z bT bP A ⊕ Xs) =
      Fintype.card (Wire a m r K) + Fintype.card S + (Fintype.card Z + bT + bP + A + 3) +
        Fintype.card Xs ∧
    ‖nrun prim (selOf hS (ε / 4) UJg pc l) ∘L
        (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L U‖ ≤ ε := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := sel_transfer hS hadj hc₀ hc₁ hL prim hprim UJg hUJg pc
    hpcV hpcG hξ D hD hpc l hv hsec U (by linarith : (0 : ℝ) < ε / 4) (by linarith) hrel
  refine ⟨h1, h2, h3, h4, h5, h6, h7.trans ?_⟩
  have hk : (nPriv l : ℝ) * ξ ≤ cR * (ε / (4 * cR)) :=
    mul_le_mul hR hξε hξ hcR.le
  have e : cR * (ε / (4 * cR)) = ε / 4 := by
    field_simp
  linarith

/-- **Proposition `gate:prop:finite` over a finite gate set from the native data**: the supplied
circuit is the native private operation compiled selectively once (`GateSelective.privSel`, budget
`η`), within `η + 4 ζ` of the enable-controlled operation; with `η + 4 ζ ≤ ε/(4 c_* R)`, the
conclusions of `gate_prop_finite_sel`, with `|privSel| ≤ nKeepN + K L(η/(K+1))`. -/
theorem gate_prop_finite_sel_native (hS : Synthesis 𝒢 Xs L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    {a m r K : ℕ} (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp Empty (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB Empty (Fin a ⊕ S) Z)) {ε cR η ζ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcR : 0 < cR) (hη : 0 < η) (hζ : 0 ≤ ζ) (hξε : η + 4 * ζ ≤ ε / (4 * cR))
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (hD : IsUnitary D)
    (hN : NativeOK prim nd (selOp (fun _ : Cfg Empty => D)))
    (l : List (Instr (Wire a m r K))) (hv : ∀ i ∈ l, i.Valid Wire.anc)
    (hsec : ∀ i ∈ l, SecOK (wireRel a m r K) i) (hR : (nPriv l : ℝ) ≤ cR)
    (U : Reg S R →L[ℂ] Reg S R)
    (hrel : ‖run (simSem (P := Reg S R) (UJop (R := R) UJg) D) l ∘L io - io ∘L U‖ ≤ ε / 2) :
    (∀ i ∈ selOf hS (ε / 4) UJg (privSel hS η nd ar) l, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selOf hS (ε / 4) UJg (privSel hS η nd ar) l → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selOf hS (ε / 4) UJg (privSel hS η nd ar) l) =
      nPriv l * (2 * nCallsN p nd.V)) ∧
    nGatesN (privSel hS η nd ar) ≤ nKeepN 𝒢 (privMacro nd ar) +
      nSynN 𝒢 (privMacro nd ar) * L (η / (nSynN 𝒢 (privMacro nd ar) + 1)) ∧
    (nGatesN (selOf hS (ε / 4) UJg (privSel hS η nd ar) l) : ℝ) ≤
      (nPriv l : ℝ) * nGatesN (privSel hS η nd ar) + (knownG UJg.length l : ℝ) *
        (c₁ * Real.log (((knownG UJg.length l : ℝ) + 1) / (ε / 4)) + c₀ + 1) ∧
    Fintype.card (HW (Wire a m r K) S Empty (Z ⊕ Xs) ar.bT ar.bP ar.A ⊕ Xs) =
      Fintype.card (Wire a m r K) + Fintype.card S +
        (Fintype.card Z + Fintype.card Xs + ar.bT + ar.bP + ar.A + 3) + Fintype.card Xs ∧
    ‖nrun prim (selOf hS (ε / 4) UJg (privSel hS η nd ar) l) ∘L
        (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L U‖ ≤ ε := by
  obtain ⟨hpV, hpG, hpg, hpc, hpa⟩ := privSel_spec (R := R) hS hη nd hnd ar hζ har
  obtain ⟨h1, h2, h3, -, h5, h6, h7⟩ := gate_prop_finite_sel hS hadj hc₀ hc₁ hL prim hprim UJg
    hUJg (privSel hS η nd ar) hpV hpG hε hε1 hcR (by positivity) hξε D hD
    (hpa prim hprim _ hN) l hv hsec hR U hrel
  refine ⟨h1, h2, fun p => by rw [h3 p, hpc p], hpg, h5, ?_, h7⟩
  rw [h6, Fintype.card_sum]

end FiniteSel

/-! ### Proposition `gate:prop:core` over a finite gate set -/

section CoreSel

variable {S Z Y J Xs : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y] [Fintype Xs] [DecidableEq Xs] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **Proposition `gate:prop:core` over a finite gate set with a supplied finite-set private
circuit.** In the regime of the clipped construction, with `U_J` given by gates `UJg` and the core
data for `D`, and a supplied private circuit over `𝒢` within `ξ` of the enable-controlled `D` on
clean work wires: the selective clipped circuit (`selOf hS δ UJg pc`) is valid and over `𝒢`, makes
exactly `6 d` copies of the calls of the private circuit, synthesises at most
`G_known ≤ 200 (d+1)(a+m+r+1) + 84 d C_J` occurrences, has at most
`6 d G_C + G_known (c₁ log((G_known+1)/δ) + c₀ + 1)` gates on
`2a + 3m + 6r + 3 + |S| + (|Z| + b_T + b_P + A + 3) + |X|` qubits, with the slot and degree bounds of
`gate_prop_core`, and its full output is within `ε + 6 d ξ + δ` of `e^{-i a J†KJ}`. -/
theorem gate_prop_core_sel [FiniteDimensional ℂ R] (hS : Synthesis 𝒢 Xs L) (hadj : AdjClosed 𝒢)
    {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (a : ℕ) {s τ ε : ℝ} (Rg : Regime s τ ε)
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (UJ D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (hb : UJop (R := R) UJg = UJ)
    (hDu : IsUnitary D) {Kb Pp Pm : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)}
    (h : Core.CoreData s τ ε Kb D Pp Pm (UJ ∘L iota0))
    (pc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J)) (hpcV : ∀ i ∈ pc, i.Valid)
    (hpcG : ∀ g, NInstr.gate g ∈ pc → GateOf 𝒢 g) {ξ δ : ℝ} (hξ : 0 ≤ ξ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1)
    (hpc : ApproxOn CleanP (nrun prim pc) (ctrlIdeal (selOp (fun _ : Cfg Empty => D))) ξ) :
    (∀ i ∈ selOf hS δ UJg pc (clipCircuit a s τ ε), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selOf hS δ UJg pc (clipCircuit a s τ ε) → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selOf hS δ UJg pc (clipCircuit a s τ ε)) =
      6 * degree s τ ε * nCallsN p pc) ∧
    nSynN 𝒢 (hcircP (X' := Empty) (wireRel _ _ _ _) (noSel _) UJg pc (clipCircuit a s τ ε)) ≤
      knownG UJg.length (clipCircuit a s τ ε) ∧
    knownG UJg.length (clipCircuit a s τ ε) ≤
      200 * (degree s τ ε + 1) * (a + clipM s τ ε + clipR s τ ε + 1) +
        84 * degree s τ ε * UJg.length ∧
    (nGatesN (selOf hS δ UJg pc (clipCircuit a s τ ε)) : ℝ) ≤
      6 * (degree s τ ε : ℝ) * nGatesN pc +
        (knownG UJg.length (clipCircuit a s τ ε) : ℝ) *
          (c₁ * Real.log (((knownG UJg.length (clipCircuit a s τ ε) : ℝ) + 1) / δ) + c₀ + 1) ∧
    Fintype.card (HW (ClipWire a s τ ε) S Empty Z bT bP A ⊕ Xs) =
      2 * a + 3 * clipM s τ ε + 6 * clipR s τ ε + 3 + Fintype.card S +
        (Fintype.card Z + bT + bP + A + 3) + Fintype.card Xs ∧
    ((2 ^ clipM s τ ε : ℕ) : ℝ) < 2 * (degree s τ ε : ℝ) ^ 2 / (5 * ε) ∧
    2 * degree s τ ε + 2 ≤ 2 ^ clipR s τ ε ∧ 2 ^ clipR s τ ε ≤ 4 * (degree s τ ε + 1) ∧
    (degree s τ ε : ℝ) ≤ 21520 * Real.sqrt (s * τ * rval τ ε) ∧
    ‖nrun prim (selOf hS δ UJg pc (clipCircuit a s τ ε)) ∘L
          (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (aval s τ ε : ℂ)) •
            ((UJ ∘L iota0)† ∘L Kb ∘L (UJ ∘L iota0)))‖ ≤
      ε + 6 * (degree s τ ε : ℝ) * ξ + δ := by
  subst hb
  have hUJu : IsUnitary (UJop (R := R) UJg) := UJop_isUnitary UJg hUJg
  obtain ⟨hv, hp, hu, hg, hc, hm, hr1, hr2, hd, he⟩ := gate_prop_core a Rg _ D hUJu hDu h
  have hsec := secOK_clipCircuit a s τ ε
  generalize clipCircuit a s τ ε = l at hv hp hu hg he hsec ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := sel_transfer hS hadj hc₀ hc₁ hL prim hprim UJg hUJg pc
    hpcV hpcG hξ D hDu hpc l hv hsec _ hδ hδ1 he
  refine ⟨h1, h2, fun p => by rw [h3 p, hp], h4, ?_, ?_, ?_, hm, hr1, hr2, hd, ?_⟩
  · unfold knownG
    rw [hu]
    have : 12 * degree s τ ε * (7 * UJg.length) = 84 * degree s τ ε * UJg.length := by ring
    omega
  · rw [hp, Nat.cast_mul, Nat.cast_ofNat] at h5
    exact h5
  · rw [h6, hc]
  · rw [hp, Nat.cast_mul, Nat.cast_ofNat] at h7
    exact h7

/-- **Proposition `gate:prop:core` over a finite gate set with the factor-conjugated native private
call compiled selectively**: the private circuit is `pcSel hS η N.pc` (the native factor, the native
rotation and the inverse native factor of `GateOptimalBinary.ClipNative`, compiled once with the
budget `η`), within `η + 6ξ + 4ζ` of the enable-controlled `D`; the conclusions of
`gate_prop_core_sel`, with error `ε + 6 d (η + 6ξ + 4ζ) + δ` and
`|pcSel| ≤ nKeepN + K L(η/(K+1))`. -/
theorem gate_prop_core_sel_native [FiniteDimensional ℂ R] (hS : Synthesis 𝒢 Xs L)
    (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (a : ℕ) {s τ ε : ℝ} (Rg : Regime s τ ε)
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJ D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (hDu : IsUnitary D)
    {Kb Pp Pm : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)}
    (h : Core.CoreData s τ ε Kb D Pp Pm (UJ ∘L iota0)) {ξ ζ η δ : ℝ} (hξ : 0 ≤ ξ) (hζ : 0 ≤ ζ)
    (hη : 0 < η) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (N : GateOptimalBinary.ClipNative prim UJ D Z bT bP A ξ ζ) :
    (∀ i ∈ selOf hS δ N.UJg (pcSel hS η N.pc) (clipCircuit a s τ ε), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selOf hS δ N.UJg (pcSel hS η N.pc) (clipCircuit a s τ ε) →
      GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selOf hS δ N.UJg (pcSel hS η N.pc) (clipCircuit a s τ ε)) =
      6 * degree s τ ε * N.calls p) ∧
    nGatesN (pcSel hS η N.pc) ≤ nKeepN 𝒢 N.pc + nSynN 𝒢 N.pc * L (η / (nSynN 𝒢 N.pc + 1)) ∧
    knownG N.UJg.length (clipCircuit a s τ ε) ≤
      200 * (degree s τ ε + 1) * (a + clipM s τ ε + clipR s τ ε + 1) +
        84 * degree s τ ε * N.UJg.length ∧
    (nGatesN (selOf hS δ N.UJg (pcSel hS η N.pc) (clipCircuit a s τ ε)) : ℝ) ≤
      6 * (degree s τ ε : ℝ) * nGatesN (pcSel hS η N.pc) +
        (knownG N.UJg.length (clipCircuit a s τ ε) : ℝ) *
          (c₁ * Real.log (((knownG N.UJg.length (clipCircuit a s τ ε) : ℝ) + 1) / δ) + c₀ + 1) ∧
    Fintype.card (HW (ClipWire a s τ ε) S Empty (Z ⊕ Xs) bT bP A ⊕ Xs) =
      2 * a + 3 * clipM s τ ε + 6 * clipR s τ ε + 3 + Fintype.card S +
        (Fintype.card Z + Fintype.card Xs + bT + bP + A + 3) + Fintype.card Xs ∧
    ((2 ^ clipM s τ ε : ℕ) : ℝ) < 2 * (degree s τ ε : ℝ) ^ 2 / (5 * ε) ∧
    2 * degree s τ ε + 2 ≤ 2 ^ clipR s τ ε ∧ 2 ^ clipR s τ ε ≤ 4 * (degree s τ ε + 1) ∧
    (degree s τ ε : ℝ) ≤ 21520 * Real.sqrt (s * τ * rval τ ε) ∧
    ‖nrun prim (selOf hS δ N.UJg (pcSel hS η N.pc) (clipCircuit a s τ ε)) ∘L
          (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (aval s τ ε : ℂ)) •
            ((UJ ∘L iota0)† ∘L Kb ∘L (UJ ∘L iota0)))‖ ≤
      ε + 6 * (degree s τ ε : ℝ) * (η + (6 * ξ + 4 * ζ)) + δ := by
  obtain ⟨hpV, hpG, hpg, hpc, hpa⟩ := pcSel_spec (R := R) (Xs := Xs) (𝒢 := 𝒢) hS hη N.pc N.pc_valid
  have hξ' : 0 ≤ 6 * ξ + 4 * ζ := by positivity
  have hpcA := hpa prim hprim _ hξ' (N.pc_approx hprim hξ hζ)
  have hb := N.boundary
  have hUJu : IsUnitary UJ := hb ▸ UJop_isUnitary N.UJg N.ok
  obtain ⟨hv, hp, hu, hg, hc, hm, hr1, hr2, hd, he⟩ := gate_prop_core a Rg UJ D hUJu hDu h
  have hsec := secOK_clipCircuit a s τ ε
  rw [← hb] at he
  -- an opaque circuit keeps the unifier from unfolding `clipCircuit`
  generalize clipCircuit a s τ ε = l at hv hp hu hg he hsec ⊢
  obtain ⟨h1, h2, h3, -, h5, h6, h7⟩ := sel_transfer hS hadj hc₀ hc₁ hL prim hprim N.UJg N.ok
    (pcSel hS η N.pc) hpV hpG (by positivity) D hDu hpcA l hv hsec _ hδ hδ1 he
  refine ⟨h1, h2, fun p => by rw [h3 p, hpc p, hp]; rfl, hpg, ?_, ?_, ?_, hm, hr1, hr2, hd, ?_⟩
  · unfold knownG
    rw [hu]
    have : 12 * degree s τ ε * (7 * N.UJg.length) = 84 * degree s τ ε * N.UJg.length := by ring
    omega
  · rw [hp, Nat.cast_mul, Nat.cast_ofNat] at h5
    exact h5
  · rw [h6, hc, Fintype.card_sum]
  · rw [hp, Nat.cast_mul, Nat.cast_ofNat, hb] at h7
    exact h7

end CoreSel

/-! ### The signed regime: a supplied circuit for the unconditional factor -/

section UncInverse

variable {PR Z Y J : Type*} [Fintype PR] [DecidableEq PR] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The literal inverse of a supplied unconditional factor circuit implements the inverse**: if a
valid circuit is within `ξ` of the unconditional factor `U_B` on clean work wires, its
reverse-adjoint is within `ξ` of `U_B†`. -/
theorem unc_inv_approx (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (C : List (NInstr (PWr Empty PR Z bT bP A) Y J)) (hC : ∀ i ∈ C, i.Valid)
    (Usel : Reg (Empty ⊕ PR) R →L[ℂ] Reg (Empty ⊕ PR) R) (hU : IsUnitary Usel) {ξ : ℝ}
    (h : ApproxOn CleanP (nrun prim C) (uncIdeal Usel) ξ) :
    ApproxOn CleanP (nrun prim (ninv C))
      (uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) (Usel†)) ξ := by
  rw [nrun_ninv, ← uncIdeal_adjoint]
  have hCu : IsUnitary (nrun prim C) := nrun_isUnitary prim hprim _ hC
  have hO : IsUnitary (uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) Usel) :=
    localOp_isUnitary _ _ (fun _ => hU)
  have hOs : Preserves CleanP ((uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) Usel)†) := by
    rw [uncIdeal_adjoint]
    unfold uncIdeal
    apply preserves_localOp
    intro y b hy
    constructor
    · intro z
      rw [overwrite_apply_out _ y b _ (fun p hp => by simp [selPR] at hp)]
      exact hy.1 z
    · intro w
      rw [overwrite_apply_out _ y b _ (fun p hp => by simp [selPR] at hp)]
      exact hy.2 w
  exact h.adjoint hCu hO hOs

variable {Xs : Type*} [Fintype Xs] [DecidableEq Xs] {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- The lifted unconditional factor, joined, is the unconditional factor of the joined register. -/
theorem localOp_rePW_liftB_uncIdeal (Usel : Reg (Empty ⊕ PR) R →L[ℂ] Reg (Empty ⊕ PR) R) :
    localOp (rePW (X := Xs)) rePW.injective
        (fun _ => liftB (X := Xs) (uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) Usel)) =
      uncIdeal (Z := Z ⊕ Xs) (bT := bT) (bP := bP) (A := A) Usel := by
  have h1 : liftB (X := Xs) (uncIdeal (Z := Z) (bT := bT) (bP := bP) (A := A) Usel) =
      localOp ((Sum.inl : PWr Empty PR Z bT bP A → PWr Empty PR Z bT bP A ⊕ Xs) ∘ selPR)
        (Sum.inl_injective.comp selPR.injective) (fun _ => Usel) := by
    unfold liftB uncIdeal
    exact GateODE.localOp_localOp Sum.inl_injective selPR.injective (fun _ _ => Usel)
  rw [h1]
  exact GateODE.localOp_localOp' (rePW (X := Xs)).injective
    (Sum.inl_injective.comp (selPR (Sel := Empty) (PR := PR) (Z := Z) (bT := bT) (bP := bP)
      (A := A)).injective) (selPR (Z := Z ⊕ Xs) (bT := bT) (bP := bP) (A := A))
    (selPR (Z := Z ⊕ Xs) (bT := bT) (bP := bP) (A := A)).injective (fun b => rfl)
    (fun _ _ => Usel)

/-- **A factor circuit compiled selectively once**: within `η + ξ` of the unconditional factor on
clean work wires when the supplied circuit is within `ξ` (the analogue of `pcSel_spec`). -/
theorem pcSel_unc (hS : Synthesis 𝒢 Xs L) {η : ℝ} (hη : 0 < η)
    (fc : List (NInstr (PWr Empty PR Z bT bP A) Y J)) (hfcV : ∀ i ∈ fc, i.Valid)
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (Usel : Reg (Empty ⊕ PR) R →L[ℂ] Reg (Empty ⊕ PR) R) {ξ : ℝ} (hξ : 0 ≤ ξ)
    (hfc : ApproxOn CleanP (nrun prim fc) (uncIdeal Usel) ξ) :
    ApproxOn CleanP (nrun prim (pcSel hS η fc)) (uncIdeal Usel) (η + ξ) := by
  have h1 := selBudget_approxOn prim hS hη _ hfcV hprim
  have h2 : ApproxOn (fun y : Cfg (PWr Empty PR Z bT bP A ⊕ Xs) =>
      CleanP (fun p => y (Sum.inl p)))
      (localOp Sum.inl Sum.inl_injective (fun _ => nrun prim fc))
      (localOp Sum.inl Sum.inl_injective (fun _ => uncIdeal Usel)) ξ :=
    approxOn_localOp Sum.inl_injective _ _ hξ (SA := CleanP) (fun y hy => hy) (fun _ => hfc)
  have h3 : ApproxOn (fun y : Cfg (PWr Empty PR Z bT bP A ⊕ Xs) =>
      CleanP (fun p => y (Sum.inl p)) ∧ CleanX y)
      (nrun prim (selBudget hS η fc))
      (liftB (X := Xs) (uncIdeal Usel)) (η + ξ) :=
    approxOn_trans (approxOn_restrict h1 (fun y hy => hy.2))
      (approxOn_restrict h2 (fun y hy => hy.1))
  unfold pcSel
  rw [nrun_map, ← localOp_rePW_liftB_uncIdeal]
  refine approxOn_localOp rePW.injective _ _ (by linarith)
    (SA := fun y : Cfg (PWr Empty PR Z bT bP A ⊕ Xs) =>
      CleanP (fun p => y (Sum.inl p)) ∧ CleanX y) ?_ (fun _ => h3)
  intro y hy
  exact ⟨⟨fun z => hy.1 (Sum.inl z), fun w => hy.2 w⟩, fun x => hy.1 (Sum.inr x)⟩

end UncInverse

section UncMacro

variable {V S X' Z Y J : Type*} {a bT bP A : ℕ}
variable [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S] [Fintype X'] [DecidableEq X']
  [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **Every macro with a supplied factor circuit implements its released instruction of the signed
form** (factor calls unconditional): exactly, except a factor call, which is within `ξ`. -/
theorem hmacroP_unc_approx (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S))) (hUJ : ∀ g ∈ UJg, GateOK 3 g)
    (fc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J)) (hfcV : ∀ i ∈ fc, i.Valid)
    (U : Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)) (hU : IsUnitary U) {ξ : ℝ}
    (hξ : 0 ≤ ξ)
    (hfc : ApproxOn CleanP (nrun prim fc) (uncIdeal (selOp (fun _ : Cfg Empty => U))) ξ)
    (i : Instr V) :
    ApproxOn CleanX (nrun prim (hmacroP (X' := X') ρ (noSel ρ) UJg fc i))
      (liftB (conj (evalF ρ UJg U i))) (if i.isPriv then ξ else 0) := by
  cases i with
  | gate g =>
      apply ApproxOn.of_agrees
      have e1 : nrun prim (hmacroP (X' := X') ρ (noSel ρ) UJg fc (Instr.gate g)) =
          gateOp ((g.cs.map (fun c => (Sum.inl c.1, c.2))).map (fun c => (Sum.inl c.1, c.2)))
            (Sum.inl (Sum.inl g.t)) g.u := by
        simp only [hmacroP, nrun_singleton, NInstr.eval_gate, GateODE.Gate.map, List.map_map]
        rfl
      have e2 : liftB (X := XW Z bT bP A ⊕ X') (conj (evalF (R := R) ρ UJg U (Instr.gate g))) =
          gateOp ((g.cs.map (fun c => (Sum.inl c.1, c.2))).map (fun c => (Sum.inl c.1, c.2)))
            (Sum.inl (Sum.inl g.t)) g.u := by
        simp only [evalF]
        rw [conj_gateOp]
        exact localOp_gateOp Sum.inl_injective _ _ _
      rw [e1, e2]
      exact Agrees.refl _ _
  | uj cs adj =>
      apply ApproxOn.of_agrees
      set gs := if adj then gInv UJg else UJg with hgs
      have hgsok : ∀ g ∈ gs, GateOK 3 g := by
        rw [hgs]; split_ifs
        · exact gInv_ok _ hUJ
        · exact hUJ
      have hconj : conj (if adj then (UJop (R := R) UJg)† else UJop UJg) = gRun gs := by
        rw [hgs]
        split_ifs
        · rw [UJop_adjoint, conj_unfl_fl]
        · exact conj_unfl_fl _
      have e2 : liftB (X := XW Z bT bP A ⊕ X') (conj (evalF (R := R) ρ UJg U (Instr.uj cs adj))) =
          gRun (gs.map (ctrlMap (secW ρ) (fun p => (Sum.inl (mapId (S := S) ρ.anc p) :
            HW V S X' Z bT bP A)))) := by
        simp only [evalF]
        rw [liftB_conj_selOracle_canon]
        simp only [hconj]
        exact localOp_ctrl_gRun _ (secW ρ) (fun p => pEmb_ne_secW ρ p) gs
          (fun g hg => (hgsok g hg).2.1)
      have e1 : nrun prim (hmacroP (X' := X') ρ (noSel ρ) UJg fc (Instr.uj cs adj)) =
          gRun (ujGates ρ gs) := by
        simp only [hmacroP]
        rw [nrun_nGatesOf]
      rw [e1, e2]
      exact ujGates_agrees ρ gs hgsok
  | priv cs adj =>
      simp only [Instr.isPriv, if_true]
      have e1 : nrun prim (hmacroP (X' := X') ρ (noSel ρ) UJg fc (Instr.priv cs adj)) =
          localOp (ePW ρ (noSel ρ)) (ePW ρ (noSel ρ)).injective
            (fun _ => nrun prim (if adj then ninv fc else fc)) := by
        simp only [hmacroP]
        exact nrun_map prim (ePW ρ (noSel ρ)) _
      simp only [evalF]
      rw [e1, liftB_conj_unc]
      apply approxOn_localOp _ _ _ hξ (SA := CleanP)
        (fun y hy => ⟨fun z => hy (Sum.inl (Sum.inl z)),
          fun w => hy (Sum.inl (Sum.inr (Sum.inl w)))⟩)
      intro _
      cases adj
      · exact hfc
      · have h := unc_inv_approx prim hprim fc hfcV _ (selOp_isUnitary _ (fun _ => hU)) hfc
        have hadj : (selOp (fun _ : Cfg Empty => U))† = selOp (fun _ : Cfg Empty => U†) := by
          rw [selOp_adjoint]
        rw [hadj] at h
        exact h

/-- **The signed circuit with a supplied factor circuit approximates the lifted released
circuit**: the errors `ξ` of the factor calls add. -/
theorem hcircP_unc_approx (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S))) (hUJ : ∀ g ∈ UJg, GateOK 3 g)
    (fc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J)) (hfcV : ∀ i ∈ fc, i.Valid)
    (U : Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)) (hU : IsUnitary U) {ξ : ℝ}
    (hξ : 0 ≤ ξ)
    (hfc : ApproxOn CleanP (nrun prim fc) (uncIdeal (selOp (fun _ : Cfg Empty => U))) ξ)
    (l : List (Instr V)) (hv : ∀ i ∈ l, i.Valid ρ.anc) :
    ApproxOn CleanX (nrun prim (hcircP (X' := X') ρ (noSel ρ) UJg fc l))
      (liftB (conj (prodOps (evalF ρ UJg U) l))) ((nPriv l : ℝ) * ξ) := by
  have h := approxOn_flatMap prim CleanX (hmacroP (X' := X') ρ (noSel ρ) UJg fc)
    (fun i => liftB (X := XW Z bT bP A ⊕ X') (conj (evalF ρ UJg U i)))
    (fun i => if i.isPriv then ξ else 0) l
    (fun i _ => hmacroP_unc_approx prim hprim ρ UJg hUJ fc hfcV U hU hξ hfc i)
    (fun i _ => preserves_liftB _)
    (fun i hi ψ => IsUnitary.norm_apply_le
      (liftB_isUnitary (conj_isUnitary (evalF_isUnitary ρ UJg hUJ U hU i (hv i hi)))) ψ)
    (fun i hi ψ => IsUnitary.norm_apply_le (nrun_isUnitary prim hprim _
      (hmacroP_valid ρ (noSel ρ) UJg hUJ fc hfcV i (hv i hi))) ψ)
    (fun i _ => by split_ifs <;> linarith)
  rw [sum_priv_real, prodOps_liftB_conj] at h
  exact h

/-- **The full-output error of the signed circuit with a supplied factor circuit**: within
`ε₀ + n_P ξ` of the target on the system embedding when the released circuit is within `ε₀`. -/
theorem hcircP_unc_error (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S))) (hUJ : ∀ g ∈ UJg, GateOK 3 g)
    (fc : List (NInstr (PWr Empty (Fin a ⊕ S) Z bT bP A) Y J)) (hfcV : ∀ i ∈ fc, i.Valid)
    (U : Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)) (hU : IsUnitary U) {ξ : ℝ}
    (hξ : 0 ≤ ξ)
    (hfc : ApproxOn CleanP (nrun prim fc) (uncIdeal (selOp (fun _ : Cfg Empty => U))) ξ)
    (l : List (Instr V)) (hv : ∀ i ∈ l, i.Valid ρ.anc)
    (ι : Reg S R →L[ℂ] Reg V (Reg S R)) (hι : ∀ ψ, ‖ι ψ‖ = ‖ψ‖)
    (T : Reg S R →L[ℂ] Reg S R) (Orel : Reg V (Reg S R) →L[ℂ] Reg V (Reg S R))
    (hO : prodOps (V := V) (R := Reg S R) (evalF ρ UJg U) l = Orel) {ε₀ : ℝ}
    (hrel : ‖Orel ∘L ι - ι ∘L T‖ ≤ ε₀) :
    ‖nrun prim (hcircP (X' := X') ρ (noSel ρ) UJg fc l) ∘L sysEmb ι - sysEmb ι ∘L T‖ ≤
      ε₀ + (nPriv l : ℝ) * ξ := by
  have hA := hcircP_unc_approx (X' := X') prim hprim ρ UJg hUJ fc hfcV U hU hξ hfc l hv
  rw [hO] at hA
  have hε₀ : 0 ≤ ε₀ := le_trans (norm_nonneg (Orel ∘L ι - ι ∘L T)) hrel
  have hδ : 0 ≤ (nPriv l : ℝ) * ξ := by positivity
  apply ContinuousLinearMap.opNorm_le_bound _ (by linarith)
  intro ψ
  set C := nrun prim (hcircP (X' := X') ρ (noSel ρ) UJg fc l) with hC
  set φ : Reg (V ⊕ S) R := fl (ι ψ) with hφ
  have e1 : (C ∘L sysEmb ι - sysEmb ι ∘L T :
      Reg S R →L[ℂ] Reg (HW V S X' Z bT bP A) R) ψ =
      (C (cleanEmb φ) - liftB (X := XW Z bT bP A ⊕ X') (conj Orel) (cleanEmb φ)) +
        cleanEmb (fl ((Orel ∘L ι - ι ∘L T) ψ)) := by
    have h1 : liftB (X := XW Z bT bP A ⊕ X') (conj Orel) (cleanEmb φ) =
        cleanEmb (conj Orel φ) := by
      rw [← comp_apply, liftB_cleanEmb, comp_apply]
    rw [h1, hφ, conj_fl]
    simp only [sysEmb, sub_apply, comp_apply, map_sub]
    abel
  have hφn : ‖φ‖ = ‖ψ‖ := by rw [hφ, norm_fl, hι]
  rw [e1]
  calc ‖C (cleanEmb φ) - liftB (X := XW Z bT bP A ⊕ X') (conj Orel) (cleanEmb φ) +
        cleanEmb (fl ((Orel ∘L ι - ι ∘L T) ψ))‖
      ≤ ‖C (cleanEmb φ) - liftB (X := XW Z bT bP A ⊕ X') (conj Orel) (cleanEmb φ)‖ +
        ‖cleanEmb (X := XW Z bT bP A ⊕ X') (fl ((Orel ∘L ι - ι ∘L T) ψ))‖ :=
        norm_add_le _ _
    _ ≤ (nPriv l : ℝ) * ξ * ‖ψ‖ + ε₀ * ‖ψ‖ := by
        gcongr
        · have := hA _ (supp_cleanEmb φ)
          rwa [norm_cleanEmb, hφn] at this
        · rw [norm_cleanEmb, norm_fl]
          exact ((Orel ∘L ι - ι ∘L T).le_opNorm ψ).trans
            (mul_le_mul_of_nonneg_right hrel (norm_nonneg _))
    _ = (ε₀ + (nPriv l : ℝ) * ξ) * ‖ψ‖ := by ring

end UncMacro

/-! ### Proposition `gate:prop:signed` over a finite gate set -/

section SignedSel

variable {S Z Y J Xs : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y] [Fintype Xs] [DecidableEq Xs] {bT bP A : ℕ}
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable {𝒢 : Set Kind} {L : ℝ → ℕ}

/-- **The selective finite-set circuit of a released signed circuit with a supplied factor
circuit**: on `a + 1` ancillas, `U_J` from its gates on the last `a` of them (`shiftG`), every factor
call replaced by the supplied circuit (its inverse by the literal reverse-adjoint), the remaining
exact gates synthesised with the budget `δ`. -/
abbrev selSgOf (hS : Synthesis 𝒢 Xs L) (δ : ℝ) {a m r K : ℕ} (UJg : List (Gate (Fin a ⊕ S)))
    (fc : List (NInstr (PWr Empty (Fin (a + 1) ⊕ S) Z bT bP A) Y J))
    (l : List (Instr (Wire (a + 1) m r K))) :
    List (NInstr (HW (Wire (a + 1) m r K) S Empty Z bT bP A ⊕ Xs) Y J) :=
  selBudget hS δ (hcircP (X' := Empty) (wireRel (a + 1) m r K) (noSel _) (shiftG UJg) fc l)

/-- **The finite-set transfer for unconditional factor calls with a supplied factor circuit.** For
a valid released circuit of the signed form (`UncOK`) whose full output, run with `U_J ⊗ I_flag` and
`U_B ⊗ I_flag`, is within `ε₀` of `T`, and a valid supplied factor circuit over `𝒢` within `ξ` of the
unconditional `U_B ⊗ I_flag` on clean work wires: the conclusions of `sel_transfer`, with error
`ε₀ + n_P ξ + δ`. -/
theorem sel_signed_transfer (hS : Synthesis 𝒢 Xs L) (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ}
    (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    {a m r K : ℕ} (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (UJ U : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (hJ : UJop (R := R) UJg = UJ)
    (hU : IsUnitary U) (fc : List (NInstr (PWr Empty (Fin (a + 1) ⊕ S) Z bT bP A) Y J))
    (hfcV : ∀ i ∈ fc, i.Valid) (hfcG : ∀ g, NInstr.gate g ∈ fc → GateOf 𝒢 g) {ξ : ℝ}
    (hξ : 0 ≤ ξ)
    (hfc : ApproxOn CleanP (nrun prim fc) (uncIdeal (selOp (fun _ : Cfg Empty => liftA U))) ξ)
    (l : List (Instr (Wire (a + 1) m r K))) (hv : ∀ i ∈ l, i.Valid Wire.anc)
    (hunc : ∀ i ∈ l, UncOK (wireRel _ _ _ _) i) (T : Reg S R →L[ℂ] Reg S R) {ε₀ δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hrel : ‖run (simSem (P := Reg S R) (liftA UJ) (liftA U)) l ∘L io - io ∘L T‖ ≤ ε₀) :
    (∀ i ∈ selSgOf hS δ UJg fc l, i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selSgOf hS δ UJg fc l → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selSgOf hS δ UJg fc l) = nPriv l * nCallsN p fc) ∧
    nSynN 𝒢 (hcircP (X' := Empty) (wireRel (a + 1) m r K) (noSel _) (shiftG UJg) fc l) ≤
      knownG UJg.length l ∧
    (nGatesN (selSgOf hS δ UJg fc l) : ℝ) ≤
      (nPriv l : ℝ) * nGatesN fc + (knownG UJg.length l : ℝ) *
        (c₁ * Real.log (((knownG UJg.length l : ℝ) + 1) / δ) + c₀ + 1) ∧
    Fintype.card (HW (Wire (a + 1) m r K) S Empty Z bT bP A ⊕ Xs) =
      Fintype.card (Wire (a + 1) m r K) + Fintype.card S + (Fintype.card Z + bT + bP + A + 3) +
        Fintype.card Xs ∧
    ‖nrun prim (selSgOf hS δ UJg fc l) ∘L (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L T‖ ≤ ε₀ + (nPriv l : ℝ) * ξ + δ := by
  have hvN := hcircP_valid (X' := Empty) (wireRel (a + 1) m r K) (noSel _) (shiftG UJg)
    (shiftG_ok hUJg) fc hfcV l hv
  obtain ⟨hv', hk, -, hc⟩ := selBudget_spec hS hδ _ hvN
  have h0 := hcircP_nil_nGates (X' := Empty) (Z := Z) (bT := bT) (bP := bP) (A := A) (Y := Y)
    (J := J) (wireRel (a + 1) m r K) (noSel _) (shiftG UJg) (shiftG_ok hUJg) l
  rw [mul_one, shiftG_length] at h0
  have hsyn : nSynN 𝒢 (hcircP (X' := Empty) (wireRel (a + 1) m r K) (noSel _) (shiftG UJg) fc l) ≤
      knownG UJg.length l :=
    (nSynN_hcircP_le 𝒢 hadj _ _ (shiftG UJg) fc hfcG l).trans h0
  refine ⟨hv', hk, fun p => (hc p).trans (hcircP_nCalls p _ _ (shiftG UJg) fc l), hsyn, ?_, ?_,
    ?_⟩
  · have h1 := selBudget_gates_log hS hc₀ hc₁ hL hδ hδ1 _ hvN (knownG UJg.length l : ℝ)
      (by exact_mod_cast hsyn)
    have hNk : (nKeepN 𝒢 (hcircP (X' := Empty) (wireRel (a + 1) m r K) (noSel _) (shiftG UJg)
        fc l) : ℝ) ≤ (nPriv l : ℝ) * nGatesN fc + (knownG UJg.length l : ℝ) := by
      have h2 : nKeepN 𝒢 (hcircP (X' := Empty) (wireRel (a + 1) m r K) (noSel _) (shiftG UJg)
          fc l) ≤ nPriv l * nGatesN fc + knownG UJg.length l := by
        have := nKeepN_le 𝒢 (hcircP (X' := Empty) (wireRel (a + 1) m r K) (noSel _)
          (shiftG UJg) fc l)
        rw [hcircP_nGates] at this
        unfold knownG
        omega
      exact_mod_cast h2
    exact sel_count_arith hNk h1
  · rw [Fintype.card_sum, card_HW]
    simp only [Fintype.card_empty, add_zero]
  · have hO : prodOps (V := Wire (a + 1) m r K) (R := Reg S R)
        (evalF (wireRel _ _ _ _) (shiftG UJg) (liftA U)) l =
        run (simSem (P := Reg S R) (liftA UJ) (liftA U)) l := by
      rw [prodOps_evalF _ _ _ hunc, UJop_shiftG, hJ]
    have hio : ∀ ψ : Reg S R,
        ‖(io (P := Reg S R) (a := a + 1) (m := m) (r := r) (K := K)) ψ‖ = ‖ψ‖ :=
      fun ψ => by rw [io_apply, norm_bas]
    have herr := hcircP_unc_error (X' := Empty) prim hprim (wireRel _ _ _ _) (shiftG UJg)
      (shiftG_ok hUJg) fc hfcV (liftA U) (liftA_isUnitary hU) hξ hfc l hv io hio T _ hO hrel
    refine (selBudget_error_of hS hδ _ hvN prim hprim _ ?_ T herr).trans le_rfl
    intro ψ
    exact (norm_sysEmb _ (fun φ => by rw [io_apply, norm_bas]) ψ).le

/-- **Proposition `gate:prop:signed` over a finite gate set with a supplied finite-set factor
circuit.** Under the hypotheses of `GateOptimalPrecision.signed_gate_simulation` (the success
projection and the sign reflection on designated flag qubits `f ≠ z`, `wKnown`), with `U_J` from
its gates and a supplied factor circuit over `𝒢` within `ξ` of `U_B ⊗ I_flag` on clean work wires:
the selective signed circuit (`selSgOf hS δ`) is valid and over `𝒢`, makes exactly `n_P` copies of
the calls of the factor circuit, with `n_P` bounded as in `signed_gate_simulation`, synthesises at
most `G_known ≤ 64·3⁸ (N+1)(a+m+r+1) + 7 n_P C_J` occurrences, has at most
`n_P G_F + G_known (c₁ log((G_known+1)/δ) + c₀ + 1)` gates (`G_F = |fc|`, charged linearly) on
`2a + 3m + 6r + 5 + |S| + (|Z| + b_T + b_P + A + 3) + |X|` qubits, and its full output is within
`ε + n_P ξ + δ` of `exp(-itH)`. -/
theorem gate_prop_signed_sel [FiniteDimensional ℂ R] (hS : Synthesis 𝒢 Xs L)
    (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀) {a : ℕ}
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (UJ U : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (hJ : UJop (R := R) UJg = UJ)
    (hUJ : IsUnitary UJ) (hU : IsUnitary U)
    (fc : List (NInstr (PWr Empty (Fin (a + 1) ⊕ S) Z bT bP A) Y J))
    (hfcV : ∀ i ∈ fc, i.Valid) (hfcG : ∀ g, NInstr.gate g ∈ fc → GateOf 𝒢 g) {ξ : ℝ}
    (hξ : 0 ≤ ξ)
    (hfc : ApproxOn CleanP (nrun prim fc) (uncIdeal (selOp (fun _ : Cfg Empty => liftA U))) ξ)
    {f z : Fin a} (hfz : f ≠ z) {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : (wKnown UJ (unitary_adj_comp hUJ) f z).Dop U ≤ (δ : ℂ) • (1 : Reg S R →L[ℂ] Reg S R))
    (t : ℝ) {ε δs : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (hδs : 0 < δs) (hδs1 : δs ≤ 1) :
    (∀ i ∈ selSgOf hS δs UJg fc (sgCircuit a f z lam δ t ε), i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selSgOf hS δs UJg fc (sgCircuit a f z lam δ t ε) → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selSgOf hS δs UJg fc (sgCircuit a f z lam δ t ε)) =
      nPriv (sgCircuit a f z lam δ t ε) * nCallsN p fc) ∧
    ((nPriv (sgCircuit a f z lam δ t ε) : ℝ) ≤ (if sgB lam δ t ≤ ε then 0 else
      4 * 10 ^ 10 * (Real.sqrt (sgT lam t * sgB lam δ t) +
        Real.sqrt (sgT lam t * rb (sgB lam δ t) ε) + rb (sgB lam δ t) ε))) ∧
    knownG UJg.length (sgCircuit a f z lam δ t ε) ≤
      64 * 3 ^ 8 * ((sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) + 1) *
        (a + sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε + sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) +
          1)) + nPriv (sgCircuit a f z lam δ t ε) * (7 * UJg.length) ∧
    (nGatesN (selSgOf hS δs UJg fc (sgCircuit a f z lam δ t ε)) : ℝ) ≤
      (nPriv (sgCircuit a f z lam δ t ε) : ℝ) * nGatesN fc +
        (knownG UJg.length (sgCircuit a f z lam δ t ε) : ℝ) *
          (c₁ * Real.log (((knownG UJg.length (sgCircuit a f z lam δ t ε) : ℝ) + 1) / δs) +
            c₀ + 1) ∧
    Fintype.card (HW (SgWire a lam δ t ε) S Empty Z bT bP A ⊕ Xs) =
      2 * a + 3 * sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε +
        6 * sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) + 5 + Fintype.card S +
          (Fintype.card Z + bT + bP + A + 3) + Fintype.card Xs ∧
    ‖nrun prim (selSgOf hS δs UJg fc (sgCircuit a f z lam δ t ε)) ∘L
        (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • sgHam (P := Reg S R) UJ hUJ f z lam U)‖ ≤
      ε + (nPriv (sgCircuit a f z lam δ t ε) : ℝ) * ξ + δs := by
  obtain ⟨hv, hpriv, hJn, hgates, hcard, herr, -, -⟩ :=
    signed_gate_simulation (P := Reg S R) UJ U hUJ hU hfz hlam hδ hδ1 hD t hε hε1
  have hunc := uncOK_sgCircuit a f z lam δ t ε
  refine ⟨?_, ?_, ?_, hpriv, ?_, ?_, ?_, ?_⟩ <;>
  · generalize sgCircuit a f z lam δ t ε = l at hv hJn hgates herr hunc ⊢
    obtain ⟨h1, h2, h3, -, h5, h6, h7⟩ := sel_signed_transfer hS hadj hc₀ hc₁ hL prim hprim UJg
      hUJg UJ U hJ hU fc hfcV hfcG hξ hfc l hv hunc _ hδs hδs1 herr
    first
      | exact h1
      | exact h2
      | exact h3
      | exact h5
      | exact h7
      | (rw [h6, hcard])
      | (unfold knownG; rw [hJn]; omega)

/-- **Proposition `gate:prop:signed` over a finite gate set from the native factor**: the supplied
factor circuit is the native factor (`GateOptimalPrecision.factorMacro`: compute, arithmetic, local
factor gates, inverse arithmetic, uncompute, with `FactorNativeOK` and `FactorArithOK` as in
`signed_native_simulation`) compiled selectively once (`pcSel`, budget `η`), within `η + 3ξ` of
`U_B ⊗ I_flag`; the conclusions of `gate_prop_signed_sel`, with `2 n_P |W|_calls` primitive calls,
`|pcSel| ≤ nKeepN + K L(η/(K+1))` and error `ε + n_P (η + 3ξ) + δ`. -/
theorem gate_prop_signed_sel_native [FiniteDimensional ℂ R] (hS : Synthesis 𝒢 Xs L)
    (hadj : AdjClosed 𝒢) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀) {a : ℕ}
    (prim : J → Reg Y R →L[ℂ] Reg Y R) (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (UJ U : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (hJ : UJop (R := R) UJg = UJ)
    (hUJ : IsUnitary UJ) (hU : IsUnitary U) (fo : FactorOp (Fin (a + 1) ⊕ S) Z Y J bT bP A)
    (hpub : fo.Public) {ξ η : ℝ} (hξ : 0 ≤ ξ) (hη : 0 < η) (har : FactorArithOK fo ξ)
    (hN : FactorNativeOK prim fo (selOp (fun _ : Cfg Empty => liftA U)))
    {f z : Fin a} (hfz : f ≠ z) {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hD : (wKnown UJ (unitary_adj_comp hUJ) f z).Dop U ≤ (δ : ℂ) • (1 : Reg S R →L[ℂ] Reg S R))
    (t : ℝ) {ε δs : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 64) (hδs : 0 < δs) (hδs1 : δs ≤ 1) :
    (∀ i ∈ selSgOf hS δs UJg (pcSel hS η (factorMacro fo)) (sgCircuit a f z lam δ t ε),
      i.Valid) ∧
    (∀ g, NInstr.gate g ∈ selSgOf hS δs UJg (pcSel hS η (factorMacro fo))
      (sgCircuit a f z lam δ t ε) → GateOf 𝒢 g) ∧
    (∀ p : J → Bool, nCallsN p (selSgOf hS δs UJg (pcSel hS η (factorMacro fo))
        (sgCircuit a f z lam δ t ε)) =
      nPriv (sgCircuit a f z lam δ t ε) * (2 * nCallsN p fo.W)) ∧
    ((nPriv (sgCircuit a f z lam δ t ε) : ℝ) ≤ (if sgB lam δ t ≤ ε then 0 else
      4 * 10 ^ 10 * (Real.sqrt (sgT lam t * sgB lam δ t) +
        Real.sqrt (sgT lam t * rb (sgB lam δ t) ε) + rb (sgB lam δ t) ε))) ∧
    nGatesN (pcSel hS η (factorMacro fo)) ≤ nKeepN 𝒢 (factorMacro fo) +
      nSynN 𝒢 (factorMacro fo) * L (η / (nSynN 𝒢 (factorMacro fo) + 1)) ∧
    nKeepN 𝒢 (factorMacro fo) + nSynN 𝒢 (factorMacro fo) =
      2 * nGatesN fo.W + 2 * fo.circ.length + (2 * bP + bT + 4) ∧
    knownG UJg.length (sgCircuit a f z lam δ t ε) ≤
      64 * 3 ^ 8 * ((sigN (sgQ lam δ t ε) (sgOrd lam δ t ε) + 1) *
        (a + sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε + sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) +
          1)) + nPriv (sgCircuit a f z lam δ t ε) * (7 * UJg.length) ∧
    (nGatesN (selSgOf hS δs UJg (pcSel hS η (factorMacro fo)) (sgCircuit a f z lam δ t ε)) :
        ℝ) ≤
      (nPriv (sgCircuit a f z lam δ t ε) : ℝ) * nGatesN (pcSel hS η (factorMacro fo)) +
        (knownG UJg.length (sgCircuit a f z lam δ t ε) : ℝ) *
          (c₁ * Real.log (((knownG UJg.length (sgCircuit a f z lam δ t ε) : ℝ) + 1) / δs) +
            c₀ + 1) ∧
    Fintype.card (HW (SgWire a lam δ t ε) S Empty (Z ⊕ Xs) bT bP A ⊕ Xs) =
      2 * a + 3 * sigM (sgQ lam δ t ε) (sgOrd lam δ t ε) ε +
        6 * sigR (sgQ lam δ t ε) (sgOrd lam δ t ε) + 5 + Fintype.card S +
          (Fintype.card Z + Fintype.card Xs + bT + bP + A + 3) + Fintype.card Xs ∧
    ‖nrun prim (selSgOf hS δs UJg (pcSel hS η (factorMacro fo)) (sgCircuit a f z lam δ t ε)) ∘L
        (cleanEmb (X := Xs) ∘L sysEmb (io (P := Reg S R))) -
        (cleanEmb ∘L sysEmb (io (P := Reg S R))) ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) • sgHam (P := Reg S R) UJ hUJ f z lam U)‖ ≤
      ε + (nPriv (sgCircuit a f z lam δ t ε) : ℝ) * (η + 3 * ξ) + δs := by
  have hfV := factorMacro_valid fo hpub.valid har.elem har.classical
  obtain ⟨hpV, hpG, hpg, hpc, -⟩ := pcSel_spec (R := R) (Xs := Xs) (𝒢 := 𝒢) hS hη
    (factorMacro fo) hfV
  have hpa := pcSel_unc (Xs := Xs) (𝒢 := 𝒢) hS hη (factorMacro fo) hfV prim hprim _
    (by positivity : (0 : ℝ) ≤ 3 * ξ) (factorMacro_approx prim hprim fo hpub hξ har _ hN)
  have hsum := nKeepN_add_nSynN 𝒢 (factorMacro fo)
  rw [factorMacro_nGates] at hsum
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := gate_prop_signed_sel hS hadj hc₀ hc₁ hL prim hprim
    UJg hUJg UJ U hJ hUJ hU (pcSel hS η (factorMacro fo)) hpV hpG (by positivity) hpa hfz hlam
    hδ hδ1 hD t hε hε1 hδs hδs1
  refine ⟨h1, h2, fun p => by rw [h3 p, hpc p, factorMacro_nCalls], h4, hpg, hsum, h5, h6, ?_, h8⟩
  rw [h7, Fintype.card_sum]

end SignedSel

end

end ManuscriptConformance
