import ManuscriptConformance.Defs
import GateOptimalBinary.Main
import GateEfficientSynthesis.Parts
import GateEfficientBitBudget.Hamiltonian

/-!
# The gate model of the conformance statements

The gate-level conformance theorems (`gate:thm:main`, `hs:thm:gates`, `ode:thm:gates` and
Propositions `gate:prop:finite`, `gate:prop:signed`, `gate:prop:core`) are stated in the package's
native gate model (`SparseHamiltonian.GateNative`): a circuit is a list of instructions on finitely
many qubit wires `W`, each an elementary gate (a one-qubit unitary with at most three literal
controls, `NInstr.Valid`; over a finite gate set `𝒢`, a gate of `𝒢`, `GateSynth.GateOf`) or an
uncontrolled call of a supplied primitive oracle (forward or inverse) placed on some of the wires;
`nGatesN` and `nCallsN` count them, and `nrun` is the operator of the circuit on the register
`Reg W R` of the wires carrying an untouched payload `R` (the reference). This file adds:

* `cleanAlong sys`: the clean embedding of the system register along the system wires `sys`, every
  other wire zero (the manuscript's `ψ ⊗ |0⟩`); `cleanEmb_sysEmb_io`: the package's clean embedding
  of a native circuit with synthesis ancillas is `cleanAlong` along its system wires;
* `BinaryFormat`, `formal_binaryInput`: the binary sparse format of the package's gate endpoints
  (the formal restriction of the gate theorems, review item B);
* the named hypotheses `comp_bits`, `formal_nondegenerate`, `formal_gbarOne` of the gate
  theorems;
* `synthesis_of_parts`: finite-set synthesis from single-qubit synthesis of logarithmic length and
  an exact decomposition of controlled gates (the manuscript's external synthesis assumption);
* `gateWord`: the argument `b_data + log₂(N+1) + log₂(s+1) + log₂((Q+1)/ε)` of the polynomial of
  eq. `gate:eq:main-gates` (base-2 logarithms; a change of base changes only the constants);
* `qmu_eq`: the package's query scale `Q_μ` is eq. `gate:eq:query-scale` (`twoNormBound`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian SparseHamiltonian.GateCircuit SparseHamiltonian.GateNative
  SparseHamiltonian.GateSynth
open scoped InnerProduct

/-! ### The clean embedding along the system wires -/

section Clean

variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R]

/-- **The clean embedding along the system wires** `sys : S ↪ W`: the system register `Reg S R`
(the system qubits `S` with the untouched reference `R`) on the wires `sys`, every other wire in
`|0⟩`. -/
def cleanAlong {S W : Type*} [Fintype S] [DecidableEq S] [Fintype W] [DecidableEq W]
    (sys : S ↪ W) : Reg S R →L[ℂ] Reg W R :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Cfg W => R)).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi (fun y =>
      @ite _ (∀ w, (∀ s, sys s ≠ w) → y w = false) (Classical.propDecidable _)
        (coord (fun s => y (sys s))) 0)

theorem cleanAlong_apply {S W : Type*} [Fintype S] [DecidableEq S] [Fintype W] [DecidableEq W]
    (sys : S ↪ W) (ψ : Reg S R) (y : Cfg W) :
    cleanAlong sys ψ y =
      @ite _ (∀ w, (∀ s, sys s ≠ w) → y w = false) (Classical.propDecidable _)
        (ψ (fun s => y (sys s))) 0 := by
  change (@ite _ (∀ w, (∀ s, sys s ≠ w) → y w = false) (Classical.propDecidable _)
    (coord (fun s => y (sys s))) 0) ψ = _
  split_ifs <;> rfl

/-- The system wires of a native register with synthesis ancillas. -/
def sysWire (V S X' Z : Type*) (bT bP A : ℕ) (Xa : Type*) : S ↪ (HW V S X' Z bT bP A ⊕ Xa) :=
  ⟨fun s => Sum.inl (Sum.inl (Sum.inr s)), fun a b h => by simpa using h⟩

/-- **The package's clean embedding is `cleanAlong`**: for a native circuit on the released
wires `Wire a m r K`, the system qubits `S`, the work wires and the synthesis ancillas `X_a`, the
clean embedding `cleanEmb ∘ sysEmb io` places the system on its wires with every other wire in
`|0⟩`. -/
theorem cleanEmb_sysEmb_io {a m r K : ℕ} {S X' Z Xa : Type*} [Fintype S] [DecidableEq S]
    [Fintype X'] [DecidableEq X'] [Fintype Z] [DecidableEq Z] [Fintype Xa] [DecidableEq Xa]
    {bT bP A : ℕ} :
    (cleanEmb (X := Xa) ∘L sysEmb (X' := X') (Z := Z) (bT := bT) (bP := bP) (A := A)
        (Sim.io (P := Reg S R) (a := a) (m := m) (r := r) (K := K)) : Reg S R →L[ℂ] _) =
      cleanAlong (R := R) (sysWire (Sim.Wire a m r K) S X' Z bT bP A Xa) := by
  refine ContinuousLinearMap.ext fun ψ => PiLp.ext fun y => ?_
  rw [cleanAlong_apply]
  simp only [comp_apply, cleanEmb_apply, sysEmb, fl_apply, Sim.io_apply, bas_apply]
  by_cases h : ∀ w, (∀ s, sysWire (Sim.Wire a m r K) S X' Z bT bP A Xa s ≠ w) → y w = false
  · rw [if_pos h]
    have h1 : (fun x => y (Sum.inr x)) = (fun _ => false) :=
      funext fun xa => h _ (fun s hs => by cases hs)
    have h2 : (fun x => y (Sum.inl (Sum.inr x))) = (fun _ => false) :=
      funext fun x => h _ (fun s hs => by simp [sysWire] at hs)
    have h3 : (fun w => y (Sum.inl (Sum.inl (Sum.inl w)))) = Sim.cfg0 :=
      funext fun v => h _ (fun s hs => by simp [sysWire] at hs)
    rw [if_pos h1, if_pos h2, if_pos h3]
    rfl
  · rw [if_neg h]
    push Not at h
    obtain ⟨w, hw, hyw⟩ := h
    have hyw' : y w = true := by simpa using hyw
    rcases w with ((v | s) | x) | xa
    · have h3 : ¬ (fun w => y (Sum.inl (Sum.inl (Sum.inl w)))) = Sim.cfg0 := by
        intro he
        have := congrFun he v
        simp [Sim.cfg0] at this
        rw [this] at hyw'
        exact Bool.false_ne_true hyw'
      split_ifs <;> simp_all
    · exact absurd rfl (hw s)
    · have h2 : ¬ (fun x => y (Sum.inl (Sum.inr x))) = (fun _ => false) := by
        intro he
        have : y (Sum.inl (Sum.inr x)) = false := congrFun he x
        rw [this] at hyw'
        exact Bool.false_ne_true hyw'
      split_ifs <;> simp_all
    · have h1 : ¬ (fun x => y (Sum.inr x)) = (fun _ => false) := by
        intro he
        have : y (Sum.inr xa) = false := congrFun he xa
        rw [this] at hyw'
        exact Bool.false_ne_true hyw'
      rw [if_neg h1]

end Clean

/-! ### The binary sparse format -/

section Binary

open GateBinary

variable {X n : Type*} [Fintype n] [DecidableEq n]

/-- **The binary sparse format of the package's gate endpoints** (`GateEfficientBinary`): `k`-bit
indices (`en`, so the dimension is `N = 2^k`), `s = 2^{s_b}` slots enumerated by the low index
words (`range`), entries stored as two `b`-bit two's complement words read by the public decoder
`c₀(X + iY)`, `c₀ > 0`. The manuscript allows general sizes and any efficiently decoded encoding;
this is the formal restriction `formal_binaryInput` (review item B). The sizes are general for
`gate:thm:main` and `hs:thm:gates` in `GateGeneral` (by padding the oracles,
`SparseHamiltonian.GeneralSparseAccess`) and for `ode:thm:gates` in `GateODEGeneral` and
`GateODETimeGeneral` (`SparseHamiltonian.GeneralSparseODE`), with the decoder kept
(`formal_binaryDecoder`); the decoders are general for `gate:thm:main` and `hs:thm:gates` in
`GateMainDecoder` and `GateDecoder`. -/
structure BinaryFormat {s k b : ℕ} (D : NativeSparseBlockEncoding.Data X n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (sb : ℕ) (c0 : ℝ) : Prop where
  hsb : sb ≤ k
  hs : s = 2 ^ sb
  range : ∀ j : n, (∃ m, D.slot m = j) ↔ ∃ u : Fin sb → Bool, j = en (lowWord sb u)
  hb : 0 < b
  hc0 : 0 < c0
  dec : ∀ e z, D.decode e z = (c0 : ℂ) * gauss z

/-- **`formal_binaryInput`** (review item B): the data are in the binary sparse format of the
package's gate endpoints (`BinaryFormat`). -/
abbrev formal_binaryInput {s k b : ℕ} (D : NativeSparseBlockEncoding.Data X n (Cfg (VW b)) s)
    (en : Cfg (Fin k) ≃ n) (sb : ℕ) (c0 : ℝ) : Prop :=
  BinaryFormat D en sb c0

omit [DecidableEq n] in
theorem card_eq_two_pow {k : ℕ} (en : Cfg (Fin k) ≃ n) : Fintype.card n = 2 ^ k := by
  rw [← Fintype.card_congr en]
  simp

end Binary

/-! ### The named hypotheses of the gate theorems -/

/-- **`comp_bits`** (Section `gate:sec:result`: "the bit strings encoding the entries and the
public parameters have finite descriptions of at most `b_data` bits"): the stored bits of each
entry component are at most `b_data`, and every listed public parameter has bit length `b_data` in
the fixed-point model `GateBitBudget.HasBits`. -/
def comp_bits (b bd : ℕ) (xs : List ℝ) : Prop :=
  b ≤ bd ∧ List.Forall (GateBitBudget.HasBits bd) xs

/-- **`formal_nondegenerate`**: `ḡ ≥ 1` and `B > 0`. Both hold for every admissible instance
(contractivity gives `g = B/‖x(T)‖ ≥ 1`, and `x(T) ≠ 0` forces `B > 0`), so the restriction
excludes only public data without any admissible instance. -/
def formal_nondegenerate (gbar B : ℝ) : Prop := 1 ≤ gbar ∧ 0 < B

/-- **`formal_gbarOne`**: `ḡ ≥ 1`, which holds for every admissible instance (contractivity). -/
def formal_gbarOne (gbar : ℝ) : Prop := 1 ≤ gbar

/-! ### Finite-set synthesis -/

/-- **Finite-set synthesis from its parts**: single-qubit synthesis over `𝒢` with clean ancillas
`X₁` and length `L ζ ≤ c₁ log(1/ζ) + c₀` (the finite-gate assumptions of Section
`gate:sec:result`: "An arbitrary one-qubit unitary can be synthesised to error `ζ` with
`O(log(1/ζ))` gates for `0 < ζ ≤ 1/2`", Ref. KMM2013) and an exact decomposition of the one-qubit
gates with at most three controls into at most `K` gates of `𝒢` or uncontrolled one-qubit gates
("A one-qubit unitary with at most three controls (on specified bits equal to zero or one) has an
exact decomposition into a bounded number of gates from the set and uncontrolled one-qubit
unitaries", Ref. Barenco et al.; "Both synthesis and decomposition use at most a constant number
of clean ancillas") give synthesis of every elementary gate with the ancillas `X₂ ⊕ X₁` and
logarithmic length. -/
theorem synthesis_of_parts {𝒢 : Set Kind} {X₁ X₂ : Type*} [Fintype X₁] [DecidableEq X₁]
    [Fintype X₂] [DecidableEq X₂] {L : ℝ → ℕ} {K : ℕ} {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁)
    (h1 : OneQubitSynthesis 𝒢 X₁ L)
    (hL : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀)
    (h2 : ControlDecomposition 𝒢 X₂ K) :
    ∃ (L' : ℝ → ℕ) (c₀' c₁' : ℝ), 0 ≤ c₀' ∧ 0 ≤ c₁' ∧ Synthesis 𝒢 (X₂ ⊕ X₁) L' ∧
      ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (L' ζ : ℝ) ≤ c₁' * Real.log (1 / ζ) + c₀' := by
  refine ⟨fun ζ => K * (L (ζ / (K + 1)) + 1), K * (c₁ * Real.log (K + 1) + c₀ + 1), K * c₁,
    ?_, by positivity, Synthesis.of_parts h1 h2, fun ζ hζ hζ1 => ?_⟩
  · have : 0 ≤ Real.log ((K : ℝ) + 1) := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) K; linarith)
    positivity
  · have := of_parts_len_le hL K hζ hζ1
    linarith

/-! ### The polynomial argument and the query scale -/

/-- **The argument of the polynomial of eq. `gate:eq:main-gates`**:
`b_data + log₂(N+1) + log₂(s+1) + log₂((Q+1)/ε)` (base-2 logarithms; a change of base changes only
the constants of the polynomial). -/
def gateWord (bd N s : ℕ) (Q ε : ℝ) : ℝ :=
  bd + Real.logb 2 ((N : ℝ) + 1) + Real.logb 2 ((s : ℝ) + 1) + Real.logb 2 ((Q + 1) / ε)

/-- The package's query scale `Q_μ` is eq. `gate:eq:query-scale`. -/
theorem qmu_eq (s : ℕ) (η μ t ε : ℝ) :
    GateOptimalPrecision.Qmu s η μ t ε = twoNormBound s η μ t ε := by
  have e : Real.log (1 / ε) / (η ^ 2 * |t| / μ) = μ * logInv ε / (η ^ 2 * |t|) := by
    unfold logInv
    rw [div_div_eq_mul_div, mul_comm]
  unfold GateOptimalPrecision.Qmu twoNormBound LargeSparsityCore.Parameters.rval
    LargeSparsityCore.Parameters.hval LargeSparsityCore.Parameters.Lval
  rw [e]
  have h2 : (s : ℝ) * μ * |t| * (Real.log (1 / ε) /
      Real.log (Real.exp 1 + μ * logInv ε / (η ^ 2 * |t|))) =
      (s : ℝ) * μ * |t| * logInv ε / Real.log (Real.exp 1 + μ * logInv ε / (η ^ 2 * |t|)) :=
    (mul_div_assoc _ _ _).symm
  rw [h2]
  rfl

end

end ManuscriptConformance
