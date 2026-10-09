import GateEfficientSynthesisTrials.Certificate

/-!
# Worst-case counts of the synthesised protocol

The synthesised protocol is the released native four-attempt protocol
`nprotocol (synthPrep hS η prepN) g` on the trial register `SWO …`
(`GateEfficientSynthesisTrials.Register`). In every history, including four failures, it makes
at most `40 g` times the primitive calls of the native preparation (the native bound) and uses
at most `40 g N_S + 20 g (4 n + 3)` elementary gates, where `N_S ≤ N len(η/(N+1))` is the
number of gates of the synthesised preparation, `N` that of the native preparation, and
`n = |AW| + |XW| + |SX| + |S|` counts the wires tested by the seed zero test
(`synth_protocol_worst`). Only the preparation is synthesised: the zero tests and the sign are
exact gates of `𝒢`, so the synthesis factor multiplies only the gates of the preparation. With
`len ζ ≤ c₁ log(1/ζ) + c₀` on `(0, 1]` and `η ≤ 1` the gates are at most
`40 g N (c₁ log((N+1)/η) + c₀) + 20 g (4 n + 3)` (`synth_protocol_worst_log`). `card_SWO`:
the trial register has `|S| + 2 (|AW| + (|Z| + bT + bP + A + 3) + (|Zs| + 1 + nP + |X|)) + |S| + 1`
qubits, that is, `2 (|V| + |X|) + 1` for the native register `V` (`card_SWO_eq`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateSynthTrials

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateNative GateSynth
open GateODE (AW)

section Counts

variable {a m r K k l f : ℕ} {S Zs Z Y J X : Type*} {nP bT bP A : ℕ}
variable [Fintype S] [DecidableEq S] [Fintype Zs] [DecidableEq Zs] [Fintype Z] [DecidableEq Z]
  [Fintype Y] [DecidableEq Y] [Fintype X] [DecidableEq X]
variable {𝒢 : Set Kind} {len : ℝ → ℕ}

omit [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] [DecidableEq X] in
/-- **The qubits of the trial register.** -/
theorem card_SWO :
    Fintype.card (SWO a m r K k l f S Zs nP Z bT bP A X) =
      Fintype.card S + 2 * (Fintype.card (AW a m r K k l f) + (Fintype.card Z + bT + bP + A + 3) +
        (Fintype.card Zs + 1 + nP + Fintype.card X)) + Fintype.card S + 1 := by
  rw [card_HW]
  simp only [OX, SX, sPool, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, XW, AWr]
  ring

omit [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] [DecidableEq X] in
/-- **The trial register has `2 (|V| + |X|) + 1` qubits**, `V` the native register and `X` the
synthesis ancillas: the wires of `V ⊕ X`, a fresh pool of as many wires and a fresh flag. -/
theorem card_SWO_eq :
    Fintype.card (SWO a m r K k l f S Zs nP Z bT bP A X) =
      2 * (Fintype.card (HWO a m r K k l f S Zs nP Z bT bP A) + Fintype.card X) + 1 := by
  rw [card_SWO, card_HW]
  simp only [OX, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  ring

omit [DecidableEq S] [DecidableEq Zs] [DecidableEq Z] [DecidableEq X] in
/-- The wires tested by the seed zero test of the trial register. -/
theorem card_tested :
    Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) + Fintype.card (SX Zs nP X) +
        Fintype.card S =
      Fintype.card (AW a m r K k l f) + (Fintype.card Z + bT + bP + A + 3) +
        (Fintype.card Zs + 1 + nP + Fintype.card X) + Fintype.card S := by
  simp only [OX, SX, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, XW, AWr]
  ring

/-- **Worst-case counts of the synthesised protocol**, over every history: at most `40 g` times
the primitive calls of the native preparation, and at most `40 g N_S + 20 g (4 n + 3)`
elementary gates, `N_S` the gates of the synthesised preparation and `n` the wires tested by
the seed zero test. -/
theorem synth_protocol_worst (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) (g : ℝ) (hg : 1 ≤ g) :
    (∀ q : J → Bool, ((nprotocol (synthPrep hS η prepN) g hg).worstCost (wCallN q) : ℝ) ≤
      40 * g * nCallsN q prepN) ∧
    ((nprotocol (synthPrep hS η prepN) g hg).worstCost wGateN : ℝ) ≤
      40 * g * nGatesN (synthPrep hS η prepN) +
        20 * g * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card (SX Zs nP X) + Fintype.card S) + 3) := by
  refine ⟨fun q => ?_, ?_⟩
  · have h := (nprotocol_worst (synthPrep hS η prepN) g hg q).2
    rwa [(synthPrep_counts hS hη prepN hvalid).2 q] at h
  · exact (nprotocol_worst (synthPrep hS η prepN) g hg (fun _ => true)).1

/-- **Worst-case gate count with a logarithmic synthesis length**: if `len ζ ≤ c₁ log(1/ζ) + c₀`
on `(0, 1]` and `0 < η ≤ 1`, the synthesised protocol uses at most
`40 g N (c₁ log((N+1)/η) + c₀) + 20 g (4 n + 3)` elementary gates in every history, `N` the gates
of the native preparation and `n` the wires tested by the seed zero test. -/
theorem synth_protocol_worst_log (hS : Synthesis 𝒢 X len) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (prepN : List (NInstr (HWO a m r K k l f S Zs nP Z bT bP A) Y J))
    (hvalid : ∀ i ∈ prepN, i.Valid) (g : ℝ) (hg : 1 ≤ g) {c₀ c₁ : ℝ} (hc₀ : 0 ≤ c₀)
    (hc₁ : 0 ≤ c₁) (hlen : ∀ ζ : ℝ, 0 < ζ → ζ ≤ 1 → (len ζ : ℝ) ≤ c₁ * Real.log (1 / ζ) + c₀) :
    ((nprotocol (synthPrep hS η prepN) g hg).worstCost wGateN : ℝ) ≤
      40 * g * (nGatesN prepN * (c₁ * Real.log ((nGatesN prepN + 1) / η) + c₀)) +
        20 * g * (4 * (Fintype.card (AW a m r K k l f) + Fintype.card (XW Z bT bP A) +
          Fintype.card (SX Zs nP X) + Fintype.card S) + 3) := by
  have h := (synth_protocol_worst hS hη prepN hvalid g hg).2
  have hN : ((nGatesN (synthPrep hS η prepN) : ℕ) : ℝ) ≤
      nGatesN prepN * (c₁ * Real.log ((nGatesN prepN + 1) / η) + c₀) :=
    (Nat.cast_le.mpr (synthPrep_counts hS hη prepN hvalid).1).trans
      (gates_log_le hc₀ hc₁ hlen hη hη1 _ _ le_rfl)
  have hg0 : 0 ≤ 40 * g := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hN hg0]

end Counts

end

end SparseHamiltonian.GateSynthTrials
