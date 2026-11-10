import GateEfficientNative.Hamiltonian.Circuit
import GateEfficientTimeDependent.Theorem
import SparseHamiltonian.LabeledAdjointSimulation

/-!
# Native gate-efficient Hamiltonian simulation

The native circuits of Theorem `hs:thm:gates`: the released simulators with
`U_J` given by its `C_J` elementary gates and every private Cayley call
replaced by its native implementation `V† R V` with reversible angle
arithmetic and bit-controlled rotations.

* `native_simulation` (constant Hamiltonian): exact counts of primitive
  calls (`12 d` copies of the compute circuit `V`), at most
  `200 (d+1)(a+m+r+1) + 84 d C_J + 6 d G_C` elementary gates with
  `G_C = 2 nGatesN V + 2 |circ| + 2 bP + bT + 1`, the qubit count, and
  full-output error at most `ε` against `exp(-iτH)` on the system
  embedding (every non-system qubit clean, the payload `R` an untouched
  reference), when the arithmetic accuracy satisfies `48 d ζ ≤ ε`.
* `native_simulation_signed`: every real time `t`, by the literal inverse
  circuit for `t < 0`.
* `native_time_simulation`: the time-dependent version with slot-selected
  native private operations.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim
open GatePointerEncoding (wordEquivFin)
open scoped InnerProduct BigOperators

/-! ### The released semantics from the selected macros -/

section Released

variable {a m r K : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The constant private operation as a selected family without selection wires. -/
def constFam (D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) :
    Bool → Cfg Empty → (Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) :=
  fun adj _ => if adj then D† else D

/-- The slot-selected private operations as a family selected by the slot wires. -/
def slotFam (D : ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) :
    Bool → Cfg (Fin m) → (Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) :=
  fun adj w => SlotSim.adjT adj (D (wordEquivFin m w))

omit [Fintype S] [DecidableEq S] in
theorem wireRel_sec : (wireRel a m r K).sec = Wire.sec := rfl

omit [Fintype S] [DecidableEq S] in
theorem ctrlOK_sec (x : Cfg (Wire a m r K)) : ctrlOK [(Wire.sec, true)] x = x Wire.sec := by
  simp [ctrlOK]

theorem evalSel_const (UJg : List (Gate (Fin a ⊕ S))) (D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R))
    (i : Instr (Wire a m r K)) (hi : SecOK (wireRel a m r K) i) :
    evalSel (wireRel a m r K) UJg (noSel _) (constFam D) i =
      i.eval (simSem (P := Reg S R) (UJop (R := R) UJg) D) := by
  cases i with
  | gate g => rfl
  | uj cs adj =>
      simp only [SecOK] at hi
      subst hi
      simp only [evalSel, selOracle, Instr.eval, oracleOp, simSem]
      apply localOp_congr
      intro x
      simp only [wireRel_sec, ctrlOK_sec]
      rfl
  | priv cs adj =>
      simp only [SecOK] at hi
      subst hi
      simp only [evalSel, selOracle, Instr.eval, oracleOp, simSem]
      apply localOp_congr
      intro x
      simp only [wireRel_sec, ctrlOK_sec, constFam]

theorem prodOps_evalSel_const (UJg : List (Gate (Fin a ⊕ S)))
    (D : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (l : List (Instr (Wire a m r K)))
    (hl : ∀ i ∈ l, SecOK (wireRel a m r K) i) :
    prodOps (V := Wire a m r K) (R := Reg S R)
      (evalSel (wireRel a m r K) UJg (noSel _) (constFam D)) l =
      run (simSem (P := Reg S R) (UJop (R := R) UJg) D) l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [prodOps, run_cons, ih (fun j hj => hl j (List.mem_cons_of_mem i hj)),
        evalSel_const UJg D i (hl i List.mem_cons_self)]

theorem evalSel_slot (UJg : List (Gate (Fin a ⊕ S)))
    (D : ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (i : Instr (Wire a m r K))
    (hi : SecOK (wireRel a m r K) i) :
    evalSel (wireRel a m r K) UJg (slotSel a m r K) (slotFam D) i =
      SlotSim.evalT (P := Reg S R) (UJop (R := R) UJg) D i := by
  cases i with
  | gate g => rfl
  | uj cs adj =>
      simp only [SecOK] at hi
      subst hi
      simp only [evalSel, selOracle, SlotSim.evalT, oracleOp]
      apply localOp_congr
      intro x
      simp only [wireRel_sec, ctrlOK_sec]
      rfl
  | priv cs adj =>
      simp only [SecOK] at hi
      subst hi
      simp only [evalSel, selOracle, SlotSim.evalT, SlotSim.slotOracle]
      apply localOp_congr
      intro x
      simp only [wireRel_sec, ctrlOK_sec, slotFam, slotSel, slotIdx]
      rfl

theorem prodOps_evalSel_slot (UJg : List (Gate (Fin a ⊕ S)))
    (D : ℕ → Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (l : List (Instr (Wire a m r K)))
    (hl : ∀ i ∈ l, SecOK (wireRel a m r K) i) :
    prodOps (V := Wire a m r K) (R := Reg S R)
      (evalSel (wireRel a m r K) UJg (slotSel a m r K) (slotFam D)) l =
      SlotSim.runT (P := Reg S R) (UJop (R := R) UJg) D l := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      rw [prodOps, SlotSim.runT_cons, ih (fun j hj => hl j (List.mem_cons_of_mem i hj)),
        evalSel_slot UJg D i (hl i List.mem_cons_self)]

end Released

/-! ### The operator algebra of a register -/

section TopRing

variable {S : Type*} [Fintype S] [DecidableEq S]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R]

/-- The operators on a qubit register with a payload form a topological ring
(used by `NormedSpace.exp`; instance search does not reach it through the
`PiLp` norm). -/
theorem regIsTopologicalRing : IsTopologicalRing (Reg S R →L[ℂ] Reg S R) :=
  @NonUnitalSeminormedRing.toIsTopologicalRing (Reg S R →L[ℂ] Reg S R) _

attribute [scoped instance] regIsTopologicalRing

end TopRing

/-! ### Negative times -/

section Neg

variable {K P : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The literal inverse of a unitary circuit that simulates `exp(-i|t|H)` on an
embedding simulates `exp(-itH)` for `t < 0` with the same error. -/
theorem err_neg (C : K →L[ℂ] K) (hC : IsUnitary C) (ι : P →L[ℂ] K) (H : P →L[ℂ] P)
    (hH : star H = H) (t ε : ℝ) (ht : t < 0)
    (h : ‖C ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * ((|t| : ℝ) : ℂ)) • H)‖ ≤ ε) :
    ‖C† ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)‖ ≤ ε := by
  have hV := LabeledAdjointSimulation.evolution_unitary H hH |t|
  have hadj := LabeledAdjointSimulation.evolution_adjoint H hH |t|
  have ht' : ((-|t| : ℝ) : ℂ) = (t : ℂ) := by rw [abs_of_neg ht, neg_neg]
  rw [ht'] at hadj
  rw [← hadj, LabeledAdjointSimulation.adjoint_error_eq _ _ hC hV]
  exact h

end Neg

/-! ### Constant Hamiltonians -/

section Constant

variable {S Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The native gate-level simulation circuit** for target accuracy `ε`: the
released circuit at accuracy `ε/2` with native macros.  It is fixed by the
public data: the numbers `a, τ, Q, qbar, ε`, the gates of `U_J`, the compute
circuit, orientation wire and decoder of the private operation, and the
reversible arithmetic. -/
def nativeSim (a : ℕ) (τ Q qbar ε : ℝ) (UJg : List (Gate (Fin a ⊕ S)))
    (nd : NativeOp Empty (Fin a ⊕ S) Z Y J) (ar : Arith (NB Empty (Fin a ⊕ S) Z)) :
    List (NInstr (HW (SimWire a Q τ qbar (ε / 2)) S Empty Z ar.bT ar.bP ar.A) Y J) :=
  hcirc (wireRel _ _ _ _) (noSel _) UJg nd ar (simCircuit a τ Q qbar (ε / 2))

/-- **Native gate-efficient sparse Hamiltonian simulation** (Theorem
`hs:thm:gates`, constant Hamiltonian, before finite-set synthesis).

The private Cayley operation `D` is given natively: a public compute circuit
`V` of elementary gates and primitive oracle calls with `V† R_val V = D` on
clean scratch (`NativeOK`), where `R_val` is the edge rotation of the decoded
entry `z`, and public reversible arithmetic computing the rotation angles of
`z` within `ζ` (`ArithOK`).  `U_J` is given by its `C_J` elementary gates.
Under the clock promises of the released analysis for `D` and
`J = U_J ι₀` and `48 d ζ ≤ ε`, the native circuit consists of valid
elementary instructions and primitive calls, makes exactly `12 d` times the
primitive calls of `V`, uses at most
`200 (d+1)(a+m+r+1) + 84 d C_J + 6 d G_C` elementary gates, and its full
output on the system embedding is within `ε` of `exp(-iτH)`. -/
theorem native_simulation (a : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp Empty (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB Empty (Fin a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D R1 : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (H : Reg S R →L[ℂ] Reg S R)
    (hD : IsUnitary D) (hN : NativeOK prim nd (selOp (fun _ : Cfg Empty => D)))
    (τ Q b qbar ε : ℝ) (hτ : 0 ≤ τ) (hQ : 1 ≤ Q)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hζε : 48 * (fDeg Q τ qbar (ε / 2) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ nativeSim a τ Q qbar ε UJg nd ar, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (nativeSim a τ Q qbar ε UJg nd ar) =
      12 * fDeg Q τ qbar (ε / 2) * nCallsN p nd.V) ∧
    nGatesN (nativeSim a τ Q qbar ε UJg nd ar) ≤
      200 * (fDeg Q τ qbar (ε / 2) + 1) * (a + simM τ (ε / 2) + simR Q τ qbar (ε / 2) + 1) +
        84 * fDeg Q τ qbar (ε / 2) * UJg.length +
        6 * fDeg Q τ qbar (ε / 2) *
          (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) ∧
    Fintype.card (HW (SimWire a Q τ qbar (ε / 2)) S Empty Z ar.bT ar.bP ar.A) =
      Fintype.card S + (2 * a + 3 * simM τ (ε / 2) + 6 * simR Q τ qbar (ε / 2) + 3) +
        (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) ∧
    ‖nrun prim (nativeSim a τ Q qbar ε UJg nd ar) ∘L sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H)‖ ≤ ε ∧
    (fDeg Q τ qbar (ε / 2) : ℝ) ≤ 128 * (τ * qbar + Q * (1 + Real.log (6 / ε))) ∧
    TimeSchedule.steps τ (ε / 6) ≤ 2 ^ simM τ (ε / 2) ∧
    2 ^ simM τ (ε / 2) < 2 * TimeSchedule.steps τ (ε / 6) ∧
    2 * fDeg Q τ qbar (ε / 2) + 2 ≤ 2 ^ simR Q τ qbar (ε / 2) ∧
    2 ^ simR Q τ qbar (ε / 2) ≤ 4 * (fDeg Q τ qbar (ε / 2) + 1) := by
  have hε2 : 0 < ε / 2 := by linarith
  have hε21 : ε / 2 ≤ 1 := by linarith
  have hUJu : IsUnitary (UJop (R := R) UJg) := UJop_isUnitary UJg hUJg
  obtain ⟨hvalid, hP, hJ, hG, hW, herr, hdeg, hm1, hm2, hr1, hr2⟩ :=
    gate_efficient_simulation (P := Reg S R) a (UJop (R := R) UJg) D R1 H hUJu hD τ Q b qbar (ε / 2)
      hτ hQ hRight hLeft hR1
      hBoundary hSelf hH hEndpoint hbq hqQ hε2 hε21
  have hsec : ∀ i ∈ simCircuit a τ Q qbar (ε / 2), SecOK (wireRel _ _ _ _) i := by
    unfold simCircuit
    exact secOK_ampI _ _ _ _ _ _
  have hDu : ∀ w, IsUnitary (constFam D false w) := fun _ => hD
  have hDadj : ∀ w, constFam D true w = (constFam D false w)† := fun _ => rfl
  have hN' : NativeOK prim nd (selOp (constFam D false)) := hN
  have e3 : ε / 2 / 3 = ε / 6 := by ring
  have hlog : (1 : ℝ) / (ε / 2 / 3) = 6 / ε := by
    field_simp
    ring
  rw [e3] at hm1 hm2
  rw [hlog] at hdeg
  refine ⟨hcirc_valid (wireRel _ _ _ _) (noSel _) UJg hUJg nd hnd ar har.elem har.classical _
    hvalid,
    fun p => ?_, ?_, ?_, ?_, hdeg, hm1, hm2, hr1, hr2⟩
  · rw [nativeSim, hcirc_nCalls, hP]
    ring
  · refine (hcirc_nGates (wireRel _ _ _ _) (noSel _) UJg hUJg nd ar _).trans ?_
    rw [hP, hJ, mul_one]
    have h84 : 12 * fDeg Q τ qbar (ε / 2) * (7 * UJg.length) =
        84 * fDeg Q τ qbar (ε / 2) * UJg.length := by ring
    rw [h84]
    exact Nat.add_le_add_right (Nat.add_le_add_right hG _) _
  · rw [card_HW, card_simWire]
    simp only [Fintype.card_empty, add_zero]
    ring
  · have hio : ∀ ψ : Reg S R, ‖(io (P := Reg S R) (a := a) (m := simM τ (ε / 2))
        (r := simR Q τ qbar (ε / 2)) (K := simK a Q τ qbar (ε / 2))) ψ‖ = ‖ψ‖ :=
      fun ψ => by rw [io_apply, norm_bas]
    rw [nativeSim]
    generalize NormedSpace.exp ((-Complex.I * (τ : ℂ)) • H) = U at herr ⊢
    generalize simCircuit a τ Q qbar (ε / 2) = l at herr hvalid hsec hP ⊢
    have h := hcirc_error (X' := Empty) prim hprim (wireRel _ _ _ _) (noSel _) UJg hUJg nd hnd ar hζ
      har (constFam D) hDu hDadj hN' l hvalid io hio U _ (prodOps_evalSel_const UJg D l hsec) herr
    refine h.trans ?_
    rw [hP, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hζε]

/-- The native circuit for a signed time `t`: the circuit for `|t|`, or its
literal inverse for `t < 0`. -/
def nativeSimSigned (a : ℕ) (t Q qbar ε : ℝ) (UJg : List (Gate (Fin a ⊕ S)))
    (nd : NativeOp Empty (Fin a ⊕ S) Z Y J) (ar : Arith (NB Empty (Fin a ⊕ S) Z)) :
    List (NInstr (HW (SimWire a Q |t| qbar (ε / 2)) S Empty Z ar.bT ar.bP ar.A) Y J) :=
  if 0 ≤ t then nativeSim a |t| Q qbar ε UJg nd ar else ninv (nativeSim a |t| Q qbar ε UJg nd ar)

/-- **Every real time.**  For `t < 0` the literal inverse of the circuit for
`|t|` simulates `exp(-itH)` with the same counts and the same full-output
error. -/
theorem native_simulation_signed (a : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp Empty (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB Empty (Fin a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
    (har : ArithOK ar (Sum.inl (Sum.inr nd.o)) nd.dec ζ)
    (D R1 : Anc a (Reg S R) →L[ℂ] Anc a (Reg S R)) (H : Reg S R →L[ℂ] Reg S R)
    (hD : IsUnitary D) (hN : NativeOK prim nd (selOp (fun _ : Cfg Empty => D)))
    (t Q b qbar ε : ℝ) (hQ : 1 ≤ Q)
    (hRight : (1 - D) ∘L R1 = 1) (hLeft : R1 ∘L (1 - D) = 1) (hR1 : ‖R1‖ ≤ Q)
    (hBoundary : (UJop (R := R) UJg ∘L iota0 (P := Reg S R))† ∘L R1 ∘L
      (UJop (R := R) UJg ∘L iota0 (P := Reg S R)) = (2 : ℂ)⁻¹ • (1 + Complex.I • H))
    (hSelf : star H = H) (hH : ‖H‖ ≤ 1)
    (hEndpoint : ‖R1 ∘L (UJop (R := R) UJg ∘L iota0 (P := Reg S R))‖ ≤ b)
    (hbq : b ^ 2 ≤ qbar / 2) (hqQ : qbar ≤ Q)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hζε : 48 * (fDeg Q |t| qbar (ε / 2) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ nativeSimSigned a t Q qbar ε UJg nd ar, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (nativeSimSigned a t Q qbar ε UJg nd ar) =
      12 * fDeg Q |t| qbar (ε / 2) * nCallsN p nd.V) ∧
    nGatesN (nativeSimSigned a t Q qbar ε UJg nd ar) ≤
      200 * (fDeg Q |t| qbar (ε / 2) + 1) * (a + simM |t| (ε / 2) + simR Q |t| qbar (ε / 2) + 1) +
        84 * fDeg Q |t| qbar (ε / 2) * UJg.length +
        6 * fDeg Q |t| qbar (ε / 2) *
          (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) ∧
    ‖nrun prim (nativeSimSigned a t Q qbar ε UJg nd ar) ∘L sysEmb (io (P := Reg S R)) -
        sysEmb (io (P := Reg S R)) ∘L NormedSpace.exp ((-Complex.I * (t : ℂ)) • H)‖ ≤ ε := by
  obtain ⟨hvalid, hcalls, hgates, -, herr, -⟩ := native_simulation a prim hprim UJg hUJg nd hnd ar ζ
    hζ har D R1 H hD hN |t| Q b qbar ε (abs_nonneg t) hQ hRight hLeft hR1 hBoundary hSelf hH
    hEndpoint hbq hqQ hε hε1 hζε
  unfold nativeSimSigned
  split_ifs with ht
  · have ht' : ((|t| : ℝ) : ℂ) = (t : ℂ) := by rw [abs_of_nonneg ht]
    rw [ht'] at herr
    exact ⟨hvalid, hcalls, hgates, herr⟩
  · refine ⟨valid_ninv _ hvalid, fun p => ?_, ?_, ?_⟩
    · rw [nCallsN_ninv, hcalls p]
    · rw [nGatesN_ninv]
      exact hgates
    have hC : IsUnitary (nrun prim (nativeSim a |t| Q qbar ε UJg nd ar)) :=
      nrun_isUnitary prim hprim _ hvalid
    rw [nrun_ninv]
    generalize nrun prim (nativeSim a |t| Q qbar ε UJg nd ar) = C at hC herr ⊢
    refine err_neg C hC _ H hSelf t ε (lt_of_not_ge ht) ?_
    exact herr

end Constant

/-! ### Time-dependent Hamiltonians -/

section Time

variable {S Z Y J : Type*} [Fintype S] [DecidableEq S] [Fintype Z] [DecidableEq Z] [Fintype Y]
  [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- **The native time-dependent circuit** with `2^m` slots for target
accuracy `ε`: the released slot circuit for accuracy `ε/2` (filter parameter
`ε/4`) with native macros, the private calls selected by the slot wires. -/
def nativeSimT (a m : ℕ) (τ Q qbar ε : ℝ) (UJg : List (Gate (Fin a ⊕ S)))
    (nd : NativeOp (Fin m) (Fin a ⊕ S) Z Y J) (ar : Arith (NB (Fin m) (Fin a ⊕ S) Z)) :
    List (NInstr (HW (Wire a m (simR Q τ qbar (ε / 4)) (a + m + 2 * simR Q τ qbar (ε / 4))) S Empty
      Z ar.bT ar.bP ar.A) Y J) :=
  hcirc (wireRel _ _ _ _) (slotSel _ _ _ _) UJg nd ar (SlotSim.simCircuitT a τ Q qbar (ε / 4) m)

/-- **Native gate-efficient time-dependent simulation** (Theorem `hs:thm:time` with the circuit of
`hs:thm:gates`, before finite-set synthesis). The slot-selected private Cayley operations `D k` are
given natively by one compute circuit `V` on the slot wires, the private register and scratch, with
`V† R_val V` acting on clean scratch as `D k` at slot word `k`. Under the clock promises at every
slot, the mesh conditions (at half the accuracy of the released theorem) and `48 d ζ ≤ ε`, the
native circuit has the counts of `native_simulation` and its full output is within `ε` of `U(t)` for
every propagator `U` of the path. -/
theorem native_time_simulation (a m : ℕ) (prim : J → Reg Y R →L[ℂ] Reg Y R)
    (hprim : ∀ j, IsUnitary (prim j))
    (UJg : List (Gate (Fin a ⊕ S))) (hUJg : ∀ g ∈ UJg, GateOK 3 g)
    (nd : NativeOp (Fin m) (Fin a ⊕ S) Z Y J) (hnd : nd.Public)
    (ar : Arith (NB (Fin m) (Fin a ⊕ S) Z)) (ζ : ℝ) (hζ : 0 ≤ ζ)
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
    (hζε : 48 * (fDeg Q (α * t) qbar (ε / 4) : ℝ) * ζ ≤ ε) :
    (∀ i ∈ nativeSimT a m (α * t) Q qbar ε UJg nd ar, i.Valid) ∧
    (∀ p : J → Bool, nCallsN p (nativeSimT a m (α * t) Q qbar ε UJg nd ar) =
      12 * fDeg Q (α * t) qbar (ε / 4) * nCallsN p nd.V) ∧
    nGatesN (nativeSimT a m (α * t) Q qbar ε UJg nd ar) ≤
      200 * (fDeg Q (α * t) qbar (ε / 4) + 1) * (a + m + simR Q (α * t) qbar (ε / 4) + 1) +
        84 * fDeg Q (α * t) qbar (ε / 4) * UJg.length +
        6 * fDeg Q (α * t) qbar (ε / 4) *
          (2 * nGatesN nd.V + 2 * ar.circ.length + (2 * ar.bP + ar.bT + 1)) ∧
    Fintype.card (HW (Wire a m (simR Q (α * t) qbar (ε / 4))
        (a + m + 2 * simR Q (α * t) qbar (ε / 4))) S Empty Z ar.bT ar.bP ar.A) =
      Fintype.card S + (2 * a + 3 * m + 6 * simR Q (α * t) qbar (ε / 4) + 3) +
        (Fintype.card Z + ar.bT + ar.bP + ar.A + 3) ∧
    (fDeg Q (α * t) qbar (ε / 4) : ℝ) ≤ 128 * (α * t * qbar + Q * (1 + Real.log (12 / ε))) ∧
    2 * fDeg Q (α * t) qbar (ε / 4) + 2 ≤ 2 ^ simR Q (α * t) qbar (ε / 4) ∧
    2 ^ simR Q (α * t) qbar (ε / 4) ≤ 4 * (fDeg Q (α * t) qbar (ε / 4) + 1) ∧
    (∃ U : ℝ → Reg S R →L[ℂ] Reg S R, U 0 = 1 ∧ TimeDependent.SolvesOn Hpath U 0 t) ∧
    ∀ U : ℝ → Reg S R →L[ℂ] Reg S R, U 0 = 1 → TimeDependent.SolvesOn Hpath U 0 t →
      ‖nrun prim (nativeSimT a m (α * t) Q qbar ε UJg nd ar) ∘L sysEmb (io (P := Reg S R)) -
          sysEmb (io (P := Reg S R)) ∘L U t‖ ≤ ε := by
  have hε2 : 0 < ε / 2 := by linarith
  have hε21 : ε / 2 ≤ 1 := by linarith
  have hUJu : IsUnitary (UJop (R := R) UJg) := UJop_isUnitary UJg hUJg
  have hC' : TimeSchedule.steps (α * t) (ε / 2 / 6) ≤ 2 ^ m := by
    rw [show ε / 2 / 6 = ε / 12 by ring]
    exact hCayley
  have hF' : 4 * β * t ^ 2 ≤ ε / 2 * 2 ^ m := by linarith
  have hV' : 4 * t * δ ≤ ε / 2 := by linarith
  obtain ⟨hvalid, hP, hJ, hG, hW, hdeg, hr1, hr2, hex, herr⟩ :=
    SlotSim.gate_efficient_time_simulation (P := Reg S R) a m (UJop (R := R) UJg) D R1 Hpath Hs t α
      β δ Q b qbar (ε / 2)
      ht hα hβ hQ hqQ hε2 hε21 hC' hF' hUJu hD hRight hLeft hR1 hBoundary hEndpoint hbq hSelf hHs
      hPath hLip hVal hV'
  have e4 : ε / 2 / 2 = ε / 4 := by ring
  have hlog : (6 : ℝ) / (ε / 2) = 12 / ε := by
    field_simp
    ring
  rw [e4] at hvalid hP hJ hG hW hdeg hr1 hr2 herr
  rw [hlog] at hdeg
  have hsec : ∀ i ∈ SlotSim.simCircuitT a (α * t) Q qbar (ε / 4) m, SecOK (wireRel _ _ _ _) i := by
    unfold SlotSim.simCircuitT
    exact secOK_ampI _ _ _ _ _ _
  have hfam : slotFam (m := m) (S := S) (R := R) D false = fun w => D (wordEquivFin m w) := rfl
  have hDu : ∀ w, IsUnitary (slotFam (m := m) (S := S) (R := R) D false w) := by
    intro w
    rw [hfam]
    exact hD _ (wordEquivFin m w).isLt
  have hDadj : ∀ w, slotFam (m := m) (S := S) (R := R) D true w = (slotFam D false w)† :=
    fun _ => rfl
  have hN' : NativeOK prim nd (selOp (slotFam D false)) := by rw [hfam]; exact hN
  refine ⟨hcirc_valid (wireRel _ _ _ _) (slotSel _ _ _ _) UJg hUJg nd hnd ar har.elem har.classical
    _ hvalid, fun p => ?_, ?_, ?_, hdeg, hr1, hr2, hex, fun U hU0 hU => ?_⟩
  · rw [nativeSimT, hcirc_nCalls, hP]
    ring
  · refine (hcirc_nGates (wireRel _ _ _ _) (slotSel _ _ _ _) UJg hUJg nd ar _).trans ?_
    rw [hP, hJ, mul_one]
    have h84 : 12 * fDeg Q (α * t) qbar (ε / 4) * (7 * UJg.length) =
        84 * fDeg Q (α * t) qbar (ε / 4) * UJg.length := by ring
    rw [h84]
    exact Nat.add_le_add_right (Nat.add_le_add_right hG _) _
  · rw [card_HW, card_wire]
    simp only [Fintype.card_empty, add_zero]
    ring
  · have hio : ∀ ψ : Reg S R, ‖(io (P := Reg S R) (a := a) (m := m)
        (r := simR Q (α * t) qbar (ε / 4)) (K := a + m + 2 * simR Q (α * t) qbar (ε / 4))) ψ‖ =
        ‖ψ‖ :=
      fun ψ => by rw [io_apply, norm_bas]
    have herr' := herr U hU0 hU
    rw [nativeSimT]
    generalize U t = Ut at herr' ⊢
    generalize SlotSim.simCircuitT a (α * t) Q qbar (ε / 4) m = l at herr' hvalid hsec hP ⊢
    have h := hcirc_error (X' := Empty) prim hprim (wireRel _ _ _ _) (slotSel _ _ _ _) UJg hUJg nd
      hnd ar hζ har (slotFam D) hDu hDadj hN' l hvalid io hio Ut _
      (prodOps_evalSel_slot UJg D l hsec) herr'
    refine h.trans ?_
    rw [hP, Nat.cast_mul, Nat.cast_ofNat]
    linarith only [hζε]

end Time

end

end SparseHamiltonian.GateNative
