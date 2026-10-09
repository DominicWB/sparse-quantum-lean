import GateEfficientNative.Hamiltonian.Layout

/-!
# Native macros for released gate-level instructions

Every released instruction is replaced by a native macro (`hmacro`):

* an elementary gate by the same gate on the released wires;
* a sector-controlled call of `U_J` (or `U_J†`) by the `C_J` elementary gates
  of `U_J` (or of their literal inverse), each with the sector wire as an
  additional control (`ujGates`; a gate that already has three controls uses
  the released AND chain on three clean flags);
* a sector-controlled private call (or its inverse) by the native private
  implementation (`privMacro`, or its literal inverse) placed by `ePW`.

The released instructions of the simulators only use the sector wire as the
control of their oracle calls (`SecOK`, proved for every released circuit
`ampI`).  `evalSel` is the released semantics with `U_J` given by its gates
and a selected private operation.
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit GateCircuit.Sim
open GateODE (localOp_localOp localOp_localOp' localOp_gateOp overwrite_apply_ι overwrite_apply_out)
open scoped InnerProduct BigOperators

/-! ### Sector controls of the released circuits -/

section SecOK

/-- The oracle calls of an instruction are controlled by the sector wire. -/
def SecOK {V : Type*} {a : ℕ} (ρ : RelW V a) : Instr V → Prop
  | .gate _ => True
  | .uj cs _ => cs = [(ρ.sec, true)]
  | .priv cs _ => cs = [(ρ.sec, true)]

variable {a m r K : ℕ}

theorem secOK_ofGates (gs : List (Gate (Wire a m r K))) :
    ∀ i ∈ ofGates gs, SecOK (wireRel a m r K) i := by
  intro i hi
  simp only [ofGates, List.mem_map] at hi
  obtain ⟨g, _, rfl⟩ := hi
  trivial

theorem secOK_inv {V : Type*} {a : ℕ} (ρ : RelW V a) (i : Instr V) (h : SecOK ρ i) :
    SecOK ρ i.inv := by
  cases i with
  | gate g => trivial
  | uj cs adj => exact h
  | priv cs adj => exact h

theorem secOK_invList {V : Type*} {a : ℕ} (ρ : RelW V a) (l : List (Instr V))
    (h : ∀ i ∈ l, SecOK ρ i) : ∀ i ∈ invList l, SecOK ρ i := by
  intro i hi
  simp only [invList, List.mem_reverse, List.mem_map] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  exact secOK_inv ρ j (h j hj)

theorem secOK_selectI (c σ : ℝ) (n : ℕ) :
    ∀ i ∈ selectI (a := a) (m := m) (r := r) (K := K) c σ n, SecOK (wireRel a m r K) i := by
  induction n with
  | zero => intro i hi; simp [selectI] at hi
  | succ n ih =>
      intro i hi
      rw [selectI, List.mem_append] at hi
      rcases hi with hi | hi
      · exact ih i hi
      · split_ifs at hi with h
        · simp only [stepI, bnetI, List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false] at hi
          rcases hi with ((rfl | (rfl | hi) | rfl) | hi)
          · rfl
          · rfl
          · exact secOK_ofGates _ i hi
          · rfl
          · exact secOK_ofGates _ i hi
        · simp at hi

theorem secOK_lcuI {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ) (N : ℕ) :
    ∀ i ∈ lcuI (a := a) (m := m) (K := K) hL nOf wt c σ N, SecOK (wireRel a m r K) i := by
  intro i hi
  simp only [lcuI, List.mem_append] at hi
  rcases hi with (((hi | hi) | hi) | hi) | hi
  · exact secOK_ofGates _ i hi
  · exact secOK_ofGates _ i hi
  · exact secOK_selectI c σ N i hi
  · exact secOK_ofGates _ i hi
  · exact secOK_ofGates _ i hi

/-- Every released amplified circuit controls its oracle calls by the sector wire. -/
theorem secOK_ampI {L : ℕ} (hL : L ≤ 2 ^ r) (nOf : Fin L → ℕ) (wt : Fin L → ℝ) (c σ : ℝ) (N : ℕ) :
    ∀ i ∈ ampI (a := a) (m := m) (K := K) hL nOf wt c σ N, SecOK (wireRel a m r K) i := by
  intro i hi
  simp only [ampI, List.mem_append] at hi
  rcases hi with ((((hi | hi) | hi) | hi) | hi) | hi
  · exact secOK_lcuI hL nOf wt c σ N i hi
  · exact secOK_ofGates _ i hi
  · exact secOK_invList _ _ (secOK_lcuI hL nOf wt c σ N) i hi
  · exact secOK_ofGates _ i hi
  · exact secOK_lcuI hL nOf wt c σ N i hi
  · exact secOK_ofGates _ i hi

end SecOK

/-! ### `U_J` from its gates -/

section UJ

variable {a : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The unitary of a gate list on the ancilla and system wires, as an operator
on the ancilla register with the system payload. -/
def UJop (UJg : List (Gate (Fin a ⊕ S))) : Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R) :=
  unfl ∘L gRun UJg ∘L fl

omit [CompleteSpace R] in
theorem conj_unfl_fl (G : Reg (Fin a ⊕ S) R →L[ℂ] Reg (Fin a ⊕ S) R) :
    conj (unfl ∘L G ∘L fl : Reg (Fin a) (Reg S R) →L[ℂ] _) = G := by
  unfold conj
  ext φ
  simp

theorem UJop_adjoint (UJg : List (Gate (Fin a ⊕ S))) :
    (UJop (R := R) UJg)† =
      (unfl ∘L gRun (Q := R) (gInv UJg) ∘L fl :
        Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)) := by
  unfold UJop
  rw [adjoint_comp, adjoint_comp, fl_adjoint, gRun_gInv, comp_assoc]
  have h : (unfl (W := Fin a) (S := S) (R := R))† = fl := by rw [← fl_adjoint, adjoint_adjoint]
  rw [h]

theorem UJop_isUnitary (UJg : List (Gate (Fin a ⊕ S))) (h : ∀ g ∈ UJg, GateOK 3 g) :
    IsUnitary (UJop (R := R) UJg) := by
  have hG := gRun_isUnitary (Q := R) UJg (fun g hg => (h g hg).2.2)
  constructor
  · have : star (UJop (R := R) UJg) * UJop UJg = (unfl ∘L (star (gRun (Q := R) UJg) *
        gRun UJg) ∘L fl : Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)) := by
      rw [star_eq_adjoint, star_eq_adjoint, UJop_adjoint, mul_def, mul_def, UJop, gRun_gInv]
      ext ψ; simp
    rw [this, hG.1]
    ext ψ; simp
  · have : UJop (R := R) UJg * star (UJop UJg) = (unfl ∘L (gRun (Q := R) UJg *
        star (gRun UJg)) ∘L fl : Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R)) := by
      rw [star_eq_adjoint, star_eq_adjoint, UJop_adjoint, mul_def, mul_def, UJop, gRun_gInv]
      ext ψ; simp
    rw [this, hG.2]
    ext ψ; simp

end UJ

/-! ### The macros -/

section Macro

variable {V S X' Z Sel Y J : Type*} {a : ℕ}

/-- The controlled gates of `U_J` on the native register. -/
def ujGates {bT bP A : ℕ} (ρ : RelW V a) (gs : List (Gate (Fin a ⊕ S))) :
    List (Gate (HW V S X' Z bT bP A)) :=
  gs.flatMap (fun g => ctrlGate (secW ρ) flagList (GateODE.Gate.map (pEmb ρ) g))

/-- The native macro of a released instruction. -/
def hmacro (ρ : RelW V a) (sw : SelWires ρ Sel) (UJg : List (Gate (Fin a ⊕ S)))
    (nd : NativeOp Sel (Fin a ⊕ S) Z Y J) (ar : Arith (NB Sel (Fin a ⊕ S) Z)) :
    Instr V → List (NInstr (HW V S X' Z ar.bT ar.bP ar.A) Y J)
  | .gate g => [NInstr.gate (GateODE.Gate.map wEmb g)]
  | .uj _ adj => nGatesOf (ujGates ρ (if adj then gInv UJg else UJg))
  | .priv _ adj => (if adj then ninv (privMacro nd ar) else privMacro nd ar).map
      (NInstr.map (ePW ρ sw))

variable [Fintype V] [DecidableEq V] [Fintype S] [DecidableEq S] [Fintype Sel] [DecidableEq Sel]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]

/-- The released semantics with `U_J` from its gates and a selected private
operation (`Dfam false`) and its inverse (`Dfam true`). -/
def evalSel (ρ : RelW V a) (UJg : List (Gate (Fin a ⊕ S))) (sw : SelWires ρ Sel)
    (Dfam : Bool → Cfg Sel → (Reg (Fin a) (Reg S R) →L[ℂ] Reg (Fin a) (Reg S R))) :
    Instr V → Reg V (Reg S R) →L[ℂ] Reg V (Reg S R)
  | .gate g => gateOp g.cs g.t g.u
  | .uj _ adj => selOracle ρ (noSel ρ) (fun _ => if adj then (UJop UJg)† else UJop UJg)
  | .priv _ adj => selOracle ρ sw (Dfam adj)

end Macro

end

end SparseHamiltonian.GateNative
