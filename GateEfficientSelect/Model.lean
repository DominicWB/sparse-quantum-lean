import GateEfficientODE.Time.Theorem

/-!
# Label-selected circuits of the released simulator

Lemma `ode:lem:gate-select` of the accompanying paper selects coherently, from a label `z`,
one time-dependent branch of the released gate-level simulator. Here the label register is an
arbitrary finite set `L` of qubit wires beside the simulator wires `Wire a m r K`
(`SW a m r K L`). The instructions are those of the released simulator
(`GateCircuit.Instr`), read as follows (`evalS`):

* an elementary gate acts on the simulator wires; it is the renamed elementary gate of the
  whole register (`evalS_gate`);
* a call of `U_J` or `U_J†` acts on the simulator wires as in the released simulator, whatever
  the label;
* a private call applies, on every configuration whose label wires carry `z` and whose slot
  wires carry the slot `j`, the supplied unitary `D z j` (or its adjoint) to the ancilla slice
  under the literal controls (label- and slot-selected); one call is one instruction.

On every configuration of the label wires the circuit acts as the released slot-selected
simulator `GateCircuit.SlotSim.runT` of the selected label (`runS_eq`). The circuits are the
released instruction lists, so validity and every count are those of the released circuit, and
none of them depends on the label wires. The inverse instruction list runs as the adjoint
(`runS_invList`).

`selE` places a label `z` and a payload vector on the configuration carrying `z` with every
simulator wire clear; it is an isometry (`selE_isometry`). The selected circuit is within `ε` of
the direct sum `∑_z |z⟩⟨z| ⊗ U z` on this clean-input space, with the full output compared
(every simulator wire must return clean), as soon as the released simulator of every label is
within `ε` of `U z` on its clean column (`select_error`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GateSelect

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateCircuit.Sim (Wire Vsp anc_injective io io_apply)
open GateODE (basL basL_apply branchEmb branchEmb_isometry localOp_branch_error
  overwrite_apply_out)
open scoped InnerProduct BigOperators

variable {a m r K : ℕ} {L : Type*} [Fintype L] [DecidableEq L]
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- The wires of a label-selected simulator: the simulator wires and the label wires. -/
abbrev SW (a m r K : ℕ) (L : Type*) := Wire a m r K ⊕ L

/-- The label carried by a configuration. -/
def labelOf (x : Cfg (SW a m r K L)) : Cfg L := fun l => x (Sum.inr l)

/-- One instruction of the released simulator on the simulator wires, with the private call
selected by the label wires and the slot wires. -/
def evalS (UJ : Vsp a P →L[ℂ] Vsp a P) (D : Cfg L → ℕ → Vsp a P →L[ℂ] Vsp a P)
    (i : Instr (Wire a m r K)) : Reg (SW a m r K L) P →L[ℂ] Reg (SW a m r K L) P :=
  localOp Sum.inl Sum.inl_injective (fun x => SlotSim.evalT UJ (D (labelOf x)) i)

/-- Run a label-selected circuit: the head instruction acts first. -/
def runS (UJ : Vsp a P →L[ℂ] Vsp a P) (D : Cfg L → ℕ → Vsp a P →L[ℂ] Vsp a P) :
    List (Instr (Wire a m r K)) → Reg (SW a m r K L) P →L[ℂ] Reg (SW a m r K L) P
  | [] => 1
  | g :: gs => runS UJ D gs ∘L evalS UJ D g

section Run

variable (UJ : Vsp a P →L[ℂ] Vsp a P) (D : Cfg L → ℕ → Vsp a P →L[ℂ] Vsp a P)

/-- An elementary gate of the simulator is the renamed elementary gate of the whole
register. -/
theorem evalS_gate (g : Gate (Wire a m r K)) :
    evalS UJ D (.gate g) = (GateODE.Gate.map (Sum.inl : Wire a m r K → SW a m r K L) g).op :=
  GateODE.Gate.map_op Sum.inl_injective g

/-- On every configuration of the label wires, the circuit acts as the released slot-selected
simulator of the selected label. -/
theorem runS_eq (gs : List (Instr (Wire a m r K))) :
    runS UJ D gs =
      localOp Sum.inl Sum.inl_injective (fun x => SlotSim.runT UJ (D (labelOf x)) gs) := by
  induction gs with
  | nil => exact (localOp_one Sum.inl_injective).symm
  | cons g gs ih =>
      rw [runS, ih, evalS, localOp_comp]
      rfl

/-- The inverse instruction list runs as the adjoint. -/
theorem runS_invList (gs : List (Instr (Wire a m r K))) :
    runS UJ D (invList gs) = (runS UJ D gs)† := by
  rw [runS_eq, runS_eq, localOp_adjoint]
  congr 1
  funext x
  exact SlotSim.runT_invList _ _ gs

/-- A circuit of valid instructions with unitary supplied operations is unitary. -/
theorem runS_isUnitary (hUJ : IsUnitary UJ) (hD : ∀ z, ∀ j < 2 ^ m, IsUnitary (D z j))
    (gs : List (Instr (Wire a m r K))) (hgs : ∀ g ∈ gs, g.Valid Wire.anc) :
    IsUnitary (runS UJ D gs) := by
  rw [runS_eq]
  exact localOp_isUnitary _ _ (fun x => SlotSim.runT_isUnitary UJ _ hUJ (hD _) gs hgs)

end Run

/-! ### The clean label space -/

/-- The configuration carrying the label `z`, every simulator wire clear. -/
def labCfg (z : Cfg L) : Cfg (SW a m r K L) := Sum.elim (fun _ => false) z

omit [Fintype L] [DecidableEq L] in
theorem labCfg_injective :
    Function.Injective (labCfg (a := a) (m := m) (r := r) (K := K) (L := L)) := by
  intro z z' h
  funext l
  exact congrFun h (Sum.inr l)

omit [Fintype L] [DecidableEq L] in
theorem outPart_labCfg_injective (z z' : Cfg L)
    (h : outPart Sum.inl (labCfg (a := a) (m := m) (r := r) (K := K) z) =
      outPart Sum.inl (labCfg z')) : z = z' := by
  funext l
  exact congrFun h ⟨Sum.inr l, fun s hs => by cases hs⟩

omit [Fintype L] in
/-- Clearing the simulator wires of the label configuration keeps the label. -/
theorem labelOf_clear (z : Cfg L) :
    labelOf (clearCfg Sum.inl (labCfg (a := a) (m := m) (r := r) (K := K) z)) = z := by
  funext l
  change clearCfg Sum.inl (labCfg (a := a) (m := m) (r := r) (K := K) z) (Sum.inr l) = z l
  exact overwrite_apply_out Sum.inl (labCfg (a := a) (m := m) (r := r) (K := K) z)
    (fun _ => false) (Sum.inr l) (fun s hs => by cases hs)

/-- The clean-input space: a label and a payload vector, every simulator wire clear. -/
def selE : ODEJointLCU.BranchSpace (Cfg L) P →L[ℂ] Reg (SW a m r K L) P := branchEmb labCfg

theorem selE_isometry :
    (selE (a := a) (m := m) (r := r) (K := K) (L := L) (P := P))† ∘L selE = 1 :=
  branchEmb_isometry _ labCfg_injective

/-- **The block estimate of coherent selection.** If the released slot-selected simulator of
every label `z` is within `ε` of `U z` on its clean column, the label-selected circuit is
within `ε` of the direct sum `∑_z |z⟩⟨z| ⊗ U z` on the clean-input space, with the full output
compared. -/
theorem select_error (UJ : Vsp a P →L[ℂ] Vsp a P) (D : Cfg L → ℕ → Vsp a P →L[ℂ] Vsp a P)
    (gs : List (Instr (Wire a m r K))) (U : Cfg L → P →L[ℂ] P) (ε : ℝ) (hε : 0 ≤ ε)
    (hblock : ∀ z, ‖SlotSim.runT UJ (D z) gs ∘L io - io ∘L U z‖ ≤ ε) :
    ‖runS UJ D gs ∘L selE - selE ∘L WeightedClock.diagonal U‖ ≤ ε := by
  rw [runS_eq]
  apply localOp_branch_error Sum.inl_injective _ labCfg (fun _ _ => rfl)
    outPart_labCfg_injective _ ε hε
  intro z
  rw [labelOf_clear]
  have hio : basL (W := Wire a m r K) (Q := P) (fun _ => false) = io := by
    refine ContinuousLinearMap.ext (fun ψ => ?_)
    rw [basL_apply, io_apply]
  rw [hio]
  exact hblock z

omit [DecidableEq L] in
/-- The label-selected register has the simulator wires and the label wires. -/
theorem card_SW : Fintype.card (SW a m r K L) = Fintype.card (Wire a m r K) + Fintype.card L :=
  Fintype.card_sum

end

end SparseHamiltonian.GateSelect
