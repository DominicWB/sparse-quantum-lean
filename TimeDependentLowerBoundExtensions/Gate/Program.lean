import TimeDependentLowerBoundExtensions.Core.Masked
import GateEfficientTimeDependent.Theorem

set_option autoImplicit false

/-!
# Gate-level time-dependent circuits as oracle programs

The manuscript states its gate-level theorem (Theorem `hs:thm:gates`, line 1814, with the time
slots of line 1801) for time-independent Hamiltonians only (line 1849). The package's gate-level
time-dependent circuits (`SparseHamiltonian.GateCircuit.SlotSim.gate_efficient_time_simulation`,
the slot-selected private Cayley operation) run instruction lists `gs`
(`SparseHamiltonian.GateCircuit.Instr`): elementary gates, calls of the public unitary `U_J` and
slot-selected private calls `slotOracle cs D` with literal controls `cs`, each private call,
forward or inverse, counted once (`nPriv gs`). On a hard path constant in time (the manuscript,
lines 1512-1516) the private operation is the same at every slot, `D k = D_x`.

* `privFamily D`: the labelled family of private calls, one label per list of literal controls;
* `slotOracle_const_eq`: a constant private call is a masked call of `D_x` in one fixed layout
  of the wires (`localOp` is a block diagonal over the configurations of the other wires), the
  same layout for every list of controls;
* `exists_program`: for public `U_J` and valid instructions, every instruction list is a program
  over `privFamily D` with `nPriv gs` calls and the same operator as `runT U_J D gs`.
-/

namespace TimeDependentLowerBoundExtensions.Gate

noncomputable section

open SparseHamiltonian OracleCircuit
open SparseHamiltonian.GateCircuit SparseHamiltonian.GateCircuit.Sim
  SparseHamiltonian.GateCircuit.SlotSim
open scoped InnerProduct InnerProductSpace

variable {a m r K : ℕ}
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

/-- **The family of private calls** of a private operation constant in time: the label `cs`
(literal controls) on input `x` is `slotOracle cs (fun _ => D_x)`. -/
def privFamily {X : Type*} (Dp : X → Vsp a P →L[ℂ] Vsp a P) :
    List (Wire a m r K × Bool) → X → Reg (Wire a m r K) P →L[ℂ] Reg (Wire a m r K) P :=
  fun cs x => slotOracle cs (fun _ => Dp x)

/-- **A constant private call is a masked call in one fixed layout**: there are a finite
branch register `ι` (the configurations of the non-ancilla wires) and one fixed isometric
identification `L` of the wires with `ℂ^ι ⊗ Vsp a P` such that every private call with controls
`cs` of a constant operation `A` is `L⁻¹ (masked m_cs A) L`. -/
theorem slotOracle_const_eq :
    ∃ (ι : Type) (_ : Fintype ι)
      (L : Reg (Wire a m r K) P ≃ₗᵢ[ℂ] SparseLowerBounds.Joint ι (Vsp a P)),
      ∀ cs : List (Wire a m r K × Bool), ∃ msk : ι → Bool, ∀ A : Vsp a P →L[ℂ] Vsp a P,
        slotOracle cs (fun _ => A) = L.symm.conjStarAlgEquiv (MaskedProgram.masked msk A) := by
  refine ⟨Cfg (Out (Wire.anc : Fin a → Wire a m r K)), _,
    layout (Q := P) Wire.anc anc_injective, fun cs => ⟨fun x' => ctrlOK cs (joinCfg Wire.anc x'
      (fun _ => false)), fun A => ?_⟩⟩
  rw [slotOracle, localOp, MaskedProgram.masked]

/-- **Gate-level circuits are oracle programs**: for a public unitary `U_J`, a private operation
constant in time (any operators) and an instruction list of valid instructions, there is a program
over `privFamily D` with exactly `nPriv gs` calls whose operator is `runT U_J D gs` on every
input. -/
theorem exists_program {X : Type*} (UJ : Vsp a P →L[ℂ] Vsp a P) (hUJ : IsUnitary UJ)
    (Dp : X → Vsp a P →L[ℂ] Vsp a P)
    (gs : List (Instr (Wire a m r K))) (hgs : ∀ g ∈ gs, g.Valid Wire.anc) :
    ∃ p : MultiOracleCircuit.Program (privFamily (m := m) (r := r) (K := K) Dp),
      (∀ x, p.eval x = runT UJ (fun _ => Dp x) gs) ∧ p.count = nPriv gs := by
  induction gs with
  | nil => exact ⟨.identity, fun _ => rfl, rfl⟩
  | cons g gs ih =>
    obtain ⟨p, hp, hc⟩ := ih (fun g' hg' => hgs g' (List.mem_cons_of_mem g hg'))
    have hg := hgs g List.mem_cons_self
    have key : ∃ pg : MultiOracleCircuit.Program (privFamily (m := m) (r := r) (K := K) Dp),
        (∀ x, pg.eval x = evalT UJ (fun _ => Dp x) g) ∧
          pg.count = if g.isPriv then 1 else 0 := by
      cases g with
      | gate g' => exact ⟨.fixed _ (gateOp_isUnitary g'.cs g'.t g'.u hg.2.2), fun _ => rfl, rfl⟩
      | uj cs adj =>
        have hU : IsUnitary (if adj then UJ† else UJ) := by
          cases adj
          · exact hUJ
          · exact hUJ.adjoint
        exact ⟨.fixed _ (oracleOp_isUnitary Wire.anc anc_injective cs _ hU), fun _ => rfl, rfl⟩
      | priv cs adj =>
        cases adj
        · exact ⟨.query cs, fun _ => rfl, rfl⟩
        · refine ⟨.queryAdjoint cs, fun x => ?_, rfl⟩
          change (slotOracle cs (fun _ => Dp x))† = slotOracle cs (fun _ => (Dp x)†)
          exact slotOracle_adjoint cs _
    obtain ⟨pg, hpg, hcg⟩ := key
    refine ⟨.seq p pg, fun x => ?_, ?_⟩
    · rw [MultiOracleCircuit.Program.eval_seq, hp, hpg, runT_cons]
      rfl
    · rw [MultiOracleCircuit.Program.count_seq, hc, hcg, nPriv, nPriv, List.countP_cons]

end

end TimeDependentLowerBoundExtensions.Gate
