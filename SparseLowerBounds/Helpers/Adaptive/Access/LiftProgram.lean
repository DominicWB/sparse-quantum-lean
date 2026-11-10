import SparseLowerBounds.Helpers.CompileReduction.AncillaCircuit

set_option synthInstance.maxHeartbeats 400000

section
/-!
# Helper: lifting a uniform program to an untouched spectator register

For `Adaptive/Access`. A program `p` over a uniform oracle family `Q` on `K`
runs unchanged on every copy of a spectator register `ℂ^Ω`: replace each
fixed gate `U` by `1_Ω ⊗ U = Joint.fiber (fun _ => U)` and keep every oracle
letter, now a letter of the spectated family `x ↦ 1_Ω ⊗ Q x`. The lifted
program evaluates to `1_Ω ⊗ p.eval x` (`eval_liftProgram`) and makes exactly
the same number of oracle calls (`count_liftProgram`). This is the
spectator case of the purification remark of the manuscript
(proof of Lemma `qlsl:lem:xor`): untouched registers cost no queries.
-/

namespace SparseLowerBounds.Helpers.Adaptive.Access

noncomputable section
set_option autoImplicit false
open SparseHamiltonian OracleCircuit

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {X : Type*}

/-- Lift a program over `Q` to the spectated family `x ↦ 1_Ω ⊗ Q x`: fixed
gates become `1_Ω ⊗ U`, oracle letters stay oracle letters. -/
def liftProgram (Ω : Type*) [Fintype Ω] {Q : X → K →L[ℂ] K} :
    Program Q → Program (fun x => Joint.fiber (fun _ : Ω => Q x))
  | .fixed U hU => .fixed (Joint.fiber fun _ : Ω => U)
      (CompileReduction.isUnitary_fiber _ fun _ => hU)
  | .query => .query
  | .queryAdjoint => .queryAdjoint
  | .seq p q => .seq (liftProgram Ω p) (liftProgram Ω q)

/-- The lifted program evaluates to `1_Ω ⊗ p.eval x`. -/
theorem eval_liftProgram (Ω : Type*) [Fintype Ω] {Q : X → K →L[ℂ] K} (p : Program Q)
    (x : X) : (liftProgram Ω p).eval x = Joint.fiber (fun _ : Ω => p.eval x) := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint =>
      simp only [liftProgram, Program.eval_queryAdjoint, Joint.star_fiber]
  | seq p q hp hq =>
      simp only [liftProgram, Program.eval_seq, hp, hq, Joint.fiber_mul]

/-- Lifting to a spectator register makes the same number of oracle calls. -/
@[simp] theorem count_liftProgram (Ω : Type*) [Fintype Ω] {Q : X → K →L[ℂ] K}
    (p : Program Q) : (liftProgram Ω p).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq => simp only [liftProgram, Program.count_seq, hp, hq]

end

end SparseLowerBounds.Helpers.Adaptive.Access
end
