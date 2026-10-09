import GateEfficientNative.Model.Flatten

/-!
# Instructions that do not touch a set of wires

An elementary gate changes only its target wire, a primitive call only the
wires it is placed on.  If no instruction of a circuit changes a wire of the
set `bad`, the circuit and its inverse keep every vector supported on the
configurations that are zero on `bad` (`pres2_nrun_zeroOn`).
-/

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

namespace SparseHamiltonian.GateNative

noncomputable section
open ContinuousLinearMap OracleCircuit GateCircuit
open GateODE (overwrite_apply_out adjIf)
open scoped InnerProduct BigOperators

variable {V V' Y J : Type*}

/-- The configuration is zero on the wires `bad`. -/
def ZeroOn (bad : V → Prop) (x : Cfg V) : Prop := ∀ w, bad w → x w = false

/-- The instruction may change a wire of `bad`. -/
def NInstr.Touches (bad : V → Prop) : NInstr V Y J → Prop
  | .gate g => bad g.t
  | .call _ _ pos => ∃ y, bad (pos y)

theorem NInstr.touches_inv (bad : V → Prop) (i : NInstr V Y J) :
    i.inv.Touches bad ↔ i.Touches bad := by
  cases i <;> exact Iff.rfl

theorem NInstr.not_touches_map (bad : V' → Prop) (f : V ↪ V') (hf : ∀ v, ¬ bad (f v))
    (i : NInstr V Y J) : ¬ (i.map f).Touches bad := by
  cases i with
  | gate g => exact hf g.t
  | call j adj pos =>
      rintro ⟨y, hy⟩
      exact hf (pos y) hy

section Pres

variable [Fintype V] [DecidableEq V] [Fintype Y] [DecidableEq Y]
variable {R : Type*} [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
variable (prim : J → Reg Y R →L[ℂ] Reg Y R)

theorem preserves_eval_zeroOn (bad : V → Prop) (i : NInstr V Y J) (hi : ¬ i.Touches bad) :
    Preserves (ZeroOn bad) (i.eval prim) := by
  cases i with
  | gate g =>
      have ht : ¬ bad g.t := hi
      change Preserves (ZeroOn bad) (gateOp g.cs g.t g.u)
      unfold gateOp
      apply preserves_condOp
      intro x b hx w hw
      rw [Function.update_of_ne (fun (h : w = g.t) => ht (h ▸ hw))]
      exact hx w hw
  | call j adj pos =>
      have ht : ∀ y, ¬ bad (pos y) := fun y hy => hi ⟨y, hy⟩
      change Preserves (ZeroOn bad) (localOp pos pos.injective (fun _ => adjIf adj (prim j)))
      apply preserves_localOp
      intro y b hy w hw
      rw [overwrite_apply_out (⇑pos) y b w (fun c (hc : pos c = w) => ht c (hc ▸ hw))]
      exact hy w hw

theorem preserves_nrun_zeroOn (bad : V → Prop) (is : List (NInstr V Y J))
    (h : ∀ i ∈ is, ¬ i.Touches bad) : Preserves (ZeroOn bad) (nrun prim is) := by
  induction is with
  | nil => exact Preserves.one _
  | cons i is ih =>
      rw [nrun_cons]
      exact (preserves_eval_zeroOn prim bad i (h i List.mem_cons_self)).comp
        (ih (fun i' hi' => h i' (List.mem_cons_of_mem i hi')))

/-- **A circuit that does not touch `bad` keeps `bad` clean**, and so does its
inverse. -/
theorem pres2_nrun_zeroOn (bad : V → Prop) (is : List (NInstr V Y J))
    (h : ∀ i ∈ is, ¬ i.Touches bad) : Pres2 (ZeroOn bad) (nrun prim is) := by
  refine ⟨preserves_nrun_zeroOn prim bad is h, ?_⟩
  rw [← nrun_ninv]
  apply preserves_nrun_zeroOn prim bad
  intro i hi
  simp only [ninv, List.mem_reverse, List.mem_map] at hi
  obtain ⟨i', hi', rfl⟩ := hi
  rw [NInstr.touches_inv]
  exact h i' hi'

end Pres

end

end SparseHamiltonian.GateNative
