import SparseHamiltonian.MaskedProgram

/-!
# Control of complete lookup programs from ordinary queries

The source program uses the target lookup; the physical program queries an
ordinary scratch lookup. A fixed branch mask is compiled through every gate,
then the proved two-query lookup construction replaces every masked query.
The mask and all free gates are independent of the unknown table.
-/

namespace SparseHamiltonian.LookupProgramControl

noncomputable section
open OracleCircuit MaskedLookupCurry

variable {X I A Z : Type*} [Fintype I] [Fintype A] [Fintype Z] [AddCommGroup Z]

/-- An arbitrary fixed control of a q-query lookup implementation costs at
most 2q ordinary lookup queries, with exact full-workspace semantics. -/
theorem implements_masked (f : X → A → Z) (active : I → Bool)
    {F : X → Payload A Z →L[ℂ] Payload A Z} {q : ℕ}
    (h : Implements (localSigned 1 f) F q) :
    Implements (oracle (I := I) f)
      (fun x => MaskedProgram.masked active (F x)) (2 * q) := by
  have hQuery : Implements (oracle (I := I) f)
      (fun x => MaskedProgram.masked active (localSigned 1 f x)) 2 :=
    masked_diagonal_two_queries active f
  simpa only [Nat.mul_comm] using
    MaskedProgram.implements_of_masked_query h active (oracle f) hQuery

/-- The resulting circuit is one uniform program, with an exact full-space
operator identity for every unknown table. -/
theorem program_certificate (f : X → A → Z) (active : I → Bool)
    (p : Program (localSigned 1 f)) :
    ∃ controlled : Program (oracle (I := I) f),
      (∀ x, controlled.eval x = MaskedProgram.masked active (p.eval x)) ∧
      controlled.count ≤ 2 * p.count :=
  implements_masked f active ⟨p, fun _ => rfl, le_rfl⟩

end
end SparseHamiltonian.LookupProgramControl
