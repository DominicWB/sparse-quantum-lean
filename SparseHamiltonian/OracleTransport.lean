import SparseHamiltonian.RegisterEquivalences

/-!
# Fixed Hilbert-space transport of uniform query programs

A table-independent unitary equivalence changes the representation of every
gate and oracle letter.  The resulting program has exactly the same number of
queries; no control or oracle-dependent change of coordinates is introduced.
-/

namespace SparseHamiltonian.OracleCircuit
noncomputable section

variable {H K X : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Both unitary identities survive a fixed isometric change of coordinates. -/
theorem IsUnitary.transport {U : H →L[ℂ] H} (hU : IsUnitary U)
    (e : H ≃ₗᵢ[ℂ] K) : IsUnitary (e.conjStarAlgEquiv U) := by
  constructor
  · have h := congrArg e.conjStarAlgEquiv hU.1
    simpa only [map_mul, map_star, map_one] using h
  · have h := congrArg e.conjStarAlgEquiv hU.2
    simpa only [map_mul, map_star, map_one] using h

namespace Program
variable {O : X → H →L[ℂ] H}

/-- Conjugate each gate and oracle by the same fixed register equivalence. -/
def transport (e : H ≃ₗᵢ[ℂ] K) : Program O →
    Program (fun x => e.conjStarAlgEquiv (O x))
  | .fixed U hU => .fixed (e.conjStarAlgEquiv U) (hU.transport e)
  | .query => .query
  | .queryAdjoint => .queryAdjoint
  | .seq p q => .seq (transport e p) (transport e q)

@[simp] theorem count_transport (e : H ≃ₗᵢ[ℂ] K) (p : Program O) :
    (p.transport e).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq => simp only [transport, count_seq, hp, hq]

/-- Evaluation is exactly the fixed conjugation of the original computation. -/
@[simp] theorem eval_transport (e : H ≃ₗᵢ[ℂ] K) (p : Program O) (x : X) :
    (p.transport e).eval x = e.conjStarAlgEquiv (p.eval x) := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => exact (map_star e.conjStarAlgEquiv (O x)).symm
  | seq p q hp hq => simp only [transport, eval_seq, hp, hq, map_mul]

end Program

/-- A fixed Hilbert-space reindexing preserves an implementation's query bound. -/
theorem Implements.transport {O F : X → H →L[ℂ] H} {q : ℕ}
    (h : Implements O F q) (e : H ≃ₗᵢ[ℂ] K) :
    Implements (fun x => e.conjStarAlgEquiv (O x))
      (fun x => e.conjStarAlgEquiv (F x)) q := by
  obtain ⟨p, hp, hq⟩ := h
  refine ⟨p.transport e, ?_, ?_⟩
  · intro x
    rw [Program.eval_transport, hp x]
  · simpa only [Program.count_transport] using hq

end
end SparseHamiltonian.OracleCircuit
