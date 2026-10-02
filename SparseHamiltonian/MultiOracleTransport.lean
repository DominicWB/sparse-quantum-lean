import SparseHamiltonian.MultiWeightedProgramClockBounds

/-! # Fixed representation changes for explicitly labeled native programs -/
namespace SparseHamiltonian.MultiOracleCircuit.Program

noncomputable section
open OracleCircuit

variable {H K X L : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {O : L → X → H →L[ℂ] H}

/-- Change coordinates uniformly, preserving each native label and each query. -/
def transport (e : H ≃ₗᵢ[ℂ] K) : Program O →
    Program (fun l x => e.conjStarAlgEquiv (O l x))
  | .fixed U hU => .fixed (e.conjStarAlgEquiv U) (hU.transport e)
  | .query l => .query l
  | .queryAdjoint l => .queryAdjoint l
  | .seq p q => .seq (transport e p) (transport e q)

@[simp] theorem count_transport (e : H ≃ₗᵢ[ℂ] K) (p : Program O) :
    (p.transport e).count = p.count := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [transport, count_seq, hp, hq]

@[simp] theorem cost_transport (e : H ≃ₗᵢ[ℂ] K) (p : Program O) (w : L → ℕ) :
    (p.transport e).cost w = p.cost w := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => rfl
  | seq p q hp hq => simp only [transport, cost_seq, hp, hq]

@[simp] theorem labelCount_transport [DecidableEq L] (e : H ≃ₗᵢ[ℂ] K)
    (p : Program O) (l : L) : (p.transport e).labelCount l = p.labelCount l := cost_transport e p _

/-- Exact evaluation under the public change of coordinates. -/
@[simp] theorem eval_transport (e : H ≃ₗᵢ[ℂ] K) (p : Program O) (x : X) :
    (p.transport e).eval x = e.conjStarAlgEquiv (p.eval x) := by
  induction p with
  | fixed U hU => rfl
  | query l => rfl
  | queryAdjoint l => exact (map_star e.conjStarAlgEquiv _).symm
  | seq p q hp hq => simp only [transport, eval_seq, hp, hq, map_mul]

/-- Full-space involutions remain exact after register flattening. -/
theorem involution_transport (e : H ≃ₗᵢ[ℂ] K) (p : Program O) (x : X)
    (hp : p.eval x * p.eval x = 1) :
    (p.transport e).eval x * (p.transport e).eval x = 1 := by
  rw [eval_transport, ← map_mul, hp, map_one]

/-- Hermiticity is also preserved on the complete new workspace. -/
theorem selfAdjoint_transport (e : H ≃ₗᵢ[ℂ] K) (p : Program O) (x : X)
    (hp : star (p.eval x) = p.eval x) :
    star ((p.transport e).eval x) = (p.transport e).eval x := by
  rw [eval_transport, ← map_star, hp]

end
end SparseHamiltonian.MultiOracleCircuit.Program
