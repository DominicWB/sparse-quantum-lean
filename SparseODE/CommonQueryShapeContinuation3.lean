import SparseODE.CommonQueryShapeContinuation2

/-!
# Modular erasure of the concrete native Cayley circuits

Every compiler boundary is discharged by a small structural theorem. In
particular, the kernel never needs to unfold the complete concrete 24-query
or 72-query circuit, its fixed matrix gates, and all its register layouts in
one definitional-equality check.
-/

namespace SparseHamiltonian.CommonQueryShape

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct

variable {L X P K : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- The shape of a single-oracle program, with its eventual native label. -/
def singleErase {O : X → K →L[ℂ] K} (l : L) : OracleCircuit.Program O → Shape L
  | .fixed _ _ => .fixed
  | .query => .query l
  | .queryAdjoint => .queryAdjoint l
  | .seq p q => .seq (singleErase l p) (singleErase l q)

theorem singleErase_transport {O : X → P →L[ℂ] P} (l : L)
    (e : P ≃ₗᵢ[ℂ] K) (p : OracleCircuit.Program O) :
    singleErase l (p.transport e) = singleErase l p := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq =>
    simp only [OracleCircuit.Program.transport, singleErase, hp, hq]

theorem singleErase_retarget {O : X → K →L[ℂ] K} (l : L)
    (O' : X → K →L[ℂ] K) (p : OracleCircuit.Program O) :
    singleErase l (p.retarget O') = singleErase l p := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq =>
    simp only [OracleCircuit.Program.retarget, singleErase, hp, hq]

/-- Lifting the fixed gates, with a single physical query as the implementation,
leaves the complete query syntax unchanged. -/
theorem singleErase_compile_query {O : X → K →L[ℂ] K} {F : X → P →L[ℂ] P}
    (l : L) (E : P →L[ℂ] K) (hE : E† ∘L E = 1)
    (p : OracleCircuit.Program F) :
    singleErase l (EncodedOracle.compile E hE
      (.query : OracleCircuit.Program O) p) = singleErase l p := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq =>
    simp only [EncodedOracle.compile, singleErase, hp, hq]

theorem erase_embed_single {O : L → X → K →L[ℂ] K} (l : L)
    (p : OracleCircuit.Program (O l)) :
    erase (MultiOracleCircuit.Program.embed l p) = singleErase l p := by
  induction p with
  | fixed U hU => rfl
  | query => rfl
  | queryAdjoint => rfl
  | seq p q hp hq =>
    simp only [MultiOracleCircuit.Program.embed, erase, singleErase, hp, hq]

end
end SparseHamiltonian.CommonQueryShape
