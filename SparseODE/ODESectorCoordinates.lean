import SparseODE.ODECountedSourceCertificate

/-!
# Query-preserving coordinates for the source/matrix direct sum

Both register equivalences are fixed independently of the oracle input.
This compiler connects the abstract source-loading workspace to finite
computational coordinates without adding queries or assuming controlled access.
-/
namespace SparseHamiltonian.ODESectorCoordinates

noncomputable section
open ContinuousLinearMap OracleCircuit
open scoped InnerProduct
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

variable {B K B' K' X L : Type*}
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup B'] [InnerProductSpace ℂ B'] [CompleteSpace B']
  [NormedAddCommGroup K'] [InnerProductSpace ℂ K'] [CompleteSpace K']

def layout (eB : B ≃ₗᵢ[ℂ] B') (eK : K ≃ₗᵢ[ℂ] K') :
    ODESourceTransport.Space B K ≃ₗᵢ[ℂ] ODESourceTransport.Space B' K' :=
  LinearIsometryEquiv.withLpProdCongr 2 eB eK

omit [CompleteSpace B] [CompleteSpace K] [CompleteSpace B'] [CompleteSpace K'] in
@[simp] theorem layout_apply (eB : B ≃ₗᵢ[ℂ] B') (eK : K ≃ₗᵢ[ℂ] K')
    (v : ODESourceTransport.Space B K) :
    layout eB eK v = WithLp.toLp 2 (eB v.fst, eK v.snd) := rfl

theorem matrix_intertwines (eB : B ≃ₗᵢ[ℂ] B') (eK : K ≃ₗᵢ[ℂ] K')
    (U : K →L[ℂ] K) :
    ODESourceTransport.matrixGate (B := B') (eK.conjStarAlgEquiv U) ∘L
        (layout eB eK).toLinearIsometry.toContinuousLinearMap =
      (layout eB eK).toLinearIsometry.toContinuousLinearMap ∘L ODESourceTransport.matrixGate U := by
  ext v
  change ODESourceTransport.matrixGate (eK.conjStarAlgEquiv U) (layout eB eK v) =
    layout eB eK (ODESourceTransport.matrixGate U v)
  simp only [layout_apply, ODESourceTransport.matrixGate_apply, WithLp.fst, WithLp.snd]
  change WithLp.toLp 2 (eB v.ofLp.1, eK (U (eK.symm (eK v.ofLp.2)))) =
    WithLp.toLp 2 (eB v.ofLp.1, eK (U v.ofLp.2))
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem source_intertwines (eB : B ≃ₗᵢ[ℂ] B') (eK : K ≃ₗᵢ[ℂ] K')
    (S : B →L[ℂ] B) :
    ODESourceTransport.sourceGate (K := K') (eB.conjStarAlgEquiv S) ∘L
        (layout eB eK).toLinearIsometry.toContinuousLinearMap =
      (layout eB eK).toLinearIsometry.toContinuousLinearMap ∘L ODESourceTransport.sourceGate S := by
  ext v
  change ODESourceTransport.sourceGate (eB.conjStarAlgEquiv S) (layout eB eK v) =
    layout eB eK (ODESourceTransport.sourceGate S v)
  simp only [layout_apply, ODESourceTransport.sourceGate_apply, WithLp.fst, WithLp.snd]
  change WithLp.toLp 2 (eB (S (eB.symm (eB v.ofLp.1))), eK v.ofLp.2) =
    WithLp.toLp 2 (eB (S v.ofLp.1), eK v.ofLp.2)
  rw [LinearIsometryEquiv.symm_apply_apply]

def oracle (O : L → X → K →L[ℂ] K) (S : Bool → X → B →L[ℂ] B) :
    L ⊕ Bool → X → ODESourceTransport.Space B K →L[ℂ]
      ODESourceTransport.Space B K :=
  Sum.elim (fun l x => ODESourceTransport.matrixGate (O l x))
    (fun b x => ODESourceTransport.sourceGate (S b x))

theorem oracle_unitary (O : L → X → K →L[ℂ] K) (S : Bool → X → B →L[ℂ] B)
    (hO : ∀ l x, IsUnitary (O l x)) (hS : ∀ b x, IsUnitary (S b x)) :
    ∀ l x, IsUnitary (oracle O S l x) := by
  intro l x
  cases l with
  | inl l => exact ODESourceTransport.matrixGate_unitary (O l x) (hO l x)
  | inr b => exact ODESourceTransport.sourceGate_unitary (S b x) (hS b x)

def flatOracle (eB : B ≃ₗᵢ[ℂ] B') (eK : K ≃ₗᵢ[ℂ] K')
    (O : L → X → K →L[ℂ] K) (S : Bool → X → B →L[ℂ] B) :=
  oracle (fun l x => eK.conjStarAlgEquiv (O l x))
    (fun b x => eB.conjStarAlgEquiv (S b x))

/-- Only the representation of each register changes; every label is retained. -/
def compile (eB : B ≃ₗᵢ[ℂ] B') (eK : K ≃ₗᵢ[ℂ] K')
    (O : L → X → K →L[ℂ] K) (S : Bool → X → B →L[ℂ] B)
    (p : MultiOracleCircuit.Program (oracle O S)) :
    MultiOracleCircuit.Program (flatOracle eB eK O S) :=
  EncodedLabeledProgram.compile (layout eB eK).toLinearIsometry.toContinuousLinearMap
    (layout eB eK).toLinearIsometry.adjoint_comp_self (fun l => .query l) p

theorem compile_cost (eB : B ≃ₗᵢ[ℂ] B') (eK : K ≃ₗᵢ[ℂ] K')
    (O : L → X → K →L[ℂ] K) (S : Bool → X → B →L[ℂ] B)
    (p : MultiOracleCircuit.Program (oracle O S)) (w : L ⊕ Bool → ℕ) :
    (compile eB eK O S p).cost w = p.cost w := by
  simp only [compile, EncodedLabeledProgram.compile_cost,
    MultiOracleCircuit.Program.cost_query]

theorem compile_eval (eB : B ≃ₗᵢ[ℂ] B') (eK : K ≃ₗᵢ[ℂ] K')
    (O : L → X → K →L[ℂ] K) (S : Bool → X → B →L[ℂ] B)
    (hO : ∀ l x, IsUnitary (O l x)) (hS : ∀ b x, IsUnitary (S b x))
    (p : MultiOracleCircuit.Program (oracle O S)) (x : X) :
    (compile eB eK O S p).eval x ∘L (layout eB eK).toLinearIsometry.toContinuousLinearMap =
      (layout eB eK).toLinearIsometry.toContinuousLinearMap ∘L p.eval x := by
  apply EncodedLabeledProgram.compile_eval
  · exact oracle_unitary _ _ (fun l y => (hO l y).transport eK)
      (fun b y => (hS b y).transport eB)
  · exact oracle_unitary O S hO hS
  · intro l y
    cases l with
    | inl l => exact matrix_intertwines eB eK (O l y)
    | inr b => exact source_intertwines eB eK (S b y)

end
end SparseHamiltonian.ODESectorCoordinates
