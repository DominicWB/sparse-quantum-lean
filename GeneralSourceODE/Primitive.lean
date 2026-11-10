import GeneralSourceODE.Counted
import SparseODE.ODEPrimitiveSourceJoin

/-!
# The counted general-source algorithm on primitive matrix access

General-source counterpart of `TimeDependentODE.SourceTD.primitive_source_certificate`.
The trial family is the counted randomized amplification of the compiled
circuit of `Compiled.program`, whose two counted source interfaces are the
preparation `U_load ∘ (P_w ⊗ 1)` with public phases and the unpreparation
`P_w† ⊗ 1`. Its matrix-sector controls are compiled by the released concrete
compiler `ODECoordinateNativeControl.compile`. Accuracy, success and the
pre-compilation query bounds come from `Compiled.counted_source_certificate`;
the conclusion is the released `ODEPrimitiveSourceJoin.TrialCertificate`, with
the same constants.
-/

namespace SparseHamiltonian.GeneralSourceODE

noncomputable section
open ContinuousLinearMap OracleCircuit ODEStateNormalization
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

namespace Compiled

variable {ι P K X L : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : ℕ} {O : L → X → K →L[ℂ] K}

/-- The released transfer through the primitive-control compiler, packaged as
the released trial certificate for an arbitrary logical trial family. -/
theorem trialCertificate_of_transfer {A B H : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (eA : H ≃ₗᵢ[ℂ] EuclideanSpace ℂ A) (eB : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ B)
    (S : Bool → X → H →L[ℂ] H)
    (hO : ∀ l x, IsUnitary (O l x)) (hS : ∀ b x, IsUnitary (S b x))
    (a0 : A) (b0 : B) (image : L → X → B)
    (hvalid : ∀ l x, eB.conjStarAlgEquiv (O l x) (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image l x) 1)
    (q : ℕ → MultiOracleCircuit.Program (ODESectorCoordinates.oracle O S)) (M : ℕ)
    (ψ : ODESourceTransport.Space H K) (hψ : ‖ψ‖ = 1)
    (F : P →L[ℂ] ODESourceTransport.Space H K) (hF : F† ∘L F = 1)
    (x : X) (target : P) (s Θ ell g η : ℝ)
    (hM : 0 < M) (hMle : (M : ℝ) ≤ 5 * g)
    (hMatrix : ∀ j, j < M →
      ((q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
        106168320 * g * ImprovedODEQueryBudget.queryShape s Θ ell)
    (hSource : ∀ j, j < M → ∀ b : Bool,
      ((q j).cost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤ 10 * g)
    (hSourceTotal : ∀ j, j < M →
      ((q j).cost ODESourceQueryBudget.sourceTotalWeight : ℝ) ≤ 20 * g)
    (hSuccess : (1 : ℝ) / 4 ≤
      (∑ j ∈ Finset.range M,
        ‖ODEHeraldedSuccess.successProjector F ((q j).eval x ψ)‖ ^ 2) / (M : ℝ))
    (hDirection : ∀ j, j < M → (F†) ((q j).eval x ψ) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((F†) ((q j).eval x ψ)) - unitDirection target‖ ≤ η) :
    ODEPrimitiveSourceJoin.TrialCertificate
      (fun j => ODECoordinateNativeControl.compile eA eB O S a0 b0 (q j)) M
      (ODECoordinateNativeControl.input eA eB a0 b0 ψ)
      (ODECoordinateNativeControl.input eA eB a0 b0 ∘L F) x target s Θ ell g η := by
  have hNew := ODECoordinateNativeControl.transfer_certificate
    eA eB O S hO hS a0 b0 image hvalid q M ψ hψ F hF x target s Θ ell g η
    hMatrix hSource hSourceTotal hSuccess hDirection
  exact {
    cutoff_pos := hM
    cutoff_le := hMle
    seed_unit := hNew.1
    output_isometry := hNew.2.1
    matrix_queries := hNew.2.2.1
    source_queries := hNew.2.2.2.1
    total_source_queries := hNew.2.2.2.2.1
    mean_success := hNew.2.2.2.2.2.1
    direction_error := hNew.2.2.2.2.2.2 }

/-- The trial family in the logical oracle vocabulary of the primitive-control
compiler: the matrix family `O` and the two counted source interfaces. Its free
reflections use the public seed and output encoding. -/
def logicalTrials (p : MultiOracleCircuit.Program O)
    (Pw : X → Weights.LabelOp (Option (Fin N)))
    (J : X → Option (Fin N) → P →L[ℂ] P) (φ : Option (Fin N) → ℂ)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (v target : P) (hv : ‖v‖ = 1) (g ε : ℝ) (x : X)
    (hz : 0 < ODESourceBranches.mass z) (hW : WeightPrep (Pw x) z)
    (hCert : ODEActualSourceError.Certificate E z c (phased (J x) φ) (p.eval x) v target g ε) :
    ℕ → MultiOracleCircuit.Program
      (ODESectorCoordinates.oracle O (sourceFamily (ι := ι) Pw J φ)) :=
  let ψ := ODECompiledSource.seed E (seedCoefficients c) v
  let F := ODECompiledSource.output E (seedCoefficients c)
  let p' := program p (sourceFamily Pw J φ) E hE
  let h := compiled_geometry p Pw J φ E hE z c hc v target hv g ε x hz hW hCert
  fun j => ODECountedAmplification.program p' F h.2.1 ψ h.1 j

/-- Counted amplification using only public data: the SELECT program, the
supplied weight and loading interfaces, the public phases, the clean encoding,
the public LCHS coefficients and the seed. All inputs to free reflections are
explicit public data. -/
def publicLogicalTrials (p : MultiOracleCircuit.Program O)
    (Pw : X → Weights.LabelOp (Option (Fin N)))
    (J : X → Option (Fin N) → P →L[ℂ] P) (φ : Option (Fin N) → ℂ)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1) (c : ι → ℂ) (v : P)
    (hSeed : ‖ODECompiledSource.seed E (seedCoefficients c) v‖ = 1)
    (hOutput : (ODECompiledSource.output E (seedCoefficients c))† ∘L
      ODECompiledSource.output E (seedCoefficients c) = 1) :
    ℕ → MultiOracleCircuit.Program
      (ODESectorCoordinates.oracle O (sourceFamily (ι := ι) Pw J φ)) :=
  fun j => ODECountedAmplification.program (program p (sourceFamily Pw J φ) E hE)
    (ODECompiledSource.output E (seedCoefficients c)) hOutput
    (ODECompiledSource.seed E (seedCoefficients c) v) hSeed j

/-- The geometry proof justifies the public reflections but does not change
their circuit syntax. -/
theorem logicalTrials_eq_publicLogicalTrials (p : MultiOracleCircuit.Program O)
    (Pw : X → Weights.LabelOp (Option (Fin N)))
    (J : X → Option (Fin N) → P →L[ℂ] P) (φ : Option (Fin N) → ℂ)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (v target : P) (hv : ‖v‖ = 1) (g ε : ℝ) (x : X)
    (hz : 0 < ODESourceBranches.mass z) (hW : WeightPrep (Pw x) z)
    (hCert : ODEActualSourceError.Certificate E z c (phased (J x) φ) (p.eval x) v target g ε)
    (hSeed : ‖ODECompiledSource.seed E (seedCoefficients c) v‖ = 1)
    (hOutput : (ODECompiledSource.output E (seedCoefficients c))† ∘L
      ODECompiledSource.output E (seedCoefficients c) = 1) :
    logicalTrials p Pw J φ E hE z c hc v target hv g ε x hz hW hCert =
      publicLogicalTrials p Pw J φ E hE c v hSeed hOutput := by
  unfold logicalTrials publicLogicalTrials
  rfl

/-- **Primitive trial certificate.** The counted trial family compiled to
primitive matrix access by the released controlled-letter compiler. The matrix
count gains exactly the factor three of that compiler; each counted source
interface is still charged one query per call. -/
theorem primitive_source_certificate (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x))
    (Pw : X → Weights.LabelOp (Option (Fin N))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin N) → P →L[ℂ] P) (hJ : ∀ x a, IsUnitary (J x a))
    (φ : Option (Fin N) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (v target : P) (hv : ‖v‖ = 1) (s Θ ell g ε : ℝ) (hg : 1 ≤ g) (x : X)
    (hz : 0 < ODESourceBranches.mass z) (hW : WeightPrep (Pw x) z)
    (hCert : ODEActualSourceError.Certificate E z c (phased (J x) φ) (p.eval x) v target g ε)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape s Θ ell)
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (eA : Branch ι P N ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (eB : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) (a0 : A) (b0 : B)
    (image : L → X → B)
    (hvalid : ∀ l x, eB.conjStarAlgEquiv (O l x) (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image l x) 1) :
    let q := logicalTrials p Pw J φ E hE z c hc v target hv g ε x hz hW hCert
    let Jin := ODECoordinateNativeControl.input eA eB a0 b0
    ODEPrimitiveSourceJoin.TrialCertificate
      (fun j => ODECoordinateNativeControl.compile eA eB O
        (sourceFamily (ι := ι) Pw J φ) a0 b0 (q j))
      (ODEGroverAverage.chosenIterations g)
      (Jin (ODECompiledSource.seed E (seedCoefficients c) v))
      (Jin ∘L ODECompiledSource.output E (seedCoefficients c))
      x target s Θ ell g (ε / 500) := by
  let S : Bool → X → Branch ι P N →L[ℂ] Branch ι P N := sourceFamily Pw J φ
  let ψ : Physical ι P K N := ODECompiledSource.seed E (seedCoefficients c) v
  let F : P →L[ℂ] Physical ι P K N := ODECompiledSource.output E (seedCoefficients c)
  let q : ℕ → MultiOracleCircuit.Program (ODESectorCoordinates.oracle O S) :=
    logicalTrials p Pw J φ E hE z c hc v target hv g ε x hz hW hCert
  let M : ℕ := ODEGroverAverage.chosenIterations g
  let Jin : Physical ι P K N →L[ℂ] ODESectorTensor.Physical A B :=
    ODECoordinateNativeControl.input eA eB a0 b0
  change ODEPrimitiveSourceJoin.TrialCertificate
    (fun j => ODECoordinateNativeControl.compile eA eB O S a0 b0 (q j))
    M (Jin ψ) (Jin ∘L F) x target s Θ ell g (ε / 500)
  have h := compiled_geometry p Pw J φ E hE z c hc v target hv g ε x hz hW hCert
  have hψ : ‖ψ‖ = 1 := h.1
  have hF : F† ∘L F = 1 := h.2.1
  have hOld := counted_source_certificate p hO Pw hPw J hJ φ hφ E hE z c hc v target hv
    s Θ ell g ε hg x hz hW hCert hq
  have hMatrix : ∀ j, j < M →
      ((q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
        106168320 * g * ImprovedODEQueryBudget.queryShape s Θ ell := hOld.2.2.1
  have hSource : ∀ j, j < M → ∀ b : Bool,
      ((q j).cost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤ 10 * g :=
    hOld.2.2.2.1
  have hSourceTotal : ∀ j, j < M →
      ((q j).cost ODESourceQueryBudget.sourceTotalWeight : ℝ) ≤ 20 * g :=
    hOld.2.2.2.2.1
  have hSuccess : (1 : ℝ) / 4 ≤
      (∑ j ∈ Finset.range M,
        ‖ODEHeraldedSuccess.successProjector F ((q j).eval x ψ)‖ ^ 2) / (M : ℝ) :=
    hOld.2.2.2.2.2.1
  have hDirection : ∀ j, j < M → (F†) ((q j).eval x ψ) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection ((F†) ((q j).eval x ψ)) - unitDirection target‖ ≤ ε / 500 :=
    hOld.2.2.2.2.2.2
  exact trialCertificate_of_transfer eA eB S hO (sourceFamily_unitary hPw hJ hφ)
    a0 b0 image hvalid q M ψ hψ F hF x target s Θ ell g (ε / 500) hOld.1 hOld.2.1
    hMatrix hSource hSourceTotal hSuccess hDirection

/-- **Public trial certificate.** The primitive trial certificate for the trial
family built from public data alone. -/
theorem public_source_certificate (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x))
    (Pw : X → Weights.LabelOp (Option (Fin N))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin N) → P →L[ℂ] P) (hJ : ∀ x a, IsUnitary (J x a))
    (φ : Option (Fin N) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (v target : P) (hv : ‖v‖ = 1) (s Θ ell g ε : ℝ) (hg : 1 ≤ g) (x : X)
    (hz : 0 < ODESourceBranches.mass z) (hW : WeightPrep (Pw x) z)
    (hCert : ODEActualSourceError.Certificate E z c (phased (J x) φ) (p.eval x) v target g ε)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape s Θ ell)
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (eA : Branch ι P N ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (eB : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) (a0 : A) (b0 : B)
    (image : L → X → B)
    (hvalid : ∀ l x, eB.conjStarAlgEquiv (O l x) (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image l x) 1)
    (hSeed : ‖ODECompiledSource.seed E (seedCoefficients c) v‖ = 1)
    (hOutput : (ODECompiledSource.output E (seedCoefficients c))† ∘L
      ODECompiledSource.output E (seedCoefficients c) = 1) :
    ODEPrimitiveSourceJoin.TrialCertificate
      (fun j => ODECoordinateNativeControl.compile eA eB O
        (sourceFamily (ι := ι) Pw J φ) a0 b0
        (publicLogicalTrials p Pw J φ E hE c v hSeed hOutput j))
      (ODEGroverAverage.chosenIterations g)
      (ODECoordinateNativeControl.input eA eB a0 b0
        (ODECompiledSource.seed E (seedCoefficients c) v))
      (ODECoordinateNativeControl.input eA eB a0 b0 ∘L
        ODECompiledSource.output E (seedCoefficients c))
      x target s Θ ell g (ε / 500) := by
  rw [← logicalTrials_eq_publicLogicalTrials p Pw J φ E hE z c hc v target hv g ε x hz hW hCert
    hSeed hOutput]
  exact primitive_source_certificate p hO Pw hPw J hJ φ hφ E hE z c hc v target hv
    s Θ ell g ε hg x hz hW hCert hq eA eB a0 b0 image hvalid

end Compiled

end

end SparseHamiltonian.GeneralSourceODE
