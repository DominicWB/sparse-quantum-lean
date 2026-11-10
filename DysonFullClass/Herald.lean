import GeneralSourceODE.Primitive
import SparseODE.ODECompleteSuccess

set_option autoImplicit false
set_option synthInstance.maxSize 2048

/-!
# Amplification of the actual general-source preparation from its herald window

Manuscript, proof of Lemma `odel:lem:dyson`: "The actual success amplitude
`‖y‖/(e^z B_q)` is `Ω(1/(e^z ḡ))`. Amplify the actual circuit using its own inverse. A direct trial
covers amplitudes above `1/2` with constant probability; for smaller amplitudes, randomised
amplification with a bounded schedule of `O(e^z ḡ)` calls does so. Mixing the two trials and
repeating a constant number of times gives heralded success probability at least `2/3` without
changing the conditional direction."

The released general-source pipeline (`GeneralSourceODE.Compiled`: weights `P_w`, loading
`U_load`, public phases, the matrix program, the label unpreparation `P_w†`; randomised
amplification of the actual compiled circuit about its public seed and output flag; the
three-query primitive-control compiler; the four-trial wrapper) is stated for the LCHS
certificate `ODEActualSourceError.Certificate`. Its downstream steps use only three facts about
the decoded vector of the actual circuit: its norm lies in `[1/(4 g), 1/2]` and its direction is
within `ε/500` of the target. This module states the pipeline from these three facts, for an
arbitrary matrix program over an arbitrary unitary matrix access with a basis-image promise, so
that it applies to the Dyson preparation.

* `herald_geometry`: the public seed and output flag and the amplitude window of the actual
  compiled circuit;
* `herald_counted`: the counted randomised amplification (mean success at least `1/4`, `10 g`
  calls of each counted source interface per trial, the matrix shape);
* `herald_trial_certificate`: the released primitive trial certificate of the public trial family;
* `herald_certificate`: the released complete certificate of the four-trial protocol (success at
  least `2/3`, conditional trace distance at most `ε`, worst-case matrix queries
  `1274019840 g queryShape s Θ ℓ`, at most `40 g` calls of each counted source interface).
-/

namespace DysonFullClass

noncomputable section
open SparseHamiltonian ContinuousLinearMap OracleCircuit ODEStateNormalization
open SparseHamiltonian.GeneralSourceODE
open SparseHamiltonian.GeneralSourceODE.Compiled
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096

variable {ι P K X L : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : ℕ} {O : L → X → K →L[ℂ] K}

set_option maxHeartbeats 1000000 in
/-- **The herald window of the actual compiled circuit**: from the amplitude window and the
direction error of the decoded vector of the source-correctness analysis. -/
theorem herald_geometry (p : MultiOracleCircuit.Program O)
    (Pw : X → Weights.LabelOp (Option (Fin N)))
    (J : X → Option (Fin N) → P →L[ℂ] P) (φ : Option (Fin N) → ℂ)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (v target : P) (hv : ‖v‖ = 1) (g ε : ℝ) (x : X) (hz : 0 < ODESourceBranches.mass z)
    (hW : WeightPrep (Pw x) z)
    (hLower : 1 / (4 * g) ≤
      ‖ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v‖)
    (hUpper : ‖ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v‖ ≤ 1 / 2)
    (hDir : ‖unitDirection (ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v) -
      unitDirection target‖ ≤ ε / 500) :
    ‖ODECompiledSource.seed E (seedCoefficients c) v‖ = 1 ∧
      (ODECompiledSource.output E (seedCoefficients c))† ∘L
        ODECompiledSource.output E (seedCoefficients c) = 1 ∧
      1 / (4 * g) ≤ ODEGroverActual.amplitude (ODECompiledSource.output E (seedCoefficients c))
        ((program p (sourceFamily Pw J φ) E hE).eval x)
        (ODECompiledSource.seed E (seedCoefficients c) v) ∧
      ODEGroverActual.amplitude (ODECompiledSource.output E (seedCoefficients c))
        ((program p (sourceFamily Pw J φ) E hE).eval x)
        (ODECompiledSource.seed E (seedCoefficients c) v) ≤ 1 / 2 ∧
      ‖unitDirection (((ODECompiledSource.output E (seedCoefficients c))†)
          ((program p (sourceFamily Pw J φ) E hE).eval x
            (ODECompiledSource.seed E (seedCoefficients c) v))) - unitDirection target‖ ≤
        ε / 500 := by
  have hpos : 0 < ODECoherentLCU.coefficientMass (seedCoefficients (N := N) c) := by
    rw [seedCoefficients_mass]
    exact hc
  have hψ := ODECompiledSource.seed_unit E (seedCoefficients c) hE hpos v hv
  have hF := ODECompiledSource.output_isometry E (seedCoefficients c) hE hpos
  have hDec := decoded_actual p Pw J φ E hE z c v x hz hW
  have hAmp : ODEGroverActual.amplitude (ODECompiledSource.output E (seedCoefficients c))
      ((program p (sourceFamily Pw J φ) E hE).eval x)
      (ODECompiledSource.seed E (seedCoefficients c) v) =
        ‖ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v‖ := by
    rw [← hDec]
    exact ODEHeraldedSuccess.successfulComponent_norm _ hF _ _
  refine ⟨hψ, hF, ?_, ?_, ?_⟩
  · rw [hAmp]; exact hLower
  · rw [hAmp]; exact hUpper
  · rw [hDec]; exact hDir

set_option maxHeartbeats 1000000 in
/-- **Counted randomised amplification of the actual compiled circuit** (public trial family
`Compiled.publicLogicalTrials`). -/
theorem herald_counted (p : MultiOracleCircuit.Program O) (hO : ∀ l x, IsUnitary (O l x))
    (Pw : X → Weights.LabelOp (Option (Fin N))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin N) → P →L[ℂ] P) (hJ : ∀ x a, IsUnitary (J x a))
    (φ : Option (Fin N) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (v target : P) (hv : ‖v‖ = 1) (s Θ ell g ε : ℝ) (hg : 1 ≤ g) (x : X)
    (hz : 0 < ODESourceBranches.mass z) (hW : WeightPrep (Pw x) z)
    (hLower : 1 / (4 * g) ≤
      ‖ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v‖)
    (hUpper : ‖ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v‖ ≤ 1 / 2)
    (hDir : ‖unitDirection (ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v) -
      unitDirection target‖ ≤ ε / 500)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape s Θ ell)
    (hSeed : ‖ODECompiledSource.seed E (seedCoefficients c) v‖ = 1)
    (hOutput : (ODECompiledSource.output E (seedCoefficients c))† ∘L
      ODECompiledSource.output E (seedCoefficients c) = 1) :
    0 < ODEGroverAverage.chosenIterations g ∧ (ODEGroverAverage.chosenIterations g : ℝ) ≤ 5 * g ∧
      (∀ j, j < ODEGroverAverage.chosenIterations g →
        (((publicLogicalTrials p Pw J φ E hE c v hSeed hOutput j).cost
          (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℕ) : ℝ) ≤
          106168320 * g * ImprovedODEQueryBudget.queryShape s Θ ell) ∧
      (∀ j, j < ODEGroverAverage.chosenIterations g → ∀ b : Bool,
        (((publicLogicalTrials p Pw J φ E hE c v hSeed hOutput j).cost
          (ODESourceQueryBudget.sourceWeight b) : ℕ) : ℝ) ≤ 10 * g) ∧
      (∀ j, j < ODEGroverAverage.chosenIterations g →
        (((publicLogicalTrials p Pw J φ E hE c v hSeed hOutput j).cost
          ODESourceQueryBudget.sourceTotalWeight : ℕ) : ℝ) ≤ 20 * g) ∧
      (1 : ℝ) / 4 ≤
        (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
          ‖ODEHeraldedSuccess.successProjector (ODECompiledSource.output E (seedCoefficients c))
            ((publicLogicalTrials p Pw J φ E hE c v hSeed hOutput j).eval x
              (ODECompiledSource.seed E (seedCoefficients c) v))‖ ^ 2) /
          (ODEGroverAverage.chosenIterations g : ℝ) ∧
      ∀ j, j < ODEGroverAverage.chosenIterations g →
        ((ODECompiledSource.output E (seedCoefficients c))†)
          ((publicLogicalTrials p Pw J φ E hE c v hSeed hOutput j).eval x
            (ODECompiledSource.seed E (seedCoefficients c) v)) ≠ 0 →
        ∃ ω : ℂ, ‖ω‖ = 1 ∧
          ‖ω • unitDirection (((ODECompiledSource.output E (seedCoefficients c))†)
            ((publicLogicalTrials p Pw J φ E hE c v hSeed hOutput j).eval x
              (ODECompiledSource.seed E (seedCoefficients c) v))) - unitDirection target‖ ≤
            ε / 500 := by
  let ψ := ODECompiledSource.seed E (seedCoefficients c) v
  let F := ODECompiledSource.output E (seedCoefficients c)
  let p' := program p (sourceFamily Pw J φ) E hE
  have h := herald_geometry p Pw J φ E hE z c hc v target hv g ε x hz hW hLower hUpper hDir
  have hU : IsUnitary (p'.eval x) :=
    program_unitary p hO _ (sourceFamily_unitary hPw hJ hφ) E hE x
  have hState (j : ℕ) :
      (publicLogicalTrials p Pw J φ E hE c v hSeed hOutput j).eval x ψ =
        ODEGroverActual.trial F (p'.eval x) ψ j :=
    ODECountedAmplification.state_eq p' F hOutput ψ hSeed j x hU
  obtain ⟨hM, hMUpper, hSuccess, hDirection⟩ :=
    ODEGroverActual.randomized_certificate F hOutput (p'.eval x) hU ψ hSeed
      g hg h.2.2.1 h.2.2.2.1 target (ε / 500) h.2.2.2.2
  refine ⟨hM, hMUpper, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hBound := ODECountedAmplification.cost_le p' F hOutput ψ hSeed g hg j hj
      (ODESourceQueryBudget.matrixWeight (fun _ => 1))
    have hCost : p'.cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = p.count := by
      simpa only [MultiOracleCircuit.Program.cost_const, Nat.mul_one] using
        program_matrix_cost p (sourceFamily Pw J φ) E hE (fun _ => 1)
    rw [hCost] at hBound
    have hg0 : 0 ≤ g := by linarith
    calc
      _ ≤ 10 * g * (p.count : ℝ) := hBound
      _ ≤ 10 * g * (10616832 * ImprovedODEQueryBudget.queryShape s Θ ell) :=
        mul_le_mul_of_nonneg_left hq (mul_nonneg (by norm_num) hg0)
      _ = _ := by ring
  · intro j hj b
    have hBound := ODECountedAmplification.cost_le p' F hOutput ψ hSeed g hg j hj
      (ODESourceQueryBudget.sourceWeight b)
    have hCost : p'.cost (ODESourceQueryBudget.sourceWeight b) = 1 :=
      program_source_cost p (sourceFamily Pw J φ) E hE b
    rw [hCost, Nat.cast_one, mul_one] at hBound
    exact hBound
  · intro j hj
    have hBound := ODECountedAmplification.cost_le p' F hOutput ψ hSeed g hg j hj
      ODESourceQueryBudget.sourceTotalWeight
    have hCost : p'.cost ODESourceQueryBudget.sourceTotalWeight = 2 :=
      program_source_total_cost p (sourceFamily Pw J φ) E hE
    rw [hCost] at hBound
    norm_num only [Nat.cast_ofNat] at hBound
    change ((ODECountedAmplification.program p' F hOutput ψ hSeed j).cost
      ODESourceQueryBudget.sourceTotalWeight : ℝ) ≤ 20 * g
    nlinarith
  · change (1 : ℝ) / 4 ≤
      (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
        ‖ODEHeraldedSuccess.successProjector F
          ((publicLogicalTrials p Pw J φ E hE c v hSeed hOutput j).eval x ψ)‖ ^ 2) /
        (ODEGroverAverage.chosenIterations g : ℝ)
    simp_rw [hState]
    exact hSuccess
  · intro j _hj hNonzero
    change (F†) ((publicLogicalTrials p Pw J φ E hE c v hSeed hOutput j).eval x ψ) ≠ 0 at hNonzero
    have hn : ODEGroverActual.decoded F (p'.eval x) ψ j ≠ 0 := by
      change (F†) (ODEGroverActual.trial F (p'.eval x) ψ j) ≠ 0
      rw [← hState j]
      exact hNonzero
    change ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ‖ω • unitDirection ((F†)
          ((publicLogicalTrials p Pw J φ E hE c v hSeed hOutput j).eval x ψ)) -
        unitDirection target‖ ≤ ε / 500
    rw [hState j]
    exact hDirection j hn

set_option maxHeartbeats 2000000 in
/-- **The released primitive trial certificate of the public trial family** compiled to primitive
matrix access by the released three-query control compiler. -/
theorem herald_trial_certificate (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x))
    (Pw : X → Weights.LabelOp (Option (Fin N))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin N) → P →L[ℂ] P) (hJ : ∀ x a, IsUnitary (J x a))
    (φ : Option (Fin N) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (v target : P) (hv : ‖v‖ = 1) (s Θ ell g ε : ℝ) (hg : 1 ≤ g) (x : X)
    (hz : 0 < ODESourceBranches.mass z) (hW : WeightPrep (Pw x) z)
    (hLower : 1 / (4 * g) ≤
      ‖ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v‖)
    (hUpper : ‖ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v‖ ≤ 1 / 2)
    (hDir : ‖unitDirection (ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v) -
      unitDirection target‖ ≤ ε / 500)
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
  obtain ⟨hM, hMle, hMatrix, hSource, hSourceTotal, hSuccess, hDirection⟩ :=
    herald_counted p hO Pw hPw J hJ φ hφ E hE z c hc v target hv s Θ ell g ε hg x hz hW
      hLower hUpper hDir hq hSeed hOutput
  exact trialCertificate_of_transfer eA eB (sourceFamily Pw J φ) hO
    (sourceFamily_unitary hPw hJ hφ) a0 b0 image hvalid
    (fun j => publicLogicalTrials p Pw J φ E hE c v hSeed hOutput j)
    (ODEGroverAverage.chosenIterations g) _ hSeed _ hOutput x target s Θ ell g (ε / 500)
    hM hMle hMatrix hSource hSourceTotal hSuccess hDirection

set_option maxHeartbeats 2000000 in
/-- **The released complete certificate** of the four-trial protocol of the public trial family,
from the herald window: success at least `2/3`, conditional trace distance at most `ε`, worst-case
matrix queries at most `1274019840 g queryShape s Θ ℓ`, at most `40 g` calls of each counted
source interface. -/
theorem herald_certificate (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x))
    (Pw : X → Weights.LabelOp (Option (Fin N))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin N) → P →L[ℂ] P) (hJ : ∀ x a, IsUnitary (J x a))
    (φ : Option (Fin N) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (v target : P) (hv : ‖v‖ = 1) (s Θ ell g ε : ℝ) (hg : 1 ≤ g) (hε : 0 ≤ ε)
    (htarget : target ≠ 0) (x : X)
    (hz : 0 < ODESourceBranches.mass z) (hW : WeightPrep (Pw x) z)
    (hLower : 1 / (4 * g) ≤
      ‖ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v‖)
    (hUpper : ‖ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v‖ ≤ 1 / 2)
    (hDir : ‖unitDirection (ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v) -
      unitDirection target‖ ≤ ε / 500)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape s Θ ell)
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [FiniteDimensional ℂ P]
    (eA : Branch ι P N ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (eB : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) (a0 : A) (b0 : B)
    (image : L → X → B)
    (hvalid : ∀ l x, eB.conjStarAlgEquiv (O l x) (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image l x) 1)
    (hSeed : ‖ODECompiledSource.seed E (seedCoefficients c) v‖ = 1)
    (hOutput : (ODECompiledSource.output E (seedCoefficients c))† ∘L
      ODECompiledSource.output E (seedCoefficients c) = 1) :
    ODECompleteTrial.Certificate
      (fun j => ODECoordinateNativeControl.compile eA eB O
        (sourceFamily (ι := ι) Pw J φ) a0 b0
        (publicLogicalTrials p Pw J φ E hE c v hSeed hOutput j))
      (ODEGroverAverage.chosenIterations g)
      (ODECoordinateNativeControl.input eA eB a0 b0
        (ODECompiledSource.seed E (seedCoefficients c) v))
      (ODECoordinateNativeControl.input eA eB a0 b0 ∘L
        ODECompiledSource.output E (seedCoefficients c))
      x target s Θ ell g ε :=
  ODECompleteTrial.of_trialCertificate
    (fun j => (ODECoordinateNativeControl.compile eA eB O (sourceFamily Pw J φ) a0 b0
      (publicLogicalTrials p Pw J φ E hE c v hSeed hOutput j)).eval_unitary
      (ODECoordinateNativeControl.physicalOracle_unitary eA eB O (sourceFamily Pw J φ) hO
        (sourceFamily_unitary hPw hJ hφ)) x)
    hε htarget
    (herald_trial_certificate p hO Pw hPw J hJ φ hφ E hE z c hc v target hv s Θ ell g ε hg x
      hz hW hLower hUpper hDir hq eA eB a0 b0 image hvalid hSeed hOutput)

end

end DysonFullClass
