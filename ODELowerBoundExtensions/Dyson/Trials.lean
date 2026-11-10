import SparseODE.ODECompleteSuccess
import SparseODE.ODECoordinateNativeControl
import TimeDependentODE.Source.Public
import TimeDependentODE.Source.Primitive

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Amplification and the four-trial wrapper for any LCU preparation (`odel:lem:dyson`)

Manuscript: the proof of Lemma `odel:lem:dyson`: "Amplify the actual circuit using its own inverse.
A direct trial covers amplitudes above `1/2` with constant probability; for smaller amplitudes,
randomised amplification with a bounded schedule of `O(e^z ḡ)` calls does so. Mixing the two
trials and repeating a constant number of times gives heralded success probability at least `2/3`
without changing the conditional direction."

This is the release's completion pipeline of `TimeDependentExtensions.ODE.solver`
(`MeshSource.publicTrials`, `SourceTD.primitive_source_certificate`,
`ODECompleteTrial.of_trialCertificate`) with the LCHS-specific certificate
(`ODEActualSourceError.Certificate`, coefficient mass `3`) replaced by its three consequences
actually used downstream: the decoded vector of the source-loaded preparation has norm in
`[1/(4 g), 1/2]` and direction within `ε/500` of the target. For any SELECT `p` over any matrix
oracle with a basis-image promise:

* the public trials are `SourceTD.publicLogicalTrials` (released source loading, then the
  released randomized amplification `ODECountedAmplification.program` with cutoff
  `chosenIterations g`), compiled by `ODECoordinateNativeControl.compile` to the physical oracle
  (three native calls per matrix letter, one call per source interface);
* `certificate_of_herald`: these trials satisfy the released complete certificate
  `ODECompleteTrial.Certificate` (four attempts, success `≥ 2/3`, conditional density within
  trace distance `ε`, worst-case matrix queries `≤ 1274019840 g · queryShape s 0 ℓ`) whenever
  `10 · count p ≤ 106168320 · queryShape s 0 ℓ`.

The amplitude bounds are hypotheses about the single instance `x`; the trials, seed and output
are public. The proof follows `ODECountedAmplification.randomized_certificate` per instance
(`state_eq`, `ODEGroverActual.randomized_certificate`, `cost_le`), then
`ODECoordinateNativeControl.transfer_certificate` and `ODECompleteTrial.of_trialCertificate`.
-/

namespace ODELowerBoundExtensions.Dyson

noncomputable section

open SparseHamiltonian ContinuousLinearMap OracleCircuit
open scoped InnerProduct BigOperators

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 4096 in
/-- **The released completion for an LCU preparation with a certified herald window.** -/
theorem certificate_of_herald {ι P K X L : Type*} [Fintype ι]
    [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P] [FiniteDimensional ℂ P]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {N : ℕ} {O : L → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) (hO : ∀ l x, IsUnitary (O l x))
    (J₀ : X → P →L[ℂ] P) (Jb : X → Fin N → P →L[ℂ] P)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x q, IsUnitary (Jb x q))
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (d : Option (Fin N) × ι → ℂ) (hd : 0 < ODECoherentLCU.coefficientMass d)
    (v : P) (hv : ‖v‖ = 1)
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (eA : ODECompiledSource.Branch ι P N ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (eB : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) (a0 : A) (b0 : B) (image : L → X → B)
    (hvalid : ∀ l x, eB.conjStarAlgEquiv (O l x) (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image l x) 1)
    (s ell g ε : ℝ) (hg : 1 ≤ g) (hε : 0 ≤ ε)
    (hcount : 10 * (p.count : ℝ) ≤ 106168320 * ImprovedODEQueryBudget.queryShape s 0 ell)
    (x : X) (target : P) (htarget : target ≠ 0)
    (hLower : 1 / (4 * g) ≤ ‖ODEJointSourceLCU.decoded E d
      (fun a => TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x) a.1) (p.eval x) v‖)
    (hUpper : ‖ODEJointSourceLCU.decoded E d
      (fun a => TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x) a.1) (p.eval x) v‖ ≤ 1 / 2)
    (hError : ‖ODEStateNormalization.unitDirection (ODEJointSourceLCU.decoded E d
        (fun a => TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x) a.1) (p.eval x) v) -
      ODEStateNormalization.unitDirection target‖ ≤ ε / 500) :
    ODECompleteTrial.Certificate
      (fun j => ODECoordinateNativeControl.compile eA eB O
        (TimeDependentODE.SourceTD.sourceFamily (ι := ι) J₀ Jb) a0 b0
        (TimeDependentODE.SourceTD.publicLogicalTrials p J₀ Jb E hE d v
          (ODECompiledSource.seed_unit E d hE hd v hv)
          (ODECompiledSource.output_isometry E d hE hd) j))
      (ODEGroverAverage.chosenIterations g)
      (ODECoordinateNativeControl.input eA eB a0 b0 (ODECompiledSource.seed E d v))
      (ODECoordinateNativeControl.input eA eB a0 b0 ∘L ODECompiledSource.output E d)
      x target s 0 ell g ε := by
  let S : Bool → X → ODECompiledSource.Branch ι P N →L[ℂ] ODECompiledSource.Branch ι P N :=
    TimeDependentODE.SourceTD.sourceFamily J₀ Jb
  have hS : ∀ b x, IsUnitary (S b x) :=
    TimeDependentODE.SourceTD.sourceFamily_unitary J₀ Jb hJ₀ hJb
  have hψ : ‖ODECompiledSource.seed E d v‖ = 1 := ODECompiledSource.seed_unit E d hE hd v hv
  have hF : (ODECompiledSource.output E d)† ∘L ODECompiledSource.output E d = 1 :=
    ODECompiledSource.output_isometry E d hE hd
  let ψ : ODECompiledSource.Physical ι P K N := ODECompiledSource.seed E d v
  let F : P →L[ℂ] ODECompiledSource.Physical ι P K N := ODECompiledSource.output E d
  let p' : MultiOracleCircuit.Program (ODESectorCoordinates.oracle O S) :=
    TimeDependentODE.SourceTD.program p J₀ Jb E hE
  let q : ℕ → MultiOracleCircuit.Program (ODESectorCoordinates.oracle O S) :=
    TimeDependentODE.SourceTD.publicLogicalTrials p J₀ Jb E hE d v hψ hF
  let M : ℕ := ODEGroverAverage.chosenIterations g
  let J : ODECompiledSource.Physical ι P K N →L[ℂ] ODESectorTensor.Physical A B :=
    ODECoordinateNativeControl.input eA eB a0 b0
  change ODECompleteTrial.Certificate
    (fun j => ODECoordinateNativeControl.compile eA eB O S a0 b0 (q j))
    M (J ψ) (J ∘L F) x target s 0 ell g ε
  have hU : IsUnitary (p'.eval x) :=
    TimeDependentODE.SourceTD.program_unitary p J₀ Jb E hE hO hJ₀ hJb x
  have hDec : (F†) (p'.eval x ψ) = ODEJointSourceLCU.decoded E d
      (fun a => TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x) a.1) (p.eval x) v :=
    TimeDependentODE.SourceTD.decoded_eq p hO J₀ Jb E hE d v x
  have hAmp : ODEGroverActual.amplitude F (p'.eval x) ψ = ‖ODEJointSourceLCU.decoded E d
      (fun a => TimeDependentODE.SourceTD.branchTD (J₀ x) (Jb x) a.1) (p.eval x) v‖ := by
    rw [← hDec]
    exact ODEHeraldedSuccess.successfulComponent_norm F hF (p'.eval x) ψ
  have hErr : ‖ODEStateNormalization.unitDirection ((F†) (p'.eval x ψ)) -
      ODEStateNormalization.unitDirection target‖ ≤ ε / 500 := by
    rw [hDec]; exact hError
  have hState (j : ℕ) : (q j).eval x ψ = ODEGroverActual.trial F (p'.eval x) ψ j :=
    ODECountedAmplification.state_eq p' F hF ψ hψ j x hU
  obtain ⟨hM, hMUpper, hSuccess, hDirection⟩ :=
    ODEGroverActual.randomized_certificate F hF (p'.eval x) hU ψ hψ g hg
      (hAmp ▸ hLower) (hAmp ▸ hUpper) target (ε / 500) hErr
  have hg0 : 0 ≤ g := by linarith
  have hCostLe (j : ℕ) (hj : j < M) (w : (L ⊕ Bool) → ℕ) :
      ((q j).cost w : ℝ) ≤ 10 * g * (p'.cost w : ℝ) :=
    ODECountedAmplification.cost_le p' F hF ψ hψ g hg j hj w
  have hMatrix : ∀ j, j < M →
      ((q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
        106168320 * g * ImprovedODEQueryBudget.queryShape s 0 ell := by
    intro j hj
    have hBound := hCostLe j hj (ODESourceQueryBudget.matrixWeight (fun _ => 1))
    have hCost0 : p'.cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) =
        p.cost (fun _ => 1) :=
      TimeDependentODE.SourceTD.program_matrix_cost p J₀ Jb E hE (fun _ => 1)
    have hCost : p'.cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = p.count := by
      rw [hCost0]
      simp only [MultiOracleCircuit.Program.cost_const, Nat.mul_one]
    rw [hCost] at hBound
    calc
      _ ≤ 10 * g * (p.count : ℝ) := hBound
      _ = g * (10 * (p.count : ℝ)) := by ring
      _ ≤ g * (106168320 * ImprovedODEQueryBudget.queryShape s 0 ell) :=
        mul_le_mul_of_nonneg_left hcount hg0
      _ = _ := by ring
  have hSource : ∀ j, j < M → ∀ b : Bool,
      ((q j).cost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤ 10 * g := by
    intro j hj b
    have hBound := hCostLe j hj (ODESourceQueryBudget.sourceWeight b)
    have hCost : p'.cost (ODESourceQueryBudget.sourceWeight b) = 1 :=
      TimeDependentODE.SourceTD.program_source_cost p J₀ Jb E hE b
    rw [hCost, Nat.cast_one, mul_one] at hBound
    exact hBound
  have hSourceTotal : ∀ j, j < M →
      ((q j).cost ODESourceQueryBudget.sourceTotalWeight : ℝ) ≤ 20 * g := by
    intro j hj
    have hBound := hCostLe j hj ODESourceQueryBudget.sourceTotalWeight
    have hCost : p'.cost ODESourceQueryBudget.sourceTotalWeight = 2 :=
      TimeDependentODE.SourceTD.program_source_total_cost p J₀ Jb E hE
    rw [hCost] at hBound
    norm_num only [Nat.cast_ofNat] at hBound
    linarith
  have hSuccess' : (1 : ℝ) / 4 ≤
      (∑ j ∈ Finset.range M,
        ‖ODEHeraldedSuccess.successProjector F ((q j).eval x ψ)‖ ^ 2) / (M : ℝ) := by
    simpa only [ODEGroverActual.meanProbability, ODEGroverActual.probability,
      hState] using hSuccess
  have hDirection' : ∀ j, j < M → (F†) ((q j).eval x ψ) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • ODEStateNormalization.unitDirection ((F†) ((q j).eval x ψ)) -
          ODEStateNormalization.unitDirection target‖ ≤ ε / 500 := by
    intro j _hj hNonzero
    have hn : ODEGroverActual.decoded F (p'.eval x) ψ j ≠ 0 := by
      simpa only [hState, ODEGroverActual.decoded] using hNonzero
    simpa only [hState, ODEGroverActual.decoded] using hDirection j hn
  have hNew := ODECoordinateNativeControl.transfer_certificate
    eA eB O S hO hS a0 b0 image hvalid q M ψ hψ F hF x target s 0 ell g (ε / 500)
    hMatrix hSource hSourceTotal hSuccess' hDirection'
  have hBounds := ODEGroverAverage.chosenIterations_bounds g hg
  have hTrial : ODEPrimitiveSourceJoin.TrialCertificate
      (fun j => ODECoordinateNativeControl.compile eA eB O S a0 b0 (q j))
      M (J ψ) (J ∘L F) x target s 0 ell g (ε / 500) :=
    { cutoff_pos := hBounds.1
      cutoff_le := hBounds.2.2
      seed_unit := hNew.1
      output_isometry := hNew.2.1
      matrix_queries := hNew.2.2.1
      source_queries := hNew.2.2.2.1
      total_source_queries := hNew.2.2.2.2.1
      mean_success := hNew.2.2.2.2.2.1
      direction_error := hNew.2.2.2.2.2.2 }
  exact ODECompleteTrial.of_trialCertificate
    (fun j => (ODECoordinateNativeControl.compile eA eB O S a0 b0 (q j)).eval_unitary
      (ODECoordinateNativeControl.physicalOracle_unitary eA eB O S hO hS) x)
    hε htarget hTrial

/-- The shape parameters of the released certificate at `Θ = 0`: `queryShape s 0 ℓ = ℓ`. -/
theorem queryShape_zero (s ell : ℝ) : ImprovedODEQueryBudget.queryShape s 0 ell = ell := by
  simp [ImprovedODEQueryBudget.queryShape]

end

end ODELowerBoundExtensions.Dyson
