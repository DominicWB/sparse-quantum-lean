import GeneralSourceODE.Compiled

/-!
# Counted amplification for the supplied weight preparation

The source-correctness certificate `ODEActualSourceError.Certificate` for the
actual source vectors `z` and the phased preparations transfers to the
compiled circuit of `Compiled.program`, whose two counted source interfaces are
the preparation (supplied `P_w`, supplied `U_load`, public phases) and the
supplied label unpreparation `P_w†` (`compiled_geometry`). The seed and the
output encoding are public; only the supplied weight preparation knows the
source norms. The released randomized amplification then gives a finite trial
family with mean success at least one quarter, the proved direction error
and at most `10 g` calls of each counted source interface per trial
(`counted_source_certificate`).
-/

namespace SparseHamiltonian.GeneralSourceODE

noncomputable section
open ContinuousLinearMap OracleCircuit ODEStateNormalization
open scoped InnerProduct BigOperators
set_option synthInstance.maxSize 2048

namespace Compiled

variable {ι P K X L : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : ℕ} {O : L → X → K →L[ℂ] K}

/-- The phased preparations: `φ a • J a` on source label `a`. -/
def phased (J : Option (Fin N) → P →L[ℂ] P) (φ : Option (Fin N) → ℂ) :
    Option (Fin N) → P →L[ℂ] P :=
  fun a => φ a • J a

/-- The weight-preparation hypothesis: `P_w |none⟩` has the square roots of the
actual source probabilities as amplitudes. -/
def WeightPrep (Q : Weights.LabelOp (Option (Fin N))) (z : Option (Fin N) → P) : Prop :=
  ∀ a, Weights.amp Q a none = (Real.sqrt (ODESourceBranches.probability z a) : ℂ)

omit [CompleteSpace P] in
theorem seedCoefficients_mass (c : ι → ℂ) :
    ODECoherentLCU.coefficientMass (seedCoefficients (N := N) c) =
      ODECoherentLCU.coefficientMass c :=
  ODESourceCoefficients.coefficientMass_normalized _ c (Weights.pointWeight_nonneg none)
    (Weights.pointWeight_sum none)

/-- The decoded vector of the compiled circuit is the source-correctness
decoded vector. -/
theorem decoded_actual (p : MultiOracleCircuit.Program O)
    (Pw : X → Weights.LabelOp (Option (Fin N))) (J : X → Option (Fin N) → P →L[ℂ] P)
    (φ : Option (Fin N) → ℂ) (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (v : P) (x : X)
    (hz : 0 < ODESourceBranches.mass z) (hW : WeightPrep (Pw x) z) :
    ((ODECompiledSource.output E (seedCoefficients c))†)
        ((program p (sourceFamily Pw J φ) E hE).eval x
          (ODECompiledSource.seed E (seedCoefficients c) v)) =
      ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v :=
  decoded_eq p Pw J φ E hE c v x (ODESourceBranches.probability z)
    (ODESourceBranches.probability_nonneg z) (ODESourceBranches.sum_probability z hz) hW

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Transport the proved source certificate to the compiled circuit. -/
theorem compiled_geometry (p : MultiOracleCircuit.Program O)
    (Pw : X → Weights.LabelOp (Option (Fin N)))
    (J : X → Option (Fin N) → P →L[ℂ] P) (φ : Option (Fin N) → ℂ)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (v target : P) (hv : ‖v‖ = 1) (g ε : ℝ) (x : X) (hz : 0 < ODESourceBranches.mass z)
    (hW : WeightPrep (Pw x) z)
    (hCert : ODEActualSourceError.Certificate E z c (phased (J x) φ) (p.eval x) v target g ε) :
    let ψ := ODECompiledSource.seed E (seedCoefficients c) v
    let F := ODECompiledSource.output E (seedCoefficients c)
    let W := (program p (sourceFamily Pw J φ) E hE).eval x
    ‖ψ‖ = 1 ∧ F† ∘L F = 1 ∧
      1 / (4 * g) ≤ ODEGroverActual.amplitude F W ψ ∧
      ODEGroverActual.amplitude F W ψ ≤ 1 / 2 ∧
      ‖unitDirection ((F†) (W ψ)) - unitDirection target‖ ≤ ε / 500 := by
  intro ψ F W
  have hpos : 0 < ODECoherentLCU.coefficientMass (seedCoefficients (N := N) c) := by
    rw [seedCoefficients_mass]
    exact hc
  have hψ : ‖ψ‖ = 1 := ODECompiledSource.seed_unit E (seedCoefficients c) hE hpos v hv
  have hF : F† ∘L F = 1 := ODECompiledSource.output_isometry E (seedCoefficients c) hE hpos
  have hDec : (F†) (W ψ) = ODEActualSourceError.decoded E z c (phased (J x) φ) (p.eval x) v :=
    decoded_actual p Pw J φ E hE z c v x hz hW
  have hAmp : ODEGroverActual.amplitude F W ψ =
      ‖ODEHeraldedSuccess.successfulComponent (ODEActualSourceError.output E z c) (p.eval x)
        (ODEActualSourceError.input E z c (phased (J x) φ) v)‖ := by
    change ‖ODEHeraldedSuccess.successfulComponent F W ψ‖ = _
    rw [ODEHeraldedSuccess.successfulComponent_norm F hF,
      ODEHeraldedSuccess.successfulComponent_norm _ hCert.output_isometry]
    exact congrArg norm hDec
  refine ⟨hψ, hF, ?_, ?_, ?_⟩
  · rw [hAmp]
    exact hCert.amplitude_lower
  · rw [hAmp]
    exact hCert.amplitude_upper.le
  · rw [hDec]
    exact hCert.direction_error

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
/-- A concrete finite family of trial circuits attains mean success at least
one quarter; every successful trial has the proved public error, charges at
most `10 g` calls of each counted source interface and retains the improved
matrix-query shape. All query bounds are worst-case over the sampled index. -/
theorem counted_source_certificate (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x))
    (Pw : X → Weights.LabelOp (Option (Fin N))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin N) → P →L[ℂ] P) (hJ : ∀ x a, IsUnitary (J x a))
    (φ : Option (Fin N) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (E : Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (hc : 0 < ODECoherentLCU.coefficientMass c)
    (v target : P) (hv : ‖v‖ = 1) (s Θ ell g ε : ℝ) (hg : 1 ≤ g) (x : X)
    (hz : 0 < ODESourceBranches.mass z) (hW : WeightPrep (Pw x) z)
    (hCert : ODEActualSourceError.Certificate E z c (phased (J x) φ) (p.eval x) v target g ε)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape s Θ ell) :
    let ψ := ODECompiledSource.seed E (seedCoefficients c) v
    let F := ODECompiledSource.output E (seedCoefficients c)
    let p' := program p (sourceFamily Pw J φ) E hE
    let h := compiled_geometry p Pw J φ E hE z c hc v target hv g ε x hz hW hCert
    let q := fun j => ODECountedAmplification.program p' F h.2.1 ψ h.1 j
    let M := ODEGroverAverage.chosenIterations g
    0 < M ∧ (M : ℝ) ≤ 5 * g ∧
      (∀ j, j < M →
        ((q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
          106168320 * g * ImprovedODEQueryBudget.queryShape s Θ ell) ∧
      (∀ j, j < M → ∀ b : Bool,
        ((q j).cost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤ 10 * g) ∧
      (∀ j, j < M →
        ((q j).cost ODESourceQueryBudget.sourceTotalWeight : ℝ) ≤ 20 * g) ∧
      (1 : ℝ) / 4 ≤
        (∑ j ∈ Finset.range M,
          ‖ODEHeraldedSuccess.successProjector F ((q j).eval x ψ)‖ ^ 2) / (M : ℝ) ∧
      ∀ j, j < M → (F†) ((q j).eval x ψ) ≠ 0 →
        ∃ ω : ℂ, ‖ω‖ = 1 ∧
          ‖ω • unitDirection ((F†) ((q j).eval x ψ)) - unitDirection target‖ ≤ ε / 500 := by
  dsimp only
  let ψ := ODECompiledSource.seed E (seedCoefficients c) v
  let F := ODECompiledSource.output E (seedCoefficients c)
  let p' := program p (sourceFamily Pw J φ) E hE
  have h := compiled_geometry p Pw J φ E hE z c hc v target hv g ε x hz hW hCert
  have hU : IsUnitary (p'.eval x) :=
    program_unitary p hO _ (sourceFamily_unitary hPw hJ hφ) E hE x
  have hState (j : ℕ) :
      (ODECountedAmplification.program p' F h.2.1 ψ h.1 j).eval x ψ =
        ODEGroverActual.trial F (p'.eval x) ψ j :=
    ODECountedAmplification.state_eq p' F h.2.1 ψ h.1 j x hU
  obtain ⟨hM, hMUpper, hSuccess, hDirection⟩ :=
    ODEGroverActual.randomized_certificate F h.2.1 (p'.eval x) hU ψ h.1
      g hg h.2.2.1 h.2.2.2.1 target (ε / 500) h.2.2.2.2
  refine ⟨hM, hMUpper, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hBound := ODECountedAmplification.cost_le p' F h.2.1 ψ h.1 g hg j hj
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
    have hBound := ODECountedAmplification.cost_le p' F h.2.1 ψ h.1 g hg j hj
      (ODESourceQueryBudget.sourceWeight b)
    have hCost : p'.cost (ODESourceQueryBudget.sourceWeight b) = 1 :=
      program_source_cost p (sourceFamily Pw J φ) E hE b
    simpa only [hCost, Nat.cast_one, mul_one] using hBound
  · intro j hj
    have hBound := ODECountedAmplification.cost_le p' F h.2.1 ψ h.1 g hg j hj
      ODESourceQueryBudget.sourceTotalWeight
    have hCost : p'.cost ODESourceQueryBudget.sourceTotalWeight = 2 :=
      program_source_total_cost p (sourceFamily Pw J φ) E hE
    rw [hCost] at hBound
    norm_num only [Nat.cast_ofNat] at hBound
    nlinarith
  · change (1 : ℝ) / 4 ≤
      (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
        ‖ODEHeraldedSuccess.successProjector F
          ((ODECountedAmplification.program p' F h.2.1 ψ h.1 j).eval x ψ)‖ ^ 2) /
        (ODEGroverAverage.chosenIterations g : ℝ)
    simp_rw [hState]
    exact hSuccess
  · intro j _hj hNonzero
    change (F†)
      ((ODECountedAmplification.program p' F h.2.1 ψ h.1 j).eval x ψ) ≠ 0 at hNonzero
    have hn : ODEGroverActual.decoded F (p'.eval x) ψ j ≠ 0 := by
      change (F†) (ODEGroverActual.trial F (p'.eval x) ψ j) ≠ 0
      rw [← hState j]
      exact hNonzero
    change ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ‖ω • unitDirection ((F†)
          ((ODECountedAmplification.program p' F h.2.1 ψ h.1 j).eval x ψ)) -
        unitDirection target‖ ≤ ε / 500
    rw [hState j]
    exact hDirection j hn

end Compiled

end

end SparseHamiltonian.GeneralSourceODE
