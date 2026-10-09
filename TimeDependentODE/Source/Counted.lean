import TimeDependentODE.Source.Compiled

/-!
# Source-counted randomized ODE preparation with time-dependent forcing

Time-dependent counterpart of `SparseHamiltonian.ODECountedSourceCertificate`.
This endpoint joins the source correctness certificate for the branch map
`branchTD` to the actual compiled source-loading program `SourceTD.program`.
The physical seed, output encoding and routing are the released,
input-independent ones. Each trial charges the full preparation and its
inverse, including both supplied source interfaces; the label-dependent forcing
interface is charged exactly as the constant one. Matrix calls here are the
sector-controlled native calls; their compilation to the original primitive
access model and Gaussian LCHS estimates remain separate obligations.
-/

namespace SparseHamiltonian.TimeDependentODE.SourceTD

noncomputable section
open ContinuousLinearMap OracleCircuit ODEStateNormalization
open scoped InnerProduct BigOperators
set_option synthInstance.maxSize 2048

variable {ι P K X L : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : ℕ} {O : L → X → K →L[ℂ] K}

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Transport the proved source certificate to the actual source-loading
program. In particular, the fixed seed is unit without assuming any new
accuracy or success property of this compiled program. -/
theorem compiled_geometry (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (J₀ : X → P →L[ℂ] P)
    (Jb : X → Fin N → P →L[ℂ] P)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x q, IsUnitary (Jb x q))
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (v target : P) (g ε : ℝ) (x : X)
    (hCert : ODEActualSourceError.Certificate E z c
      (branchTD (J₀ x) (Jb x)) (p.eval x) v target g ε) :
    let d := ODEActualSourceError.coefficients z c
    let ψ := ODECompiledSource.seed E d v
    let F := ODECompiledSource.output E d
    let W := (program p J₀ Jb E hE).eval x
    ‖ψ‖ = 1 ∧ F† ∘L F = 1 ∧
      1 / (4 * g) ≤ ODEGroverActual.amplitude F W ψ ∧
      ODEGroverActual.amplitude F W ψ ≤ 1 / 2 ∧
      ‖unitDirection ((F†) (W ψ)) - unitDirection target‖ ≤ ε / 500 := by
  let d : Option (Fin N) × ι → ℂ := ODEActualSourceError.coefficients z c
  let ψ : ODECompiledSource.Physical ι P K N := ODECompiledSource.seed E d v
  let F : P →L[ℂ] ODECompiledSource.Physical ι P K N := ODECompiledSource.output E d
  let W : ODECompiledSource.Physical ι P K N →L[ℂ]
      ODECompiledSource.Physical ι P K N :=
    (program p J₀ Jb E hE).eval x
  change ‖ψ‖ = 1 ∧ F† ∘L F = 1 ∧
    1 / (4 * g) ≤ ODEGroverActual.amplitude F W ψ ∧
    ODEGroverActual.amplitude F W ψ ≤ 1 / 2 ∧
    ‖unitDirection ((F†) (W ψ)) - unitDirection target‖ ≤ ε / 500
  let I : K →L[ℂ] ODECompiledSource.Physical ι P K N :=
    ODESourceTransport.matrixEmbedding
  let F₀ : P →L[ℂ] K := ODEActualSourceError.output E z c
  let ψ₀ : K := ODEActualSourceError.input E z c
    (branchTD (J₀ x) (Jb x)) v
  have hI : I† ∘L I = 1 :=
    ODESourceTransport.matrixEmbedding_isometry
      (B := ODECompiledSource.Branch ι P N) (K := K)
  have hW : IsUnitary W :=
    program_unitary p J₀ Jb E hE hO hJ₀ hJb x
  have hState : W ψ = I (p.eval x ψ₀) :=
    program_state p hO J₀ Jb E hE d v x
  have hSeed : ‖ψ‖ = 1 := by
    calc
      ‖ψ‖ = ‖W ψ‖ :=
        (W.norm_map_iff_adjoint_comp_self.mpr hW.1 ψ).symm
      _ = ‖I (p.eval x ψ₀)‖ := congrArg (fun y => ‖y‖) hState
      _ = ‖p.eval x ψ₀‖ := I.norm_map_iff_adjoint_comp_self.mpr hI _
      _ = 1 := hCert.evolved_unit
  have hF : F† ∘L F = 1 :=
    ODESourceHeraldLift.output_isometry I hI F₀ hCert.output_isometry
  have hAmplitude : ODEGroverActual.amplitude F W ψ =
      ODEGroverActual.amplitude F₀ (p.eval x) ψ₀ :=
    ODESourceHeraldLift.amplitude_eq_of_state_eq I hI F₀ (p.eval x) ψ₀ W ψ hState
  have hDecoded : (F†) (W ψ) = (F₀†) (p.eval x ψ₀) :=
    ODESourceHeraldLift.decoded_eq_of_state_eq I hI F₀ (p.eval x) ψ₀ W ψ hState
  have hLower : 1 / (4 * g) ≤ ODEGroverActual.amplitude F W ψ :=
    hCert.amplitude_lower.trans hAmplitude.ge
  have hUpper : ODEGroverActual.amplitude F W ψ ≤ 1 / 2 :=
    hAmplitude.le.trans hCert.amplitude_upper.le
  have hErrorEq :
      ‖unitDirection ((F†) (W ψ)) - unitDirection target‖ =
        ‖unitDirection ((F₀†) (p.eval x ψ₀)) - unitDirection target‖ :=
    congrArg (fun y : P => ‖unitDirection y - unitDirection target‖) hDecoded
  have hError : ‖unitDirection ((F†) (W ψ)) - unitDirection target‖ ≤ ε / 500 :=
    hErrorEq.le.trans hCert.direction_error
  exact ⟨hSeed, hF, hLower, hUpper, hError⟩

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
/-- A concrete finite family of circuits attains mean success at least one
quarter. Every successful trial has the same proved public error, charges at
most `10*g` calls of each supplied source interface (the label-dependent
forcing interface included), and retains the improved matrix-query shape. All
query bounds are worst-case over the sampled index. -/
theorem counted_source_certificate (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (J₀ : X → P →L[ℂ] P)
    (Jb : X → Fin N → P →L[ℂ] P)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x q, IsUnitary (Jb x q))
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (v target : P)
    (s Θ ell g ε : ℝ) (hg : 1 ≤ g) (x : X)
    (hCert : ODEActualSourceError.Certificate E z c
      (branchTD (J₀ x) (Jb x)) (p.eval x) v target g ε)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape s Θ ell) :
    let d := ODEActualSourceError.coefficients z c
    let ψ := ODECompiledSource.seed E d v
    let F := ODECompiledSource.output E d
    let p' := program p J₀ Jb E hE
    let h := compiled_geometry p hO J₀ Jb hJ₀ hJb E hE z c v target g ε x hCert
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
  let d := ODEActualSourceError.coefficients z c
  let ψ := ODECompiledSource.seed E d v
  let F := ODECompiledSource.output E d
  let p' := program p J₀ Jb E hE
  have h := compiled_geometry p hO J₀ Jb hJ₀ hJb E hE z c v target g ε x hCert
  have hU : IsUnitary (p'.eval x) := p'.eval_unitary
    (oracle_unitary J₀ Jb hO hJ₀ hJb) x
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
        program_matrix_cost p J₀ Jb E hE (fun _ => 1)
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
      program_source_cost p J₀ Jb E hE b
    simpa only [hCost, Nat.cast_one, mul_one] using hBound
  · intro j hj
    have hBound := ODECountedAmplification.cost_le p' F h.2.1 ψ h.1 g hg j hj
      ODESourceQueryBudget.sourceTotalWeight
    have hCost : p'.cost ODESourceQueryBudget.sourceTotalWeight = 2 :=
      program_source_total_cost p J₀ Jb E hE
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

end
end SparseHamiltonian.TimeDependentODE.SourceTD
