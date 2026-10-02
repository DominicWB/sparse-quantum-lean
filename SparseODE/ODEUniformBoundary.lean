import SparseODE.ODEUniformPositiveEndpoint

/-!
# One boundary circuit family for every promised ODE input

The source norms, time and unit seed are public.  Each existential circuit
family is selected before the matrix input and the source vectors.  The
zero-energy branch includes the empty-promise case of zero public source
mass; no positive-mass promise is added to the endpoint.

-/

namespace SparseHamiltonian.ODEUniformBoundary

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- One zero-energy family, with the existential placed before every unknown
input and source vector.  The seed and output embedding use public norms. -/
def ZeroEnergyOutcome (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
    ∃ q : ℕ → MultiOracleCircuit.Program (ODEDegenerateSource.oracle (L := Query) J₀ Jb),
      (∀ j y, IsUnitary ((q j).eval y)) ∧
      (∀ j w, (q j).cost (ODESourceQueryBudget.matrixWeight w) = 0) ∧
      ∀ (x : X) (v b : EuclideanSpace ℂ n), ‖v‖ = r₀ → ‖b‖ = rb →
        (v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v) →
        (b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b) →
        ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
        r₀ + T * rb ≤
          g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ →
        ODEPrimitiveSourceJoin.TrialCertificate q
          (ODEGroverAverage.chosenIterations g)
          (ODEDegenerateSource.publicSeed r₀ rb T seed)
          (ODEDegenerateSource.publicOutput (P := EuclideanSpace ℂ n) r₀ rb T)
          x (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)
          (s : ℝ) (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
          (ImprovedODEQueryBudget.logBudget g ε) g (ε / 500)

/-- One initial-source query family, uniformly correct for all valid zero-time
ODE targets.  This case needs no norm promise or forcing-oracle promise. -/
def ZeroTimeOutcome (D : Data X n Z s) (etaH etaD g ε : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
    ∃ q : ℕ → MultiOracleCircuit.Program (ODESourceQueryBudget.oracle
      (ODEMainEndpoint.unusedMatrixOracle (X := X) (n := n))
      (ODEZeroTime.sourceFamily J₀ Jb)),
      (∀ j y, IsUnitary ((q j).eval y)) ∧
      (∀ j, (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0) ∧
      (∀ j, (q j).cost (ODESourceQueryBudget.sourceWeight true) = 0) ∧
      (∀ j x, ODEHeraldedSuccess.successProbability
        (1 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) ((q j).eval x) seed = 1) ∧
      ∀ (x : X) (v b : EuclideanSpace ℂ n),
        (v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v) →
        ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b 0 ≠ 0 →
        ODEPrimitiveSourceJoin.TrialCertificate q 1 seed
          (1 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
          x (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b 0)
          (s : ℝ) (ImprovedODEQueryBudget.theta (0 * etaH) (0 * etaD) g ε)
          (ImprovedODEQueryBudget.logBudget g ε) g (ε / 500)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- For positive public source mass, one source-only circuit family works for
every compatible input and both unknown source directions.  Its complete
certificate concerns the actual ODE solution, not the affine surrogate. -/
theorem zero_energy_positive_mass (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (h₀ : 0 ≤ r₀) (hb : 0 ≤ rb) (hB : 0 < r₀ + T * rb)
    (hρ : etaH + ImprovedODEQueryBudget.radius g ε * etaD = 0)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ZeroEnergyOutcome D etaH etaD T g ε r₀ rb J₀ Jb seed := by
  have hεOne : ε ≤ 1 := hεHalf.trans (by norm_num)
  let ψ := ODEDegenerateSource.publicSeed r₀ rb T seed
  let F := ODEDegenerateSource.publicOutput (P := EuclideanSpace ℂ n) r₀ rb T
  have hψ : ‖ψ‖ = 1 :=
    ODEDegenerateSource.publicSeed_unit r₀ rb T h₀ hb hT hB seed hSeed
  have hF : F† ∘L F = 1 :=
    ODEDegenerateSource.publicOutput_isometry r₀ rb T h₀ hb hT hB
  have h := ODEDegenerateSource.randomized_solver (L := Query)
    J₀ Jb hJ₀ hJb seed hSeed r₀ rb T g ε h₀ hb hT hB hg hε hεHalf
  -- Expose the source theorem's let binders and abstract the complete
  -- family before projecting any bounds.  The family is then an ordinary
  -- variable, so certificate transport never unfolds its amplified circuit.
  dsimp only at h
  generalize ODECountedAmplification.program
    (ODEDegenerateSource.preparation (L := Query) J₀ Jb)
    (ODEDegenerateSource.publicOutput (P := EuclideanSpace ℂ n) r₀ rb T)
    (ODEDegenerateSource.publicOutput_isometry (P := EuclideanSpace ℂ n)
      r₀ rb T h₀ hb hT hB)
    (ODEDegenerateSource.publicSeed r₀ rb T seed)
    (ODEDegenerateSource.publicSeed_unit r₀ rb T
      h₀ hb hT hB seed hSeed) = q at h
  rcases h with ⟨hM, hMUpper, hUnitary, hMatrix, hSource, hTotal, hCorrect⟩
  have hTheta : 0 ≤ ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε :=
    ImprovedODEQueryBudget.theta_nonneg (T * etaH) (T * etaD) g ε
      (mul_nonneg hT hH) (mul_nonneg hT hDiss) hg hε hεOne
  have hell : 0 ≤ ImprovedODEQueryBudget.logBudget g ε :=
    (by norm_num : (0 : ℝ) ≤ 1).trans
      (ImprovedODEQueryBudget.logBudget_ge_one g ε hg hε hεOne)
  have hShape := ImprovedODEQueryBudget.queryShape_nonneg (s : ℝ)
    (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
    (ImprovedODEQueryBudget.logBudget g ε) hTheta hell
  refine ⟨q, hUnitary, hMatrix, ?_⟩
  intro x v b hv hbnorm hInitial hForcing hTarget hBudget
  have hSolution := ODEZeroEnergy.native_solution_of_zero_energy
    D etaH etaD g ε hH hDiss hg hε hεOne hρ hrH hrD v b T x
  have hAffine : v + T • b ≠ 0 := by simpa only [hSolution] using hTarget
  have hAffineBudget : r₀ + T * rb ≤ g * ‖v + T • b‖ := by
    simpa only [hSolution] using hBudget
  have hResult := hCorrect x v b hv hbnorm hInitial hForcing hAffine hAffineBudget
  have hCert := ODEMainEndpoint.source_only_trial_certificate q
    (ODEGroverAverage.chosenIterations g) ψ F x (v + T • b)
    (s : ℝ) (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
    (ImprovedODEQueryBudget.logBudget g ε) g (ε / 500)
    (by linarith) hShape hM hMUpper hψ hF hMatrix hSource hTotal
    hResult.1 hResult.2
  exact Eq.mpr (congrArg (fun target : EuclideanSpace ℂ n =>
    ODEPrimitiveSourceJoin.TrialCertificate q
      (ODEGroverAverage.chosenIterations g) ψ F x target
      (s : ℝ) (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
      (ImprovedODEQueryBudget.logBudget g ε) g (ε / 500)) hSolution) hCert

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- Uniform zero-energy ODE preparation, including public source masses for
which the nonzero-target promise is empty.  Only the public scalar data
select the circuit; all unknown directions and matrix inputs follow it. -/
theorem zero_energy_solver (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (h₀ : 0 ≤ r₀) (hb : 0 ≤ rb)
    (hρ : etaH + ImprovedODEQueryBudget.radius g ε * etaD = 0)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ZeroEnergyOutcome D etaH etaD T g ε r₀ rb J₀ Jb seed := by
  by_cases hB : 0 < r₀ + T * rb
  · exact zero_energy_positive_mass D etaH etaD T g ε r₀ rb
      hH hDiss hT hg hε hεHalf h₀ hb hB hρ hrH hrD J₀ Jb hJ₀ hJb seed hSeed
  · refine ⟨fun _ => MultiOracleCircuit.Program.identity, ?_, ?_, ?_⟩
    · intro j y
      exact isUnitary_one
    · intro j w
      exact MultiOracleCircuit.Program.cost_identity _
    · intro x v b hv hbnorm _hInitial _hForcing hTarget _hBudget
      have hSolution := ODEZeroEnergy.native_solution_of_zero_energy
        D etaH etaD g ε hH hDiss hg hε (hεHalf.trans (by norm_num))
        hρ hrH hrD v b T x
      have hAffine : v + T • b ≠ 0 := by simpa only [hSolution] using hTarget
      have hNorm := ODEDegenerateSource.affine_norm_le v b T hT
      rw [hv, hbnorm] at hNorm
      exact (hB ((norm_pos_iff.mpr hAffine).trans_le hNorm)).elim

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- At zero time a single fixed initial-source query works for every promised
matrix input and every initial/forcing vector.  Its output flag succeeds
with probability one, and no matrix or forcing query is necessary. -/
theorem zero_time_solver (D : Data X n Z s) (etaH etaD g ε : ℝ)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ZeroTimeOutcome D etaH etaD g ε J₀ Jb seed := by
  let O := ODEMainEndpoint.unusedMatrixOracle (X := X) (n := n)
  let p := ODEZeroTime.program O J₀ Jb
  refine ⟨fun _ => p, ?_, ?_, ?_, ?_, ?_⟩
  · intro j y
    exact ODEZeroTime.program_unitary O J₀ Jb hJ₀ y
  · intro j
    exact (ODEZeroTime.program_costs O J₀ Jb).1
  · intro j
    exact (ODEZeroTime.program_costs O J₀ Jb).2.2.1
  · intro j x
    exact ODEZeroTime.success_probability O J₀ Jb hJ₀ seed hSeed x
  · intro x v b hInitial hTarget
    have h := ODEMainEndpoint.zero_time_solver D etaH etaD g ε hg hε hεHalf
      J₀ Jb hJ₀ v b seed hSeed x hInitial hTarget
    exact h.2.2.2

end
end SparseHamiltonian.ODEUniformBoundary
