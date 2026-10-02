import SparseODE.ODEDegenerateSource

/-!
# ODE endpoints at public boundary parameters

The zero-time and zero-energy branches use actual source-only circuits.
The positive branch uses the derived Gaussian table. All branches refer
to the actual solution and retain their success, accuracy and query bounds.
No matrix query is made in either boundary branch.

-/

namespace SparseHamiltonian.ODEMainEndpoint

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Unused matrix labels on the source-only workspace. The associated
zero-time program has no call to any of these labels. -/
def unusedMatrixOracle : Query → X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  fun _ _ => 1

/-- The exact source-only outcome uses the actual ODE target and the full
advertised matrix-query envelope. Its matrix cost is additionally zero. -/
def ZeroTimeOutcome (D : Data X n Z s) (etaH etaD T g ε : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (v b seed : EuclideanSpace ℂ n) (x : X) : Prop :=
  let p := ODEZeroTime.program (unusedMatrixOracle (X := X) (n := n)) J₀ Jb
  (∀ y, IsUnitary (p.eval y)) ∧
    p.cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0 ∧
    ODEHeraldedSuccess.successProbability (1 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (p.eval x) seed = 1 ∧
    ODEPrimitiveSourceJoin.TrialCertificate (fun _ : ℕ => p) 1 seed
      (1 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) x
      (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)
      (s : ℝ) (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
      (ImprovedODEQueryBudget.logBudget g ε) g (ε / 500)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- At a zero horizon the full public resource/error certificate is obtained
by one initial-source query, with deterministic success. -/
theorem zero_time_solver (D : Data X n Z s) (etaH etaD g ε : ℝ)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y))
    (v b seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) (x : X)
    (hInitial : v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v)
    (hTarget : ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b 0 ≠ 0) :
    ZeroTimeOutcome D etaH etaD 0 g ε J₀ Jb v b seed x := by
  have hεOne : ε ≤ 1 := hεHalf.trans (by norm_num)
  have hell : 0 ≤ ImprovedODEQueryBudget.logBudget g ε :=
    (by norm_num : (0 : ℝ) ≤ 1).trans
      (ImprovedODEQueryBudget.logBudget_ge_one g ε hg hε hεOne)
  have h := ODEZeroTime.zero_time_trial_certificate
    (unusedMatrixOracle (X := X) (n := n)) J₀ Jb hJ₀
    (ODEPublicSourceMesh.generator D x) v b seed hSeed x hTarget hInitial
    (s : ℝ) (ImprovedODEQueryBudget.logBudget g ε) g (ε / 500)
    hell hg (by positivity)
  refine ⟨h.1, (ODEZeroTime.program_costs
    (unusedMatrixOracle (X := X) (n := n)) J₀ Jb).1, h.2.1, ?_⟩
  simpa only [ImprovedODEQueryBudget.theta, zero_mul, zero_add] using h.2.2

/-- Public nonnegative parameters select exactly the cases used by the
solver: zero horizon, zero effective energy, or the positive Gaussian case. -/
theorem parameter_cases (etaH etaD T g ε : ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    T = 0 ∨
      (0 < T ∧ etaH + ImprovedODEQueryBudget.radius g ε * etaD = 0) ∨
      (0 < T ∧ 0 < etaH + ImprovedODEQueryBudget.radius g ε * etaD) := by
  have hρ : 0 ≤ etaH + ImprovedODEQueryBudget.radius g ε * etaD :=
    add_nonneg hH (mul_nonneg
      (ImprovedODEQueryBudget.radius_nonneg g ε hg hε hεOne) hDiss)
  rcases eq_or_lt_of_le hT with hZero | hPositive
  · exact Or.inl hZero.symm
  · rcases eq_or_lt_of_le hρ with hZero | hPositiveEnergy
    · exact Or.inr (Or.inl ⟨hPositive, hZero.symm⟩)
    · exact Or.inr (Or.inr ⟨hPositive, hPositiveEnergy⟩)

/-- Source-only amplified trials on the fixed source workspace. Their seed
and output depend on the two public norms, and all matrix costs vanish. -/
def ZeroEnergyOutcome (D : Data X n Z s) (etaH etaD T g ε : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (v b seed : EuclideanSpace ℂ n) (x : X) : Prop :=
  ∃ q : ℕ → MultiOracleCircuit.Program (ODEDegenerateSource.oracle (L := Query) J₀ Jb),
    (∀ j y, IsUnitary ((q j).eval y)) ∧
      (∀ j w, (q j).cost (ODESourceQueryBudget.matrixWeight w) = 0) ∧
      ODEPrimitiveSourceJoin.TrialCertificate q
        (ODEGroverAverage.chosenIterations g)
        (ODEDegenerateSource.publicSeed ‖v‖ ‖b‖ T seed)
        (ODEDegenerateSource.publicOutput (P := EuclideanSpace ℂ n) ‖v‖ ‖b‖ T)
        x (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)
        (s : ℝ) (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
        (ImprovedODEQueryBudget.logBudget g ε) g (ε / 500)

/-- Package the source-only bounds while the circuit, flag and seed are
abstract parameters.  This avoids normalizing concrete compiled programs
when constructing the individual fields of the trial certificate. -/
theorem source_only_trial_certificate {P R L : Type*}
    [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
    [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    {V : (L ⊕ Bool) → X → R →L[ℂ] R}
    (q : ℕ → MultiOracleCircuit.Program V) (M : ℕ) (ψ : R) (F : P →L[ℂ] R)
    (x : X) (target : P) (s Θ ell g η : ℝ)
    (hg : 0 ≤ g) (hShape : 0 ≤ ImprovedODEQueryBudget.queryShape s Θ ell)
    (hM : 0 < M) (hMUpper : (M : ℝ) ≤ 5 * g)
    (hψ : ‖ψ‖ = 1) (hF : F† ∘L F = 1)
    (hMatrix : ∀ j w, (q j).cost (ODESourceQueryBudget.matrixWeight w) = 0)
    (hSource : ∀ j, j < M → ∀ a : Bool,
      ((q j).cost (ODESourceQueryBudget.sourceWeight a) : ℝ) ≤ 10 * g)
    (hTotal : ∀ j, j < M →
      ((q j).cost ODESourceQueryBudget.sourceTotalWeight : ℝ) ≤ 20 * g)
    (hSuccess : (1 : ℝ) / 4 ≤
      (∑ j ∈ Finset.range M,
        ‖ODEHeraldedSuccess.successProjector F ((q j).eval x ψ)‖ ^ 2) / (M : ℝ))
    (hDirection : ∀ j, j < M → (F†) ((q j).eval x ψ) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • ODEStateNormalization.unitDirection ((F†) ((q j).eval x ψ)) -
          ODEStateNormalization.unitDirection target‖ ≤ η) :
    ODEPrimitiveSourceJoin.TrialCertificate q M ψ F x target s Θ ell g η := by
  refine {
    cutoff_pos := hM
    cutoff_le := hMUpper
    seed_unit := hψ
    output_isometry := hF
    matrix_queries := ?_
    source_queries := hSource
    total_source_queries := hTotal
    mean_success := hSuccess
    direction_error := hDirection }
  intro j _hj
  rw [hMatrix j (fun _ => 1), Nat.cast_zero]
  exact mul_nonneg (mul_nonneg (by norm_num) hg) hShape

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
/-- Zero effective energy derives the source-only target and its complete
trial certificate from the original sparse row bounds. -/
theorem zero_energy_solver (D : Data X n Z s) (etaH etaD T g ε : ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hρ : etaH + ImprovedODEQueryBudget.radius g ε * etaD = 0)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (v b seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) (x : X)
    (hInitial : v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v)
    (hForcing : b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b)
    (hTarget : ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0)
    (hBudget : ‖v‖ + T * ‖b‖ ≤
      g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖) :
    ZeroEnergyOutcome D etaH etaD T g ε J₀ Jb v b seed x := by
  have hεOne : ε ≤ 1 := hεHalf.trans (by norm_num)
  have hSolution := ODEZeroEnergy.native_solution_of_zero_energy
    D etaH etaD g ε hH hDiss hg hε hεOne hρ hrH hrD v b T x
  have hAffine : v + T • b ≠ 0 := by simpa only [hSolution] using hTarget
  have hAffineBudget : ‖v‖ + T * ‖b‖ ≤ g * ‖v + T • b‖ := by
    simpa only [hSolution] using hBudget
  have hB : 0 < ‖v‖ + T * ‖b‖ :=
    (norm_pos_iff.mpr hAffine).trans_le (ODEDegenerateSource.affine_norm_le v b T hT)
  let ψ := ODEDegenerateSource.publicSeed ‖v‖ ‖b‖ T seed
  let F := ODEDegenerateSource.publicOutput (P := EuclideanSpace ℂ n) ‖v‖ ‖b‖ T
  have hψ : ‖ψ‖ = 1 := ODEDegenerateSource.publicSeed_unit
    ‖v‖ ‖b‖ T (norm_nonneg v) (norm_nonneg b) hT hB seed hSeed
  have hF : F† ∘L F = 1 := ODEDegenerateSource.publicOutput_isometry
    ‖v‖ ‖b‖ T (norm_nonneg v) (norm_nonneg b) hT hB
  have h := ODEDegenerateSource.randomized_solver (L := Query)
    J₀ Jb hJ₀ hJb seed hSeed ‖v‖ ‖b‖ T g ε
    (norm_nonneg v) (norm_nonneg b) hT hB hg hε hεHalf
  -- Expose only the six let binders in the source theorem, then abstract
  -- the complete circuit family before projecting its certificates.
  -- Keeping q as an ordinary variable avoids comparing separate expanded
  -- copies of the source preparation and its amplification circuit.
  dsimp only at h
  generalize ODECountedAmplification.program
    (ODEDegenerateSource.preparation (L := Query) J₀ Jb)
    (ODEDegenerateSource.publicOutput (P := EuclideanSpace ℂ n) ‖v‖ ‖b‖ T)
    (ODEDegenerateSource.publicOutput_isometry (P := EuclideanSpace ℂ n)
      ‖v‖ ‖b‖ T (norm_nonneg v) (norm_nonneg b) hT hB)
    (ODEDegenerateSource.publicSeed ‖v‖ ‖b‖ T seed)
    (ODEDegenerateSource.publicSeed_unit ‖v‖ ‖b‖ T
      (norm_nonneg v) (norm_nonneg b) hT hB seed hSeed) = q at h
  rcases h with ⟨hM, hMUpper, hUnitary, hMatrix, hSource, hTotal, hCorrect⟩
  have hResult := hCorrect x v b rfl rfl hInitial hForcing hAffine hAffineBudget
  have hTheta : 0 ≤ ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε :=
    ImprovedODEQueryBudget.theta_nonneg (T * etaH) (T * etaD) g ε
      (mul_nonneg hT hH) (mul_nonneg hT hDiss) hg hε hεOne
  have hell : 0 ≤ ImprovedODEQueryBudget.logBudget g ε :=
    (by norm_num : (0 : ℝ) ≤ 1).trans
      (ImprovedODEQueryBudget.logBudget_ge_one g ε hg hε hεOne)
  have hShape := ImprovedODEQueryBudget.queryShape_nonneg (s : ℝ)
    (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
    (ImprovedODEQueryBudget.logBudget g ε) hTheta hell
  have hCert := source_only_trial_certificate q
    (ODEGroverAverage.chosenIterations g) ψ F x (v + T • b)
    (s : ℝ) (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
    (ImprovedODEQueryBudget.logBudget g ε) g (ε / 500)
    (by linarith) hShape hM hMUpper hψ hF hMatrix hSource hTotal
    hResult.1 hResult.2
  refine ⟨q, hUnitary, hMatrix, ?_⟩
  exact Eq.mpr (congrArg (fun target : EuclideanSpace ℂ n =>
    ODEPrimitiveSourceJoin.TrialCertificate q
      (ODEGroverAverage.chosenIterations g) ψ F x target
      (s : ℝ) (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
      (ImprovedODEQueryBudget.logBudget g ε) g (ε / 500)) hSolution) hCert

/-- The three explicit implementations cover every nonnegative horizon and
energy bound. Each alternative includes its actual circuit certificate;
the case conditions are public numerical conditions, not oracle tests. -/
def Outcome (D : Data X n Z s) (etaH etaD T g ε : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (v b seed : EuclideanSpace ℂ n) (x : X) : Prop :=
  (T = 0 ∧ ZeroTimeOutcome D etaH etaD T g ε J₀ Jb v b seed x) ∨
    (0 < T ∧ etaH + ImprovedODEQueryBudget.radius g ε * etaD = 0 ∧
      ZeroEnergyOutcome D etaH etaD T g ε J₀ Jb v b seed x) ∨
    (0 < T ∧ 0 < etaH + ImprovedODEQueryBudget.radius g ε * etaD ∧
      ODEPublicGaussianEndpoint.Outcome D etaH etaD T g ε J₀ Jb v b seed x)

/-- Actual constant-coefficient ODE solution preparation for all nonnegative
public durations and Hermitian-part energy bounds. No Gaussian, truncation,
quadrature, simulation, amplification or internal-circuit correctness
premise remains beyond the supplied source-interface promises.
The endpoint retains the existing pointwise circuit-existence scope, and
the separate constructor-independence lemmas do not change that scope. -/
theorem solver (D : Data X n Z s) (etaH etaD T g ε : ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (x : X) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (v b seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) (x : X)
    (hInitial : v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v)
    (hForcing : b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b)
    (hTarget : ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0)
    (hBudget : ‖v‖ + T * ‖b‖ ≤
      g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖) :
    Outcome D etaH etaD T g ε J₀ Jb v b seed x := by
  rcases parameter_cases etaH etaD T g ε hH hDiss hT hg hε
      (hεHalf.trans (by norm_num)) with hZero | ⟨hPositive, hEnergyZero⟩ |
      ⟨hPositive, hEnergyPositive⟩
  · subst T
    exact Or.inl ⟨rfl, zero_time_solver D etaH etaD g ε hg hε hεHalf
      J₀ Jb hJ₀ v b seed hSeed x hInitial hTarget⟩
  · exact Or.inr (Or.inl ⟨hPositive, hEnergyZero,
      zero_energy_solver D etaH etaD T g ε hH hDiss hT hg hε hεHalf
        hEnergyZero hrH hrD J₀ Jb hJ₀ hJb v b seed hSeed x
        hInitial hForcing hTarget hBudget⟩)
  · exact Or.inr (Or.inr ⟨hPositive, hEnergyPositive,
      ODEPublicGaussianEndpoint.positive_time_solver D etaH etaD T g ε
        hH hDiss hEnergyPositive hPositive hg hε hεHalf hrH hcH hrD hcD hPSD
        J₀ Jb hJ₀ hJb v b seed hSeed x hInitial hForcing hTarget hBudget⟩)

end
end SparseHamiltonian.ODEMainEndpoint
