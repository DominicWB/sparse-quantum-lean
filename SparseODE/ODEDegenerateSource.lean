import SparseODE.ODEZeroTime

/-!
# A source-only solver for the zero generator

The exact target is v + T • b.  One identity propagation branch and two
opposite-sign coefficient labels give the existing mass-three herald.
All seed, output and reflection data depend only on the public source norms,
time and fixed unit seed; unknown source directions enter solely through
the two supplied source interfaces.  Every amplified trial makes zero
matrix calls and at most 10*g calls to each source interface.

-/

namespace SparseHamiltonian.ODEDegenerateSource

noncomputable section
open ContinuousLinearMap OracleCircuit ODEStateNormalization
open scoped BigOperators InnerProduct

variable {P X L : Type*}
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]

abbrev Branch (P : Type*) [NormedAddCommGroup P] :=
  ODECompiledSource.Branch Bool P 1

abbrev Physical (P : Type*) [NormedAddCommGroup P] :=
  ODECompiledSource.Physical Bool P (Branch P) 1

/-- The coefficients sum to one and have absolute mass three. -/
def coefficient : Bool → ℂ
  | false => ((2 : ℝ) : ℂ)
  | true => -1

theorem coefficient_mass : ODECoherentLCU.coefficientMass coefficient = 3 := by
  norm_num [ODECoherentLCU.coefficientMass, Fintype.sum_bool, coefficient,
    Complex.norm_real, Real.norm_eq_abs]

omit [CompleteSpace P] in
theorem coefficient_identity_sum :
    (∑ i : Bool, coefficient i • (1 : P →L[ℂ] P)) = 1 := by
  simp only [Fintype.sum_bool, coefficient, Complex.ofReal_ofNat]
  module

/-- The probabilities use only the two known source norms. -/
def publicProbability (r₀ rb T : ℝ) : Option (Fin 1) → ℝ
  | none => r₀ / (r₀ + T * rb)
  | some _ => (T * rb) / (r₀ + T * rb)

def publicCoefficients (r₀ rb T : ℝ) : Option (Fin 1) × Bool → ℂ :=
  ODESourceCoefficients.productCoeff (publicProbability r₀ rb T) coefficient

theorem publicProbability_nonneg (r₀ rb T : ℝ)
    (h₀ : 0 ≤ r₀) (hb : 0 ≤ rb) (hT : 0 ≤ T) :
    ∀ a, 0 ≤ publicProbability r₀ rb T a := by
  intro a
  cases a <;> simp only [publicProbability] <;> positivity

theorem sum_publicProbability (r₀ rb T : ℝ) (hB : 0 < r₀ + T * rb) :
    (∑ a, publicProbability r₀ rb T a) = 1 := by
  simp only [Fintype.sum_option, publicProbability, Fin.sum_univ_one]
  rw [← add_div, div_self hB.ne']

theorem publicCoefficients_mass (r₀ rb T : ℝ)
    (h₀ : 0 ≤ r₀) (hb : 0 ≤ rb) (hT : 0 ≤ T) (hB : 0 < r₀ + T * rb) :
    ODECoherentLCU.coefficientMass (publicCoefficients r₀ rb T) = 3 := by
  rw [publicCoefficients, ODESourceCoefficients.coefficientMass_product
    (publicProbability r₀ rb T) coefficient (publicProbability_nonneg r₀ rb T h₀ hb hT),
    sum_publicProbability r₀ rb T hB, one_mul, coefficient_mass]

omit [CompleteSpace P] in
/-- The actual norm-weighted table agrees with the public table whenever
the two supplied norms are correct.  No vector direction occurs on the right. -/
theorem actual_coefficients_eq (v b : P) (r₀ rb T : ℝ) (hT : 0 ≤ T)
    (hv : ‖v‖ = r₀) (hb : ‖b‖ = rb) :
    ODEActualSourceError.coefficients (ODESourceBranches.sourceVector v b T 1)
      coefficient = publicCoefficients r₀ rb T := by
  have hmass : ODESourceBranches.mass (ODESourceBranches.sourceVector v b T 1) =
      r₀ + T * rb := by
    rw [ODESourceBranches.mass_sourceVector v b T hT 1 (by norm_num), hv, hb]
  unfold ODEActualSourceError.coefficients publicCoefficients
  apply congrArg (fun w : Option (Fin 1) → ℝ =>
    ODESourceCoefficients.productCoeff w coefficient)
  funext a
  cases a with
  | none =>
      simp only [ODESourceBranches.probability, ODESourceBranches.sourceVector,
        publicProbability, hmass, hv]
  | some i =>
      simp only [ODESourceBranches.probability, ODESourceBranches.sourceVector,
        ODESourceQuadrature.weight, Nat.cast_one, div_one, publicProbability,
        hmass, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hT, hb]

omit [CompleteSpace P] in
theorem affine_norm_le (v b : P) (T : ℝ) (hT : 0 ≤ T) :
    ‖v + T • b‖ ≤ ‖v‖ + T * ‖b‖ := by
  calc
    _ ≤ ‖v‖ + ‖T • b‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hT]

omit [CompleteSpace P] in
/-- With zero generator, one forcing label gives an exact finite source sum. -/
theorem source_sum (v b : P) (T : ℝ) :
    (∑ a : Option (Fin 1),
      (1 : P →L[ℂ] P) (ODESourceBranches.sourceVector v b T 1 a)) = v + T • b := by
  simp [Fintype.sum_option, ODESourceBranches.sourceVector,
    ODESourceQuadrature.weight, Complex.coe_smul]

theorem encoding_isometry :
    (1 : Branch P →L[ℂ] Branch P)† ∘L (1 : Branch P →L[ℂ] Branch P) = 1 := by
  exact (isUnitary_one : IsUnitary (1 : Branch P →L[ℂ] Branch P)).1

/-- Exact identity propagation discharges all three approximation premises
of the actual source certificate. -/
theorem exact_source_certificate (J₀ Jb : P →L[ℂ] P)
    (hJ₀ : IsUnitary J₀) (hJb : IsUnitary Jb)
    (seed v b : P) (hseed : ‖seed‖ = 1) (T g ε : ℝ)
    (hT : 0 ≤ T) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hInitial : v ≠ 0 → J₀ seed = unitDirection v)
    (hForcing : b ≠ 0 → Jb seed = unitDirection b)
    (hTarget : v + T • b ≠ 0)
    (hBudget : ‖v‖ + T * ‖b‖ ≤ g * ‖v + T • b‖) :
    ODEActualSourceError.Certificate (1 : Branch P →L[ℂ] Branch P)
      (ODESourceBranches.sourceVector v b T 1) coefficient
      (ODESourcePreparations.branch J₀ Jb 1) 1 seed (v + T • b) g ε := by
  have hν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  apply ODEActualSourceError.actual_source_certificate
    (1 : Branch P →L[ℂ] Branch P) encoding_isometry
    (ODESourceBranches.sourceVector v b T 1) coefficient coefficient_mass
    (ODESourcePreparations.branch J₀ Jb 1)
    (ODESourcePreparations.branch_isometry J₀ Jb 1 hJ₀.1 hJb.1)
    seed hseed (ODESourcePreparations.branch_prepares J₀ Jb seed v b T hT 1
      hInitial hForcing) 1 isUnitary_one
    (fun _ _ => (1 : P →L[ℂ] P)) (fun _ => (1 : P →L[ℂ] P))
    (v + T • b) g ε hTarget hg hε hεHalf
  · rw [ODESourceBranches.mass_sourceVector v b T hT 1 (by norm_num)]
    exact affine_norm_le v b T hT
  · rw [ODESourceBranches.mass_sourceVector v b T hT 1 (by norm_num)]
    exact hBudget
  · rw [WeightedClock.diagonal_one, sub_self]
    have hz : ‖(0 : Branch P →L[ℂ] Branch P)‖ = (0 : ℝ) := by
      convert! (@norm_zero (Branch P →L[ℂ] Branch P) _) using 1
    convert! hν.le using 1
  · intro a
    rw [coefficient_identity_sum]
    simp only [sub_self, norm_zero]
    linarith
  · rw [source_sum, sub_self, norm_zero]
    exact mul_nonneg hν.le (ODESourceBranches.mass_nonneg _)

/-- A concrete unused matrix interface.  Its labels can be chosen to match
the native matrix vocabulary, but every circuit below has zero such calls. -/
def dummyOracle (_ : L) (_ : X) : Branch P →L[ℂ] Branch P := 1

def oracle (J₀ Jb : X → P →L[ℂ] P) :
    L ⊕ Bool → X → Physical P →L[ℂ] Physical P :=
  ODESourceQueryBudget.oracle
    (ODESourceTransport.matrixOracle (B := Branch P) (dummyOracle (P := P)))
    (ODECompiledSource.sourceOracle (ι := Bool) (K := Branch P) J₀ Jb 1)

def preparation (J₀ Jb : X → P →L[ℂ] P) :
    MultiOracleCircuit.Program (oracle (L := L) J₀ Jb) :=
  ODECompiledSource.program
    (MultiOracleCircuit.Program.identity :
      MultiOracleCircuit.Program (dummyOracle (P := P) (X := X) (L := L)))
    J₀ Jb (1 : Branch P →L[ℂ] Branch P) encoding_isometry

def publicSeed (r₀ rb T : ℝ) (seed : P) : Physical P :=
  ODECompiledSource.seed (1 : Branch P →L[ℂ] Branch P)
    (publicCoefficients r₀ rb T) seed

def publicOutput (r₀ rb T : ℝ) : P →L[ℂ] Physical P :=
  ODECompiledSource.output (1 : Branch P →L[ℂ] Branch P)
    (publicCoefficients r₀ rb T)

theorem publicSeed_unit (r₀ rb T : ℝ) (h₀ : 0 ≤ r₀) (hb : 0 ≤ rb)
    (hT : 0 ≤ T) (hB : 0 < r₀ + T * rb) (seed : P) (hseed : ‖seed‖ = 1) :
    ‖publicSeed r₀ rb T seed‖ = 1 := by
  apply ODECompiledSource.seed_unit _ _ encoding_isometry _ seed hseed
  rw [publicCoefficients_mass r₀ rb T h₀ hb hT hB]
  norm_num

theorem publicOutput_isometry (r₀ rb T : ℝ) (h₀ : 0 ≤ r₀) (hb : 0 ≤ rb)
    (hT : 0 ≤ T) (hB : 0 < r₀ + T * rb) :
    (publicOutput (P := P) r₀ rb T)† ∘L publicOutput r₀ rb T = 1 := by
  apply ODECompiledSource.output_isometry _ _ encoding_isometry
  rw [publicCoefficients_mass r₀ rb T h₀ hb hT hB]
  norm_num

theorem oracle_unitary (J₀ Jb : X → P →L[ℂ] P)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x)) :
    ∀ l x, IsUnitary (oracle (L := L) J₀ Jb l x) :=
  ODECompiledSource.oracle_unitary (ι := Bool) (K := Branch P) J₀ Jb 1
    (fun _ _ => isUnitary_one) hJ₀ hJb

theorem preparation_matrix_cost (J₀ Jb : X → P →L[ℂ] P) (w : L → ℕ) :
    (preparation J₀ Jb).cost (ODESourceQueryBudget.matrixWeight w) = 0 := by
  have h := ODECompiledSource.program_matrix_cost
    (MultiOracleCircuit.Program.identity :
      MultiOracleCircuit.Program (dummyOracle (P := P) (X := X) (L := L)))
    J₀ Jb (1 : Branch P →L[ℂ] Branch P) encoding_isometry w
  rw [MultiOracleCircuit.Program.cost_identity] at h
  convert! h using 1

theorem preparation_source_cost (J₀ Jb : X → P →L[ℂ] P) (a : Bool) :
    (preparation (L := L) J₀ Jb).cost (ODESourceQueryBudget.sourceWeight a) = 1 :=
  ODECompiledSource.program_source_cost _ J₀ Jb _ encoding_isometry a

theorem preparation_source_total_cost (J₀ Jb : X → P →L[ℂ] P) :
    (preparation (L := L) J₀ Jb).cost ODESourceQueryBudget.sourceTotalWeight = 2 :=
  ODECompiledSource.program_source_total_cost _ J₀ Jb _ encoding_isometry

set_option maxRecDepth 4096 in
/-- Geometry of the public preparation is derived from the exact source
certificate and the source compiler's proved action. -/
theorem public_geometry (J₀ Jb : X → P →L[ℂ] P)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (seed v b : P) (hseed : ‖seed‖ = 1) (r₀ rb T g ε : ℝ)
    (hT : 0 ≤ T) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hv : ‖v‖ = r₀) (hb : ‖b‖ = rb) (x : X)
    (hInitial : v ≠ 0 → J₀ x seed = unitDirection v)
    (hForcing : b ≠ 0 → Jb x seed = unitDirection b)
    (hTarget : v + T • b ≠ 0)
    (hBudget : r₀ + T * rb ≤ g * ‖v + T • b‖) :
    let ψ := publicSeed r₀ rb T seed
    let F := publicOutput (P := P) r₀ rb T
    let W := (preparation (L := L) J₀ Jb).eval x
    ‖ψ‖ = 1 ∧ F† ∘L F = 1 ∧
      1 / (4 * g) ≤ ODEGroverActual.amplitude F W ψ ∧
      ODEGroverActual.amplitude F W ψ ≤ 1 / 2 ∧
      ‖unitDirection ((F†) (W ψ)) - unitDirection (v + T • b)‖ ≤ ε / 500 := by
  have hBudget' : ‖v‖ + T * ‖b‖ ≤ g * ‖v + T • b‖ := by
    simpa only [hv, hb] using hBudget
  have hCert := exact_source_certificate (J₀ x) (Jb x) (hJ₀ x) (hJb x)
    seed v b hseed T g ε hT hg hε hεHalf hInitial hForcing hTarget hBudget'
  have h := ODECountedSourceCertificate.compiled_geometry
    (MultiOracleCircuit.Program.identity :
      MultiOracleCircuit.Program (dummyOracle (P := P) (X := X) (L := L)))
    (fun _ _ => isUnitary_one) J₀ Jb hJ₀ hJb
    (1 : Branch P →L[ℂ] Branch P) encoding_isometry
    (ODESourceBranches.sourceVector v b T 1) coefficient seed (v + T • b) g ε x hCert
  dsimp only at h
  rw [actual_coefficients_eq v b r₀ rb T hT hv hb] at h
  exact h

/-- Pointwise correctness for the counted amplification program, proved before
specializing the physical workspace.  The proof rewrites only the evaluated
state, so it does not normalize the compiled source circuit. -/
theorem counted_pointwise_correct {K : Type*}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {O : L → X → K →L[ℂ] K}
    (p : MultiOracleCircuit.Program O) (F : P →L[ℂ] K)
    (hF : F† ∘L F = 1) (ψ : K) (hψ : ‖ψ‖ = 1)
    (x : X) (hW : IsUnitary (p.eval x)) (g η : ℝ) (hg : 1 ≤ g)
    (target : P)
    (hLower : 1 / (4 * g) ≤ ODEGroverActual.amplitude F (p.eval x) ψ)
    (hUpper : ODEGroverActual.amplitude F (p.eval x) ψ ≤ 1 / 2)
    (hError : ‖unitDirection ((F†) (p.eval x ψ)) -
      unitDirection target‖ ≤ η) :
    (1 : ℝ) / 4 ≤
      (∑ j ∈ Finset.range (ODEGroverAverage.chosenIterations g),
        ‖ODEHeraldedSuccess.successProjector F
          ((ODECountedAmplification.program p F hF ψ hψ j).eval x ψ)‖ ^ 2) /
          (ODEGroverAverage.chosenIterations g : ℝ) ∧
    ∀ j, j < ODEGroverAverage.chosenIterations g →
      (F†) ((ODECountedAmplification.program p F hF ψ hψ j).eval x ψ) ≠ 0 →
      ∃ ω : ℂ, ‖ω‖ = 1 ∧
        ‖ω • unitDirection
          ((F†) ((ODECountedAmplification.program p F hF ψ hψ j).eval x ψ)) -
          unitDirection target‖ ≤ η := by
  have hState (j : ℕ) :
      (ODECountedAmplification.program p F hF ψ hψ j).eval x ψ =
        ODEGroverActual.trial F (p.eval x) ψ j :=
    ODECountedAmplification.state_eq p F hF ψ hψ j x hW
  obtain ⟨_hM, _hMUpper, hSuccess, hDirection⟩ :=
    ODEGroverActual.randomized_certificate F hF (p.eval x) hW ψ hψ
      g hg hLower hUpper target η hError
  constructor
  · simpa only [ODEGroverActual.meanProbability, ODEGroverActual.probability,
      hState] using hSuccess
  · intro j _hj hNonzero
    have hn : ODEGroverActual.decoded F (p.eval x) ψ j ≠ 0 := by
      simpa only [hState, ODEGroverActual.decoded] using hNonzero
    simpa only [hState, ODEGroverActual.decoded] using hDirection j hn

set_option maxRecDepth 4096 in
/-- Public fixed seed and flag give one uniform finite trial family.  Source
vectors are quantified after the family, so their directions cannot enter
its fixed gates.  All preparation and inverse-preparation calls are counted. -/
theorem randomized_solver (J₀ Jb : X → P →L[ℂ] P)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (seed : P) (hseed : ‖seed‖ = 1) (r₀ rb T g ε : ℝ)
    (h₀ : 0 ≤ r₀) (hb : 0 ≤ rb) (hT : 0 ≤ T) (hB : 0 < r₀ + T * rb)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2) :
    let ψ := publicSeed r₀ rb T seed
    let F := publicOutput (P := P) r₀ rb T
    let hψ := publicSeed_unit r₀ rb T h₀ hb hT hB seed hseed
    let hF := publicOutput_isometry (P := P) r₀ rb T h₀ hb hT hB
    let q := fun j => ODECountedAmplification.program
      (preparation (L := L) J₀ Jb) F hF ψ hψ j
    let M := ODEGroverAverage.chosenIterations g
    0 < M ∧ (M : ℝ) ≤ 5 * g ∧
      (∀ j x, IsUnitary ((q j).eval x)) ∧
      (∀ j w, (q j).cost (ODESourceQueryBudget.matrixWeight w) = 0) ∧
      (∀ j, j < M → ∀ a : Bool,
        ((q j).cost (ODESourceQueryBudget.sourceWeight a) : ℝ) ≤ 10 * g) ∧
      (∀ j, j < M →
        ((q j).cost ODESourceQueryBudget.sourceTotalWeight : ℝ) ≤ 20 * g) ∧
      ∀ (x : X) (v b : P), ‖v‖ = r₀ → ‖b‖ = rb →
        (v ≠ 0 → J₀ x seed = unitDirection v) →
        (b ≠ 0 → Jb x seed = unitDirection b) →
        v + T • b ≠ 0 → r₀ + T * rb ≤ g * ‖v + T • b‖ →
        (1 : ℝ) / 4 ≤
          (∑ j ∈ Finset.range M,
            ‖ODEHeraldedSuccess.successProjector F ((q j).eval x ψ)‖ ^ 2) / (M : ℝ) ∧
        ∀ j, j < M → (F†) ((q j).eval x ψ) ≠ 0 →
          ∃ ω : ℂ, ‖ω‖ = 1 ∧
            ‖ω • unitDirection ((F†) ((q j).eval x ψ)) -
              unitDirection (v + T • b)‖ ≤ ε / 500 := by
  intro ψ F hψ hF q M
  have hO := oracle_unitary (L := L) J₀ Jb hJ₀ hJb
  obtain ⟨hM, _hCoverage, hMUpper⟩ := ODEGroverAverage.chosenIterations_bounds g hg
  refine ⟨hM, hMUpper, ?_, ?_, ?_, ?_, ?_⟩
  · intro j x
    exact (q j).eval_unitary hO x
  · intro j w
    change (ODECountedAmplification.program
      (preparation (L := L) J₀ Jb) F hF ψ hψ j).cost
        (ODESourceQueryBudget.matrixWeight w) = 0
    rw [ODECountedAmplification.cost_eq, preparation_matrix_cost, Nat.mul_zero]
  · intro j hj a
    have h := ODECountedAmplification.cost_le
      (preparation (L := L) J₀ Jb) F hF ψ hψ g hg j hj
      (ODESourceQueryBudget.sourceWeight a)
    rw [preparation_source_cost] at h
    simpa only [Nat.cast_one, mul_one] using h
  · intro j hj
    have h := ODECountedAmplification.cost_le
      (preparation (L := L) J₀ Jb) F hF ψ hψ g hg j hj
      ODESourceQueryBudget.sourceTotalWeight
    rw [preparation_source_total_cost] at h
    norm_num only [Nat.cast_ofNat] at h
    nlinarith
  · intro x v b hv hbnorm hInitial hForcing hTarget hBudget
    have hGeometry := public_geometry (L := L) J₀ Jb hJ₀ hJb seed v b hseed
      r₀ rb T g ε hT hg hε hεHalf hv hbnorm x hInitial hForcing hTarget hBudget
    exact counted_pointwise_correct
      (preparation (L := L) J₀ Jb) F hF ψ hψ x
      ((preparation (L := L) J₀ Jb).eval_unitary hO x)
      g (ε / 500) hg (v + T • b)
      hGeometry.2.2.1 hGeometry.2.2.2.1 hGeometry.2.2.2.2

end
end SparseHamiltonian.ODEDegenerateSource
