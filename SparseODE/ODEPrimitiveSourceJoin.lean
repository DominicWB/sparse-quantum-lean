import SparseODE.ODECoordinateNativeControl

/-!
# The counted source algorithm on primitive matrix access

The trial family here is the source-loading and randomized-amplification
circuit already proved in ODE9. Its matrix-sector controls are compiled by
the concrete ODE10 compiler. Accuracy, success and the pre-compilation query
bounds are obtained from the source certificate, rather than supplied as
additional promises about the amplified or compiled circuit.
-/

namespace SparseHamiltonian.ODEPrimitiveSourceJoin

noncomputable section
open ContinuousLinearMap OracleCircuit ODEStateNormalization
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 2000000

variable {ι P K X L : Type*} [Fintype ι]
  [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {N : ℕ} {O : L → X → K →L[ℂ] K}

/-- The two supplied source payloads, before adjoining the matrix sector.
`false` selects the initial preparation and `true` the forcing preparation. -/
def sourceFamily (J₀ Jb : X → P →L[ℂ] P) (N : ℕ) :
    Bool → X → ODECompiledSource.Branch ι P N →L[ℂ]
      ODECompiledSource.Branch ι P N :=
  fun b x => if b then ODESourceControls.forcing (Jb x) N
    else ODESourceControls.initial (J₀ x) N

theorem sourceFamily_unitary (J₀ Jb : X → P →L[ℂ] P) (N : ℕ)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x)) :
    ∀ b x, IsUnitary (sourceFamily (ι := ι) J₀ Jb N b x) := by
  intro b x
  cases b with
  | false => exact ODESourceControls.initial_unitary (J₀ x) N (hJ₀ x)
  | true => exact ODESourceControls.forcing_unitary (Jb x) N (hJb x)

/-- A certificate about actual finite trial circuits. Matrix queries and the
two supplied source interfaces are counted separately on the same syntax. -/
structure TrialCertificate {R : Type*}
    [NormedAddCommGroup R] [InnerProductSpace ℂ R] [CompleteSpace R]
    {V : (L ⊕ Bool) → X → R →L[ℂ] R}
    (q : ℕ → MultiOracleCircuit.Program V) (M : ℕ) (ψ : R) (F : P →L[ℂ] R)
    (x : X) (target : P) (s Θ ell g η : ℝ) : Prop where
  cutoff_pos : 0 < M
  cutoff_le : (M : ℝ) ≤ 5 * g
  seed_unit : ‖ψ‖ = 1
  output_isometry : F† ∘L F = 1
  matrix_queries : ∀ j, j < M →
    ((q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
      318504960 * g * ImprovedODEQueryBudget.queryShape s Θ ell
  source_queries : ∀ j, j < M → ∀ b : Bool,
    ((q j).cost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤ 10 * g
  total_source_queries : ∀ j, j < M →
    ((q j).cost ODESourceQueryBudget.sourceTotalWeight : ℝ) ≤ 20 * g
  mean_success : (1 : ℝ) / 4 ≤
    (∑ j ∈ Finset.range M,
      ‖ODEHeraldedSuccess.successProjector F ((q j).eval x ψ)‖ ^ 2) / (M : ℝ)
  direction_error : ∀ j, j < M → (F†) ((q j).eval x ψ) ≠ 0 →
    ∃ ω : ℂ, ‖ω‖ = 1 ∧
      ‖ω • unitDirection ((F†) ((q j).eval x ψ)) - unitDirection target‖ ≤ η

/-- The actual ODE9 family, expressed in the logical oracle vocabulary of
the primitive-control compiler. Its free reflections use the fixed seed and
output encoding; neither source-dependent reflection is declared free. -/
def logicalTrials (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (J₀ Jb : X → P →L[ℂ] P)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (v target : P)
    (g ε : ℝ) (x : X)
    (hCert : ODEActualSourceError.Certificate E z c
      (ODESourcePreparations.branch (J₀ x) (Jb x) N) (p.eval x) v target g ε) :
    ℕ → MultiOracleCircuit.Program
      (ODESectorCoordinates.oracle O (sourceFamily (ι := ι) J₀ Jb N)) :=
  let d : Option (Fin N) × ι → ℂ := ODEActualSourceError.coefficients z c
  let ψ : ODECompiledSource.Physical ι P K N := ODECompiledSource.seed E d v
  let F : P →L[ℂ] ODECompiledSource.Physical ι P K N := ODECompiledSource.output E d
  let p' : MultiOracleCircuit.Program
      (ODESectorCoordinates.oracle O (sourceFamily (ι := ι) J₀ Jb N)) :=
    ODECompiledSource.program p J₀ Jb E hE
  let h := ODECountedSourceCertificate.compiled_geometry
    p hO J₀ Jb hJ₀ hJb E hE z c v target g ε x hCert
  fun j => ODECountedAmplification.program p' F h.2.1 ψ h.1 j

/-- Compile the source-loading and amplification algorithm to primitive
matrix queries. The matrix count increases by exactly the factor three
already proved for the controlled-letter compiler. Source counts, herald
probabilities and decoded normalized vectors retain their proved values. -/
theorem primitive_source_certificate (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (J₀ Jb : X → P →L[ℂ] P)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (v target : P)
    (s Θ ell g ε : ℝ) (hg : 1 ≤ g) (x : X)
    (hCert : ODEActualSourceError.Certificate E z c
      (ODESourcePreparations.branch (J₀ x) (Jb x) N) (p.eval x) v target g ε)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape s Θ ell)
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (eA : ODECompiledSource.Branch ι P N ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (eB : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) (a0 : A) (b0 : B)
    (image : L → X → B)
    (hvalid : ∀ l x, eB.conjStarAlgEquiv (O l x) (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image l x) 1) :
    let q := logicalTrials p hO J₀ Jb hJ₀ hJb E hE z c v target g ε x hCert
    let J := ODECoordinateNativeControl.input eA eB a0 b0
    TrialCertificate
      (fun j => ODECoordinateNativeControl.compile eA eB O
        (sourceFamily (ι := ι) J₀ Jb N) a0 b0 (q j))
      (ODEGroverAverage.chosenIterations g)
      (J (ODECompiledSource.seed E (ODEActualSourceError.coefficients z c) v))
      (J ∘L ODECompiledSource.output E (ODEActualSourceError.coefficients z c))
      x target s Θ ell g (ε / 500) := by
  let S : Bool → X → ODECompiledSource.Branch ι P N →L[ℂ]
      ODECompiledSource.Branch ι P N := sourceFamily J₀ Jb N
  let d : Option (Fin N) × ι → ℂ := ODEActualSourceError.coefficients z c
  let ψ : ODECompiledSource.Physical ι P K N := ODECompiledSource.seed E d v
  let F : P →L[ℂ] ODECompiledSource.Physical ι P K N := ODECompiledSource.output E d
  let q : ℕ → MultiOracleCircuit.Program (ODESectorCoordinates.oracle O S) :=
    logicalTrials p hO J₀ Jb hJ₀ hJb E hE z c v target g ε x hCert
  let M : ℕ := ODEGroverAverage.chosenIterations g
  let J : ODECompiledSource.Physical ι P K N →L[ℂ] ODESectorTensor.Physical A B :=
    ODECoordinateNativeControl.input eA eB a0 b0
  change TrialCertificate
    (fun j => ODECoordinateNativeControl.compile eA eB O S a0 b0 (q j))
    M (J ψ) (J ∘L F) x target s Θ ell g (ε / 500)
  have h := ODECountedSourceCertificate.compiled_geometry
    p hO J₀ Jb hJ₀ hJb E hE z c v target g ε x hCert
  have hψ : ‖ψ‖ = 1 := h.1
  have hF : F† ∘L F = 1 := h.2.1
  have hOld := ODECountedSourceCertificate.counted_source_certificate
    p hO J₀ Jb hJ₀ hJb E hE z c v target s Θ ell g ε hg x hCert hq
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
  have hNew := ODECoordinateNativeControl.transfer_certificate
    eA eB O S hO (sourceFamily_unitary J₀ Jb N hJ₀ hJb)
    a0 b0 image hvalid q M ψ hψ F hF x target s Θ ell g (ε / 500)
    hMatrix hSource hSourceTotal hSuccess hDirection
  exact {
    cutoff_pos := hOld.1
    cutoff_le := hOld.2.1
    seed_unit := hNew.1
    output_isometry := hNew.2.1
    matrix_queries := hNew.2.2.1
    source_queries := hNew.2.2.2.1
    total_source_queries := hNew.2.2.2.2.1
    mean_success := hNew.2.2.2.2.2.1
    direction_error := hNew.2.2.2.2.2.2 }

end
end SparseHamiltonian.ODEPrimitiveSourceJoin
