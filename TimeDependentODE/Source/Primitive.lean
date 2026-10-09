import TimeDependentODE.Source.Counted

/-!
# The counted time-dependent source algorithm on primitive matrix access

Time-dependent counterpart of `SparseHamiltonian.ODEPrimitiveSourceJoin`. The
trial family here is the time-dependent source-loading and randomized
amplification circuit of `SourceTD.counted_source_certificate`, whose forcing
interface applies `Jb x q` on every forcing label `some q`. Its matrix-sector
controls are compiled by the released concrete compiler
`ODECoordinateNativeControl.compile`. Accuracy, success and the
pre-compilation query bounds are obtained from the source certificate for the
branch map `branchTD`, rather than supplied as additional promises about the
amplified or compiled circuit. The conclusion is the released
`ODEPrimitiveSourceJoin.TrialCertificate`, with the same constants.
-/

namespace SparseHamiltonian.TimeDependentODE.SourceTD

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
`false` selects the released initial preparation and `true` the
label-dependent forcing preparation. -/
def sourceFamily (J₀ : X → P →L[ℂ] P) (Jb : X → Fin N → P →L[ℂ] P) :
    Bool → X → ODECompiledSource.Branch ι P N →L[ℂ]
      ODECompiledSource.Branch ι P N :=
  fun b x => if b then forcing (Jb x)
    else ODESourceControls.initial (J₀ x) N

theorem sourceFamily_unitary (J₀ : X → P →L[ℂ] P) (Jb : X → Fin N → P →L[ℂ] P)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x q, IsUnitary (Jb x q)) :
    ∀ b x, IsUnitary (sourceFamily (ι := ι) J₀ Jb b x) := by
  intro b x
  cases b with
  | false => exact ODESourceControls.initial_unitary (J₀ x) N (hJ₀ x)
  | true => exact forcing_unitary (Jb x) (hJb x)

/-- The actual time-dependent trial family, expressed in the logical oracle
vocabulary of the primitive-control compiler. Its free reflections use the
fixed seed and output encoding; neither source-dependent reflection is
declared free. -/
def logicalTrials (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (J₀ : X → P →L[ℂ] P)
    (Jb : X → Fin N → P →L[ℂ] P)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x q, IsUnitary (Jb x q))
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (v target : P)
    (g ε : ℝ) (x : X)
    (hCert : ODEActualSourceError.Certificate E z c
      (branchTD (J₀ x) (Jb x)) (p.eval x) v target g ε) :
    ℕ → MultiOracleCircuit.Program
      (ODESectorCoordinates.oracle O (sourceFamily (ι := ι) J₀ Jb)) :=
  let d : Option (Fin N) × ι → ℂ := ODEActualSourceError.coefficients z c
  let ψ : ODECompiledSource.Physical ι P K N := ODECompiledSource.seed E d v
  let F : P →L[ℂ] ODECompiledSource.Physical ι P K N := ODECompiledSource.output E d
  let p' : MultiOracleCircuit.Program
      (ODESectorCoordinates.oracle O (sourceFamily (ι := ι) J₀ Jb)) :=
    program p J₀ Jb E hE
  let h := compiled_geometry p hO J₀ Jb hJ₀ hJb E hE z c v target g ε x hCert
  fun j => ODECountedAmplification.program p' F h.2.1 ψ h.1 j

/-- Compile the time-dependent source-loading and amplification algorithm to
primitive matrix queries. The matrix count increases by exactly the factor
three already proved for the controlled-letter compiler. Source counts, herald
probabilities and decoded normalized vectors retain their proved values; the
label-dependent forcing interface is still charged one query per call. -/
theorem primitive_source_certificate (p : MultiOracleCircuit.Program O)
    (hO : ∀ l x, IsUnitary (O l x)) (J₀ : X → P →L[ℂ] P)
    (Jb : X → Fin N → P →L[ℂ] P)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x q, IsUnitary (Jb x q))
    (E : ODECompiledSource.Branch ι P N →L[ℂ] K) (hE : E† ∘L E = 1)
    (z : Option (Fin N) → P) (c : ι → ℂ) (v target : P)
    (s Θ ell g ε : ℝ) (hg : 1 ≤ g) (x : X)
    (hCert : ODEActualSourceError.Certificate E z c
      (branchTD (J₀ x) (Jb x)) (p.eval x) v target g ε)
    (hq : (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape s Θ ell)
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (eA : ODECompiledSource.Branch ι P N ≃ₗᵢ[ℂ] EuclideanSpace ℂ A)
    (eB : K ≃ₗᵢ[ℂ] EuclideanSpace ℂ B) (a0 : A) (b0 : B)
    (image : L → X → B)
    (hvalid : ∀ l x, eB.conjStarAlgEquiv (O l x) (EuclideanSpace.single b0 1) =
      EuclideanSpace.single (image l x) 1) :
    let q := logicalTrials p hO J₀ Jb hJ₀ hJb E hE z c v target g ε x hCert
    let J := ODECoordinateNativeControl.input eA eB a0 b0
    ODEPrimitiveSourceJoin.TrialCertificate
      (fun j => ODECoordinateNativeControl.compile eA eB O
        (sourceFamily (ι := ι) J₀ Jb) a0 b0 (q j))
      (ODEGroverAverage.chosenIterations g)
      (J (ODECompiledSource.seed E (ODEActualSourceError.coefficients z c) v))
      (J ∘L ODECompiledSource.output E (ODEActualSourceError.coefficients z c))
      x target s Θ ell g (ε / 500) := by
  let S : Bool → X → ODECompiledSource.Branch ι P N →L[ℂ]
      ODECompiledSource.Branch ι P N := sourceFamily J₀ Jb
  let d : Option (Fin N) × ι → ℂ := ODEActualSourceError.coefficients z c
  let ψ : ODECompiledSource.Physical ι P K N := ODECompiledSource.seed E d v
  let F : P →L[ℂ] ODECompiledSource.Physical ι P K N := ODECompiledSource.output E d
  let q : ℕ → MultiOracleCircuit.Program (ODESectorCoordinates.oracle O S) :=
    logicalTrials p hO J₀ Jb hJ₀ hJb E hE z c v target g ε x hCert
  let M : ℕ := ODEGroverAverage.chosenIterations g
  let J : ODECompiledSource.Physical ι P K N →L[ℂ] ODESectorTensor.Physical A B :=
    ODECoordinateNativeControl.input eA eB a0 b0
  change ODEPrimitiveSourceJoin.TrialCertificate
    (fun j => ODECoordinateNativeControl.compile eA eB O S a0 b0 (q j))
    M (J ψ) (J ∘L F) x target s Θ ell g (ε / 500)
  have h := compiled_geometry p hO J₀ Jb hJ₀ hJb E hE z c v target g ε x hCert
  have hψ : ‖ψ‖ = 1 := h.1
  have hF : F† ∘L F = 1 := h.2.1
  have hOld := counted_source_certificate
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
    eA eB O S hO (sourceFamily_unitary J₀ Jb hJ₀ hJb)
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
end SparseHamiltonian.TimeDependentODE.SourceTD
