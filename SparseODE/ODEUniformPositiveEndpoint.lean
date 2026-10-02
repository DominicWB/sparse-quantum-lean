import SparseODE.ODEUniformNativeSource

namespace SparseHamiltonian.ODEUniformPositiveEndpoint

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- One physical schedule, encoding, seed, flag and trial family work for
every matrix input and every pair of source directions of the supplied norms.
The full primitive certificate is under the universal quantifiers. -/
def Outcome (D : Data X n Z s) (etaH etaD T g ε r₀ rb : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (Tslots d : ℕ)
    (E : ODEFinalNativeSource.SourceSpace
        (Fin (ODEPublicGaussianEndpoint.gridSize D T g ε) ⊕ Bool) n
        (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε)) →L[ℂ]
      ODEFinalNativeSource.MatrixSpace
        (Fin (ODEPublicGaussianEndpoint.gridSize D T g ε) ⊕ Bool) n Z
        (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε)) Tslots d)
    (q : ℕ → MultiOracleCircuit.Program
      (ODEFinalNativeSource.physicalOracle
        (ι := Fin (ODEPublicGaussianEndpoint.gridSize D T g ε) ⊕ Bool)
        D (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
        Tslots d J₀ Jb)),
    (∀ j y, IsUnitary ((q j).eval y)) ∧
      ∀ (v b : EuclideanSpace ℂ n) (x : X),
        ‖v‖ = r₀ → ‖b‖ = rb →
        (v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v) →
        (b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b) →
        ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
        r₀ + T * rb ≤
          g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ →
        ODEPrimitiveSourceJoin.TrialCertificate q (ODEGroverAverage.chosenIterations g)
          (ODEFinalNativeSource.input D (Sum.inr false)
            (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
            Tslots d (ODECompiledSource.seed E
              (ODESourcePublicNorms.publicCoefficients r₀ rb T
                (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
                (ODECoefficientPadding.paddedCoefficient
                  (ODEPublicGaussianEndpoint.coefficients D T g ε) 3)) seed))
          (ODEFinalNativeSource.input D (Sum.inr false)
            (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
            Tslots d ∘L ODECompiledSource.output E
              (ODESourcePublicNorms.publicCoefficients r₀ rb T
                (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
                (ODECoefficientPadding.paddedCoefficient
                  (ODEPublicGaussianEndpoint.coefficients D T g ε) 3)))
          x (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)
          (s : ℝ) (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
          (ImprovedODEQueryBudget.logBudget g ε) g (ε / 500)

/-- Uniform positive-time solver with the original primitive sparse access.
There are no analytic, simulation or solution-correctness premises.  The
public source norms determine the free coefficient preparation, so source
directions as well as the matrix input vary after the circuit is selected. -/
theorem positive_time_solver (D : Data X n Z s)
    (etaH etaD T g ε r₀ rb : ℝ) (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD)
    (hρ : 0 < etaH + ImprovedODEQueryBudget.radius g ε * etaD)
    (hT : 0 < T) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (h₀ : 0 ≤ r₀) (hb : 0 ≤ rb) (hB : 0 < r₀ + T * rb)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (x : X) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ x, IsUnitary (J₀ x)) (hJb : ∀ x, IsUnitary (Jb x))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    Outcome D etaH etaD T g ε r₀ rb J₀ Jb seed := by
  let ν : ℝ := ImprovedODEQueryBudget.precision g ε
  let N : ℕ := ODEPublicSourceMesh.meshSize D T ν
  let I := Fin (ODEPublicGaussianEndpoint.gridSize D T g ε) ⊕ Bool
  let c : I → ℂ := ODECoefficientPadding.paddedCoefficient
    (ODEPublicGaussianEndpoint.coefficients D T g ε) 3
  let k := ODEPublicGaussianEndpoint.nodes D T g ε
  let kTable : Option (Fin N) × I → ℝ :=
    fun a => ODECoefficientPadding.paddedNodes k a.2
  let uTable : Option (Fin N) × I → ℝ :=
    fun a => ODESourceBranches.duration T N a.1
  have hν : 0 < ν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hN : 0 < N := ODEPublicSourceMesh.meshSize_pos D T ν
  have hεOne : ε ≤ 1 := hεHalf.trans (by norm_num)
  have hR : 0 ≤ ImprovedODEQueryBudget.radius g ε :=
    ImprovedODEQueryBudget.radius_nonneg g ε hg hε hεOne
  have hTable := ODEPublicGaussianEndpoint.table_certificate
    D hPSD T g ε hT.le hg hε hεOne
  have hc : ODECoherentLCU.coefficientMass c = 3 :=
    ODECoefficientPadding.coefficientMass_eq _ 3 hTable.2.2.1
  have hDuration : ∀ a : Option (Fin N),
      0 ≤ ODESourceBranches.duration T N a ∧ ODESourceBranches.duration T N a ≤ T := by
    intro a
    cases a with
    | none => exact ⟨hT.le, le_rfl⟩
    | some i => exact ⟨ODESourceQuadrature.time_nonneg T hT.le N i,
        ODESourceQuadrature.time_le T hT.le N hN i⟩
  have hkTable : ∀ a, |kTable a| ≤ ImprovedODEQueryBudget.radius g ε :=
    fun a => ODECoefficientPadding.paddedNodes_bound k _ hR hTable.2.1 a.2
  have huTable : ∀ a, 0 ≤ uTable a := fun a => (hDuration a.1).1
  have huTableT : ∀ a, uTable a ≤ T := fun a => (hDuration a.1).2
  obtain ⟨γ, _hγ, _hγOne, _hWidth, hTables⟩ :=
    ODENativeSourceCertificate.native_source_certificate_with_isometry
      (σ := Option (Fin N)) (ι := I) D (none, Sum.inr false)
      etaH etaD T g ε hH hDiss hρ hT hg hε hεHalf hrH hcH hrD hcD
  obtain ⟨p, hCount, hE, _hUnitary, hCertificate⟩ :=
    hTables kTable uTable hkTable huTable huTableT
  let ρ : ℝ := etaH + ImprovedODEQueryBudget.radius g ε * etaD
  let Tslots := ODENativeSimulation.slots (s : ℝ) γ ρ T ν
  let d := ODENativeSimulation.degree (s : ℝ) γ ρ T ν
  let E : ODEFinalNativeSource.SourceSpace I n N →L[ℂ]
      ODEFinalNativeSource.MatrixSpace I n Z N Tslots d :=
    ODENativeSourceCertificate.encoding (σ := Option (Fin N)) (ι := I)
      D (none, Sum.inr false) γ ρ T ν
  have hEncoding : E† ∘L E = 1 := hE
  let pNative : MultiOracleCircuit.Program
      (ODEFinalNativeSource.matrixOracle (ι := I) D N Tslots d) := p
  let a : Option (Fin N) × I → ℂ :=
    ODESourcePublicNorms.publicCoefficients r₀ rb T N c
  have ha : 0 < ODECoherentLCU.coefficientMass a := by
    rw [ODESourcePublicNorms.publicCoefficients_mass r₀ rb T N h₀ hb hT.le hN hB c hc]
    norm_num
  let q := ODEFinalNativeSource.publicTrials
    D (Sum.inr false) N Tslots d pNative J₀ Jb E hEncoding a seed
    (ODECompiledSource.seed_unit E a hEncoding ha seed hSeed)
    (ODECompiledSource.output_isometry E a hEncoding ha)
  refine ⟨Tslots, d, E, q, ?_, ?_⟩
  · intro j y
    exact (q j).eval_unitary
      (ODEFinalNativeSource.physicalOracle_unitary (ι := I) D N Tslots d J₀ Jb hJ₀ hJb) y
  · intro v b x hv hbnorm hInitial hForcing hTarget hBudget
    have hA : ODEDissipative.Dissipative (ODEPublicSourceMesh.generator D x) :=
      ODEPublicSourceMesh.generator_dissipative D x (hPSD x)
    have hMesh := ODEPublicSourceMesh.branches_certificate D T ν hT.le hν x hA v b
    have hSourceBudget : ODESourceBranches.mass (ODESourceBranches.sourceVector v b T N) ≤
        g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ := by
      rw [hMesh.2.1, hv, hbnorm]
      exact hBudget
    have hPrep := ODESourcePreparations.branch_prepares (J₀ x) (Jb x) seed v b
      T hT.le N hInitial hForcing
    have hPaddedLCHS : ∀ a' : Option (Fin N),
        ‖(∑ i : I, c i • ODENativeLCU.branchEvolution D kTable uTable x (a', i)) -
          ODESourceBranches.propagation (ODEPublicSourceMesh.generator D x) T N a'‖ ≤ 2 * ν := by
      intro a'
      have hSum := ODESourcePadding.branch_sum_eq D
        (ODEPublicGaussianEndpoint.coefficients D T g ε) 3 k
        (ODESourceBranches.duration T N) x a'
      change ‖(∑ i : I, ODECoefficientPadding.paddedCoefficient
          (ODEPublicGaussianEndpoint.coefficients D T g ε) 3 i •
          ODENativeLCU.branchEvolution D
            (fun j : Option (Fin N) × I => ODECoefficientPadding.paddedNodes k j.2)
            (fun j => ODESourceBranches.duration T N j.1) x (a', i)) -
        ODESourceBranches.propagation (ODEPublicSourceMesh.generator D x) T N a'‖ ≤ 2 * ν
      rw [hSum]
      exact hTable.2.2.2 x (ODESourceBranches.duration T N a')
        (hDuration a').1 (hDuration a').2
    have hBranch : ∀ a' : Option (Fin N),
        (ODESourcePreparations.branch (J₀ x) (Jb x) N a')† ∘L
          ODESourcePreparations.branch (J₀ x) (Jb x) N a' = 1 :=
      ODESourcePreparations.branch_isometry (J₀ x) (Jb x) N (hJ₀ x).1 (hJb x).1
    have hCert : ODEActualSourceError.Certificate E
        (ODESourceBranches.sourceVector v b T N) c
        (ODESourcePreparations.branch (J₀ x) (Jb x) N) (pNative.eval x) seed
        (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T) g ε :=
      hCertificate c hc (ODESourceBranches.sourceVector v b T N)
        (ODESourcePreparations.branch (J₀ x) (Jb x) N) hBranch seed hSeed hPrep x
        (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)
        (ODESourceBranches.propagation (ODEPublicSourceMesh.generator D x) T N)
        hTarget hMesh.2.2.2.1 hSourceBudget hPaddedLCHS hMesh.2.2.2.2
    have hCoeff : ODEActualSourceError.coefficients
        (ODESourceBranches.sourceVector v b T N) c = a :=
      ODESourcePublicNorms.actual_coefficients_eq v b r₀ rb T N hT.le hN hv hbnorm c
    exact ODEUniformNativeSource.coefficient_trial_certificate
      D (Sum.inr false) N Tslots d pNative J₀ Jb hJ₀ hJb E hEncoding
      (ODESourceBranches.sourceVector v b T N) c seed
      (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T) hSeed
      (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
      (ImprovedODEQueryBudget.logBudget g ε) g ε hg x hCert hCount a ha hCoeff

end
end SparseHamiltonian.ODEUniformPositiveEndpoint
