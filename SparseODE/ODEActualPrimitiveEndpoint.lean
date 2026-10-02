import SparseODE.ODEPublicSourceMesh

/-!
# Primitive quantum trials for the actual constant-forcing ODE

The generator is the negative of the matrix supplied by the native sparse
oracles. The target is its already proved constant-forcing solution. A public
source mesh is selected from the sparse-data scale, final time and precision,
before the unknown matrix input or source vectors. The source quadrature,
normalization and branch-preparation conditions are derived here.

The sole remaining approximation premise is a finite LCHS sum, with coefficient
mass at most three, valid uniformly over shorter nonnegative durations. Two
equal-duration opposite-coefficient branches pad that mass to exactly three
without changing the sum. The original node set need not be nonempty.

-/

namespace SparseHamiltonian.ODEActualPrimitiveEndpoint

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- The remaining finite LCHS estimate, on the original nodes and every
duration used by the initial and constant-forcing source branches. -/
def FiniteLCHS (D : Data X n Z s) (k : ι → ℝ) (c : ι → ℂ)
    (T g ε : ℝ) (x : X) : Prop :=
  ∀ u : ℝ, 0 ≤ u → u ≤ T →
    ‖ODENativeLCU.finiteSum D k (fun _ => u) c x -
        NormedSpace.exp (u • ODEPublicSourceMesh.generator D x)‖ ≤
      2 * ImprovedODEQueryBudget.precision g ε

/-- The full native trial conclusion specialised to the public source mesh
and the actual ODE solution. This transparent predicate retains all nine
success, accuracy and query guarantees from the verified primitive endpoint. -/
def OutcomeAtScale (D : Data X n Z s) (γ etaH etaD T g ε : ℝ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (c : ι → ℂ) (v b seed : EuclideanSpace ℂ n) (x : X) : Prop :=
  ODEPrimitiveEndpoint.OutcomeAtScale (ι := ι ⊕ Bool)
    D (Sum.inr false)
    (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε))
    γ (etaH + ImprovedODEQueryBudget.radius g ε * etaD) T
    (ImprovedODEQueryBudget.precision g ε) J₀ Jb
    (ODESourceBranches.sourceVector v b T
      (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision g ε)))
    (ODECoefficientPadding.paddedCoefficient c 3) seed
    (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T) x
    (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
    (ImprovedODEQueryBudget.logBudget g ε) g ε

/-- Actual-solution preparation with original sparse matrix queries and two
supplied source interfaces. Neither a source discretization certificate, a
solution-norm upper bound, nor a preparation promise for every mesh branch is
assumed. Their exact forms are derived from positivity and the public mesh.
The schedule scale is chosen before all node, coefficient, source and unknown
input parameters. The conclusion includes globally unitary trial circuits,
mean success at least `1/4`, phase-adjusted error at most `ε/500`, matrix cost
at most `318504960*g*queryShape`, and at most `10*g` calls per source interface. -/
theorem actual_ode_trials (D : Data X n Z s)
    (etaH etaD T g ε : ℝ) (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD)
    (hρ : 0 < etaH + ImprovedODEQueryBudget.radius g ε * etaD)
    (hT : 0 < T) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (x : X) (w : EuclideanSpace ℂ n),
      0 ≤ (inner ℂ w
        (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix x)) w)).re) :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ (k : ι → ℝ) (c : ι → ℂ),
        (∀ i, |k i| ≤ ImprovedODEQueryBudget.radius g ε) →
        ODECoherentLCU.coefficientMass c ≤ 3 →
        ∀ J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n,
          (∀ y, IsUnitary (J₀ y)) → (∀ y, IsUnitary (Jb y)) →
          ∀ v b seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
            ∀ x : X,
              (v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v) →
              (b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b) →
              ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
              ‖v‖ + T * ‖b‖ ≤
                g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ →
              FiniteLCHS D k c T g ε x →
              OutcomeAtScale D γ etaH etaD T g ε J₀ Jb c v b seed x := by
  let ν : ℝ := ImprovedODEQueryBudget.precision g ε
  let N : ℕ := ODEPublicSourceMesh.meshSize D T ν
  have hν : 0 < ν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hεOne : ε ≤ 1 := hεHalf.trans (by norm_num)
  have hR : 0 ≤ ImprovedODEQueryBudget.radius g ε :=
    ImprovedODEQueryBudget.radius_nonneg g ε hg hε hεOne
  obtain ⟨γ, hγ, hγOne, hWidth, hTables⟩ :=
    ODEPrimitiveEndpoint.native_ode_trials (ι := ι ⊕ Bool)
      D (Sum.inr false) N etaH etaD T g ε
      hH hDiss hρ hT hg hε hεHalf hrH hcH hrD hcD
  refine ⟨γ, hγ, hγOne, hWidth, ?_⟩
  intro k c hk hc J₀ Jb hJ₀ hJb v b seed hSeed x hInitial hForcing hTarget hBudget hLCHS
  have hA : ODEDissipative.Dissipative (ODEPublicSourceMesh.generator D x) :=
    ODEPublicSourceMesh.generator_dissipative D x (hPSD x)
  have hMesh := ODEPublicSourceMesh.branches_certificate D T ν hT.le hν x hA v b
  have hMass : ODESourceBranches.mass (ODESourceBranches.sourceVector v b T N) =
      ‖v‖ + T * ‖b‖ := hMesh.2.1
  have hDuration : ∀ a : Option (Fin N),
      0 ≤ ODESourceBranches.duration T N a ∧ ODESourceBranches.duration T N a ≤ T :=
    hMesh.2.2.1
  have hNorm : ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ ≤
      ODESourceBranches.mass (ODESourceBranches.sourceVector v b T N) :=
    hMesh.2.2.2.1
  have hQuadrature :
      ‖(∑ a, ODESourceBranches.propagation (ODEPublicSourceMesh.generator D x) T N a
          (ODESourceBranches.sourceVector v b T N a)) -
        ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ ≤
      ν * ODESourceBranches.mass (ODESourceBranches.sourceVector v b T N) :=
    hMesh.2.2.2.2
  have hSourceBudget : ODESourceBranches.mass (ODESourceBranches.sourceVector v b T N) ≤
      g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ :=
    hMass.le.trans hBudget
  have hPrep := ODESourcePreparations.branch_prepares (J₀ x) (Jb x) seed v b
    T hT.le N hInitial hForcing
  have hPaddedMass :
      ODECoherentLCU.coefficientMass (ODECoefficientPadding.paddedCoefficient c 3) = 3 :=
    ODECoefficientPadding.coefficientMass_eq c 3 hc
  let kTable : Option (Fin N) × (ι ⊕ Bool) → ℝ :=
    fun a => ODECoefficientPadding.paddedNodes k a.2
  let uTable : Option (Fin N) × (ι ⊕ Bool) → ℝ :=
    fun a => ODESourceBranches.duration T N a.1
  have hkTable : ∀ a, |kTable a| ≤ ImprovedODEQueryBudget.radius g ε :=
    fun a => ODECoefficientPadding.paddedNodes_bound k _ hR hk a.2
  have huTable : ∀ a, 0 ≤ uTable a := fun a => (hDuration a.1).1
  have huTableT : ∀ a, uTable a ≤ T := fun a => (hDuration a.1).2
  have hPaddedLCHS : ∀ a : Option (Fin N),
      ‖(∑ i : ι ⊕ Bool, ODECoefficientPadding.paddedCoefficient c 3 i •
          ODENativeLCU.branchEvolution D kTable uTable x (a, i)) -
        ODESourceBranches.propagation (ODEPublicSourceMesh.generator D x) T N a‖ ≤ 2 * ν := by
    intro a
    have hSum := ODESourcePadding.branch_sum_eq D c 3 k
      (ODESourceBranches.duration T N) x a
    change ‖(∑ i : ι ⊕ Bool, ODECoefficientPadding.paddedCoefficient c 3 i •
        ODENativeLCU.branchEvolution D
          (fun j : Option (Fin N) × (ι ⊕ Bool) => ODECoefficientPadding.paddedNodes k j.2)
          (fun j => ODESourceBranches.duration T N j.1) x (a, i)) -
      ODESourceBranches.propagation (ODEPublicSourceMesh.generator D x) T N a‖ ≤ 2 * ν
    rw [hSum]
    exact hLCHS (ODESourceBranches.duration T N a) (hDuration a).1 (hDuration a).2
  exact hTables kTable uTable hkTable huTable huTableT
    (ODECoefficientPadding.paddedCoefficient c 3) hPaddedMass J₀ Jb hJ₀ hJb
    (ODESourceBranches.sourceVector v b T N) seed hSeed x
    (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)
    (ODESourceBranches.propagation (ODEPublicSourceMesh.generator D x) T N)
    hPrep hTarget hNorm hSourceBudget hPaddedLCHS hQuadrature

end
end SparseHamiltonian.ODEActualPrimitiveEndpoint
