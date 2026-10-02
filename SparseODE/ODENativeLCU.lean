import SparseODE.ODEJointLCU

/-!
# A finite complex LCU from the actual native coherent simulator

The SELECT program is chosen before the coefficients. Its native query count
therefore applies to every finite coefficient table, with no multiplier for
the number of LCHS nodes. Known coefficient preparations are composed with
the simulator's fixed clean encoding. This establishes the actual successful
block for a finite sum; it does not assume or claim a Gaussian LCHS formula.

-/

namespace SparseHamiltonian.ODENativeLCU

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

abbrev Physical (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z]
    (s γ ρ T δ : ℝ) := ODECoherentSimulation.Physical ι n Z s γ ρ T δ

/-- The LCU uses exactly the original coherent simulator's native primitives. -/
abbrev oracle (D : Data X n Z s) (γ ρ T δ : ℝ) :
    Query → X → Physical ι n Z (s : ℝ) γ ρ T δ →L[ℂ]
      Physical ι n Z (s : ℝ) γ ρ T δ :=
  ODECoherentSimulation.oracle (ι := ι) D γ ρ T δ

/-- Known square-root coefficient weights, followed by the common encoding. -/
def input (D : Data X n Z s) (i0 : ι) (γ ρ T δ : ℝ) (c : ι → ℂ) :
    EuclideanSpace ℂ n →L[ℂ] Physical ι n Z (s : ℝ) γ ρ T δ :=
  ODEJointLCU.input (ODECoherentSimulation.input D i0 γ ρ T δ) c

/-- The output phases recover the complex coefficients without conjugation. -/
def output (D : Data X n Z s) (i0 : ι) (γ ρ T δ : ℝ) (c : ι → ℂ) :
    EuclideanSpace ℂ n →L[ℂ] Physical ι n Z (s : ℝ) γ ρ T δ :=
  ODEJointLCU.output (ODECoherentSimulation.input D i0 γ ρ T δ) c

/-- The exact physical Hamiltonian evolution for one retained node/duration. -/
def branchEvolution (D : Data X n Z s) (k u : ι → ℝ) (x : X) (i : ι) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  NormedSpace.exp ((-Complex.I * (u i : ℂ)) • SparseStateOverlap.matrixOperator
    (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)))

/-- The actual finite exponential sum, before coefficient normalization. -/
def finiteSum (D : Data X n Z s) (k u : ι → ℝ) (c : ι → ℂ) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  ∑ i, c i • branchEvolution D k u x i

def normalizedTarget (D : Data X n Z s) (k u : ι → ℝ) (c : ι → ℂ) (x : X) :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  ODEJointLCU.normalizedSum c (branchEvolution D k u x)

/-- One counted SELECT circuit implements every known complex coefficient
choice. The native query count is unchanged, both preparations are isometries,
and the successful block approximates the normalized finite exponential sum.
The coefficient mass multiplies only the restored, unnormalized error. -/
theorem finite_lcu (D : Data X n Z s) (i0 : ι)
    (etaH etaD R T δ : ℝ) (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD)
    (hρ : 0 < etaH + R * etaD) (hT : 0 < T) (hδ : 0 < δ) (hδOne : δ ≤ 1)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) :
    let ρ := etaH + R * etaD
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ k u : ι → ℝ, (∀ i, |k i| ≤ R) → (∀ i, 0 ≤ u i) → (∀ i, u i ≤ T) →
        ∃ p : MultiOracleCircuit.Program
            (K := Physical ι n Z (s : ℝ) γ ρ T δ) (oracle D γ ρ T δ),
          (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape
            (2 * (s : ℝ)) (ρ * T) (ImprovedPrecisionBudget.targetLog δ) ∧
          (∀ x, IsUnitary (p.eval x)) ∧
          ∀ c : ι → ℂ, 0 < ODECoherentLCU.coefficientMass c →
            (input D i0 γ ρ T δ c)† ∘L input D i0 γ ρ T δ c = 1 ∧
            (output D i0 γ ρ T δ c)† ∘L output D i0 γ ρ T δ c = 1 ∧
            ∀ x,
              ‖(output D i0 γ ρ T δ c)† ∘L p.eval x ∘L input D i0 γ ρ T δ c -
                normalizedTarget D k u c x‖ ≤ δ ∧
              ‖(ODECoherentLCU.coefficientMass c : ℂ) •
                ((output D i0 γ ρ T δ c)† ∘L p.eval x ∘L input D i0 γ ρ T δ c) -
                  finiteSum D k u c x‖ ≤ ODECoherentLCU.coefficientMass c * δ := by
  dsimp only
  obtain ⟨γ, hγ, hγOne, hWidth, hTables⟩ :=
    ODECoherentSimulation.simulation D i0 etaH etaD R T δ
      hH hDiss hρ hT hδ hδOne hrH hcH hrD hcD
  refine ⟨γ, hγ, hγOne, hWidth, ?_⟩
  intro k u hk hu huT
  obtain ⟨p, hCount, hE, hAction⟩ := hTables k u hk hu huT
  refine ⟨p, hCount, fun x => (hAction x).1, ?_⟩
  intro c hc
  let E := ODECoherentSimulation.input D i0 γ (etaH + R * etaD) T δ
  refine ⟨ODEJointLCU.input_isometry E c hE hc,
    ODEJointLCU.output_isometry E c hE hc, ?_⟩
  intro x
  have hError : ‖p.eval x ∘L E - E ∘L
      WeightedClock.diagonal (branchEvolution D k u x)‖ ≤ δ := (hAction x).2
  constructor
  · exact ODEJointLCU.compression_error E c hE hc (p.eval x)
      (branchEvolution D k u x) δ hError
  · exact ODEJointLCU.scaled_compression_error E c hE hc (p.eval x)
      (branchEvolution D k u x) δ hError

end
end SparseHamiltonian.ODENativeLCU
