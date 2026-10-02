import SparseODE.ODEJointSimulation

/-!
# Coherent native simulation with one clean input/output encoding

The known final alignment is a free unitary and preserves the count of every
native oracle label. Its Boolean register is an untouched query spectator.
The rescaling and clean encoding are chosen before the LCHS node/duration
table, so the same preparation is available for the subsequent source LCU.

-/

namespace SparseHamiltonian.ODECoherentSimulation

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

abbrev Public (ι n : Type*) [Fintype ι] [Fintype n] :=
  ODEJointSimulation.Public ι n

/-- The sole extra workspace is the alignment spectator. -/
abbrev Physical (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z]
    (s γ ρ T ε : ℝ) :=
  CleanOutputAlignment.Double (ODEJointSimulation.Physical ι n Z s γ ρ T ε)

/-- All counted calls remain original native sparse primitives. -/
abbrev oracle (D : Data X n Z s) (γ ρ T ε : ℝ) :
    Query → X → Physical ι n Z (s : ℝ) γ ρ T ε →L[ℂ]
      Physical ι n Z (s : ℝ) γ ρ T ε :=
  AlignedMultiOracleProgram.oracle (ODEJointSimulation.oracle (ι := ι) D γ ρ T ε)

/-- One fixed clean preparation, independent of the node/duration table. -/
def input (D : Data X n Z s) (i0 : ι) (γ ρ T ε : ℝ) :
    Public ι n →L[ℂ] Physical ι n Z (s : ℝ) γ ρ T ε :=
  AlignedMultiOracleProgram.input (ODEJointSimulation.input D i0 γ ρ T ε)

omit [DecidableEq ι] [DecidableEq Z] in
theorem native_oracle_unitary (D : Data X n Z s) (γ ρ T ε : ℝ)
    (l : Query) (x : X) :
    IsUnitary (ODEJointSimulation.oracle (ι := ι) D γ ρ T ε l x) :=
  ODEJointNative.oracle_unitary D
    (ODENativeSimulation.slots (s : ℝ) γ ρ T ε)
    (ODENativeSimulation.degree (s : ℝ) γ ρ T ε) l x

omit [DecidableEq ι] [DecidableEq Z] in
theorem oracle_unitary (D : Data X n Z s) (γ ρ T ε : ℝ)
    (l : Query) (x : X) : IsUnitary (oracle (ι := ι) D γ ρ T ε l x) :=
  CoherentQuerySchedule.oracle_unitary
    (ODEJointSimulation.oracle (ι := ι) D γ ρ T ε)
    (native_oracle_unitary D γ ρ T ε) l x

/-- One common clean encoding and optimized schedule implement every allowed
coherent node/duration table, uniformly over the unknown sparse matrix.
There is no branch-cardinality factor or controlled-oracle assumption. -/
theorem simulation (D : Data X n Z s) (i0 : ι)
    (etaH etaD R T ε : ℝ) (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD)
    (hρ : 0 < etaH + R * etaD) (hT : 0 < T) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) :
    let ρ := etaH + R * etaD
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ k u : ι → ℝ, (∀ i, |k i| ≤ R) → (∀ i, 0 ≤ u i) → (∀ i, u i ≤ T) →
        ∃ p : MultiOracleCircuit.Program
            (K := Physical ι n Z (s : ℝ) γ ρ T ε) (oracle D γ ρ T ε),
          (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape
            (2 * (s : ℝ)) (ρ * T) (ImprovedPrecisionBudget.targetLog ε) ∧
          (input D i0 γ ρ T ε)† ∘L input D i0 γ ρ T ε = 1 ∧
          ∀ x, IsUnitary (p.eval x) ∧
            ‖p.eval x ∘L input D i0 γ ρ T ε -
              input D i0 γ ρ T ε ∘L ODEJointSimulation.evolution D k u x‖ ≤ ε := by
  dsimp only
  obtain ⟨γ, hγ, hγOne, hWidth, hTables⟩ :=
    ODEJointSimulation.exists_coherent_native_simulation D i0 etaH etaD R T ε
      hH hDiss hρ hT hε hεOne hrH hcH hrD hcD
  refine ⟨γ, hγ, hγOne, hWidth, ?_⟩
  intro k u hk hu huT
  obtain ⟨p, hCount, hIn, hOut, hAction⟩ := hTables k u hk hu huT
  obtain ⟨q, hCountEq, _hCosts, hInput, hAligned⟩ :=
    AlignedMultiOracleProgram.exists_aligned_program
      (P := Public ι n)
      (K := ODEJointSimulation.Physical ι n Z (s : ℝ) γ (etaH + R * etaD) T ε)
      (ODEJointSimulation.oracle D γ (etaH + R * etaD) T ε)
      (native_oracle_unitary D γ (etaH + R * etaD) T ε)
      (ODEJointSimulation.input D i0 γ (etaH + R * etaD) T ε)
      (ODEJointSimulation.output D i0 γ (etaH + R * etaD) T ε) hIn hOut p
      (ODEJointSimulation.evolution D k u) ε (fun x => (hAction x).2)
  refine ⟨q, ?_, hInput, hAligned⟩
  rw [hCountEq]
  exact hCount

end
end SparseHamiltonian.ODECoherentSimulation
