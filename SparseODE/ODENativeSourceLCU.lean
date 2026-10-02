import SparseODE.ODESourcePreparations

/-!
# Native sparse simulation with supplied branch source preparations

One coherent native simulator is chosen before both the complex coefficients
and the known isometric source-preparation maps. Its original row, column,
and value queries have no multiplier for either the number of source labels
or the number of LCHS nodes. The input encoding includes the supplied sources;
constructing and counting their preparation calls is a separate obligation.

-/

namespace SparseHamiltonian.ODENativeSourceLCU

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
    (s γ ρ T δ : ℝ) := ODENativeLCU.Physical ι n Z s γ ρ T δ

/-- The unchanged sparse-oracle family; source preparations are separate inputs. -/
abbrev oracle (D : Data X n Z s) (γ ρ T δ : ℝ) :
    Query → X → Physical ι n Z (s : ℝ) γ ρ T δ →L[ℂ]
      Physical ι n Z (s : ℝ) γ ρ T δ :=
  ODENativeLCU.oracle (ι := ι) D γ ρ T δ

/-- Coherent supplied sources composed with the common clean encoding. -/
def input (D : Data X n Z s) (i0 : ι) (γ ρ T δ : ℝ) (c : ι → ℂ)
    (J : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    EuclideanSpace ℂ n →L[ℂ] Physical ι n Z (s : ℝ) γ ρ T δ :=
  ODEJointSourceLCU.input (ODECoherentSimulation.input D i0 γ ρ T δ) c J

/-- Output decoding erases coefficient labels and retains the public state. -/
def output (D : Data X n Z s) (i0 : ι) (γ ρ T δ : ℝ) (c : ι → ℂ) :
    EuclideanSpace ℂ n →L[ℂ] Physical ι n Z (s : ℝ) γ ρ T δ :=
  ODENativeLCU.output D i0 γ ρ T δ c

/-- Actual public vector in the successful output coordinates. -/
def decoded (D : Data X n Z s) (i0 : ι) (γ ρ T δ : ℝ) (c : ι → ℂ)
    (J : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (W : Physical ι n Z (s : ℝ) γ ρ T δ →L[ℂ]
      Physical ι n Z (s : ℝ) γ ρ T δ) (v : EuclideanSpace ℂ n) :
    EuclideanSpace ℂ n :=
  ODEJointSourceLCU.decoded (ODECoherentSimulation.input D i0 γ ρ T δ) c J W v

/-- The finite exponential source sum, with coefficient normalization restored. -/
def target (D : Data X n Z s) (k u : ι → ℝ) (c : ι → ℂ)
    (J : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (x : X) (v : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  ∑ i, c i • ODENativeLCU.branchEvolution D k u x i (J i v)

/-- The counted simulator controls the actual source-vector error. It is
chosen before the coefficient and source maps, so adding known source labels
or LCHS nodes does not multiply its matrix-query count. The isometric source
maps are supplied explicitly; this theorem does not construct them. -/
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
            ∀ J : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n,
              (∀ i, (J i)† ∘L J i = 1) →
              (input D i0 γ ρ T δ c J)† ∘L input D i0 γ ρ T δ c J = 1 ∧
              (output D i0 γ ρ T δ c)† ∘L output D i0 γ ρ T δ c = 1 ∧
              ∀ x v,
                ‖(ODECoherentLCU.coefficientMass c : ℂ) •
                    decoded D i0 γ ρ T δ c J (p.eval x) v - target D k u c J x v‖ ≤
                  ODECoherentLCU.coefficientMass c * δ * ‖v‖ ∧
                (‖v‖ = 1 → ‖input D i0 γ ρ T δ c J v‖ = 1 ∧
                  ‖p.eval x (input D i0 γ ρ T δ c J v)‖ = 1) := by
  dsimp only
  obtain ⟨γ, hγ, hγOne, hWidth, hTables⟩ :=
    ODECoherentSimulation.simulation D i0 etaH etaD R T δ
      hH hDiss hρ hT hδ hδOne hrH hcH hrD hcD
  refine ⟨γ, hγ, hγOne, hWidth, ?_⟩
  intro k u hk hu huT
  obtain ⟨p, hCount, hE, hAction⟩ := hTables k u hk hu huT
  refine ⟨p, hCount, fun x => (hAction x).1, ?_⟩
  intro c hc J hJ
  let E := ODECoherentSimulation.input D i0 γ (etaH + R * etaD) T δ
  have hIn : (input D i0 γ (etaH + R * etaD) T δ c J)† ∘L
      input D i0 γ (etaH + R * etaD) T δ c J = 1 :=
    ODEJointSourceLCU.input_isometry E c J hE hc hJ
  have hOut : (output D i0 γ (etaH + R * etaD) T δ c)† ∘L
      output D i0 γ (etaH + R * etaD) T δ c = 1 :=
    ODEJointLCU.output_isometry E c hE hc
  refine ⟨hIn, hOut, ?_⟩
  intro x v
  have hError : ‖p.eval x ∘L E - E ∘L
      WeightedClock.diagonal (ODENativeLCU.branchEvolution D k u x)‖ ≤ δ :=
    (hAction x).2
  constructor
  · exact ODEJointSourceLCU.actual_vector_error E c J hE hc hJ (p.eval x)
      (ODENativeLCU.branchEvolution D k u x) δ hError v
  · intro hv
    have hInputNorm : ‖input D i0 γ (etaH + R * etaD) T δ c J v‖ = 1 := by
      rw [(input D i0 γ (etaH + R * etaD) T δ c J).norm_map_iff_adjoint_comp_self.mpr hIn, hv]
    refine ⟨hInputNorm, ?_⟩
    rw [(p.eval x).norm_map_iff_adjoint_comp_self.mpr (hAction x).1.1, hInputNorm]


/-- Choosing the ODE radius and precision gives the improved selected-query
budget for the same source-aware native simulator. The finite coefficient
and source tables are still chosen after the counted program. -/
theorem native_selected (D : Data X n Z s) (i0 : ι)
    (etaH etaD T g ε : ℝ) (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD)
    (hρ : 0 < etaH + ImprovedODEQueryBudget.radius g ε * etaD)
    (hT : 0 < T) (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) :
    let R := ImprovedODEQueryBudget.radius g ε
    let ν := ImprovedODEQueryBudget.precision g ε
    let ρ := etaH + R * etaD
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ k u : ι → ℝ, (∀ i, |k i| ≤ R) → (∀ i, 0 ≤ u i) → (∀ i, u i ≤ T) →
        ∃ p : MultiOracleCircuit.Program
            (K := Physical ι n Z (s : ℝ) γ ρ T ν) (oracle D γ ρ T ν),
          (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ)
            (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
            (ImprovedODEQueryBudget.logBudget g ε) ∧
          (∀ x, IsUnitary (p.eval x)) ∧
          ∀ c : ι → ℂ, 0 < ODECoherentLCU.coefficientMass c →
            ∀ J : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n,
              (∀ i, (J i)† ∘L J i = 1) →
              (input D i0 γ ρ T ν c J)† ∘L input D i0 γ ρ T ν c J = 1 ∧
              (output D i0 γ ρ T ν c)† ∘L output D i0 γ ρ T ν c = 1 ∧
              ∀ x v,
                ‖(ODECoherentLCU.coefficientMass c : ℂ) •
                    decoded D i0 γ ρ T ν c J (p.eval x) v - target D k u c J x v‖ ≤
                  ODECoherentLCU.coefficientMass c * ν * ‖v‖ ∧
                (‖v‖ = 1 → ‖input D i0 γ ρ T ν c J v‖ = 1 ∧
                  ‖p.eval x (input D i0 γ ρ T ν c J v)‖ = 1) := by
  dsimp only
  have hν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hνOne : ImprovedODEQueryBudget.precision g ε ≤ 1 :=
    (ImprovedODEQueryBudget.precision_le_one_ten_thousandth g ε hg hεOne).trans
      (by norm_num)
  obtain ⟨γ, hγ, hγOne, hWidth, hTables⟩ :=
    finite_lcu D i0 etaH etaD (ImprovedODEQueryBudget.radius g ε) T
      (ImprovedODEQueryBudget.precision g ε)
      hH hDiss hρ hT hν hνOne hrH hcH hrD hcD
  refine ⟨γ, hγ, hγOne, hWidth, ?_⟩
  intro k u hk hu huT
  obtain ⟨p, hCount, hUnitary, hSources⟩ := hTables k u hk hu huT
  refine ⟨p, ?_, hUnitary, hSources⟩
  exact ODEFinitePropagator.query_bound p.count (s : ℝ) etaH etaD T g ε
    (Nat.cast_nonneg s) hH hDiss hT.le hg hε hεOne hCount

end
end SparseHamiltonian.ODENativeSourceLCU
