import SparseODE.ODEJointCayley

/-!
# Coherent native Hamiltonian SELECT for the ODE solver

One optimized schedule implements all public LCHS nodes and all durations
between zero and the supplied positive horizon. The program uses only the
original primitive sparse queries, with spectator registers. Its full
operator error is uniform on arbitrary superpositions of the branch label.

-/

namespace SparseHamiltonian.ODEJointSimulation

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding CayleyClockInterface
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

abbrev Public (ι n : Type*) [Fintype ι] [Fintype n] := ODEJointNative.Public ι n
abbrev Private (ι n : Type*) [Fintype ι] [Fintype n] := ODEJointNative.Private ι n

abbrev Physical (ι n Z : Type*) [Fintype ι] [Fintype n] [Fintype Z]
    (s γ ρ T ε : ℝ) :=
  ODEJointNative.Physical ι n Z (ODENativeSimulation.slots s γ ρ T ε)
    (ODENativeSimulation.degree s γ ρ T ε)

abbrev oracle (D : Data X n Z s) (γ ρ T ε : ℝ) :
    Query → X → Physical ι n Z (s : ℝ) γ ρ T ε →L[ℂ]
      Physical ι n Z (s : ℝ) γ ρ T ε :=
  ODEJointNative.oracle D (ODENativeSimulation.slots (s : ℝ) γ ρ T ε)
    (ODENativeSimulation.degree (s : ℝ) γ ρ T ε)

def embedding (D : Data X n Z s) (i0 : ι) (γ ρ T ε : ℝ) :=
  ODEJointNative.embedding D i0 (ODENativeSimulation.slots (s : ℝ) γ ρ T ε)
    (ODENativeSimulation.degree (s : ℝ) γ ρ T ε)

/-- This clean input is independent of the LCHS nodes and branch durations. -/
def input (D : Data X n Z s) (i0 : ι) (γ ρ T ε : ℝ) :
    Public ι n →L[ℂ] Physical ι n Z (s : ℝ) γ ρ T ε :=
  (embedding D i0 γ ρ T ε).toContinuousLinearMap ∘L
    SharpClockQuery.evolutionInput (P := Public ι n) (V := Private ι n)
      (time (2 * (s : ℝ)) (ρ * T) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε

/-- The output encoding also depends only on the common public schedule. -/
def output (D : Data X n Z s) (i0 : ι) (γ ρ T ε : ℝ) :
    Public ι n →L[ℂ] Physical ι n Z (s : ℝ) γ ρ T ε :=
  (embedding D i0 γ ρ T ε).toContinuousLinearMap ∘L
    SharpClockSimulation.evolutionOutput (P := Public ι n) (V := Private ι n)
      (time (2 * (s : ℝ)) (ρ * T) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε

/-- The physical SELECT target, with the actual duration in each block. -/
def evolution (D : Data X n Z s) (k u : ι → ℝ) (x : X) :
    Public ι n →L[ℂ] Public ι n :=
  WeightedClock.diagonal (fun i => NormedSpace.exp
    ((-Complex.I * (u i : ℂ)) • SparseStateOverlap.matrixOperator
      (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i))))

/-- The active circuit acts on the joint public/private system; no separate
per-branch invocation of the Hamiltonian simulator is required. -/
theorem active_implementsOn (D : Data X n Z s) (i0 : ι)
    (k u : ι → ℝ) (γ ρ T ε : ℝ) (r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (oracle (ι := ι) D γ ρ T ε)
      (fun x => SharpLabeledActiveClockQuery.evolutionActiveClock
        (P := Public ι n) (ODEJointCayley.action D x k u ρ T γ)
        (time (2 * (s : ℝ)) (ρ * T) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε r)
      (embedding D i0 γ ρ T ε).toContinuousLinearMap 72 :=
  ODEJointNative.implementsOn D i0 k (fun i => γ * (u i / T)) ρ
    (ODENativeSimulation.slots (s : ℝ) γ ρ T ε)
    (ODENativeSimulation.degree (s : ℝ) γ ρ T ε) r

/-- Actual coherent native simulation at one public rescaling. Every circuit
and analytic obligation follows from the original input data. -/
theorem native_at_scale (D : Data X n Z s) (i0 : ι)
    (etaH etaD R T : ℝ) (k u : ι → ℝ) (γ ε : ℝ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hρ : 0 < etaH + R * etaD)
    (hT : 0 < T) (hk : ∀ i, |k i| ≤ R)
    (hu : ∀ i, 0 ≤ u i) (huT : ∀ i, u i ≤ T)
    (hγ : 0 < γ) (hγOne : γ ≤ 1) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hBudget : time (2 * (s : ℝ)) ((etaH + R * etaD) * T) γ * moment γ +
      width (2 * (s : ℝ)) γ * ImprovedPrecisionBudget.circuitLog ε ≤
        12 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) ((etaH + R * etaD) * T)
          (ImprovedPrecisionBudget.targetLog ε)) :
    ∃ p : MultiOracleCircuit.Program (oracle (ι := ι) D γ (etaH + R * etaD) T ε),
      (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape
        (2 * (s : ℝ)) ((etaH + R * etaD) * T) (ImprovedPrecisionBudget.targetLog ε) ∧
      (input D i0 γ (etaH + R * etaD) T ε)† ∘L input D i0 γ (etaH + R * etaD) T ε = 1 ∧
      (output D i0 γ (etaH + R * etaD) T ε)† ∘L output D i0 γ (etaH + R * etaD) T ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L input D i0 γ (etaH + R * etaD) T ε -
          output D i0 γ (etaH + R * etaD) T ε ∘L evolution D k u x‖ ≤ ε := by
  obtain ⟨p, hCount, hIn, hOut, hAction⟩ :=
    ODEJointCayley.query_certificate (Label := Query)
      (K := Physical ι n Z (s : ℝ) γ (etaH + R * etaD) T ε)
      D etaH etaD R T k u hH hDiss hρ hT hk hu huT hrH hcH hrD hcD
      γ ε hγ hγOne hε hεOne hBudget (oracle D γ (etaH + R * etaD) T ε)
      (ODEJointNative.oracle_unitary D
        (ODENativeSimulation.slots (s : ℝ) γ (etaH + R * etaD) T ε)
        (ODENativeSimulation.degree (s : ℝ) γ (etaH + R * etaD) T ε))
      (embedding D i0 γ (etaH + R * etaD) T ε).toContinuousLinearMap
      (embedding D i0 γ (etaH + R * etaD) T ε).adjoint_comp_self
      72 (fun r _ => active_implementsOn D i0 k u γ (etaH + R * etaD) T ε r)
  refine ⟨p, ?_, hIn, hOut, fun x => ?_⟩
  · calc
      (p.count : ℝ) ≤ 9216 * (72 : ℝ) * ImprovedPrecisionBudget.shape
          (2 * (s : ℝ)) ((etaH + R * etaD) * T) (ImprovedPrecisionBudget.targetLog ε) := hCount
      _ = 663552 * ImprovedPrecisionBudget.shape
          (2 * (s : ℝ)) ((etaH + R * etaD) * T) (ImprovedPrecisionBudget.targetLog ε) := by ring
  · obtain ⟨hUnitary, hError⟩ := hAction x
    rw [CoherentDiagonalExp.exp_diagonal
      (V := fun _ : ι => EuclideanSpace ℂ n)
      (fun i : ι => (-Complex.I * (u i : ℂ)) •
        SparseStateOverlap.matrixOperator
          (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) (k i)))] at hError
    exact ⟨hUnitary, hError⟩

/-- One optimized rescaling and fixed pair of encodings work for every finite
node/duration table within the public bounds. Query complexity and full
operator error have no branch-cardinality factor. Zero-duration blocks are
included; the common horizon and energy radius are assumed positive. -/
theorem exists_coherent_native_simulation (D : Data X n Z s) (i0 : ι)
    (etaH etaD R T ε : ℝ) (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD)
    (hρ : 0 < etaH + R * etaD) (hT : 0 < T) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) :
    let ρ := etaH + R * etaD
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ k u : ι → ℝ, (∀ i, |k i| ≤ R) → (∀ i, 0 ≤ u i) → (∀ i, u i ≤ T) →
        ∃ p : MultiOracleCircuit.Program (oracle (ι := ι) D γ ρ T ε),
          (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape
            (2 * (s : ℝ)) (ρ * T) (ImprovedPrecisionBudget.targetLog ε) ∧
          (input D i0 γ ρ T ε)† ∘L input D i0 γ ρ T ε = 1 ∧
          (output D i0 γ ρ T ε)† ∘L output D i0 γ ρ T ε = 1 ∧
          ∀ x, IsUnitary (p.eval x) ∧
            ‖p.eval x ∘L input D i0 γ ρ T ε -
              output D i0 γ ρ T ε ∘L evolution D k u x‖ ≤ ε := by
  dsimp only
  have hs : (1 : ℝ) ≤ s := by
    have hsNat : 1 ≤ s := D.slots_pos
    exact_mod_cast hsNat
  have hsTwo : (1 : ℝ) ≤ 2 * (s : ℝ) := by linarith
  obtain ⟨γ, hγ, hγOne, hWidth, hBudget⟩ :=
    ImprovedPrecisionBudget.exists_rescaling_for_precision
      (2 * (s : ℝ)) ((etaH + R * etaD) * T) ε hsTwo
      (mul_nonneg hρ.le hT.le) hε hεOne
  refine ⟨γ, hγ, hγOne, hWidth, ?_⟩
  intro k u hk hu huT
  exact native_at_scale D i0 etaH etaD R T k u γ ε hH hDiss hρ hT hk hu huT
    hγ hγOne hε hεOne hrH hcH hrD hcD hBudget

end
end SparseHamiltonian.ODEJointSimulation
