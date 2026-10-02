import SparseODE.ODEFixedTaggedQuery

namespace SparseHamiltonian.ODENativeSimulation

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding CayleyClockInterface
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {X n Z : Type*} [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- The tagged private space has moment parameter 2s, and the normalized
physical duration is rho*t. These public schedule sizes do not depend on k. -/
def slots (s γ ρ t ε : ℝ) : ℕ :=
  ImprovedNativeSimulation.slots (2 * s) γ (ρ * t) ε

def degree (s γ ρ t ε : ℝ) : ℕ :=
  ImprovedNativeSimulation.degree (2 * s) γ (ρ * t) ε

abbrev oracle (D : Data X n Z s) (γ ρ t ε : ℝ) :=
  ODENativeActive.oracle D (slots (s : ℝ) γ ρ t ε) (degree (s : ℝ) γ ρ t ε)

/-- The encoding is fixed across all branches at a given public schedule. -/
def embedding (D : Data X n Z s) (γ ρ t ε : ℝ) :=
  ODENativeActive.embedding D (slots (s : ℝ) γ ρ t ε) (degree (s : ℝ) γ ρ t ε)

def input (D : Data X n Z s) (γ ρ t ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ]
      ODENativeActive.Physical n Z (slots (s : ℝ) γ ρ t ε)
        (degree (s : ℝ) γ ρ t ε) :=
  (embedding D γ ρ t ε).toContinuousLinearMap ∘L
    SharpClockQuery.evolutionInput (P := EuclideanSpace ℂ n)
      (V := ODETaggedMoments.PrivateSpace n)
      (time (2 * (s : ℝ)) (ρ * t) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε

def output (D : Data X n Z s) (γ ρ t ε : ℝ) :
    EuclideanSpace ℂ n →L[ℂ]
      ODENativeActive.Physical n Z (slots (s : ℝ) γ ρ t ε)
        (degree (s : ℝ) γ ρ t ε) :=
  (embedding D γ ρ t ε).toContinuousLinearMap ∘L
    SharpClockSimulation.evolutionOutput (P := EuclideanSpace ℂ n)
      (V := ODETaggedMoments.PrivateSpace n)
      (time (2 * (s : ℝ)) (ρ * t) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε

/-- All native-control and original sparse-query obligations are discharged
by the previously constructed 72-call active circuit. -/
theorem active_implementsOn (D : Data X n Z s) (k γ ρ t ε : ℝ) (r : ℕ) :
    LabeledEncodedOracle.ImplementsOn (oracle D γ ρ t ε)
      (fun x => SharpLabeledActiveClockQuery.evolutionActiveClock
        (P := EuclideanSpace ℂ n) (ODEFixedTaggedMoments.action D x
          (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) ρ γ)
        (time (2 * (s : ℝ)) (ρ * t) γ) (width (2 * (s : ℝ)) γ) (moment γ) ε r)
      (embedding D γ ρ t ε).toContinuousLinearMap 72 :=
  ODENativeActive.implementsOn D k γ ρ (slots (s : ℝ) γ ρ t ε)
    (degree (s : ℝ) γ ρ t ε) r

/-- An actual primitive sparse-oracle simulation at a supplied public
rescaling. The assumptions concern only entry energies and scalar parameters;
there is no controlled-oracle or implementation premise. -/
theorem native_at_scale (D : Data X n Z s) (k γ ρ t ε : ℝ)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hγOne : γ ≤ 1)
    (ht : 0 ≤ t) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hrow : ∀ x i, ∑ j, ‖ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k i j‖ ^ 2 ≤ ρ ^ 2)
    (hcol : ∀ x j, ∑ i, ‖ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k i j‖ ^ 2 ≤ ρ ^ 2)
    (hBudget : time (2 * (s : ℝ)) (ρ * t) γ * moment γ +
      width (2 * (s : ℝ)) γ * ImprovedPrecisionBudget.circuitLog ε ≤
        12 * ImprovedPrecisionBudget.shape (2 * (s : ℝ)) (ρ * t)
          (ImprovedPrecisionBudget.targetLog ε)) :
    ∃ p : MultiOracleCircuit.Program
        (K := ODENativeActive.Physical n Z (slots (s : ℝ) γ ρ t ε)
          (degree (s : ℝ) γ ρ t ε)) (oracle D γ ρ t ε),
      (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape
        (2 * (s : ℝ)) (ρ * t) (ImprovedPrecisionBudget.targetLog ε) ∧
      (input D γ ρ t ε)† ∘L input D γ ρ t ε = 1 ∧
      (output D γ ρ t ε)† ∘L output D γ ρ t ε = 1 ∧
      ∀ x, IsUnitary (p.eval x) ∧
        ‖p.eval x ∘L input D γ ρ t ε - output D γ ρ t ε ∘L
          NormedSpace.exp ((-Complex.I * (t : ℂ)) •
            SparseStateOverlap.matrixOperator
              (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k))‖ ≤ ε := by
  obtain ⟨p, hCount, hIn, hOut, hAction⟩ :=
    ODEFixedTaggedQuery.query_certificate
      (Label := Query)
      (K := ODENativeActive.Physical n Z (slots (s : ℝ) γ ρ t ε)
        (degree (s : ℝ) γ ρ t ε)) D
      (fun x => ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k) ρ hρ
      (fun x => ODEMatrixEnergy.lchsHamiltonian_isHermitian (D.matrix x) k)
      (fun x => ODEMatrixEnergy.lchsHamiltonian_eq_zero (D.matrix x) k)
      hrow hcol γ t ε hγ hγOne ht hε hεOne hBudget (oracle D γ ρ t ε)
      (ODENativeActive.oracle_unitary D (slots (s : ℝ) γ ρ t ε)
        (degree (s : ℝ) γ ρ t ε))
      (embedding D γ ρ t ε).toContinuousLinearMap (embedding D γ ρ t ε).adjoint_comp_self
      72 (fun r _ => active_implementsOn D k γ ρ t ε r)
  refine ⟨p, ?_, hIn, hOut, hAction⟩
  calc
    (p.count : ℝ) ≤ 9216 * (72 : ℝ) * ImprovedPrecisionBudget.shape
        (2 * (s : ℝ)) (ρ * t) (ImprovedPrecisionBudget.targetLog ε) := hCount
    _ = 663552 * ImprovedPrecisionBudget.shape
        (2 * (s : ℝ)) (ρ * t) (ImprovedPrecisionBudget.targetLog ε) := by ring

/-- One optimized rescaling, physical register and input/output encoding work
for every real LCHS node in the public interval. This is a uniform family of
individual programs. `ODECoherentSimulation.simulation` supplies the coherent
node/duration construction. -/
theorem exists_uniform_lchs_simulations (D : Data X n Z s)
    (etaH etaD R t ε : ℝ) (hH : 0 ≤ etaH) (hD : 0 ≤ etaD)
    (hρ : 0 < etaH + R * etaD) (ht : 0 ≤ t) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) :
    let ρ := etaH + R * etaD
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ k : ℝ, |k| ≤ R →
        ∃ p : MultiOracleCircuit.Program
            (K := ODENativeActive.Physical n Z (slots (s : ℝ) γ ρ t ε)
              (degree (s : ℝ) γ ρ t ε)) (oracle D γ ρ t ε),
          (p.count : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape
            (2 * (s : ℝ)) (ρ * t) (ImprovedPrecisionBudget.targetLog ε) ∧
          (input D γ ρ t ε)† ∘L input D γ ρ t ε = 1 ∧
          (output D γ ρ t ε)† ∘L output D γ ρ t ε = 1 ∧
          ∀ x, IsUnitary (p.eval x) ∧
            ‖p.eval x ∘L input D γ ρ t ε - output D γ ρ t ε ∘L
              NormedSpace.exp ((-Complex.I * (t : ℂ)) •
                SparseStateOverlap.matrixOperator
                  (ODEMatrixEnergy.lchsHamiltonian (D.matrix x) k))‖ ≤ ε := by
  dsimp only
  have hs : (1 : ℝ) ≤ s := by
    have hsNat : 1 ≤ s := D.slots_pos
    exact_mod_cast hsNat
  have hsTwo : (1 : ℝ) ≤ 2 * (s : ℝ) := by linarith
  obtain ⟨γ, hγ, hγOne, hWidth, hBudget⟩ :=
    ImprovedPrecisionBudget.exists_rescaling_for_precision
      (2 * (s : ℝ)) ((etaH + R * etaD) * t) ε hsTwo
      (mul_nonneg hρ.le ht) hε hεOne
  refine ⟨γ, hγ, hγOne, hWidth, ?_⟩
  intro k hk
  have hEnergy := fun x => ODEMatrixEnergy.lchs_energies_le_radius
    (D.matrix x) etaH etaD k R hH hD hk (hrH x) (hcH x) (hrD x) (hcD x)
  exact native_at_scale D k γ (etaH + R * etaD) t ε hρ hγ hγOne ht hε hεOne
    (fun x => (hEnergy x).1) (fun x => (hEnergy x).2) hBudget

end
end SparseHamiltonian.ODENativeSimulation
