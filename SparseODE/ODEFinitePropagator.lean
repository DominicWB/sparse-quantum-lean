import SparseODE.ODECoefficientPadding

/-!
# A counted finite LCHS block with normalization exactly three

Two cancelling zero-duration branches fix the normalization without changing
the ideal finite sum. The coherent circuit is constructed from the original
sparse oracles, and its count is put into the improved ODE precision budget.
The Gaussian approximation is deliberately a separate analytic obligation.

-/

namespace SparseHamiltonian.ODEFinitePropagator

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
    (s γ ρ T δ : ℝ) := ODENativeLCU.Physical (ι ⊕ Bool) n Z s γ ρ T δ

abbrev oracle (D : Data X n Z s) (γ ρ T δ : ℝ) :
    Query → X → Physical ι n Z (s : ℝ) γ ρ T δ →L[ℂ]
      Physical ι n Z (s : ℝ) γ ρ T δ :=
  ODENativeLCU.oracle (ι := ι ⊕ Bool) D γ ρ T δ

/-- The extra zero-duration branches also provide a public native dummy label. -/
def input (D : Data X n Z s) (γ ρ T δ : ℝ) (c : ι → ℂ) :
    EuclideanSpace ℂ n →L[ℂ] Physical ι n Z (s : ℝ) γ ρ T δ :=
  ODENativeLCU.input D (Sum.inr false : ι ⊕ Bool) γ ρ T δ
    (ODECoefficientPadding.paddedCoefficient c 3)

def output (D : Data X n Z s) (γ ρ T δ : ℝ) (c : ι → ℂ) :
    EuclideanSpace ℂ n →L[ℂ] Physical ι n Z (s : ℝ) γ ρ T δ :=
  ODENativeLCU.output D (Sum.inr false : ι ⊕ Bool) γ ρ T δ
    (ODECoefficientPadding.paddedCoefficient c 3)

/-- Apply the already proved scalar conversion to the actual native count. -/
theorem query_bound (q : ℕ) (s etaH etaD T g ε : ℝ)
    (hs : 0 ≤ s) (hH : 0 ≤ etaH) (hD : 0 ≤ etaD) (hT : 0 ≤ T)
    (hg : 1 ≤ g) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hq : (q : ℝ) ≤ 663552 * ImprovedPrecisionBudget.shape (2 * s)
      ((etaH + ImprovedODEQueryBudget.radius g ε * etaD) * T)
      (ImprovedPrecisionBudget.targetLog (ImprovedODEQueryBudget.precision g ε))) :
    (q : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape s
      (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
      (ImprovedODEQueryBudget.logBudget g ε) := by
  have hTime : (etaH + ImprovedODEQueryBudget.radius g ε * etaD) * T =
      ImprovedODEQueryBudget.effectiveTime (T * etaH) (T * etaD) g ε := by
    unfold ImprovedODEQueryBudget.effectiveTime
    ring
  change (q : ℝ) ≤ 663552 * ImprovedODEQueryBudget.queryShape (2 * s)
    ((etaH + ImprovedODEQueryBudget.radius g ε * etaD) * T)
    (ImprovedODEQueryBudget.simulationLog g ε) at hq
  rw [hTime] at hq
  have h := ImprovedODEQueryBudget.selected_query_bound 663552 (q : ℝ) s
    (T * etaH) (T * etaD) g ε (by norm_num) hs (mul_nonneg hT hH)
    (mul_nonneg hT hD) hg hε hεOne hq
  calc
    (q : ℝ) ≤ 16 * 663552 * ImprovedODEQueryBudget.queryShape s
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
        (ImprovedODEQueryBudget.logBudget g ε) := h
    _ = _ := by ring

/-- An actual native unitary has a successful block approximating the desired
finite sum divided by three. Its matrix queries obey the improved selected
ODE budget. Supplying a separate LCHS error of 2nu gives propagator error 5nu.
The theorem constructs neither the Gaussian coefficients nor amplification. -/
theorem finite_lchs (D : Data X n Z s)
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
        ∃ p : MultiOracleCircuit.Program (oracle (ι := ι) D γ ρ T ν),
          (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ)
            (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
            (ImprovedODEQueryBudget.logBudget g ε) ∧
          (∀ x, IsUnitary (p.eval x)) ∧
          ∀ c : ι → ℂ, ODECoherentLCU.coefficientMass c ≤ 3 →
            (input D γ ρ T ν c)† ∘L input D γ ρ T ν c = 1 ∧
            (output D γ ρ T ν c)† ∘L output D γ ρ T ν c = 1 ∧
            ∀ x,
              ‖(3 : ℂ) • ((output D γ ρ T ν c)† ∘L p.eval x ∘L input D γ ρ T ν c) -
                ODENativeLCU.finiteSum D k u c x‖ ≤ 3 * ν ∧
              ∀ S : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n,
                ‖ODENativeLCU.finiteSum D k u c x - S‖ ≤ 2 * ν →
                ‖(3 : ℂ) • ((output D γ ρ T ν c)† ∘L p.eval x ∘L input D γ ρ T ν c) -
                  S‖ ≤ 5 * ν := by
  dsimp only
  have hν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hνOne : ImprovedODEQueryBudget.precision g ε ≤ 1 :=
    (ImprovedODEQueryBudget.precision_le_one_ten_thousandth g ε hg hεOne).trans
      (by norm_num)
  have hR := ImprovedODEQueryBudget.radius_nonneg g ε hg hε hεOne
  obtain ⟨γ, hγ, hγOne, hWidth, hTables⟩ :=
    ODENativeLCU.finite_lcu (ι := ι ⊕ Bool) D (Sum.inr false)
      etaH etaD (ImprovedODEQueryBudget.radius g ε) T
      (ImprovedODEQueryBudget.precision g ε) hH hDiss hρ hT hν hνOne hrH hcH hrD hcD
  refine ⟨γ, hγ, hγOne, hWidth, ?_⟩
  intro k u hk hu huT
  obtain ⟨p, hCount, hUnitary, hCoefficients⟩ := hTables
    (ODECoefficientPadding.paddedNodes k) (ODECoefficientPadding.paddedDurations u)
    (ODECoefficientPadding.paddedNodes_bound k _ hR hk)
    (ODECoefficientPadding.paddedDurations_nonneg u hu)
    (ODECoefficientPadding.paddedDurations_le u T hT.le huT)
  refine ⟨p, query_bound p.count (s : ℝ) etaH etaD T g ε
    (Nat.cast_nonneg s) hH hDiss hT.le hg hε hεOne hCount, hUnitary, ?_⟩
  intro c hc
  have hMass := ODECoefficientPadding.coefficientMass_eq c 3 hc
  have hMassPos : 0 < ODECoherentLCU.coefficientMass
      (ODECoefficientPadding.paddedCoefficient c 3) := by
    rw [hMass]
    norm_num
  obtain ⟨hIn, hOut, hError⟩ := hCoefficients
    (ODECoefficientPadding.paddedCoefficient c 3) hMassPos
  refine ⟨hIn, hOut, fun x => ?_⟩
  have hScaled := (hError x).2
  rw [hMass, ODECoefficientPadding.finiteSum_eq D c 3 k u x] at hScaled
  refine ⟨hScaled, fun S hS => ?_⟩
  calc
    _ ≤ ‖(3 : ℂ) • ((output D γ (etaH + ImprovedODEQueryBudget.radius g ε * etaD) T
        (ImprovedODEQueryBudget.precision g ε) c)† ∘L p.eval x ∘L
          input D γ (etaH + ImprovedODEQueryBudget.radius g ε * etaD) T
            (ImprovedODEQueryBudget.precision g ε) c) - ODENativeLCU.finiteSum D k u c x‖ +
        ‖ODENativeLCU.finiteSum D k u c x - S‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 3 * ImprovedODEQueryBudget.precision g ε +
        2 * ImprovedODEQueryBudget.precision g ε := add_le_add hScaled hS
    _ = 5 * ImprovedODEQueryBudget.precision g ε := by ring

end
end SparseHamiltonian.ODEFinitePropagator
