import SparseODE.ODEFinalNativeSource

/-!
# Native ODE endpoint with explicit approximation hypotheses

This extension keeps the fixed encoding isometry already proved by the native
simulation theorem. It will join the actual source-loaded preparation to the
primitive-control compiler and the randomized amplification certificate.
The finite LCHS operator error and source quadrature error remain explicit
mathematical hypotheses; Gaussian coefficient construction is not claimed.

-/

namespace SparseHamiltonian.ODENativeSourceCertificate

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
set_option maxHeartbeats 3000000

variable {σ ι X n Z : Type*}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n]
  [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- The native source certificate with the fixed input isometry retained.
Both the circuit error and the query bound are proved by the simulator. -/
theorem native_source_certificate_with_isometry (D : Data X n Z s) (i0 : σ × ι)
    (etaH etaD T g ε : ℝ) (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD)
    (hρ : 0 < etaH + ImprovedODEQueryBudget.radius g ε * etaD)
    (hT : 0 < T) (hg : 1 ≤ g) (hε : 0 < ε) (hεHalf : ε ≤ 1 / 2)
    (hrH : ∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) :
    let R := ImprovedODEQueryBudget.radius g ε
    let ν := ImprovedODEQueryBudget.precision g ε
    let ρ := etaH + R * etaD
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ 1 ≤ γ * Real.sqrt (2 * (s : ℝ)) ∧
      ∀ k u : σ × ι → ℝ,
        (∀ a, |k a| ≤ R) → (∀ a, 0 ≤ u a) → (∀ a, u a ≤ T) →
        ∃ p : MultiOracleCircuit.Program
            (K := Physical σ ι n Z (s : ℝ) γ ρ T ν) (oracle D γ ρ T ν),
          (p.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ)
            (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) g ε)
            (ImprovedODEQueryBudget.logBudget g ε) ∧
          (encoding D i0 γ ρ T ν)† ∘L encoding D i0 γ ρ T ν = 1 ∧
          (∀ x, IsUnitary (p.eval x)) ∧
          ∀ c : ι → ℂ, ODECoherentLCU.coefficientMass c = 3 →
            ∀ z : σ → EuclideanSpace ℂ n,
              ∀ J : σ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n,
                (∀ a, (J a)† ∘L J a = 1) →
                ∀ v : EuclideanSpace ℂ n, ‖v‖ = 1 →
                  (∀ a, z a ≠ 0 → J a v = ODEStateNormalization.unitDirection (z a)) →
                  ∀ x : X, ∀ target : EuclideanSpace ℂ n,
                    ∀ S : σ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n,
                      target ≠ 0 → ‖target‖ ≤ ODESourceBranches.mass z →
                      ODESourceBranches.mass z ≤ g * ‖target‖ →
                      (∀ a, ‖(∑ i, c i • ODENativeLCU.branchEvolution D k u x (a, i)) -
                          S a‖ ≤ 2 * ν) →
                      ‖(∑ a, S a (z a)) - target‖ ≤ ν * ODESourceBranches.mass z →
                      ODEActualSourceError.Certificate
                        (encoding D i0 γ ρ T ν) z c J (p.eval x) v target g ε := by
  dsimp only
  have hεOne : ε ≤ 1 := by linarith
  have hν := ImprovedODEQueryBudget.precision_pos g ε hg hε
  have hνOne : ImprovedODEQueryBudget.precision g ε ≤ 1 :=
    (ImprovedODEQueryBudget.precision_le_one_ten_thousandth g ε hg hεOne).trans
      (by norm_num)
  obtain ⟨γ, hγ, hγOne, hWidth, hTables⟩ :=
    ODECoherentSimulation.simulation (ι := σ × ι) D i0
      etaH etaD (ImprovedODEQueryBudget.radius g ε) T
      (ImprovedODEQueryBudget.precision g ε)
      hH hDiss hρ hT hν hνOne hrH hcH hrD hcD
  refine ⟨γ, hγ, hγOne, hWidth, ?_⟩
  intro k u hk hu huT
  obtain ⟨p, hCount, hE, hAction⟩ := hTables k u hk hu huT
  refine ⟨p, ?_, hE, fun x => (hAction x).1, ?_⟩
  · exact ODEFinitePropagator.query_bound p.count (s : ℝ) etaH etaD T g ε
      (Nat.cast_nonneg s) hH hDiss hT.le hg hε hεOne hCount
  · intro c hc z J hJ v hv hPrep x target S hTarget hNorm hBudget hLCHS hQuadrature
    let E := encoding D i0 γ
      (etaH + ImprovedODEQueryBudget.radius g ε * etaD) T
      (ImprovedODEQueryBudget.precision g ε)
    have hSimulation : ‖p.eval x ∘L E - E ∘L WeightedClock.diagonal
        (fun a : σ × ι => ODENativeLCU.branchEvolution D k u x (a.1, a.2))‖ ≤
          ImprovedODEQueryBudget.precision g ε := (hAction x).2
    exact ODEActualSourceError.actual_source_certificate E hE z c hc J hJ
      v hv hPrep (p.eval x) (hAction x).1
      (fun a i => ODENativeLCU.branchEvolution D k u x (a, i)) S
      target g ε hTarget hg hε hεHalf hNorm hBudget hSimulation hLCHS hQuadrature


end
end SparseHamiltonian.ODENativeSourceCertificate
