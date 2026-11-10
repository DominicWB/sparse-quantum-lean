import GeneralSourceExtensions.Mesh.Approx
import GeneralSourceExtensions.Mesh.Duhamel

/-!
# The mesh endpoints with the certificate on the propagated vector integral

The manuscript states the source certificate of eq. `ode:eq:source-interface-mass` on the
propagated vector integral, `‖∫₀ᵀ U(T, v) b(v) dv - ∑ ω_i U(T, v_i) b_i‖ ≤ ζ B`. On a mesh with
breakpoints the integral is `∑_r ∫_{t_r}^{t_{r+1}} U(T, v) b_r(v) dv`. For continuous pieces,
Duhamel's formula on the mesh (`mesh_duhamel`) identifies it with `x(T) - U(T, 0) x(0)`, so the
mesh endpoints hold with this certificate:

* `mesh_solver_integral`: `Mesh.mesh_solver` with continuous pieces and the integral certificate
  (`MeshIntegralOutcome`);
* `mesh_approx_solver_nonneg_integral`: `Mesh.mesh_approx_solver_nonneg` (mesh, approximate
  preparations, every `T ≥ 0`) with continuous pieces and the integral certificate
  (`MeshApproxIntegralOutcome`).
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSourceExtensions.Mesh

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE ratio accuracy radius precision
  lipschitz Index lchsCoefficients)
open SparseHamiltonian.GeneralSourceODE (SourceCall sources phases phases_norm)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- `MeshOutcome` for continuous pieces with the certificate on the propagated vector
integral. -/
def MeshIntegralOutcome (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (d : ℕ) (tf : ODERepeatProtocol.TrialFamily
      (MeshOracles.actualOracle (ι := Index D T (cq * gbar) ε) D m N d Pw J)
      (EuclideanSpace ℂ n)),
    tf.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
    (∀ j y, IsUnitary ((tf.circuit j).eval y)) ∧
    ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      (∀ r : Fin M, ContinuousOn (G r) (Icc (t r) (t ((r : ℕ) + 1)))) →
      (∀ r : Fin M, ContinuousOn (b r) (Icc (t r) (t ((r : ℕ) + 1)))) →
      (∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep (Pw x) (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → J x (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
          ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      ζ + cq * (sampleError D x t G + refinementError D t T N) ≤ ε / (2000 * gbar) →
      GeneralSourceODE.Oracles.ActualCertificate
        (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

/-- `MeshApproxBudgetOutcome` for continuous pieces with the certificate on the propagated vector
integral. -/
def MeshApproxIntegralOutcome (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Q : ℝ) : Prop :=
  ∃ (d : ℕ) (tf : ODERepeatProtocol.TrialFamily
      (MeshOracles.actualOracle (ι := Index D T (cq * gbar) ε) D m N d Pw J)
      (EuclideanSpace ℂ n)),
    tf.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
    (∀ j y, IsUnitary ((tf.circuit j).eval y)) ∧
    ∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
      (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
      (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
      ‖Pw x - P‖ ≤ δ → (∀ a, ‖J x a - L a‖ ≤ δ) →
      30 * ratio (cq * gbar) * δ ≤ 1 / 400 → 30 * ratio (cq * gbar) * δ ≤ ε / 20 →
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      (∀ r : Fin M, ContinuousOn (G r) (Icc (t r) (t ((r : ℕ) + 1)))) →
      (∀ r : Fin M, ContinuousOn (b r) (Icc (t r) (t ((r : ℕ) + 1)))) →
      (∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep P (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → L (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
          ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      ζ + cq * (sampleError D x t G + refinementError D t T N) ≤ ε / (2000 * gbar) →
      ApproxCertificate (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε ∧
      ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
        GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤ Q

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh, with the certificate on
the propagated vector integral.** Under the hypotheses of `mesh_solver`, for continuous generator
and forcing pieces, the public trial family over the actual oracles satisfies
`MeshIntegralOutcome`: the certificate
`‖∑_r ∫_{t_r}^{t_{r+1}} U(T, v) b_r(v) dv - ∑ ω_i U(T, v_i) b_i‖ ≤ ζ B` replaces the one on the
propagated source sum (`mesh_duhamel`). -/
theorem mesh_solver_integral (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 < T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hρ : 0 < etaH + radius (cq * gbar) ε * etaD)
    (hClock : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ N)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (N : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    MeshIntegralOutcome D t N etaH etaD T gbar cq ε v ω Pw J seed := by
  obtain ⟨d, tf, hch, hU, hC⟩ := mesh_solver D hM t hN etaH etaD T gbar cq ε v ω hH hDiss hT hg
    hcq hε hεOne hmesh hρ hClock hCayley hv hrH hcH hrD hcD hPSD Pw hPw J hJ seed hSeed
  refine ⟨d, tf, hch, hU, fun x G b sol bv U ζ hG hGc hbc hsol hUm hW hL0 hL hMass hInt hTarget
    hB hBudget => ?_⟩
  have hD := mesh_duhamel hmesh hUm hG hGc b hbc sol hsol
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t := by
    rw [← hD]
    exact hInt
  exact hC x G b sol bv U ζ hG (fun r => (hGc r).intervalIntegrable_of_Icc
    (hmesh.mono (Nat.le_succ r))) hsol hUm hW hL0 hL hMass hCertP hTarget hB hBudget

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh, with approximate
preparations, for every `T ≥ 0`, with the certificate on the propagated vector integral.** Under
the hypotheses of `mesh_approx_solver_nonneg`, for continuous generator and forcing pieces,
`MeshApproxIntegralOutcome` holds with the budget of `mesh_approx_solver_nonneg`. -/
theorem mesh_approx_solver_nonneg_integral (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (t : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ)
    (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hmesh : IsMesh t M T)
    (hClock : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ N)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (N : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    MeshApproxIntegralOutcome D t N etaH etaD T gbar cq ε v ω Pw J seed
      (if T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0 then 0 else
        1274019840 * ratio (cq * gbar) * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))) := by
  obtain ⟨d, tf, hch, hU, hC⟩ := mesh_approx_solver_nonneg D hM t hN etaH etaD T gbar cq ε v ω
    hH hDiss hT hg hcq hε hεOne hmesh hClock hCayley hv hrH hcH hrD hcD hPSD Pw hPw J hJ seed
    hSeed
  refine ⟨d, tf, hch, hU, fun x P L δ G b sol bv U ζ hP hL hδ hPd hLd hδ1 hδε hG hGc hbc hsol hUm
    hW hL0 hL' hMass hInt hTarget hB hBudget => ?_⟩
  have hD := mesh_duhamel hmesh hUm hG hGc b hbc sol hsol
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t := by
    rw [← hD]
    exact hInt
  exact hC x P L δ G b sol bv U ζ hP hL hδ hPd hLd hδ1 hδε hG
    (fun r => (hGc r).intervalIntegrable_of_Icc (hmesh.mono (Nat.le_succ r))) hsol hUm hW hL0 hL'
    hMass hCertP hTarget hB hBudget

end

end SparseHamiltonian.GeneralSourceExtensions.Mesh
