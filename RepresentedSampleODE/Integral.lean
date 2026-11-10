import RepresentedSampleODE.Approx
import GeneralSourceExtensions.Mesh.Integral

/-!
# Represented samples of any sign, with the certificate on the propagated vector integral

As `GeneralSourceExtensions.Mesh.mesh_solver_integral` and
`GeneralSourceExtensions.Mesh.mesh_approx_solver_nonneg_integral`, with `RobustBudget` in place of
the positivity of the represented samples:

* `robust_solver_integral`, `robust_approx_solver_nonneg_integral`;
* negativity bounds from the true path: for accretive continuous pieces the averages
  `κ_r = (1/Δ_r) ∫_{t_r}^{t_{r+1}} ‖Herm(G_r(u) - G̃_r)‖ du` (`pathNegativity`) are negativity
  bounds of the represented samples with negativity mass the *dissipative sample error*
  `ΔD = ∑_r ∫ ‖Herm(G_r - G̃_r)‖ ≤ ΔG` (`dissipativeError`);
* `robust_approx_solver_nonneg_path`: the combined endpoint with the budgets
  `ζ + c_q (ΔG + 2 ΔD + 2 ΔR) ≤ ε / (2000 ḡ)` and `6 R (ΔD + ΔR) ≤ ν`, in which only the true
  path is dissipative.
-/

set_option autoImplicit false

namespace SparseHamiltonian.RepresentedSampleODE

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions SparseHamiltonian.GeneralSourceExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE ratio accuracy radius precision
  lipschitz Index lchsCoefficients)
open SparseHamiltonian.GeneralSourceODE (SourceCall sources phases phases_norm)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshScale sampleError refinementError
  IsMeshPropagator mesh_duhamel)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- `RobustOutcome` for continuous pieces with the certificate on the propagated vector
integral. -/
def RobustIntegralOutcome (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
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
      RobustBudget D x t G T N cq gbar ε ζ →
      GeneralSourceODE.Oracles.ActualCertificate
        (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

/-- `RobustApproxBudgetOutcome` for continuous pieces with the certificate on the propagated vector
integral. -/
def RobustApproxIntegralOutcome (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
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
      RobustBudget D x t G T N cq gbar ε ζ →
      ApproxCertificate (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε ∧
      ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
        GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤ Q

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh, with the certificate on
the propagated vector integral, represented samples of any sign.** Under the hypotheses of
`robust_mesh_solver`, for continuous generator
and forcing pieces, the public trial family over the actual oracles satisfies
`RobustIntegralOutcome`: the certificate
`‖∑_r ∫_{t_r}^{t_{r+1}} U(T, v) b_r(v) dv - ∑ ω_i U(T, v_i) b_i‖ ≤ ζ B` replaces the one on the
propagated source sum (`mesh_duhamel`). -/
theorem robust_solver_integral (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
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
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    RobustIntegralOutcome D t N etaH etaD T gbar cq ε v ω Pw J seed := by
  obtain ⟨d, tf, hch, hU, hC⟩ := robust_mesh_solver D hM t hN etaH etaD T gbar cq ε v ω hH hDiss hT
    hg hcq hε hεOne hmesh hρ hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed hSeed
  refine ⟨d, tf, hch, hU, fun x G b sol bv U ζ hG hGc hbc hsol hUm hW hL0 hL hMass hInt hTarget
    hB hBudget => ?_⟩
  have hD := mesh_duhamel hmesh hUm hG hGc b hbc sol hsol
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t := by
    rw [← hD]
    exact hInt
  exact hC x G b sol bv U ζ hG (fun r => (hGc r).intervalIntegrable_of_Icc
    (hmesh.mono (Nat.le_succ r))) hUm hW hL0 hL hMass hCertP hTarget hB hBudget

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh, with approximate
preparations, for every `T ≥ 0`, with the certificate on the propagated vector integral,
represented samples of any sign.** Under
the hypotheses of `robust_approx_solver_nonneg`, for continuous generator and forcing pieces,
`RobustApproxIntegralOutcome` holds with the budget of `robust_approx_solver_nonneg`. -/
theorem robust_approx_solver_nonneg_integral (D : Data (X × Fin M) n Z s) (hM : 0 < M)
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
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    RobustApproxIntegralOutcome D t N etaH etaD T gbar cq ε v ω Pw J seed
      (if T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0 then 0 else
        1274019840 * ratio (cq * gbar) * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))) := by
  obtain ⟨d, tf, hch, hU, hC⟩ := robust_approx_solver_nonneg D hM t hN etaH etaD T gbar cq ε v ω
    hH hDiss hT hg hcq hε hεOne hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed
    hSeed
  refine ⟨d, tf, hch, hU, fun x P L δ G b sol bv U ζ hP hL hδ hPd hLd hδ1 hδε hG hGc hbc hsol hUm
    hW hL0 hL' hMass hInt hTarget hB hBudget => ?_⟩
  have hD := mesh_duhamel hmesh hUm hG hGc b hbc sol hsol
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t := by
    rw [← hD]
    exact hInt
  exact hC x P L δ G b sol bv U ζ hP hL hδ hPd hLd hδ1 hδε hG
    (fun r => (hGc r).intervalIntegrable_of_Icc (hmesh.mono (Nat.le_succ r))) hUm hW hL0 hL'
    hMass hCertP hTarget hB hBudget

/-! ### Negativity bounds from the true path -/

omit [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The real part of a quadratic form is at most the norm of the Hermitian part. -/
theorem re_inner_le_dissipative (A : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (w : EuclideanSpace ℂ n) :
    (inner ℂ w (A w)).re ≤ ‖ODEHermitianReduction.dissipativePart A‖ * ‖w‖ ^ 2 := by
  rw [← ODEHermitianReduction.real_inner_dissipativePart]
  calc (inner ℂ w (ODEHermitianReduction.dissipativePart A w)).re
      ≤ ‖inner ℂ w (ODEHermitianReduction.dissipativePart A w)‖ := Complex.re_le_norm _
    _ ≤ ‖w‖ * ‖ODEHermitianReduction.dissipativePart A w‖ := norm_inner_le_norm _ _
    _ ≤ ‖w‖ * (‖ODEHermitianReduction.dissipativePart A‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left (le_opNorm _ _) (norm_nonneg _)
    _ = ‖ODEHermitianReduction.dissipativePart A‖ * ‖w‖ ^ 2 := by ring

/-- The dissipative sample error `ΔD = ∑_r ∫_{t_r}^{t_{r+1}} ‖Herm(G_r(u) - G̃_r)‖ du`. -/
def dissipativeError (D : Data (X × Fin M) n Z s) (x : X) (t : ℕ → ℝ)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) : ℝ :=
  ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), ‖ODEHermitianReduction.dissipativePart
    (G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r)))‖

/-- The negativity bound of interval `r` from the true path: the average of
`‖Herm(G_r(u) - G̃_r)‖` over the interval (the norm of the sample on an empty interval). -/
def pathNegativity (D : Data (X × Fin M) n Z s) (x : X) (t : ℕ → ℝ)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (r : Fin M) : ℝ :=
  if 0 < t ((r : ℕ) + 1) - t r then
    (∫ u in t r..t ((r : ℕ) + 1), ‖ODEHermitianReduction.dissipativePart
      (G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r)))‖) /
        (t ((r : ℕ) + 1) - t r)
  else ‖SparseStateOverlap.matrixOperator (D.matrix (x, r))‖

omit [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem dissipative_continuousOn {G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n}
    {S : Set ℝ} (hG : ContinuousOn G S) (C : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    ContinuousOn (fun u => ‖ODEHermitianReduction.dissipativePart (G u - C)‖) S := by
  have h1 : ContinuousOn (fun u => G u - C) S := hG.sub continuousOn_const
  have h2 : ContinuousOn (fun u => (G u - C)†) S :=
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := EuclideanSpace ℂ n)
      (F := EuclideanSpace ℂ n)).continuous.comp_continuousOn h1
  have h3 : ContinuousOn (fun u => ODEHermitianReduction.dissipativePart (G u - C)) S := by
    simp only [ODEHermitianReduction.dissipativePart, HermitianDilation.hermitianPart]
    exact (h1.add h2).const_smul ((2 : ℂ)⁻¹)
  exact h3.norm

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem dissipativeError_nonneg (D : Data (X × Fin M) n Z s) (x : X) {t : ℕ → ℝ} {T : ℝ}
    (hmesh : IsMesh t M T) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    0 ≤ dissipativeError D x t G :=
  Finset.sum_nonneg fun r _ =>
    intervalIntegral.integral_nonneg (hmesh.mono (Nat.le_succ r)) fun _ _ => norm_nonneg _

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The dissipative sample error is at most the sample error. -/
theorem dissipativeError_le_sampleError (D : Data (X × Fin M) n Z s) (x : X) {t : ℕ → ℝ}
    {T : ℝ} (hmesh : IsMesh t M T)
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hGc : ∀ r : Fin M, ContinuousOn (G r) (Icc (t r) (t ((r : ℕ) + 1)))) :
    dissipativeError D x t G ≤ sampleError D x t G := by
  refine Finset.sum_le_sum fun r _ => ?_
  have hab := hmesh.mono (Nat.le_succ r)
  have h1 := (dissipative_continuousOn (hGc r)
    (SparseStateOverlap.matrixOperator (D.matrix (x, r)))).intervalIntegrable_of_Icc
      (μ := MeasureTheory.volume) hab
  have h2 : IntervalIntegrable
      (fun u => ‖G r u - SparseStateOverlap.matrixOperator (D.matrix (x, r))‖)
      MeasureTheory.volume (t r) (t ((r : ℕ) + 1)) :=
    (((hGc r).sub continuousOn_const).norm).intervalIntegrable_of_Icc hab
  exact intervalIntegral.integral_mono_on hab h1 h2
    (fun u _ => ODEHermitianReduction.norm_dissipativePart_le _)

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
theorem pathNegativity_nonneg (D : Data (X × Fin M) n Z s) (x : X) {t : ℕ → ℝ} {T : ℝ}
    (hmesh : IsMesh t M T) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (r : Fin M) : 0 ≤ pathNegativity D x t G r := by
  unfold pathNegativity
  split_ifs with h
  · exact div_nonneg (intervalIntegral.integral_nonneg (hmesh.mono (Nat.le_succ r))
      fun _ _ => norm_nonneg _) h.le
  · exact norm_nonneg _

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **The path averages are negativity bounds.** For accretive continuous pieces the represented
samples satisfy `Re ⟨w, G̃_r w⟩ ≥ -κ_r ‖w‖²` with `κ_r = pathNegativity`. -/
theorem pathNegativity_bound (D : Data (X × Fin M) n Z s) (x : X) {t : ℕ → ℝ}
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGc : ∀ r : Fin M, ContinuousOn (G r) (Icc (t r) (t ((r : ℕ) + 1))))
    (r : Fin M) (w : EuclideanSpace ℂ n) :
    -pathNegativity D x t G r * ‖w‖ ^ 2 ≤
      (inner ℂ w (SparseStateOverlap.matrixOperator (D.matrix (x, r)) w)).re := by
  unfold pathNegativity
  set A := SparseStateOverlap.matrixOperator (D.matrix (x, r)) with hA
  split_ifs with hpos
  · set a := t r
    set b := t ((r : ℕ) + 1)
    have hab : a ≤ b := by linarith
    set f : ℝ → ℝ := fun u => ‖ODEHermitianReduction.dissipativePart (G r u - A)‖ with hf
    have hfint : IntervalIntegrable f MeasureTheory.volume a b :=
      (dissipative_continuousOn (hGc r) A).intervalIntegrable_of_Icc hab
    set c : ℝ := (inner ℂ w (A w)).re with hc
    have key : ∀ u ∈ Icc a b, -(f u * ‖w‖ ^ 2) ≤ c := by
      intro u hu
      have h0 := hG r u hu w
      have h1 := re_inner_le_dissipative (G r u - A) w
      have e : (inner ℂ w ((G r u - A) w)).re = (inner ℂ w (G r u w)).re - c := by
        rw [hc, sub_apply, inner_sub_right, Complex.sub_re]
      rw [e] at h1
      simp only [hf]
      linarith
    have hint : ∫ u in a..b, -(f u * ‖w‖ ^ 2) ≤ ∫ u in a..b, c :=
      intervalIntegral.integral_mono_on hab ((hfint.mul_const (‖w‖ ^ 2)).neg)
        intervalIntegrable_const key
    have e1 : ∫ u in a..b, -(f u * ‖w‖ ^ 2) = -((∫ u in a..b, f u) * ‖w‖ ^ 2) := by
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_mul_const]
    have e2 : ∫ u in a..b, c = (b - a) * c := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
    rw [e1, e2] at hint
    have hba : 0 < b - a := hpos
    set I : ℝ := ∫ u in a..b, f u with hI
    have e3 : -(I / (b - a)) * ‖w‖ ^ 2 = -(I * ‖w‖ ^ 2) / (b - a) := by ring
    rw [e3, div_le_iff₀ hba]
    linarith [mul_comm c (b - a)]
  · have h := re_inner_le_dissipative (-A) w
    rw [neg_apply, inner_neg_right, Complex.neg_re] at h
    have hd : ‖ODEHermitianReduction.dissipativePart (-A)‖ ≤ ‖A‖ :=
      (ODEHermitianReduction.norm_dissipativePart_le _).trans (norm_neg A).le
    have hm := mul_le_mul_of_nonneg_right hd (sq_nonneg ‖w‖)
    linarith

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The negativity mass of the path bounds is the dissipative sample error. -/
theorem negativity_pathNegativity (D : Data (X × Fin M) n Z s) (x : X) {t : ℕ → ℝ} {T : ℝ}
    (hmesh : IsMesh t M T) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    negativity t (pathNegativity D x t G) = dissipativeError D x t G := by
  unfold negativity dissipativeError
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold pathNegativity
  split_ifs with hpos
  · field_simp
  · have h0 : t ((r : ℕ) + 1) - t r = 0 := le_antisymm (not_lt.mp hpos) (hmesh.length_nonneg r)
    have h1 : t ((r : ℕ) + 1) = t r := by linarith
    rw [h0, zero_mul, h1, intervalIntegral.integral_same]

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- **`RobustBudget` from the true path**: for accretive continuous pieces the budgets
`ζ + c_q (ΔG + 2 ΔD + 2 ΔR) ≤ ε / (2000 ḡ)` and `6 R (ΔD + ΔR) ≤ ν` give `RobustBudget` with the
path negativity bounds. -/
theorem robustBudget_of_path (D : Data (X × Fin M) n Z s) (x : X) {t : ℕ → ℝ} {T : ℝ}
    (hmesh : IsMesh t M T) {N : ℕ}
    (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hG : ∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u))
    (hGc : ∀ r : Fin M, ContinuousOn (G r) (Icc (t r) (t ((r : ℕ) + 1))))
    {cq gbar ε ζ : ℝ}
    (h1 : ζ + cq * (sampleError D x t G + 2 * dissipativeError D x t G +
      2 * refinementError D t T N) ≤ ε / (2000 * gbar))
    (h2 : 6 * radius (cq * gbar) ε * (dissipativeError D x t G + refinementError D t T N) ≤
      precision (cq * gbar) ε) :
    RobustBudget D x t G T N cq gbar ε ζ := by
  refine ⟨pathNegativity D x t G, pathNegativity_nonneg D x hmesh G,
    pathNegativity_bound D x G hG hGc, ?_, ?_⟩
  · rw [negativity_pathNegativity D x hmesh G]
    exact h1
  · rw [negativity_pathNegativity D x hmesh G]
    exact h2

/-- `RobustApproxIntegralOutcome` with the budgets of the true path: the target budget
`ζ + c_q (ΔG + 2 ΔD + 2 ΔR) ≤ ε / (2000 ḡ)` and the branch budget `6 R (ΔD + ΔR) ≤ ν`, with the
dissipative sample error `ΔD` (`dissipativeError`). -/
def PathApproxIntegralOutcome (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
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
      ζ + cq * (sampleError D x t G + 2 * dissipativeError D x t G +
        2 * refinementError D t T N) ≤ ε / (2000 * gbar) →
      6 * radius (cq * gbar) ε * (dissipativeError D x t G + refinementError D t T N) ≤
        precision (cq * gbar) ε →
      ApproxCertificate (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε ∧
      ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
        GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤ Q

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh, approximate preparations,
every `T ≥ 0`, the certificate on the propagated vector integral, and represented samples of any
sign, with the budgets of the true path.** Under the hypotheses of
`robust_approx_solver_nonneg_integral`, `PathApproxIntegralOutcome` holds: the negativity bounds of
the represented samples are the path averages `pathNegativity`, whose negativity mass is the
dissipative sample error `ΔD ≤ ΔG`. Only the true path is dissipative. -/
theorem robust_approx_solver_nonneg_path (D : Data (X × Fin M) n Z s) (hM : 0 < M)
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
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    PathApproxIntegralOutcome D t N etaH etaD T gbar cq ε v ω Pw J seed
      (if T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0 then 0 else
        1274019840 * ratio (cq * gbar) * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))) := by
  obtain ⟨d, tf, hch, hU, hC⟩ := robust_approx_solver_nonneg_integral D hM t hN etaH etaD T gbar cq
    ε v ω hH hDiss hT hg hcq hε hεOne hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed
    hSeed
  refine ⟨d, tf, hch, hU, fun x P L δ G b sol bv U ζ hP hL hδ hPd hLd hδ1 hδε hG hGc hbc hsol hUm
    hW hL0 hL' hMass hInt hTarget hB hB1 hB2 => ?_⟩
  exact hC x P L δ G b sol bv U ζ hP hL hδ hPd hLd hδ1 hδε hG hGc hbc hsol hUm hW hL0 hL' hMass
    hInt hTarget hB (robustBudget_of_path D x hmesh G hG hGc hB1 hB2)

end

end SparseHamiltonian.RepresentedSampleODE
