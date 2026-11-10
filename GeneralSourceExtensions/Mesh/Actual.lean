import GeneralSourceExtensions.Mesh.Zero

/-!
# The general source interface on a mesh, over the actual oracles

The counted two-interface trial families of `Mesh.mesh_propagated_solver` and `Mesh.mesh_zero_core`
run on the actual oracles `P_w`, `U_load`, `P_w†` of the `N`-slot workspace
(`MeshOracles.actualTrials`): each preparation call is one `P_w` call, one `U_load` call and the
public phases, each unpreparation call one `P_w†` call. The released four-attempt protocol keeps
its guarantees (`GeneralSourceODE.Oracles.actual_certificate`).

* `lchsCoefficients_mass`: the public LCHS coefficients have absolute mass three for every
  `T ≥ 0`;
* `mesh_actual_build`: the transfer, with the per-trial matrix costs of the counted family;
* `mesh_solver`: Theorem `ode:thm:time` with the general source interface on a mesh, over the
  actual oracles (`MeshOutcome`);
* `mesh_solver_nonneg`: the same for every `T ≥ 0` and without `ρ > 0`, with no matrix query in
  the zero cases (`MeshBudgetOutcome`).
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

omit [Fintype Z] [AddCommGroup Z] [DecidableEq Z] in
/-- The public LCHS coefficients have absolute mass three for every `T ≥ 0`. -/
theorem lchsCoefficients_mass (D : Data (X × Fin M) n Z s) {T : ℝ} (hT : 0 ≤ T) (g ε : ℝ)
    (hg : 1 ≤ ratio g) (hε : 0 < ε) (hεOne : ε ≤ 1) :
    ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε) = 3 := by
  have hL : 0 ≤ lipschitz D T :=
    mul_nonneg hT (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
  have hε' : 0 < accuracy ε := by unfold accuracy; linarith
  have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
  obtain ⟨-, -, hMass, -⟩ := TimeDependentODE.GaussianLCHS.table_certificate
    (V := EuclideanSpace ℂ n)
    (fun (_ : Unit) (_ : ℂ) => (0 : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n))
    (fun _ _ => analyticAt_const) (fun _ _ _ => by simp) (lipschitz D T) hL
    (fun _ k l => by simp only [sub_self, norm_zero]; exact mul_nonneg hL (abs_nonneg _))
    (ratio g) (accuracy ε) hg hε' hε'One
  exact ODECoefficientPadding.coefficientMass_eq _ 3 hMass

/-- **One public trial family on a mesh over the actual oracles.** For every valid instance, four
fresh trials have the released guarantees (`GeneralSourceODE.Oracles.ActualCertificate`). -/
def MeshOutcome (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
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
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      (∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep (Pw x) (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → J x (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      ζ + cq * (sampleError D x t G + refinementError D t T N) ≤ ε / (2000 * gbar) →
      GeneralSourceODE.Oracles.ActualCertificate
        (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

/-- `MeshOutcome` in which the four-attempt protocol makes at most `Q` matrix queries in every
history. -/
def MeshBudgetOutcome (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Q : ℝ) : Prop :=
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
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      (∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep (Pw x) (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → J x (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      ζ + cq * (sampleError D x t G + refinementError D t T N) ≤ ε / (2000 * gbar) →
      GeneralSourceODE.Oracles.ActualCertificate
        (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε ∧
      ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
        GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤ Q

set_option maxHeartbeats 8000000 in
/-- **The transfer to the actual oracles on a mesh.** From a counted two-interface family with
the released complete certificate for every valid instance, the substituted family over the
actual oracles has the same per-trial matrix costs and satisfies the released guarantees. -/
theorem mesh_actual_build (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a)) (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) (d : ℕ)
    (E : GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      MeshNative.MatrixSpace (Index D T (cq * gbar) ε) n Z m M N d)
    (hE : E† ∘L E = 1)
    (q : ℕ → MultiOracleCircuit.Program
      (MeshNative.physicalOracle (ι := Index D T (cq * gbar) ε) D m N d Pw J (phases ω)))
    (hCert : ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      (∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep (Pw x) (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → J x (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      ζ + cq * (sampleError D x t G + refinementError D t T N) ≤ ε / (2000 * gbar) →
      ODECompleteTrial.Certificate q
        (ODEGroverAverage.chosenIterations (ratio (cq * gbar)))
        (MeshNative.input D hM (Sum.inr false) m N d
          (ODECompiledSource.seed E
            (GeneralSourceODE.Compiled.seedCoefficients
              (lchsCoefficients D T (cq * gbar) ε)) seed))
        (MeshNative.input D hM (Sum.inr false) m N d ∘L
          ODECompiledSource.output E
            (GeneralSourceODE.Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)))
        x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε) :
    ∃ tf : ODERepeatProtocol.TrialFamily
        (MeshOracles.actualOracle (ι := Index D T (cq * gbar) ε) D m N d Pw J)
        (EuclideanSpace ℂ n),
      tf.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
      (∀ j y, IsUnitary ((tf.circuit j).eval y)) ∧
      (∀ j : Fin tf.choices, (tf.circuit j).cost GeneralSourceODE.Oracles.matrixCalls =
        (q j.val).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) ∧
      ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
        (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
        (bv : Fin m → EuclideanSpace ℂ n)
        (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
        (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
        (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
        (∀ r : Fin M, SolvesODE (G r) (b r) sol (t r) (t ((r : ℕ) + 1))) →
        IsMeshPropagator G t T U →
        GeneralSourceODE.Compiled.WeightPrep (Pw x) (sources (sol 0) bv ω) →
        (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
        (∀ i, ω i ≠ 0 → bv i ≠ 0 → J x (some i) seed =
          ODEStateNormalization.unitDirection (bv i)) →
        ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
        ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
        sol T ≠ 0 →
        meshScale sol b t ≤ gbar * ‖sol T‖ →
        ζ + cq * (sampleError D x t G + refinementError D t T N) ≤ ε / (2000 * gbar) →
        GeneralSourceODE.Oracles.ActualCertificate
          (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
          (ratio (cq * gbar)) ε := by
  have hg1 : 1 ≤ ratio (cq * gbar) := by
    unfold ratio
    nlinarith
  obtain ⟨hMpos, -, -⟩ := ODEGroverAverage.chosenIterations_bounds (ratio (cq * gbar)) hg1
  have hcpos : 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D T (cq * gbar) ε) := by
    rw [lchsCoefficients_mass D hT (cq * gbar) ε hg1 hε hεOne]
    norm_num
  have hψ := MeshNative.seed_unit D hM (Sum.inr false) m N d E hE
    (lchsCoefficients D T (cq * gbar) ε) hcpos seed hSeed
  have hF := MeshNative.output_isometry D hM (Sum.inr false) m N d E hE
    (lchsCoefficients D T (cq * gbar) ε) hcpos
  let q' := MeshOracles.actualTrials D m N d Pw J (phases ω) (phases_norm ω) q
  have hEval : ∀ j x, (q' j).eval x = (q j).eval x := fun j x =>
    MultiOracleCircuit.Program.eval_substitute (q j) _
      (MeshOracles.implementation_eval D m N d Pw J (phases ω) (phases_norm ω)) x
  have hActual := MeshOracles.actualOracle_unitary (ι := Index D T (cq * gbar) ε) D m N d hPw hJ
  have hCost : ∀ (w : Query ⊕ SourceCall → ℕ) (j : ℕ),
      (q' j).cost w = (q j).cost (fun l =>
        (MeshOracles.implementation D m N d Pw J (phases ω) (phases_norm ω) l).cost w) :=
    fun w j => MultiOracleCircuit.Program.cost_substitute (q j) _ w
  have hMatrix : ∀ j, (q' j).cost GeneralSourceODE.Oracles.matrixCalls =
      (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := fun j => by
    rw [hCost]
    exact congrArg (q j).cost (funext (MeshOracles.implementation_matrix D m N d Pw J _ _))
  refine ⟨ODERepeatProtocol.ofCircuits q'
    (ODEGroverAverage.chosenIterations (ratio (cq * gbar))) hMpos _ hψ _ hF, rfl,
    fun j y => (q' j.val).eval_unitary hActual y, fun j => hMatrix j.val, ?_⟩
  intro x G b sol bv U ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  have hC := hCert x G b sol bv U ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact GeneralSourceODE.Oracles.actual_certificate hC q' hMpos hψ hF (fun j => hEval j x)
    hMatrix
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (MeshOracles.implementation_weight D m N d Pw J _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (MeshOracles.implementation_load D m N d Pw J _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (MeshOracles.implementation_unweight D m N d Pw J _ _)))
    (fun j => by
      rw [hCost, funext (MeshOracles.implementation_source D m N d Pw J _ _),
        GeneralSourceODE.Oracles.cost_add, NativeHermitianDilation.cost_scale])

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh, on the actual
oracles.** Under the hypotheses of `mesh_propagated_solver`, one public family of trial circuits
over the coherent sampled-time matrix oracle on `N` slots and the supplied `P_w`, `U_load` and
`P_w†` gives, by four fresh trials, the normalized solution with conditional trace distance at
most `ε` and success probability at least `2/3`, with at most
`1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)` matrix queries and `40 g'` calls of each of `P_w`, `U_load`
and `P_w†` in every history, `g' = 2 c_q ḡ`. -/
theorem mesh_solver (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
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
    MeshOutcome D t N etaH etaD T gbar cq ε v ω Pw J seed := by
  obtain ⟨d, E, hE, q, _hU, hCert⟩ := mesh_propagated_solver D hM t hN etaH etaD T gbar cq ε v ω
    hH hDiss hT hg hcq hε hεOne hmesh hρ hClock hCayley hv hrH hcH hrD hcD hPSD Pw hPw J hJ
    seed hSeed
  obtain ⟨tf, hch, hU, -, hC⟩ := mesh_actual_build D hM t N etaH etaD T gbar cq ε v ω hT.le hg
    hcq hε hεOne Pw hPw J hJ seed hSeed d E hE q hCert
  exact ⟨d, tf, hch, hU, hC⟩

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh, for every `T ≥ 0`.**
Under the hypotheses of `mesh_solver` with `0 ≤ T` in place of `0 < T` and without
`ρ = η_H + R η_D > 0`, `MeshBudgetOutcome` holds with
`Q = if T = 0 ∨ ρ = 0 then 0 else 1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)`. -/
theorem mesh_solver_nonneg (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
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
    MeshBudgetOutcome D t N etaH etaD T gbar cq ε v ω Pw J seed
      (if T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0 then 0 else
        1274019840 * ratio (cq * gbar) * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))) := by
  by_cases hZero : T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0
  · rw [if_pos hZero]
    obtain ⟨d, E, hE, q, _hU, hCost, hCert⟩ := mesh_zero_core D hM t hN etaH etaD T gbar cq ε v
      ω hH hDiss hT hZero hg hcq hε hεOne hmesh hv hrH hrD hPSD Pw hPw J hJ seed hSeed
    obtain ⟨tf, hch, hU, hcost, hC⟩ := mesh_actual_build D hM t N etaH etaD T gbar cq ε v ω hT
      hg hcq hε hεOne Pw hPw J hJ seed hSeed d E hE q hCert
    have h := ODERepeatProtocol.Protocol.repeat_worstCost_le tf 4
      GeneralSourceODE.Oracles.matrixCalls 0 (fun j => by rw [hcost j]; exact hCost j.val)
    rw [mul_zero] at h
    exact ⟨d, tf, hch, hU, fun x G b sol bv U ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
      ⟨hC x G b sol bv U ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12, h⟩⟩
  · rw [if_neg hZero]
    have hg' : 1 ≤ ratio (cq * gbar) := by unfold ratio; nlinarith
    have hε' : 0 < accuracy ε := by unfold accuracy; linarith
    have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
    have hR : 0 ≤ radius (cq * gbar) ε :=
      ImprovedODEQueryBudget.radius_nonneg _ _ hg' hε' hε'One
    have hTpos : 0 < T := lt_of_le_of_ne hT (fun h => hZero (Or.inl h.symm))
    have hρ : 0 < etaH + radius (cq * gbar) ε * etaD :=
      lt_of_le_of_ne (add_nonneg hH (mul_nonneg hR hDiss)) (fun h => hZero (Or.inr h.symm))
    obtain ⟨d, tf, hch, hU, hC⟩ := mesh_solver D hM t hN etaH etaD T gbar cq ε v ω hH hDiss
      hTpos hg hcq hε hεOne hmesh hρ hClock hCayley hv hrH hcH hrD hcD hPSD Pw hPw J hJ seed
      hSeed
    exact ⟨d, tf, hch, hU, fun x G b sol bv U ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
      let hc := hC x G b sol bv U ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      ⟨hc, hc.matrix_queries⟩⟩

end

end SparseHamiltonian.GeneralSourceExtensions.Mesh
