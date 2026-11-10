import CleanWorkODE.Oracles
import RepresentedSampleODE.Regular

/-!
# Theorem `ode:thm:time` with preparations on temporary work registers

The approximate-preparation endpoints of `RepresentedSampleODE` ask the supplied `P_w` and
`U_load` to be within `δ` of exact preparations in the full operator norm. The manuscript allows
temporary work registers and bounds only the clean-input errors (Section `ode:sec:time`, the
paragraph after eq. `ode:eq:source-interface-preparation`, with the temporary-work convention of
eq. `access:eq:full-output`). Here the supplied operations act on their
registers and a temporary work register with basis `W` and clean state `w₀`:

* `WorkApproxBudgetOutcome`, `work_approx_build`, `work_approx_solver_nonneg`: as
  `RepresentedSampleODE.robust_approx_solver_nonneg`, for a supplied `P_w` on the label and work
  registers and a supplied `U_load` on the label, data and work registers within `δ` of `P` and
  `∑_a |a⟩⟨a| ⊗ L(a)` on a clean work register (`CleanErr`); the protocol runs the released
  trial family with every fixed gate acting as the identity on the work register, and heralds on
  the output flag and a clean work register;
* `WorkRegularOutcome`, `work_approx_solver_nonneg_regular`: the same for integrable generator
  pieces, mild solutions and the budgets of the true path, as
  `RepresentedSampleODE.robust_approx_solver_nonneg_regular`.

The public trial family is fixed before the instance, the counts are the released ones, and the
budgets `30 g' δ ≤ 1/400` and `30 g' δ ≤ ε/20` (`g' = 2 c_q ḡ`) are unchanged.
-/

set_option autoImplicit false

namespace SparseHamiltonian.CleanWorkODE

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions SparseHamiltonian.GeneralSourceExtensions
open SparseHamiltonian.RepresentedSampleODE
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE ratio accuracy radius precision
  lipschitz Index lchsCoefficients)
open SparseHamiltonian.GeneralSourceODE (SourceCall sources phases phases_norm)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshScale sampleError refinementError
  IsMeshPropagator lchsCoefficients_mass)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {X n Z W : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] [Fintype W] [DecidableEq W] {s M : ℕ}

/-- **The general source interface on a mesh with preparations on temporary work registers and a
matrix budget, represented samples of any sign.** One public trial family over the actual oracles
with a work register, fixed before the instance; for every instance with exact unitary
preparations `P`, `L` such that the supplied `P_w(x)` and `U_load(x)` are within `δ` of `P` and
`∑_a |a⟩⟨a| ⊗ L(a)` on a clean work register, `30 g' δ ≤ 1/400` and `30 g' δ ≤ ε / 20`
(`g' = 2 c_q ḡ`), and the hypotheses of `RobustOutcome` for `P`, `L`, four fresh trials satisfy
`ApproxCertificate` and make at most `Q` matrix queries in every history. -/
def WorkApproxBudgetOutcome (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ) (w₀ : W)
    (Pw : X → LabelW m W →L[ℂ] LabelW m W) (J : X → LoadW m n W →L[ℂ] LoadW m n W)
    (seed : EuclideanSpace ℂ n) (Q : ℝ) : Prop :=
  ∃ (d : ℕ) (tf : ODERepeatProtocol.TrialFamily
      (actualOracleW (ι := Index D T (cq * gbar) ε) D m N d Pw J) (EuclideanSpace ℂ n)),
    tf.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
    (∀ j y, IsUnitary ((tf.circuit j).eval y)) ∧
    ∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
      (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
      (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
      CleanErr (cleanPi (V := ℂ) w₀) (Pw x) P δ →
      CleanErr (cleanPi (V := ℂ) w₀) (J x) (ctrlL L) δ →
      30 * ratio (cq * gbar) * δ ≤ 1 / 400 → 30 * ratio (cq * gbar) * δ ≤ ε / 20 →
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep P (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → L (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
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
/-- **The construction with a work register.** From a two-interface family for the exact
preparation instances `Inst X n m` (the sparse data read through `Inst.input`) with the released
complete certificate, the family run with every fixed gate lifted to the work register on the
actual oracles with a work register, seeded and heralded on a clean work register, has the
per-trial matrix costs of the two-interface family and satisfies `ApproxCertificate` for every
instance whose supplied preparations are within `δ` of exact ones on a clean work register. -/
theorem work_approx_build (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq) (hε : 0 < ε) (hεOne : ε ≤ 1) (w₀ : W)
    (Pw : X → LabelW m W →L[ℂ] LabelW m W) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → LoadW m n W →L[ℂ] LoadW m n W) (hJ : ∀ x, IsUnitary (J x))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) (d : ℕ)
    (E : GeneralSourceODE.Native.SourceSpace
        (Index (pullback D (Inst.input (X := X) (n := n) (m := m))) T (cq * gbar) ε) n m →L[ℂ]
      MeshNative.MatrixSpace
        (Index (pullback D (Inst.input (X := X) (n := n) (m := m))) T (cq * gbar) ε) n Z m M N d)
    (hE : E† ∘L E = 1)
    (q : ℕ → MultiOracleCircuit.Program
      (MeshNative.physicalOracle
        (ι := Index (pullback D (Inst.input (X := X) (n := n) (m := m))) T (cq * gbar) ε)
        (pullback D (Inst.input (X := X) (n := n) (m := m))) m N d Inst.weight Inst.loader
        (phases ω)))
    (hCert : ∀ (p : Inst X n m) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep (Inst.weight p) (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → Inst.loader p none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → Inst.loader p (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      RobustBudget (pullback D (Inst.input (X := X) (n := n) (m := m))) p t G T N cq gbar ε ζ →
      ODECompleteTrial.Certificate q
        (ODEGroverAverage.chosenIterations (ratio (cq * gbar)))
        (MeshNative.input (pullback D (Inst.input (X := X) (n := n) (m := m))) hM (Sum.inr false)
          m N d (ODECompiledSource.seed E
            (GeneralSourceODE.Compiled.seedCoefficients
              (lchsCoefficients (pullback D (Inst.input (X := X) (n := n) (m := m))) T
                (cq * gbar) ε)) seed))
        (MeshNative.input (pullback D (Inst.input (X := X) (n := n) (m := m))) hM (Sum.inr false)
            m N d ∘L
          ODECompiledSource.output E
            (GeneralSourceODE.Compiled.seedCoefficients
              (lchsCoefficients (pullback D (Inst.input (X := X) (n := n) (m := m))) T
                (cq * gbar) ε)))
        p (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε) :
    ∃ tf : ODERepeatProtocol.TrialFamily
        (actualOracleW (ι := Index D T (cq * gbar) ε) D m N d Pw J) (EuclideanSpace ℂ n),
      tf.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
      (∀ j y, IsUnitary ((tf.circuit j).eval y)) ∧
      (∀ j : Fin tf.choices, (tf.circuit j).cost GeneralSourceODE.Oracles.matrixCalls =
        (q j.val).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) ∧
    ∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
      (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
      (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
      CleanErr (cleanPi (V := ℂ) w₀) (Pw x) P δ →
      CleanErr (cleanPi (V := ℂ) w₀) (J x) (ctrlL L) δ →
      30 * ratio (cq * gbar) * δ ≤ 1 / 400 → 30 * ratio (cq * gbar) * δ ≤ ε / 20 →
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      (∀ r : Fin M, IntervalIntegrable (G r) volume (t r) (t ((r : ℕ) + 1))) →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep P (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → L (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      ODESourceBranches.mass (sources (sol 0) bv ω) ≤ cq * meshScale sol b t →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * meshScale sol b t →
      sol T ≠ 0 →
      meshScale sol b t ≤ gbar * ‖sol T‖ →
      RobustBudget D x t G T N cq gbar ε ζ →
      ApproxCertificate (ODERepeatProtocol.Protocol.repeatTrials tf 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε := by
  let D' := (pullback D (Inst.input (X := X) (n := n) (m := m)))
  have hg1 : 1 ≤ ratio (cq * gbar) := by
    unfold ratio
    nlinarith
  obtain ⟨hMpos, -, -⟩ := ODEGroverAverage.chosenIterations_bounds (ratio (cq * gbar)) hg1
  have hcpos : 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D' T (cq * gbar) ε) := by
    rw [lchsCoefficients_mass D' hT (cq * gbar) ε hg1 hε hεOne]
    norm_num
  have hψ := MeshNative.seed_unit D' hM (Sum.inr false) m N d E hE
    (lchsCoefficients D' T (cq * gbar) ε) hcpos seed hSeed
  have hF := MeshNative.output_isometry D' hM (Sum.inr false) m N d E hE
    (lchsCoefficients D' T (cq * gbar) ε) hcpos
  -- The family over the exact actual oracles of the instances.
  let q₁ := MeshOracles.actualTrials D' m N d Inst.weight Inst.loader (phases ω)
    (phases_norm ω) q
  have hEval : ∀ j y, (q₁ j).eval y = (q j).eval y := fun j y =>
    MultiOracleCircuit.Program.eval_substitute (q j) _
      (MeshOracles.implementation_eval D' m N d Inst.weight Inst.loader (phases ω)
        (phases_norm ω)) y
  have hO₁ := MeshOracles.actualOracle_unitary (ι := Index D' T (cq * gbar) ε) D' m N d
    (Inst.weight_unitary (X := X) (n := n) (m := m))
    (Inst.loader_unitary (X := X) (n := n) (m := m))
  have hO₂ := actualOracleW_unitary (ι := Index D T (cq * gbar) ε) D m N d hPw hJ
  have hCost : ∀ (w : Query ⊕ SourceCall → ℕ) (j : ℕ),
      (q₁ j).cost w = (q j).cost (fun l =>
        (MeshOracles.implementation D' m N d Inst.weight Inst.loader (phases ω)
          (phases_norm ω) l).cost w) :=
    fun w j => MultiOracleCircuit.Program.cost_substitute (q j) _ w
  have hMatrix : ∀ j, (q₁ j).cost GeneralSourceODE.Oracles.matrixCalls =
      (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := fun j => by
    rw [hCost]
    exact congrArg (q j).cost (funext (MeshOracles.implementation_matrix D' m N d _ _ _ _))
  -- The same syntax, with every fixed gate lifted to the work register, on the actual oracles
  -- with a work register.
  let q₂ : ℕ → MultiOracleCircuit.Program
      (actualOracleW (ι := Index D T (cq * gbar) ε) D m N d Pw J) :=
    fun j => workRecast (piWork w₀) (q₁ j)
  refine ⟨ODERepeatProtocol.ofCircuits q₂
    (ODEGroverAverage.chosenIterations (ratio (cq * gbar))) hMpos _
    ((piWork w₀).clean_unit hψ) _ ((piWork w₀).output_isometry hF), rfl,
    fun j y => (q₂ j.val).eval_unitary hO₂ y,
    fun j => (cost_workRecast _ _ _).trans (hMatrix j.val), ?_⟩
  intro x P L δ G b sol bv U ζ hP hL hδ hPc hJc hδ1 hδε hG hGint hU hW hLoad₀ hLoad hMassB
    hCertP hTarget hB hBudget
  let p : Inst X n m := Inst.mk x P L hP hL
  have hC := hCert p G b sol bv U ζ hG hGint hU hW hLoad₀ hLoad hMassB hCertP hTarget hB
    hBudget
  have hclean := actualOracleW_clean (ι := Index D T (cq * gbar) ε) D D' m N d w₀ Pw J
    Inst.weight Inst.loader x p
    (fun l => MeshOracles.actualOracle_pullback_matrix D (Inst.input (X := X) (n := n) (m := m))
      m N d (fun _ => 1) (fun _ _ => 1) Inst.weight Inst.loader l p) (hPw x) hP hδ hPc hJc
  exact work_certificate (piWork w₀) hC q₁ hMpos hψ hF (fun j => hEval j p) hMatrix
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (MeshOracles.implementation_weight D' m N d _ _ _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (MeshOracles.implementation_load D' m N d _ _ _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (MeshOracles.implementation_unweight D' m N d _ _ _ _)))
    (fun j => by
      rw [hCost, funext (MeshOracles.implementation_source D' m N d _ _ _ _),
        GeneralSourceODE.Oracles.cost_add, NativeHermitianDilation.cost_scale])
    hO₁ hO₂ x hδ hclean hδ1 hδε hTarget

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh and preparations on
temporary work registers, for every `T ≥ 0`, represented samples of any sign.** Under uniform
sparse energy bounds, the slot conditions on `N` and public nodes in `[0, T]`, with a supplied
unitary `P_w` on the label and work registers and a supplied unitary `U_load` on the label, data
and work registers, one public trial family over the coherent sampled-time matrix oracle on `N`
slots and the supplied `P_w`, `U_load`, `P_w†` satisfies `WorkApproxBudgetOutcome` with
`Q = if T = 0 ∨ ρ = 0 then 0 else 1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)`, `g' = 2 c_q ḡ`: for every
instance whose supplied preparations are within `δ` of exact unitary preparations on a clean work
register, with `30 g' δ ≤ 1/400` and `30 g' δ ≤ ε/20`, accretive interval-integrable pieces with
propagator `U`, the sample certificate and `RobustBudget`, four fresh trials, heralded on a clean
work register, succeed with probability at least `2/3`, have conditional trace distance at most
`ε`, and make at most `40 g'` calls of each supplied operation and at most `Q` matrix queries in
every history. -/
theorem work_approx_solver_nonneg (D : Data (X × Fin M) n Z s) (hM : 0 < M) (t : ℕ → ℝ)
    {N : ℕ} (hN : 0 < N) (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
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
    (w₀ : W) (Pw : X → LabelW m W →L[ℂ] LabelW m W) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → LoadW m n W →L[ℂ] LoadW m n W) (hJ : ∀ x, IsUnitary (J x))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    WorkApproxBudgetOutcome D t N etaH etaD T gbar cq ε v ω w₀ Pw J seed
      (if T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0 then 0 else
        1274019840 * ratio (cq * gbar) * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))) := by
  by_cases hZero : T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0
  · rw [if_pos hZero]
    obtain ⟨d, E, hE, q, _hU, hCost, hCert⟩ := robust_zero_core
      (pullback D (Inst.input (X := X) (n := n) (m := m))) hM t hN etaH etaD T gbar cq ε v ω
      hH hDiss hT hZero hg hcq hε hεOne hmesh hv
      (fun y i => hrH (Inst.input y.1, y.2) i) (fun y i => hrD (Inst.input y.1, y.2) i)
      Inst.weight (Inst.weight_unitary (X := X) (n := n) (m := m))
      Inst.loader (Inst.loader_unitary (X := X) (n := n) (m := m)) seed hSeed
    obtain ⟨tf, hch, hU, hcost, hC⟩ := work_approx_build D hM t N etaH etaD T gbar cq ε v ω hT
      hg hcq hε hεOne w₀ Pw hPw J hJ seed hSeed d E hE q hCert
    have h := ODERepeatProtocol.Protocol.repeat_worstCost_le tf 4
      GeneralSourceODE.Oracles.matrixCalls 0 (fun j => by rw [hcost j]; exact hCost j.val)
    rw [mul_zero] at h
    exact ⟨d, tf, hch, hU, fun x P L δ G b sol bv U ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
      h14 h15 h16 h17 h18 => ⟨hC x P L δ G b sol bv U ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
        h12 h13 h14 h15 h16 h17 h18, h⟩⟩
  · rw [if_neg hZero]
    have hg' : 1 ≤ ratio (cq * gbar) := by unfold ratio; nlinarith
    have hε' : 0 < accuracy ε := by unfold accuracy; linarith
    have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
    have hR : 0 ≤ radius (cq * gbar) ε :=
      ImprovedODEQueryBudget.radius_nonneg _ _ hg' hε' hε'One
    have hTpos : 0 < T := lt_of_le_of_ne hT (fun h => hZero (Or.inl h.symm))
    have hρ : 0 < etaH + radius (cq * gbar) ε * etaD :=
      lt_of_le_of_ne (add_nonneg hH (mul_nonneg hR hDiss)) (fun h => hZero (Or.inr h.symm))
    obtain ⟨d, E, hE, q, _hU, hCert⟩ := robust_propagated_solver
      (pullback D (Inst.input (X := X) (n := n) (m := m))) hM t hN etaH etaD T gbar cq ε v ω
      hH hDiss hTpos hg hcq hε hεOne hmesh hρ hClock hCayley hv
      (fun y i => hrH (Inst.input y.1, y.2) i) (fun y j => hcH (Inst.input y.1, y.2) j)
      (fun y i => hrD (Inst.input y.1, y.2) i) (fun y j => hcD (Inst.input y.1, y.2) j)
      Inst.weight (Inst.weight_unitary (X := X) (n := n) (m := m))
      Inst.loader (Inst.loader_unitary (X := X) (n := n) (m := m)) seed hSeed
    obtain ⟨tf, hch, hU, -, hC⟩ := work_approx_build D hM t N etaH etaD T gbar cq ε v ω hT
      hg hcq hε hεOne w₀ Pw hPw J hJ seed hSeed d E hE q hCert
    exact ⟨d, tf, hch, hU, fun x P L δ G b sol bv U ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
      h14 h15 h16 h17 h18 =>
      let hc := hC x P L δ G b sol bv U ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
        h17 h18
      ⟨hc, hc.matrix_queries⟩⟩

/-- `WorkApproxBudgetOutcome` for integrable generator pieces (`RegularPieces`), mild solutions
(`MildSolution`), the certificate on the propagated vector integral and the budgets of the true
path, as `RepresentedSampleODE.RegularApproxOutcome`. -/
def WorkRegularOutcome (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ) (w₀ : W)
    (Pw : X → LabelW m W →L[ℂ] LabelW m W) (J : X → LoadW m n W →L[ℂ] LoadW m n W)
    (seed : EuclideanSpace ℂ n) (Q : ℝ) : Prop :=
  ∃ (d : ℕ) (tf : ODERepeatProtocol.TrialFamily
      (actualOracleW (ι := Index D T (cq * gbar) ε) D m N d Pw J) (EuclideanSpace ℂ n)),
    tf.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
    (∀ j y, IsUnitary ((tf.circuit j).eval y)) ∧
    ∀ (x : X) (P : GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
      (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
      (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
      IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
      CleanErr (cleanPi (V := ℂ) w₀) (Pw x) P δ →
      CleanErr (cleanPi (V := ℂ) w₀) (J x) (ctrlL L) δ →
      30 * ratio (cq * gbar) * δ ≤ 1 / 400 → 30 * ratio (cq * gbar) * δ ≤ ε / 20 →
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      RegularPieces t G →
      MildSolution t T b sol U →
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
/-- **Theorem `ode:thm:time` with the general source interface on a mesh, preparations on
temporary work registers, every `T ≥ 0`, the certificate on the propagated vector integral,
represented samples of any sign, integrable pieces and mild solutions.** Under the hypotheses of
`work_approx_solver_nonneg`, `WorkRegularOutcome` holds: the generator pieces need only be
integrable on their mesh intervals, the solution only be mild, and the budgets are those of the
true path. -/
theorem work_approx_solver_nonneg_regular (D : Data (X × Fin M) n Z s) (hM : 0 < M)
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
    (w₀ : W) (Pw : X → LabelW m W →L[ℂ] LabelW m W) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → LoadW m n W →L[ℂ] LoadW m n W) (hJ : ∀ x, IsUnitary (J x))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    WorkRegularOutcome D t N etaH etaD T gbar cq ε v ω w₀ Pw J seed
      (if T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0 then 0 else
        1274019840 * ratio (cq * gbar) * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))) := by
  obtain ⟨d, tf, hch, hU, hC⟩ := work_approx_solver_nonneg D hM t hN etaH etaD T gbar cq ε v ω
    hH hDiss hT hg hcq hε hεOne hmesh hClock hCayley hv hrH hcH hrD hcD w₀ Pw hPw J hJ seed
    hSeed
  refine ⟨d, tf, hch, hU, fun x P L δ G b sol bv U ζ hP hL hδ hPc hJc hδ1 hδε hG hreg hsol hUm
    hW hL0 hL' hMass hInt hTarget hB hB1 hB2 => ?_⟩
  have hD : sol T - U 0 (sol 0) T =
      ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T := by
    rw [hsol.2]
    abel
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤
      ζ * meshScale sol b t := by
    rw [hD]
    exact hInt
  exact hC x P L δ G b sol bv U ζ hP hL hδ hPc hJc hδ1 hδε hG hreg hUm hW hL0 hL' hMass
    hCertP hTarget hB (robustBudget_of_path_int D x hmesh G hG hreg hB1 hB2)

end

end SparseHamiltonian.CleanWorkODE
