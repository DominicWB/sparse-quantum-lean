import GeneralSourceExtensions.Approx.Pullback
import GeneralSourceExtensions.Zero

/-!
# The general source interface with approximately implemented preparations

The released endpoint `GeneralSourceODE.solver` assumes that the supplied weight preparation
`P_w` and the label-controlled loader `U_load` act exactly as in
`ode:eq:source-interface-preparation`. Here the supplied oracles are arbitrary unitaries within
`δ` in operator norm of exact ones: for every instance there are unitaries `P` and `L a` that
prepare the source weights and directions exactly, with `‖P_w(x) - P‖ ≤ δ` and
`‖U_load(x, a) - L a‖ ≤ δ` for every label. The exact preparations may depend on the whole instance;
they are not supplied to the algorithm.

One public trial family over the coherent sampled-time matrix oracle and the supplied `P_w`,
`U_load`, `P_w†` serves every instance. It is the released family of `GeneralSourceODE.solver`
built for the input type of exact preparation instances (`Inst`), with the sparse data read
through the input projection (`pullback`), and run on the supplied oracles (`recast`). Each
trial makes at most `10 g'` calls of each supplied operation (`g' = 2 c_q ḡ`), so it moves by at
most `30 g' δ` in operator norm; under `30 g' δ ≤ 1/400` and `30 g' δ ≤ ε / 20`, four fresh trials
succeed with probability at least `2/3` and their conditional output is within trace distance `ε`
of the normalised solution, with the released worst-case counts (`ApproxCertificate`).

* `approx_build`: the construction from the released two-interface outcome for the exact
  preparation instances;
* `approx_solver`: `ode:thm:time` with the general source interface and approximate
  preparations, under the hypotheses of the released solver;
* `approx_solver_nonneg`: the same for every `T ≥ 0` and without `ρ = η_H + R η_D > 0`, with no
  matrix query in the zero cases `T = 0` or `ρ = 0`.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSourceExtensions

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set
open TimeDependentODE GeneralSourceODE
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- **The general source interface with approximate preparations.** One public trial family over
the actual oracles, fixed before the instance; for every instance with exact unitary
preparations `P`, `L` within `δ` of the supplied `P_w(x)`, `U_load(x, ·)`, `30 g' δ ≤ 1/400` and
`30 g' δ ≤ ε / 20` (`g' = 2 c_q ḡ`), and the hypotheses of `GeneralSourceODE.Outcome` for `P`,
`L`, four fresh trials satisfy `ApproxCertificate`. -/
def ApproxOutcome (D : Data (X × Fin M) n Z s) (etaH etaD T gbar cq ε : ℝ) {m : ℕ}
    (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (d : ℕ) (t : ODERepeatProtocol.TrialFamily
      (Oracles.actualOracle (ι := Index D T (cq * gbar) ε) D m d Pw J) (EuclideanSpace ℂ n)),
    t.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
    (∀ j y, IsUnitary ((t.circuit j).eval y)) ∧
    ∀ (x : X) (P : Weights.LabelOp (Option (Fin m)))
      (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
      (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b sol : ℝ → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (βG δG ζ : ℝ),
      IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
      ‖Pw x - P‖ ≤ δ → (∀ a, ‖J x a - L a‖ ≤ δ) →
      30 * ratio (cq * gbar) * δ ≤ 1 / 400 → 30 * ratio (cq * gbar) * δ ≤ ε / 20 →
      0 ≤ βG →
      (∀ u ∈ Icc 0 T, Accretive (G u)) →
      (∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|) →
      (∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG) →
      ContinuousOn b (Icc 0 T) →
      SolvesODE G b sol 0 T →
      IsPropagator G U T →
      Compiled.WeightPrep P (sources (sol 0) (fun i => b (v i)) ω) →
      (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → b (v i) ≠ 0 → L (some i) seed =
        ODEStateNormalization.unitDirection (b (v i))) →
      ODESourceBranches.mass (sources (sol 0) (fun i => b (v i)) ω) ≤
        cq * sourceScale sol b T →
      ‖(∫ u in (0 : ℝ)..T, U u (b u) T) - ∑ i, ω i • U (v i) (b (v i)) T‖ ≤
        ζ * sourceScale sol b T →
      sol T ≠ 0 →
      sourceScale sol b T ≤ gbar * ‖sol T‖ →
      ζ + cq * (T * (βG * (T / M) + δG)) ≤ ε / (2000 * gbar) →
      ApproxCertificate (ODERepeatProtocol.Protocol.repeatTrials t 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

/-- `ApproxOutcome` in which the four-attempt protocol makes at most `Q` matrix queries in every
history. -/
def ApproxBudgetOutcome (D : Data (X × Fin M) n Z s) (etaH etaD T gbar cq ε : ℝ) {m : ℕ}
    (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Q : ℝ) : Prop :=
  ∃ (d : ℕ) (t : ODERepeatProtocol.TrialFamily
      (Oracles.actualOracle (ι := Index D T (cq * gbar) ε) D m d Pw J) (EuclideanSpace ℂ n)),
    t.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
    (∀ j y, IsUnitary ((t.circuit j).eval y)) ∧
    ∀ (x : X) (P : Weights.LabelOp (Option (Fin m)))
      (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
      (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b sol : ℝ → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (βG δG ζ : ℝ),
      IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
      ‖Pw x - P‖ ≤ δ → (∀ a, ‖J x a - L a‖ ≤ δ) →
      30 * ratio (cq * gbar) * δ ≤ 1 / 400 → 30 * ratio (cq * gbar) * δ ≤ ε / 20 →
      0 ≤ βG →
      (∀ u ∈ Icc 0 T, Accretive (G u)) →
      (∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|) →
      (∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG) →
      ContinuousOn b (Icc 0 T) →
      SolvesODE G b sol 0 T →
      IsPropagator G U T →
      Compiled.WeightPrep P (sources (sol 0) (fun i => b (v i)) ω) →
      (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → b (v i) ≠ 0 → L (some i) seed =
        ODEStateNormalization.unitDirection (b (v i))) →
      ODESourceBranches.mass (sources (sol 0) (fun i => b (v i)) ω) ≤
        cq * sourceScale sol b T →
      ‖(∫ u in (0 : ℝ)..T, U u (b u) T) - ∑ i, ω i • U (v i) (b (v i)) T‖ ≤
        ζ * sourceScale sol b T →
      sol T ≠ 0 →
      sourceScale sol b T ≤ gbar * ‖sol T‖ →
      ζ + cq * (T * (βG * (T / M) + δG)) ≤ ε / (2000 * gbar) →
      ApproxCertificate (ODERepeatProtocol.Protocol.repeatTrials t 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε ∧
      ((ODERepeatProtocol.Protocol.repeatTrials t 4).worstCost Oracles.matrixCalls : ℝ) ≤ Q

omit [DecidableEq Z] in
/-- Forgetting the budget. -/
theorem approxOutcome_of_budget (D : Data (X × Fin M) n Z s) (etaH etaD T gbar cq ε : ℝ)
    {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ) (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Q : ℝ)
    (h : ApproxBudgetOutcome D etaH etaD T gbar cq ε v ω Pw J seed Q) :
    ApproxOutcome D etaH etaD T gbar cq ε v ω Pw J seed := by
  obtain ⟨d, t, hch, hU, hC⟩ := h
  exact ⟨d, t, hch, hU, fun x P L δ G b sol U βG δG ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    h14 h15 h16 h17 h18 h19 h20 h21 h22 => (hC x P L δ G b sol U βG δG ζ h1 h2 h3 h4 h5 h6 h7 h8
      h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22).1⟩

set_option maxHeartbeats 8000000 in
/-- **The construction.** From the released two-interface outcome for the exact preparation
instances `Inst X n m` (the sparse data read through `Inst.input`), the released public trial
family run on the supplied oracles `P_w`, `U_load`, `P_w†` has the per-trial matrix costs of the
two-interface family and satisfies `ApproxCertificate` for every instance with exact
preparations within `δ`. -/
theorem approx_build (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a)) (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) (d : ℕ)
    (E : Native.SourceSpace
        (Index (pullback D (Inst.input (X := X) (n := n) (m := m))) T (cq * gbar) ε) n m →L[ℂ]
      Native.MatrixSpace
        (Index (pullback D (Inst.input (X := X) (n := n) (m := m))) T (cq * gbar) ε) n Z m M d)
    (hE : E† ∘L E = 1)
    (q : ℕ → MultiOracleCircuit.Program
      (Native.physicalOracle
        (ι := Index (pullback D (Inst.input (X := X) (n := n) (m := m))) T (cq * gbar) ε)
        (pullback D (Inst.input (X := X) (n := n) (m := m))) m d Inst.weight Inst.loader
        (phases ω)))
    (hCert : ∀ (p : Inst X n m) (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b sol : ℝ → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (βG δG ζ : ℝ), 0 ≤ βG →
      (∀ u ∈ Icc 0 T, Accretive (G u)) →
      (∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|) →
      (∀ r : Fin M, ‖G ((r : ℕ) * T / M) - SparseStateOverlap.matrixOperator
        ((pullback D (Inst.input (X := X) (n := n) (m := m))).matrix (p, r))‖ ≤ δG) →
      SolvesODE G b sol 0 T →
      IsPropagator G U T →
      Compiled.WeightPrep (Inst.weight p) (sources (sol 0) (fun i => b (v i)) ω) →
      (sol 0 ≠ 0 → Inst.loader p none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → b (v i) ≠ 0 → Inst.loader p (some i) seed =
        ODEStateNormalization.unitDirection (b (v i))) →
      ODESourceBranches.mass (sources (sol 0) (fun i => b (v i)) ω) ≤
        cq * sourceScale sol b T →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (b (v i)) T‖ ≤
        ζ * sourceScale sol b T →
      sol T ≠ 0 →
      sourceScale sol b T ≤ gbar * ‖sol T‖ →
      ζ + cq * (T * (βG * (T / M) + δG)) ≤ ε / (2000 * gbar) →
      ODECompleteTrial.Certificate q
        (ODEGroverAverage.chosenIterations (ratio (cq * gbar)))
        (Native.input (pullback D (Inst.input (X := X) (n := n) (m := m))) hM (Sum.inr false) m d
          (ODECompiledSource.seed E
            (Compiled.seedCoefficients (lchsCoefficients
              (pullback D (Inst.input (X := X) (n := n) (m := m))) T (cq * gbar) ε)) seed))
        (Native.input (pullback D (Inst.input (X := X) (n := n) (m := m))) hM (Sum.inr false) m d ∘L
          ODECompiledSource.output E
            (Compiled.seedCoefficients (lchsCoefficients
              (pullback D (Inst.input (X := X) (n := n) (m := m))) T (cq * gbar) ε)))
        p (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε) :
    ∃ t : ODERepeatProtocol.TrialFamily
        (Oracles.actualOracle (ι := Index D T (cq * gbar) ε) D m d Pw J) (EuclideanSpace ℂ n),
      t.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
      (∀ j y, IsUnitary ((t.circuit j).eval y)) ∧
      (∀ j : Fin t.choices, (t.circuit j).cost Oracles.matrixCalls =
        (q j.val).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1))) ∧
      ∀ (x : X) (P : Weights.LabelOp (Option (Fin m)))
        (L : Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (δ : ℝ)
        (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
        (b sol : ℝ → EuclideanSpace ℂ n)
        (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (βG δG ζ : ℝ),
        IsUnitary P → (∀ a, IsUnitary (L a)) → 0 ≤ δ →
        ‖Pw x - P‖ ≤ δ → (∀ a, ‖J x a - L a‖ ≤ δ) →
        30 * ratio (cq * gbar) * δ ≤ 1 / 400 → 30 * ratio (cq * gbar) * δ ≤ ε / 20 →
        0 ≤ βG →
        (∀ u ∈ Icc 0 T, Accretive (G u)) →
        (∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|) →
        (∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
          SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG) →
        ContinuousOn b (Icc 0 T) →
        SolvesODE G b sol 0 T →
        IsPropagator G U T →
        Compiled.WeightPrep P (sources (sol 0) (fun i => b (v i)) ω) →
        (sol 0 ≠ 0 → L none seed = ODEStateNormalization.unitDirection (sol 0)) →
        (∀ i, ω i ≠ 0 → b (v i) ≠ 0 → L (some i) seed =
          ODEStateNormalization.unitDirection (b (v i))) →
        ODESourceBranches.mass (sources (sol 0) (fun i => b (v i)) ω) ≤
          cq * sourceScale sol b T →
        ‖(∫ u in (0 : ℝ)..T, U u (b u) T) - ∑ i, ω i • U (v i) (b (v i)) T‖ ≤
          ζ * sourceScale sol b T →
        sol T ≠ 0 →
        sourceScale sol b T ≤ gbar * ‖sol T‖ →
        ζ + cq * (T * (βG * (T / M) + δG)) ≤ ε / (2000 * gbar) →
        ApproxCertificate (ODERepeatProtocol.Protocol.repeatTrials t 4) x (sol T) (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
          (ratio (cq * gbar)) ε := by
  let D' := pullback D (Inst.input (X := X) (n := n) (m := m))
  have hg1 : 1 ≤ ratio (cq * gbar) := by
    unfold ratio
    nlinarith
  obtain ⟨hMpos, -, -⟩ := ODEGroverAverage.chosenIterations_bounds (ratio (cq * gbar)) hg1
  have hPSD' : ∀ (y : Inst X n m × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator
        (ODEMatrixEnergy.dissipativePart (D'.matrix y)) w)).re :=
    fun y w => hPSD (Inst.input y.1, y.2) w
  have hcpos : 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D' T (cq * gbar) ε) := by
    have hL : 0 ≤ lipschitz D' T :=
      mul_nonneg hT (mul_nonneg (Nat.cast_nonneg s) D'.scale_pos.le)
    have hε' : 0 < accuracy ε := by unfold accuracy; linarith
    have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
    obtain ⟨-, -, hMass, -⟩ := GaussianLCHS.table_certificate
      (fun y : Inst X n m × Option (Fin m) => family D' hM T v y.1 y.2)
      (fun y z => family_analyticAt D' hM T v y.1 y.2 z)
      (fun y z hz => family_norm_le_one D' hM T hT v hPSD' y.1 y.2 z hz)
      (lipschitz D' T) hL (fun y k l => family_lipschitz D' hM T hT v y.1 y.2 k l)
      (ratio (cq * gbar)) (accuracy ε) hg1 hε' hε'One
    have hc : ODECoherentLCU.coefficientMass (lchsCoefficients D' T (cq * gbar) ε) = 3 :=
      ODECoefficientPadding.coefficientMass_eq _ 3 hMass
    rw [hc]
    norm_num
  have hψ := Native.seed_unit D' hM (Sum.inr false) m d E hE
    (lchsCoefficients D' T (cq * gbar) ε) hcpos seed hSeed
  have hF := Native.output_isometry D' hM (Sum.inr false) m d E hE
    (lchsCoefficients D' T (cq * gbar) ε) hcpos
  -- The family over the exact actual oracles of the instances.
  let q₁ := Oracles.actualTrials D' m d Inst.weight Inst.loader (phases ω) (phases_norm ω) q
  have hEval : ∀ j y, (q₁ j).eval y = (q j).eval y := fun j y =>
    MultiOracleCircuit.Program.eval_substitute (q j) _
      (Oracles.implementation_eval D' m d Inst.weight Inst.loader (phases ω) (phases_norm ω)) y
  have hO₁ := Oracles.actualOracle_unitary (ι := Index D' T (cq * gbar) ε) D' m d
    (Inst.weight_unitary (X := X) (n := n) (m := m))
    (Inst.loader_unitary (X := X) (n := n) (m := m))
  have hO₂ := Oracles.actualOracle_unitary (ι := Index D T (cq * gbar) ε) D m d hPw hJ
  have hCost : ∀ (w : Query ⊕ SourceCall → ℕ) (j : ℕ),
      (q₁ j).cost w = (q j).cost (fun l =>
        (Oracles.implementation D' m d Inst.weight Inst.loader (phases ω) (phases_norm ω) l).cost
          w) :=
    fun w j => MultiOracleCircuit.Program.cost_substitute (q j) _ w
  have hMatrix : ∀ j, (q₁ j).cost Oracles.matrixCalls =
      (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := fun j => by
    rw [hCost]
    exact congrArg (q j).cost (funext (Oracles.implementation_matrix D' m d _ _ _ _))
  -- The same syntax on the supplied oracles.
  let q₂ : ℕ → MultiOracleCircuit.Program
      (Oracles.actualOracle (ι := Index D T (cq * gbar) ε) D m d Pw J) :=
    fun j => recast (q₁ j)
  refine ⟨ODERepeatProtocol.ofCircuits q₂
    (ODEGroverAverage.chosenIterations (ratio (cq * gbar))) hMpos _ hψ _ hF, rfl,
    fun j y => (q₂ j.val).eval_unitary hO₂ y, fun j => (cost_recast _ _).trans (hMatrix j.val),
    ?_⟩
  intro x P L δ G b sol U βG δG ζ hP hL hδ hPd hLd hδ1 hδε hβG hG hGLip hGs hbc hsol hU hW
    hLoad₀ hLoad hMassB hInt hTarget hB hBudget
  let p : Inst X n m := Inst.mk x P L hP hL
  -- Duhamel's formula turns the vector-integral certificate into the
  -- propagated-sum certificate.
  have hΛ : ∀ u ∈ Icc 0 T, ‖G u‖ ≤ ‖G 0‖ + βG * T := by
    intro u hu
    have h := hGLip u hu 0 ⟨le_rfl, hT⟩
    rw [sub_zero, abs_of_nonneg hu.1] at h
    calc
      ‖G u‖ = ‖G 0 + (G u - G 0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖G 0‖ + ‖G u - G 0‖ := norm_add_le _ _
      _ ≤ ‖G 0‖ + βG * T := add_le_add le_rfl (h.trans (mul_le_mul_of_nonneg_left hu.2 hβG))
  have hDu := duhamel hT hU hG _ hΛ hbc hsol
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (b (v i)) T‖ ≤
      ζ * sourceScale sol b T := by
    rw [← hDu]
    exact hInt
  have hC := hCert p G b sol U βG δG ζ hβG hG hGLip hGs hsol hU hW hLoad₀ hLoad hMassB hCertP
    hTarget hB hBudget
  have hdev := actualOracle_dev (ι := Index D T (cq * gbar) ε) D D' m d Pw J Inst.weight
    Inst.loader x p
    (fun l => actualOracle_pullback_matrix D (Inst.input (X := X) (n := n) (m := m)) m d Pw J
      Inst.weight Inst.loader l p) hδ hPd hLd
  exact approx_certificate hC q₁ hMpos hψ hF (fun j => hEval j p) hMatrix
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (Oracles.implementation_weight D' m d _ _ _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (Oracles.implementation_load D' m d _ _ _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (Oracles.implementation_unweight D' m d _ _ _ _)))
    (fun j => by
      rw [hCost, funext (Oracles.implementation_source D' m d _ _ _ _), Oracles.cost_add,
        NativeHermitianDilation.cost_scale])
    hO₁ hO₂ x hδ hdev hδ1 hδε hTarget

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface and approximate
preparations.** Under the hypotheses of the released `GeneralSourceODE.solver`, with supplied
unitary `P_w` and `U_load`, one public trial family over the coherent sampled-time matrix oracle
and the supplied `P_w`, `U_load` and `P_w†` satisfies `ApproxOutcome`: for every instance with
exact unitary preparations `P`, `L` within `δ` of the supplied ones, `30 g' δ ≤ 1/400` and
`30 g' δ ≤ ε / 20` (`g' = 2 c_q ḡ`) and the released instance hypotheses for `P`, `L`, four fresh
trials succeed with probability at least `2/3`, have conditional trace distance at most `ε` and
make at most `1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)` matrix queries and `40 g'` calls of each of
`P_w`, `U_load` and `P_w†` in every history. -/
theorem approx_solver (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 < T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hρ : 0 < etaH + radius (cq * gbar) ε * etaD)
    (hMesh : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ M)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (M : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ApproxOutcome D etaH etaD T gbar cq ε v ω Pw J seed := by
  obtain ⟨d, E, hE, q, _hU, hCert⟩ := propagated_solver
    (pullback D (Inst.input (X := X) (n := n) (m := m))) hM etaH etaD T gbar cq ε v ω
    hH hDiss hT hg hcq hε hεOne hρ hMesh hCayley hv
    (fun y i => hrH (Inst.input y.1, y.2) i) (fun y j => hcH (Inst.input y.1, y.2) j)
    (fun y i => hrD (Inst.input y.1, y.2) i) (fun y j => hcD (Inst.input y.1, y.2) j)
    (fun y w => hPSD (Inst.input y.1, y.2) w)
    Inst.weight (Inst.weight_unitary (X := X) (n := n) (m := m))
    Inst.loader (Inst.loader_unitary (X := X) (n := n) (m := m)) seed hSeed
  obtain ⟨t, hch, hU, -, hC⟩ := approx_build D hM etaH etaD T gbar cq ε v ω hT.le hg hcq hε
    hεOne hPSD Pw hPw J hJ seed hSeed d E hE q hCert
  exact ⟨d, t, hch, hU, hC⟩

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface and approximate preparations,
for every `T ≥ 0`.** Under the hypotheses of `approx_solver` with `0 ≤ T` in place of `0 < T` and
without `ρ = η_H + R η_D > 0`, `ApproxBudgetOutcome` holds with
`Q = if T = 0 ∨ ρ = 0 then 0 else 1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)`: in the zero cases the
public trial family uses the identity SELECT and makes no matrix query. -/
theorem approx_solver_nonneg (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hMesh : 8 * s * ((etaH + radius (cq * gbar) ε * etaD) * T) ≤ M)
    (hCayley : 3 * (Real.sqrt (2 * (s : ℝ)) *
      ((etaH + radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
        precision (cq * gbar) ε * (M : ℝ) ^ 2)
    (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hcH : ∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hcD : ∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    ApproxBudgetOutcome D etaH etaD T gbar cq ε v ω Pw J seed
      (if T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0 then 0 else
        1274019840 * ratio (cq * gbar) * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))) := by
  by_cases hZero : T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0
  · rw [if_pos hZero]
    obtain ⟨d, E, hE, q, _hU, hCost, hCert⟩ := zero_core
      (pullback D (Inst.input (X := X) (n := n) (m := m))) hM etaH etaD T gbar cq ε v ω
      hH hDiss hT hZero hg hcq hε hεOne hv
      (fun y i => hrH (Inst.input y.1, y.2) i) (fun y i => hrD (Inst.input y.1, y.2) i)
      (fun y w => hPSD (Inst.input y.1, y.2) w)
      Inst.weight (Inst.weight_unitary (X := X) (n := n) (m := m))
      Inst.loader (Inst.loader_unitary (X := X) (n := n) (m := m)) seed hSeed
    obtain ⟨t, hch, hU, hcost, hC⟩ := approx_build D hM etaH etaD T gbar cq ε v ω hT hg hcq hε
      hεOne hPSD Pw hPw J hJ seed hSeed d E hE q hCert
    have h := ODERepeatProtocol.Protocol.repeat_worstCost_le t 4 Oracles.matrixCalls 0
      (fun j => by rw [hcost j]; exact hCost j.val)
    rw [mul_zero] at h
    exact ⟨d, t, hch, hU, fun x P L δ G b sol U βG δG ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 => ⟨hC x P L δ G b sol U βG δG ζ h1 h2 h3 h4 h5 h6
        h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22, h⟩⟩
  · rw [if_neg hZero]
    have hg' : 1 ≤ ratio (cq * gbar) := by unfold ratio; nlinarith
    have hε' : 0 < accuracy ε := by unfold accuracy; linarith
    have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
    have hR : 0 ≤ radius (cq * gbar) ε :=
      ImprovedODEQueryBudget.radius_nonneg _ _ hg' hε' hε'One
    have hTpos : 0 < T := lt_of_le_of_ne hT (fun h => hZero (Or.inl h.symm))
    have hρ : 0 < etaH + radius (cq * gbar) ε * etaD :=
      lt_of_le_of_ne (add_nonneg hH (mul_nonneg hR hDiss)) (fun h => hZero (Or.inr h.symm))
    obtain ⟨d, E, hE, q, _hU, hCert⟩ := propagated_solver
      (pullback D (Inst.input (X := X) (n := n) (m := m))) hM etaH etaD T gbar cq ε v ω
      hH hDiss hTpos hg hcq hε hεOne hρ hMesh hCayley hv
      (fun y i => hrH (Inst.input y.1, y.2) i) (fun y j => hcH (Inst.input y.1, y.2) j)
      (fun y i => hrD (Inst.input y.1, y.2) i) (fun y j => hcD (Inst.input y.1, y.2) j)
      (fun y w => hPSD (Inst.input y.1, y.2) w)
      Inst.weight (Inst.weight_unitary (X := X) (n := n) (m := m))
      Inst.loader (Inst.loader_unitary (X := X) (n := n) (m := m)) seed hSeed
    obtain ⟨t, hch, hU, -, hC⟩ := approx_build D hM etaH etaD T gbar cq ε v ω hT hg hcq hε
      hεOne hPSD Pw hPw J hJ seed hSeed d E hE q hCert
    refine ⟨d, t, hch, hU, fun x P L δ G b sol U βG δG ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
      h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 => ?_⟩
    have hc := hC x P L δ G b sol U βG δG ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
      h16 h17 h18 h19 h20 h21 h22
    exact ⟨hc, hc.matrix_queries⟩

end

end SparseHamiltonian.GeneralSourceExtensions
