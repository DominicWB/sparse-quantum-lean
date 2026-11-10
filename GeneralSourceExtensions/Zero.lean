import GeneralSourceODE.Theorem
import ZeroTimeRemarks.ODETime

/-!
# The general source interface at zero time or with a known zero generator

The released endpoint `SparseHamiltonian.GeneralSourceODE.solver` of Theorem `ode:thm:time` with
the general source interface assumes `T > 0` and `ρ = η_H + R η_D > 0`. As for the earlier ODE
solvers (`ZeroTimeRemarks`), zero time or a known zero generator needs no matrix query: at
`T = 0` every slot duration of every source label vanishes, and with `η_H + R η_D = 0` every
represented sample vanishes, so every branch product is the identity and the identity program is
an exact SELECT for the released clean encoding at the rescaling `γ = 1`.

* `trial_matrix_cost`: the released public trials of `GeneralSourceODE.Native` built on the
  identity SELECT make no matrix query;
* `durationTable_zero`, `durationTable_eq_zero`: at `T = 0` every duration vanishes, so the
  branch products are the identity (`ZeroTimeRemarks.ODETime.branchEvolution_eq_one`), as they
  are when every sample vanishes;
* `zero_core`: the identity SELECT in the zero cases, with no matrix query in any trial
  (`PropagatedTrialOutcome … 0`);
* `zero_propagated_solver`: `GeneralSourceODE.PropagatedOutcome` in the zero cases, with the
  released public seed and output flag and the four-attempt protocol making no matrix query
  (`PropagatedBudgetOutcome … 0`);
* `zero_solver`: the same on the actual oracles `P_w`, `U_load`, `P_w†` (`BudgetOutcome … 0`);
* **`solver_nonneg`**: `ode:thm:time` with the general source interface for every `T ≥ 0` and
  without `ρ > 0`, with matrix-query budget `if T = 0 ∨ η_H + R η_D = 0 then 0 else` the released
  bound.

References to the manuscript use its labels.
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

set_option maxHeartbeats 3000000 in
/-- With the identity SELECT, every trial of the released public family of the general source
interface makes no matrix query. -/
theorem trial_matrix_cost {ι : Type*} [Fintype ι] [DecidableEq ι] (D : Data (X × Fin M) n Z s)
    (hM : 0 < M) (i0 : ι) (m d : ℕ) (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (φ : Option (Fin m) → ℂ)
    (E : Native.SourceSpace ι n m →L[ℂ] Native.MatrixSpace ι n Z m M d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1) (j : ℕ) :
    (Native.publicTrials D hM i0 m d MultiOracleCircuit.Program.identity Pw J φ E hE c seed
      hSeed hOutput j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0 := by
  unfold Native.publicTrials
  rw [ODECoordinateNativeControl.compile_matrix_cost]
  unfold Compiled.publicLogicalTrials
  rw [ODECountedAmplification.cost_eq]
  apply Nat.mul_eq_zero.mpr
  right
  apply Nat.mul_eq_zero.mpr
  right
  exact (Compiled.program_matrix_cost _ _ E hE _).trans
    (MultiOracleCircuit.Program.cost_identity _)

/-- At `T = 0` the duration table of every source label vanishes. -/
theorem durationTable_zero {ι : Type*} {m : ℕ} (v : Fin m → ℝ) (hv : ∀ i, v i ∈ Icc 0 0)
    (b : Option (Fin m) × ι) (r : Fin M) : durationTable 0 v b r = 0 := by
  have h0 : startTime v b.1 = 0 := by
    cases hb : b.1 with
    | none => rfl
    | some i => exact le_antisymm (hv i).2 (hv i).1
  unfold durationTable durations width clip
  rw [h0]
  simp

/-- At `T = 0` the duration table of every source label vanishes (for any label type). -/
theorem durationTable_eq_zero {ι : Type*} {m : ℕ} {T : ℝ} (hT0 : T = 0) (v : Fin m → ℝ)
    (hv : ∀ i, v i ∈ Icc 0 T) (b : Option (Fin m) × ι) (r : Fin M) :
    durationTable T v b r = 0 := by
  subst hT0
  exact durationTable_zero v hv b r

/-- **The two-interface outcome with a matrix-query budget**: `GeneralSourceODE.PropagatedOutcome`
in which, in addition, the certified four-attempt protocol has worst-case matrix-query count at
most `Q` (so every history makes at most `Q` matrix queries). -/
def PropagatedBudgetOutcome (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Q : ℝ) : Prop :=
  ∃ (d : ℕ)
    (E : Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      Native.MatrixSpace (Index D T (cq * gbar) ε) n Z m M d)
    (_hE : E† ∘L E = 1)
    (q : ℕ → MultiOracleCircuit.Program
      (Native.physicalOracle (ι := Index D T (cq * gbar) ε) D m d Pw J (phases ω))),
    (∀ j y, IsUnitary ((q j).eval y)) ∧
    ∀ (x : X) (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b sol : ℝ → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (βG δG ζ : ℝ), 0 ≤ βG →
      (∀ u ∈ Icc 0 T, Accretive (G u)) →
      (∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|) →
      (∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG) →
      SolvesODE G b sol 0 T →
      IsPropagator G U T →
      Compiled.WeightPrep (Pw x) (sources (sol 0) (fun i => b (v i)) ω) →
      (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → b (v i) ≠ 0 → J x (some i) seed =
        ODEStateNormalization.unitDirection (b (v i))) →
      ODESourceBranches.mass (sources (sol 0) (fun i => b (v i)) ω) ≤
        cq * sourceScale sol b T →
      ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (b (v i)) T‖ ≤
        ζ * sourceScale sol b T →
      sol T ≠ 0 →
      sourceScale sol b T ≤ gbar * ‖sol T‖ →
      ζ + cq * (T * (βG * (T / M) + δG)) ≤ ε / (2000 * gbar) →
      ∃ h : ODECompleteTrial.Certificate q
          (ODEGroverAverage.chosenIterations (ratio (cq * gbar)))
          (Native.input D hM (Sum.inr false) m d
            (ODECompiledSource.seed E
              (Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)) seed))
          (Native.input D hM (Sum.inr false) m d ∘L
            ODECompiledSource.output E
              (Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)))
          x (sol T) (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
          (ratio (cq * gbar)) ε,
        ((ODECompleteTrial.algorithm h.trial).worstCost
          (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤ Q

/-- **The two-interface outcome with a per-trial matrix-query budget**:
`GeneralSourceODE.PropagatedOutcome` in which every trial circuit makes at most `Qt` matrix
queries. -/
def PropagatedTrialOutcome (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Qt : ℝ) : Prop :=
  ∃ (d : ℕ)
    (E : Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      Native.MatrixSpace (Index D T (cq * gbar) ε) n Z m M d)
    (_hE : E† ∘L E = 1)
    (q : ℕ → MultiOracleCircuit.Program
      (Native.physicalOracle (ι := Index D T (cq * gbar) ε) D m d Pw J (phases ω))),
    (∀ j y, IsUnitary ((q j).eval y)) ∧
    (∀ j, ((q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤ Qt) ∧
    ∀ (x : X) (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b sol : ℝ → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (βG δG ζ : ℝ), 0 ≤ βG →
      (∀ u ∈ Icc 0 T, Accretive (G u)) →
      (∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|) →
      (∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG) →
      SolvesODE G b sol 0 T →
      IsPropagator G U T →
      Compiled.WeightPrep (Pw x) (sources (sol 0) (fun i => b (v i)) ω) →
      (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → b (v i) ≠ 0 → J x (some i) seed =
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
        (Native.input D hM (Sum.inr false) m d
          (ODECompiledSource.seed E
            (Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)) seed))
        (Native.input D hM (Sum.inr false) m d ∘L
          ODECompiledSource.output E
            (Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)))
        x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε

set_option maxHeartbeats 4000000 in
/-- **The identity SELECT in the zero cases** (two counted source interfaces): if `T = 0` or
`η_H + R η_D = 0`, the released public trial family with the identity SELECT makes no matrix
query in any trial and satisfies the released complete certificate for every valid instance. The
mesh conditions and the column promises are not needed. -/
theorem zero_core (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hZero : T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    PropagatedTrialOutcome D hM etaH etaD T gbar cq ε v ω Pw J seed 0 := by
  set g : ℝ := cq * gbar with hgdef
  have hg1 : 1 ≤ g := by nlinarith
  have hg' : 1 ≤ ratio g := by unfold ratio; linarith
  have hε' : 0 < accuracy ε := by unfold accuracy; linarith
  have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
  have hε'Half : accuracy ε ≤ 1 / 2 := by unfold accuracy; linarith
  have hν : 0 < precision g ε := ImprovedODEQueryBudget.precision_pos _ _ hg' hε'
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  -- One public Gaussian table for every product family.
  have hL : 0 ≤ lipschitz D T :=
    mul_nonneg hT (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
  obtain ⟨_hGrid, _hNodes, hMass, hApprox⟩ := GaussianLCHS.table_certificate
    (fun y : X × Option (Fin m) => family D hM T v y.1 y.2)
    (fun y z => family_analyticAt D hM T v y.1 y.2 z)
    (fun y z hz => family_norm_le_one D hM T hT v hPSD y.1 y.2 z hz)
    (lipschitz D T) hL (fun y k l => family_lipschitz D hM T hT v y.1 y.2 k l)
    (ratio g) (accuracy ε) hg' hε' hε'One
  have hc : ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε) = 3 :=
    ODECoefficientPadding.coefficientMass_eq _ 3 hMass
  -- Every branch product is the identity.
  have hOne : ∀ (x : X) (a' : Native.Label (Index D T g ε) m),
      TimeDependentODE.Select.branchEvolution D hM (nodeTable D T g ε m) (durationTable T v) x
        a' = 1 := by
    intro x a'
    apply ZeroTimeRemarks.ODETime.branchEvolution_eq_one
    rcases hZero with hT0 | hρ
    · left
      intro r
      exact durationTable_eq_zero hT0 v hv a' r
    · right
      intro r
      have hRadius : 0 < radius g ε :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4)
          (ODEGaussianParameters.radius_ge_four _ _ hg' hε' hε'One)
      exact ODEZeroEnergy.matrix_zero_of_effective_energy (D.matrix (x, r)) etaH etaD
        (radius g ε) hH hDiss hRadius hρ (hrH (x, r)) (hrD (x, r))
  -- The identity SELECT on the released clean encoding at the rescaling `γ = 1`.
  let i0 : Index D T g ε := Sum.inr false
  let ρ : ℝ := etaH + radius g ε * etaD
  let d := TimeDependentODE.Select.degree (s : ℝ) 1 ρ T (precision g ε) M
  let E : Native.SourceSpace (Index D T g ε) n m →L[ℂ]
      Native.MatrixSpace (Index D T g ε) n Z m M d :=
    TimeDependentODE.Select.alignedInput D hM (Native.dummy hM i0 m) 1 ρ T (precision g ε)
  have hEiso : E† ∘L E = 1 := ZeroTimeRemarks.ODETime.alignedInput_isometry D hM _ 1 ρ T _
  let pN : MultiOracleCircuit.Program
      (Native.matrixOracle (ι := Index D T g ε) D m d) := MultiOracleCircuit.Program.identity
  let c := lchsCoefficients D T g ε
  have hcpos : 0 < ODECoherentLCU.coefficientMass c := by
    change 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D T g ε)
    rw [hc]
    norm_num
  have hsc : 0 < ODECoherentLCU.coefficientMass (Compiled.seedCoefficients (N := m) c) := by
    rw [Compiled.seedCoefficients_mass]
    exact hcpos
  have hSeedUnit := ODECompiledSource.seed_unit E (Compiled.seedCoefficients c) hEiso hsc
    seed hSeed
  have hOutput := ODECompiledSource.output_isometry E (Compiled.seedCoefficients c) hEiso hsc
  let q := Native.publicTrials D hM i0 m d pN Pw J (phases ω) E hEiso c seed
    hSeedUnit hOutput
  have hΘ : 0 ≤ ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε) :=
    ImprovedODEQueryBudget.theta_nonneg _ _ _ _ (mul_nonneg hT hH) (mul_nonneg hT hDiss)
      hg' hε' hε'One
  have hLog : 0 ≤ ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε) :=
    le_trans zero_le_one (ImprovedODEQueryBudget.logBudget_ge_one _ _ hg' hε' hε'One)
  have hq : (pN.count : ℝ) ≤ 10616832 * ImprovedODEQueryBudget.queryShape (s : ℝ)
      (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
      (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) := by
    rw [MultiOracleCircuit.Program.count_identity, Nat.cast_zero]
    exact mul_nonneg (by norm_num) (ImprovedODEQueryBudget.queryShape_nonneg _ _ _ hΘ hLog)
  have hOracle := Native.physicalOracle_unitary (ι := Index D T g ε) D m d Pw hPw J hJ
    (phases ω) (phases_norm ω)
  have hCost : ∀ j, (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0 :=
    fun j => trial_matrix_cost D hM i0 m d Pw J (phases ω) E hEiso c seed _ _ j
  refine ⟨d, E, hEiso, q, fun j y => (q j).eval_unitary hOracle y,
    fun j => by rw [hCost j, Nat.cast_zero], ?_⟩
  intro x G b sol U βG δG ζ hβG hG hGLip hGs _hsol hU hW hLoad₀ hLoad hMassB hCert
    hTarget hB hBudget
  -- The propagated target of the represented samples.
  let Gs := Sampling.generator D hM x
  have hGsAcc : ∀ r, Accretive (Gs r) := Sampling.generator_accretive D hM hPSD x
  let bv : Fin m → EuclideanSpace ℂ n := fun i => b (v i)
  let z := sources (sol 0) bv ω
  let y := nodeTarget Gs T M v (sol 0) bv ω
  set Bs := sourceScale sol b T with hBs
  have hδG : 0 ≤ δG := (norm_nonneg _).trans (hGs ⟨0, hM⟩)
  have hGs' : ∀ r < M, ‖G (r * T / M) - Gs r‖ ≤ δG := by
    intro r hr
    have hidx : TimeDependent.Sampled.sampleIndex hM r = ⟨r, hr⟩ :=
      Fin.ext (Nat.mod_eq_of_lt hr)
    change ‖G (r * T / M) - SparseStateOverlap.matrixOperator
      (D.matrix (x, TimeDependent.Sampled.sampleIndex hM r))‖ ≤ δG
    rw [hidx]
    exact hGs ⟨r, hr⟩
  have hTargetErr := target_error hT hM v hv ω G hG Gs hGsAcc βG δG hβG hδG hGLip hGs'
    U hU (sol 0) bv
  set K : ℝ := βG * (T / M) + δG with hK
  have hK0 : 0 ≤ K := add_nonneg (mul_nonneg hβG (div_nonneg hT hMR.le)) hδG
  have hBs0 : 0 ≤ Bs :=
    add_nonneg (norm_nonneg _) (intervalIntegral.integral_nonneg hT fun u _ => norm_nonneg _)
  have hErr : ‖sol T - y‖ ≤ (ζ + cq * (T * K)) * Bs := by
    have hsplit : sol T - y =
        (sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (b (v i)) T) +
          ((U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - y) := by
      simp only [bv]
      abel
    rw [hsplit]
    have hMassK : T * K * ODESourceBranches.mass z ≤ cq * (T * K) * Bs := by
      have hTK : 0 ≤ T * K := mul_nonneg hT hK0
      calc
        T * K * ODESourceBranches.mass z ≤ T * K * (cq * Bs) :=
          mul_le_mul_of_nonneg_left hMassB hTK
        _ = cq * (T * K) * Bs := by ring
    calc
      _ ≤ ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (b (v i)) T‖ +
          ‖(U 0 (sol 0) T + ∑ i, ω i • U (v i) (bv i) T) - y‖ := norm_add_le _ _
      _ ≤ ζ * Bs + T * K * ODESourceBranches.mass z := add_le_add hCert hTargetErr
      _ ≤ ζ * Bs + cq * (T * K) * Bs := add_le_add le_rfl hMassK
      _ = (ζ + cq * (T * K)) * Bs := by ring
  have hErrBudget : (ζ + cq * (T * K)) * Bs ≤ ε * Bs / (2000 * gbar) := by
    have h := mul_le_mul_of_nonneg_right hBudget hBs0
    calc
      (ζ + cq * (T * K)) * Bs ≤ ε / (2000 * gbar) * Bs := h
      _ = ε * Bs / (2000 * gbar) := by ring
  obtain ⟨hy, hBy, hDir⟩ := Sampling.target_budget (sol T) y Bs gbar ε _ hg hε hεOne
    hTarget hB hErr hErrBudget
  have hNorm : ‖y‖ ≤ ODESourceBranches.mass z :=
    nodeTarget_norm_le Gs hGsAcc hT M v (sol 0) bv ω
  have hz : 0 < ODESourceBranches.mass z := ODESourceBranches.mass_pos_of_solution z y hy hNorm
  have hBudget' : ODESourceBranches.mass z ≤ ratio g * ‖y‖ := by
    have hcq0 : 0 ≤ cq := by linarith
    calc
      ODESourceBranches.mass z ≤ cq * Bs := hMassB
      _ ≤ cq * (2 * gbar * ‖y‖) := mul_le_mul_of_nonneg_left hBy hcq0
      _ = ratio g * ‖y‖ := by rw [hgdef]; unfold ratio; ring
  -- Hypotheses of the released actual-source certificate.
  have hJph : ∀ a, (Compiled.phased (J x) (phases ω) a)† ∘L
      Compiled.phased (J x) (phases ω) a = 1 :=
    phased_isometry (J x) (hJ x) ω
  have hPrep := phased_prepares (J x) (sol 0) bv ω seed hLoad₀ hLoad
  have hSim : ‖pN.eval x ∘L E - E ∘L WeightedClock.diagonal
      (fun a' : Option (Fin m) × Index D T g ε =>
        TimeDependentODE.Select.branchEvolution D hM (nodeTable D T g ε m) (durationTable T v) x
          (a'.1, a'.2))‖ ≤ ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
    have hDiag : WeightedClock.diagonal
        (fun a' : Option (Fin m) × Index D T g ε =>
          TimeDependentODE.Select.branchEvolution D hM (nodeTable D T g ε m) (durationTable T v)
            x (a'.1, a'.2)) = 1 := by
      simp only [hOne]
      exact WeightedClock.diagonal_one
    rw [hDiag, MultiOracleCircuit.Program.eval_identity, sub_eq_zero.mpr, norm_zero]
    · exact hν.le
    · rfl
  have hLCHS : ∀ a', ‖(∑ i, lchsCoefficients D T g ε i •
      TimeDependentODE.Select.branchEvolution D hM (nodeTable D T g ε m) (durationTable T v) x
        (a', i)) - family D hM T v x a' (-Complex.I)‖ ≤
          2 * ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) := by
    intro a'
    have hsum : (∑ i, lchsCoefficients D T g ε i •
        TimeDependentODE.Select.branchEvolution D hM (nodeTable D T g ε m) (durationTable T v) x
          (a', i)) =
          ∑ j, GaussianLCHS.coefficients (lipschitz D T) (ratio g) (accuracy ε) j •
            family D hM T v x a'
              (GaussianLCHS.nodes (lipschitz D T) (ratio g) (accuracy ε) j : ℂ) := by
      simp only [branchEvolution_eq_family]
      exact Sampling.padded_sum _ _ _
    rw [hsum]
    exact hApprox (x, a')
  have hQuad : ‖(∑ a', family D hM T v x a' (-Complex.I) (z a')) - y‖ ≤
      ImprovedODEQueryBudget.precision (ratio g) (accuracy ε) * ODESourceBranches.mass z := by
    have hsum : (∑ a', family D hM T v x a' (-Complex.I) (z a')) = y := by
      apply Finset.sum_congr rfl
      intro a' _
      rw [family_neg_I]
    rw [hsum, sub_self, norm_zero]
    exact mul_nonneg hν.le (ODESourceBranches.mass_nonneg z)
  have hCertS : ODEActualSourceError.Certificate E z c
      (Compiled.phased (J x) (phases ω)) (pN.eval x) seed y (ratio g) (accuracy ε) :=
    ODEActualSourceError.actual_source_certificate E hEiso z c hc
      (Compiled.phased (J x) (phases ω)) hJph seed hSeed hPrep (pN.eval x)
      (pN.eval_unitary (Native.matrixOracle_unitary D m d) x)
      (fun a' i => TimeDependentODE.Select.branchEvolution D hM (nodeTable D T g ε m)
        (durationTable T v) x (a', i))
      (fun a' => family D hM T v x a' (-Complex.I)) y (ratio g) (accuracy ε)
      hy hg' hε' hε'Half hNorm hBudget' hSim hLCHS hQuad
  -- The released primitive trial certificate, then the solution direction.
  have hTrial := Native.trial_certificate D hM i0 m d pN Pw hPw J hJ (phases ω)
    (phases_norm ω) E hEiso z c hcpos seed y hSeed
    (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio g) (accuracy ε))
    (ImprovedODEQueryBudget.logBudget (ratio g) (accuracy ε)) (ratio g) (accuracy ε) hg' x
    hz hW hCertS hq hSeedUnit hOutput
  have hFinal := retarget (η' := ε / 500) hTrial hDir (by unfold accuracy; linarith)
  exact ODECompleteTrial.of_trialCertificate
    (fun j => (q j).eval_unitary hOracle x) hε.le hTarget hFinal

/-- A per-trial matrix budget `Qt` gives the four-attempt budget `4 Qt`. -/
theorem budget_of_trial (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Qt : ℝ)
    (h : PropagatedTrialOutcome D hM etaH etaD T gbar cq ε v ω Pw J seed Qt) :
    PropagatedBudgetOutcome D hM etaH etaD T gbar cq ε v ω Pw J seed (4 * Qt) := by
  obtain ⟨d, E, hE, q, hU, hCost, hC⟩ := h
  refine ⟨d, E, hE, q, hU, fun x G b sol U βG δG ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    h14 => ?_⟩
  have hFull := hC x G b sol U βG δG ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  exact ⟨hFull, ODERepeatProtocol.fourTrials_worstCost_le q _ hFull.trial.cutoff_pos _
    hFull.trial.seed_unit _ hFull.trial.output_isometry
    (ODESourceQueryBudget.matrixWeight (fun _ => 1)) Qt (fun j _ => hCost j)⟩

/-- **Theorem `ode:thm:time` with the general source interface at zero time or with a known
zero generator** (two counted source interfaces). If `T = 0` or the public energy bounds give
`η_H + R η_D = 0`, the released public trial family with the identity SELECT satisfies
`PropagatedBudgetOutcome` with `Q = 0`: the released complete certificate for every valid
instance, with no matrix query in any history. The mesh conditions and the column promises are
not needed. -/
theorem zero_propagated_solver (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hZero : T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    PropagatedBudgetOutcome D hM etaH etaD T gbar cq ε v ω Pw J seed 0 := by
  have h := budget_of_trial D hM etaH etaD T gbar cq ε v ω Pw J seed 0
    (zero_core D hM etaH etaD T gbar cq ε v ω hH hDiss hT hZero hg hcq hε hεOne hv hrH hrD hPSD
      Pw hPw J hJ seed hSeed)
  rwa [mul_zero] at h

/-! ### The actual oracles `P_w`, `U_load`, `P_w†` -/

/-- **The released outcome over the actual oracles with a matrix-query budget**:
`GeneralSourceODE.Outcome` in which the four-attempt protocol makes at most `Q` matrix queries
in every history. -/
def BudgetOutcome (D : Data (X × Fin M) n Z s) (etaH etaD T gbar cq ε : ℝ) {m : ℕ}
    (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Q : ℝ) : Prop :=
  ∃ (d : ℕ) (t : ODERepeatProtocol.TrialFamily
      (Oracles.actualOracle (ι := Index D T (cq * gbar) ε) D m d Pw J) (EuclideanSpace ℂ n)),
    t.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
    (∀ j y, IsUnitary ((t.circuit j).eval y)) ∧
    ∀ (x : X) (G : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b sol : ℝ → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (βG δG ζ : ℝ), 0 ≤ βG →
      (∀ u ∈ Icc 0 T, Accretive (G u)) →
      (∀ u ∈ Icc 0 T, ∀ w ∈ Icc 0 T, ‖G u - G w‖ ≤ βG * |u - w|) →
      (∀ r : Fin M, ‖G ((r : ℕ) * T / M) -
        SparseStateOverlap.matrixOperator (D.matrix (x, r))‖ ≤ δG) →
      ContinuousOn b (Icc 0 T) →
      SolvesODE G b sol 0 T →
      IsPropagator G U T →
      Compiled.WeightPrep (Pw x) (sources (sol 0) (fun i => b (v i)) ω) →
      (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → b (v i) ≠ 0 → J x (some i) seed =
        ODEStateNormalization.unitDirection (b (v i))) →
      ODESourceBranches.mass (sources (sol 0) (fun i => b (v i)) ω) ≤
        cq * sourceScale sol b T →
      ‖(∫ u in (0 : ℝ)..T, U u (b u) T) - ∑ i, ω i • U (v i) (b (v i)) T‖ ≤
        ζ * sourceScale sol b T →
      sol T ≠ 0 →
      sourceScale sol b T ≤ gbar * ‖sol T‖ →
      ζ + cq * (T * (βG * (T / M) + δG)) ≤ ε / (2000 * gbar) →
      Oracles.ActualCertificate (ODERepeatProtocol.Protocol.repeatTrials t 4) x (sol T) (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))
        (ratio (cq * gbar)) ε ∧
      ((ODERepeatProtocol.Protocol.repeatTrials t 4).worstCost Oracles.matrixCalls : ℝ) ≤ Q

omit [DecidableEq Z] in
/-- Forgetting the budget gives the released outcome over the actual oracles. -/
theorem outcome_of_budget (D : Data (X × Fin M) n Z s) (etaH etaD T gbar cq ε : ℝ) {m : ℕ}
    (v : Fin m → ℝ) (ω : Fin m → ℂ) (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (Q : ℝ)
    (h : BudgetOutcome D etaH etaD T gbar cq ε v ω Pw J seed Q) :
    Outcome D etaH etaD T gbar cq ε v ω Pw J seed := by
  obtain ⟨d, t, hch, hU, hC⟩ := h
  exact ⟨d, t, hch, hU, fun x G b sol U βG δG ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    h15 => (hC x G b sol U βG δG ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15).1⟩

omit [DecidableEq Z] in
/-- The released outcome over the actual oracles satisfies `BudgetOutcome` with `Q` the
released worst-case bound `1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)`, `g' = 2 c_q ḡ`. -/
theorem budget_of_outcome (D : Data (X × Fin M) n Z s) (etaH etaD T gbar cq ε : ℝ) {m : ℕ}
    (v : Fin m → ℝ) (ω : Fin m → ℂ) (Pw : X → Weights.LabelOp (Option (Fin m)))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) (h : Outcome D etaH etaD T gbar cq ε v ω Pw J seed) :
    BudgetOutcome D etaH etaD T gbar cq ε v ω Pw J seed
      (1274019840 * ratio (cq * gbar) * ImprovedODEQueryBudget.queryShape (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
        (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))) := by
  obtain ⟨d, t, hch, hU, hC⟩ := h
  refine ⟨d, t, hch, hU, fun x G b sol U βG δG ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    h15 => ?_⟩
  have hc := hC x G b sol U βG δG ζ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  exact ⟨hc, hc.matrix_queries⟩

set_option maxHeartbeats 4000000 in
/-- **From the two counted source interfaces to the actual oracles, with the matrix budget.**
For `T ≥ 0`, a public trial family over the two composite interfaces with at most `Qt` matrix
queries per trial and the released complete certificate gives, after substituting `P_w`, `U_load`
and the public phases for the preparation interface and `P_w†` for the unpreparation interface,
the released outcome over the actual oracles with at most `4 Qt` matrix queries in every
history; Duhamel's formula turns the certificate on the propagated vector integral into the one
on the propagated source sum. -/
theorem actual_of_trial (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hT : 0 ≤ T) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq) (hε : 0 < ε) (hεOne : ε ≤ 1)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) (Qt : ℝ)
    (h : PropagatedTrialOutcome D hM etaH etaD T gbar cq ε v ω Pw J seed Qt) :
    BudgetOutcome D etaH etaD T gbar cq ε v ω Pw J seed (4 * Qt) := by
  obtain ⟨d, E, hE, q, _hUnit, hQt, hCert⟩ := h
  have hg1 : 1 ≤ ratio (cq * gbar) := by
    unfold ratio
    nlinarith
  obtain ⟨hMpos, -, -⟩ := ODEGroverAverage.chosenIterations_bounds (ratio (cq * gbar)) hg1
  have hcpos : 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D T (cq * gbar) ε) := by
    have hL : 0 ≤ lipschitz D T :=
      mul_nonneg hT (mul_nonneg (Nat.cast_nonneg s) D.scale_pos.le)
    have hε' : 0 < accuracy ε := by unfold accuracy; linarith
    have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
    obtain ⟨-, -, hMass, -⟩ := GaussianLCHS.table_certificate
      (fun y : X × Option (Fin m) => family D hM T v y.1 y.2)
      (fun y z => family_analyticAt D hM T v y.1 y.2 z)
      (fun y z hz => family_norm_le_one D hM T hT v hPSD y.1 y.2 z hz)
      (lipschitz D T) hL (fun y k l => family_lipschitz D hM T hT v y.1 y.2 k l)
      (ratio (cq * gbar)) (accuracy ε) hg1 hε' hε'One
    have hc : ODECoherentLCU.coefficientMass (lchsCoefficients D T (cq * gbar) ε) = 3 :=
      ODECoefficientPadding.coefficientMass_eq _ 3 hMass
    rw [hc]
    norm_num
  -- The public seed and output flag on the primitive workspace.
  have hψ := Native.seed_unit D hM (Sum.inr false) m d E hE
    (lchsCoefficients D T (cq * gbar) ε) hcpos seed hSeed
  have hF := Native.output_isometry D hM (Sum.inr false) m d E hE
    (lchsCoefficients D T (cq * gbar) ε) hcpos
  -- The trial family over the actual oracles.
  let q' := Oracles.actualTrials D m d Pw J (phases ω) (phases_norm ω) q
  have hEval : ∀ j x, (q' j).eval x = (q j).eval x := fun j x =>
    MultiOracleCircuit.Program.eval_substitute (q j) _
      (Oracles.implementation_eval D m d Pw J (phases ω) (phases_norm ω)) x
  have hActual := Oracles.actualOracle_unitary (ι := Index D T (cq * gbar) ε) D m d hPw hJ
  have hCost : ∀ (w : Query ⊕ SourceCall → ℕ) (j : ℕ),
      (q' j).cost w = (q j).cost (fun l =>
        (Oracles.implementation D m d Pw J (phases ω) (phases_norm ω) l).cost w) :=
    fun w j => MultiOracleCircuit.Program.cost_substitute (q j) _ w
  have hMatrix : ∀ j, (q' j).cost Oracles.matrixCalls =
      (q j).cost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) := fun j => by
    rw [hCost]
    exact congrArg (q j).cost (funext (Oracles.implementation_matrix D m d Pw J _ _))
  refine ⟨d, ODERepeatProtocol.ofCircuits q'
    (ODEGroverAverage.chosenIterations (ratio (cq * gbar))) hMpos _ hψ _ hF, rfl,
    fun j y => (q' j.val).eval_unitary hActual y, ?_⟩
  intro x G b sol U βG δG ζ hβG hG hGLip hGs hbc hsol hU hW hLoad₀ hLoad hMassB hInt
    hTarget hB hBudget
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
  have hD := duhamel hT hU hG _ hΛ hbc hsol
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (b (v i)) T‖ ≤
      ζ * sourceScale sol b T := by
    rw [← hD]
    exact hInt
  have hC := hCert x G b sol U βG δG ζ hβG hG hGLip hGs hsol hU hW hLoad₀ hLoad hMassB
    hCertP hTarget hB hBudget
  refine ⟨Oracles.actual_certificate hC q' hMpos hψ hF (fun j => hEval j x) hMatrix
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (Oracles.implementation_weight D m d Pw J _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (Oracles.implementation_load D m d Pw J _ _)))
    (fun j => by
      rw [hCost]
      exact congrArg (q j).cost (funext (Oracles.implementation_unweight D m d Pw J _ _)))
    (fun j => by
      rw [hCost, funext (Oracles.implementation_source D m d Pw J _ _), Oracles.cost_add,
        NativeHermitianDilation.cost_scale]), ?_⟩
  exact ODERepeatProtocol.fourTrials_worstCost_le q' _ hMpos _ hψ _ hF Oracles.matrixCalls Qt
    (fun j _ => by rw [hMatrix j]; exact hQt j)

set_option maxHeartbeats 4000000 in
/-- **Theorem `ode:thm:time` with the general source interface at zero time or with a known
zero generator, on the actual oracles.** If `T = 0` or `η_H + R η_D = 0`, one public family of
trial circuits over the coherent sampled-time matrix oracle and the supplied `P_w`, `U_load` and
`P_w†` satisfies `BudgetOutcome` with `Q = 0`: for every valid instance, four fresh trials give
the released guarantees (success at least `175/256 > 2/3`, conditional trace distance at most
`ε`, at most `40 g'` calls of each of `P_w`, `U_load` and `P_w†`, `g' = 2 c_q ḡ`) and make no
matrix query in any history. The mesh conditions and the column promises are not needed. -/
theorem zero_solver (D : Data (X × Fin M) n Z s) (hM : 0 < M)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (hH : 0 ≤ etaH) (hDiss : 0 ≤ etaD) (hT : 0 ≤ T)
    (hZero : T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0) (hg : 1 ≤ gbar) (hcq : 1 ≤ cq)
    (hε : 0 < ε) (hεOne : ε ≤ 1) (hv : ∀ i, v i ∈ Icc 0 T)
    (hrH : ∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2)
    (hrD : ∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2)
    (hPSD : ∀ (y : X × Fin M) (w : EuclideanSpace ℂ n), 0 ≤ (inner ℂ w
      (SparseStateOverlap.matrixOperator (ODEMatrixEnergy.dissipativePart (D.matrix y)) w)).re)
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    BudgetOutcome D etaH etaD T gbar cq ε v ω Pw J seed 0 := by
  have h := actual_of_trial D hM etaH etaD T gbar cq ε v ω hT hg hcq hε hεOne hPSD Pw hPw J hJ
    seed hSeed 0 (zero_core D hM etaH etaD T gbar cq ε v ω hH hDiss hT hZero hg hcq hε hεOne hv
      hrH hrD hPSD Pw hPw J hJ seed hSeed)
  rwa [mul_zero] at h

set_option maxHeartbeats 4000000 in
/-- **Theorem `ode:thm:time` with the general source interface for every `T ≥ 0`.** Under the
hypotheses of the released `GeneralSourceODE.solver` with `0 ≤ T` in place of `0 < T` and
without the positivity of `ρ = η_H + R η_D`, `BudgetOutcome` holds with
`Q = if T = 0 ∨ ρ = 0 then 0 else 1274019840 g' (√s Θ + √(s Θ ℓ) + ℓ)`, `g' = 2 c_q ḡ`. -/
theorem solver_nonneg (D : Data (X × Fin M) n Z s) (hM : 0 < M)
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
    BudgetOutcome D etaH etaD T gbar cq ε v ω Pw J seed
      (if T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0 then 0 else
        1274019840 * ratio (cq * gbar) * ImprovedODEQueryBudget.queryShape (s : ℝ)
          (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) (ratio (cq * gbar)) (accuracy ε))
          (ImprovedODEQueryBudget.logBudget (ratio (cq * gbar)) (accuracy ε))) := by
  by_cases hZero : T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0
  · rw [if_pos hZero]
    exact zero_solver D hM etaH etaD T gbar cq ε v ω hH hDiss hT hZero hg hcq hε hεOne hv hrH
      hrD hPSD Pw hPw J hJ seed hSeed
  · rw [if_neg hZero]
    have hg' : 1 ≤ ratio (cq * gbar) := by unfold ratio; nlinarith
    have hε' : 0 < accuracy ε := by unfold accuracy; linarith
    have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
    have hR : 0 ≤ radius (cq * gbar) ε :=
      ImprovedODEQueryBudget.radius_nonneg _ _ hg' hε' hε'One
    have hTpos : 0 < T := lt_of_le_of_ne hT (fun h => hZero (Or.inl h.symm))
    have hρ : 0 < etaH + radius (cq * gbar) ε * etaD :=
      lt_of_le_of_ne (add_nonneg hH (mul_nonneg hR hDiss)) (fun h => hZero (Or.inr h.symm))
    exact budget_of_outcome D etaH etaD T gbar cq ε v ω Pw J seed
      (solver D hM etaH etaD T gbar cq ε v ω hH hDiss hTpos hg hcq hε hεOne hρ hMesh hCayley hv
        hrH hcH hrD hcD hPSD Pw hPw J hJ seed hSeed)

end

end SparseHamiltonian.GeneralSourceExtensions
