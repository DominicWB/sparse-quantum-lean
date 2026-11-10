import ManuscriptConformance.TimeLoaderColumns
import ManuscriptConformance.ActualRuns

/-!
# The actual runs of Theorem `ode:thm:time` with a loader specified on its clean columns (item D1)

`ManuscriptConformance.ode_thm_time_actual` adds to `ode_thm_time`, for exact source preparations,
the accuracy of every actual successful trial and history (`TrialsClose`, `HistoriesClose`). Here
the same is proved for the protocol of `ode_thm_time_columns`, over `P_w`, a unitary loader `Lo`
on the whole branch register specified only on its clean columns, and `P_w†`.

The trials of that protocol and those of the label-controlled family `columnLoader Lo` agree on
the public seed, but not as operators. So the transfer of `ode_thm_time_actual` (equal
evaluations, `trialsClose_congr`) is replaced by its seed form:

* `MeshOracles.columns_seed_eval`: on the public seed, the trials over `P_w`, `Lo`, `P_w†` have the
  outputs of the public trial family of any label-controlled `J` with
  `Lo (P_w ⊗ 1)|seed state⟩ = loader J (P_w ⊗ 1)|seed state⟩`;
* `trialsClose_congr_seed`: `TrialsClose` depends on a trial family only through its outputs on
  the seed;
* `MeshOracles.columns_trialsClose`: so `TrialsClose` transfers from the public trial family of
  `J` to the trials over `P_w`, `Lo`, `P_w†`;
* `ode_thm_time_actual_columns`: the statement of `ode_thm_time_actual` for this protocol. It has
  `HeraldedOutput`, `TrialsClose`, `HistoriesClose`, and the matrix-query and source-call bounds
  with the constant of `ode_thm_time_actual`.

Scope: the exact case of item D1. The approximate-preparation forms keep the label-controlled
loader.
-/

set_option autoImplicit false

namespace ManuscriptConformance

open ContinuousLinearMap SparseHamiltonian OracleCircuit
open scoped InnerProduct InnerProductSpace

section Seed

variable {E K X L L' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **`TrialsClose` depends only on the outputs on the seed**: two program families whose trials
have the same output on the seed `ψ` at `x` have the same selected outputs. This is the seed form
of `trialsClose_congr`. -/
theorem trialsClose_congr_seed {O : L → X → K →L[ℂ] K} {O' : L' → X → K →L[ℂ] K}
    {q : ℕ → MultiOracleCircuit.Program O} {q' : ℕ → MultiOracleCircuit.Program O'} {M : ℕ}
    (hM : 0 < M) {ψ : K} (hψ : ‖ψ‖ = 1) {F : E →L[ℂ] K} (hF : F† ∘L F = 1) {x : X}
    {target : E} {ε : ℝ} (hEval : ∀ j, (q' j).eval x ψ = (q j).eval x ψ)
    (h : TrialsClose (ODERepeatProtocol.ofCircuits q M hM ψ hψ F hF) x target ε) :
    TrialsClose (ODERepeatProtocol.ofCircuits q' M hM ψ hψ F hF) x target ε := by
  intro j hne
  have e : (ODERepeatProtocol.ofCircuits q' M hM ψ hψ F hF).amplitude x j =
      (ODERepeatProtocol.ofCircuits q M hM ψ hψ F hF).amplitude x j := by
    change (F†) ((q' j.val).eval x ψ) = (F†) ((q j.val).eval x ψ)
    rw [hEval j.val]
  have e' : (ODERepeatProtocol.ofCircuits q' M hM ψ hψ F hF).outputDirection x j =
      (ODERepeatProtocol.ofCircuits q M hM ψ hψ F hF).outputDirection x j := by
    unfold ODERepeatProtocol.TrialFamily.outputDirection
    rw [e]
  rw [e] at hne
  rw [e']
  exact h j hne

end Seed

end ManuscriptConformance

namespace SparseHamiltonian.GeneralSourceExtensions.MeshOracles

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding
open SparseHamiltonian.GeneralSourceODE
open scoped InnerProduct BigOperators
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {ι X n Z : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s M m : ℕ}

/-- **On the public seed, the trials over `P_w`, `Lo`, `P_w†` have the outputs of the public trial
family of a label-controlled `J`**, when `Lo` and `loader J` agree on the seed branch state after
`P_w`. This is the evaluation step of `columns_certificate`. -/
theorem columns_seed_eval (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m N d : ℕ)
    (p : MultiOracleCircuit.Program (MeshNative.matrixOracle (ι := ι) D m N d))
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (hLo : ∀ x, IsUnitary (Lo x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a)) (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (E : Native.SourceSpace ι n m →L[ℂ] MeshNative.MatrixSpace ι n Z m M N d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1)
    (x : X)
    (hagree : Lo x (Weights.act (Pw x)
        (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed)) =
      Weights.loader (J x) (Weights.act (Pw x)
        (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed))) (j : ℕ) :
    (actualTrialsL D m N d Pw Lo φ hφ
        (MeshNative.publicTrialsS D hM i0 m N d p (Compiled.sourceFamilyL Pw Lo φ) E hE c seed
          hSeed hOutput) j).eval x
        (MeshNative.input D hM i0 m N d
          (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)) =
      (MeshNative.publicTrials D hM i0 m N d p Pw J φ E hE c seed hSeed hOutput j).eval x
        (MeshNative.input D hM i0 m N d
          (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)) := by
  rw [MeshNative.publicTrials_eq_publicTrialsS]
  have hfalse : Compiled.sourceFamilyL (ι := ι) Pw Lo φ false x
      (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed) =
      Native.sourceFamily (ι := ι) Pw J φ false x
        (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed) := by
    rw [Compiled.sourceFamilyL_false, Native.sourceFamily, Compiled.sourceFamily_false]
    unfold Compiled.prepL Compiled.prep
    simp only [comp_apply]
    rw [hagree]
  have hEval : (actualTrialsL D m N d Pw Lo φ hφ
      (MeshNative.publicTrialsS D hM i0 m N d p (Compiled.sourceFamilyL Pw Lo φ) E hE c seed hSeed
        hOutput) j).eval x =
      (MeshNative.publicTrialsS D hM i0 m N d p (Compiled.sourceFamilyL Pw Lo φ) E hE c seed hSeed
        hOutput j).eval x :=
    MultiOracleCircuit.Program.eval_substitute _ _ (implementationL_eval D m N d Pw Lo φ hφ) x
  rw [hEval]
  have h := MeshNative.publicTrialsS_seed_congr D hM i0 m N d p (Compiled.sourceFamilyL Pw Lo φ)
    (Native.sourceFamily Pw J φ)
    (Compiled.sourceFamilyL_unitary hPw hLo hφ) (Compiled.sourceFamily_unitary hPw hJ hφ)
    E hE c seed hSeed hOutput x
    ((Compiled.sourceFamilyL_true Pw Lo φ x).trans (Compiled.sourceFamily_true Pw J φ x).symm)
    hfalse j
  convert h using 2

/-- **`TrialsClose` transfers from the public trial family of a label-controlled `J` to the trials
over `P_w`, `Lo`, `P_w†`**, when `Lo` and `loader J` agree on the seed branch state after `P_w`
(`columns_seed_eval`, `ManuscriptConformance.trialsClose_congr_seed`). -/
theorem columns_trialsClose (D : Data (X × Fin M) n Z s) (hM : 0 < M) (i0 : ι) (m N d : ℕ)
    (p : MultiOracleCircuit.Program (MeshNative.matrixOracle (ι := ι) D m N d))
    (Pw : X → Weights.LabelOp (Option (Fin m))) (hPw : ∀ x, IsUnitary (Pw x))
    (Lo : X → Native.SourceSpace ι n m →L[ℂ] Native.SourceSpace ι n m)
    (hLo : ∀ x, IsUnitary (Lo x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a)) (φ : Option (Fin m) → ℂ) (hφ : ∀ a, ‖φ a‖ = 1)
    (E : Native.SourceSpace ι n m →L[ℂ] MeshNative.MatrixSpace ι n Z m M N d) (hE : E† ∘L E = 1)
    (c : ι → ℂ) (seed : EuclideanSpace ℂ n)
    (hSeed : ‖ODECompiledSource.seed E (Compiled.seedCoefficients c) seed‖ = 1)
    (hOutput : (ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      ODECompiledSource.output E (Compiled.seedCoefficients c) = 1)
    (x : X) {Mc : ℕ} (hMc : 0 < Mc) {target : EuclideanSpace ℂ n} {ε : ℝ}
    (hψ : ‖MeshNative.input D hM i0 m N d
      (ODECompiledSource.seed E (Compiled.seedCoefficients c) seed)‖ = 1)
    (hF : (MeshNative.input D hM i0 m N d ∘L
        ODECompiledSource.output E (Compiled.seedCoefficients c))† ∘L
      (MeshNative.input D hM i0 m N d ∘L
        ODECompiledSource.output E (Compiled.seedCoefficients c)) = 1)
    (hagree : Lo x (Weights.act (Pw x)
        (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed)) =
      Weights.loader (J x) (Weights.act (Pw x)
        (ODEJointLCU.coefficientInput (Compiled.seedCoefficients c) seed)))
    (h : ManuscriptConformance.TrialsClose (ODERepeatProtocol.ofCircuits
      (MeshNative.publicTrials D hM i0 m N d p Pw J φ E hE c seed hSeed hOutput) Mc hMc _ hψ _ hF)
      x target ε) :
    ManuscriptConformance.TrialsClose (ODERepeatProtocol.ofCircuits
      (actualTrialsL D m N d Pw Lo φ hφ
        (MeshNative.publicTrialsS D hM i0 m N d p (Compiled.sourceFamilyL Pw Lo φ) E hE c seed
          hSeed hOutput)) Mc hMc _ hψ _ hF) x target ε := by
  apply ManuscriptConformance.trialsClose_congr_seed hMc hψ hF _ h
  intro j
  convert columns_seed_eval D hM i0 m N d p Pw hPw Lo hLo J hJ φ hφ E hE c seed hSeed hOutput x
    hagree j using 2

end

end SparseHamiltonian.GeneralSourceExtensions.MeshOracles

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Set
open SparseHamiltonian.GeneralSourceExtensions
open scoped InnerProduct InnerProductSpace

set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

universe u v w

set_option maxHeartbeats 16000000 in
/-- **Theorem `ode:thm:time` with the accuracy of the actual successful runs and a loader specified
on its clean columns only (item D1, exact case).** The statement of `ode_thm_time_actual`, with
the label-controlled `U_load` replaced by any unitary `Lo` on the whole branch register, specified
only on the clean columns `|a, τ⟩|seed⟩` of the labels with nonzero source vectors (as in
`ode_thm_time_columns`).

One public trial family `tf` over `MeshOracles.actualOracleL` (the sampled-time matrix oracle on
`N` slots and the supplied `P_w`, `Lo`, `P_w†`) is fixed before the instance. Four fresh trials
satisfy `HeraldedOutput`, with the matrix-query and source-call bounds of `ode_thm_time_actual`.
In addition:

* `TrialsClose`: every actual trial with a nonzero selected output prepares `x(T)/‖x(T)‖` to
  Euclidean error at most `ε` up to a global phase;
* `HistoriesClose`: the same for every positive-probability successful history of
  `repeatTrials tf 4`. -/
theorem ode_thm_time_actual_columns :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s M : ℕ} (D : Data (X × Fin M) n Z s), 0 < M →
        ∀ (t : ℕ → ℝ) (N : ℕ), 0 < N →
        ∀ (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ),
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 1 ≤ gbar → 1 ≤ cq → 0 < ε → ε ≤ 1 →
        TimeDependentExtensions.IsMesh t M T →
        8 * s * ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T) ≤ N →
        3 * (Real.sqrt (2 * (s : ℝ)) *
          ((etaH + TimeDependentODE.radius (cq * gbar) ε * etaD) * T)) ^ 3 ≤
          TimeDependentODE.precision (cq * gbar) ε * (N : ℝ) ^ 2 →
        (∀ i, v i ∈ Icc 0 T) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix y) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ y i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ y j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix y) i j‖ ^ 2 ≤ etaD ^ 2) →
        ∀ (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m))), (∀ x, IsUnitary (Pw x)) →
        ∀ (Lo : X → GeneralSourceODE.Native.SourceSpace
            (TimeDependentODE.Index D T (cq * gbar) ε) n m →L[ℂ]
          GeneralSourceODE.Native.SourceSpace (TimeDependentODE.Index D T (cq * gbar) ε) n m),
        (∀ x, IsUnitary (Lo x)) →
        ∀ seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∃ (d : ℕ) (tf : ODERepeatProtocol.TrialFamily
            (MeshOracles.actualOracleL (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d Pw
              Lo)
            (EuclideanSpace ℂ n)),
          ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ : ℝ),
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces t G →
            RepresentedSampleODE.MildSolution t T b sol U →
            formal_classicalPropagator G t T U →
            GeneralSourceODE.Compiled.WeightPrep (Pw x) (GeneralSourceODE.sources (sol 0) bv ω) →
            (sol 0 ≠ 0 → ∀ τ : TimeDependentODE.Index D T (cq * gbar) ε,
              Lo x (PiLp.single 2 (none, τ) seed) =
                PiLp.single 2 (none, τ) (ODEStateNormalization.unitDirection (sol 0))) →
            (∀ i, ω i ≠ 0 → bv i ≠ 0 → ∀ τ : TimeDependentODE.Index D T (cq * gbar) ε,
              Lo x (PiLp.single 2 (some i, τ) seed) =
                PiLp.single 2 (some i, τ) (ODEStateNormalization.unitDirection (bv i))) →
            ODESourceBranches.mass (GeneralSourceODE.sources (sol 0) bv ω) ≤
              cq * Mesh.meshScale sol b t →
            ‖(∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T) -
                ∑ i, ω i • U (v i) (bv i) T‖ ≤ ζ * Mesh.meshScale sol b t →
            sol T ≠ 0 →
            Mesh.meshScale sol b t ≤ gbar * ‖sol T‖ →
            ζ + cq * (Mesh.sampleError D x t G + 2 * RepresentedSampleODE.dissipativeError D x t G +
                2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (cq * gbar) ε *
                (RepresentedSampleODE.dissipativeError D x t G + Mesh.refinementError D t T N) ≤
              TimeDependentODE.precision (cq * gbar) ε →
            HeraldedOutput (ODERepeatProtocol.Protocol.repeatTrials tf 4) x
              (ODEStateNormalization.unitDirection (sol T)) ε ∧
            TrialsClose tf x (sol T) ε ∧ HistoriesClose tf x (sol T) ε ∧
            ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
              GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤
              C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε)) ∧
            ((ODERepeatProtocol.Protocol.repeatTrials tf 4).worstCost
              GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ C * (cq * gbar) := by
  refine ⟨2548039680, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ s M D hM t N hN etaH etaD T gbar cq ε m v ω hH hDiss hT hg hcq hε hεOne
    hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw Lo hLo seed hSeed
  have hg1 : 1 ≤ TimeDependentODE.ratio (cq * gbar) := by
    unfold TimeDependentODE.ratio
    nlinarith
  -- A label-controlled family with the clean columns of `Lo`; it is not called by the circuits.
  let J := GeneralSourceODE.columnLoader Lo seed (Sum.inr false)
  have hJ : ∀ x a, IsUnitary (J x a) := fun x a => GeneralSourceODE.loadUnitary_unitary _ _
  -- The public outcome of `J`, for every `T ≥ 0`.
  have hPub : RepresentedSampleODE.RobustPublicOutcome D hM t N etaH etaD T gbar cq ε v ω Pw J
      seed := by
    by_cases hZero : T = 0 ∨ etaH + TimeDependentODE.radius (cq * gbar) ε * etaD = 0
    · exact RepresentedSampleODE.robust_zero_core_public D hM t hN etaH etaD T gbar cq ε v ω hH
        hDiss hT hZero hg hcq hε hεOne hmesh hv hrH hrD Pw hPw J hJ seed hSeed
    · push Not at hZero
      have hε' : 0 < TimeDependentODE.accuracy ε := by
        unfold TimeDependentODE.accuracy
        linarith
      have hε'One : TimeDependentODE.accuracy ε ≤ 1 := by
        unfold TimeDependentODE.accuracy
        linarith
      have hR : 0 ≤ TimeDependentODE.radius (cq * gbar) ε :=
        le_trans (by norm_num : (0 : ℝ) ≤ 4)
          (ODEGaussianParameters.radius_ge_four _ _ hg1 hε' hε'One)
      have hT' : 0 < T := lt_of_le_of_ne hT (Ne.symm hZero.1)
      have hρ : 0 < etaH + TimeDependentODE.radius (cq * gbar) ε * etaD :=
        lt_of_le_of_ne (by positivity) (Ne.symm hZero.2)
      exact RepresentedSampleODE.robust_propagated_solver_public D hM t hN etaH etaD T gbar cq ε v
        ω hH hDiss hT' hg hcq hε hεOne hmesh hρ hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed
        hSeed
  obtain ⟨d, E, hE, p, hSeedU, hOut, hCert⟩ := hPub
  obtain ⟨hMpos, -, -⟩ := ODEGroverAverage.chosenIterations_bounds
    (TimeDependentODE.ratio (cq * gbar)) hg1
  have hcpos : 0 < ODECoherentLCU.coefficientMass
      (TimeDependentODE.lchsCoefficients D T (cq * gbar) ε) := by
    rw [Mesh.lchsCoefficients_mass D hT (cq * gbar) ε hg1 hε hεOne]
    norm_num
  have hψ := MeshNative.seed_unit (ι := TimeDependentODE.Index D T (cq * gbar) ε) D hM
    (Sum.inr false) m N d E hE (TimeDependentODE.lchsCoefficients D T (cq * gbar) ε) hcpos seed
    hSeed
  have hF := MeshNative.output_isometry (ι := TimeDependentODE.Index D T (cq * gbar) ε) D hM
    (Sum.inr false) m N d E hE (TimeDependentODE.lchsCoefficients D T (cq * gbar) ε) hcpos
  let q' := MeshOracles.actualTrialsL D m N d Pw Lo (GeneralSourceODE.phases ω)
    (GeneralSourceODE.phases_norm ω)
    (MeshNative.publicTrialsS (ι := TimeDependentODE.Index D T (cq * gbar) ε) D hM (Sum.inr false)
      m N d p (GeneralSourceODE.Compiled.sourceFamilyL Pw Lo (GeneralSourceODE.phases ω)) E hE
      (TimeDependentODE.lchsCoefficients D T (cq * gbar) ε) seed hSeedU hOut)
  refine ⟨d, ODERepeatProtocol.ofCircuits q'
    (ODEGroverAverage.chosenIterations (TimeDependentODE.ratio (cq * gbar))) hMpos _ hψ _ hF,
    fun x G b sol bv U ζ hG hreg hsol hUm hW hCol₀ hCol hMass hInt hTarget hB hB1 hB2 => ?_⟩
  -- The mild solution and the integrated source certificate.
  have hD : sol T - U 0 (sol 0) T =
      ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T := by
    rw [hsol.2]
    abel
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤
      ζ * Mesh.meshScale sol b t := by
    rw [hD]
    exact hInt
  -- The clean columns of `J` are those of `Lo`.
  have hcolJ : ∀ (a : Option (Fin m)) (u : EuclideanSpace ℂ n), u ≠ 0 →
      (∀ τ : TimeDependentODE.Index D T (cq * gbar) ε, Lo x (PiLp.single 2 (a, τ) seed) =
        PiLp.single 2 (a, τ) (ODEStateNormalization.unitDirection u)) →
      J x a seed = ODEStateNormalization.unitDirection u := by
    intro a u hu h
    change GeneralSourceODE.loadUnitary seed ((Lo x (PiLp.single 2 (a, Sum.inr false) seed))
      (a, Sum.inr false)) seed = _
    rw [h (Sum.inr false), PiLp.single_eq_same]
    exact GeneralSourceODE.loadUnitary_apply seed _ hSeed
      (ODEStateNormalization.unitDirection_norm u hu)
  have hLoad₀ : sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0) :=
    fun h0 => hcolJ none (sol 0) h0 (hCol₀ h0)
  have hLoad : ∀ i, ω i ≠ 0 → bv i ≠ 0 → J x (some i) seed =
      ODEStateNormalization.unitDirection (bv i) :=
    fun i hω hb => hcolJ (some i) (bv i) hb (hCol i hω hb)
  -- The certificate of the label-controlled family `J`.
  have hC := hCert x G b sol bv U ζ hG hreg hUm hW hLoad₀ hLoad hMass hCertP hTarget hB
    (RepresentedSampleODE.robustBudget_of_path_int D x hmesh G hG hreg hB1 hB2)
  -- `Lo` and the label-controlled `J` agree on the seed branch state after `P_w`.
  have hagree : Lo x (GeneralSourceODE.Weights.act (Pw x) (ODEJointLCU.coefficientInput
      (GeneralSourceODE.Compiled.seedCoefficients
        (TimeDependentODE.lchsCoefficients D T (cq * gbar) ε)) seed)) =
      GeneralSourceODE.Weights.loader (J x) (GeneralSourceODE.Weights.act (Pw x)
        (ODEJointLCU.coefficientInput
          (GeneralSourceODE.Compiled.seedCoefficients
            (TimeDependentODE.lchsCoefficients D T (cq * gbar) ε)) seed)) := by
    rw [GeneralSourceODE.Weights.act_seedInput]
    apply GeneralSourceODE.Weights.clean_congr
    intro bb hbb
    rw [GeneralSourceODE.Weights.loader_single]
    have hamp : GeneralSourceODE.Weights.amp (Pw x) bb.1 none ≠ 0 := fun h => hbb (by simp [h])
    rw [hW bb.1] at hamp
    have hz : GeneralSourceODE.sources (sol 0) bv ω bb.1 ≠ 0 := by
      intro h0
      apply hamp
      simp [ODESourceBranches.probability, h0]
    rcases bb with ⟨a, τ⟩
    cases a with
    | none =>
        have h0 : sol 0 ≠ 0 := hz
        dsimp only
        rw [hCol₀ h0 τ, hLoad₀ h0]
    | some i =>
        have h0 : ω i • bv i ≠ 0 := hz
        obtain ⟨hω, hb⟩ := smul_ne_zero_iff.mp h0
        dsimp only
        rw [hCol i hω hb τ, hLoad i hω hb]
  have hA := MeshOracles.columns_certificate (ι := TimeDependentODE.Index D T (cq * gbar) ε) D hM
    (Sum.inr false) m N d p Pw hPw Lo hLo J hJ (GeneralSourceODE.phases ω)
    (GeneralSourceODE.phases_norm ω) E hE (TimeDependentODE.lchsCoefficients D T (cq * gbar) ε)
    seed hSeedU hOut x hMpos hψ hF hC hagree
  have hTC := MeshOracles.columns_trialsClose (ι := TimeDependentODE.Index D T (cq * gbar) ε) D
    hM (Sum.inr false) m N d p Pw hPw Lo hLo J hJ (GeneralSourceODE.phases ω)
    (GeneralSourceODE.phases_norm ω) E hE (TimeDependentODE.lchsCoefficients D T (cq * gbar) ε)
    seed hSeedU hOut x hMpos hψ hF hagree (trialsClose_of_certificate hMpos hψ hF hC hε.le)
  refine ⟨⟨hA.success_two_thirds, hA.output_density, hA.conditional_error⟩, hTC,
    historiesClose_of_trialsClose hTC, ?_, ?_⟩
  · refine hA.matrix_queries.trans (le_of_eq ?_)
    rw [ImprovedODEQueryBudget.queryShape, ImprovedODEQueryBudget.theta, time_log_eq]
    unfold TimeDependentODE.ratio
    ring
  · refine hA.source_calls.trans ?_
    unfold TimeDependentODE.ratio
    have : 0 ≤ cq * gbar := by positivity
    nlinarith

end

end ManuscriptConformance
