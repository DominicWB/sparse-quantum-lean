import ManuscriptConformance.LoaderApprox
import ManuscriptConformance.TimeLoaderColumns

/-!
# Theorem `ode:thm:time` with a loader approximately specified on its clean columns (item D1)

`LoaderApprox` proves the stability of the public mesh trial family under a loader that is close to
a label-controlled one on the seed branch state. Here this is combined with the public outcomes of
`TimeLoaderColumns` (every `T ≥ 0`) into the endpoint of `ode:thm:time` with approximate columns.

The loader is any unitary `Lo` on the whole branch register. The hypothesis on it concerns only
the clean subspace `{∑_b α_b |b⟩|seed⟩}`: there `Lo` is within `δ` in operator norm of the
label-controlled reference `loader J` (`CleanClose`). The reference `J` is a label-controlled
family with the released exact columns `J_a |seed⟩ = x₀/‖x₀‖`, resp. `b(v_i)/‖b(v_i)‖`. It need not
be implemented: the trials call `P_w`, `Lo` and `P_w†` only, and `Lo` is arbitrary outside the
clean subspace.

* `cleanState`, `CleanClose`: the clean branch states and the closeness of two operators on them.
* `RegularOutcomeColumnsApprox`, `robust_solver_nonneg_regular_columns_approx`: the solver of
  `RegularOutcomeColumns` (every `T ≥ 0`, integrable pieces, mild solutions, represented samples
  of any sign, the sampling budgets of `ode:thm:time`), for every instance on which `Lo` is
  `CleanClose` to `loader J` within `δ`, `20 g' δ ≤ 1/400` and `20 g' δ ≤ ε/20`
  (`g' = 2 c_q ḡ`). Four fresh trials satisfy `ApproxCertificate`: success at least `2/3`,
  conditional trace distance at most `ε`, and the released counts.
* `ManuscriptConformance.ode_thm_time_columns_approx`: the statement of `ode_thm_time`
  (mixed-output form) with these hypotheses and the condition `40 c_q ḡ δ ≤ min(1/400, ε/20)`.

Scope: approximate columns relative to a label-controlled reference fixed with the other public
data. The forms on temporary work registers (`CleanWorkODE`), with references chosen per instance,
keep the label-controlled loader.
-/

set_option autoImplicit false

namespace SparseHamiltonian.GeneralSourceODE.Weights

variable {σ ι P : Type*} [Fintype σ] [Fintype ι] [NormedAddCommGroup P] [InnerProductSpace ℂ P]

/-- The clean branch state `∑_b α_b |b⟩|v⟩`. -/
def cleanState (α : σ × ι → ℂ) (v : P) : Space σ ι P := WithLp.toLp 2 (fun b => α b • v)

/-- **Two operators are within `δ` on the clean subspace** of the seed `v`: on every clean branch
state `∑_b α_b |b⟩|v⟩` they differ by at most `δ` times its norm. -/
def CleanClose (A B : Space σ ι P →L[ℂ] Space σ ι P) (v : P) (δ : ℝ) : Prop :=
  ∀ α : σ × ι → ℂ, ‖A (cleanState α v) - B (cleanState α v)‖ ≤ δ * ‖cleanState α v‖

end SparseHamiltonian.GeneralSourceODE.Weights

namespace SparseHamiltonian.RepresentedSampleODE

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding Set MeasureTheory
open TimeDependentExtensions SparseHamiltonian.GeneralSourceExtensions
open SparseHamiltonian.TimeDependentODE (Accretive SolvesODE ratio accuracy radius precision
  lipschitz Index lchsCoefficients retarget)
open SparseHamiltonian.GeneralSourceODE (startTime sources phases phases_norm mass_sources
  phased_isometry phased_prepares nodeTable)
open SparseHamiltonian.GeneralSourceExtensions.Mesh (meshScale sampleError refinementError
  IsMeshPropagator)
open scoped BigOperators InnerProduct
set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

variable {X n Z : Type*} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z]
  [DecidableEq Z] {s M : ℕ}

/-- **The guarantee with approximate columns.** One public trial family over the actual oracles
`P_w`, `Lo`, `P_w†` on `N` slots and the coherent sampled-time matrix oracle, chosen before every
unknown instance. Each instance has the hypotheses of `RegularOutcomeColumns`, with two changes:
the exact columns are those of the label-controlled reference `J`, and `Lo` is within `δ` of
`loader J` on the clean subspace (`CleanClose`), with `20 g' δ ≤ 1/400` and `20 g' δ ≤ ε/20`.
Four fresh trials then satisfy `ApproxCertificate`. -/
def RegularOutcomeColumnsApprox (D : Data (X × Fin M) n Z s) (t : ℕ → ℝ) (N : ℕ)
    (etaH etaD T gbar cq ε : ℝ) {m : ℕ} (v : Fin m → ℝ) (ω : Fin m → ℂ)
    (Pw : X → GeneralSourceODE.Weights.LabelOp (Option (Fin m)))
    (Lo : X → GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m)
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (seed : EuclideanSpace ℂ n) : Prop :=
  ∃ (d : ℕ) (tf : ODERepeatProtocol.TrialFamily
      (MeshOracles.actualOracleL (ι := Index D T (cq * gbar) ε) D m N d Pw Lo)
      (EuclideanSpace ℂ n)),
    tf.choices = ODEGroverAverage.chosenIterations (ratio (cq * gbar)) ∧
    (∀ j y, IsUnitary ((tf.circuit j).eval y)) ∧
    ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
      (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
      (bv : Fin m → EuclideanSpace ℂ n)
      (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ δ : ℝ),
      (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), Accretive (G r u)) →
      RegularPieces t G →
      MildSolution t T b sol U →
      IsMeshPropagator G t T U →
      GeneralSourceODE.Compiled.WeightPrep (Pw x) (sources (sol 0) bv ω) →
      (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
      (∀ i, ω i ≠ 0 → bv i ≠ 0 → J x (some i) seed =
        ODEStateNormalization.unitDirection (bv i)) →
      GeneralSourceODE.Weights.CleanClose (Lo x)
        (GeneralSourceODE.Weights.loader (ι := Index D T (cq * gbar) ε) (J x)) seed δ →
      20 * ratio (cq * gbar) * δ ≤ 1 / 400 → 20 * ratio (cq * gbar) * δ ≤ ε / 20 →
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
        (ratio (cq * gbar)) ε

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:time` with the general source interface on a mesh, every `T ≥ 0`, the
certificate on the propagated vector integral, represented samples of any sign, integrable pieces,
mild solutions, and a loader approximately specified on its clean columns (item D1).** Under the
hypotheses of `robust_solver_nonneg_regular_columns`, with a label-controlled reference `J` that
need not be implemented: `RegularOutcomeColumnsApprox`. The public outcome of `J`
(`robust_zero_core_public`, `robust_propagated_solver_public`) gives the trial family and the
certificate of `J`; `MeshOracles.columns_approx_certificate` transfers it to `Lo`, through the
deviation of `Lo` on the seed branch state, which is a clean state of norm `1`. -/
theorem robust_solver_nonneg_regular_columns_approx (D : Data (X × Fin M) n Z s) (hM : 0 < M)
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
    (Lo : X → GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m →L[ℂ]
      GeneralSourceODE.Native.SourceSpace (Index D T (cq * gbar) ε) n m)
    (hLo : ∀ x, IsUnitary (Lo x))
    (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ : ∀ x a, IsUnitary (J x a))
    (seed : EuclideanSpace ℂ n) (hSeed : ‖seed‖ = 1) :
    RegularOutcomeColumnsApprox D t N etaH etaD T gbar cq ε v ω Pw Lo J seed := by
  have hg1 : 1 ≤ ratio (cq * gbar) := by
    unfold ratio
    nlinarith
  -- The public outcome of the reference `J`, for every `T ≥ 0`.
  have hPub : RobustPublicOutcome D hM t N etaH etaD T gbar cq ε v ω Pw J seed := by
    by_cases hZero : T = 0 ∨ etaH + radius (cq * gbar) ε * etaD = 0
    · exact robust_zero_core_public D hM t hN etaH etaD T gbar cq ε v ω hH hDiss hT hZero hg hcq
        hε hεOne hmesh hv hrH hrD Pw hPw J hJ seed hSeed
    · have hε' : 0 < accuracy ε := by unfold accuracy; linarith
      have hε'One : accuracy ε ≤ 1 := by unfold accuracy; linarith
      have hR : 0 ≤ radius (cq * gbar) ε :=
        ImprovedODEQueryBudget.radius_nonneg _ _ hg1 hε' hε'One
      have hTpos : 0 < T := lt_of_le_of_ne hT (fun h => hZero (Or.inl h.symm))
      have hρ : 0 < etaH + radius (cq * gbar) ε * etaD :=
        lt_of_le_of_ne (add_nonneg hH (mul_nonneg hR hDiss)) (fun h => hZero (Or.inr h.symm))
      exact robust_propagated_solver_public D hM t hN etaH etaD T gbar cq ε v ω hH hDiss hTpos hg
        hcq hε hεOne hmesh hρ hClock hCayley hv hrH hcH hrD hcD Pw hPw J hJ seed hSeed
  obtain ⟨d, E, hE, p, hSeedU, hOut, hCert⟩ := hPub
  obtain ⟨hMpos, -, -⟩ := ODEGroverAverage.chosenIterations_bounds (ratio (cq * gbar)) hg1
  have hcpos : 0 < ODECoherentLCU.coefficientMass (lchsCoefficients D T (cq * gbar) ε) := by
    rw [Mesh.lchsCoefficients_mass D hT (cq * gbar) ε hg1 hε hεOne]
    norm_num
  have hψ := MeshNative.seed_unit (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false) m N d E hE
    (lchsCoefficients D T (cq * gbar) ε) hcpos seed hSeed
  have hF := MeshNative.output_isometry (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false) m N d
    E hE (lchsCoefficients D T (cq * gbar) ε) hcpos
  have hActual := MeshOracles.actualOracleL_unitary (ι := Index D T (cq * gbar) ε) D m N d hPw hLo
  refine ⟨d, ODERepeatProtocol.ofCircuits (MeshOracles.actualTrialsL D m N d Pw Lo (phases ω)
      (phases_norm ω) (MeshNative.publicTrialsS (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false)
        m N d p (GeneralSourceODE.Compiled.sourceFamilyL Pw Lo (phases ω)) E hE
        (lchsCoefficients D T (cq * gbar) ε) seed hSeedU hOut))
    (ODEGroverAverage.chosenIterations (ratio (cq * gbar))) hMpos _ hψ _ hF, rfl,
    fun j y => MultiOracleCircuit.Program.eval_unitary _ hActual y, ?_⟩
  intro x G b sol bv U ζ δ hG hreg hsol hUm hW hL0 hL hclean hδ1 hδε hMassB hInt hTarget hB hB1
    hB2
  -- The mild solution and the integrated source certificate.
  have hD : sol T - U 0 (sol 0) T =
      ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1), U u (b r u) T := by
    rw [hsol.2]
    abel
  have hCertP : ‖sol T - U 0 (sol 0) T - ∑ i, ω i • U (v i) (bv i) T‖ ≤
      ζ * meshScale sol b t := by
    rw [hD]
    exact hInt
  -- The certificate of the reference `J`.
  have hC := hCert x G b sol bv U ζ hG hreg hUm hW hL0 hL hMassB hCertP hTarget hB
    (robustBudget_of_path_int D x hmesh G hG hreg hB1 hB2)
  -- `Lo` is within `δ` of `loader J` on the seed branch state, a clean state of norm `1`.
  have hcs : 0 < ODECoherentLCU.coefficientMass
      (GeneralSourceODE.Compiled.seedCoefficients (N := m)
        (lchsCoefficients D T (cq * gbar) ε)) := by
    rw [GeneralSourceODE.Compiled.seedCoefficients_mass]
    exact hcpos
  have hnorm : ‖GeneralSourceODE.Weights.act (ι := Index D T (cq * gbar) ε) (Pw x)
      (ODEJointLCU.coefficientInput (GeneralSourceODE.Compiled.seedCoefficients
        (lchsCoefficients D T (cq * gbar) ε)) seed)‖ = 1 := by
    rw [ODEGroverActual.norm_map_of_isUnitary (GeneralSourceODE.Weights.act_unitary (hPw x)),
      (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr
        (ODEJointLCU.coefficientInput_isometry _ hcs), hSeed]
  have hdev : ‖Lo x (GeneralSourceODE.Weights.act (Pw x) (ODEJointLCU.coefficientInput
      (GeneralSourceODE.Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε)) seed)) -
      GeneralSourceODE.Weights.loader (J x) (GeneralSourceODE.Weights.act (Pw x)
        (ODEJointLCU.coefficientInput
          (GeneralSourceODE.Compiled.seedCoefficients (lchsCoefficients D T (cq * gbar) ε))
          seed))‖ ≤ δ := by
    have e' : GeneralSourceODE.Weights.cleanState
        (fun b' : Option (Fin m) × Index D T (cq * gbar) ε =>
          GeneralSourceODE.Weights.amp (Pw x) b'.1 none *
            (Real.sqrt (ODECoherentLCU.coefficientProbability
              (GeneralSourceODE.Compiled.seedCoefficients (N := m)
                (lchsCoefficients D T (cq * gbar) ε)) (none, b'.2)) : ℂ)) seed =
        GeneralSourceODE.Weights.act (ι := Index D T (cq * gbar) ε) (Pw x)
          (ODEJointLCU.coefficientInput (GeneralSourceODE.Compiled.seedCoefficients
            (lchsCoefficients D T (cq * gbar) ε)) seed) := by
      rw [GeneralSourceODE.Weights.act_seedInput]
      rfl
    have h := hclean (fun b' : Option (Fin m) × Index D T (cq * gbar) ε =>
      GeneralSourceODE.Weights.amp (Pw x) b'.1 none *
        (Real.sqrt (ODECoherentLCU.coefficientProbability
          (GeneralSourceODE.Compiled.seedCoefficients (N := m)
            (lchsCoefficients D T (cq * gbar) ε)) (none, b'.2)) : ℂ))
    rw [e', hnorm, mul_one] at h
    exact h
  exact MeshOracles.columns_approx_certificate (ι := Index D T (cq * gbar) ε) D hM (Sum.inr false) m
    N d p Pw hPw Lo hLo J hJ (phases ω) (phases_norm ω) E hE (lchsCoefficients D T (cq * gbar) ε)
    seed hSeedU hOut x hMpos hψ hF hC hdev hδ1 hδε hTarget

end

end SparseHamiltonian.RepresentedSampleODE

/-! ### The conformance theorem -/

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Set
open SparseHamiltonian.GeneralSourceExtensions
open scoped InnerProduct InnerProductSpace

set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

universe u v w

set_option maxHeartbeats 16000000 in
/-- **Theorem `ode:thm:time` with a loader approximately specified on its clean columns (item
D1).** The statement of `ode_thm_time`, with the label-controlled `U_load` replaced by any unitary
`Lo` on the whole branch register. The hypotheses on `Lo` are:

* a label-controlled reference `J` (unitary, not implemented, fixed with the public data) has the
  released exact columns on the instance;
* `Lo` is within `δ` of `loader J` on the clean subspace `{∑_b α_b |b⟩|seed⟩}` (`CleanClose`),
  and is arbitrary elsewhere;
* `40 c_q ḡ δ ≤ 1/400` and `40 c_q ḡ δ ≤ ε/20`.

One protocol over `MeshOracles.actualOracleL` (the sampled-time matrix oracle on `N` clock slots
and the supplied `P_w`, `Lo`, `P_w†`) is fixed before the instance. It succeeds with probability at
least `2/3` and has conditional output within trace distance `ε` of `x(T)/‖x(T)‖`, with the
matrix-query and source-call bounds of `ode_thm_time` (`C = 2548039680`).

Formal restriction: `formal_classicalPropagator` (as in `ode_thm_time`). Conclusion form:
mixed-output. -/
theorem ode_thm_time_columns_approx :
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
        ∀ (J : X → Option (Fin m) → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
        (∀ x a, IsUnitary (J x a)) →
        ∀ seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∃ (d : ℕ) (A : ODERepeatProtocol.Protocol
            (MeshOracles.actualOracleL (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d Pw
              Lo)
            (EuclideanSpace ℂ n)),
          ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ δ : ℝ),
            (∀ r : Fin M, ∀ u ∈ Icc (t r) (t ((r : ℕ) + 1)), TimeDependentODE.Accretive (G r u)) →
            RepresentedSampleODE.RegularPieces t G →
            RepresentedSampleODE.MildSolution t T b sol U →
            formal_classicalPropagator G t T U →
            GeneralSourceODE.Compiled.WeightPrep (Pw x) (GeneralSourceODE.sources (sol 0) bv ω) →
            (sol 0 ≠ 0 → J x none seed = ODEStateNormalization.unitDirection (sol 0)) →
            (∀ i, ω i ≠ 0 → bv i ≠ 0 →
              J x (some i) seed = ODEStateNormalization.unitDirection (bv i)) →
            GeneralSourceODE.Weights.CleanClose (Lo x)
              (GeneralSourceODE.Weights.loader (ι := TimeDependentODE.Index D T (cq * gbar) ε)
                (J x)) seed δ →
            40 * (cq * gbar) * δ ≤ 1 / 400 → 40 * (cq * gbar) * δ ≤ ε / 20 →
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
            HeraldedOutput A x (ODEStateNormalization.unitDirection (sol T)) ε ∧
            (A.worstCost GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤
              C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε)) ∧
            (A.worstCost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ C * (cq * gbar) := by
  refine ⟨2548039680, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ s M D hM t N hN etaH etaD T gbar cq ε m v ω hH hDiss hT hg hcq hε hεOne
    hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw Lo hLo J hJ seed hSeed
  obtain ⟨d, tf, -, -, hC⟩ := RepresentedSampleODE.robust_solver_nonneg_regular_columns_approx D hM
    t hN etaH etaD T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne hmesh hClock hCayley hv hrH hcH hrD
    hcD Pw hPw Lo hLo J hJ seed hSeed
  refine ⟨d, ODERepeatProtocol.Protocol.repeatTrials tf 4, fun x G b sol bv U ζ δ hG hreg hsol hUm
    hW hL0 hL hclean hδ1 hδε hMass hInt hTarget hB hB1 hB2 => ?_⟩
  have e : 20 * TimeDependentODE.ratio (cq * gbar) * δ = 40 * (cq * gbar) * δ := by
    unfold TimeDependentODE.ratio
    ring
  have hcert := hC x G b sol bv U ζ δ hG hreg hsol hUm hW hL0 hL hclean (e ▸ hδ1) (e ▸ hδε) hMass
    hInt hTarget hB hB1 hB2
  refine ⟨⟨hcert.success_two_thirds, hcert.output_density, hcert.conditional_error⟩, ?_, ?_⟩
  · refine hcert.matrix_queries.trans (le_of_eq ?_)
    rw [ImprovedODEQueryBudget.queryShape, ImprovedODEQueryBudget.theta, time_log_eq]
    unfold TimeDependentODE.ratio
    ring
  · refine hcert.source_calls.trans ?_
    unfold TimeDependentODE.ratio
    have : 0 ≤ cq * gbar := by positivity
    nlinarith

end

end ManuscriptConformance
