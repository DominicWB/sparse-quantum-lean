import ManuscriptConformance.TimeLoaderRuns
import ManuscriptConformance.BranchCertificates

/-!
# Theorem `ode:thm:time` from branch certificates with a loader specified on its clean columns (D1)

`ManuscriptConformance.ode_thm_time_branch` and `ode_thm_time_actual_branch` replace the two
sampling budgets of `ode_thm_time` and `ode_thm_time_actual` by budgets on the integrated branch
errors `E_± = ∑_r ∫ ‖K_{±k}(G_r(u) - G̃_r)‖` of the same represented samples
(`time_budgets_of_branch`), for the same protocols. Here the same is done for the protocols of
`ode_thm_time_columns` and `ode_thm_time_actual_columns` (packages 23 and 24). Their loader is any
unitary `Lo` on the whole branch register, specified only on its clean columns.

* `ode_thm_time_branch_columns`;
* `ode_thm_time_actual_branch_columns`.

The proofs are those of the released branch forms, from the column forms.

Scope: the exact case of item D1. `ode_thm_time_approx_branch` keeps the label-controlled loader.
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit Set
open SparseHamiltonian.GeneralSourceExtensions
open scoped InnerProduct InnerProductSpace

set_option maxRecDepth 4096
set_option synthInstance.maxSize 8192

universe u v w

set_option maxHeartbeats 16000000 in
/-- **Theorem `ode:thm:time` from branch certificates, with a loader specified on its clean columns
only (item D1, exact case).** `ode_thm_time_branch` for the protocol of `ode_thm_time_columns`
(over `P_w`, a unitary loader `Lo` on the whole branch register specified only on its clean
columns, and `P_w†`). It has the guarantee of `ode_thm_time_columns`, and the same conclusions and
counts on every instance whose two sampling budgets are replaced by the budgets on the integrated
branch errors `E_±` of the same represented samples at a branch frequency `kb > 0`
(`time_budgets_of_branch`). -/
theorem ode_thm_time_branch_columns :
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
        ∃ (d : ℕ) (A : ODERepeatProtocol.Protocol
            (MeshOracles.actualOracleL (ι := TimeDependentODE.Index D T (cq * gbar) ε) D m N d Pw
              Lo)
            (EuclideanSpace ℂ n)),
          (∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
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
            HeraldedOutput A x (ODEStateNormalization.unitDirection (sol T)) ε ∧
            (A.worstCost GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤
              C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε)) ∧
            (A.worstCost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ C * (cq * gbar)) ∧
          ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ kb : ℝ), 0 < kb →
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
            ζ + cq * ((1 + 3 / kb) * sampleBranchError D x t G kb / 2 +
                2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (cq * gbar) ε *
                (sampleBranchError D x t G kb / (2 * kb) + Mesh.refinementError D t T N) ≤
              TimeDependentODE.precision (cq * gbar) ε →
            HeraldedOutput A x (ODEStateNormalization.unitDirection (sol T)) ε ∧
            (A.worstCost GeneralSourceODE.Oracles.matrixCalls : ℝ) ≤
              C * (cq * gbar) * (Real.sqrt s * (T * etaH + T * etaD *
                  Real.log (40000 * cq * gbar / ε)) +
                Real.sqrt (s * (T * etaH + T * etaD * Real.log (40000 * cq * gbar / ε)) *
                  Real.log (40000 * cq * gbar / ε)) + Real.log (40000 * cq * gbar / ε)) ∧
            (A.worstCost GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ C * (cq * gbar) := by
  obtain ⟨C, hC, h⟩ := ode_thm_time_columns.{u, v, w}
  refine ⟨C, hC, ?_⟩
  intro X n Z _ _ _ _ _ s M D hM t N hN etaH etaD T gbar cq ε m v ω hH hDiss hT hg hcq hε hεOne
    hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw Lo hLo seed hSeed
  obtain ⟨d, A, hA⟩ := h D hM t N hN etaH etaD T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne hmesh
    hClock hCayley hv hrH hcH hrD hcD Pw hPw Lo hLo seed hSeed
  refine ⟨d, A, hA, fun x G b sol bv U ζ kb hkb hG hreg hsol hUm hW hL0 hL hMass hInt hTarget hB
    hB1 hB2 => ?_⟩
  obtain ⟨c1, c2⟩ := time_budgets_of_branch D x hmesh N G hreg hg hcq hε hεOne hkb hB1 hB2
  exact hA x G b sol bv U ζ hG hreg hsol hUm hW hL0 hL hMass hInt hTarget hB c1 c2

set_option maxHeartbeats 16000000 in
/-- **Theorem `ode:thm:time` with the accuracy of every actual successful run, from branch
certificates, with a loader specified on its clean columns only (item D1, exact case).**
`ode_thm_time_actual_branch` for the trial family of `ode_thm_time_actual_columns`: its guarantee
(heralded output, `TrialsClose`, `HistoriesClose`, counts), and the same conclusions on every
instance with the sampling budgets on the branch errors, as in `ode_thm_time_branch_columns`. -/
theorem ode_thm_time_actual_branch_columns :
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
          (∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
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
              GeneralSourceODE.Oracles.sourceCalls : ℝ) ≤ C * (cq * gbar)) ∧
          ∀ (x : X) (G : Fin M → ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
            (b : Fin M → ℝ → EuclideanSpace ℂ n) (sol : ℝ → EuclideanSpace ℂ n)
            (bv : Fin m → EuclideanSpace ℂ n)
            (U : ℝ → EuclideanSpace ℂ n → ℝ → EuclideanSpace ℂ n) (ζ kb : ℝ), 0 < kb →
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
            ζ + cq * ((1 + 3 / kb) * sampleBranchError D x t G kb / 2 +
                2 * Mesh.refinementError D t T N) ≤ ε / (2000 * gbar) →
            6 * TimeDependentODE.radius (cq * gbar) ε *
                (sampleBranchError D x t G kb / (2 * kb) + Mesh.refinementError D t T N) ≤
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
  obtain ⟨C, hC, h⟩ := ode_thm_time_actual_columns.{u, v, w}
  refine ⟨C, hC, ?_⟩
  intro X n Z _ _ _ _ _ s M D hM t N hN etaH etaD T gbar cq ε m v ω hH hDiss hT hg hcq hε hεOne
    hmesh hClock hCayley hv hrH hcH hrD hcD Pw hPw Lo hLo seed hSeed
  obtain ⟨d, tf, hA⟩ := h D hM t N hN etaH etaD T gbar cq ε v ω hH hDiss hT hg hcq hε hεOne hmesh
    hClock hCayley hv hrH hcH hrD hcD Pw hPw Lo hLo seed hSeed
  refine ⟨d, tf, hA, fun x G b sol bv U ζ kb hkb hG hreg hsol hUm hW hL0 hL hMass hInt hTarget hB
    hB1 hB2 => ?_⟩
  obtain ⟨c1, c2⟩ := time_budgets_of_branch D x hmesh N G hreg hg hcq hε hεOne hkb hB1 hB2
  exact hA x G b sol bv U ζ hG hreg hsol hUm hW hL0 hL hMass hInt hTarget hB c1 c2

end

end ManuscriptConformance
