import ManuscriptConformance.Defs
import ManuscriptConformance.Readout
import ZeroTimeRemarks.ODEConstant

/-!
# Conformance: the dissipative constant-coefficient ODE solver

Theorem `ode:thm:main` in the manuscript's model (Section `ode:sec:main`):

* **Input.** `ẋ = Ax + b`, `x(0) = x₀`, `0 ≤ t ≤ T`, with constant `A` given by native sparse
  data `D` (the matrix `D.matrix x` is the negative generator `G = -A` (eq. `ode:eq:split`);
  `ODEPublicSourceMesh.generator D x` is `A`),
  split as `G = D + iH` (eq. `ode:eq:split`) with `D ⪰ 0` and row and column Euclidean norms of
  `H`, `D` at most `η_H`, `η_D`; the supplied norms `r₀ = ‖x₀‖`, `r_b = ‖b‖`; `x(T) ≠ 0` and
  `ḡ ≥ g = B/‖x(T)‖`, `B = r₀ + T r_b`.
* **Access.** The native value and in-place locator oracles of `D` (inverses included) on clean
  work registers, and the two supplied preparation unitaries `J₀`, `J_b` with
  `J₀ x seed = x₀/‖x₀‖`, `J_b x seed = b/‖b‖` and their controlled forms
  (`ODEFinalNativeSource.physicalOracle`). One protocol, fixed before the instance.
* **Guarantee** (`HeraldedOutput`, `RunsClose`). Four fresh trials of public trial circuits:
  success probability at least `2/3`; the conditional output is some mixture of unit vectors, each
  within Euclidean distance `ε` of `x(T)/‖x(T)‖` up to a global phase (`RunsClose`), so it is a
  density operator within trace distance `ε` of it. That every actual successful trial and history
  of the protocol is within `ε` is `ode_thm_main_actual` (`ActualRuns`: `TrialsClose`,
  `HistoriesClose`); `RunsClose` alone does not say it (`runsClose_diagnostic`).
* **Cost.** Worst case over all histories: matrix queries (`matrixWeight`) and calls of each
  source interface (`sourceWeight`).
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open scoped InnerProduct InnerProductSpace

set_option maxRecDepth 4096
set_option synthInstance.maxSize 4096

universe u v w

section Guarantees

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℂ P] [CompleteSpace P]
  [FiniteDimensional ℂ P]

/-- **A mixture of `ε`-close unit vectors**: the conditional output is some mixture
`∑_a w_a |u_a⟩⟨u_a|` of unit vectors (weights at least zero summing to one), each of positive
weight within Euclidean distance `ε` of `target` up to a global phase. This is a property of the
density operator alone: the decomposition is existential and need not be that of the actual runs,
and a density can have such a decomposition while one of the actual successful runs that produce
it is far from `target` (`runsClose_diagnostic` in `ActualRuns`). The accuracy of the actual
successful trials and histories of the protocol is `TrialsClose` and `HistoriesClose`
(`ActualRuns`; `ode_thm_main_actual`, `ode_thm_time_actual`). -/
def RunsClose (ρ : P →L[ℂ] P) (target : P) (ε : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (wt : ι → ℝ) (out : ι → P),
    ρ = ODEMixedOutput.ensemble wt out ∧ (∀ a, 0 ≤ wt a) ∧ ∑ a, wt a = 1 ∧
      ∀ a, wt a ≠ 0 → ‖out a‖ = 1 ∧ ∃ ω : ℂ, ‖ω‖ = 1 ∧ ‖ω • out a - target‖ ≤ ε

omit [CompleteSpace P] in
/-- A mixture of `ε`-close unit vectors (`RunsClose`) gives a density operator within trace
distance `ε`. -/
theorem traceDistanceLE_of_runsClose {ρ : P →L[ℂ] P} {target : P} {ε : ℝ}
    (h : RunsClose ρ target ε) (ht : ‖target‖ = 1) :
    ODEMixedOutput.IsDensity ρ ∧ TraceDistanceLE ρ target ε := by
  obtain ⟨ι, _, wt, out, rfl, hw, hsum, hclose⟩ := h
  exact ODEMixedOutput.ensemble_trace_distance_le wt out target ε hw hsum
    (fun a ha => (hclose a ha).1) ht (fun a ha => (hclose a ha).2)

variable {K X L : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **The heralded-output guarantee** (`ode:thm:main`): success probability at least `2/3`, and
conditional on success a density operator within trace distance `ε` of `target`. -/
def HeraldedOutput {O : L → X → K →L[ℂ] K} (A : ODERepeatProtocol.Protocol O P) (x : X)
    (target : P) (ε : ℝ) : Prop :=
  2 / 3 ≤ A.successMass x ∧ ODEMixedOutput.IsDensity (A.conditionalDensity x) ∧
    TraceDistanceLE (A.conditionalDensity x) target ε

/-- The package's complete certificate of the four-attempt protocol gives `RunsClose`. -/
theorem runsClose_of_certificate {O : (L ⊕ Bool) → X → K →L[ℂ] K}
    {q : ℕ → MultiOracleCircuit.Program O} {M : ℕ} {ψ : K} {F : P →L[ℂ] K} {x : X}
    {target : P} {s Θ ell g ε : ℝ}
    (h : ODECompleteTrial.Certificate q M ψ F x target s Θ ell g ε) (hε : 0 ≤ ε) :
    RunsClose ((ODECompleteTrial.algorithm h.trial).conditionalDensity x)
      (ODEStateNormalization.unitDirection target) ε := by
  have hMean := ODERepeatProbability.certified_mean_bounds q M ψ F x target s Θ ell g (ε / 500)
    h.unitary_trials h.trial
  refine ⟨Fin 4 × Fin M, inferInstance, ODECompleteTrial.outputWeights q M ψ F x,
    ODECompleteTrial.outputVectors q M ψ F x, h.output_eq_mixture,
    fun a => ODERepeatProbability.conditionalWeight_nonneg _
      (ODERepeatProbability.probability_nonneg q M ψ F x) hMean.1 hMean.2 a,
    ODERepeatProbability.conditionalWeight_sum _ hMean.1 hMean.2, fun a ha => ⟨?_, ?_⟩⟩
  · exact ODEStateNormalization.unitDirection_norm _
      (ODERepeatProbability.conditionalWeight_decoded_ne_zero q M ψ F x a ha)
  · obtain ⟨ω, hω, hd⟩ := h.trial.direction_error a.2.val a.2.isLt
      (ODERepeatProbability.conditionalWeight_decoded_ne_zero q M ψ F x a ha)
    exact ⟨ω, hω, hd.trans (by linarith)⟩

end Guarantees

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:main`** (eqs. `ode:eq:theta`, `ode:eq:main`). Let
`A, b` be constant, `T ≥ 0`, with the native sparse access to `G = -A = D + iH` (row and column
norms of `H`, `D` at most `η_H`, `η_D`, `D ⪰ 0`) and the preparation access `J₀`, `J_b`, with
supplied `r₀ = ‖x₀‖`, `r_b = ‖b‖` and `ḡ`. For `0 < ε ≤ 1/2`, put `ℓ = log(10⁴ ḡ/ε)` and
`Θ = T η_H + T η_D ℓ`. There is one protocol, fixed before the instance (public trial circuits
`q`, cutoff `M`, seed `ψ` and output flag `F`), such that on every instance with `x(T) ≠ 0` and
`B = r₀ + T r_b ≤ ḡ ‖x(T)‖` its four-trial run succeeds with probability at least `2/3`, the
conditional output is a mixture of unit vectors each within Euclidean distance `ε` of
`x(T)/‖x(T)‖` up to a global phase (`RunsClose`; for every actual trial with a nonzero success
branch: `ode_thm_main_actual`) and within trace distance `ε`; it uses at most
`C ḡ (√s Θ + √(s Θ ℓ) + ℓ)` matrix queries and `C ḡ` calls of each source interface in every
history, `C = 1274019840` (no logarithm of `s` or `T`). This is eq. `ode:eq:main` (whose last two
logarithms are `log(ḡ/ε)`), since `log(10⁴ ḡ/ε) ≤ 15 log(ḡ/ε)` for `ḡ ≥ 1`, `ε ≤ 1/2`. Formal
restrictions: exact unitary preparations (summary table); otherwise none (`D ⪰ 0` is
the manuscript's promise, eq. `ode:eq:split`; the instance class is that of the theorem). -/
theorem ode_thm_main :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type u} {n : Type v} {Z : Type w} [Fintype n] [DecidableEq n] [Fintype Z]
        [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : Data X n Z s)
        (etaH etaD T gbar ε r₀ rb : ℝ),
        0 ≤ etaH → 0 ≤ etaD → 0 ≤ T → 0 < ε → ε ≤ 1 / 2 →
        (∀ x i, ∑ j, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ x j, ∑ i, ‖ODEMatrixEnergy.hamiltonianPart (D.matrix x) i j‖ ^ 2 ≤ etaH ^ 2) →
        (∀ x i, ∑ j, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ x j, ∑ i, ‖ODEMatrixEnergy.dissipativePart (D.matrix x) i j‖ ^ 2 ≤ etaD ^ 2) →
        (∀ (x : X) (z : EuclideanSpace ℂ n), 0 ≤ (inner ℂ z (SparseStateOverlap.matrixOperator
          (ODEMatrixEnergy.dissipativePart (D.matrix x)) z)).re) →
        ∀ (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
        (∀ y, IsUnitary (J₀ y)) → (∀ y, IsUnitary (Jb y)) →
        ∀ seed : EuclideanSpace ℂ n, ‖seed‖ = 1 →
        ∃ (Tslots d : ℕ)
          (q : ℕ → MultiOracleCircuit.Program
            (ODEFinalNativeSource.physicalOracle
              (ι := Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) D
              (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
              Tslots d J₀ Jb))
          (M : ℕ)
          (ψ : ODEFinalNativeSource.Physical (Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕
            Bool) n Z (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
            Tslots d)
          (F : EuclideanSpace ℂ n →L[ℂ] ODEFinalNativeSource.Physical
            (Fin (ODEPublicGaussianEndpoint.gridSize D T gbar ε) ⊕ Bool) n Z
            (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε)) Tslots d),
          ∀ (x : X) (v b : EuclideanSpace ℂ n), ‖v‖ = r₀ → ‖b‖ = rb →
            (v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v) →
            (b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b) →
            ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
            r₀ + T * rb ≤
              gbar * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ →
            ∃ (hM : 0 < M) (hψ : ‖ψ‖ = 1) (hF : F† ∘L F = 1),
              HeraldedOutput (ODERepeatProtocol.fourTrials q M hM ψ hψ F hF) x
                (ODEStateNormalization.unitDirection
                  (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)) ε ∧
              RunsClose ((ODERepeatProtocol.fourTrials q M hM ψ hψ F hF).conditionalDensity x)
                (ODEStateNormalization.unitDirection
                  (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)) ε ∧
              ((ODERepeatProtocol.fourTrials q M hM ψ hψ F hF).worstCost
                  (ODESourceQueryBudget.matrixWeight fun _ => 1) : ℝ) ≤
                C * gbar * (Real.sqrt s * (T * etaH + T * etaD * Real.log (10000 * gbar / ε)) +
                  Real.sqrt (s * (T * etaH + T * etaD * Real.log (10000 * gbar / ε)) *
                    Real.log (10000 * gbar / ε)) + Real.log (10000 * gbar / ε)) ∧
              ∀ c : Bool, ((ODERepeatProtocol.fourTrials q M hM ψ hψ F hF).worstCost
                (ODESourceQueryBudget.sourceWeight c) : ℝ) ≤ C * gbar := by
  refine ⟨1274019840, by norm_num, ?_⟩
  intro X n Z _ _ _ _ _ s D etaH etaD T gbar ε r₀ rb hH hDiss hT hε hεHalf hrH hcH hrD hcD hPSD
    J₀ Jb hJ₀ hJb seed hSeed
  by_cases hex : ∃ (x : X) (v b : EuclideanSpace ℂ n), ‖v‖ = r₀ ∧ ‖b‖ = rb ∧
      ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 ∧
      (r₀ + T * rb) /
        ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖ ≤ gbar
  · obtain ⟨x₁, v₁, b₁, hv₁, hb₁, hsol₁, hg₁⟩ := hex
    have hg : 1 ≤ gbar := by
      have hRatio := ODEConstantForcing.normalization_ratio_ge_one
        (ODEPublicSourceMesh.generator D x₁)
        (ODEPublicSourceMesh.generator_dissipative D x₁ (hPSD x₁)) v₁ b₁ T hT hsol₁
      rw [hv₁, hb₁] at hRatio
      exact hRatio.trans hg₁
    obtain ⟨Tslots, d, E, q, -, hC⟩ := ZeroTimeRemarks.ODEConstant.solver_nonneg D etaH etaD T
      gbar ε r₀ rb hH hDiss hT hε hεHalf hrH hcH hrD hcD hPSD J₀ Jb hJ₀ hJb seed hSeed x₁ v₁ b₁
      hv₁ hb₁ hsol₁ hg₁
    have hℓ : 0 ≤ Real.log (10000 * gbar / ε) :=
      Real.log_nonneg (by rw [le_div_iff₀ hε]; nlinarith)
    have hshape : 0 ≤ ImprovedODEQueryBudget.queryShape (s : ℝ)
        (ImprovedODEQueryBudget.theta (T * etaH) (T * etaD) gbar ε)
        (ImprovedODEQueryBudget.logBudget gbar ε) := by
      unfold ImprovedODEQueryBudget.queryShape ImprovedODEQueryBudget.theta
        ImprovedODEQueryBudget.logBudget
      have : 0 ≤ T * etaH + T * etaD * Real.log (10000 * gbar / ε) := by positivity
      positivity
    refine ⟨Tslots, d, q, ODEGroverAverage.chosenIterations gbar,
      ODEFinalNativeSource.input D (Sum.inr false)
        (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε)) Tslots d
        (ODECompiledSource.seed E
          (ODESourcePublicNorms.publicCoefficients r₀ rb T
            (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
            (ODECoefficientPadding.paddedCoefficient
              (ODEPublicGaussianEndpoint.coefficients D T gbar ε) 3)) seed),
      ODEFinalNativeSource.input D (Sum.inr false)
        (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε)) Tslots d ∘L
          ODECompiledSource.output E
            (ODESourcePublicNorms.publicCoefficients r₀ rb T
              (ODEPublicSourceMesh.meshSize D T (ImprovedODEQueryBudget.precision gbar ε))
              (ODECoefficientPadding.paddedCoefficient
                (ODEPublicGaussianEndpoint.coefficients D T gbar ε) 3)),
      fun x v b hv hb hJv hJbv hsol hB => ?_⟩
    obtain ⟨h, hQ⟩ := hC v b x hv hb hJv hJbv hsol hB
    refine ⟨h.trial.cutoff_pos, h.trial.seed_unit, h.trial.output_isometry,
      ⟨h.success_two_thirds, h.output_density, h.conditional_error⟩,
      runsClose_of_certificate h hε.le, hQ.trans ?_, fun c => (h.source_queries c).trans ?_⟩
    · split_ifs
      · have : (0 : ℝ) ≤ 1274019840 * gbar := by positivity
        exact mul_nonneg this hshape
      · exact le_rfl
    · nlinarith
  · refine ⟨0, 0, fun _ => .fixed 1 OracleCircuit.isUnitary_one, 1, 0, 0,
      fun x v b hv hb _ _ hsol hB => ?_⟩
    exfalso
    refine hex ⟨x, v, b, hv, hb, hsol, ?_⟩
    rw [div_le_iff₀ (norm_pos_iff.mpr hsol)]
    linarith


end

end ManuscriptConformance
