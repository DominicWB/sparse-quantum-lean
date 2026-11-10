import ManuscriptConformance.ODEUpper
import MixedOutputODE.Complexity
import GeneralODEZeroTime.Theorem

/-!
# Conformance: general constant-coefficient equations

Theorem `ode:thm:general` and its proof. The theorem "combines the new sparse-access conversion with
the propagator-dependent stability analysis" and, in its last step (solving and selecting the final
time), uses "a near-optimal block-input linear-system algorithm [Costa et al.; Dalzell]", from which
it requests only a conditional output trace distance (eq. `ode:eq:history-solver-tolerance`). That
external solver is the hypothesis `ext_blockSolver` (`MixedOutputODE.MixedBlockSolver`): with
`c κ log(2/δ)` calls of the block encoding and its control, heralded success probability at least
`q₀`, a circuit, work register and decoder fixed before the instance, and conditional reduced-state
trace distance `δ`. It is the manuscript's own assumption; its form here is a formal restriction (summary table).

* **Input.** `ẋ = Ax + b`, constant, with native sparse data for `G = -A` (`D.matrix x`), the
  spectral bound `‖A‖ ≤ Λ`, `Λ > 0`; supplied `r₀ = ‖x₀‖`, `r_b = ‖b‖`, `C̄ ≥ C_A =
  max_{t ≤ T} ‖e^{At}‖`, `ḡ_path ≥ max_{t ≤ T} ‖x(t)‖/‖x(T)‖`, `x(T) ≠ 0`.
* **Access.** The native sparse primitives of `D` and the preparations `J₀`, `J_b`
  (`GeneralODE.physicalOracle`).
* **Guarantee.** One protocol, fixed before the instance; success probability at least `2/3`;
  after the solver's work register is discarded (`MixedOutputODE.ptrace`), a density operator
  within trace distance `ε` of `x(T)/‖x(T)‖`.
* **Cost.** `Õ(√s ḡ_path C̄ (1 + ΛT))` matrix queries, with the explicit suppressed factor `𝓛³/√q₀`,
  `𝓛 = 1 + log((1 + ΛT) C̄ ḡ_path/ε)` (`GeneralODE.Complexity.logFactor`), a fixed polynomial in the
  logarithms of the theorem: `log(1/ε) ≤ log(2C̄) + log(2 + ḡ_B/ε)` since `C̄ ḡ_B ≥ 1` (the last
  paragraph of the proof). The bound `ḡ_B` is not needed. The case `T = 0` (direct preparation of
  the initial state) is `ode_thm_general_zero`.
-/

set_option autoImplicit false

namespace ManuscriptConformance

noncomputable section
open ContinuousLinearMap SparseHamiltonian NativeSparseBlockEncoding OracleCircuit
open scoped InnerProduct InnerProductSpace

set_option maxRecDepth 4096
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:general`** (eq. `ode:eq:general`), for `T > 0`,
conditional on the external block-input linear-system solver of the manuscript's proof
(`ext_blockSolver`). One protocol, fixed before the instance, has success probability at least
`2/3` and conditional reduced output within trace distance `ε` of the normalised final state on
every instance, using at most `C c (ḡ_path/√q₀) C̄ (1 + ΛT) √s 𝓛³` matrix queries and
`C' c (ḡ_path/√q₀) C̄ (1 + ΛT) 𝓛` calls of each preparation (an addition of the package: Theorem
`ode:thm:general` states the matrix-query count only), `𝓛 = 1 + log((1 + ΛT) C̄ ḡ_path/ε)`,
`C = 227776401506304000`, `C' = 26292000`. The supplied bounds satisfy `1 ≤ C̄` and `1 ≤ ḡ_path`,
as the manuscript's bounds `C̄ ≥ C_A = max_t ‖e^{At}‖ ≥ 1` and `ḡ_path ≥ g_path ≥ 1` do (by the
definitions of `C_A` and `g_path` before the theorem). Formal restrictions: the form of `ext_blockSolver` and exact unitary preparations (summary table). -/
theorem ode_thm_general (c q₀ : ℝ) (hc : 0 ≤ c) (hq₀ : 0 < q₀) (hq₀1 : q₀ ≤ 1)
    (ext_blockSolver :
      MixedOutputODE.MixedBlockSolver (fun κ δ => c * κ * Real.log (2 / δ)) q₀)
    {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
    {s : ℕ} (D : Data X n Z s) (Λ T Cbar gpath ε r₀ rb : ℝ)
    (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ gpath) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hA : ∀ x, ‖SparseStateOverlap.matrixOperator (D.matrix x)‖ ≤ Λ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1) :
    ∃ (Tn d w : ℕ) (W : Type) (_ : Fintype W) (_ : DecidableEq W)
      (A : ODERepeatProtocol.Protocol
        (GeneralODE.physicalOracle D J₀ Jb (GeneralODE.Plan.arcDegree Λ T Cbar gpath ε) Tn d
          (GeneralODE.Plan.steps Λ T) (GeneralODE.Plan.degree Λ T Cbar gpath ε) w)
        (EuclideanSpace ℂ (n × W))),
      (A.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
          227776401506304000 * (c * (gpath / Real.sqrt q₀) * (Cbar * (1 + Λ * T)) *
            Real.sqrt s * (1 + Real.log ((1 + Λ * T) * Cbar * gpath / ε)) ^ 3) ∧
      (∀ b : Bool, (A.worstCost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤
          26292000 * (c * (gpath / Real.sqrt q₀) * (Cbar * (1 + Λ * T)) *
            (1 + Real.log ((1 + Λ * T) * Cbar * gpath / ε)))) ∧
      ∀ (x : X) (v b : EuclideanSpace ℂ n), ‖v‖ = r₀ → ‖b‖ = rb →
        (v ≠ 0 → J₀ x seed = ODEStateNormalization.unitDirection v) →
        (b ≠ 0 → Jb x seed = ODEStateNormalization.unitDirection b) →
        (∀ t, 0 ≤ t → t ≤ T →
          ‖NormedSpace.exp (t • ODEPublicSourceMesh.generator D x)‖ ≤ Cbar) →
        (∀ t, 0 ≤ t → t ≤ T →
          ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b t‖ ≤
            gpath * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖) →
        ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
        2 / 3 ≤ A.successMass x ∧
          ODEMixedOutput.IsDensity (MixedOutputODE.ptrace (A.conditionalDensity x)) ∧
          TraceDistanceLE (MixedOutputODE.ptrace (A.conditionalDensity x))
            (ODEStateNormalization.unitDirection
              (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T)) ε := by
  obtain ⟨Tn, d, w, W, hW, hWd, A, h1, h2, h3⟩ := MixedOutputODE.general_query_bound c q₀ hc
    ext_blockSolver hq₀ hq₀1 D Λ T Cbar gpath ε r₀ rb hΛ hT hC hg hε hε1 hA J₀ Jb hJ₀ hJb seed
    hseed
  refine ⟨Tn, d, w, W, hW, hWd, A, h1, h2, fun x v b hv hb hJv hJbv hCA hpath hsol => ?_⟩
  have h := h3 x v b hv hb hJv hJbv hCA hpath hsol
  exact ⟨h.success_two_thirds, h.output_density, h.conditional_error⟩

set_option maxHeartbeats 8000000 in
/-- **Theorem `ode:thm:general` at `T = 0`** ("The case `T = 0` is direct preparation of the initial
state", the proof of Theorem `ode:thm:general`). In the oracle model of `ode_thm_general` (any
register parameters), one protocol, fixed before the instance, makes no matrix query and no forcing
call and at most `40` calls of the initial-state preparation in every history, and on every instance
with `x₀ ≠ 0` succeeds with probability at least `2/3` with conditional output within trace distance
`ε` of `x₀/‖x₀‖`, for every `ε ≥ 0`. Formal restrictions: exact unitary preparations (summary table). -/
theorem ode_thm_general_zero {X n Z : Type} [Fintype n] [DecidableEq n] [Fintype Z]
    [AddCommGroup Z] [DecidableEq Z] {s : ℕ} (D : Data X n Z s)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1) (N Tn d m K w : ℕ) (hw : 0 < w) :
    ∃ A : ODERepeatProtocol.Protocol (GeneralODE.physicalOracle D J₀ Jb N Tn d m K w)
        (EuclideanSpace ℂ n),
      A.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) = 0 ∧
      A.worstCost (ODESourceQueryBudget.sourceWeight true) = 0 ∧
      A.worstCost (ODESourceQueryBudget.sourceWeight false) ≤ 40 ∧
      ∀ (x : X) (v b : EuclideanSpace ℂ n), v ≠ 0 →
        J₀ x seed = ODEStateNormalization.unitDirection v → ∀ ε : ℝ, 0 ≤ ε →
          HeraldedOutput A x (ODEStateNormalization.unitDirection
            (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b 0)) ε := by
  obtain ⟨A, h1, h2, h3, h4⟩ := GeneralODE.general_zero D J₀ Jb hJ₀ hJb seed hseed N Tn d m K w hw
  refine ⟨A, h1, h2, h3, fun x v b hv hJv ε hε => ?_⟩
  have h := h4 x v b hv hJv ε hε
  exact ⟨h.success_two_thirds, h.output_density, h.conditional_error⟩

end

end ManuscriptConformance
