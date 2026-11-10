import MixedOutputODE.Protocol
import GeneralODE.Theorem

/-!
# Theorem `ode:thm:general` with a mixed-output linear-system solver

Theorem `ode:thm:general` (general constant-coefficient equations) asks the
block-input linear-system solver only for a conditional output trace
distance `δ_LS` (eq. `ode:eq:history-solver-tolerance`), so the
solver's output may be mixed. This file proves the theorem from that weaker
hypothesis, `MixedBlockSolver f q₀`, with the matrix and source access, the
history construction and the instance hypotheses of the released
`GeneralODE.general`.

**Main theorem** (`general`). For `0 < ε ≤ 1/2`, `Λ, T > 0`, `C̄, g ≥ 1` and
`0 < q₀ ≤ 1` there are a work register `W` and one protocol, chosen before
the unknown input, such that in every history

* the number of native matrix queries is at most
  `40 (5g/√q₀) · f(κ, ε/(4096 g²)) · 3 K · 1327104 · shape(2s, 2(K+1), log(2/ε_n))`
  (`matrixBudget`), and each source interface is called at most
  `40 (5g/√q₀) · 3 f(κ, ε/(4096 g²))` times (`sourceBudget`);

and for every input with `‖e^{tA}‖ ≤ C̄` and `‖x(t)‖ ≤ g ‖x(T)‖` on `[0, T]` and
`x(T) ≠ 0`, the success probability is at least `175/256 > 2/3` and, after the
solver's work register is discarded, the conditional output is a density
operator within trace distance `ε` of `x(T)/‖x(T)‖` (`MixedOutcome`).

Besides the solver hypothesis and the output register (`n × W`, reduced by
`ptrace`), the only change in parameters and budgets from `GeneralODE.general`
is the requested solver accuracy, `ε/(4096 g²)` instead of `ε/(40 g)`: it
enters the query bound only through `f`, and only logarithmically for a solver
with `f(κ, δ) = c κ log(2/δ)`. The released pure-output interface implies the
mixed-output one (`mixed_of_block`), so `general_of_block` recovers a
pure-solver version of the theorem.
-/

namespace SparseHamiltonian.MixedOutputODE

noncomputable section
open ContinuousLinearMap OracleCircuit NativeSparseBlockEncoding ODEMixedOutput
  ODEStateNormalization GeneralODE GeneralODE.Solver GeneralODE.Registers GeneralODE.History
  GeneralODE.Implemented GeneralODE.NativeBlock SparseStateOverlap
open scoped InnerProduct BigOperators ComplexConjugate Nat
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

variable {n : Type} [Fintype n] [DecidableEq n]
variable {X Z : Type} [Fintype Z] [AddCommGroup Z] [DecidableEq Z] {s : ℕ}

/-- Worst-case native matrix queries with the mixed solver accuracy. -/
def matrixBudget (f : ℝ → ℝ → ℝ) (q₀ : ℝ) (s : ℕ) (Λ T Cbar g ε : ℝ) : ℝ :=
  40 * Plan.gain g q₀ * (f (Plan.kappa Λ T Cbar) (mixedDelta g ε) *
    (3 * ((Plan.degree Λ T Cbar g ε : ℝ) * (1327104 * ImprovedPrecisionBudget.shape (2 * (s : ℝ))
      (2 * (Plan.arcDegree Λ T Cbar g ε : ℝ))
      (ImprovedPrecisionBudget.targetLog (Plan.nativeError Λ T Cbar g ε))))))

/-- Worst-case calls of each source interface with the mixed solver accuracy. -/
def sourceBudget (f : ℝ → ℝ → ℝ) (q₀ : ℝ) (Λ T Cbar g ε : ℝ) : ℝ :=
  40 * Plan.gain g q₀ * (3 * f (Plan.kappa Λ T Cbar) (mixedDelta g ε))

/-- The guarantee of Theorem `ode:thm:general` with a mixed-output solver:
one protocol for all inputs; its output carries the solver's work register,
which is discarded. -/
def Outcome (f : ℝ → ℝ → ℝ) (q₀ : ℝ) (D : Data X n Z s)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (seed : EuclideanSpace ℂ n)
    (Λ T Cbar g ε r₀ rb : ℝ) : Prop :=
  ∃ (Tn d w : ℕ) (W : Type) (_ : Fintype W) (_ : DecidableEq W)
    (prot : ODERepeatProtocol.Protocol
      (physicalOracle D J₀ Jb (Plan.arcDegree Λ T Cbar g ε) Tn d (Plan.steps Λ T)
        (Plan.degree Λ T Cbar g ε) w) (EuclideanSpace ℂ (n × W))),
    (prot.worstCost (ODESourceQueryBudget.matrixWeight (fun _ => 1)) : ℝ) ≤
        matrixBudget f q₀ s Λ T Cbar g ε ∧
    (∀ b : Bool, (prot.worstCost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤
        sourceBudget f q₀ Λ T Cbar g ε) ∧
    ∀ (x : X) (v b : EuclideanSpace ℂ n), ‖v‖ = r₀ → ‖b‖ = rb →
      (v ≠ 0 → J₀ x seed = unitDirection v) → (b ≠ 0 → Jb x seed = unitDirection b) →
      (∀ t, 0 ≤ t → t ≤ T → ‖NormedSpace.exp (t • ODEPublicSourceMesh.generator D x)‖ ≤ Cbar) →
      (∀ t, 0 ≤ t → t ≤ T →
        ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b t‖ ≤
          g * ‖ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T‖) →
      ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T ≠ 0 →
      MixedOutcome prot x (ODEConstantForcing.solution (ODEPublicSourceMesh.generator D x) v b T) ε

/-- The construction, for public norms with a nonzero right-hand side. -/
theorem exists_protocol (f : ℝ → ℝ → ℝ) (q₀ : ℝ) (hsolver : MixedBlockSolver f q₀)
    (hq₀ : 0 < q₀) (hq₀1 : q₀ ≤ 1) (D : Data X n Z s) (Λ T Cbar g ε r₀ rb : ℝ)
    (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hA : ∀ x, ‖matrixOperator (D.matrix x)‖ ≤ Λ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1)
    (hr : 0 < (T / Real.sqrt (Plan.steps Λ T)) ^ 2 * rb ^ 2 + r₀ ^ 2) :
    Outcome f q₀ D J₀ Jb seed Λ T Cbar g ε r₀ rb := by
  have hm : 1 ≤ Plan.steps Λ T := Plan.steps_pos hΛ hT
  have hN1 : 1 ≤ Plan.arcDegree Λ T Cbar g ε := Nat.le_add_left 1 _
  -- Lemma `ode:lem:block`
  obtain ⟨Tn, d, qP, Ein, Eout, hin, hout, hqP, hblk⟩ := exists_native_block D Λ hΛ hA
    (Plan.arcDegree Λ T Cbar g ε) hN1 (Plan.nativeError Λ T Cbar g ε)
    (Plan.nativeError_pos hΛ hT hC hg hε) (Plan.nativeError_le hΛ hT hC hg hε hε1)
  -- the history encoding
  have hτ0 : 0 ≤ Plan.alpha Λ * (T / Plan.steps Λ T) := by
    have := Plan.alpha_pos hΛ
    positivity
  have hτ1 : Plan.alpha Λ * (T / Plan.steps Λ T) ≤ 1 := by
    have hs : (0 : ℝ) < Plan.steps Λ T := by exact_mod_cast hm
    rw [← mul_div_assoc, div_le_one hs]
    exact Plan.alpha_mul_le Λ T
  -- the protocol
  obtain ⟨w, W, hWf, hWd, prot, h1, h2, h3⟩ := exists_mixed_protocol_of_block f q₀ hsolver hq₀
    hq₀1
    (histData (Plan.steps Λ T) (Plan.degree Λ T Cbar g ε) hm (Plan.alpha Λ * (T / Plan.steps Λ T))
      hτ0 hτ1 (D.slot ⟨0, D.slots_pos⟩) (flatClean D (Plan.arcDegree Λ T Cbar g ε) Tn d)
      Ein Eout hin hout)
    (flatOracle D (Plan.arcDegree Λ T Cbar g ε) Tn d)
    (flatOracle_unitary D (Plan.arcDegree Λ T Cbar g ε) Tn d)
    (flatImage D (Plan.arcDegree Λ T Cbar g ε) Tn d)
    (flatOracle_valid D (Plan.arcDegree Λ T Cbar g ε) Tn d) qP
    (ODEPublicSourceMesh.generator D) J₀ Jb hJ₀ hJb seed hseed Λ T Cbar g ε (Plan.alpha Λ)
    (2 * Plan.nativeError Λ T Cbar g ε + (1 / 4) ^ Plan.arcDegree Λ T Cbar g ε / 2)
    (2 * Plan.nativeError Λ T Cbar g ε) r₀ rb rfl rfl rfl hm hT (Plan.alpha_pos hΛ)
    (Plan.alpha_mul_le Λ T) (Plan.eight_mul_le hΛ hT)
    (fun x => by
      change ‖-matrixOperator (D.matrix x)‖ ≤ Λ
      rw [norm_neg]
      exact hA x)
    (fun x => (hblk x).1) (fun x => (hblk x).2) hC hg hε hε1
    (Plan.budget_identity hΛ hT hC hg hε) (Plan.budget_matrix hΛ hT hC hg hε)
    (Plan.budget_taylor hΛ hT hC hg hε) hr
  unfold Outcome
  refine ⟨Tn, d, w, W, hWf, hWd, prot, h1.trans ?_, h2, h3⟩
  have hg0 : 0 ≤ 40 * Plan.gain g q₀ := by
    have := Plan.one_le_gain hg hq₀ hq₀1
    linarith
  have h2' : ∀ b : Bool, (prot.worstCost (ODESourceQueryBudget.sourceWeight b) : ℝ) ≤
      sourceBudget f q₀ Λ T Cbar g ε := h2
  have hf : (0 : ℝ) ≤ f (Plan.kappa Λ T Cbar) (mixedDelta g ε) := by
    have h0 := (Nat.cast_nonneg _).trans (h2' true)
    unfold sourceBudget at h0
    have hgp : 0 < 40 * Plan.gain g q₀ := by
      have := Plan.one_le_gain hg hq₀ hq₀1
      linarith
    have h3f : 0 ≤ 3 * f (Plan.kappa Λ T Cbar) (mixedDelta g ε) := by
      by_contra hcon
      push Not at hcon
      have := mul_neg_of_pos_of_neg hgp hcon
      linarith
    linarith
  unfold matrixBudget
  apply mul_le_mul_of_nonneg_left _ hg0
  apply mul_le_mul_of_nonneg_left _ hf
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact mul_le_mul_of_nonneg_left hqP (Nat.cast_nonneg _)

/-- **Theorem `ode:thm:general` with a mixed-output solver.** -/
theorem general (f : ℝ → ℝ → ℝ) (q₀ : ℝ) (hsolver : MixedBlockSolver f q₀)
    (hq₀ : 0 < q₀) (hq₀1 : q₀ ≤ 1) (D : Data X n Z s) (Λ T Cbar g ε r₀ rb : ℝ)
    (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hA : ∀ x, ‖matrixOperator (D.matrix x)‖ ≤ Λ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1) :
    Outcome f q₀ D J₀ Jb seed Λ T Cbar g ε r₀ rb := by
  by_cases hr : 0 < (T / Real.sqrt (Plan.steps Λ T)) ^ 2 * rb ^ 2 + r₀ ^ 2
  · exact exists_protocol f q₀ hsolver hq₀ hq₀1 D Λ T Cbar g ε r₀ rb hΛ hT hC hg hε hε1 hA
      J₀ Jb hJ₀ hJb seed hseed hr
  · have hr' : 0 < (T / Real.sqrt (Plan.steps Λ T)) ^ 2 * (0 : ℝ) ^ 2 + (1 : ℝ) ^ 2 := by norm_num
    obtain ⟨Tn, d, w, W, hWf, hWd, prot, h1, h2, -⟩ := exists_protocol f q₀ hsolver hq₀ hq₀1 D
      Λ T Cbar g ε 1 0 hΛ hT hC hg hε hε1 hA J₀ Jb hJ₀ hJb seed hseed hr'
    unfold Outcome
    refine ⟨Tn, d, w, W, hWf, hWd, prot, h1, h2, ?_⟩
    intro x v b hv hb _ _ _ _ hne
    exfalso
    have hle : (T / Real.sqrt (Plan.steps Λ T)) ^ 2 * rb ^ 2 + r₀ ^ 2 ≤ 0 := not_lt.mp hr
    have hm : (0 : ℝ) < Plan.steps Λ T := by exact_mod_cast Plan.steps_pos hΛ hT
    have hμ : 0 < (T / Real.sqrt (Plan.steps Λ T)) ^ 2 := by
      have := Real.sqrt_pos.mpr hm
      positivity
    have hr₀ : r₀ = 0 := by nlinarith [sq_nonneg r₀]
    have hrb : rb = 0 := by
      have : (T / Real.sqrt (Plan.steps Λ T)) ^ 2 * rb ^ 2 ≤ 0 := by nlinarith [sq_nonneg r₀]
      have : rb ^ 2 ≤ 0 := by
        by_contra hcon
        push Not at hcon
        have := mul_pos hμ hcon
        linarith
      nlinarith [sq_nonneg rb]
    have hv0 : v = 0 := norm_eq_zero.mp (hv.trans hr₀)
    have hb0 : b = 0 := norm_eq_zero.mp (hb.trans hrb)
    apply hne
    rw [hv0, hb0]
    exact solution_zero_zero _ T

/-- The released pure-output solver gives the same guarantee, with the mixed
accuracy request. -/
theorem general_of_block (f : ℝ → ℝ → ℝ) (q₀ : ℝ) (hsolver : BlockSolver f q₀)
    (hq₀ : 0 < q₀) (hq₀1 : q₀ ≤ 1) (D : Data X n Z s) (Λ T Cbar g ε r₀ rb : ℝ)
    (hΛ : 0 < Λ) (hT : 0 < T) (hC : 1 ≤ Cbar) (hg : 1 ≤ g) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hA : ∀ x, ‖matrixOperator (D.matrix x)‖ ≤ Λ)
    (J₀ Jb : X → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (hJ₀ : ∀ y, IsUnitary (J₀ y)) (hJb : ∀ y, IsUnitary (Jb y))
    (seed : EuclideanSpace ℂ n) (hseed : ‖seed‖ = 1) :
    Outcome f q₀ D J₀ Jb seed Λ T Cbar g ε r₀ rb :=
  general f q₀ (mixed_of_block f q₀ hsolver) hq₀ hq₀1 D Λ T Cbar g ε r₀ rb hΛ hT hC hg hε hε1
    hA J₀ Jb hJ₀ hJb seed hseed

end

end SparseHamiltonian.MixedOutputODE
