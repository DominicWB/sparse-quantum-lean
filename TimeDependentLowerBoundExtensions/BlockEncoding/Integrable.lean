import TimeDependentLowerBoundExtensions.BlockEncoding.Bound
import IntegrablePathSimulation.BlockEncoding.Theorem

set_option autoImplicit false
set_option synthInstance.maxSize 4096

/-!
# Calls of time-indexed block encodings under the integrable-path criterion

For an integrable Hermitian path it suffices to have a certified bound on the integrated sample
errors (the manuscript, lines 1500-1504), and the block-encoding simulator of
`IntegrablePathSimulation.BlockEncoding.simulation` meets the corresponding criterion on the
released aligned block-encoding family. The lower bound of Theorem `hsl:thm:main` applies to the
time-dependent class with time-independent hard instances (lines 1512-1516).

* `BEIntegrableCriterion`: the error criterion of
  `IntegrablePathSimulation.BlockEncoding.simulation` for one program (every path self-adjoint
  at almost every time of `[0, T]` and interval integrable on `[0, T]`, whose integrated sample
  errors against `α_BE J† O_r J` are at most `ε / 9`, and every integral-sense propagator `U`,
  error at most `ε` at time `T`);
* `beIntegrableCriterion_endpoint`: on the constant hard data the constant path has zero sample
  error and `exp(-iuH_x)` is an integral-sense propagator
  (`TimeDependentHamiltonianLowerBound.isPropagator_constProp`), so the criterion gives the
  endpoint error against `exp(-iτH_x)`;
* `main_max_block_integrable`: `c₀ (√s τ + √(sτr) + r) ≤ 8 · max(Q_T, Q_M, Q_P)` under this
  criterion, from `main_max_block_endpoint`.
-/

namespace TimeDependentLowerBoundExtensions.BlockEncoding

noncomputable section

open SparseHamiltonian NativeSparseBlockEncoding OracleCircuit ContinuousLinearMap
open SparseLowerBounds SparseLowerBounds.Hamiltonian HsRelease
open TimeDependentHamiltonianLowerBound (constProp)
open IntegrablePathSimulation.Propagator (IsPropagator)
open MeasureTheory Set
open scoped InnerProduct InnerProductSpace

section Criterion

variable {X n B₀ : Type*} [Fintype n] [DecidableEq n] [Fintype B₀] [DecidableEq B₀] {M : ℕ}
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- **The error criterion of `IntegrablePathSimulation.BlockEncoding.simulation`** for a run
`run x` with input encoding `ι`, samples `O`, boundary `J`, normalisation `α`, mesh `t` with `M`
intervals, final time `T` and error `ε`: for every instance, every path `H` that is
self-adjoint at almost every time of `[0, T]` and interval integrable on `[0, T]`, whose
integrated sample errors `∑_r ∫ ‖H(u) - α J† O_r J‖ du` are at most `ε / 9`, and every
propagator `U` of `H` in the integral sense, `‖run x ∘ ι - ι ∘ U(T)‖ ≤ ε`. -/
def BEIntegrableCriterion (run : X → K →L[ℂ] K) (ι : EuclideanSpace ℂ n →L[ℂ] K)
    (O : X → Fin M → EuclideanSpace ℂ B₀ →L[ℂ] EuclideanSpace ℂ B₀)
    (J : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ B₀) (α : ℝ) (t : ℕ → ℝ) (T ε : ℝ) : Prop :=
  ∀ x, ∀ (H U : ℝ → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n),
    (∀ᵐ u, u ∈ Icc 0 T → star (H u) = H u) →
    IntervalIntegrable H volume 0 T →
    ∑ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
        ‖H u - TimeDependentExtensions.BlockEncoding.blockSample (O x r) J α‖ ≤ ε / 9 →
    IsPropagator H U T →
    ‖run x ∘L ι - ι ∘L U T‖ ≤ ε

end Criterion

variable {X N Z : Type} [Fintype N] [DecidableEq N] [Fintype Z] [AddCommGroup Z] [DecidableEq Z]
  {s : ℕ}

/-- **The integrable-path criterion on the constant hard data gives the endpoint error**: the
constant path `H(u) = H_x` is self-adjoint, integrable and has zero sample error against
`α_BE J† (beOp D x) J = H_x`, and `exp(-iuH_x)` is its propagator in the integral sense on
`[0, τ]`. -/
theorem beIntegrableCriterion_endpoint {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (D : Data X N Z s)
    (hH : ∀ x, (D.matrix x).IsHermitian) (M : ℕ) (t : ℕ → ℝ) {τ ε : ℝ} (hτ : 0 ≤ τ)
    (hε : 0 ≤ ε) (run : X → K →L[ℂ] K) (ι : EuclideanSpace ℂ N →L[ℂ] K)
    (hcrit : BEIntegrableCriterion run ι (beConst D M) (beJ D) (beAlpha D) t τ ε) (x : X) :
    ‖run x ∘L ι - ι ∘L NormedSpace.exp ((-Complex.I * (τ : ℂ)) •
      SparseStateOverlap.matrixOperator (D.matrix x))‖ ≤ ε := by
  have hS : ∀ r : Fin M, ∫ u in t r..t ((r : ℕ) + 1),
      ‖SparseStateOverlap.matrixOperator (D.matrix x) -
        TimeDependentExtensions.BlockEncoding.blockSample (beConst D M x r) (beJ D)
          (beAlpha D)‖ = 0 := by
    intro r
    simp only [beConst, blockSample_beOp D hH x, sub_self, norm_zero,
      intervalIntegral.integral_zero]
  exact hcrit x (fun _ => SparseStateOverlap.matrixOperator (D.matrix x))
    (constProp (SparseStateOverlap.matrixOperator (D.matrix x)))
    (Filter.Eventually.of_forall fun _ _ =>
      SparseHamiltonian.SparseValuePrecision.matrixOperator_star_eq _ (hH x))
    intervalIntegrable_const
    (by rw [Finset.sum_eq_zero (fun r _ => hS r)]; linarith)
    (TimeDependentHamiltonianLowerBound.isPropagator_constProp _ hτ)

variable {τ ε : ℝ}

/-- **Theorem `hsl:thm:main` for calls of time-indexed block encodings, integrable-path
criterion** (eq. `hsl:eq:main`): as `main_max_block`, for programs over the released aligned
block-encoding families of the constant Hermitian block encodings of the time, mixed and
precision families (any numbers of samples, slot counts and schedules) and isometric
encodings, each meeting the error criterion of
`IntegrablePathSimulation.BlockEncoding.simulation` (`BEIntegrableCriterion`, boundary `beJ`,
normalisation `beAlpha`, any mesh `t`, final time `τ`, error `ε`),
`c₀ (√s τ + √(sτr) + r) ≤ 8 · max(Q_T, Q_M, Q_P)`, `Q = p.count`, inverses included. The
factor `8` comes from the reduction. -/
theorem main_max_block_integrable (h : HSRange τ s ε) (MT MM MP NT NM NP : ℕ)
    (αT TT εT αM TM εM αP TP εP : ℝ)
    (tT tM tP : ℕ → ℝ)
    (pT : MultiOracleCircuit.Program (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (timeData τ s h.s_ge) MT) NT αT TT εT))
    (ιT : EuclideanSpace ℂ (SearchIndex (timeN τ) (hsMu s) s) →L[ℂ]
      BETimeWork τ s MT NT αT TT εT) (hιT : ιT† ∘L ιT = 1)
    (hT : BEIntegrableCriterion pT.eval ιT (beConst (timeData τ s h.s_ge) MT)
      (beJ (timeData τ s h.s_ge)) (beAlpha (timeData τ s h.s_ge)) tT τ ε)
    (pM : MultiOracleCircuit.Program (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (mixedMainData τ ε s h.s_ge) MM) NM αM TM εM))
    (ιM : EuclideanSpace ℂ (SearchIndex (precN τ ε) (hsMu s) s) →L[ℂ]
      BEMixedWork τ ε s MM NM αM TM εM) (hιM : ιM† ∘L ιM = 1)
    (hM : BEIntegrableCriterion pM.eval ιM (beConst (mixedMainData τ ε s h.s_ge) MM)
      (beJ (mixedMainData τ ε s h.s_ge)) (beAlpha (mixedMainData τ ε s h.s_ge)) tM τ ε)
    (pP : MultiOracleCircuit.Program (TimeDependentExtensions.BlockEncoding.alignedOracle
      (beConst (precisionMainData τ ε s h.s_ge) MP) NP αP TP εP))
    (ιP : EuclideanSpace ℂ (ScalarIndex (precN τ ε) s) →L[ℂ]
      BEPrecisionWork τ ε s MP NP αP TP εP) (hιP : ιP† ∘L ιP = 1)
    (hP : BEIntegrableCriterion pP.eval ιP (beConst (precisionMainData τ ε s h.s_ge) MP)
      (beJ (precisionMainData τ ε s h.s_ge)) (beAlpha (precisionMainData τ ε s h.s_ge)) tP τ
      ε) :
    c0 * (Real.sqrt s * τ + Real.sqrt (s * τ * hsR τ ε) + hsR τ ε) ≤
      8 * max (pT.count : ℝ) (max (pM.count : ℝ) (pP.count)) := by
  have hτ : 0 ≤ τ := by linarith [h.one_le_tau]
  have hε : 0 ≤ ε := h.eps_pos.le
  exact main_max_block_endpoint h MT MM MP NT NM NP αT TT εT αM TM εM αP TP εP pT ιT hιT
    (beIntegrableCriterion_endpoint _ (hard_instances h).1.isHermitian MT tT hτ hε pT.eval ιT
      hT)
    pM ιM hιM
    (beIntegrableCriterion_endpoint _ (hard_instances h).2.1.isHermitian MM tM hτ hε pM.eval ιM
      hM)
    pP ιP hιP
    (beIntegrableCriterion_endpoint _ (hard_instances h).2.2.1.isHermitian MP tP hτ hε pP.eval
      ιP hP)

end

end TimeDependentLowerBoundExtensions.BlockEncoding
